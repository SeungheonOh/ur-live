{-# LANGUAGE DerivingStrategies #-}

-- | Specialize named functions on concrete higher-order value arguments.
--
-- This is Ur/Web's @ESpecialize@ pass.  Constructor specialization can leave
-- runtime arguments whose types contain functions, most notably a monad
-- dictionary with rank-2 @Return@ and @Bind@ fields.  Such values cannot cross
-- the monomorphic boundary.  When a named function is called with a concrete
-- dictionary, callback, or other function-containing value, this pass clones
-- the function with that argument substituted into its body.
--
-- Recursive functions require two precautions from the reference pass:
--
-- * only an argument prefix invariant across recursive calls is eligible; and
-- * free local variables in specialized arguments become explicit parameters
--   of the generated top-level binding.
--
-- A round may expose another opportunity after untangling and shaking, so the
-- public entry point iterates to a fixed point.
module Vr.Core.ExpressionSpecialize
  ( specializeFile
  ) where

import Control.Monad.State.Strict (State, evalState, get, gets, modify')
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import qualified Vr.Core.Reduce as Reduce
import qualified Vr.Core.Shake as Shake
import qualified Vr.Core.Substitute as Substitute
import qualified Vr.Core.Syntax as C
import qualified Vr.Core.Untangle as Untangle
import Vr.Source (Located (..), Span, noSpan)

type Binding = (String, C.GlobalId, C.Con, C.Expr, String)

type Environment = [(String, C.Con)]

data SpecializationKey = SpecializationKey ![C.Con] ![C.Expr]
  deriving stock (Eq, Ord, Show)

data FunctionInfo = FunctionInfo
  { functionName :: !String
  , functionInstances :: !(Map.Map SpecializationKey C.GlobalId)
  , functionBody :: !C.Expr
  , functionType :: !C.Con
  , functionUrl :: !String
  , functionConstantArguments :: !Int
  }

data SpecializeState = SpecializeState
  { specializeNextId :: !Int
  , specializeFunctions :: !(Map.Map C.GlobalId FunctionInfo)
  , specializeGenerated :: ![Binding]
  , specializeChanged :: !Bool
  , specializeFunctionTypes :: !(Set.Set C.GlobalId)
  }

type SpecializeM = State SpecializeState

-- | Run expression specialization to a fixed point.  Reduction exposes record
-- projections and beta-redexes created by substitution; untangling and shaking
-- make generated recursive groups available to the next round and discard the
-- now-unreferenced generic versions.
specializeFile :: Reduce.ReduceSettings -> C.File -> C.File
specializeFile settings file = go Map.empty (maximumGlobal file + 1) file
  where
    go functions nextId currentFile =
      let reduced = Reduce.reduceFile settings currentFile
          (changed, specialized, functions', nextId') =
            specializeRound functions nextId reduced
       in if changed
            then
              go functions' nextId'
                (Shake.shakeFile (Untangle.untangleFile specialized))
            else specialized

specializeRound
  :: Map.Map C.GlobalId FunctionInfo
  -> Int
  -> C.File
  -> (Bool, C.File, Map.Map C.GlobalId FunctionInfo, Int)
specializeRound functions nextId file =
  let initial =
        SpecializeState
          { specializeNextId = max nextId (maximumGlobal file + 1)
          , specializeFunctions = functions
          , specializeGenerated = []
          , specializeChanged = False
          , specializeFunctionTypes = collectFunctionTypes file
          }
      (declarations, final) = runStatePair (mapM specializeDeclaration file) initial
   in ( specializeChanged final
      , concat declarations
      , specializeFunctions final
      , specializeNextId final
      )

runStatePair :: State state value -> state -> (value, state)
runStatePair action initial =
  let tagged = do
        value <- action
        state <- get
        pure (value, state)
   in evalState tagged initial

specializeDeclaration :: C.Decl -> SpecializeM [C.Decl]
specializeDeclaration declaration = do
  modify' $ \state -> state {specializeGenerated = []}
  registerRecursiveDeclaration declaration
  declaration' <-
    if polymorphicDeclaration declaration
      then pure declaration
      else traverseDeclaration declaration
  registerOrdinaryDeclaration declaration
  generated <- gets (reverse . specializeGenerated)
  pure (materialize declaration' generated)

materialize :: C.Decl -> [Binding] -> [C.Decl]
materialize declaration generated = case generated of
  [] -> [declaration]
  _ -> case locatedValue declaration of
    C.DValRec bindings ->
      [declaration {locatedValue = C.DValRec (generated <> bindings)}]
    _ ->
      [ Located (locatedSpan declaration) (C.DValRec generated)
      , declaration
      ]

registerRecursiveDeclaration :: C.Decl -> SpecializeM ()
registerRecursiveDeclaration declaration = case locatedValue declaration of
  C.DValRec bindings -> do
    let family = Set.fromList [identifier | (_, identifier, _, _, _) <- bindings]
        constantCount = minimum (largeCount : [constantArguments family expression | (_, _, _, expression, _) <- bindings])
        insertOne functions (name, identifier, typ, expression, url) =
          Map.insert identifier (FunctionInfo name Map.empty expression typ url constantCount) functions
    modify' $ \state ->
      state {specializeFunctions = foldl' insertOne (specializeFunctions state) bindings}
  _ -> pure ()

registerOrdinaryDeclaration :: C.Decl -> SpecializeM ()
registerOrdinaryDeclaration declaration = case locatedValue declaration of
  C.DVal name identifier typ expression url -> case locatedValue expression of
    C.EAbs {} -> do
      let count = constantArguments (Set.singleton identifier) expression
      modify' $ \state -> state
        { specializeFunctions =
            Map.insert identifier (FunctionInfo name Map.empty expression typ url count)
              (specializeFunctions state)
        }
    C.ENamed target -> do
      functions <- gets specializeFunctions
      case Map.lookup target functions of
        Nothing -> pure ()
        Just info ->
          modify' $ \state -> state
            {specializeFunctions = Map.insert identifier info (specializeFunctions state)}
    _ -> pure ()
  _ -> pure ()

polymorphicDeclaration :: C.Decl -> Bool
polymorphicDeclaration declaration = case locatedValue declaration of
  C.DVal _ _ typ _ _ -> polymorphicResult typ
  C.DValRec bindings -> any (\(_, _, typ, _, _) -> polymorphicResult typ) bindings
  _ -> False

-- ESpecialize leaves static abstraction to Unpoly.  Only result position is
-- inspected: a monomorphic function may legitimately accept a polymorphic
-- dictionary, which is precisely the argument this pass must eliminate.
polymorphicResult :: C.Con -> Bool
polymorphicResult typ = case locatedValue typ of
  C.TFun _ result -> polymorphicResult result
  C.TCFun {} -> True
  C.TKFun {} -> True
  _ -> False

traverseDeclaration :: C.Decl -> SpecializeM C.Decl
traverseDeclaration declaration = case locatedValue declaration of
  C.DVal name identifier typ expression url -> do
    expression' <- specializeExpr [] expression
    pure (at (C.DVal name identifier typ expression' url))
  C.DValRec bindings -> do
    bindings' <- mapM binding bindings
    pure (at (C.DValRec bindings'))
  C.DTable name identifier row sqlName primary keys constraints uniques -> do
    primary' <- specializeExpr [] primary
    constraints' <- specializeExpr [] constraints
    pure (at (C.DTable name identifier row sqlName primary' keys constraints' uniques))
  C.DView name identifier sqlName expression row -> do
    expression' <- specializeExpr [] expression
    pure (at (C.DView name identifier sqlName expression' row))
  C.DIndex table modes -> do
    table' <- specializeExpr [] table
    modes' <- specializeExpr [] modes
    pure (at (C.DIndex table' modes'))
  C.DTask kind body -> do
    kind' <- specializeExpr [] kind
    body' <- specializeExpr [] body
    pure (at (C.DTask kind' body'))
  C.DPolicy expression -> do
    expression' <- specializeExpr [] expression
    pure (at (C.DPolicy expression'))
  _ -> pure declaration
  where
    at = Located (locatedSpan declaration)
    binding (name, identifier, typ, expression, url) = do
      expression' <- specializeExpr [] expression
      pure (name, identifier, typ, expression', url)

specializeExpr :: Environment -> C.Expr -> SpecializeM C.Expr
specializeExpr environment expression = case runtimeApplication expression of
  Just (identifier, arguments) -> do
    functions <- gets specializeFunctions
    case Map.lookup identifier functions of
      Nothing -> descend environment expression
      Just info -> do
        arguments' <- mapM (specializeExpr environment) arguments
        attemptSpecialization environment expression identifier info arguments'
  Nothing -> descend environment expression

attemptSpecialization
  :: Environment
  -> C.Expr
  -> C.GlobalId
  -> FunctionInfo
  -> [C.Expr]
  -> SpecializeM C.Expr
attemptSpecialization environment original sourceId info arguments = do
  functionTypes <- gets specializeFunctionTypes
  case splitSpecializedArguments functionTypes (functionConstantArguments info) (functionType info) arguments of
    Nothing -> pure (rebuildRuntimeApplication original sourceId arguments)
    Just (selected, remaining) -> do
      let free = Set.toAscList (Set.unions (map freeVariables selected))
          captured = mapMaybe (`environmentAt` environment) free
      if length captured /= length free
        then pure (rebuildRuntimeApplication original sourceId arguments)
        else do
          let squished = map (squishVariables free) selected
          if all relativeExpression squished
            then pure (rebuildRuntimeApplication original sourceId arguments)
            else do
              let capturedTypes = map (semanticCon . snd) captured
                  key = SpecializationKey capturedTypes (map semanticExpr squished)
              instances <- gets specializeFunctions
              case Map.lookup sourceId instances >>= Map.lookup key . functionInstances of
                Just target -> pure (specializedApplication original target free remaining)
                Nothing -> case trimArguments squished (functionType info) (functionBody info) of
                  Nothing -> pure (rebuildRuntimeApplication original sourceId arguments)
                  Just (body, typ) -> do
                    target <- freshGlobal
                    -- Install the memo entry before visiting the generated body
                    -- so recursive calls select this same specialization.
                    modify' $ \state -> state
                      { specializeFunctions = Map.adjust
                          (\current -> current
                            {functionInstances = Map.insert key target (functionInstances current)})
                          sourceId
                          (specializeFunctions state)
                      , specializeChanged = True
                      }
                    let (capturedBody, capturedType) = abstractCaptures (locatedSpan original) captured body typ
                    body' <- specializeExpr [] capturedBody
                    let binding =
                          ( functionName info <> "_espec"
                          , target
                          , capturedType
                          , body'
                          , functionUrl info
                          )
                    modify' $ \state -> state
                      {specializeGenerated = binding : specializeGenerated state}
                    pure (specializedApplication original target free remaining)

descend :: Environment -> C.Expr -> SpecializeM C.Expr
descend environment expression = case locatedValue expression of
  C.ECon classification constructor arguments payload -> do
    payload' <- traverse (specializeExpr environment) payload
    pure (at (C.ECon classification constructor arguments payload'))
  C.EFfiApp moduleName name arguments -> do
    arguments' <- mapM typed arguments
    pure (at (C.EFfiApp moduleName name arguments'))
  C.EApp function argument -> do
    function' <- specializeExpr environment function
    argument' <- specializeExpr environment argument
    pure (at (C.EApp function' argument'))
  C.EAbs name domain range body -> do
    body' <- specializeExpr ((name, domain) : environment) body
    pure (at (C.EAbs name domain range body'))
  C.ECApp function argument -> do
    function' <- specializeExpr environment function
    pure (at (C.ECApp function' argument))
  C.ECAbs name kind body -> do
    body' <- specializeExpr environment body
    pure (at (C.ECAbs name kind body'))
  C.EKAbs name body -> do
    body' <- specializeExpr environment body
    pure (at (C.EKAbs name body'))
  C.EKApp function kind -> do
    function' <- specializeExpr environment function
    pure (at (C.EKApp function' kind))
  C.ERecord fields -> do
    fields' <- mapM field fields
    pure (at (C.ERecord fields'))
  C.EField record name typ rest -> do
    record' <- specializeExpr environment record
    pure (at (C.EField record' name typ rest))
  C.EConcat left leftRow right rightRow -> do
    left' <- specializeExpr environment left
    right' <- specializeExpr environment right
    pure (at (C.EConcat left' leftRow right' rightRow))
  C.ECut record name typ rest -> do
    record' <- specializeExpr environment record
    pure (at (C.ECut record' name typ rest))
  C.ECutMulti record fields rest -> do
    record' <- specializeExpr environment record
    pure (at (C.ECutMulti record' fields rest))
  C.ECase scrutinee branches input result -> do
    scrutinee' <- specializeExpr environment scrutinee
    branches' <- mapM branch branches
    pure (at (C.ECase scrutinee' branches' input result))
  C.EWrite value -> at . C.EWrite <$> specializeExpr environment value
  C.EClosure identifier captures -> do
    captures' <- mapM (specializeExpr environment) captures
    pure (at (C.EClosure identifier captures'))
  C.ELet name typ value body -> do
    value' <- specializeExpr environment value
    body' <- specializeExpr ((name, typ) : environment) body
    pure (at (C.ELet name typ value' body'))
  C.EServerCall identifier arguments typ failureMode -> do
    arguments' <- mapM (specializeExpr environment) arguments
    pure (at (C.EServerCall identifier arguments' typ failureMode))
  _ -> pure expression
  where
    at = Located (locatedSpan expression)
    typed (value, typ) = (,typ) <$> specializeExpr environment value
    field (name, value, typ) = (,,) name <$> specializeExpr environment value <*> pure typ
    branch (pattern', body) = do
      body' <- specializeExpr (patternBindings pattern' <> environment) body
      pure (pattern', body')

runtimeApplication :: C.Expr -> Maybe (C.GlobalId, [C.Expr])
runtimeApplication expression = case go expression [] of
  (Located _ (C.ENamed identifier), arguments@(_ : _)) -> Just (identifier, arguments)
  _ -> Nothing
  where
    go current arguments = case locatedValue current of
      C.EApp function argument -> go function (argument : arguments)
      _ -> (current, arguments)

rebuildRuntimeApplication :: C.Expr -> C.GlobalId -> [C.Expr] -> C.Expr
rebuildRuntimeApplication original identifier =
  foldl' (\function argument -> Located (locatedSpan original) (C.EApp function argument))
    (Located (locatedSpan original) (C.ENamed identifier))

specializedApplication :: C.Expr -> C.GlobalId -> [Int] -> [C.Expr] -> C.Expr
specializedApplication original identifier free remaining =
  rebuildRuntimeApplication original identifier (captureArguments <> remaining)
  where
    -- Captures are abstracted by ascending original index, which makes the
    -- last one outermost; apply them in the corresponding reverse order.
    captureArguments =
      [Located (locatedSpan original) (C.ERel index) | index <- reverse free]

splitSpecializedArguments
  :: Set.Set C.GlobalId
  -> Int
  -> C.Con
  -> [C.Expr]
  -> Maybe ([C.Expr], [C.Expr])
splitSpecializedArguments known = go True []
  where
    go initial selected count typ arguments = case (count > 0, locatedValue typ, arguments) of
      (True, C.TFun domain result, argument : rest)
        | initial || functionInside known domain ->
            go (initial && not (functionInside known domain)) (argument : selected) (count - 1) result rest
      _
        | initial -> Nothing
        | otherwise -> Just (reverse selected, arguments)

trimArguments :: [C.Expr] -> C.Con -> C.Expr -> Maybe (C.Expr, C.Con)
trimArguments [] typ expression = Just (expression, typ)
trimArguments (argument : rest) typ expression = case (locatedValue typ, locatedValue expression) of
  (C.TFun _ result, C.EAbs _ _ _ body) ->
    trimArguments rest result (Substitute.substituteValue 0 argument body)
  _ -> Nothing

abstractCaptures
  :: Span
  -> [(String, C.Con)]
  -> C.Expr
  -> C.Con
  -> (C.Expr, C.Con)
abstractCaptures location captures body typ = foldl' abstract (body, typ) captures
  where
    abstract (nestedBody, nestedType) (name, capturedType) =
      ( Located location (C.EAbs name capturedType nestedType nestedBody)
      , Located location (C.TFun capturedType nestedType)
      )

relativeExpression :: C.Expr -> Bool
relativeExpression expression = case locatedValue expression of
  C.ERel {} -> True
  _ -> False

environmentAt :: Int -> Environment -> Maybe (String, C.Con)
environmentAt index environment
  | index < 0 = Nothing
  | otherwise = case drop index environment of
      value : _ -> Just value
      [] -> Nothing

patternBindings :: C.Pattern -> Environment
patternBindings pattern' = case locatedValue pattern' of
  C.PVar name typ -> [(name, typ)]
  C.PPrim {} -> []
  C.PCon _ _ _ nested -> maybe [] patternBindings nested
  C.PRecord fields ->
    reverse (concatMap (reverse . patternBindings . middle) fields)
  where
    middle (_, value, _) = value

freeVariables :: C.Expr -> Set.Set Int
freeVariables = go 0
  where
    go bound expression = direct bound expression <> children bound expression
    direct bound expression = case locatedValue expression of
      C.ERel index | index >= bound -> Set.singleton (index - bound)
      _ -> Set.empty
    children bound expression = case locatedValue expression of
      C.ECon _ _ _ payload -> maybe Set.empty (go bound) payload
      C.EFfiApp _ _ arguments -> Set.unions [go bound value | (value, _) <- arguments]
      C.EApp function argument -> go bound function <> go bound argument
      C.EAbs _ _ _ body -> go (bound + 1) body
      C.ECApp function _ -> go bound function
      C.ECAbs _ _ body -> go bound body
      C.EKAbs _ body -> go bound body
      C.EKApp function _ -> go bound function
      C.ERecord fields -> Set.unions [go bound value | (_, value, _) <- fields]
      C.EField record _ _ _ -> go bound record
      C.EConcat left _ right _ -> go bound left <> go bound right
      C.ECut record _ _ _ -> go bound record
      C.ECutMulti record _ _ -> go bound record
      C.ECase scrutinee branches _ _ ->
        go bound scrutinee
          <> Set.unions
            [go (bound + Substitute.patternBindingCount pattern') body | (pattern', body) <- branches]
      C.EWrite value -> go bound value
      C.EClosure _ captures -> Set.unions (map (go bound) captures)
      C.ELet _ _ value body -> go bound value <> go (bound + 1) body
      C.EServerCall _ arguments _ _ -> Set.unions (map (go bound) arguments)
      _ -> Set.empty

squishVariables :: [Int] -> C.Expr -> C.Expr
squishVariables free = go 0
  where
    positions = Map.fromList (zip free [0 ..])
    go bound expression = expression {locatedValue = case locatedValue expression of
      C.ERel index
        | index >= bound
        , Just position <- Map.lookup (index - bound) positions ->
            C.ERel (position + bound)
      C.ECon classification constructor arguments payload -> C.ECon classification constructor arguments (fmap (go bound) payload)
      C.EFfiApp moduleName name arguments -> C.EFfiApp moduleName name [(go bound value, typ) | (value, typ) <- arguments]
      C.EApp function argument -> C.EApp (go bound function) (go bound argument)
      C.EAbs name domain range body -> C.EAbs name domain range (go (bound + 1) body)
      C.ECApp function argument -> C.ECApp (go bound function) argument
      C.ECAbs name kind body -> C.ECAbs name kind (go bound body)
      C.EKAbs name body -> C.EKAbs name (go bound body)
      C.EKApp function kind -> C.EKApp (go bound function) kind
      C.ERecord fields -> C.ERecord [(name, go bound value, typ) | (name, value, typ) <- fields]
      C.EField record name typ rest -> C.EField (go bound record) name typ rest
      C.EConcat left leftRow right rightRow -> C.EConcat (go bound left) leftRow (go bound right) rightRow
      C.ECut record name typ rest -> C.ECut (go bound record) name typ rest
      C.ECutMulti record fields rest -> C.ECutMulti (go bound record) fields rest
      C.ECase scrutinee branches input result -> C.ECase
        (go bound scrutinee)
        [(pattern', go (bound + Substitute.patternBindingCount pattern') body) | (pattern', body) <- branches]
        input result
      C.EWrite value -> C.EWrite (go bound value)
      C.EClosure identifier captures -> C.EClosure identifier (map (go bound) captures)
      C.ELet name typ value body -> C.ELet name typ (go bound value) (go (bound + 1) body)
      C.EServerCall identifier arguments typ failureMode -> C.EServerCall identifier (map (go bound) arguments) typ failureMode
      other -> other}

constantArguments :: Set.Set C.GlobalId -> C.Expr -> Int
constantArguments family = enter 0
  where
    enter depth expression = case locatedValue expression of
      C.EAbs _ _ _ body -> enter (depth + 1) body
      _ -> calculate depth expression

    calculate depth expression = case locatedValue expression of
      C.EPrim {} -> largeCount
      C.ERel {} -> largeCount
      C.ENamed identifier
        | Set.member identifier family -> 0
        | otherwise -> largeCount
      C.ECon _ _ _ payload -> maybe largeCount (calculate depth) payload
      C.EFfi {} -> largeCount
      C.EFfiApp _ _ arguments -> minimum (largeCount : [calculate depth value | (value, _) <- arguments])
      C.EApp function argument -> case runtimeApplication expression of
        Just (identifier, arguments)
          | Set.member identifier family -> visitArguments depth 0 arguments
        _ -> min (calculate depth function) (calculate depth argument)
      C.EAbs _ _ _ body -> calculate (depth + 1) body
      C.ECApp function _ -> calculate depth function
      C.ECAbs _ _ body -> calculate depth body
      C.EKAbs _ body -> calculate depth body
      C.EKApp function _ -> calculate depth function
      C.ERecord fields -> minimum (largeCount : [calculate depth value | (_, value, _) <- fields])
      C.EField record _ _ _ -> calculate depth record
      C.EConcat left _ right _ -> min (calculate depth left) (calculate depth right)
      C.ECut record _ _ _ -> calculate depth record
      C.ECutMulti record _ _ -> calculate depth record
      C.ECase scrutinee branches _ _ ->
        minimum
          ( calculate depth scrutinee
          : [calculate (depth + Substitute.patternBindingCount pattern') body | (pattern', body) <- branches]
          )
      C.EWrite value -> calculate depth value
      C.EClosure _ captures -> minimum (largeCount : map (calculate depth) captures)
      C.ELet _ _ value body -> min (calculate depth value) (calculate (depth + 1) body)
      C.EServerCall _ arguments _ _ -> minimum (largeCount : map (calculate depth) arguments)

    visitArguments depth count arguments = case arguments of
      Located _ (C.ERel index) : rest
        | index == depth - 1 - count -> visitArguments depth (count + 1) rest
      _ -> minimum (count : map (calculate depth) arguments)

largeCount :: Int
largeCount = maxBound `div` 4

collectFunctionTypes :: C.File -> Set.Set C.GlobalId
collectFunctionTypes = foldl' declaration Set.empty
  where
    declaration known source = case locatedValue source of
      C.DCon _ identifier _ definition
        | functionInside known definition -> Set.insert identifier known
      C.DDatatype definitions
        | any (datatypeContainsFunction known) definitions ->
            foldl' (flip Set.insert) known [identifier | (_, identifier, _, _) <- definitions]
      _ -> known
    datatypeContainsFunction known (_, _, _, constructors) =
      any (maybe False (functionInside known) . third) constructors
    third (_, _, value) = value

functionInside :: Set.Set C.GlobalId -> C.Con -> Bool
functionInside known constructor = direct || children
  where
    direct = case locatedValue constructor of
      C.TFun {} -> True
      C.TCFun {} -> True
      C.CFfi "Basis" name -> name `elem`
        [ "transaction"
        , "eq"
        , "num"
        , "ord"
        , "show"
        , "read"
        , "sql_injectable_prim"
        , "sql_injectable"
        ]
      C.CNamed identifier -> Set.member identifier known
      _ -> False
    children = case locatedValue constructor of
      C.TFun domain result -> functionInside known domain || functionInside known result
      C.TCFun _ _ body -> functionInside known body
      C.TRecord row -> functionInside known row
      C.CApp function argument -> functionInside known function || functionInside known argument
      C.CAbs _ _ body -> functionInside known body
      C.CKAbs _ body -> functionInside known body
      C.CKApp function _ -> functionInside known function
      C.TKFun _ body -> functionInside known body
      C.CRecord _ fields -> any (functionInside known . fst) fields || any (functionInside known . snd) fields
      C.CConcat left right -> functionInside known left || functionInside known right
      C.CTuple elements -> any (functionInside known) elements
      C.CProj tuple _ -> functionInside known tuple
      _ -> False

semanticCon :: C.Con -> C.Con
semanticCon = Substitute.semanticCon

semanticExpr :: C.Expr -> C.Expr
semanticExpr expression = Located noSpan $ case locatedValue expression of
  C.ECon classification constructor arguments payload ->
    C.ECon classification (semanticPatCon constructor) (map semanticCon arguments) (fmap semanticExpr payload)
  C.EFfiApp moduleName name arguments ->
    C.EFfiApp moduleName name [(semanticExpr value, semanticCon typ) | (value, typ) <- arguments]
  C.EApp function argument -> C.EApp (semanticExpr function) (semanticExpr argument)
  C.EAbs name domain range body -> C.EAbs name (semanticCon domain) (semanticCon range) (semanticExpr body)
  C.ECApp function argument -> C.ECApp (semanticExpr function) (semanticCon argument)
  C.ECAbs name kind body -> C.ECAbs name (Substitute.semanticKind kind) (semanticExpr body)
  C.EKAbs name body -> C.EKAbs name (semanticExpr body)
  C.EKApp function kind -> C.EKApp (semanticExpr function) (Substitute.semanticKind kind)
  C.ERecord fields -> C.ERecord [(semanticCon name, semanticExpr value, semanticCon typ) | (name, value, typ) <- fields]
  C.EField record name typ rest -> C.EField (semanticExpr record) (semanticCon name) (semanticCon typ) (semanticCon rest)
  C.EConcat left leftRow right rightRow -> C.EConcat (semanticExpr left) (semanticCon leftRow) (semanticExpr right) (semanticCon rightRow)
  C.ECut record name typ rest -> C.ECut (semanticExpr record) (semanticCon name) (semanticCon typ) (semanticCon rest)
  C.ECutMulti record fields rest -> C.ECutMulti (semanticExpr record) (semanticCon fields) (semanticCon rest)
  C.ECase scrutinee branches input result -> C.ECase
    (semanticExpr scrutinee)
    [(semanticPattern pattern', semanticExpr body) | (pattern', body) <- branches]
    (semanticCon input)
    (semanticCon result)
  C.EWrite value -> C.EWrite (semanticExpr value)
  C.EClosure identifier captures -> C.EClosure identifier (map semanticExpr captures)
  C.ELet name typ value body -> C.ELet name (semanticCon typ) (semanticExpr value) (semanticExpr body)
  C.EServerCall identifier arguments typ failureMode -> C.EServerCall identifier (map semanticExpr arguments) (semanticCon typ) failureMode
  other -> other

semanticPattern :: C.Pattern -> C.Pattern
semanticPattern pattern' = Located noSpan $ case locatedValue pattern' of
  C.PVar name typ -> C.PVar name (semanticCon typ)
  C.PCon classification constructor arguments nested ->
    C.PCon classification (semanticPatCon constructor) (map semanticCon arguments) (fmap semanticPattern nested)
  C.PRecord fields -> C.PRecord [(name, semanticPattern nested, semanticCon typ) | (name, nested, typ) <- fields]
  other -> other

semanticPatCon :: C.PatCon -> C.PatCon
semanticPatCon constructor = case constructor of
  C.PConFfi moduleName datatype parameters name payload classification ->
    C.PConFfi moduleName datatype parameters name (fmap semanticCon payload) classification
  other -> other

freshGlobal :: SpecializeM C.GlobalId
freshGlobal = do
  next <- gets specializeNextId
  modify' $ \state -> state {specializeNextId = next + 1}
  pure (C.GlobalId next)

maximumGlobal :: C.File -> Int
maximumGlobal file = maximum (0 : concatMap declarationIds file)
  where
    declarationIds declaration = case locatedValue declaration of
      C.DCon _ identifier _ _ -> one identifier
      C.DDatatype definitions -> concat
        [ one identifier <> [C.unGlobalId constructor | (_, constructor, _) <- constructors]
        | (_, identifier, _, constructors) <- definitions
        ]
      C.DVal _ identifier _ _ _ -> one identifier
      C.DValRec bindings -> [C.unGlobalId identifier | (_, identifier, _, _, _) <- bindings]
      C.DExport _ identifier _ -> one identifier
      C.DTable _ identifier _ _ _ _ _ _ -> one identifier
      C.DSequence _ identifier _ -> one identifier
      C.DView _ identifier _ _ _ -> one identifier
      C.DCookie _ identifier _ _ -> one identifier
      C.DStyle _ identifier _ -> one identifier
      C.DOnError identifier -> one identifier
      _ -> []
    one = pure . C.unGlobalId
