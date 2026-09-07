{-# LANGUAGE DerivingStrategies #-}

-- | Ur/Web's @Unpoly@ pass: specialize named constructor-polymorphic values.
-- Every concrete instantiation receives one stable global identity.  Recursive
-- families are registered together before any generated body is traversed.
module Vr.Core.Specialize
  ( specializeFile
  ) where

import Control.Monad.State.Strict (StateT (..), get, gets, modify', runStateT)
import Control.Monad (foldM, forM)
import qualified Data.Map.Strict as Map
import qualified Vr.Core.Substitute as Substitute
import qualified Vr.Core.Syntax as C
import Vr.Source (Diagnostic, DiagnosticPhase (MonoPhase), Located (..), Span, diagnostic)

data StaticApplication = ConstructorArgument !C.Con
  deriving stock (Eq, Ord, Show)

data Application = StaticApplication !Span !StaticApplication
  deriving stock (Eq, Ord, Show)

data ValueMember = ValueMember !String !C.GlobalId !C.Con !C.Expr !String
  deriving stock (Eq, Ord, Show)

data Definition
  = ValueGroup ![C.Kind] ![ValueMember]
  deriving stock (Eq, Ord, Show)

data Generated = GeneratedValue !String !C.GlobalId !C.Con !C.Expr !String !Span
  deriving stock (Eq, Ord, Show)

data SpecializeState = SpecializeState
  { specializeNextId :: !Int
  , specializeDefinitions :: !(Map.Map C.GlobalId Definition)
  , specializeMemo :: !(Map.Map (C.GlobalId, [StaticApplication]) C.GlobalId)
  , specializeGenerated :: ![[Generated]]
  }

type SpecializeM = StateT SpecializeState (Either Diagnostic)

specializeFile :: C.File -> Either [Diagnostic] C.File
specializeFile file = case runStateT (foldM specializeTopLevel [] file) initial of
  Left problem -> Left [problem]
  Right (declarations, _) -> Right declarations
  where
    initial = SpecializeState (maximumGlobal file + 1) (collectDefinitions file) Map.empty []

-- Ur/Web inserts specializations generated while visiting a declaration just
-- before that declaration.  Nested specializations precede the specialization
-- whose body requested them.
specializeTopLevel :: [C.Decl] -> C.Decl -> SpecializeM [C.Decl]
specializeTopLevel declarations declaration = do
  declarations' <- specializeDeclaration declaration
  generated <- gets specializeGenerated
  modify' $ \state -> state {specializeGenerated = []}
  pure (declarations <> materializeGenerated (reverse generated) <> declarations')

specializeDeclaration :: C.Decl -> SpecializeM [C.Decl]
specializeDeclaration declaration = case locatedValue declaration of
  C.DCon name identifier kind definition ->
    pure [declaration {locatedValue = C.DCon name identifier kind (Substitute.normalizeCon definition)}]
  C.DForeign moduleName name typ ->
    pure [declaration {locatedValue = C.DForeign moduleName name (Substitute.normalizeCon typ)}]
  C.DDatatype definitions ->
    pure [declaration {locatedValue = C.DDatatype (map normalizeDatatype definitions)}]
  C.DVal name identifier typ expression url -> do
    expression' <- specializeExpr expression
    pure [declaration {locatedValue = C.DVal name identifier (Substitute.normalizeCon typ) expression' url}]
  C.DValRec bindings -> do
    bindings' <- mapM specializeMonomorphicBinding bindings
    pure [declaration {locatedValue = C.DValRec bindings'} | not (null bindings')]
  C.DExport {} -> pure [declaration]
  C.DTable name identifier row sqlName primary keys constraints uniques -> do
    primary' <- specializeExpr primary
    constraints' <- specializeExpr constraints
    pure [declaration {locatedValue = C.DTable name identifier (norm row) sqlName primary' (norm keys) constraints' (norm uniques)}]
  C.DSequence {} -> pure [declaration]
  C.DView name identifier sqlName expression row -> do
    expression' <- specializeExpr expression
    pure [declaration {locatedValue = C.DView name identifier sqlName expression' (norm row)}]
  C.DIndex table modes -> do
    table' <- specializeExpr table
    modes' <- specializeExpr modes
    pure [declaration {locatedValue = C.DIndex table' modes'}]
  C.DDatabase {} -> pure [declaration]
  C.DCookie name identifier typ runtimeName ->
    pure [declaration {locatedValue = C.DCookie name identifier (norm typ) runtimeName}]
  C.DStyle {} -> pure [declaration]
  C.DTask kind body -> do
    kind' <- specializeExpr kind
    body' <- specializeExpr body
    pure [declaration {locatedValue = C.DTask kind' body'}]
  C.DPolicy expression -> do
    expression' <- specializeExpr expression
    pure [declaration {locatedValue = C.DPolicy expression'}]
  C.DOnError {} -> pure [declaration]
  where norm = Substitute.normalizeCon

normalizeDatatype
  :: (String, C.GlobalId, [String], [(String, C.GlobalId, Maybe C.Con)])
  -> (String, C.GlobalId, [String], [(String, C.GlobalId, Maybe C.Con)])
normalizeDatatype (name, identifier, parameters, constructors) =
  (name, identifier, parameters, [(constructor, constructorId, fmap Substitute.normalizeCon payload) | (constructor, constructorId, payload) <- constructors])

specializeMonomorphicBinding
  :: (String, C.GlobalId, C.Con, C.Expr, String)
  -> SpecializeM (String, C.GlobalId, C.Con, C.Expr, String)
specializeMonomorphicBinding (name, identifier, typ, expression, url) =
  (,,,,) name identifier (Substitute.normalizeCon typ) <$> specializeExpr expression <*> pure url

specializeExpr :: C.Expr -> SpecializeM C.Expr
specializeExpr original = do
  replaced <- specializeNamedHead (Substitute.normalizeExprHead original)
  case locatedValue replaced of
    C.ECon classification constructor arguments payload -> do
      payload' <- traverse specializeExpr payload
      pure replaced {locatedValue = C.ECon classification constructor (map Substitute.normalizeCon arguments) payload'}
    C.EFfiApp moduleName name arguments -> do
      arguments' <- mapM typedExpr arguments
      pure replaced {locatedValue = C.EFfiApp moduleName name arguments'}
    C.EApp function argument -> binary replaced C.EApp function argument
    C.EAbs name domain range body -> do
      body' <- specializeExpr body
      pure replaced {locatedValue = C.EAbs name (norm domain) (norm range) body'}
    C.ECApp function argument -> do
      function' <- specializeExpr function
      specializeNamedHead replaced {locatedValue = C.ECApp function' (norm argument)}
    C.ECAbs name kind body -> do
      body' <- specializeExpr body
      pure replaced {locatedValue = C.ECAbs name kind body'}
    C.EKAbs name body -> do
      body' <- specializeExpr body
      pure replaced {locatedValue = C.EKAbs name body'}
    C.EKApp function kind -> do
      function' <- specializeExpr function
      specializeNamedHead replaced {locatedValue = C.EKApp function' kind}
    C.ERecord fields -> do
      fields' <- mapM recordField fields
      pure replaced {locatedValue = C.ERecord fields'}
    C.EField record field typ rest -> do
      record' <- specializeExpr record
      pure replaced {locatedValue = C.EField record' (norm field) (norm typ) (norm rest)}
    C.EConcat left leftRow right rightRow -> do
      left' <- specializeExpr left
      right' <- specializeExpr right
      pure replaced {locatedValue = C.EConcat left' (norm leftRow) right' (norm rightRow)}
    C.ECut record field typ rest -> do
      record' <- specializeExpr record
      pure replaced {locatedValue = C.ECut record' (norm field) (norm typ) (norm rest)}
    C.ECutMulti record fields rest -> do
      record' <- specializeExpr record
      pure replaced {locatedValue = C.ECutMulti record' (norm fields) (norm rest)}
    C.ECase scrutinee branches input result -> do
      scrutinee' <- specializeExpr scrutinee
      branches' <- mapM branch branches
      pure replaced {locatedValue = C.ECase scrutinee' branches' (norm input) (norm result)}
    C.EWrite value -> unary replaced C.EWrite value
    C.EClosure identifier values -> do
      values' <- mapM specializeExpr values
      pure replaced {locatedValue = C.EClosure identifier values'}
    C.ELet name typ value body -> do
      value' <- specializeExpr value
      body' <- specializeExpr body
      pure replaced {locatedValue = C.ELet name (norm typ) value' body'}
    C.EServerCall identifier values typ failureMode -> do
      values' <- mapM specializeExpr values
      pure replaced {locatedValue = C.EServerCall identifier values' (norm typ) failureMode}
    _ -> pure replaced
  where
    norm = Substitute.normalizeCon
    typedExpr (expression, typ) = (,) <$> specializeExpr expression <*> pure (norm typ)
    recordField (field, value, typ) = (,,) (norm field) <$> specializeExpr value <*> pure (norm typ)
    branch (pattern', body) = (,) (normalizePattern pattern') <$> specializeExpr body
    unary container make value = do
      value' <- specializeExpr value
      pure container {locatedValue = make value'}
    binary container make left right = do
      left' <- specializeExpr left
      right' <- specializeExpr right
      pure container {locatedValue = make left' right'}

specializeNamedHead :: C.Expr -> SpecializeM C.Expr
specializeNamedHead expression = case collectApplications expression of
  (Located at (C.ENamed identifier), applications) -> do
    state <- get
    case Map.lookup identifier (specializeDefinitions state) of
      Nothing -> pure expression
      Just definition ->
        let arguments = [argument | StaticApplication _ argument <- applications]
         in case definitionStaticArity identifier definition of
              Nothing -> pure expression
              Just arity
                | null arguments || any staticOpen arguments || length arguments > arity -> pure expression
                | otherwise -> do
                    target <- requestSpecialization at identifier arguments definition
                    rebuildApplications (Located (locatedSpan expression) (C.ENamed target)) applications
  _ -> pure expression

rebuildApplications :: C.Expr -> [Application] -> SpecializeM C.Expr
rebuildApplications = foldM step
  where
    step function application = case application of
      StaticApplication {} -> pure function

requestSpecialization
  :: Span
  -> C.GlobalId
  -> [StaticApplication]
  -> Definition
  -> SpecializeM C.GlobalId
requestSpecialization at sourceId arguments definition = do
  state <- get
  let normalizedArguments = map normalizeStatic arguments
      key = (sourceId, normalizedArguments)
  case Map.lookup key (specializeMemo state) of
    Just identifier -> pure identifier
    Nothing -> do
      case definition of
        ValueGroup kinds members -> do
          let allocated = zip members [specializeNextId state ..]
              identities =
                [ (memberId, C.GlobalId fresh)
                | (ValueMember _ memberId _ _ _, fresh) <- allocated
                ]
              identifier = case lookup sourceId identities of
                Just target -> target
                Nothing -> C.GlobalId (specializeNextId state)
              memo' = foldl
                (\memo (memberId, target) -> Map.insert (memberId, normalizedArguments) target memo)
                (specializeMemo state)
                identities
          -- Register every member before descending into any body.  Recursive
          -- and mutually recursive references therefore resolve to this same
          -- generated family instead of spawning duplicate specializations.
          modify' $ \current ->
            current
              { specializeNextId = specializeNextId current + length members
              , specializeMemo = memo'
              }
          instantiated <- forM allocated $ \(ValueMember name _ typ expression url, fresh) -> do
            (typ', expression') <- instantiateValue at normalizedArguments typ expression
            pure (ValueMember (specializedName name normalizedArguments) (C.GlobalId fresh) typ' expression' url)
          let remainingKinds = drop (length normalizedArguments) kinds
              generatedDefinition = ValueGroup remainingKinds instantiated
              generatedDefinitions = foldl
                (\definitions (ValueMember _ generatedId _ _ _) -> Map.insert generatedId generatedDefinition definitions)
                (specializeDefinitions state)
                instantiated
          -- Partially specialized values remain eligible for a later Unpoly
          -- request, exactly like the generated entries in the reference
          -- pass's function table.
          modify' $ \current -> current {specializeDefinitions = generatedDefinitions}
          generated <- forM instantiated $ \(ValueMember name generatedId typ expression url) -> do
            expression' <- specializeExpr expression
            pure (GeneratedValue name generatedId typ expression' url at)
          modify' $ \current -> current {specializeGenerated = generated : specializeGenerated current}
          pure identifier

instantiateValue
  :: Span
  -> [StaticApplication]
  -> C.Con
  -> C.Expr
  -> SpecializeM (C.Con, C.Expr)
instantiateValue at arguments = go arguments
  where
    go [] typ expression = pure (Substitute.normalizeCon typ, Substitute.normalizeExprHead expression)
    go (argument : rest) typ expression = case (argument, locatedValue (Substitute.normalizeCon typ)) of
      (ConstructorArgument constructor, C.TCFun _ _ bodyType) ->
        let expression' = case locatedValue (Substitute.normalizeExprHead expression) of
              C.ECAbs _ _ body -> Substitute.substituteConInExpr 0 constructor body
              _ -> expression
         in go rest (Substitute.substituteCon 0 constructor bodyType) expression'
      _ -> liftFailure at "specialization-shape" "Static arguments do not match the polymorphic value's binders"

collectApplications :: C.Expr -> (C.Expr, [Application])
collectApplications expression = case locatedValue expression of
  C.ECApp function argument -> let (headExpression, arguments) = collectApplications function in (headExpression, arguments <> [StaticApplication (locatedSpan expression) (ConstructorArgument argument)])
  _ -> (expression, [])

definitionStaticArity :: C.GlobalId -> Definition -> Maybe Int
definitionStaticArity sourceId definition = case definition of
  ValueGroup kinds members -> case [length kinds | ValueMember _ identifier _ _ _ <- members, identifier == sourceId] of
    arity : _ -> Just arity
    [] -> Nothing

normalizeStatic :: StaticApplication -> StaticApplication
normalizeStatic argument = case argument of
  ConstructorArgument constructor -> ConstructorArgument (Substitute.semanticCon constructor)

-- Ur/Web leaves an application alone while any static operand still depends
-- on an enclosing binder.  A later traversal/pass may see it again after the
-- binder has been instantiated.  Specializing an open recursive call would
-- create a bogus erased instance in addition to the concrete one.
staticOpen :: StaticApplication -> Bool
staticOpen argument = case argument of
  ConstructorArgument constructor -> openCon 0 constructor

openCon :: Int -> C.Con -> Bool
openCon depth constructor = case locatedValue constructor of
  C.CRel index -> index >= depth
  C.TFun domain range -> openCon depth domain || openCon depth range
  C.TCFun _ _ body -> openCon (depth + 1) body
  C.TRecord row -> openCon depth row
  C.CApp function value -> openCon depth function || openCon depth value
  C.CAbs _ _ body -> openCon (depth + 1) body
  C.CKAbs _ body -> openCon depth body
  C.CKApp function _ -> openCon depth function
  C.TKFun _ body -> openCon depth body
  C.CRecord _ fields -> any (openCon depth . fst) fields || any (openCon depth . snd) fields
  C.CConcat left right -> openCon depth left || openCon depth right
  C.CTuple elements -> any (openCon depth) elements
  C.CProj tuple _ -> openCon depth tuple
  _ -> False

normalizePattern :: C.Pattern -> C.Pattern
normalizePattern pattern' = pattern' {locatedValue = case locatedValue pattern' of
  C.PVar name typ -> C.PVar name (Substitute.normalizeCon typ)
  C.PCon classification constructor arguments nested -> C.PCon classification constructor (map Substitute.normalizeCon arguments) (fmap normalizePattern nested)
  C.PRecord fields -> C.PRecord [(name, normalizePattern nested, Substitute.normalizeCon typ) | (name, nested, typ) <- fields]
  other -> other}

collectDefinitions :: C.File -> Map.Map C.GlobalId Definition
collectDefinitions = Map.fromList . concatMap declarationDefinitions
  where
    declarationDefinitions declaration = case locatedValue declaration of
      C.DVal name identifier typ expression url ->
        let member = ValueMember name identifier typ expression url
         in [(identifier, ValueGroup (leadingConstructorKinds expression) [member])]
      C.DValRec bindings -> recursiveDefinitions bindings
      _ -> []

    recursiveDefinitions bindings =
      let members = [ValueMember name identifier typ expression url | (name, identifier, typ, expression, url) <- bindings]
       in case members of
            [] -> []
            ValueMember _ _ _ firstExpression _ : _ ->
              let kinds = leadingConstructorKinds firstExpression
                  sameBinders (ValueMember _ _ _ expression _) =
                    map Substitute.semanticKind (leadingConstructorKinds expression)
                      == map Substitute.semanticKind kinds
                  identifiers = Map.fromList [(identifier, ()) | ValueMember _ identifier _ _ _ <- members]
                  regular (ValueMember _ _ _ expression _) =
                    not (hasIrregularRecursiveCall identifiers (length kinds) (dropConstructorAbstractions (length kinds) expression))
               in if all sameBinders members && all regular members
                    then [(identifier, ValueGroup kinds members) | ValueMember _ identifier _ _ _ <- members]
                    else []

leadingConstructorKinds :: C.Expr -> [C.Kind]
leadingConstructorKinds expression = case locatedValue expression of
  C.ECAbs _ kind body -> kind : leadingConstructorKinds body
  _ -> []

dropConstructorAbstractions :: Int -> C.Expr -> C.Expr
dropConstructorAbstractions count expression
  | count <= 0 = expression
  | otherwise = case locatedValue expression of
      C.ECAbs _ _ body -> dropConstructorAbstractions (count - 1) body
      _ -> expression

-- A recursive family is regular only when every recursive constructor
-- application passes the family's leading parameters back unchanged.  This is
-- the same de Bruijn-index test used by Ur/Web's Unpoly pass; declining an
-- irregular family prevents an infinite chain such as f[a] -> f[list a].
hasIrregularRecursiveCall :: Map.Map C.GlobalId () -> Int -> C.Expr -> Bool
hasIrregularRecursiveCall family parameterCount = go 0
  where
    go constructorDepth expression = irregularAt constructorDepth expression || case locatedValue expression of
      C.ECon _ _ _ payload -> maybe False (go constructorDepth) payload
      C.EFfiApp _ _ arguments -> any (go constructorDepth . fst) arguments
      C.EApp function argument -> go constructorDepth function || go constructorDepth argument
      C.EAbs _ _ _ body -> go constructorDepth body
      C.ECApp function _ -> go constructorDepth function
      C.ECAbs _ _ body -> go (constructorDepth + 1) body
      C.EKAbs _ body -> go constructorDepth body
      C.EKApp function _ -> go constructorDepth function
      C.ERecord fields -> any (go constructorDepth . middle) fields
      C.EField record _ _ _ -> go constructorDepth record
      C.EConcat left _ right _ -> go constructorDepth left || go constructorDepth right
      C.ECut record _ _ _ -> go constructorDepth record
      C.ECutMulti record _ _ -> go constructorDepth record
      C.ECase scrutinee branches _ _ -> go constructorDepth scrutinee || any (go constructorDepth . snd) branches
      C.EWrite value -> go constructorDepth value
      C.EClosure _ values -> any (go constructorDepth) values
      C.ELet _ _ value body -> go constructorDepth value || go constructorDepth body
      C.EServerCall _ values _ _ -> any (go constructorDepth) values
      _ -> False

    irregularAt constructorDepth expression = case locatedValue expression of
      C.ECApp function argument -> headIsIrregular constructorDepth argument 1 function
      _ -> False

    headIsIrregular constructorDepth argument position function = case locatedValue function of
      C.ENamed identifier
        | Map.member identifier family -> case locatedValue argument of
            C.CRel index -> index /= parameterCount - position + constructorDepth
            _ -> True
      C.ECApp nested _ -> headIsIrregular constructorDepth argument (position + 1) nested
      _ -> False

    middle (_, value, _) = value

materializeGenerated :: [[Generated]] -> [C.Decl]
materializeGenerated = concatMap materializeGroup

materializeGroup :: [Generated] -> [C.Decl]
materializeGroup generated = valueDeclaration
  where
    values =
      [ ((name, identifier, typ, expression, url), at)
      | GeneratedValue name identifier typ expression url at <- generated
      ]
    valueDeclaration = case values of
      [] -> []
      (_, at) : _ -> [Located at (C.DValRec (map fst values))]

specializedName :: String -> [StaticApplication] -> String
specializedName name _ = name <> "_unpoly"

maximumGlobal :: C.File -> Int
maximumGlobal file = maximum (0 : concatMap declarationIds file)
  where
    declarationIds declaration = case locatedValue declaration of
      C.DCon _ identifier _ _ -> one identifier
      C.DDatatype definitions -> concat [[C.unGlobalId identifier] <> [C.unGlobalId constructor | (_, constructor, _) <- constructors] | (_, identifier, _, constructors) <- definitions]
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

liftFailure :: Span -> String -> String -> SpecializeM value
liftFailure at code message = StateT (const (Left (diagnostic MonoPhase code at message)))
