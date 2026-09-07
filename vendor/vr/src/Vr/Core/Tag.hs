{-# LANGUAGE DerivingStrategies #-}

-- | Extract dynamic link and form handlers before Core reduction.  This is
-- the target-independent semantic part of Ur/Web's Tag pass: handler
-- applications become explicit closures, wrapper exports are generated, and
-- the original handler export is suppressed when the wrapper owns its URL.
module Vr.Core.Tag
  ( tagFile
  ) where

import Control.Monad.State.Strict (State, get, modify', runState)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Vr.Core.Syntax as C
import Vr.Middle (Effect (..), ExportKind (..))
import Vr.Source
  ( Diagnostic
  , DiagnosticPhase (CorePhase)
  , Located (..)
  , Span
  , diagnostic
  )

data ValueInfo = ValueInfo
  { valueName :: !String
  , valueType :: !C.Con
  , valueExpression :: !C.Expr
  , valueUrl :: !String
  }

data Wrapper = Wrapper
  { wrapperIdentifier :: !C.GlobalId
  , wrapperKind :: !ExportKind
  , wrapperLocation :: !Span
  }

data TagState = TagState
  { nextIdentifier :: !Int
  , wrappersByTarget :: !(Map.Map C.GlobalId Wrapper)
  , wrapperOrder :: ![C.GlobalId]
  , pathOwners :: !(Map.Map String (ExportKind, C.GlobalId))
  , problems :: ![Diagnostic]
  }

data ApplicationArgument
  = StaticArgument !C.Con !Span
  | DynamicArgument !C.Expr !Span

-- | Rewrite link/action handler occurrences and append their generated Core
-- wrappers.  Diagnostics are accumulated so duplicate paths and incompatible
-- handler modes are reported together.
tagFile :: C.File -> Either [Diagnostic] C.File
tagFile file =
  let environment = collectValues file
      aliases = collectAliases file
      initial = TagState
        { nextIdentifier = maximumIdentifier file + 1
        , wrappersByTarget = Map.empty
        , wrapperOrder = []
        , pathOwners = Map.empty
        , problems = []
        }
      (rewritten, final) = runState (mapM (tagDeclaration environment aliases) file) initial
      generated = concatMap (generateWrapper environment final) (reverse (wrapperOrder final))
      retained = filter (retainExport environment aliases final) rewritten
   in case reverse (problems final) of
        [] -> Right (retained <> generated)
        diagnostics -> Left diagnostics

tagDeclaration
  :: Map.Map C.GlobalId ValueInfo
  -> Map.Map C.GlobalId C.GlobalId
  -> C.Decl
  -> State TagState C.Decl
tagDeclaration environment aliases declaration = do
  value <- case locatedValue declaration of
    C.DVal name identifier typ expression url ->
      C.DVal name identifier typ <$> tagExpression environment aliases expression <*> pure url
    C.DValRec bindings -> C.DValRec <$> mapM rewriteBinding bindings
    C.DTable name identifier row sqlName primary primaryType constraints constraintsType ->
      C.DTable name identifier row sqlName
        <$> tagExpression environment aliases primary
        <*> pure primaryType
        <*> tagExpression environment aliases constraints
        <*> pure constraintsType
    C.DView name identifier sqlName expression row ->
      C.DView name identifier sqlName <$> tagExpression environment aliases expression <*> pure row
    C.DIndex table modes ->
      C.DIndex <$> tagExpression environment aliases table <*> tagExpression environment aliases modes
    C.DTask schedule body ->
      C.DTask <$> tagExpression environment aliases schedule <*> tagExpression environment aliases body
    C.DPolicy expression -> C.DPolicy <$> tagExpression environment aliases expression
    other -> pure other
  pure declaration {locatedValue = value}
  where
    rewriteBinding (name, identifier, typ, expression, url) =
      (,,,,) name identifier typ <$> tagExpression environment aliases expression <*> pure url

tagExpression
  :: Map.Map C.GlobalId ValueInfo
  -> Map.Map C.GlobalId C.GlobalId
  -> C.Expr
  -> State TagState C.Expr
tagExpression environment aliases source = do
  descended <- case locatedValue source of
    C.ECon classification constructor arguments payload ->
      replace source . C.ECon classification constructor arguments <$> traverse recur payload
    C.EFfiApp moduleName name arguments ->
      replace source . C.EFfiApp moduleName name <$> mapM typed arguments
    C.EApp function argument -> replace source <$> (C.EApp <$> recur function <*> recur argument)
    C.EAbs name domain range body -> replace source . C.EAbs name domain range <$> recur body
    C.ECApp function argument -> replace source . (`C.ECApp` argument) <$> recur function
    C.ECAbs name kind body -> replace source . C.ECAbs name kind <$> recur body
    C.EKAbs name body -> replace source . C.EKAbs name <$> recur body
    C.EKApp function kind -> replace source . (`C.EKApp` kind) <$> recur function
    C.ERecord fields -> replace source . C.ERecord <$> mapM field fields
    C.EField record name before after -> replace source . (\record' -> C.EField record' name before after) <$> recur record
    C.EConcat left leftType right rightType ->
      replace source <$> (C.EConcat <$> recur left <*> pure leftType <*> recur right <*> pure rightType)
    C.ECut record name fieldType resultType ->
      replace source . (\record' -> C.ECut record' name fieldType resultType) <$> recur record
    C.ECutMulti record names resultType ->
      replace source . (\record' -> C.ECutMulti record' names resultType) <$> recur record
    C.ECase scrutinee branches input result ->
      replace source <$> (C.ECase <$> recur scrutinee <*> mapM branch branches <*> pure input <*> pure result)
    C.EWrite expression -> replace source . C.EWrite <$> recur expression
    C.EClosure identifier captures -> replace source . C.EClosure identifier <$> mapM recur captures
    C.ELet name typ value body -> replace source <$> (C.ELet name typ <$> recur value <*> recur body)
    C.EServerCall identifier arguments typ failure ->
      replace source . (\arguments' -> C.EServerCall identifier arguments' typ failure) <$> mapM recur arguments
    _ -> pure source
  tagSpecial environment aliases descended
  where
    recur = tagExpression environment aliases
    typed (expression, typ) = (,typ) <$> recur expression
    field (name, expression, typ) = (,,) name <$> recur expression <*> pure typ
    branch (pattern', expression) = (pattern',) <$> recur expression

tagSpecial
  :: Map.Map C.GlobalId ValueInfo
  -> Map.Map C.GlobalId C.GlobalId
  -> C.Expr
  -> State TagState C.Expr
tagSpecial environment aliases source =
  let (headExpression, arguments) = collectApplication source
      dynamic = [expression | DynamicArgument expression _ <- arguments]
   in case locatedValue headExpression of
        C.EFfi "Basis" "tag"
          | length dynamic == 7 -> rewriteTag environment aliases source headExpression arguments
        C.EFfi "Basis" "url"
          | [target] <- dynamic -> rewriteUrl environment aliases source headExpression arguments target (Link ReadCookieWrite)
        C.EFfi "Basis" "effectfulUrl"
          | [target] <- dynamic -> rewriteUrl environment aliases source headExpression arguments target (Extern ReadCookieWrite)
        _ -> pure source

rewriteTag
  :: Map.Map C.GlobalId ValueInfo
  -> Map.Map C.GlobalId C.GlobalId
  -> C.Expr
  -> C.Expr
  -> [ApplicationArgument]
  -> State TagState C.Expr
rewriteTag environment aliases source headExpression arguments = do
  let dynamicPositions =
        [ (index, expression)
        | (index, DynamicArgument expression _) <- zip [0 :: Int ..] arguments
        ]
  case drop 4 dynamicPositions of
    (attributeIndex, attributes) : _ -> case locatedValue attributes of
      C.ERecord fields -> do
        fields' <- mapM rewriteAttribute fields
        let attributes' = attributes {locatedValue = C.ERecord fields'}
            arguments' = replaceDynamic attributeIndex attributes' arguments
        pure (rebuildApplication headExpression arguments')
      _ -> pure source
    [] -> pure source
  where
    rewriteAttribute (name, expression, typ) = case constructorName name of
      Just "Link" -> tagged "Link" (Link ReadCookieWrite) expression
      Just "Action" -> tagged "Action" (Action ReadWrite) expression
      _ -> pure (name, expression, typ)
    tagged newName kind expression = do
      expression' <- tagHandler environment aliases kind newName expression
      let at = locatedSpan expression
      pure (Located (locatedSpan source) (C.CName newName), expression', ffiString at)

rewriteUrl
  :: Map.Map C.GlobalId ValueInfo
  -> Map.Map C.GlobalId C.GlobalId
  -> C.Expr
  -> C.Expr
  -> [ApplicationArgument]
  -> C.Expr
  -> ExportKind
  -> State TagState C.Expr
rewriteUrl environment aliases source headExpression arguments target kind = case locatedValue target of
  C.ERel 0 -> pure source
  _ -> do
    target' <- tagHandler environment aliases kind "Url" target
    let dynamicIndices = [index | (index, DynamicArgument _ _) <- zip [0 :: Int ..] arguments]
    case dynamicIndices of
      [index] -> pure (rebuildApplication headExpression (replaceDynamic index target' arguments))
      _ -> pure source

tagHandler
  :: Map.Map C.GlobalId ValueInfo
  -> Map.Map C.GlobalId C.GlobalId
  -> ExportKind
  -> String
  -> C.Expr
  -> State TagState C.Expr
tagHandler environment aliases kind attribute expression =
  case unravelHandler environment expression of
    Nothing -> do
      addProblem expression "invalid-handler" ("Invalid " <> attribute <> " expression")
      pure expression
    Just (rawTarget, arguments) -> do
      let target = canonical aliases rawTarget
      case Map.lookup target environment of
        Nothing -> do
          addProblem expression "unknown-handler" ("Unknown handler #" <> show (C.unGlobalId target))
          pure expression
        Just info -> do
          wrapper <- getWrapper expression info target kind
          pure expression {locatedValue = C.EClosure (wrapperIdentifier wrapper) arguments}

getWrapper
  :: C.Expr
  -> ValueInfo
  -> C.GlobalId
  -> ExportKind
  -> State TagState Wrapper
getWrapper source info target kind = do
  state <- get
  case Map.lookup target (wrappersByTarget state) of
    Just wrapper -> do
      if sameMode (wrapperKind wrapper) kind
        then pure ()
        else addProblem source "handler-modes"
          ("Function " <> valueUrl info <> " is needed for multiple modes (link, form, or RPC handler)")
      pure wrapper
    Nothing -> do
      case Map.lookup (valueUrl info) (pathOwners state) of
        Just (ownedKind, owner)
          | owner /= target -> addProblem source "duplicate-handler-path" ("Duplicate URL prefix " <> valueUrl info)
          | not (sameMode ownedKind kind) -> addProblem source "handler-modes"
              ("Function " <> valueUrl info <> " is needed for multiple modes (link, form, or RPC handler)")
        _ -> pure ()
      current <- get
      let identifier = C.GlobalId (nextIdentifier current)
          wrapper = Wrapper identifier kind (locatedSpan source)
      modify' $ \next -> next
        { nextIdentifier = nextIdentifier next + 1
        , wrappersByTarget = Map.insert target wrapper (wrappersByTarget next)
        , wrapperOrder = target : wrapperOrder next
        , pathOwners = Map.insert (valueUrl info) (kind, target) (pathOwners next)
        }
      pure wrapper

generateWrapper :: Map.Map C.GlobalId ValueInfo -> TagState -> C.GlobalId -> [C.Decl]
generateWrapper environment state target = case
  (Map.lookup target environment, Map.lookup target (wrappersByTarget state)) of
    (Just info, Just wrapper) ->
      let at = wrapperLocation wrapper
          unit = unitCon at
          (arguments, _) = unwindFunctions (valueType info)
          appliedHandler = foldl
            (\function (index, _) -> Located at (C.EApp function (Located at (C.ERel index))))
            (Located at (C.ENamed target))
            (zip (reverse [0 .. length arguments - 1]) arguments)
          page = Located at (C.EApp appliedHandler (Located at (C.ERecord [])))
          body = Located at (C.EWrite page)
          transactionUnit = Located at (C.TFun unit unit)
          wrapperType = foldr (\domain range -> Located at (C.TFun domain range)) transactionUnit arguments
          wrapperBody = foldr
            (\(index, domain) nested ->
              Located at (C.EAbs ("x" <> show index) domain (expressionRange index arguments transactionUnit) nested))
            body
            (zip [0 :: Int ..] arguments)
          value = Located at (C.DVal
            ("wrap_" <> valueName info)
            (wrapperIdentifier wrapper)
            wrapperType
            wrapperBody
            (valueUrl info))
          export = Located at (C.DExport (wrapperKind wrapper) (wrapperIdentifier wrapper) False)
       in [value, export]
    _ -> []

-- The result annotation on each nested abstraction is the remaining wrapper
-- function type.  Core consumers use it when specializing and lowering.
expressionRange :: Int -> [C.Con] -> C.Con -> C.Con
expressionRange index arguments result =
  foldr (\domain range -> Located (locatedSpan domain) (C.TFun domain range))
    result
    (drop (index + 1) arguments)

retainExport
  :: Map.Map C.GlobalId ValueInfo
  -> Map.Map C.GlobalId C.GlobalId
  -> TagState
  -> C.Decl
  -> Bool
retainExport environment aliases state declaration = case locatedValue declaration of
  C.DExport kind identifier _ ->
    let target = canonical aliases identifier
     in case Map.lookup target environment >>= \info -> Map.lookup (valueUrl info) (pathOwners state) of
          Just (ownedKind, owner) -> owner == target && not (sameMode ownedKind kind)
          Nothing -> True
  _ -> True

sameMode :: ExportKind -> ExportKind -> Bool
sameMode left right = mode left == mode right
  where
    mode kind = case kind of
      Link _ -> 0 :: Int
      Action _ -> 1
      Rpc _ -> 2
      Extern _ -> 3

unravelHandler :: Map.Map C.GlobalId ValueInfo -> C.Expr -> Maybe (C.GlobalId, [C.Expr])
unravelHandler environment = go []
  where
    go arguments expression = case locatedValue expression of
      C.ENamed identifier -> Just (identifier, arguments)
      C.EApp function argument -> go (argument : arguments) function
      _ -> case
        [ identifier
        | (identifier, info) <- Map.toList environment
        , valueExpression info == expression
        ] of
          identifier : _ -> Just (identifier, arguments)
          [] -> Nothing

collectApplication :: C.Expr -> (C.Expr, [ApplicationArgument])
collectApplication = go []
  where
    go arguments expression = case locatedValue expression of
      C.EApp function argument ->
        go (DynamicArgument argument (locatedSpan expression) : arguments) function
      C.ECApp function argument ->
        go (StaticArgument argument (locatedSpan expression) : arguments) function
      _ -> (expression, arguments)

rebuildApplication :: C.Expr -> [ApplicationArgument] -> C.Expr
rebuildApplication = foldl apply
  where
    apply function argument = case argument of
      StaticArgument constructor at -> Located at (C.ECApp function constructor)
      DynamicArgument expression at -> Located at (C.EApp function expression)

replaceDynamic :: Int -> C.Expr -> [ApplicationArgument] -> [ApplicationArgument]
replaceDynamic wanted replacement = zipWith replaceAt [0 :: Int ..]
  where
    replaceAt index argument
      | index == wanted = case argument of
          DynamicArgument _ at -> DynamicArgument replacement at
          _ -> argument
      | otherwise = argument

constructorName :: C.Con -> Maybe String
constructorName constructor = case locatedValue constructor of
  C.CName name -> Just name
  _ -> Nothing

replace :: Located source -> value -> Located value
replace source value = Located (locatedSpan source) value

collectValues :: C.File -> Map.Map C.GlobalId ValueInfo
collectValues = Map.fromList . concatMap collect
  where
    collect declaration = case locatedValue declaration of
      C.DVal name identifier typ expression url ->
        [(identifier, ValueInfo name typ expression url)]
      C.DValRec bindings ->
        [ (identifier, ValueInfo name typ expression url)
        | (name, identifier, typ, expression, url) <- bindings
        ]
      _ -> []

collectAliases :: C.File -> Map.Map C.GlobalId C.GlobalId
collectAliases = Map.fromList . concatMap collect
  where
    collect declaration = case locatedValue declaration of
      C.DVal _ identifier _ expression _ -> case locatedValue expression of
        C.ENamed target -> [(identifier, target)]
        _ -> []
      _ -> []

canonical :: Map.Map C.GlobalId C.GlobalId -> C.GlobalId -> C.GlobalId
canonical aliases = go Set.empty
  where
    go seen identifier
      | Set.member identifier seen = identifier
      | otherwise = case Map.lookup identifier aliases of
          Just next -> go (Set.insert identifier seen) next
          Nothing -> identifier

unwindFunctions :: C.Con -> ([C.Con], C.Con)
unwindFunctions typ = case locatedValue typ of
  C.TFun domain range ->
    let (arguments, result) = unwindFunctions range
     in (domain : arguments, result)
  _ -> ([], typ)

unitCon :: Span -> C.Con
unitCon at = Located at (C.TRecord (Located at (C.CRecord (Located at C.KType) [])))

ffiString :: Span -> C.Con
ffiString at = Located at (C.CFfi "Basis" "string")

addProblem :: Located source -> String -> String -> State TagState ()
addProblem source code message = modify' $ \state -> state
  { problems = diagnostic CorePhase code (locatedSpan source) message : problems state }

maximumIdentifier :: C.File -> Int
maximumIdentifier file = maximum (0 : concatMap collect file)
  where
    collect declaration = case locatedValue declaration of
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
    one identifier = [C.unGlobalId identifier]
