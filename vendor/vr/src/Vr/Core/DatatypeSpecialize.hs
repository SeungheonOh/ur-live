{-# LANGUAGE DerivingStrategies #-}

-- | Ur/Web's @Specialize@ pass for parameterized Core datatypes.
--
-- Concrete applications receive one memoized, parameter-free datatype and a
-- fresh constructor family.  A datatype used with an open constructor is left
-- alone: specializing such a use would be incoherent, and the reference
-- compiler reports it later if it survives to Monoize.
module Vr.Core.DatatypeSpecialize
  ( specializeFile
  ) where

import Control.Monad (foldM)
import Control.Monad.State.Strict (State, evalState, get, gets, modify')
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Vr.Core.Substitute as Substitute
import qualified Vr.Core.Syntax as C
import Vr.Source (Located (..), Span)

data DatatypeDefinition = DatatypeDefinition
  { datatypeName :: !String
  , datatypeParameterCount :: !Int
  , datatypeConstructors :: ![(String, C.GlobalId, Maybe C.Con)]
  }
  deriving stock (Eq, Ord, Show)

data DatatypeInstance = DatatypeInstance
  { instanceDatatype :: !C.GlobalId
  , instanceConstructors :: !(Map.Map C.GlobalId C.GlobalId)
  }
  deriving stock (Eq, Ord, Show)

data SpecializeState = SpecializeState
  { specializeNextId :: !Int
  , specializeDatatypes :: !(Map.Map C.GlobalId DatatypeDefinition)
  , specializeConstructorParents :: !(Map.Map C.GlobalId C.GlobalId)
  , specializeMemo :: !(Map.Map (C.GlobalId, [C.Con]) DatatypeInstance)
  , specializePending :: ![(String, C.GlobalId, [String], [(String, C.GlobalId, Maybe C.Con)])]
  }

type SpecializeM = State SpecializeState

specializeFile :: C.File -> C.File
specializeFile file = evalState (foldM step [] file) initial
  where
    disqualified = fancyDatatypes file
    initial = SpecializeState (maximumGlobal file + 1) Map.empty Map.empty Map.empty []

    step declarations declaration = do
      declaration' <- specializeDeclaration declaration
      pending <- takePending
      case locatedValue declaration' of
        C.DDatatype definitions -> do
          if any (\(_, identifier, _, _) -> Set.member identifier disqualified) definitions
            then pure ()
            else registerDatatypes definitions
          let combined = reverse pending <> definitions
          pure (declarations <> [declaration' {locatedValue = C.DDatatype combined}])
        _ ->
          let generated = case pending of
                [] -> []
                _ -> [Located (locatedSpan declaration') (C.DDatatype (reverse pending))]
           in pure (declarations <> generated <> [declaration'])

takePending :: SpecializeM [(String, C.GlobalId, [String], [(String, C.GlobalId, Maybe C.Con)])]
takePending = do
  pending <- gets specializePending
  modify' $ \state -> state {specializePending = []}
  pure pending

registerDatatypes
  :: [(String, C.GlobalId, [String], [(String, C.GlobalId, Maybe C.Con)])]
  -> SpecializeM ()
registerDatatypes definitions = modify' $ \state ->
  state
    { specializeDatatypes = foldl addDatatype (specializeDatatypes state) definitions
    , specializeConstructorParents = foldl addConstructors (specializeConstructorParents state) definitions
    }
  where
    addDatatype known (name, identifier, parameters, constructors) =
      Map.insert identifier (DatatypeDefinition name (length parameters) constructors) known
    addConstructors known (_, identifier, _, constructors) =
      foldl (\parents (_, constructor, _) -> Map.insert constructor identifier parents) known constructors

specializeDeclaration :: C.Decl -> SpecializeM C.Decl
specializeDeclaration declaration = case locatedValue declaration of
  C.DCon name identifier kind definition ->
    rebuild . C.DCon name identifier kind <$> specializeCon definition
  C.DForeign moduleName name typ ->
    rebuild . C.DForeign moduleName name <$> specializeCon typ
  C.DDatatype definitions -> do
    definitions' <- mapM datatype definitions
    pure (rebuild (C.DDatatype definitions'))
  C.DVal name identifier typ expression url ->
    rebuild <$> (C.DVal name identifier <$> specializeCon typ <*> specializeExpr expression <*> pure url)
  C.DValRec bindings -> rebuild . C.DValRec <$> mapM binding bindings
  C.DExport {} -> pure declaration
  C.DTable name identifier row sqlName primary keys constraints uniques ->
    rebuild <$> (C.DTable name identifier <$> specializeCon row <*> pure sqlName <*> specializeExpr primary <*> specializeCon keys <*> specializeExpr constraints <*> specializeCon uniques)
  C.DSequence {} -> pure declaration
  C.DView name identifier sqlName expression row ->
    rebuild <$> (C.DView name identifier sqlName <$> specializeExpr expression <*> specializeCon row)
  C.DIndex table modes -> rebuild <$> (C.DIndex <$> specializeExpr table <*> specializeExpr modes)
  C.DDatabase {} -> pure declaration
  C.DCookie name identifier typ runtimeName ->
    rebuild <$> (C.DCookie name identifier <$> specializeCon typ <*> pure runtimeName)
  C.DStyle {} -> pure declaration
  C.DTask kind body -> rebuild <$> (C.DTask <$> specializeExpr kind <*> specializeExpr body)
  C.DPolicy expression -> rebuild . C.DPolicy <$> specializeExpr expression
  C.DOnError {} -> pure declaration
  where
    rebuild = Located (locatedSpan declaration)
    datatype (name, identifier, parameters, constructors) =
      (,,,) name identifier parameters <$> mapM constructor constructors
    constructor (name, identifier, payload) =
      (,,) name identifier <$> traverse specializeCon payload
    binding (name, identifier, typ, expression, url) =
      (,,,,) name identifier <$> specializeCon typ <*> specializeExpr expression <*> pure url

specializeCon :: C.Con -> SpecializeM C.Con
specializeCon source = do
  rebuilt <- case locatedValue source of
    C.TFun domain range -> at <$> (C.TFun <$> specializeCon domain <*> specializeCon range)
    C.TCFun name kind body -> at . C.TCFun name kind <$> specializeCon body
    C.TRecord row -> at . C.TRecord <$> specializeCon row
    C.CApp function argument -> at <$> (C.CApp <$> specializeCon function <*> specializeCon argument)
    C.CAbs name kind body -> at . C.CAbs name kind <$> specializeCon body
    C.CKAbs name body -> at . C.CKAbs name <$> specializeCon body
    C.CKApp function kind -> at . (`C.CKApp` kind) <$> specializeCon function
    C.TKFun name body -> at . C.TKFun name <$> specializeCon body
    C.CRecord kind fields -> at . C.CRecord kind <$> mapM field fields
    C.CConcat left right -> at <$> (C.CConcat <$> specializeCon left <*> specializeCon right)
    C.CTuple elements -> at . C.CTuple <$> mapM specializeCon elements
    C.CProj tuple index -> at . (`C.CProj` index) <$> specializeCon tuple
    _ -> pure source
  considerDatatypeApplication rebuilt
  where
    at = Located (locatedSpan source)
    field (name, value) = (,) <$> specializeCon name <*> specializeCon value

considerDatatypeApplication :: C.Con -> SpecializeM C.Con
considerDatatypeApplication constructor = case collectConApplications constructor of
  (Located _ (C.CNamed identifier), arguments@(_ : _)) -> do
    definitions <- gets specializeDatatypes
    case Map.lookup identifier definitions of
      Just definition | length arguments == datatypeParameterCount definition -> do
        instance' <- requestDatatype (locatedSpan constructor) identifier arguments definition
        pure (Located (locatedSpan constructor) (C.CNamed (instanceDatatype instance')))
      _ -> pure constructor
  _ -> pure constructor

specializeExpr :: C.Expr -> SpecializeM C.Expr
specializeExpr source = case locatedValue source of
  C.ECon classification constructor arguments payload -> do
    payload' <- traverse specializeExpr payload
    arguments' <- mapM specializeCon arguments
    constructorBase <- specializePatConTypes constructor
    (constructor', instantiated) <- specializePatCon (locatedSpan source) constructorBase arguments'
    pure (at (C.ECon classification constructor' (if instantiated then [] else arguments') payload'))
  C.EFfiApp moduleName name arguments -> at . C.EFfiApp moduleName name <$> mapM typed arguments
  C.EApp function argument -> at <$> (C.EApp <$> specializeExpr function <*> specializeExpr argument)
  C.EAbs name domain range body -> at <$> (C.EAbs name <$> specializeCon domain <*> specializeCon range <*> specializeExpr body)
  C.ECApp function argument -> at <$> (C.ECApp <$> specializeExpr function <*> specializeCon argument)
  C.ECAbs name kind body -> at . C.ECAbs name kind <$> specializeExpr body
  C.EKAbs name body -> at . C.EKAbs name <$> specializeExpr body
  C.EKApp function kind -> at . (`C.EKApp` kind) <$> specializeExpr function
  C.ERecord fields -> at . C.ERecord <$> mapM recordField fields
  C.EField record field typ rest -> at <$> (C.EField <$> specializeExpr record <*> specializeCon field <*> specializeCon typ <*> specializeCon rest)
  C.EConcat left leftRow right rightRow -> at <$> (C.EConcat <$> specializeExpr left <*> specializeCon leftRow <*> specializeExpr right <*> specializeCon rightRow)
  C.ECut record field typ rest -> at <$> (C.ECut <$> specializeExpr record <*> specializeCon field <*> specializeCon typ <*> specializeCon rest)
  C.ECutMulti record fields rest -> at <$> (C.ECutMulti <$> specializeExpr record <*> specializeCon fields <*> specializeCon rest)
  C.ECase scrutinee branches input result -> at <$> (C.ECase <$> specializeExpr scrutinee <*> mapM branch branches <*> specializeCon input <*> specializeCon result)
  C.EWrite value -> at . C.EWrite <$> specializeExpr value
  C.EClosure identifier values -> at . C.EClosure identifier <$> mapM specializeExpr values
  C.ELet name typ value body -> at <$> (C.ELet name <$> specializeCon typ <*> specializeExpr value <*> specializeExpr body)
  C.EServerCall identifier values typ failureMode -> at <$> (C.EServerCall identifier <$> mapM specializeExpr values <*> specializeCon typ <*> pure failureMode)
  _ -> pure source
  where
    at = Located (locatedSpan source)
    typed (expression, typ) = (,) <$> specializeExpr expression <*> specializeCon typ
    recordField (field, value, typ) = (,,) <$> specializeCon field <*> specializeExpr value <*> specializeCon typ
    branch (pattern', body) = (,) <$> specializePattern pattern' <*> specializeExpr body

specializePattern :: C.Pattern -> SpecializeM C.Pattern
specializePattern source = case locatedValue source of
  C.PVar name typ -> at . C.PVar name <$> specializeCon typ
  C.PPrim {} -> pure source
  C.PCon classification constructor arguments nested -> do
    nested' <- traverse specializePattern nested
    arguments' <- mapM specializeCon arguments
    constructorBase <- specializePatConTypes constructor
    (constructor', instantiated) <- specializePatCon (locatedSpan source) constructorBase arguments'
    pure (at (C.PCon classification constructor' (if instantiated then [] else arguments') nested'))
  C.PRecord fields -> at . C.PRecord <$> mapM field fields
  where
    at = Located (locatedSpan source)
    field (name, nested, typ) = (,,) name <$> specializePattern nested <*> specializeCon typ

specializePatConTypes :: C.PatCon -> SpecializeM C.PatCon
specializePatConTypes constructor = case constructor of
  C.PConFfi moduleName datatypeName parameters name payload classification ->
    C.PConFfi moduleName datatypeName parameters name <$> traverse specializeCon payload <*> pure classification
  C.PConVar {} -> pure constructor

specializePatCon :: Span -> C.PatCon -> [C.Con] -> SpecializeM (C.PatCon, Bool)
specializePatCon location constructor arguments = case (constructor, arguments) of
  (C.PConVar oldConstructor, _ : _) | not (any openCon arguments) -> do
    state <- get
    case Map.lookup oldConstructor (specializeConstructorParents state) >>= (\parent -> (parent,) <$> Map.lookup parent (specializeDatatypes state)) of
      Nothing -> pure (constructor, False)
      Just (parent, definition)
        | length arguments /= datatypeParameterCount definition -> pure (constructor, False)
        | otherwise -> do
            instance' <- requestDatatype location parent arguments definition
            case Map.lookup oldConstructor (instanceConstructors instance') of
              Just concrete -> pure (C.PConVar concrete, True)
              Nothing -> pure (constructor, False)
  _ -> pure (constructor, False)

requestDatatype
  :: Span
  -> C.GlobalId
  -> [C.Con]
  -> DatatypeDefinition
  -> SpecializeM DatatypeInstance
requestDatatype _location sourceId arguments definition = do
  state <- get
  let normalizedArguments = map Substitute.semanticCon arguments
      key = (sourceId, normalizedArguments)
  case Map.lookup key (specializeMemo state) of
    Just instance' -> pure instance'
    Nothing -> do
      let datatypeId = C.GlobalId (specializeNextId state)
          allocated = zip (datatypeConstructors definition) [specializeNextId state + 1 ..]
          constructorMap = Map.fromList [(oldId, C.GlobalId fresh) | ((_, oldId, _), fresh) <- allocated]
          instance' = DatatypeInstance datatypeId constructorMap
      modify' $ \current ->
        current
          { specializeNextId = specializeNextId current + 1 + length allocated
          , specializeMemo = Map.insert key instance' (specializeMemo current)
          }
      constructors <- mapM (instantiateConstructor normalizedArguments) allocated
      let generated = (datatypeName definition <> "_s", datatypeId, [], constructors)
      modify' $ \current -> current {specializePending = generated : specializePending current}
      pure instance'
  where
    instantiateConstructor concrete ((name, _, payload), fresh) = do
      payload' <- traverse (specializeCon . instantiateParameters concrete) payload
      pure (name, C.GlobalId fresh, payload')

instantiateParameters :: [C.Con] -> C.Con -> C.Con
instantiateParameters arguments body =
  foldl (flip (Substitute.substituteCon 0)) body (reverse arguments)

collectConApplications :: C.Con -> (C.Con, [C.Con])
collectConApplications constructor = case locatedValue constructor of
  C.CApp function argument ->
    let (headConstructor, arguments) = collectConApplications function
     in (headConstructor, arguments <> [argument])
  _ -> (constructor, [])

openCon :: C.Con -> Bool
openCon constructor = case locatedValue constructor of
  C.CRel {} -> True
  C.TFun domain range -> openCon domain || openCon range
  C.TCFun _ _ body -> openCon body
  C.TRecord row -> openCon row
  C.CApp function argument -> openCon function || openCon argument
  C.CAbs _ _ body -> openCon body
  C.CKAbs _ body -> openCon body
  C.CKApp function _ -> openCon function
  C.TKFun _ body -> openCon body
  C.CRecord _ fields -> any (openCon . fst) fields || any (openCon . snd) fields
  C.CConcat left right -> openCon left || openCon right
  C.CTuple elements -> any openCon elements
  C.CProj tuple _ -> openCon tuple
  _ -> False

fancyDatatypes :: C.File -> Set.Set C.GlobalId
fancyDatatypes = foldMap declarationFancy
  where
    declarationFancy declaration =
      let ignored = case locatedValue declaration of
            C.DDatatype definitions -> Set.fromList [identifier | (_, identifier, _, _) <- definitions]
            _ -> Set.empty
       in foldDeclarationCons (fancyCon ignored) declaration

    fancyCon ignored constructor = direct <> children
      where
        direct = case locatedValue constructor of
          C.CApp _ argument | openCon argument -> case collectConApplications constructor of
            (Located _ (C.CNamed identifier), _) | Set.notMember identifier ignored -> Set.singleton identifier
            _ -> Set.empty
          _ -> Set.empty
        children = foldConChildren (fancyCon ignored) constructor

foldDeclarationCons :: (C.Con -> Set.Set C.GlobalId) -> C.Decl -> Set.Set C.GlobalId
foldDeclarationCons visit declaration = case locatedValue declaration of
  C.DCon _ _ _ definition -> visit definition
  C.DDatatype definitions -> foldMap (foldMap (foldMap visit . third) . fourth) definitions
  C.DVal _ _ typ expression _ -> visit typ <> foldExprCons visit expression
  C.DValRec bindings -> foldMap (\(_, _, typ, expression, _) -> visit typ <> foldExprCons visit expression) bindings
  C.DTable _ _ row _ primary keys constraints uniques -> visit row <> foldExprCons visit primary <> visit keys <> foldExprCons visit constraints <> visit uniques
  C.DView _ _ _ expression row -> foldExprCons visit expression <> visit row
  C.DIndex table modes -> foldExprCons visit table <> foldExprCons visit modes
  C.DCookie _ _ typ _ -> visit typ
  C.DTask kind body -> foldExprCons visit kind <> foldExprCons visit body
  C.DPolicy expression -> foldExprCons visit expression
  _ -> Set.empty
  where
    third (_, _, value) = value
    fourth (_, _, _, value) = value

foldExprCons :: (C.Con -> Set.Set C.GlobalId) -> C.Expr -> Set.Set C.GlobalId
foldExprCons visit expression = case locatedValue expression of
  C.ECon _ constructor arguments payload -> foldPatConCons visit constructor <> foldMap visit arguments <> foldMap (foldExprCons visit) payload
  C.EFfiApp _ _ arguments -> foldMap (\(value, typ) -> foldExprCons visit value <> visit typ) arguments
  C.EApp function argument -> foldExprCons visit function <> foldExprCons visit argument
  C.EAbs _ domain range body -> visit domain <> visit range <> foldExprCons visit body
  C.ECApp function argument -> foldExprCons visit function <> visit argument
  C.ECAbs _ _ body -> foldExprCons visit body
  C.EKAbs _ body -> foldExprCons visit body
  C.EKApp function _ -> foldExprCons visit function
  C.ERecord fields -> foldMap (\(field, value, typ) -> visit field <> foldExprCons visit value <> visit typ) fields
  C.EField record field typ rest -> foldExprCons visit record <> visit field <> visit typ <> visit rest
  C.EConcat left leftRow right rightRow -> foldExprCons visit left <> visit leftRow <> foldExprCons visit right <> visit rightRow
  C.ECut record field typ rest -> foldExprCons visit record <> visit field <> visit typ <> visit rest
  C.ECutMulti record fields rest -> foldExprCons visit record <> visit fields <> visit rest
  C.ECase scrutinee branches input result -> foldExprCons visit scrutinee <> foldMap (\(pattern', body) -> foldPatternCons visit pattern' <> foldExprCons visit body) branches <> visit input <> visit result
  C.EWrite value -> foldExprCons visit value
  C.EClosure _ values -> foldMap (foldExprCons visit) values
  C.ELet _ typ value body -> visit typ <> foldExprCons visit value <> foldExprCons visit body
  C.EServerCall _ values typ _ -> foldMap (foldExprCons visit) values <> visit typ
  _ -> Set.empty

foldPatternCons :: (C.Con -> Set.Set C.GlobalId) -> C.Pattern -> Set.Set C.GlobalId
foldPatternCons visit pattern' = case locatedValue pattern' of
  C.PVar _ typ -> visit typ
  C.PCon _ constructor arguments nested -> foldPatConCons visit constructor <> foldMap visit arguments <> foldMap (foldPatternCons visit) nested
  C.PRecord fields -> foldMap (\(_, nested, typ) -> foldPatternCons visit nested <> visit typ) fields
  C.PPrim {} -> Set.empty

foldPatConCons :: (C.Con -> Set.Set C.GlobalId) -> C.PatCon -> Set.Set C.GlobalId
foldPatConCons visit constructor = case constructor of
  C.PConFfi _ _ _ _ payload _ -> foldMap visit payload
  C.PConVar {} -> Set.empty

foldConChildren :: (C.Con -> Set.Set C.GlobalId) -> C.Con -> Set.Set C.GlobalId
foldConChildren visit constructor = case locatedValue constructor of
  C.TFun domain range -> visit domain <> visit range
  C.TCFun _ _ body -> visit body
  C.TRecord row -> visit row
  C.CApp function argument -> visit function <> visit argument
  C.CAbs _ _ body -> visit body
  C.CKAbs _ body -> visit body
  C.CKApp function _ -> visit function
  C.TKFun _ body -> visit body
  C.CRecord _ fields -> foldMap (\(name, value) -> visit name <> visit value) fields
  C.CConcat left right -> visit left <> visit right
  C.CTuple elements -> foldMap visit elements
  C.CProj tuple _ -> visit tuple
  _ -> Set.empty

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
