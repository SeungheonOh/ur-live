-- | Lift recursive local functions and transactions to top-level recursive
-- groups, abstracting their free kind, constructor, and value variables.  This
-- is the required precondition for conversion to the Explicit language.
module Vr.Explicit.Unnest
  ( unnestFile
  ) where

import Data.List (elemIndex)
import qualified Data.Set as Set
import Vr.Elaborate.Substitute (liftCon, liftConInExpr, liftKindInExpr)
import Vr.Elaborate.Syntax
import Vr.Source (Explicitness (..), Located (..), Span, noSpan)

data Context = Context
  { contextKindNames :: ![String]
  , contextConstructors :: ![(String, Kind)]
  , contextValues :: ![(String, Con)]
  }

data UnnestState = UnnestState
  { stateNextGlobal :: !Int
  , stateLifted :: ![(String, GlobalId, Con, Expr)]
  }

emptyContext :: Context
emptyContext = Context [] [] []

unnestFile :: File -> File
unnestFile file = fst (processDeclarations basis file initial)
  where
    basis = findBasis file
    initial = UnnestState (maximumGlobal file + 1) []

processDeclarations :: Maybe GlobalId -> [Decl] -> UnnestState -> ([Decl], UnnestState)
processDeclarations _ [] state = ([], state)
processDeclarations basis (declaration : rest) state0 =
  let (first, state1) = processDeclaration basis declaration state0
      (later, state2) = processDeclarations basis rest state1
   in (first <> later, state2)

processDeclaration :: Maybe GlobalId -> Decl -> UnnestState -> ([Decl], UnnestState)
processDeclaration basis declaration state0 = case locatedValue declaration of
  DVal name identifier typ expression ->
    finishExplored declaration state0 $ \state ->
      let (expression', state') = unnestExpression basis emptyContext expression state
       in (declaration {locatedValue = DVal name identifier typ expression'}, state')
  DValRec bindings ->
    finishExplored declaration state0 $ \state ->
      let mapBinding current (name, identifier, typ, expression) =
            let (expression', next) = unnestExpression basis emptyContext expression current
             in ((name, identifier, typ, expression'), next)
          (bindings', state') = mapAccum mapBinding state bindings
       in (declaration {locatedValue = DValRec bindings'}, state')
  DTask kind expression ->
    finishExplored declaration state0 $ \state ->
      let (kind', state1) = unnestExpression basis emptyContext kind state
          (expression', state2) = unnestExpression basis emptyContext expression state1
       in (declaration {locatedValue = DTask kind' expression'}, state2)
  DPolicy expression ->
    finishExplored declaration state0 $ \state ->
      let (expression', state') = unnestExpression basis emptyContext expression state
       in (declaration {locatedValue = DPolicy expression'}, state')
  DStr name identifier signature structure ->
    let (structure', state1) = processStructure basis structure state0
     in ([declaration {locatedValue = DStr name identifier signature structure'}], state1)
  _ -> ([declaration], state0)
  where
    finishExplored original state action =
      let (mapped, state1) = action state
          lifted = stateLifted state1
          at = locatedSpan original
          declarations = case locatedValue mapped of
            DValRec bindings -> [mapped {locatedValue = DValRec (bindings <> lifted)}]
            _ -> [Located at (DValRec lifted), mapped]
       in (declarations, state1 {stateLifted = []})

processStructure :: Maybe GlobalId -> Structure -> UnnestState -> (Structure, UnnestState)
processStructure basis structure state = case locatedValue structure of
  StrConst declarations ->
    let (declarations', state') = processDeclarations basis declarations state
     in (structure {locatedValue = StrConst declarations'}, state')
  StrFun name identifier domain range body ->
    let (body', state') = processStructure basis body state
     in (structure {locatedValue = StrFun name identifier domain range body'}, state')
  StrError -> error "Unnest received StrError after successful finalization"
  _ -> (structure, state)

unnestExpression :: Maybe GlobalId -> Context -> Expr -> UnnestState -> (Expr, UnnestState)
unnestExpression basis context expression state0 = case locatedValue expression of
  EApp function argument ->
    let (function', state1) = recurse context function state0
        (argument', state2) = recurse context argument state1
     in (replace (EApp function' argument'), state2)
  EAbs name domain range body ->
    let bodyContext = enterValue name domain context
        (body', state1) = recurse bodyContext body state0
     in (replace (EAbs name domain range body'), state1)
  ECApp function argument ->
    let (function', state1) = recurse context function state0
     in (replace (ECApp function' argument), state1)
  ECAbs explicitness name kind body ->
    let bodyContext = enterConstructor name kind context
        (body', state1) = recurse bodyContext body state0
     in (replace (ECAbs explicitness name kind body'), state1)
  EKAbs name body ->
    let bodyContext = context {contextKindNames = name : contextKindNames context}
        (body', state1) = recurse bodyContext body state0
     in (replace (EKAbs name body'), state1)
  EKApp function kind ->
    let (function', state1) = recurse context function state0
     in (replace (EKApp function' kind), state1)
  ERecord fields ->
    let mapField current (name, value, typ) =
          let (value', next) = recurse context value current
           in ((name, value', typ), next)
        (fields', state1) = mapAccum mapField state0 fields
     in (replace (ERecord fields'), state1)
  EField record name field rest ->
    let (record', state1) = recurse context record state0
     in (replace (EField record' name field rest), state1)
  EConcat left leftRow right rightRow ->
    let (left', state1) = recurse context left state0
        (right', state2) = recurse context right state1
     in (replace (EConcat left' leftRow right' rightRow), state2)
  ECut record name field rest ->
    let (record', state1) = recurse context record state0
     in (replace (ECut record' name field rest), state1)
  ECutMulti record fields rest ->
    let (record', state1) = recurse context record state0
     in (replace (ECutMulti record' fields rest), state1)
  ECase scrutinee branches input result ->
    let (scrutinee', state1) = recurse context scrutinee state0
        mapBranch current (pattern', body) =
          let branchContext = enterPattern pattern' context
              (body', next) = recurse branchContext body current
           in ((pattern', body'), next)
        (branches', state2) = mapAccum mapBranch state1 branches
     in (replace (ECase scrutinee' branches' input result), state2)
  ELet declarations body result ->
    let (declarations', bodyContext, state1) = mapLocalDeclarations basis context declarations state0
        (body', state2) = recurse bodyContext body state1
        mapped = replace (ELet declarations' body' result)
     in transformLet basis context mapped state2
  _ -> (expression, state0)
  where
    recurse = unnestExpression basis
    replace value = expression {locatedValue = value}

mapLocalDeclarations
  :: Maybe GlobalId
  -> Context
  -> [EDecl]
  -> UnnestState
  -> ([EDecl], Context, UnnestState)
mapLocalDeclarations _ context [] state = ([], context, state)
mapLocalDeclarations basis context (declaration : rest) state0 = case locatedValue declaration of
  EDVal pattern' typ expression ->
    let (expression', state1) = unnestExpression basis context expression state0
        declaration' = declaration {locatedValue = EDVal pattern' typ expression'}
        context' = enterPattern pattern' context
        (rest', finalContext, state2) = mapLocalDeclarations basis context' rest state1
     in (declaration' : rest', finalContext, state2)
  EDValRec bindings ->
    let recursiveContext = foldl' (\current (name, typ, _) -> enterValue name typ current) context bindings
        mapBinding current (name, typ, expression) =
          let (expression', next) = unnestExpression basis recursiveContext expression current
           in ((name, typ, expression'), next)
        (bindings', state1) = mapAccum mapBinding state0 bindings
        declaration' = declaration {locatedValue = EDValRec bindings'}
        (rest', finalContext, state2) = mapLocalDeclarations basis recursiveContext rest state1
     in (declaration' : rest', finalContext, state2)

transformLet :: Maybe GlobalId -> Context -> Expr -> UnnestState -> (Expr, UnnestState)
transformLet basis context expression state0 = case locatedValue expression of
  ELet declarations body result ->
    let promoted = map promoteFunction declarations
        initial = (contextValues context, stateNextGlobal state0, stateLifted state0, [], 0)
        (remaining, (_, nextGlobal, lifted, substitutions, removed)) =
          foldl' (stepLocal basis context) ([], initial) promoted
        body' = applyAndRemove body substitutions removed
        expression' = expression {locatedValue = ELet remaining body' result}
     in (expression', UnnestState nextGlobal lifted)
  _ -> (expression, state0)
  where
    promoteFunction declaration = case locatedValue declaration of
      EDVal (Located _ (PVar name _)) typ value
        -- Turning a non-recursive value into a one-element recursive group
        -- introduces the function itself at relative index zero.  Shift every
        -- formerly free value across that new binder, matching Ur/Web's
        -- E.liftExpInExp 0 operation in Unnest.
        | functionInside basis typ -> declaration {locatedValue = EDValRec [(name, typ, liftExprValues 1 0 value)]}
      _ -> declaration

type LetAccumulator = ([(String, Con)], Int, [(String, GlobalId, Con, Expr)], [(Int, Expr)], Int)

stepLocal
  :: Maybe GlobalId
  -> Context
  -> ([EDecl], LetAccumulator)
  -> EDecl
  -> ([EDecl], LetAccumulator)
stepLocal _ context (done, (values, nextGlobal, lifted, substitutions, removed)) declaration =
  case locatedValue declaration of
    EDVal pattern' typ value ->
      let value' = applyAndRemove value substitutions removed
          values' = patternVariables pattern' values
          substitutions' = addPatternBinders (patternBindCount pattern') substitutions
       in (done <> [declaration {locatedValue = EDVal pattern' typ value'}],
           (values', nextGlobal, lifted, substitutions', removed))
    EDValRec bindings ->
      let at = locatedSpan declaration
          count = length bindings
          localSubstitutions =
            [ (index + count, liftExprValues count 0 replacement)
            | (index, replacement) <- substitutions
            , not (isRelative replacement)
            ]
          substitutedBindings =
            [ (name, typ, applySubstitutions expression localSubstitutions)
            | (name, typ, expression) <- bindings
            ]
          (kindFree0, conFree0, valueFree) = foldMap (bindingFree count) substitutedBindings
          kindFree1 = Set.foldl' (addConstructorKindFree context) kindFree0 conFree0
          kindFree = Set.foldl' (addValueKindFree values) kindFree1 valueFree
          conFree = Set.foldl' (addValueConFree values) conFree0 valueFree
          identifiers = map (GlobalId . (+ nextGlobal)) [0 .. count - 1]
          namedBindings = zipWith attachIdentifier substitutedBindings identifiers
          substitutionsShifted =
            [ (index + count, if isRelative replacement then replacement else liftExprValues count 0 replacement)
            | (index, replacement) <- substitutions
            ]
          callSubstitutions = zipWith (makeCall at count kindFree conFree valueFree) [0 ..] namedBindings
          substitutions' = callSubstitutions <> substitutionsShifted
          liftedBindings = map (abstractBinding at context values count kindFree conFree valueFree callSubstitutions) namedBindings
          values' = reverse [(name, typ) | (name, _, typ, _) <- liftedBindings] <> values
       in ( done
          , ( values'
            , nextGlobal + count
            , liftedBindings <> lifted
            , substitutions'
            , removed + count
            )
          )
  where
    attachIdentifier (name, typ, value) identifier = (name, identifier, typ, value)

bindingFree :: Int -> (String, Con, Expr) -> (Set.Set Int, Set.Set Int, Set.Set Int)
bindingFree count (_, typ, expression) =
  let (kindFromType, conFromType) = freeCon 0 0 typ
      (kindFromExpr, conFromExpr, valueFromExpr) = freeExpr 0 0 count expression
   in (Set.union kindFromType kindFromExpr, Set.union conFromType conFromExpr, valueFromExpr)

addConstructorKindFree :: Context -> Set.Set Int -> Int -> Set.Set Int
addConstructorKindFree context accumulated index = case indexMaybe index (contextConstructors context) of
  Nothing -> accumulated
  Just (_, kind) -> Set.union accumulated (freeKind 0 kind)

addValueKindFree :: [(String, Con)] -> Set.Set Int -> Int -> Set.Set Int
addValueKindFree values accumulated index = case indexMaybe index values of
  Nothing -> accumulated
  Just (_, typ) -> Set.union accumulated (fst (freeCon 0 0 typ))

addValueConFree :: [(String, Con)] -> Set.Set Int -> Int -> Set.Set Int
addValueConFree values accumulated index = case indexMaybe index values of
  Nothing -> accumulated
  Just (_, typ) -> Set.union accumulated (snd (freeCon 0 0 typ))

makeCall
  :: Span
  -> Int
  -> Set.Set Int
  -> Set.Set Int
  -> Set.Set Int
  -> Int
  -> (String, GlobalId, Con, Expr)
  -> (Int, Expr)
makeCall at count kindFree conFree valueFree position (_, identifier, _, _) =
  let start = Located at (ENamed identifier)
      withKinds = foldr (\index expression -> Located at (EKApp expression (Located at (KRel index)))) start (Set.toAscList kindFree)
      withConstructors = foldr (\index expression -> Located at (ECApp expression (Located at (CRel index)))) withKinds (Set.toAscList conFree)
      withValues = foldr (\index expression -> Located at (EApp expression (Located at (ERel (count + index))))) withConstructors (Set.toAscList valueFree)
   in (count - position - 1, withValues)

abstractBinding
  :: Span
  -> Context
  -> [(String, Con)]
  -> Int
  -> Set.Set Int
  -> Set.Set Int
  -> Set.Set Int
  -> [(Int, Expr)]
  -> (String, GlobalId, Con, Expr)
  -> (String, GlobalId, Con, Expr)
abstractBinding at context values recursiveCount kindFree conFree valueFree callSubstitutions (name, identifier, typ0, expression0) =
  let location = at
      expression1 = applySubstitutions expression0 callSubstitutions
      kindIndices = Set.toAscList kindFree
      conIndices = Set.toAscList conFree
      valueIndices = Set.toAscList valueFree
      typ1 = squishCon kindIndices conIndices typ0
      expression2 = squishExpr recursiveCount kindIndices conIndices valueIndices expression1
      (expression3, typ2) = foldl' (abstractValue location kindIndices conIndices values) (expression2, typ1) valueIndices
      (expression4, typ3) = foldl' (abstractConstructor location context) (expression3, typ2) conIndices
      (expression5, typ4) = foldl' (abstractKind location context) (expression4, typ3) kindIndices
   in ('$' : name, identifier, typ4, expression5)

abstractValue :: Span -> [Int] -> [Int] -> [(String, Con)] -> (Expr, Con) -> Int -> (Expr, Con)
abstractValue at kindIndices conIndices values (expression, typ) index = case indexMaybe index values of
  Nothing -> (expression, typ)
  Just (name, argumentType) ->
    let argumentType' = squishCon kindIndices conIndices argumentType
     in (Located at (EAbs name argumentType' typ expression), Located at (TFun argumentType' typ))

abstractConstructor :: Span -> Context -> (Expr, Con) -> Int -> (Expr, Con)
abstractConstructor at context (expression, typ) index = case indexMaybe index (contextConstructors context) of
  Nothing -> (expression, typ)
  Just (name, kind) ->
    ( Located at (ECAbs Explicit name kind expression)
    , Located at (TCFun Explicit name kind typ)
    )

abstractKind :: Span -> Context -> (Expr, Con) -> Int -> (Expr, Con)
abstractKind at context (expression, typ) index = case indexMaybe index (contextKindNames context) of
  Nothing -> (expression, typ)
  Just name -> (Located at (EKAbs name expression), Located at (TKFun name typ))

functionInside :: Maybe GlobalId -> Con -> Bool
functionInside basis typ = case locatedValue typ of
  TFun {} -> True
  CApp function _ -> case (basis, locatedValue function) of
    (Just expected, CModProj actual [] "transaction") -> expected == actual
    _ -> False
  _ -> False

enterValue :: String -> Con -> Context -> Context
enterValue name typ context = context {contextValues = (name, typ) : contextValues context}

enterConstructor :: String -> Kind -> Context -> Context
enterConstructor name kind context =
  context
    { contextConstructors = (name, kind) : contextConstructors context
    , contextValues = [(valueName, liftCon 0 1 typ) | (valueName, typ) <- contextValues context]
    }

enterPattern :: Pattern -> Context -> Context
enterPattern pattern' context = context {contextValues = patternVariables pattern' (contextValues context)}

patternVariables :: Pattern -> [(String, Con)] -> [(String, Con)]
patternVariables pattern' values = case locatedValue pattern' of
  PVar name typ -> (name, typ) : values
  PCon _ _ _ nested -> maybe values (`patternVariables` values) nested
  PRecord fields _ -> foldl' (\current (_, nested, _) -> patternVariables nested current) values fields
  PPrim {} -> values

patternBindCount :: Pattern -> Int
patternBindCount pattern' = case locatedValue pattern' of
  PVar {} -> 1
  PCon _ _ _ nested -> maybe 0 patternBindCount nested
  PRecord fields _ -> sum [patternBindCount nested | (_, nested, _) <- fields]
  PPrim {} -> 0

addPatternBinders :: Int -> [(Int, Expr)] -> [(Int, Expr)]
addPatternBinders count substitutions = iterate addOne substitutions !! count
  where
    addOne current =
      (0, Located noLocation (ERel 0))
        : [(index + 1, liftExprValues 1 0 expression) | (index, expression) <- current]

isRelative :: Expr -> Bool
isRelative expression = case locatedValue expression of
  ERel {} -> True
  _ -> False

applyAndRemove :: Expr -> [(Int, Expr)] -> Int -> Expr
applyAndRemove expression substitutions removed =
  liftExprValues (-removed) (length substitutions) (applySubstitutions expression substitutions)

applySubstitutions :: Expr -> [(Int, Expr)] -> Expr
applySubstitutions = foldl' (\expression (index, replacement) -> substituteValue index replacement expression)

substituteValue :: Int -> Expr -> Expr -> Expr
substituteValue target replacement = go 0 0 0
  where
    go kindBound conBound valueBound expression = case locatedValue expression of
      ERel index | index == target + valueBound ->
        liftKindInExpr 0 kindBound (liftConInExpr 0 conBound (liftExprValues valueBound 0 replacement))
      EApp function argument -> two expression EApp function argument
      EAbs name domain range body -> expression {locatedValue = EAbs name domain range (go kindBound conBound (valueBound + 1) body)}
      ECApp function argument -> expression {locatedValue = ECApp (go kindBound conBound valueBound function) argument}
      ECAbs explicitness name kind body -> expression {locatedValue = ECAbs explicitness name kind (go kindBound (conBound + 1) valueBound body)}
      EKAbs name body -> expression {locatedValue = EKAbs name (go (kindBound + 1) conBound valueBound body)}
      EKApp function kind -> expression {locatedValue = EKApp (go kindBound conBound valueBound function) kind}
      ERecord fields -> expression {locatedValue = ERecord [(name, go kindBound conBound valueBound value, typ) | (name, value, typ) <- fields]}
      EField record name field rest -> expression {locatedValue = EField (go kindBound conBound valueBound record) name field rest}
      EConcat left leftRow right rightRow -> expression {locatedValue = EConcat (go kindBound conBound valueBound left) leftRow (go kindBound conBound valueBound right) rightRow}
      ECut record name field rest -> expression {locatedValue = ECut (go kindBound conBound valueBound record) name field rest}
      ECutMulti record fields rest -> expression {locatedValue = ECutMulti (go kindBound conBound valueBound record) fields rest}
      ECase scrutinee branches input result -> expression
        { locatedValue = ECase
            (go kindBound conBound valueBound scrutinee)
            [ (pattern', go kindBound conBound (valueBound + patternBindCount pattern') body)
            | (pattern', body) <- branches
            ] input result
        }
      ELet declarations body typ ->
        let (declarations', finalBound) = substituteDeclarations kindBound conBound valueBound declarations
         in expression {locatedValue = ELet declarations' (go kindBound conBound finalBound body) typ}
      _ -> expression
      where
        two original make left right = original {locatedValue = make (go kindBound conBound valueBound left) (go kindBound conBound valueBound right)}
    substituteDeclarations _ _ bound [] = ([], bound)
    substituteDeclarations kb cb bound (declaration : rest) = case locatedValue declaration of
      EDVal pattern' typ value ->
        let value' = go kb cb bound value
            nextBound = bound + patternBindCount pattern'
            (rest', finalBound) = substituteDeclarations kb cb nextBound rest
         in (declaration {locatedValue = EDVal pattern' typ value'} : rest', finalBound)
      EDValRec bindings ->
        let count = length bindings
            bindings' = [(name, typ, go kb cb (bound + count) value) | (name, typ, value) <- bindings]
            (rest', finalBound) = substituteDeclarations kb cb (bound + count) rest
         in (declaration {locatedValue = EDValRec bindings'} : rest', finalBound)

liftExprValues :: Int -> Int -> Expr -> Expr
liftExprValues amount cutoff = go 0
  where
    go bound expression = case locatedValue expression of
      ERel index | index >= cutoff + bound -> expression {locatedValue = ERel (index + amount)}
      EApp function argument -> two expression EApp function argument
      EAbs name domain range body -> expression {locatedValue = EAbs name domain range (go (bound + 1) body)}
      ECApp function argument -> expression {locatedValue = ECApp (go bound function) argument}
      ECAbs explicitness name kind body -> expression {locatedValue = ECAbs explicitness name kind (go bound body)}
      EKAbs name body -> expression {locatedValue = EKAbs name (go bound body)}
      EKApp function kind -> expression {locatedValue = EKApp (go bound function) kind}
      ERecord fields -> expression {locatedValue = ERecord [(name, go bound value, typ) | (name, value, typ) <- fields]}
      EField record name field rest -> expression {locatedValue = EField (go bound record) name field rest}
      EConcat left leftRow right rightRow -> expression {locatedValue = EConcat (go bound left) leftRow (go bound right) rightRow}
      ECut record name field rest -> expression {locatedValue = ECut (go bound record) name field rest}
      ECutMulti record fields rest -> expression {locatedValue = ECutMulti (go bound record) fields rest}
      ECase scrutinee branches input result -> expression
        { locatedValue = ECase (go bound scrutinee)
            [(pattern', go (bound + patternBindCount pattern') body) | (pattern', body) <- branches]
            input result
        }
      ELet declarations body typ ->
        let (declarations', finalBound) = liftDeclarations bound declarations
         in expression {locatedValue = ELet declarations' (go finalBound body) typ}
      _ -> expression
      where
        two original make left right = original {locatedValue = make (go bound left) (go bound right)}
    liftDeclarations bound [] = ([], bound)
    liftDeclarations bound (declaration : rest) = case locatedValue declaration of
      EDVal pattern' typ value ->
        let value' = go bound value
            nextBound = bound + patternBindCount pattern'
            (rest', finalBound) = liftDeclarations nextBound rest
         in (declaration {locatedValue = EDVal pattern' typ value'} : rest', finalBound)
      EDValRec bindings ->
        let count = length bindings
            bindings' = [(name, typ, go (bound + count) value) | (name, typ, value) <- bindings]
            (rest', finalBound) = liftDeclarations (bound + count) rest
         in (declaration {locatedValue = EDValRec bindings'} : rest', finalBound)

freeKind :: Int -> Kind -> Set.Set Int
freeKind bound kind = case locatedValue kind of
  KRel index | index >= bound -> Set.singleton (index - bound)
  KArrow domain range -> Set.union (freeKind bound domain) (freeKind bound range)
  KRecord element -> freeKind bound element
  KTuple elements -> foldMap (freeKind bound) elements
  KFun _ body -> freeKind (bound + 1) body
  KTupleMeta _ _ observations -> foldMap (freeKind bound . snd) observations
  _ -> Set.empty

freeCon :: Int -> Int -> Con -> (Set.Set Int, Set.Set Int)
freeCon kindBound conBound constructor = case locatedValue constructor of
  CRel index | index >= conBound -> (Set.empty, Set.singleton (index - conBound))
  TFun domain range -> both [domain, range]
  TCFun _ _ kind body -> (freeKind kindBound kind, Set.empty) <> freeCon kindBound (conBound + 1) body
  TRecord row -> freeCon kindBound conBound row
  TDisjoint left right body -> both [left, right, body]
  CApp function argument -> both [function, argument]
  CAbs _ kind body -> (freeKind kindBound kind, Set.empty) <> freeCon kindBound (conBound + 1) body
  CKAbs _ body -> freeCon (kindBound + 1) conBound body
  CKApp function kind -> freeCon kindBound conBound function <> (freeKind kindBound kind, Set.empty)
  TKFun _ body -> freeCon (kindBound + 1) conBound body
  CRecord kind fields ->
    (freeKind kindBound kind, Set.empty)
      <> foldMap (\(name, value) -> both [name, value]) fields
  CConcat left right -> both [left, right]
  CMap domain range -> (Set.union (freeKind kindBound domain) (freeKind kindBound range), Set.empty)
  CTuple elements -> both elements
  CProj tuple _ -> freeCon kindBound conBound tuple
  CMeta _ _ kind _ -> (freeKind kindBound kind, Set.empty)
  _ -> mempty
  where
    both = foldMap (freeCon kindBound conBound)

freePattern :: Int -> Int -> Pattern -> (Set.Set Int, Set.Set Int)
freePattern kindBound conBound pattern' = case locatedValue pattern' of
  PVar _ typ -> freeCon kindBound conBound typ
  PPrim {} -> mempty
  PCon _ _ arguments nested -> foldMap (freeCon kindBound conBound) arguments <> maybe mempty (freePattern kindBound conBound) nested
  PRecord fields _ -> foldMap (\(_, nested, typ) -> freePattern kindBound conBound nested <> freeCon kindBound conBound typ) fields

freeExpr :: Int -> Int -> Int -> Expr -> (Set.Set Int, Set.Set Int, Set.Set Int)
freeExpr kindBound conBound valueBound expression = case locatedValue expression of
  ERel index | index >= valueBound -> (Set.empty, Set.empty, Set.singleton (index - valueBound))
  EApp function argument -> expressions [function, argument]
  EAbs _ domain range body -> cons [domain, range] <> freeExpr kindBound conBound (valueBound + 1) body
  ECApp function argument -> freeExpr kindBound conBound valueBound function <> con argument
  ECAbs _ _ kind body -> kindOnly kind <> freeExpr kindBound (conBound + 1) valueBound body
  EKAbs _ body -> freeExpr (kindBound + 1) conBound valueBound body
  EKApp function kind -> freeExpr kindBound conBound valueBound function <> kindOnly kind
  ERecord fields -> foldMap (\(name, value, typ) -> con name <> freeExpr kindBound conBound valueBound value <> con typ) fields
  EField record name field rest -> freeExpr kindBound conBound valueBound record <> cons [name, field, rest]
  EConcat left leftRow right rightRow -> expressions [left, right] <> cons [leftRow, rightRow]
  ECut record name field rest -> freeExpr kindBound conBound valueBound record <> cons [name, field, rest]
  ECutMulti record fields rest -> freeExpr kindBound conBound valueBound record <> cons [fields, rest]
  ECase scrutinee branches input result ->
    freeExpr kindBound conBound valueBound scrutinee
      <> cons [input, result]
      <> foldMap (\(pattern', body) -> fromConPair (freePattern kindBound conBound pattern') <> freeExpr kindBound conBound (valueBound + patternBindCount pattern') body) branches
  ELet declarations body typ ->
    let (declarationFree, finalBound) = freeDeclarations valueBound declarations
     in declarationFree <> freeExpr kindBound conBound finalBound body <> con typ
  _ -> mempty
  where
    con value = fromConPair (freeCon kindBound conBound value)
    cons = foldMap con
    expressions = foldMap (freeExpr kindBound conBound valueBound)
    kindOnly kind = (freeKind kindBound kind, Set.empty, Set.empty)
    freeDeclarations bound [] = (mempty, bound)
    freeDeclarations bound (declaration : rest) = case locatedValue declaration of
      EDVal pattern' typ value ->
        let here = fromConPair (freePattern kindBound conBound pattern' <> freeCon kindBound conBound typ) <> freeExpr kindBound conBound bound value
            nextBound = bound + patternBindCount pattern'
            (later, finalBound) = freeDeclarations nextBound rest
         in (here <> later, finalBound)
      EDValRec bindings ->
        let count = length bindings
            here = foldMap (\(_, typ, value) -> con typ <> freeExpr kindBound conBound (bound + count) value) bindings
            (later, finalBound) = freeDeclarations (bound + count) rest
         in (here <> later, finalBound)

fromConPair :: (Set.Set Int, Set.Set Int) -> (Set.Set Int, Set.Set Int, Set.Set Int)
fromConPair (kinds, constructors) = (kinds, constructors, Set.empty)

squishCon :: [Int] -> [Int] -> Con -> Con
squishCon kindIndices conIndices = squishConUnder kindIndices conIndices 0 0

squishKind :: [Int] -> Int -> Kind -> Kind
squishKind indices = go
  where
    go bound kind = kind {locatedValue = case locatedValue kind of
      KRel index | index >= bound -> KRel (positionOf (index - bound) indices + bound)
      KArrow domain range -> KArrow (go bound domain) (go bound range)
      KRecord element -> KRecord (go bound element)
      KTuple elements -> KTuple (map (go bound) elements)
      KFun name body -> KFun name (go (bound + 1) body)
      KTupleMeta identifier at observations -> KTupleMeta identifier at [(index, go bound observed) | (index, observed) <- observations]
      other -> other}

squishExpr :: Int -> [Int] -> [Int] -> [Int] -> Expr -> Expr
squishExpr recursiveCount kindIndices conIndices valueIndices = go 0 0 recursiveCount
  where
    go kindBound conBound valueBound expression = expression {locatedValue = case locatedValue expression of
      ERel index | index >= valueBound -> ERel (positionOf (index - valueBound) valueIndices + valueBound - recursiveCount)
      EApp function argument -> EApp (go kindBound conBound valueBound function) (go kindBound conBound valueBound argument)
      EAbs name domain range body -> EAbs name (squishConAt kindBound conBound domain) (squishConAt kindBound conBound range) (go kindBound conBound (valueBound + 1) body)
      ECApp function argument -> ECApp (go kindBound conBound valueBound function) (squishConAt kindBound conBound argument)
      ECAbs explicitness name kind body -> ECAbs explicitness name (squishKind kindIndices kindBound kind) (go kindBound (conBound + 1) valueBound body)
      EKAbs name body -> EKAbs name (go (kindBound + 1) conBound valueBound body)
      EKApp function kind -> EKApp (go kindBound conBound valueBound function) (squishKind kindIndices kindBound kind)
      ERecord fields -> ERecord [(squishConAt kindBound conBound name, go kindBound conBound valueBound value, squishConAt kindBound conBound typ) | (name, value, typ) <- fields]
      EField record name field rest -> EField (go kindBound conBound valueBound record) (squishConAt kindBound conBound name) (squishConAt kindBound conBound field) (squishConAt kindBound conBound rest)
      EConcat left leftRow right rightRow -> EConcat (go kindBound conBound valueBound left) (squishConAt kindBound conBound leftRow) (go kindBound conBound valueBound right) (squishConAt kindBound conBound rightRow)
      ECut record name field rest -> ECut (go kindBound conBound valueBound record) (squishConAt kindBound conBound name) (squishConAt kindBound conBound field) (squishConAt kindBound conBound rest)
      ECutMulti record fields rest -> ECutMulti (go kindBound conBound valueBound record) (squishConAt kindBound conBound fields) (squishConAt kindBound conBound rest)
      ECase scrutinee branches input result -> ECase
        (go kindBound conBound valueBound scrutinee)
        [(squishPattern kindBound conBound pattern', go kindBound conBound (valueBound + patternBindCount pattern') body) | (pattern', body) <- branches]
        (squishConAt kindBound conBound input) (squishConAt kindBound conBound result)
      ELet declarations body typ ->
        let (declarations', finalBound) = squishDeclarations kindBound conBound valueBound declarations
         in ELet declarations' (go kindBound conBound finalBound body) (squishConAt kindBound conBound typ)
      other -> other}
    squishConAt kindBound conBound = squishConUnder kindIndices conIndices kindBound conBound
    squishDeclarations _ _ bound [] = ([], bound)
    squishDeclarations kb cb bound (declaration : rest) = case locatedValue declaration of
      EDVal pattern' typ value ->
        let pattern'' = squishPattern kb cb pattern'
            value' = go kb cb bound value
            nextBound = bound + patternBindCount pattern'
            (rest', finalBound) = squishDeclarations kb cb nextBound rest
         in (declaration {locatedValue = EDVal pattern'' (squishConAt kb cb typ) value'} : rest', finalBound)
      EDValRec bindings ->
        let count = length bindings
            bindings' = [(name, squishConAt kb cb typ, go kb cb (bound + count) value) | (name, typ, value) <- bindings]
            (rest', finalBound) = squishDeclarations kb cb (bound + count) rest
         in (declaration {locatedValue = EDValRec bindings'} : rest', finalBound)
    squishPattern kb cb pattern' = pattern' {locatedValue = case locatedValue pattern' of
      PVar name typ -> PVar name (squishConAt kb cb typ)
      PCon classification constructor arguments nested -> PCon classification constructor (map (squishConAt kb cb) arguments) (fmap (squishPattern kb cb) nested)
      PRecord fields flexible -> PRecord [(name, squishPattern kb cb nested, squishConAt kb cb typ) | (name, nested, typ) <- fields] flexible
      other -> other}

squishConUnder :: [Int] -> [Int] -> Int -> Int -> Con -> Con
squishConUnder kindIndices conIndices = go
  where
    go kindBound conBound constructor = constructor {locatedValue = case locatedValue constructor of
      TFun domain range -> TFun (go kindBound conBound domain) (go kindBound conBound range)
      TCFun explicitness name kind body -> TCFun explicitness name (squishKind kindIndices kindBound kind) (go kindBound (conBound + 1) body)
      TRecord row -> TRecord (go kindBound conBound row)
      TDisjoint left right body -> TDisjoint (go kindBound conBound left) (go kindBound conBound right) (go kindBound conBound body)
      CRel index | index >= conBound -> CRel (positionOf (index - conBound) conIndices + conBound)
      CApp function argument -> CApp (go kindBound conBound function) (go kindBound conBound argument)
      CAbs name kind body -> CAbs name (squishKind kindIndices kindBound kind) (go kindBound (conBound + 1) body)
      CKAbs name body -> CKAbs name (go (kindBound + 1) conBound body)
      CKApp function kind -> CKApp (go kindBound conBound function) (squishKind kindIndices kindBound kind)
      TKFun name body -> TKFun name (go (kindBound + 1) conBound body)
      CRecord kind fields -> CRecord (squishKind kindIndices kindBound kind) [(go kindBound conBound name, go kindBound conBound value) | (name, value) <- fields]
      CConcat left right -> CConcat (go kindBound conBound left) (go kindBound conBound right)
      CMap domain range -> CMap (squishKind kindIndices kindBound domain) (squishKind kindIndices kindBound range)
      CTuple elements -> CTuple (map (go kindBound conBound) elements)
      CProj tuple index -> CProj (go kindBound conBound tuple) index
      CMeta identifier level kind name -> CMeta identifier level (squishKind kindIndices kindBound kind) name
      other -> other}

positionOf :: Int -> [Int] -> Int
positionOf index values = case elemIndex index values of
  Just position -> position
  Nothing -> error ("Unnest free-variable invariant: missing index " <> show index)

mapAccum :: (state -> value -> (result, state)) -> state -> [value] -> ([result], state)
mapAccum _ state [] = ([], state)
mapAccum step state (value : rest) =
  let (result, state1) = step state value
      (results, state2) = mapAccum step state1 rest
   in (result : results, state2)

indexMaybe :: Int -> [value] -> Maybe value
indexMaybe index values
  | index < 0 = Nothing
  | otherwise = case drop index values of
      value : _ -> Just value
      [] -> Nothing

findBasis :: File -> Maybe GlobalId
findBasis [] = Nothing
findBasis (declaration : rest) = case locatedValue declaration of
  DFfiStr "Basis" identifier _ -> Just identifier
  _ -> findBasis rest

maximumGlobal :: File -> Int
maximumGlobal file = maximum (0 : concatMap declarationGlobals file)

declarationGlobals :: Decl -> [Int]
declarationGlobals declaration = case locatedValue declaration of
  DCon _ identifier _ _ -> one identifier
  DDatatype definitions -> concatMap datatypeGlobals definitions
  DDatatypeImp _ identifier original _ _ _ constructors -> one identifier <> one original <> concatMap constructorGlobals constructors
  DVal _ identifier _ _ -> one identifier
  DValRec bindings -> [unGlobalId identifier | (_, identifier, _, _) <- bindings]
  DSgn _ identifier signature -> one identifier <> signatureGlobals signature
  DStr _ identifier signature structure -> one identifier <> signatureGlobals signature <> structureGlobals structure
  DFfiStr _ identifier signature -> one identifier <> signatureGlobals signature
  DConstraint {} -> []
  DExport identifier signature structure -> one identifier <> signatureGlobals signature <> structureGlobals structure
  DTable basis _ identifier _ _ _ _ _ -> one basis <> one identifier
  DSequence basis _ identifier -> one basis <> one identifier
  DView basis _ identifier _ _ -> one basis <> one identifier
  DIndex {} -> []
  DDatabase {} -> []
  DCookie basis _ identifier _ -> one basis <> one identifier
  DStyle basis _ identifier -> one basis <> one identifier
  DTask {} -> []
  DPolicy {} -> []
  DOnError identifier _ _ -> one identifier
  DFfi _ identifier _ _ -> one identifier
  where one = pure . unGlobalId

datatypeGlobals :: (String, GlobalId, [String], [(String, GlobalId, Maybe Con)]) -> [Int]
datatypeGlobals (_, identifier, _, constructors) = unGlobalId identifier : concatMap constructorGlobals constructors

constructorGlobals :: (String, GlobalId, Maybe Con) -> [Int]
constructorGlobals (_, identifier, _) = [unGlobalId identifier]

signatureGlobals :: Signature -> [Int]
signatureGlobals signature = case locatedValue signature of
  SgnConst items -> concatMap signatureItemGlobals items
  SgnVar identifier -> [unGlobalId identifier]
  SgnFun _ identifier domain range -> unGlobalId identifier : signatureGlobals domain <> signatureGlobals range
  SgnWhere base _ _ _ -> signatureGlobals base
  SgnProj identifier _ _ -> [unGlobalId identifier]
  SgnError -> []

signatureItemGlobals :: SigItem -> [Int]
signatureItemGlobals item = case locatedValue item of
  SgiConAbs _ identifier _ -> [unGlobalId identifier]
  SgiCon _ identifier _ _ -> [unGlobalId identifier]
  SgiDatatype definitions -> concatMap datatypeGlobals definitions
  SgiDatatypeImp _ identifier original _ _ _ constructors -> unGlobalId identifier : unGlobalId original : concatMap constructorGlobals constructors
  SgiVal _ identifier _ -> [unGlobalId identifier]
  SgiStr _ _ identifier signature -> unGlobalId identifier : signatureGlobals signature
  SgiSgn _ identifier signature -> unGlobalId identifier : signatureGlobals signature
  SgiConstraint {} -> []
  SgiClassAbs _ identifier _ -> [unGlobalId identifier]
  SgiClass _ identifier _ _ -> [unGlobalId identifier]

structureGlobals :: Structure -> [Int]
structureGlobals structure = case locatedValue structure of
  StrConst declarations -> concatMap declarationGlobals declarations
  StrVar identifier -> [unGlobalId identifier]
  StrProj base _ -> structureGlobals base
  StrFun _ identifier domain range body -> unGlobalId identifier : signatureGlobals domain <> signatureGlobals range <> structureGlobals body
  StrApp function argument -> structureGlobals function <> structureGlobals argument
  StrError -> []

noLocation :: Span
noLocation = noSpan
