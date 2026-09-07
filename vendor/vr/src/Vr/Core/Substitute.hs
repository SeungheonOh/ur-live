-- | Capture-avoiding substitution and normalization for Core's kind and
-- constructor binders.  Specialization uses these operations to make every
-- static application concrete before Mono lowering.
module Vr.Core.Substitute
  ( substituteCon
  , substituteConInExpr
  , substituteKind
  , substituteKindInCon
  , substituteKindInExpr
  , substituteValue
  , liftExprValues
  , liftCon
  , patternBindingCount
  , semanticCon
  , semanticKind
  , normalizeCon
  , normalizeConWith
  , normalizeExprHead
  ) where

import qualified Vr.Core.Syntax as C
import Vr.Source (Located (..), noSpan)

-- | Substitute a runtime expression for one de Bruijn value variable.
-- Constructor and kind binders do not affect value indices; value lambdas,
-- lets, and pattern binders do.
substituteValue :: Int -> C.Expr -> C.Expr -> C.Expr
substituteValue depth replacement expression = expression {locatedValue = case locatedValue expression of
  C.ERel index
    | index == depth -> locatedValue (liftExprValues 0 depth replacement)
    | index > depth -> C.ERel (index - 1)
    | otherwise -> C.ERel index
  C.ECon classification constructor arguments payload -> C.ECon classification constructor arguments (fmap go payload)
  C.EFfiApp moduleName name arguments -> C.EFfiApp moduleName name [(go value, typ) | (value, typ) <- arguments]
  C.EApp function argument -> C.EApp (go function) (go argument)
  C.EAbs name domain range body -> C.EAbs name domain range (substituteValue (depth + 1) replacement body)
  C.ECApp function argument -> C.ECApp (go function) argument
  -- A value substituted below a constructor binder keeps the same value
  -- index, but every free constructor mentioned by that value moves out by
  -- one level.  CoreEnv.subExpInExp in Ur/Web performs this same RelC lift.
  C.ECAbs name kind body ->
    C.ECAbs name kind (substituteValue depth (liftConInExpr 0 1 replacement) body)
  C.EKAbs name body -> C.EKAbs name (go body)
  C.EKApp function kind -> C.EKApp (go function) kind
  C.ERecord fields -> C.ERecord [(field, go value, typ) | (field, value, typ) <- fields]
  C.EField record field typ rest -> C.EField (go record) field typ rest
  C.EConcat left leftRow right rightRow -> C.EConcat (go left) leftRow (go right) rightRow
  C.ECut record field typ rest -> C.ECut (go record) field typ rest
  C.ECutMulti record fields rest -> C.ECutMulti (go record) fields rest
  C.ECase scrutinee branches input result -> C.ECase
    (go scrutinee)
    [(pattern', substituteValue (depth + patternBindingCount pattern') replacement body) | (pattern', body) <- branches]
    input result
  C.EWrite value -> C.EWrite (go value)
  C.EClosure identifier captures -> C.EClosure identifier (map go captures)
  C.ELet name typ value body -> C.ELet name typ (go value) (substituteValue (depth + 1) replacement body)
  C.EServerCall identifier arguments typ failureMode -> C.EServerCall identifier (map go arguments) typ failureMode
  other -> other}
  where go = substituteValue depth replacement

-- | Shift free runtime value variables at or beyond a cutoff.
liftExprValues :: Int -> Int -> C.Expr -> C.Expr
liftExprValues _ 0 = id
liftExprValues cutoff amount = walk 0
  where
    walk bound expression = expression {locatedValue = case locatedValue expression of
      C.ERel index | index >= cutoff + bound -> C.ERel (index + amount)
      C.ECon classification constructor arguments payload -> C.ECon classification constructor arguments (fmap (walk bound) payload)
      C.EFfiApp moduleName name arguments -> C.EFfiApp moduleName name [(walk bound value, typ) | (value, typ) <- arguments]
      C.EApp function argument -> C.EApp (walk bound function) (walk bound argument)
      C.EAbs name domain range body -> C.EAbs name domain range (walk (bound + 1) body)
      C.ECApp function argument -> C.ECApp (walk bound function) argument
      C.ECAbs name kind body -> C.ECAbs name kind (walk bound body)
      C.EKAbs name body -> C.EKAbs name (walk bound body)
      C.EKApp function kind -> C.EKApp (walk bound function) kind
      C.ERecord fields -> C.ERecord [(field, walk bound value, typ) | (field, value, typ) <- fields]
      C.EField record field typ rest -> C.EField (walk bound record) field typ rest
      C.EConcat left leftRow right rightRow -> C.EConcat (walk bound left) leftRow (walk bound right) rightRow
      C.ECut record field typ rest -> C.ECut (walk bound record) field typ rest
      C.ECutMulti record fields rest -> C.ECutMulti (walk bound record) fields rest
      C.ECase scrutinee branches input result -> C.ECase
        (walk bound scrutinee)
        [(pattern', walk (bound + patternBindingCount pattern') body) | (pattern', body) <- branches]
        input result
      C.EWrite value -> C.EWrite (walk bound value)
      C.EClosure identifier captures -> C.EClosure identifier (map (walk bound) captures)
      C.ELet name typ value body -> C.ELet name typ (walk bound value) (walk (bound + 1) body)
      C.EServerCall identifier arguments typ failureMode -> C.EServerCall identifier (map (walk bound) arguments) typ failureMode
      other -> other}

patternBindingCount :: C.Pattern -> Int
patternBindingCount pattern' = case locatedValue pattern' of
  C.PVar {} -> 1
  C.PCon _ _ _ nested -> maybe 0 patternBindingCount nested
  C.PRecord fields -> sum [patternBindingCount nested | (_, nested, _) <- fields]
  C.PPrim {} -> 0

-- | Canonical, location-free constructor used for memo-table identity.
-- Source spans are diagnostic metadata and Ur/Web's 'CoreUtil.Con.compare'
-- deliberately ignores them.
semanticCon :: C.Con -> C.Con
semanticCon source = strip (normalizeCon source)
  where
    strip constructor = Located noSpan $ case locatedValue constructor of
      C.TFun domain range -> C.TFun (strip domain) (strip range)
      C.TCFun name kind body -> C.TCFun name (semanticKind kind) (strip body)
      C.TRecord row -> C.TRecord (strip row)
      C.CApp function argument -> C.CApp (strip function) (strip argument)
      C.CAbs name kind body -> C.CAbs name (semanticKind kind) (strip body)
      C.CKAbs name body -> C.CKAbs name (strip body)
      C.CKApp function kind -> C.CKApp (strip function) (semanticKind kind)
      C.TKFun name body -> C.TKFun name (strip body)
      C.CRecord kind fields -> C.CRecord (semanticKind kind) [(strip name, strip value) | (name, value) <- fields]
      C.CConcat left right -> C.CConcat (strip left) (strip right)
      C.CMap domain range -> C.CMap (semanticKind domain) (semanticKind range)
      C.CTuple elements -> C.CTuple (map strip elements)
      C.CProj tuple index -> C.CProj (strip tuple) index
      other -> other

-- | Location-free kind identity matching the reference comparator.
semanticKind :: C.Kind -> C.Kind
semanticKind kind = Located noSpan $ case locatedValue kind of
  C.KArrow domain range -> C.KArrow (semanticKind domain) (semanticKind range)
  C.KRecord element -> C.KRecord (semanticKind element)
  C.KTuple elements -> C.KTuple (map semanticKind elements)
  C.KFun name body -> C.KFun name (semanticKind body)
  other -> other

substituteCon :: Int -> C.Con -> C.Con -> C.Con
substituteCon depth replacement constructor = constructor {locatedValue = case locatedValue constructor of
  C.CRel index
    | index == depth -> locatedValue (liftCon 0 depth replacement)
    | index > depth -> C.CRel (index - 1)
    | otherwise -> C.CRel index
  C.TFun domain range -> C.TFun (go domain) (go range)
  C.TCFun name kind body -> C.TCFun name kind (substituteCon (depth + 1) replacement body)
  C.TRecord row -> C.TRecord (go row)
  C.CApp function argument -> C.CApp (go function) (go argument)
  C.CAbs name kind body -> C.CAbs name kind (substituteCon (depth + 1) replacement body)
  C.CKAbs name body -> C.CKAbs name (go body)
  C.CKApp function kind -> C.CKApp (go function) kind
  C.TKFun name body -> C.TKFun name (go body)
  C.CRecord kind fields -> C.CRecord kind [(go field, go value) | (field, value) <- fields]
  C.CConcat left right -> C.CConcat (go left) (go right)
  C.CTuple elements -> C.CTuple (map go elements)
  C.CProj tuple index -> C.CProj (go tuple) index
  other -> other}
  where go = substituteCon depth replacement

substituteKind :: Int -> C.Kind -> C.Kind -> C.Kind
substituteKind depth replacement kind = kind {locatedValue = case locatedValue kind of
  C.KRel index
    | index == depth -> locatedValue (liftKind 0 depth replacement)
    | index > depth -> C.KRel (index - 1)
    | otherwise -> C.KRel index
  C.KArrow domain range -> C.KArrow (go domain) (go range)
  C.KRecord element -> C.KRecord (go element)
  C.KTuple elements -> C.KTuple (map go elements)
  C.KFun name body -> C.KFun name (substituteKind (depth + 1) replacement body)
  other -> other}
  where go = substituteKind depth replacement

substituteKindInCon :: Int -> C.Kind -> C.Con -> C.Con
substituteKindInCon depth replacement constructor = constructor {locatedValue = case locatedValue constructor of
  C.TFun domain range -> C.TFun (go domain) (go range)
  C.TCFun name kind body -> C.TCFun name (substituteKind depth replacement kind) (go body)
  C.TRecord row -> C.TRecord (go row)
  C.CApp function argument -> C.CApp (go function) (go argument)
  C.CAbs name kind body -> C.CAbs name (substituteKind depth replacement kind) (go body)
  C.CKAbs name body -> C.CKAbs name (substituteKindInCon (depth + 1) replacement body)
  C.CKApp function kind -> C.CKApp (go function) (substituteKind depth replacement kind)
  C.TKFun name body -> C.TKFun name (substituteKindInCon (depth + 1) replacement body)
  C.CRecord kind fields -> C.CRecord (substituteKind depth replacement kind) [(go field, go value) | (field, value) <- fields]
  C.CConcat left right -> C.CConcat (go left) (go right)
  C.CMap domain range -> C.CMap (substituteKind depth replacement domain) (substituteKind depth replacement range)
  C.CTuple elements -> C.CTuple (map go elements)
  C.CProj tuple index -> C.CProj (go tuple) index
  other -> other}
  where go = substituteKindInCon depth replacement

substituteConInExpr :: Int -> C.Con -> C.Expr -> C.Expr
substituteConInExpr depth replacement expression = expression {locatedValue = case locatedValue expression of
  C.ECon classification constructor arguments payload -> C.ECon classification (conPat constructor) (map con arguments) (fmap go payload)
  C.EFfiApp moduleName name arguments -> C.EFfiApp moduleName name [(go value, con typ) | (value, typ) <- arguments]
  C.EApp function argument -> C.EApp (go function) (go argument)
  C.EAbs name domain range body -> C.EAbs name (con domain) (con range) (go body)
  C.ECApp function argument -> C.ECApp (go function) (con argument)
  C.ECAbs name kind body -> C.ECAbs name kind (substituteConInExpr (depth + 1) replacement body)
  C.EKAbs name body -> C.EKAbs name (go body)
  C.EKApp function kind -> C.EKApp (go function) kind
  C.ERecord fields -> C.ERecord [(con field, go value, con typ) | (field, value, typ) <- fields]
  C.EField record field typ rest -> C.EField (go record) (con field) (con typ) (con rest)
  C.EConcat left leftRow right rightRow -> C.EConcat (go left) (con leftRow) (go right) (con rightRow)
  C.ECut record field typ rest -> C.ECut (go record) (con field) (con typ) (con rest)
  C.ECutMulti record fields rest -> C.ECutMulti (go record) (con fields) (con rest)
  C.ECase scrutinee branches input result -> C.ECase (go scrutinee) [(patternCon pattern', go body) | (pattern', body) <- branches] (con input) (con result)
  C.EWrite value -> C.EWrite (go value)
  C.EClosure identifier values -> C.EClosure identifier (map go values)
  C.ELet name typ value body -> C.ELet name (con typ) (go value) (go body)
  C.EServerCall identifier values typ failureMode -> C.EServerCall identifier (map go values) (con typ) failureMode
  other -> other}
  where
    go = substituteConInExpr depth replacement
    con = substituteCon depth replacement
    conPat constructor = case constructor of
      C.PConFfi moduleName datatypeName parameters name payload classification ->
        C.PConFfi moduleName datatypeName parameters name (fmap con payload) classification
      other -> other
    patternCon pattern' = pattern' {locatedValue = case locatedValue pattern' of
      C.PVar name typ -> C.PVar name (con typ)
      C.PCon classification constructor arguments nested -> C.PCon classification (conPat constructor) (map con arguments) (fmap patternCon nested)
      C.PRecord fields -> C.PRecord [(name, patternCon nested, con typ) | (name, nested, typ) <- fields]
      other -> other}

substituteKindInExpr :: Int -> C.Kind -> C.Expr -> C.Expr
substituteKindInExpr depth replacement expression = expression {locatedValue = case locatedValue expression of
  C.ECon classification constructor arguments payload -> C.ECon classification (kindPat constructor) (map con arguments) (fmap go payload)
  C.EFfiApp moduleName name arguments -> C.EFfiApp moduleName name [(go value, con typ) | (value, typ) <- arguments]
  C.EApp function argument -> C.EApp (go function) (go argument)
  C.EAbs name domain range body -> C.EAbs name (con domain) (con range) (go body)
  C.ECApp function argument -> C.ECApp (go function) (con argument)
  C.ECAbs name kind body -> C.ECAbs name (substituteKind depth replacement kind) (go body)
  C.EKAbs name body -> C.EKAbs name (substituteKindInExpr (depth + 1) replacement body)
  C.EKApp function kind -> C.EKApp (go function) (substituteKind depth replacement kind)
  C.ERecord fields -> C.ERecord [(con field, go value, con typ) | (field, value, typ) <- fields]
  C.EField record field typ rest -> C.EField (go record) (con field) (con typ) (con rest)
  C.EConcat left leftRow right rightRow -> C.EConcat (go left) (con leftRow) (go right) (con rightRow)
  C.ECut record field typ rest -> C.ECut (go record) (con field) (con typ) (con rest)
  C.ECutMulti record fields rest -> C.ECutMulti (go record) (con fields) (con rest)
  C.ECase scrutinee branches input result -> C.ECase (go scrutinee) [(patternKind pattern', go body) | (pattern', body) <- branches] (con input) (con result)
  C.EWrite value -> C.EWrite (go value)
  C.EClosure identifier values -> C.EClosure identifier (map go values)
  C.ELet name typ value body -> C.ELet name (con typ) (go value) (go body)
  C.EServerCall identifier values typ failureMode -> C.EServerCall identifier (map go values) (con typ) failureMode
  other -> other}
  where
    go = substituteKindInExpr depth replacement
    con = substituteKindInCon depth replacement
    kindPat constructor = case constructor of
      C.PConFfi moduleName datatypeName parameters name payload classification ->
        C.PConFfi moduleName datatypeName parameters name (fmap con payload) classification
      other -> other
    patternKind pattern' = pattern' {locatedValue = case locatedValue pattern' of
      C.PVar name typ -> C.PVar name (con typ)
      C.PCon classification constructor arguments nested -> C.PCon classification (kindPat constructor) (map con arguments) (fmap patternKind nested)
      C.PRecord fields -> C.PRecord [(name, patternKind nested, con typ) | (name, nested, typ) <- fields]
      other -> other}

normalizeCon :: C.Con -> C.Con
normalizeCon = normalizeConWith normalizeCon

-- | Normalize one constructor using the supplied traversal for its children.
-- Core reduction uses this to expand aliases while visiting each original
-- node once. Substitution creates new redexes and still uses full ordinary
-- normalization: its arguments have already been expanded and normalized.
normalizeConWith :: (C.Con -> C.Con) -> C.Con -> C.Con
normalizeConWith child constructor = case locatedValue constructor of
  C.CApp function argument ->
    normalizeConApplication constructor (child function) (child argument)
  C.CKApp function kind ->
    let function' = child function
     in case locatedValue function' of
          C.CKAbs _ body -> normalizeCon (substituteKindInCon 0 kind body)
          _ -> constructor {locatedValue = C.CKApp function' kind}
  C.CProj tuple index ->
    let tuple' = child tuple
     in case locatedValue tuple' of
          C.CTuple elements | index >= 1 && index <= length elements -> elements !! (index - 1)
          _ -> constructor {locatedValue = C.CProj tuple' index}
  C.CConcat left right ->
    let left' = child left
        right' = child right
     in case (locatedValue left', locatedValue right') of
          (C.CRecord kind fields, C.CRecord _ more) -> constructor {locatedValue = C.CRecord kind (fields <> more)}
          (C.CRecord _ [], _) -> right'
          (_, C.CRecord _ []) -> left'
          _ -> constructor {locatedValue = C.CConcat left' right'}
  C.TFun domain range -> constructor {locatedValue = C.TFun (child domain) (child range)}
  C.TCFun name kind body -> constructor {locatedValue = C.TCFun name kind (child body)}
  C.TRecord row -> constructor {locatedValue = C.TRecord (child row)}
  C.CAbs name kind body -> constructor {locatedValue = C.CAbs name kind (child body)}
  C.CKAbs name body -> constructor {locatedValue = C.CKAbs name (child body)}
  C.TKFun name body -> constructor {locatedValue = C.TKFun name (child body)}
  C.CRecord kind fields -> constructor {locatedValue = C.CRecord kind [(child name, child value) | (name, value) <- fields]}
  C.CTuple elements -> constructor {locatedValue = C.CTuple (map child elements)}
  _ -> constructor

-- Both operands are already in normal form. Row-map reduction applies the
-- same mapper to every already-normalized field; walking either operand again
-- would duplicate that work for every column. Substitution can introduce new
-- redexes and still goes through full normalization, with the original spans.
normalizeConApplication :: C.Con -> C.Con -> C.Con -> C.Con
normalizeConApplication source function argument = case locatedValue function of
  C.CAbs _ _ body -> normalizeCon (substituteCon 0 argument body)
  C.CApp mapperHead mapper -> case (locatedValue mapperHead, locatedValue argument) of
    (C.CMap _ range, C.CRecord _ fields) -> source
      {locatedValue = C.CRecord range
        [(name, normalizeConApplication source mapper value) | (name, value) <- fields]}
    _ -> application
  _ -> application
  where
    application = source {locatedValue = C.CApp function argument}

normalizeExprHead :: C.Expr -> C.Expr
normalizeExprHead expression = case locatedValue expression of
  C.ECApp function argument ->
    let function' = normalizeExprHead function
     in case locatedValue function' of
          C.ECAbs _ _ body -> normalizeExprHead (substituteConInExpr 0 (normalizeCon argument) body)
          _ -> expression {locatedValue = C.ECApp function' (normalizeCon argument)}
  C.EKApp function kind ->
    let function' = normalizeExprHead function
     in case locatedValue function' of
          C.EKAbs _ body -> normalizeExprHead (substituteKindInExpr 0 kind body)
          _ -> expression {locatedValue = C.EKApp function' kind}
  _ -> expression

liftCon :: Int -> Int -> C.Con -> C.Con
liftCon _ 0 constructor = constructor
liftCon cutoff amount constructor = constructor {locatedValue = case locatedValue constructor of
  C.CRel index | index >= cutoff -> C.CRel (index + amount)
  C.TFun domain range -> C.TFun (go domain) (go range)
  C.TCFun name kind body -> C.TCFun name kind (liftCon (cutoff + 1) amount body)
  C.TRecord row -> C.TRecord (go row)
  C.CApp function argument -> C.CApp (go function) (go argument)
  C.CAbs name kind body -> C.CAbs name kind (liftCon (cutoff + 1) amount body)
  C.CKAbs name body -> C.CKAbs name (go body)
  C.CKApp function kind -> C.CKApp (go function) kind
  C.TKFun name body -> C.TKFun name (go body)
  C.CRecord kind fields -> C.CRecord kind [(go field, go value) | (field, value) <- fields]
  C.CConcat left right -> C.CConcat (go left) (go right)
  C.CTuple elements -> C.CTuple (map go elements)
  C.CProj tuple index -> C.CProj (go tuple) index
  other -> other}
  where go = liftCon cutoff amount

-- | Shift free constructor variables throughout an expression.  Expression
-- constructor abstractions extend the cutoff; value and kind binders do not.
-- This is needed when capture-avoiding value substitution carries an
-- expression across an 'ECAbs'.
liftConInExpr :: Int -> Int -> C.Expr -> C.Expr
liftConInExpr cutoff amount = walk 0
  where
    walk bound expression = expression {locatedValue = case locatedValue expression of
      C.ECon classification constructor arguments payload ->
        C.ECon classification (patCon bound constructor) (map (con bound) arguments) (fmap (walk bound) payload)
      C.EFfiApp moduleName name arguments ->
        C.EFfiApp moduleName name [(walk bound value, con bound typ) | (value, typ) <- arguments]
      C.EApp function argument -> C.EApp (walk bound function) (walk bound argument)
      C.EAbs name domain range body ->
        C.EAbs name (con bound domain) (con bound range) (walk bound body)
      C.ECApp function argument -> C.ECApp (walk bound function) (con bound argument)
      C.ECAbs name kind body -> C.ECAbs name kind (walk (bound + 1) body)
      C.EKAbs name body -> C.EKAbs name (walk bound body)
      C.EKApp function kind -> C.EKApp (walk bound function) kind
      C.ERecord fields ->
        C.ERecord [(con bound field, walk bound value, con bound typ) | (field, value, typ) <- fields]
      C.EField record field typ rest ->
        C.EField (walk bound record) (con bound field) (con bound typ) (con bound rest)
      C.EConcat left leftRow right rightRow ->
        C.EConcat (walk bound left) (con bound leftRow) (walk bound right) (con bound rightRow)
      C.ECut record field typ rest ->
        C.ECut (walk bound record) (con bound field) (con bound typ) (con bound rest)
      C.ECutMulti record fields rest ->
        C.ECutMulti (walk bound record) (con bound fields) (con bound rest)
      C.ECase scrutinee branches input result ->
        C.ECase
          (walk bound scrutinee)
          [(pattern bound pattern', walk bound body) | (pattern', body) <- branches]
          (con bound input)
          (con bound result)
      C.EWrite value -> C.EWrite (walk bound value)
      C.EClosure identifier values -> C.EClosure identifier (map (walk bound) values)
      C.ELet name typ value body ->
        C.ELet name (con bound typ) (walk bound value) (walk bound body)
      C.EServerCall identifier values typ failureMode ->
        C.EServerCall identifier (map (walk bound) values) (con bound typ) failureMode
      other -> other}

    con bound = liftCon (cutoff + bound) amount

    patCon bound constructor = case constructor of
      C.PConFfi moduleName datatypeName parameters name payload classification ->
        C.PConFfi moduleName datatypeName parameters name (fmap (con bound) payload) classification
      other -> other

    pattern bound pattern' = pattern' {locatedValue = case locatedValue pattern' of
      C.PVar name typ -> C.PVar name (con bound typ)
      C.PCon classification constructor arguments nested ->
        C.PCon classification (patCon bound constructor) (map (con bound) arguments) (fmap (pattern bound) nested)
      C.PRecord fields ->
        C.PRecord [(name, pattern bound nested, con bound typ) | (name, nested, typ) <- fields]
      other -> other}

liftKind :: Int -> Int -> C.Kind -> C.Kind
liftKind _ 0 kind = kind
liftKind cutoff amount kind = kind {locatedValue = case locatedValue kind of
  C.KRel index | index >= cutoff -> C.KRel (index + amount)
  C.KArrow domain range -> C.KArrow (go domain) (go range)
  C.KRecord element -> C.KRecord (go element)
  C.KTuple elements -> C.KTuple (map go elements)
  C.KFun name body -> C.KFun name (liftKind (cutoff + 1) amount body)
  other -> other}
  where go = liftKind cutoff amount
