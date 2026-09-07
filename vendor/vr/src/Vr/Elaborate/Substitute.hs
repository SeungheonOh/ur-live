{-# LANGUAGE LambdaCase #-}

module Vr.Elaborate.Substitute
  ( substituteCon
  , substituteKindInCon
  , substituteKind
  , liftKind
  , liftKindInCon
  , liftConInExpr
  , liftKindInExpr
  , liftCon
  , liftConMetaDepth
  , lowerCon
  ) where

import Vr.Elaborate.Syntax
import Vr.Source (Located (..))

substituteCon :: Int -> Con -> Con -> Con
substituteCon depth replacement constructor = case locatedValue constructor of
  CRel index
    | index == depth -> liftCon 0 depth replacement
    | index > depth -> constructor {locatedValue = CRel (index - 1)}
    | otherwise -> constructor
  TFun domain range -> two TFun domain range
  TCFun explicitness name kind body -> constructor {locatedValue = TCFun explicitness name kind (substituteCon (depth + 1) replacement body)}
  TRecord row -> one TRecord row
  TDisjoint left right body -> constructor {locatedValue = TDisjoint (go left) (go right) (go body)}
  CApp function argument -> two CApp function argument
  CAbs name kind body -> constructor {locatedValue = CAbs name kind (substituteCon (depth + 1) replacement body)}
  CKAbs name body -> constructor {locatedValue = CKAbs name (go body)}
  CKApp function kind -> constructor {locatedValue = CKApp (go function) kind}
  TKFun name body -> constructor {locatedValue = TKFun name (go body)}
  CRecord kind fields -> constructor {locatedValue = CRecord kind [(go name, go value) | (name, value) <- fields]}
  CConcat left right -> two CConcat left right
  CTuple elements -> constructor {locatedValue = CTuple (map go elements)}
  CProj tuple index -> constructor {locatedValue = CProj (go tuple) index}
  CMeta identifier level kind name -> constructor {locatedValue = CMeta identifier (max 0 (level - 1)) kind name}
  _ -> constructor
  where
    go = substituteCon depth replacement
    one make value = constructor {locatedValue = make (go value)}
    two make left right = constructor {locatedValue = make (go left) (go right)}

substituteKindInCon :: Int -> Kind -> Con -> Con
substituteKindInCon depth replacement constructor = case locatedValue constructor of
  TFun domain range -> two TFun domain range
  TCFun explicitness name kind body -> constructor {locatedValue = TCFun explicitness name (substituteKind depth replacement kind) (go body)}
  TRecord row -> one TRecord row
  TDisjoint left right body -> constructor {locatedValue = TDisjoint (go left) (go right) (go body)}
  CApp function argument -> two CApp function argument
  CAbs name kind body -> constructor {locatedValue = CAbs name (substituteKind depth replacement kind) (go body)}
  CKAbs name body -> constructor {locatedValue = CKAbs name (substituteKindInCon (depth + 1) replacement body)}
  CKApp function kind -> constructor {locatedValue = CKApp (go function) (substituteKind depth replacement kind)}
  TKFun name body -> constructor {locatedValue = TKFun name (substituteKindInCon (depth + 1) replacement body)}
  CRecord kind fields -> constructor {locatedValue = CRecord (substituteKind depth replacement kind) [(go name, go value) | (name, value) <- fields]}
  CConcat left right -> two CConcat left right
  CMap domain range -> constructor {locatedValue = CMap (substituteKind depth replacement domain) (substituteKind depth replacement range)}
  CTuple elements -> constructor {locatedValue = CTuple (map go elements)}
  CProj tuple index -> constructor {locatedValue = CProj (go tuple) index}
  CMeta identifier lift kind name -> constructor {locatedValue = CMeta identifier lift (substituteKind depth replacement kind) name}
  _ -> constructor
  where
    go = substituteKindInCon depth replacement
    one make value = constructor {locatedValue = make (go value)}
    two make left right = constructor {locatedValue = make (go left) (go right)}

substituteKind :: Int -> Kind -> Kind -> Kind
substituteKind depth replacement kind = case locatedValue kind of
  KRel index
    | index == depth -> liftKind 0 depth replacement
    | index > depth -> kind {locatedValue = KRel (index - 1)}
    | otherwise -> kind
  KArrow domain range -> kind {locatedValue = KArrow (go domain) (go range)}
  KRecord element -> kind {locatedValue = KRecord (go element)}
  KTuple elements -> kind {locatedValue = KTuple (map go elements)}
  KFun name body -> kind {locatedValue = KFun name (substituteKind (depth + 1) replacement body)}
  _ -> kind
  where go = substituteKind depth replacement

liftKind :: Int -> Int -> Kind -> Kind
liftKind cutoff amount kind = case locatedValue kind of
  KRel index
    | index >= cutoff -> kind {locatedValue = KRel (index + amount)}
    | otherwise -> kind
  KArrow domain range -> kind {locatedValue = KArrow (go domain) (go range)}
  KRecord element -> kind {locatedValue = KRecord (go element)}
  KTuple elements -> kind {locatedValue = KTuple (map go elements)}
  KFun name body -> kind {locatedValue = KFun name (liftKind (cutoff + 1) amount body)}
  _ -> kind
  where go = liftKind cutoff amount

liftKindInCon :: Int -> Int -> Con -> Con
liftKindInCon cutoff amount constructor = constructor {locatedValue = case locatedValue constructor of
  TFun domain range -> TFun (go domain) (go range)
  TCFun explicitness name kind body -> TCFun explicitness name (liftKind cutoff amount kind) (go body)
  TRecord row -> TRecord (go row)
  TDisjoint left right body -> TDisjoint (go left) (go right) (go body)
  CApp function argument -> CApp (go function) (go argument)
  CAbs name kind body -> CAbs name (liftKind cutoff amount kind) (go body)
  CKAbs name body -> CKAbs name (liftKindInCon (cutoff + 1) amount body)
  CKApp function kind -> CKApp (go function) (liftKind cutoff amount kind)
  TKFun name body -> TKFun name (liftKindInCon (cutoff + 1) amount body)
  CRecord kind fields -> CRecord (liftKind cutoff amount kind) [(go name, go value) | (name, value) <- fields]
  CConcat left right -> CConcat (go left) (go right)
  CMap domain range -> CMap (liftKind cutoff amount domain) (liftKind cutoff amount range)
  CTuple elements -> CTuple (map go elements)
  CProj tuple index -> CProj (go tuple) index
  CMeta identifier level kind name -> CMeta identifier level (liftKind cutoff amount kind) name
  other -> other}
  where go = liftKindInCon cutoff amount

liftConInPattern :: Int -> Int -> Pattern -> Pattern
liftConInPattern cutoff amount pattern' = pattern' {locatedValue = case locatedValue pattern' of
  PVar name typ -> PVar name (liftCon cutoff amount typ)
  PCon classification constructor parameters argument ->
    PCon classification constructor (map (liftCon cutoff amount) parameters) (fmap go argument)
  PRecord fields flexible -> PRecord [(name, go value, liftCon cutoff amount typ) | (name, value, typ) <- fields] flexible
  other -> other}
  where go = liftConInPattern cutoff amount

liftKindInPattern :: Int -> Int -> Pattern -> Pattern
liftKindInPattern cutoff amount pattern' = pattern' {locatedValue = case locatedValue pattern' of
  PVar name typ -> PVar name (liftKindInCon cutoff amount typ)
  PCon classification constructor parameters argument ->
    PCon classification constructor (map (liftKindInCon cutoff amount) parameters) (fmap go argument)
  PRecord fields flexible -> PRecord [(name, go value, liftKindInCon cutoff amount typ) | (name, value, typ) <- fields] flexible
  other -> other}
  where go = liftKindInPattern cutoff amount

liftConInExpr :: Int -> Int -> Expr -> Expr
liftConInExpr cutoff amount expression = expression {locatedValue = case locatedValue expression of
  EApp function argument -> EApp (go function) (go argument)
  EAbs name domain range body -> EAbs name (liftCon cutoff amount domain) (liftCon cutoff amount range) (go body)
  ECApp function argument -> ECApp (go function) (liftCon cutoff amount argument)
  ECAbs explicitness name kind body -> ECAbs explicitness name kind (liftConInExpr (cutoff + 1) amount body)
  EKAbs name body -> EKAbs name (go body)
  EKApp function kind -> EKApp (go function) kind
  ERecord fields -> ERecord [(liftCon cutoff amount name, go value, liftCon cutoff amount typ) | (name, value, typ) <- fields]
  EField record name field rest -> EField (go record) (liftCon cutoff amount name) (liftCon cutoff amount field) (liftCon cutoff amount rest)
  EConcat left leftType right rightType -> EConcat (go left) (liftCon cutoff amount leftType) (go right) (liftCon cutoff amount rightType)
  ECut record name field rest -> ECut (go record) (liftCon cutoff amount name) (liftCon cutoff amount field) (liftCon cutoff amount rest)
  ECutMulti record fields rest -> ECutMulti (go record) (liftCon cutoff amount fields) (liftCon cutoff amount rest)
  ECase scrutinee branches discriminant result ->
    ECase (go scrutinee) [(liftConInPattern cutoff amount pattern', go body) | (pattern', body) <- branches]
      (liftCon cutoff amount discriminant) (liftCon cutoff amount result)
  ELet declarations body typ -> ELet (map liftDeclaration declarations) (go body) (liftCon cutoff amount typ)
  other -> other}
  where
    go = liftConInExpr cutoff amount
    liftDeclaration declaration = declaration {locatedValue = case locatedValue declaration of
      EDVal pattern' typ value -> EDVal (liftConInPattern cutoff amount pattern') (liftCon cutoff amount typ) (go value)
      EDValRec bindings -> EDValRec [(name, liftCon cutoff amount typ, go value) | (name, typ, value) <- bindings]}

liftKindInExpr :: Int -> Int -> Expr -> Expr
liftKindInExpr cutoff amount expression = expression {locatedValue = case locatedValue expression of
  EApp function argument -> EApp (go function) (go argument)
  EAbs name domain range body -> EAbs name (liftKindInCon cutoff amount domain) (liftKindInCon cutoff amount range) (go body)
  ECApp function argument -> ECApp (go function) (liftKindInCon cutoff amount argument)
  ECAbs explicitness name kind body -> ECAbs explicitness name (liftKind cutoff amount kind) (go body)
  EKAbs name body -> EKAbs name (liftKindInExpr (cutoff + 1) amount body)
  EKApp function kind -> EKApp (go function) (liftKind cutoff amount kind)
  ERecord fields -> ERecord [(liftKindInCon cutoff amount name, go value, liftKindInCon cutoff amount typ) | (name, value, typ) <- fields]
  EField record name field rest -> EField (go record) (liftKindInCon cutoff amount name) (liftKindInCon cutoff amount field) (liftKindInCon cutoff amount rest)
  EConcat left leftType right rightType -> EConcat (go left) (liftKindInCon cutoff amount leftType) (go right) (liftKindInCon cutoff amount rightType)
  ECut record name field rest -> ECut (go record) (liftKindInCon cutoff amount name) (liftKindInCon cutoff amount field) (liftKindInCon cutoff amount rest)
  ECutMulti record fields rest -> ECutMulti (go record) (liftKindInCon cutoff amount fields) (liftKindInCon cutoff amount rest)
  ECase scrutinee branches discriminant result ->
    ECase (go scrutinee) [(liftKindInPattern cutoff amount pattern', go body) | (pattern', body) <- branches]
      (liftKindInCon cutoff amount discriminant) (liftKindInCon cutoff amount result)
  ELet declarations body typ -> ELet (map liftDeclaration declarations) (go body) (liftKindInCon cutoff amount typ)
  other -> other}
  where
    go = liftKindInExpr cutoff amount
    liftDeclaration declaration = declaration {locatedValue = case locatedValue declaration of
      EDVal pattern' typ value -> EDVal (liftKindInPattern cutoff amount pattern') (liftKindInCon cutoff amount typ) (go value)
      EDValRec bindings -> EDValRec [(name, liftKindInCon cutoff amount typ, go value) | (name, typ, value) <- bindings]}

liftCon :: Int -> Int -> Con -> Con
-- A zero shift preserves every index and metavariable level. Reuse the tree
-- when following a solved metavariable at its original constructor depth.
liftCon _ 0 constructor = constructor
liftCon cutoff amount constructor = case locatedValue constructor of
  CRel index | index >= cutoff -> constructor {locatedValue = CRel (index + amount)}
  TFun domain range -> two TFun domain range
  TCFun explicitness name kind body -> constructor {locatedValue = TCFun explicitness name kind (liftCon (cutoff + 1) amount body)}
  TRecord row -> one TRecord row
  TDisjoint left right body -> constructor {locatedValue = TDisjoint (go left) (go right) (go body)}
  CApp function argument -> two CApp function argument
  CAbs name kind body -> constructor {locatedValue = CAbs name kind (liftCon (cutoff + 1) amount body)}
  CKAbs name body -> constructor {locatedValue = CKAbs name (go body)}
  CKApp function kind -> constructor {locatedValue = CKApp (go function) kind}
  TKFun name body -> constructor {locatedValue = TKFun name (go body)}
  CRecord kind fields -> constructor {locatedValue = CRecord kind [(go name, go value) | (name, value) <- fields]}
  CConcat left right -> two CConcat left right
  CTuple elements -> constructor {locatedValue = CTuple (map go elements)}
  CProj tuple index -> constructor {locatedValue = CProj (go tuple) index}
  CMeta identifier level kind name -> constructor {locatedValue = CMeta identifier (level + amount) kind name}
  _ -> constructor
  where
    go = liftCon cutoff amount
    one make value = constructor {locatedValue = make (go value)}
    two make left right = constructor {locatedValue = make (go left) (go right)}

-- Named value schemes are closed with respect to ordinary de Bruijn
-- constructors, but their unsolved inference variables must remember how many
-- constructor binders surround a later use site.
liftConMetaDepth :: Int -> Con -> Con
liftConMetaDepth amount constructor = constructor {locatedValue = case locatedValue constructor of
  TFun domain range -> TFun (go domain) (go range)
  TCFun explicitness name kind body -> TCFun explicitness name kind body
  TRecord row -> TRecord (go row)
  TDisjoint left right body -> TDisjoint (go left) (go right) (go body)
  CApp function argument -> CApp (go function) (go argument)
  CAbs name kind body -> CAbs name kind body
  CKAbs name body -> CKAbs name body
  CKApp function kind -> CKApp (go function) kind
  TKFun name body -> TKFun name body
  CRecord kind fields -> CRecord kind [(go name, go value) | (name, value) <- fields]
  CConcat left right -> CConcat (go left) (go right)
  CTuple elements -> CTuple (map go elements)
  CProj tuple index -> CProj (go tuple) index
  CMeta identifier level kind name -> CMeta identifier (level + amount) kind name
  other -> other}
  where
    go = liftConMetaDepth amount

-- Remove a number of surrounding constructor binders.  Failure means that the
-- constructor mentions one of those binders and therefore cannot be stored as
-- the solution of an inference variable created outside their scope.
lowerCon :: Int -> Con -> Maybe Con
lowerCon amount = go 0
  where
    go bound constructor = case locatedValue constructor of
      CRel index
        | index < bound -> Just constructor
        | index - bound < amount -> Nothing
        | otherwise -> Just constructor {locatedValue = CRel (index - amount)}
      TFun domain range -> two bound constructor TFun domain range
      TCFun explicitness name kind body -> do
        body' <- go (bound + 1) body
        pure constructor {locatedValue = TCFun explicitness name kind body'}
      TRecord row -> one bound constructor TRecord row
      TDisjoint left right body -> do
        left' <- go bound left
        right' <- go bound right
        body' <- go bound body
        pure constructor {locatedValue = TDisjoint left' right' body'}
      CApp function argument -> two bound constructor CApp function argument
      CAbs name kind body -> do
        body' <- go (bound + 1) body
        pure constructor {locatedValue = CAbs name kind body'}
      CKAbs name body -> (\body' -> constructor {locatedValue = CKAbs name body'}) <$> go bound body
      CKApp function kind -> (\function' -> constructor {locatedValue = CKApp function' kind}) <$> go bound function
      TKFun name body -> (\body' -> constructor {locatedValue = TKFun name body'}) <$> go bound body
      CRecord kind fields -> do
        fields' <- mapM (\(name, value) -> (,) <$> go bound name <*> go bound value) fields
        pure constructor {locatedValue = CRecord kind fields'}
      CConcat left right -> two bound constructor CConcat left right
      CTuple elements -> (\elements' -> constructor {locatedValue = CTuple elements'}) <$> mapM (go bound) elements
      CProj tuple index -> (\tuple' -> constructor {locatedValue = CProj tuple' index}) <$> go bound tuple
      CMeta identifier level kind name
        | level < amount -> Nothing
        | otherwise -> Just constructor {locatedValue = CMeta identifier (level - amount) kind name}
      _ -> Just constructor
    one bound original make value = (\value' -> original {locatedValue = make value'}) <$> go bound value
    two bound original make left right = do
      left' <- go bound left
      right' <- go bound right
      pure original {locatedValue = make left' right'}
