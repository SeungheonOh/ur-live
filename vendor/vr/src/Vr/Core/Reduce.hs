{-# LANGUAGE DerivingStrategies #-}

-- | Ur/Web-compatible Core reduction and global inlining policy.
--
-- This is the reduction pass immediately before @Unpoly@ in the reference
-- pipeline.  In particular, an ordinary polymorphic global is always an
-- inline candidate (unless its canonical path is listed by @neverInline@),
-- independent of call count or body size.
module Vr.Core.Reduce
  ( ReduceSettings (..)
  , defaultReduceSettings
  , reduceFile
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Vr.Core.Substitute as Substitute
import qualified Vr.Core.Syntax as C
import Vr.Source (Located (..), Span)

data ReduceSettings = ReduceSettings
  { reduceCoreInline :: !Int
  , reduceNeverInline :: !(Set.Set String)
  }
  deriving stock (Eq, Show)

defaultReduceSettings :: ReduceSettings
defaultReduceSettings = ReduceSettings 5 Set.empty

data ReduceState = ReduceState
  { stateAliases :: !(Map.Map C.GlobalId C.Con)
  , stateInlineValues :: !(Map.Map C.GlobalId C.Expr)
  }

reduceFile :: ReduceSettings -> C.File -> C.File
reduceFile settings file = reverse declarations
  where
    uses = valueUseCounts file
    (declarations, _) = foldl step ([], ReduceState Map.empty Map.empty) file
    step (done, state) declaration =
      let (declaration', state') = reduceDeclaration settings uses state declaration
       in (declaration' : done, state')

reduceDeclaration
  :: ReduceSettings
  -> Map.Map C.GlobalId Int
  -> ReduceState
  -> C.Decl
  -> (C.Decl, ReduceState)
reduceDeclaration settings uses state declaration = case locatedValue declaration of
  C.DCon name identifier kind definition ->
    let definition' = reduceCon state definition
     in (at (C.DCon name identifier kind definition'), state {stateAliases = Map.insert identifier definition' (stateAliases state)})
  C.DForeign moduleName name typ ->
    (at (C.DForeign moduleName name (reduceCon state typ)), state)
  C.DDatatype definitions ->
    (at (C.DDatatype (map datatype definitions)), state)
  C.DVal name identifier typ expression url ->
    let typ' = reduceCon state typ
        expression' = reduceExpr state Set.empty expression
        declaration' = at (C.DVal name identifier typ' expression' url)
        state'
          | mayInline settings uses identifier typ' expression' url =
              state {stateInlineValues = Map.insert identifier expression' (stateInlineValues state)}
          | otherwise = state
     in (declaration', state')
  C.DValRec bindings ->
    (at (C.DValRec (map binding bindings)), state)
  C.DExport {} -> (declaration, state)
  C.DTable name identifier row sqlName primary keys constraints uniques ->
    ( at (C.DTable name identifier (con row) sqlName (expr primary) (con keys) (expr constraints) (con uniques))
    , state
    )
  C.DSequence {} -> (declaration, state)
  C.DView name identifier sqlName expression row ->
    (at (C.DView name identifier sqlName (expr expression) (con row)), state)
  C.DIndex table modes -> (at (C.DIndex (expr table) (expr modes)), state)
  C.DDatabase {} -> (declaration, state)
  C.DCookie name identifier typ runtimeName ->
    (at (C.DCookie name identifier (con typ) runtimeName), state)
  C.DStyle {} -> (declaration, state)
  C.DTask kind body -> (at (C.DTask (expr kind) (expr body)), state)
  C.DPolicy expression -> (at (C.DPolicy (expr expression)), state)
  C.DOnError {} -> (declaration, state)
  where
    at = Located (locatedSpan declaration)
    con = reduceCon state
    expr = reduceExpr state Set.empty
    datatype (name, identifier, parameters, constructors) =
      (name, identifier, parameters, [(constructorName, constructorId, fmap con payload) | (constructorName, constructorId, payload) <- constructors])
    binding (name, identifier, typ, expression, url) =
      (name, identifier, con typ, expr expression, url)

mayInline
  :: ReduceSettings
  -> Map.Map C.GlobalId Int
  -> C.GlobalId
  -> C.Con
  -> C.Expr
  -> String
  -> Bool
mayInline settings uses identifier typ expression url =
  not (pathMember (reduceNeverInline settings) url)
    && case Map.lookup identifier uses of
      Nothing -> False
      Just count ->
        count <= 1
          || isRecord expression
          || isPolicy typ
          || isPolymorphic typ
          || expressionSizeAtMost (reduceCoreInline settings) expression
  where
    isRecord value = case locatedValue value of C.ERecord {} -> True; _ -> False
    -- The caller has already reduced the complete declaration type. Repeating
    -- that traversal here (and again for polymorphism) changes no decision.
    isPolicy constructor = case locatedValue constructor of
      C.CFfi "Basis" "sql_policy" -> True
      C.TFun _ result -> isPolicy result
      _ -> False

pathMember :: Set.Set String -> String -> Bool
pathMember = flip Set.member

reduceCon :: ReduceState -> C.Con -> C.Con
reduceCon state constructor = case locatedValue constructor of
  C.CNamed identifier
    | Just definition <- Map.lookup identifier (stateAliases state) ->
        -- DCon inserts the already-reduced definition. Like Ur/Web's namedC
        -- lookup, reuse that result: traversing it again copies the entire
        -- type at every reference and needlessly normalizes it again.
        definition
  C.CFfi "Basis" "monad" -> Substitute.normalizeCon (monadConstructor (locatedSpan constructor))
  _ -> Substitute.normalizeConWith (reduceCon state) constructor

reduceExpr :: ReduceState -> Set.Set C.GlobalId -> C.Expr -> C.Expr
reduceExpr state expanding source = case locatedValue source of
  C.ENamed identifier
    | Just definition <- Map.lookup identifier (stateInlineValues state) ->
        -- Inline entries were reduced before they entered the environment.
        -- Ur/Web returns that cached expression directly; reducing it again
        -- can repeat beta-reduction beneath open constructor binders.
        definition
  C.ECon classification constructor arguments payload ->
    at (C.ECon classification (reducePatCon state constructor) (map con arguments) (fmap expr payload))
  C.EFfi "Basis" "return" -> expr (basisReturn (locatedSpan source))
  C.EFfi "Basis" "bind" -> expr (basisBind (locatedSpan source))
  C.EFfi "Basis" "mkMonad" -> expr (basisMkMonad (locatedSpan source))
  C.EFfi "Basis" "transaction_monad" -> expr (basisMonadDictionary (locatedSpan source) "transaction")
  C.EFfi "Basis" "signal_monad" -> expr (basisMonadDictionary (locatedSpan source) "signal")
  C.EFfiApp moduleName name arguments ->
    at (C.EFfiApp moduleName name [(expr value, con typ) | (value, typ) <- arguments])
  C.EApp function argument -> reduceApplication source (expr function) (expr argument)
  C.EAbs name domain range body ->
    at (C.EAbs name (con domain) (con range) (expr body))
  C.ECApp function argument ->
    let function' = expr function
        argument' = con argument
     in case locatedValue function' of
          C.ECAbs _ _ body -> expr (Substitute.substituteConInExpr 0 argument' body)
          _ -> at (C.ECApp function' argument')
  C.ECAbs name kind body -> at (C.ECAbs name kind (expr body))
  C.EKAbs name body -> at (C.EKAbs name (expr body))
  C.EKApp function kind ->
    let function' = expr function
     in case locatedValue function' of
          C.EKAbs _ body -> expr (Substitute.substituteKindInExpr 0 kind body)
          _ -> at (C.EKApp function' kind)
  C.ERecord fields -> at (C.ERecord [(con field, expr value, con typ) | (field, value, typ) <- fields])
  C.EField record field typ rest ->
    let record' = expr record
        field' = con field
     in case locatedValue record' of
          C.ERecord fields -> case findField field' fields of
            Just (_, value, _) -> value
            Nothing -> at (C.EField record' field' (con typ) (con rest))
          _ -> at (C.EField record' field' (con typ) (con rest))
  C.EConcat left leftRow right rightRow ->
    let left' = expr left
        right' = expr right
     in case (locatedValue left', locatedValue right') of
          (C.ERecord first, C.ERecord second) -> at (C.ERecord (first <> second))
          _ -> at (C.EConcat left' (con leftRow) right' (con rightRow))
  C.ECut record field typ rest ->
    let record' = expr record
        field' = con field
     in case locatedValue record' of
          C.ERecord fields -> at (C.ERecord (filter (not . sameField field' . first3) fields))
          _ -> at (C.ECut record' field' (con typ) (con rest))
  C.ECutMulti record fields rest ->
    let record' = expr record
        removed = rowFieldNames (con fields)
     in case locatedValue record' of
          C.ERecord entries -> at (C.ERecord (filter (\entry -> all (\field -> not (sameField field (first3 entry))) removed) entries))
          _ -> at (C.ECutMulti record' (con fields) (con rest))
  C.ECase _ [(pattern', body)] _ _
    | C.PRecord [] <- locatedValue pattern' -> expr body
  C.ECase scrutinee branches input result ->
    reduceCase source (expr scrutinee) [(reducePattern state pattern', expr body) | (pattern', body) <- branches] (con input) (con result)
  C.EWrite value -> at (C.EWrite (expr value))
  C.EClosure identifier captures -> at (C.EClosure identifier (map expr captures))
  C.ELet name typ value body ->
    let value' = expr value
        body' = expr body
        typ' = con typ
     in if notFfi typ' && (relativeUsesUpToTwo 0 body' <= 1 || passive value' || functionInside typ')
          then expr (Substitute.substituteValue 0 value' body')
          else at (C.ELet name typ' value' body')
  C.EServerCall identifier arguments typ failureMode ->
    at (C.EServerCall identifier (map expr arguments) (con typ) failureMode)
  _ -> source
  where
    at = Located (locatedSpan source)
    con = reduceCon state
    expr = reduceExpr state expanding
    reduceApplication original function argument = case locatedValue function of
      C.EAbs name domain _ body
        | relativeUsesUpToTwo 0 body <= 1 || passive argument || functionInside domain ->
            expr (Substitute.substituteValue 0 argument body)
        | otherwise -> Located (locatedSpan original) (C.ELet name (con domain) argument body)
      _ -> Located (locatedSpan original) (C.EApp function argument)
    reduceCase original scrutinee branches input result = case firstMatching scrutinee branches of
      Just body -> expr body
      Nothing -> Located (locatedSpan original) (C.ECase scrutinee branches input result)

firstMatching :: C.Expr -> [(C.Pattern, C.Expr)] -> Maybe C.Expr
firstMatching _ [] = Nothing
firstMatching scrutinee ((pattern', body) : rest) = case locatedValue pattern' of
  C.PVar {} -> Just (Substitute.substituteValue 0 scrutinee body)
  C.PPrim expected -> case locatedValue scrutinee of
    C.EPrim actual | actual == expected -> Just body
    C.EPrim _ -> firstMatching scrutinee rest
    _ -> Nothing
  C.PCon _ expected _ nested -> case locatedValue scrutinee of
    C.ECon _ actual _ payload | samePatCon expected actual -> case (nested, payload) of
      (Nothing, Nothing) -> Just body
      (Just nestedPattern, Just value) -> firstMatching value [(nestedPattern, body)]
      _ -> Nothing
    C.ECon {} -> firstMatching scrutinee rest
    _ -> Nothing
  C.PRecord {} -> Nothing

reducePattern :: ReduceState -> C.Pattern -> C.Pattern
reducePattern state pattern' = pattern' {locatedValue = case locatedValue pattern' of
  C.PVar name typ -> C.PVar name (reduceCon state typ)
  C.PCon classification constructor arguments nested -> C.PCon classification (reducePatCon state constructor) (map (reduceCon state) arguments) (fmap (reducePattern state) nested)
  C.PRecord fields -> C.PRecord [(name, reducePattern state nested, reduceCon state typ) | (name, nested, typ) <- fields]
  other -> other}

reducePatCon :: ReduceState -> C.PatCon -> C.PatCon
reducePatCon state constructor = case constructor of
  C.PConFfi moduleName datatypeName parameters name payload classification ->
    C.PConFfi moduleName datatypeName parameters name (fmap (reduceCon state) payload) classification
  other -> other

samePatCon :: C.PatCon -> C.PatCon -> Bool
samePatCon (C.PConVar left) (C.PConVar right) = left == right
samePatCon (C.PConFfi lm ld _ lc _ _) (C.PConFfi rm rd _ rc _ _) = (lm, ld, lc) == (rm, rd, rc)
samePatCon _ _ = False

sameField :: C.Con -> C.Con -> Bool
sameField left right = Substitute.semanticCon left == Substitute.semanticCon right

findField :: C.Con -> [(C.Con, C.Expr, C.Con)] -> Maybe (C.Con, C.Expr, C.Con)
findField _ [] = Nothing
findField name (field : rest)
  | sameField name (first3 field) = Just field
  | otherwise = findField name rest

first3 :: (first, second, third) -> first
first3 (first, _, _) = first

rowFieldNames :: C.Con -> [C.Con]
rowFieldNames row = case locatedValue (Substitute.normalizeCon row) of
  C.CRecord _ fields -> map fst fields
  _ -> []

-- These definitions are the Core encodings used by Ur/Web's reducer for its
-- overloaded monad operations.  Expanding them here lets ordinary beta and
-- record reduction select transaction_return/transaction_bind (or their
-- signal counterparts) before Unpoly and Monoize.
monadConstructor :: Span -> C.Con
monadConstructor location =
  conAt location
    (C.CAbs "m" (kindAt location (C.KArrow (kindType location) (kindType location)))
      (monadRecord location (conRel location 0)))

returnType :: Span -> C.Con -> C.Con
returnType location monad =
  conAt location
    (C.TCFun "a" (kindType location)
      (conAt location
        (C.TFun
          (conRel location 0)
          (conAt location
            (C.CApp (Substitute.liftCon 0 1 monad) (conRel location 0))))))

bindType :: Span -> C.Con -> C.Con
bindType location monad =
  conAt location
    (C.TCFun "a" (kindType location)
      (conAt location
        (C.TCFun "b" (kindType location)
          (conAt location
            (C.TFun
              (conAt location
                (C.CApp (Substitute.liftCon 0 2 monad) (conRel location 1)))
              (conAt location
                (C.TFun
                  (conAt location
                    (C.TFun
                      (conRel location 1)
                      (conAt location
                        (C.CApp (Substitute.liftCon 0 2 monad) (conRel location 0)))))
                  (conAt location
                    (C.CApp (Substitute.liftCon 0 2 monad) (conRel location 0))))))))))

monadRecord :: Span -> C.Con -> C.Con
monadRecord location monad =
  conAt location
    (C.TRecord
      (monadRow location
        [ ("Return", returnType location monad)
        , ("Bind", bindType location monad)
        ]))

basisReturn :: Span -> C.Expr
basisReturn location =
  exprAt location
    (C.ECAbs "m" (kindAt location (C.KArrow (kindType location) (kindType location)))
      (exprAt location
        (C.ECAbs "a" (kindType location)
          (exprAt location
            (C.EAbs "m"
              (monadRecord location monad)
              (returnType location monad)
              (exprAt location
                (C.ECApp
                  (monadField location "Return" (returnType location monad)
                    (monadRow location [("Bind", bindType location monad)]))
                  element)))))))
  where
    monad = conRel location 1
    element = conRel location 0

basisBind :: Span -> C.Expr
basisBind location =
  exprAt location
    (C.ECAbs "m" (kindAt location (C.KArrow (kindType location) (kindType location)))
      (exprAt location
        (C.ECAbs "a" (kindType location)
          (exprAt location
            (C.ECAbs "b" (kindType location)
              (exprAt location
                (C.EAbs "m"
                  (monadRecord location monad)
                  (bindType location monad)
                  (exprAt location
                    (C.ECApp
                      (exprAt location
                        (C.ECApp
                          (monadField location "Bind" (bindType location monad)
                            (monadRow location [("Return", returnType location monad)]))
                          firstType))
                      secondType)))))))))
  where
    monad = conRel location 2
    firstType = conRel location 1
    secondType = conRel location 0

basisMkMonad :: Span -> C.Expr
basisMkMonad location =
  exprAt location
    (C.ECAbs "m" (kindAt location (C.KArrow (kindType location) (kindType location)))
      (exprAt location
        (C.EAbs "m" dictionary dictionary (exprAt location (C.ERel 0)))))
  where
    dictionary = monadRecord location (conRel location 0)

basisMonadDictionary :: Span -> String -> C.Expr
basisMonadDictionary location name =
  exprAt location
    (C.ERecord
      [ (conName location "Return", exprAt location (C.EFfi "Basis" (name <> "_return")), returnType location monad)
      , (conName location "Bind", exprAt location (C.EFfi "Basis" (name <> "_bind")), bindType location monad)
      ])
  where
    monad = conAt location (C.CFfi "Basis" name)

monadField :: Span -> String -> C.Con -> C.Con -> C.Expr
monadField location name typ rest =
  exprAt location (C.EField (exprAt location (C.ERel 0)) (conName location name) typ rest)

monadRow :: Span -> [(String, C.Con)] -> C.Con
monadRow location fields =
  conAt location (C.CRecord (kindType location) [(conName location name, typ) | (name, typ) <- fields])

kindType :: Span -> C.Kind
kindType location = kindAt location C.KType

kindAt :: Span -> C.KindF -> C.Kind
kindAt = Located

conRel :: Span -> Int -> C.Con
conRel location = conAt location . C.CRel

conName :: Span -> String -> C.Con
conName location = conAt location . C.CName

conAt :: Span -> C.ConF -> C.Con
conAt = Located

exprAt :: Span -> C.ExprF -> C.Expr
exprAt = Located

passive :: C.Expr -> Bool
passive expression = case locatedValue expression of
  C.EPrim {} -> True
  C.ERel {} -> True
  C.ENamed {} -> True
  C.ECon _ _ _ payload -> maybe True passive payload
  C.EFfi {} -> True
  C.EAbs {} -> True
  C.ECAbs {} -> True
  C.EKAbs {} -> True
  C.ERecord fields -> all (passive . second3) fields
  C.EField record _ _ _ -> passive record
  _ -> False
  where second3 (_, second, _) = second

notFfi :: C.Con -> Bool
notFfi constructor = case locatedValue constructor of
  C.CFfi {} -> False
  _ -> True

functionInside :: C.Con -> Bool
functionInside constructor = case locatedValue (Substitute.normalizeCon constructor) of
  C.TFun {} -> True
  C.TCFun _ _ body -> functionInside body
  C.TRecord row -> functionInside row
  C.CApp left right -> functionInside left || functionInside right
  C.CAbs _ _ body -> functionInside body
  C.CKAbs _ body -> functionInside body
  C.CKApp function _ -> functionInside function
  C.TKFun _ body -> functionInside body
  C.CRecord _ fields -> any (functionInside . fst) fields || any (functionInside . snd) fields
  C.CConcat left right -> functionInside left || functionInside right
  C.CTuple elements -> any functionInside elements
  C.CProj tuple _ -> functionInside tuple
  _ -> False

isPolymorphic :: C.Con -> Bool
isPolymorphic = go
  where
    go current = case locatedValue current of
      C.TCFun {} -> True
      C.TKFun {} -> True
      C.TFun domain range -> go domain || go range
      C.TRecord row -> go row
      C.CApp left right -> go left || go right
      C.CAbs _ _ body -> go body
      C.CKAbs _ body -> go body
      C.CKApp function _ -> go function
      C.CRecord _ fields -> any (go . fst) fields || any (go . snd) fields
      C.CConcat left right -> go left || go right
      C.CTuple elements -> any go elements
      C.CProj tuple _ -> go tuple
      _ -> False

-- Only the threshold comparison is used by inlining. Stop once the budget is
-- exhausted instead of counting every node in an arbitrarily large body.
expressionSizeAtMost :: Int -> C.Expr -> Bool
expressionSizeAtMost budget expression = fits budget [expression]
  where
    fits _ [] = True
    fits remaining _ | remaining <= 0 = False
    fits remaining (current : rest) =
      fits (remaining - 1) (expressionChildren current <> rest)

-- Inlining distinguishes zero/one uses from multiple uses, not the exact
-- count. Saturation must short-circuit the remaining subtrees while retaining
-- the original binder-depth handling for lambdas, lets, and case patterns.
relativeUsesUpToTwo :: Int -> C.Expr -> Int
relativeUsesUpToTwo target expression = addUses direct children
  where
    direct = case locatedValue expression of C.ERel index | index == target -> 1; _ -> 0
    children = case locatedValue expression of
      C.EAbs _ _ _ body -> relativeUsesUpToTwo (target + 1) body
      C.ELet _ _ value body -> addUses (relativeUsesUpToTwo target value) (relativeUsesUpToTwo (target + 1) body)
      C.ECase scrutinee branches _ _ -> addUses (relativeUsesUpToTwo target scrutinee)
        (foldr addUses 0 [relativeUsesUpToTwo (target + Substitute.patternBindingCount pattern') body | (pattern', body) <- branches])
      _ -> foldr addUses 0 (map (relativeUsesUpToTwo target) (expressionChildren expression))
    addUses left right
      | left >= 2 = 2
      | otherwise = min 2 (left + right)

expressionChildren :: C.Expr -> [C.Expr]
expressionChildren expression = case locatedValue expression of
  C.ECon _ _ _ payload -> maybe [] pure payload
  C.EFfiApp _ _ arguments -> map fst arguments
  C.EApp function argument -> [function, argument]
  C.EAbs _ _ _ body -> [body]
  C.ECApp function _ -> [function]
  C.ECAbs _ _ body -> [body]
  C.EKAbs _ body -> [body]
  C.EKApp function _ -> [function]
  C.ERecord fields -> [value | (_, value, _) <- fields]
  C.EField record _ _ _ -> [record]
  C.EConcat left _ right _ -> [left, right]
  C.ECut record _ _ _ -> [record]
  C.ECutMulti record _ _ -> [record]
  C.ECase scrutinee branches _ _ -> scrutinee : map snd branches
  C.EWrite value -> [value]
  C.EClosure _ captures -> captures
  C.ELet _ _ value body -> [value, body]
  C.EServerCall _ arguments _ _ -> arguments
  _ -> []

valueUseCounts :: C.File -> Map.Map C.GlobalId Int
valueUseCounts = foldl declaration Map.empty
  where
    declaration counts source = foldl expression counts (declarationExpressions source)
    expression counts source =
      let counts' = case locatedValue source of
            C.ENamed identifier -> Map.insertWith (+) identifier 1 counts
            _ -> counts
       in foldl expression counts' (expressionChildren source)

declarationExpressions :: C.Decl -> [C.Expr]
declarationExpressions declaration = case locatedValue declaration of
  C.DVal _ _ _ expression _ -> [expression]
  C.DValRec bindings -> [expression | (_, _, _, expression, _) <- bindings]
  C.DTable _ _ _ _ primary _ constraints _ -> [primary, constraints]
  C.DView _ _ _ expression _ -> [expression]
  C.DIndex table modes -> [table, modes]
  C.DTask kind body -> [kind, body]
  C.DPolicy expression -> [expression]
  _ -> []
