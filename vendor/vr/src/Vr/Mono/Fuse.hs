-- | Output-specialize monomorphic string functions before server code
-- generation.  Ur/Web's Fuse pass creates unit-returning copies whose final
-- string is written incrementally.  Besides avoiding intermediate strings,
-- this ordering is observable to C FFI code through @uw_write@,
-- @uw_pagelen@, and @uw_Basis_clear_page@.
module Vr.Mono.Fuse
  ( fuseFile
  , inlineFullFile
  ) where

import qualified Data.ByteString as ByteString
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Word (Word8)
import Vr.Middle (ExportKind (..))
import qualified Vr.Mono.Syntax as M
import Vr.Source (Located (..), Primitive (..), Span, StringMode (..))

data Candidate = Candidate
  { candidateName :: !String
  , candidateOriginal :: !M.GlobalId
  , candidateFused :: !M.GlobalId
  , candidateOriginalType :: !M.Type
  , candidateFusedType :: !M.Type
  , candidateExpression :: !M.Expr
  , candidatePath :: !String
  , candidateLocation :: !M.Decl
  }

type ForeignTypes = Map.Map (String, String) M.Type

-- | Ur/Web enables an unbounded Mono inlining round immediately before its
-- optional SQL-cache pass.  Expanding acyclic value functions here exposes
-- query dependencies in the exported handler that consumes them, allowing
-- the cache pass to choose the same maximal response-producing expression.
-- Recursive groups remain named, as they do in the reference reducer.
inlineFullFile :: M.File -> M.File
inlineFullFile file = file
  { M.fileDeclarations = map rewriteDeclarationInline declarations
  }
  where
    declarations = M.fileDeclarations file
    foreignTypes = Map.fromList
      [ ((moduleName, name), typ)
      | Located _ (M.DForeign moduleName name typ) <- declarations
      ]
    definitions = Map.fromList
      [ (identifier, expression)
      | Located _ (M.DVal _ identifier _ expression _) <- declarations
      , eligibleInlineValue expression
      ]
    rewrite = reduceExpression foreignTypes . inlineNamed definitions Set.empty
    rewriteDeclarationInline (Located at declaration) = Located at $ case declaration of
      M.DVal name identifier typ expression path ->
        M.DVal name identifier typ (rewrite expression) path
      M.DValRec bindings -> M.DValRec
        [ (name, identifier, typ, rewrite expression, path)
        | (name, identifier, typ, expression, path) <- bindings
        ]
      M.DTable name fields primary constraints ->
        M.DTable name fields (rewrite primary) (rewrite constraints)
      M.DView name fields query -> M.DView name fields (rewrite query)
      M.DIndexDynamic table modes -> M.DIndexDynamic (rewrite table) (rewrite modes)
      M.DTask schedule body -> M.DTask (rewrite schedule) (rewrite body)
      M.DPolicy policy -> M.DPolicy (case policy of
        M.PolicyClient expression -> M.PolicyClient (rewrite expression)
        M.PolicyInsert expression -> M.PolicyInsert (rewrite expression)
        M.PolicyDelete expression -> M.PolicyDelete (rewrite expression)
        M.PolicyUpdate expression -> M.PolicyUpdate (rewrite expression)
        M.PolicySequence expression -> M.PolicySequence (rewrite expression))
      M.DPolicyRaw expression -> M.DPolicyRaw (rewrite expression)
      other -> other

eligibleInlineValue :: M.Expr -> Bool
eligibleInlineValue expression = case locatedValue expression of
  M.EAbs {} -> True
  _ -> passiveExpression expression

inlineNamed
  :: Map.Map M.GlobalId M.Expr
  -> Set.Set M.GlobalId
  -> M.Expr
  -> M.Expr
inlineNamed definitions active expression = expression {locatedValue = case locatedValue expression of
  M.ENamed identifier
    | not (Set.member identifier active)
    , Just replacement <- Map.lookup identifier definitions ->
        locatedValue (inlineNamed definitions (Set.insert identifier active) replacement)
  M.ECon kind constructor payload -> M.ECon kind constructor (recurse <$> payload)
  M.ESome typ value -> M.ESome typ (recurse value)
  M.EFfiApp moduleName name staticArguments arguments ->
    M.EFfiApp moduleName name staticArguments
      [(recurse value, typ) | (value, typ) <- arguments]
  M.EApp function argument -> M.EApp (recurse function) (recurse argument)
  M.EAbs name domain range body -> M.EAbs name domain range (recurse body)
  M.EStaticApp function argument -> M.EStaticApp (recurse function) argument
  M.EUnop operator value -> M.EUnop operator (recurse value)
  M.EBinop intness operator left right ->
    M.EBinop intness operator (recurse left) (recurse right)
  M.ERecord fields -> M.ERecord [(name, recurse value, typ) | (name, value, typ) <- fields]
  M.EField record name -> M.EField (recurse record) name
  M.ERecordConcat left right -> M.ERecordConcat (recurse left) (recurse right)
  M.ERecordCut record names -> M.ERecordCut (recurse record) names
  M.ECase scrutinee branches input result -> M.ECase (recurse scrutinee)
    [(pattern', recurse body) | (pattern', body) <- branches] input result
  M.EStrcat left right -> M.EStrcat (recurse left) (recurse right)
  M.EError value typ -> M.EError (recurse value) typ
  M.EReturnBlob content mime typ -> M.EReturnBlob (recurse <$> content) (recurse mime) typ
  M.ERedirect value typ -> M.ERedirect (recurse value) typ
  M.EWrite value -> M.EWrite (recurse value)
  M.ESeq first second -> M.ESeq (recurse first) (recurse second)
  M.ELet name typ value body -> M.ELet name typ (recurse value) (recurse body)
  M.EClosure identifier captures -> M.EClosure identifier (map recurse captures)
  M.EQuery fields tables state query body initial -> M.EQuery fields tables state
    (recurse query) (recurse body) (recurse initial)
  M.EDml value failure -> M.EDml (recurse value) failure
  M.ENextval value -> M.ENextval (recurse value)
  M.ESetval sequence' value -> M.ESetval (recurse sequence') (recurse value)
  M.EUnurlify value typ optional -> M.EUnurlify (recurse value) typ optional
  M.EJavaScript mode value -> M.EJavaScript mode (recurse value)
  M.ESignalReturn value -> M.ESignalReturn (recurse value)
  M.ESignalBind signal continuation -> M.ESignalBind (recurse signal) (recurse continuation)
  M.ESignalSource value -> M.ESignalSource (recurse value)
  M.EServerCall call typ effect failure -> M.EServerCall (recurse call) typ effect failure
  M.ERecv channel typ -> M.ERecv (recurse channel) typ
  M.ESleep value -> M.ESleep (recurse value)
  M.ESpawn value -> M.ESpawn (recurse value)
  M.ESqlCache index typ keys action -> M.ESqlCache index typ (map recurse keys) (recurse action)
  M.ESqlCacheFlush typ flushes action -> M.ESqlCacheFlush typ
    [ flush {M.sqlCacheFlushKeys = map (fmap recurse) (M.sqlCacheFlushKeys flush)}
    | flush <- flushes
    ] (recurse action)
  leaf -> leaf}
  where
    recurse = inlineNamed definitions active

-- | Add output-specialized values and retarget page-producing entry points.
-- RPC exports keep their value-returning implementation because their result
-- still needs URL serialization.
fuseFile :: M.File -> M.File
fuseFile file = file
  { M.fileDeclarations = map (rewriteDeclaration foreignTypes fusedIds) declarations <> clones
  , M.fileFunctionModes = M.fileFunctionModes file <> clonedModes
  }
  where
    declarations = M.fileDeclarations file
    foreignTypes = Map.fromList
      [ ((moduleName, name), typ)
      | Located _ (M.DForeign moduleName name typ) <- declarations
      ]
    seeds = collectCandidates declarations
    firstFresh = maximumIdentifier file + 1
    candidates = zipWith assign [firstFresh ..] seeds
    assign identifier (location, name, original, originalType, fusedType, expression, path) = Candidate
      name original (M.GlobalId identifier) originalType fusedType expression path location
    fusedIds = Map.fromList
      [(candidateOriginal candidate, candidateFused candidate) | candidate <- candidates]
    clones = map (makeClone foreignTypes fusedIds) candidates
    clonedModes =
      [ (fused, sidedness, databaseMode)
      | (original, sidedness, databaseMode) <- M.fileFunctionModes file
      , Just fused <- [Map.lookup original fusedIds]
      ]

collectCandidates
  :: [M.Decl]
  -> [(M.Decl, String, M.GlobalId, M.Type, M.Type, M.Expr, String)]
collectCandidates = concatMap collect
  where
    collect declaration@(Located _ value) = case value of
      M.DVal name identifier typ expression path
        | Just fusedType <- outputType typ
        , explicitFunction expression ->
            [(declaration, name, identifier, typ, fusedType, expression, path)]
      M.DValRec bindings ->
        [ (declaration, name, identifier, typ, fusedType, expression, path)
        | (name, identifier, typ, expression, path) <- bindings
        , Just fusedType <- [outputType typ]
        , explicitFunction expression
        ]
      _ -> []

explicitFunction :: M.Expr -> Bool
explicitFunction (Located _ expression) = case expression of
  M.EAbs {} -> True
  _ -> False

makeClone :: ForeignTypes -> Map.Map M.GlobalId M.GlobalId -> Candidate -> M.Decl
makeClone foreignTypes fusedIds candidate =
  let Located at _ = candidateLocation candidate
      expression = fuseFunction foreignTypes fusedIds
        (candidateOriginalType candidate)
        (candidateExpression candidate)
   in Located at (M.DVal
        (candidateName candidate <> "_fused")
        (candidateFused candidate)
        (candidateFusedType candidate)
        expression
        (candidatePath candidate))

outputType :: M.Type -> Maybe M.Type
outputType (Located at typ) = case typ of
  M.TFun domain range -> Located at . M.TFun domain <$> outputType range
  M.TFfi "Basis" "string" -> Just (unitType at)
  _ -> Nothing

unitType :: Span -> M.Type
unitType at = Located at (M.TRecord [])

fuseFunction :: ForeignTypes -> Map.Map M.GlobalId M.GlobalId -> M.Type -> M.Expr -> M.Expr
fuseFunction foreignTypes fusedIds sourceType source@(Located at expression) =
  case locatedValue sourceType of
    M.TFun domain range ->
      let fusedRange = maybe range id (outputType range)
       in case expression of
            M.EAbs name actualDomain _ body -> Located at
              (M.EAbs name actualDomain fusedRange
                (fuseFunction foreignTypes fusedIds range body))
            _ -> Located at
              (M.EAbs "_" domain fusedRange
                (fuseFunction foreignTypes fusedIds range
                  (Located at (M.EApp (liftExpression 0 1 source) (Located at (M.ERel 0))))))
    _ -> normalizeWrites
      (writeExpression foreignTypes fusedIds (reduceExpression foreignTypes source))

-- Ur/Web runs MonoOpt while constructing each fused writer.  Specialization
-- can expose new output boundaries after the earlier whole-file Mono pass, so
-- normalize the resulting sequence here as well.  In particular, HTML
-- whitespace on both sides of an inlined accumulator is one layout run, not
-- two independently observable newlines.
-- Normalize every maximal output sequence exactly once.  The old bottom-up
-- implementation flattened a sequence again at each parent ESeq node.  Long
-- generated pages therefore made this nominally linear pass quadratic (the
-- vendored utf8 application allocated several gigabytes while compiling only
-- 56 KiB of source).  Descending through non-sequence nodes here and treating
-- a complete ESeq tree as one region preserves the same ordering and literal
-- coalescing without the repeated traversals.
normalizeWrites :: M.Expr -> M.Expr
normalizeWrites source@(Located at expression) = case expression of
  M.ESeq {} -> rebuild at (merge (flattenInto source []))
  M.ECon kind constructor payload -> Located at
    (M.ECon kind constructor (normalizeWrites <$> payload))
  M.ESome typ value -> Located at (M.ESome typ (normalizeWrites value))
  M.EFfiApp moduleName name staticArguments arguments -> Located at
    (M.EFfiApp moduleName name staticArguments
      [(normalizeWrites value, typ) | (value, typ) <- arguments])
  M.EApp function argument -> Located at
    (M.EApp (normalizeWrites function) (normalizeWrites argument))
  M.EAbs name domain range body -> Located at
    (M.EAbs name domain range (normalizeWrites body))
  M.EStaticApp function argument -> Located at
    (M.EStaticApp (normalizeWrites function) argument)
  M.EUnop operator value -> Located at (M.EUnop operator (normalizeWrites value))
  M.EBinop intness operator left right -> Located at
    (M.EBinop intness operator (normalizeWrites left) (normalizeWrites right))
  M.ERecord fields -> Located at (M.ERecord
    [(name, normalizeWrites value, typ) | (name, value, typ) <- fields])
  M.EField record name -> Located at (M.EField (normalizeWrites record) name)
  M.ERecordConcat left right -> Located at
    (M.ERecordConcat (normalizeWrites left) (normalizeWrites right))
  M.ERecordCut record names -> Located at
    (M.ERecordCut (normalizeWrites record) names)
  M.ECase scrutinee branches input result -> Located at
    (M.ECase (normalizeWrites scrutinee)
      [(pattern', normalizeWrites body) | (pattern', body) <- branches]
      input result)
  M.EStrcat left right -> Located at
    (M.EStrcat (normalizeWrites left) (normalizeWrites right))
  M.EError value typ -> Located at (M.EError (normalizeWrites value) typ)
  M.EReturnBlob content mime typ -> Located at
    (M.EReturnBlob (normalizeWrites <$> content) (normalizeWrites mime) typ)
  M.ERedirect value typ -> Located at (M.ERedirect (normalizeWrites value) typ)
  M.EWrite value -> Located at (M.EWrite (normalizeWrites value))
  M.ELet name typ value body -> Located at
    (M.ELet name typ (normalizeWrites value) (normalizeWrites body))
  M.EClosure identifier captures -> Located at
    (M.EClosure identifier (map normalizeWrites captures))
  M.EQuery fields tables state query body initial -> Located at
    (M.EQuery fields tables state (normalizeWrites query)
      (normalizeWrites body) (normalizeWrites initial))
  M.EDml value failure -> Located at (M.EDml (normalizeWrites value) failure)
  M.ENextval value -> Located at (M.ENextval (normalizeWrites value))
  M.ESetval sequence' value -> Located at
    (M.ESetval (normalizeWrites sequence') (normalizeWrites value))
  M.EUnurlify value typ optional -> Located at
    (M.EUnurlify (normalizeWrites value) typ optional)
  M.EJavaScript mode value -> Located at (M.EJavaScript mode (normalizeWrites value))
  M.ESignalReturn value -> Located at (M.ESignalReturn (normalizeWrites value))
  M.ESignalBind signal continuation -> Located at
    (M.ESignalBind (normalizeWrites signal) (normalizeWrites continuation))
  M.ESignalSource value -> Located at (M.ESignalSource (normalizeWrites value))
  M.EServerCall call typ effect failure -> Located at
    (M.EServerCall (normalizeWrites call) typ effect failure)
  M.ERecv channel typ -> Located at (M.ERecv (normalizeWrites channel) typ)
  M.ESleep value -> Located at (M.ESleep (normalizeWrites value))
  M.ESpawn value -> Located at (M.ESpawn (normalizeWrites value))
  M.ESqlCache index typ keys action -> Located at
    (M.ESqlCache index typ (map normalizeWrites keys) (normalizeWrites action))
  M.ESqlCacheFlush typ flushes action -> Located at (M.ESqlCacheFlush typ
    [ flush
        { M.sqlCacheFlushKeys = map (fmap normalizeWrites) (M.sqlCacheFlushKeys flush)
        }
    | flush <- flushes
    ] (normalizeWrites action))
  _ -> source
  where
    flattenInto value rest = case locatedValue value of
      M.ESeq left right -> flattenInto left (flattenInto right rest)
      _ ->
        let normalized = normalizeWrites value
         in if isOutputNoOp normalized then rest else normalized : rest

    merge (first : second : rest)
      | Just firstPrimitive <- writtenPrimitive first
      , Just secondPrimitive <- writtenPrimitive second =
          merge (writtenAt first
            (joinOutputPrimitives firstPrimitive secondPrimitive) : rest)
      | otherwise = first : merge (second : rest)
    merge values = values

    rebuild location values = case values of
      [] -> Located location (M.ERecord [])
      [only] -> only
      first : rest -> Located location
        (M.ESeq first (rebuild location rest))

writtenPrimitive :: M.Expr -> Maybe Primitive
writtenPrimitive (Located _ expression) = case expression of
  M.EWrite (Located _ (M.EPrim primitive@PrimString {})) -> Just primitive
  _ -> Nothing

writtenAt :: M.Expr -> Primitive -> M.Expr
writtenAt (Located at _) primitive = Located at
  (M.EWrite (Located at (M.EPrim primitive)))

joinOutputPrimitives :: Primitive -> Primitive -> Primitive
joinOutputPrimitives (PrimString HtmlString left) (PrimString HtmlString right) =
  PrimString HtmlString (joinHtmlOutput left right)
joinOutputPrimitives (PrimString _ left) (PrimString _ right) =
  PrimString NormalString (left <> right)
joinOutputPrimitives left _ = left

joinHtmlOutput :: ByteString.ByteString -> ByteString.ByteString -> ByteString.ByteString
joinHtmlOutput left right
  | not (ByteString.null left)
  , not (ByteString.null right)
  , htmlSpace (ByteString.last left)
  , htmlSpace (ByteString.head right) = left <> ByteString.tail right
  | otherwise = left <> right

htmlSpace :: Word8 -> Bool
htmlSpace byte = byte `elem` [0x20, 0x09, 0x0a, 0x0d, 0x0c, 0x0b]

isOutputNoOp :: M.Expr -> Bool
isOutputNoOp (Located _ expression) = case expression of
  M.ERecord [] -> True
  M.EWrite (Located _ (M.EPrim (PrimString _ bytes))) -> ByteString.null bytes
  _ -> False

-- | Shift free runtime variables before eta-expanding an implicit Mono
-- function layer.  Mono's value binders are lambdas, lets, and patterns;
-- query row/state binders are represented by explicit function values.
liftExpression :: Int -> Int -> M.Expr -> M.Expr
liftExpression cutoff amount = walk 0
  where
    walk bound expression = expression {locatedValue = case locatedValue expression of
      M.ERel index
        | index >= cutoff + bound -> M.ERel (index + amount)
        | otherwise -> M.ERel index
      M.ECon kind constructor payload -> M.ECon kind constructor (walk bound <$> payload)
      M.ESome typ value -> M.ESome typ (walk bound value)
      M.EFfiApp moduleName member staticArguments arguments ->
        M.EFfiApp moduleName member staticArguments
          [(walk bound value, typ) | (value, typ) <- arguments]
      M.EApp function argument -> M.EApp (walk bound function) (walk bound argument)
      M.EAbs name domain range body -> M.EAbs name domain range (walk (bound + 1) body)
      M.EStaticApp function argument -> M.EStaticApp (walk bound function) argument
      M.EUnop operator value -> M.EUnop operator (walk bound value)
      M.EBinop intness operator left right ->
        M.EBinop intness operator (walk bound left) (walk bound right)
      M.ERecord fields -> M.ERecord
        [(name, walk bound value, typ) | (name, value, typ) <- fields]
      M.EField record field -> M.EField (walk bound record) field
      M.ERecordConcat left right -> M.ERecordConcat (walk bound left) (walk bound right)
      M.ERecordCut record fields -> M.ERecordCut (walk bound record) fields
      M.ECase scrutinee branches input result -> M.ECase
        (walk bound scrutinee)
        [ (pattern', walk (bound + patternBindingCount pattern') body)
        | (pattern', body) <- branches
        ]
        input result
      M.EStrcat left right -> M.EStrcat (walk bound left) (walk bound right)
      M.EError value typ -> M.EError (walk bound value) typ
      M.EReturnBlob content mime typ ->
        M.EReturnBlob (walk bound <$> content) (walk bound mime) typ
      M.ERedirect value typ -> M.ERedirect (walk bound value) typ
      M.EWrite value -> M.EWrite (walk bound value)
      M.ESeq first second -> M.ESeq (walk bound first) (walk bound second)
      M.ELet name typ value body ->
        M.ELet name typ (walk bound value) (walk (bound + 1) body)
      M.EClosure identifier captures -> M.EClosure identifier (map (walk bound) captures)
      M.EQuery fields tables state query body initial ->
        M.EQuery fields tables state
          (walk bound query)
          (walk (bound + 2) body)
          (walk bound initial)
      M.EDml value failure -> M.EDml (walk bound value) failure
      M.ENextval value -> M.ENextval (walk bound value)
      M.ESetval sequence' value -> M.ESetval (walk bound sequence') (walk bound value)
      M.EUnurlify value typ optional -> M.EUnurlify (walk bound value) typ optional
      M.EJavaScript mode value -> M.EJavaScript mode (walk bound value)
      M.ESignalReturn value -> M.ESignalReturn (walk bound value)
      M.ESignalBind signal continuation ->
        M.ESignalBind (walk bound signal) (walk bound continuation)
      M.ESignalSource value -> M.ESignalSource (walk bound value)
      M.EServerCall call typ effect failure ->
        M.EServerCall (walk bound call) typ effect failure
      M.ERecv channel typ -> M.ERecv (walk bound channel) typ
      M.ESleep value -> M.ESleep (walk bound value)
      M.ESpawn value -> M.ESpawn (walk bound value)
      M.ESqlCache index typ keys action ->
        M.ESqlCache index typ (map (walk bound) keys) (walk bound action)
      M.ESqlCacheFlush typ flushes action -> M.ESqlCacheFlush typ
        [ flush
            { M.sqlCacheFlushKeys = map (fmap (walk bound)) (M.sqlCacheFlushKeys flush)
            }
        | flush <- flushes
        ]
        (walk bound action)
      leaf -> leaf}

patternBindingCount :: M.Pattern -> Int
patternBindingCount pattern' = case locatedValue pattern' of
  M.PVar {} -> 1
  M.PPrim {} -> 0
  M.PCon _ _ nested -> maybe 0 patternBindingCount nested
  M.PRecord fields -> sum [patternBindingCount nested | (_, nested, _) <- fields]
  M.PNone {} -> 0
  M.PSome _ nested -> patternBindingCount nested

-- | Perform the reductions needed to expose output concatenation without
-- moving or duplicating effects.  Pure lambda arguments may be substituted;
-- effectful arguments become lets, preserving Ur's call-by-value order.
reduceExpression :: ForeignTypes -> M.Expr -> M.Expr
reduceExpression foreignTypes (Located at expression) = contract $ Located at $ case expression of
  M.ECon kind constructor payload -> M.ECon kind constructor (recurse <$> payload)
  M.ESome typ value -> M.ESome typ (recurse value)
  M.EFfiApp moduleName member staticArguments arguments ->
    M.EFfiApp moduleName member staticArguments
      [(recurse value, typ) | (value, typ) <- arguments]
  M.EApp function argument -> M.EApp (recurse function) (recurse argument)
  M.EAbs name domain range body -> M.EAbs name domain range (recurse body)
  M.EStaticApp function argument -> M.EStaticApp (recurse function) argument
  M.EUnop operator value -> M.EUnop operator (recurse value)
  M.EBinop intness operator left right ->
    M.EBinop intness operator (recurse left) (recurse right)
  M.ERecord fields -> M.ERecord
    [(name, recurse value, typ) | (name, value, typ) <- fields]
  M.EField record field -> M.EField (recurse record) field
  M.ERecordConcat left right -> M.ERecordConcat (recurse left) (recurse right)
  M.ERecordCut record fields -> M.ERecordCut (recurse record) fields
  M.ECase scrutinee branches input result -> M.ECase
    (recurse scrutinee)
    [(pattern', recurse body) | (pattern', body) <- branches]
    input result
  M.EStrcat left right -> M.EStrcat (recurse left) (recurse right)
  M.EError value typ -> M.EError (recurse value) typ
  M.EReturnBlob content mime typ ->
    M.EReturnBlob (recurse <$> content) (recurse mime) typ
  M.ERedirect value typ -> M.ERedirect (recurse value) typ
  M.EWrite value -> M.EWrite (recurse value)
  M.ESeq first second -> M.ESeq (recurse first) (recurse second)
  M.ELet name typ value body -> M.ELet name typ (recurse value) (recurse body)
  M.EClosure identifier captures -> M.EClosure identifier (map recurse captures)
  M.EQuery fields tables state query body initial ->
    M.EQuery fields tables state (recurse query) (recurse body) (recurse initial)
  M.EDml value failure -> M.EDml (recurse value) failure
  M.ENextval value -> M.ENextval (recurse value)
  M.ESetval sequence' value -> M.ESetval (recurse sequence') (recurse value)
  M.EUnurlify value typ optional -> M.EUnurlify (recurse value) typ optional
  M.EJavaScript mode value -> M.EJavaScript mode (recurse value)
  M.ESignalReturn value -> M.ESignalReturn (recurse value)
  M.ESignalBind signal continuation -> M.ESignalBind (recurse signal) (recurse continuation)
  M.ESignalSource value -> M.ESignalSource (recurse value)
  M.EServerCall call typ effect failure -> M.EServerCall (recurse call) typ effect failure
  M.ERecv channel typ -> M.ERecv (recurse channel) typ
  M.ESleep value -> M.ESleep (recurse value)
  M.ESpawn value -> M.ESpawn (recurse value)
  M.ESqlCache index typ keys action ->
    M.ESqlCache index typ (map recurse keys) (recurse action)
  M.ESqlCacheFlush typ flushes action -> M.ESqlCacheFlush typ
    [ flush {M.sqlCacheFlushKeys = map (fmap recurse) (M.sqlCacheFlushKeys flush)}
    | flush <- flushes
    ]
    (recurse action)
  leaf -> leaf
  where
    recurse = reduceExpression foreignTypes
    contract rebuilt@(Located location value) = case value of
      M.EApp function argument -> case locatedValue function of
        M.EAbs name domain _ body
          | relativeUses 0 body <= 1
          , passiveExpression argument
              || partialForeignApplication foreignTypes argument
              || isHtmlTagApplication argument ->
              reduceExpression foreignTypes (substituteExpression 0 argument body)
          | otherwise ->
              reduceExpression foreignTypes (Located location (M.ELet name domain argument body))
        M.ELet name typ bound body ->
          reduceExpression foreignTypes (Located location (M.ELet name typ bound
            (Located location (M.EApp body (liftExpression 0 1 argument)))))
        _ -> rebuilt
      M.EField record field -> case locatedValue record of
        -- Project concrete instance records after beta reduction.  Requiring
        -- every field to be passive preserves record-construction evaluation
        -- semantics for general user records while covering elaborator-built
        -- dictionaries, whose members are literals and lambdas.
        M.ERecord fields
          | all (passiveExpression . fieldValue) fields
          , Just selected <- firstMatchingField field fields ->
              reduceExpression foreignTypes selected
        _ -> rebuilt
      M.EStrcat left right -> case (locatedValue left, locatedValue right) of
        (M.EPrim (PrimString leftMode leftBytes), M.EPrim (PrimString rightMode rightBytes)) ->
          Located location (M.EPrim (PrimString (combinedStringMode leftMode rightMode)
            (leftBytes <> rightBytes)))
        (M.EPrim (PrimString HtmlString bytes), _) | ByteString.null bytes -> right
        (_, M.EPrim (PrimString HtmlString bytes)) | ByteString.null bytes -> left
        _ -> rebuilt
      M.ESeq first second -> case locatedValue first of
        M.ERecord [] -> second
        _ -> rebuilt
      M.ELet _ _ bound body
        | relativeUses 0 body <= 1
        , passiveExpression bound
            || partialForeignApplication foreignTypes bound
            || isHtmlTagApplication bound ->
            reduceExpression foreignTypes (substituteExpression 0 bound body)
      _ -> rebuilt

    combinedStringMode HtmlString HtmlString = HtmlString
    combinedStringMode _ _ = NormalString

    fieldValue (_, fieldExpression, _) = fieldExpression

    firstMatchingField selected = go
      where
        go [] = Nothing
        go ((field, fieldExpression, _) : rest)
          | field == selected = Just fieldExpression
          | otherwise = go rest

passiveExpression :: M.Expr -> Bool
passiveExpression (Located _ expression) = case expression of
  M.EPrim {} -> True
  M.ERel {} -> True
  M.ENamed {} -> True
  M.ECon _ _ payload -> maybe True passiveExpression payload
  M.ENone {} -> True
  M.ESome _ value -> passiveExpression value
  M.EFfi {} -> True
  M.EAbs {} -> True
  M.ERecord fields -> all (passiveExpression . fieldValue) fields
  M.EField value _ -> passiveExpression value
  M.ERecordConcat left right -> passiveExpression left && passiveExpression right
  M.ERecordCut value _ -> passiveExpression value
  M.EClosure _ captures -> all passiveExpression captures
  _ -> False
  where
    fieldValue (_, value, _) = value

isHtmlTagApplication :: M.Expr -> Bool
isHtmlTagApplication expression = case locatedValue (fst (collectApplications expression)) of
  M.EFfi "Basis" "tag" _ -> True
  _ -> False

partialForeignApplication :: ForeignTypes -> M.Expr -> Bool
partialForeignApplication foreignTypes expression =
  case collectApplications expression of
    (Located _ (M.EFfi moduleName name _), arguments) ->
      maybe False ((> length arguments) . functionArity) (Map.lookup (moduleName, name) foreignTypes)
    _ -> False
  where
    functionArity typ = case locatedValue typ of
      M.TFun _ range -> 1 + functionArity range
      _ -> 0

-- | Substitute one Mono value variable, removing its binder and shifting the
-- remaining relative variables exactly as Ur/Web's MonoReduce does.
substituteExpression :: Int -> M.Expr -> M.Expr -> M.Expr
substituteExpression depth replacement expression = expression {locatedValue =
  case locatedValue expression of
    M.ERel index
      | index == depth -> locatedValue (liftExpression 0 depth replacement)
      | index > depth -> M.ERel (index - 1)
      | otherwise -> M.ERel index
    M.ECon kind constructor payload -> M.ECon kind constructor (go <$> payload)
    M.ESome typ value -> M.ESome typ (go value)
    M.EFfiApp moduleName member staticArguments arguments ->
      M.EFfiApp moduleName member staticArguments
        [(go value, typ) | (value, typ) <- arguments]
    M.EApp function argument -> M.EApp (go function) (go argument)
    M.EAbs name domain range body ->
      M.EAbs name domain range (substituteExpression (depth + 1) replacement body)
    M.EStaticApp function argument -> M.EStaticApp (go function) argument
    M.EUnop operator value -> M.EUnop operator (go value)
    M.EBinop intness operator left right -> M.EBinop intness operator (go left) (go right)
    M.ERecord fields -> M.ERecord [(name, go value, typ) | (name, value, typ) <- fields]
    M.EField record field -> M.EField (go record) field
    M.ERecordConcat left right -> M.ERecordConcat (go left) (go right)
    M.ERecordCut record fields -> M.ERecordCut (go record) fields
    M.ECase scrutinee branches input result -> M.ECase
      (go scrutinee)
      [ (pattern', substituteExpression (depth + patternBindingCount pattern') replacement body)
      | (pattern', body) <- branches
      ]
      input result
    M.EStrcat left right -> M.EStrcat (go left) (go right)
    M.EError value typ -> M.EError (go value) typ
    M.EReturnBlob content mime typ -> M.EReturnBlob (go <$> content) (go mime) typ
    M.ERedirect value typ -> M.ERedirect (go value) typ
    M.EWrite value -> M.EWrite (go value)
    M.ESeq first second -> M.ESeq (go first) (go second)
    M.ELet name typ value body ->
      M.ELet name typ (go value) (substituteExpression (depth + 1) replacement body)
    M.EClosure identifier captures -> M.EClosure identifier (map go captures)
    M.EQuery fields tables state query body initial -> M.EQuery fields tables state
      (go query)
      (substituteExpression (depth + 2) replacement body)
      (go initial)
    M.EDml value failure -> M.EDml (go value) failure
    M.ENextval value -> M.ENextval (go value)
    M.ESetval sequence' value -> M.ESetval (go sequence') (go value)
    M.EUnurlify value typ optional -> M.EUnurlify (go value) typ optional
    M.EJavaScript mode value -> M.EJavaScript mode (go value)
    M.ESignalReturn value -> M.ESignalReturn (go value)
    M.ESignalBind signal continuation -> M.ESignalBind (go signal) (go continuation)
    M.ESignalSource value -> M.ESignalSource (go value)
    M.EServerCall call typ effect failure -> M.EServerCall (go call) typ effect failure
    M.ERecv channel typ -> M.ERecv (go channel) typ
    M.ESleep value -> M.ESleep (go value)
    M.ESpawn value -> M.ESpawn (go value)
    M.ESqlCache index typ keys action ->
      M.ESqlCache index typ (map go keys) (go action)
    M.ESqlCacheFlush typ flushes action -> M.ESqlCacheFlush typ
      [ flush {M.sqlCacheFlushKeys = map (fmap go) (M.sqlCacheFlushKeys flush)}
      | flush <- flushes
      ]
      (go action)
    leaf -> leaf}
  where
    go = substituteExpression depth replacement

writeExpression :: ForeignTypes -> Map.Map M.GlobalId M.GlobalId -> M.Expr -> M.Expr
writeExpression foreignTypes fusedIds source@(Located at expression) =
  case splitHtmlTag source of
    Just (opening, child, closing) -> Located at
      (M.ESeq
        (writeExpression foreignTypes fusedIds opening)
        (Located at (M.ESeq
          (writeExpression foreignTypes fusedIds child)
          (writeExpression foreignTypes fusedIds closing))))
    Nothing -> case expression of
      M.EStrcat left right -> Located at
        (M.ESeq (writeExpression foreignTypes fusedIds left) (writeExpression foreignTypes fusedIds right))
      M.ELet name typ value body ->
        let writtenBody = writeExpression foreignTypes fusedIds body
            rewrittenValue = rewriteExpression foreignTypes fusedIds value
         in if relativeUses 0 body == 1 && not (relativeUseUnderLambda 0 body)
              then sinkLet at name typ rewrittenValue writtenBody
              else Located at (M.ELet name typ rewrittenValue writtenBody)
      M.ECase scrutinee branches input _ -> Located at
        (M.ECase
          (rewriteExpression foreignTypes fusedIds scrutinee)
          [(pattern', writeExpression foreignTypes fusedIds body) | (pattern', body) <- branches]
          input
          (unitType at))
      M.EPrim (PrimString _ bytes) | ByteString.null bytes -> Located at (M.ERecord [])
      _ -> case rewriteFusedCall fusedIds source of
        Just call -> rewriteExpression foreignTypes fusedIds call
        Nothing -> Located at (M.EWrite (rewriteExpression foreignTypes fusedIds source))

-- | Split an ordinary container tag so child effects observe the opening tag
-- in the page buffer, as they do after Ur/Web's MonoOpt/Fuse passes.  Special
-- client islands, dynamic nodes, and void controls retain their dedicated
-- lowering paths.
splitHtmlTag :: M.Expr -> Maybe (M.Expr, M.Expr, M.Expr)
splitHtmlTag source = do
  let (function, arguments) = collectApplications source
  staticArguments <- case locatedValue function of
    M.EFfi "Basis" "tag" found -> Just found
    _ -> Nothing
  [classes, dynamicClasses, style, dynamicStyle, attributes, descriptor, child] <- pure arguments
  rawName <- htmlBasisTagName descriptor
  let name = htmlElementName rawName
  if rawName `elem` specialTags || name `elem` voidTags
    then Nothing
    else
      let at = locatedSpan source
          openingFunction = Located at (M.EFfi "Basis" "__vr_tag_open" staticArguments)
          opening = foldl (\function' argument -> Located at (M.EApp function' argument))
            openingFunction
            [classes, dynamicClasses, style, dynamicStyle, attributes, descriptor]
          closing = Located at (M.EPrim
            (PrimString HtmlString (ByteString.pack (map (fromIntegral . fromEnum) ("</" <> name <> ">")))))
       in Just (opening, child, closing)
  where
    specialTags = ["active", "script", "dyn"]
    voidTags = ["input", "img", "br", "hr", "meta", "link"]

htmlBasisTagName :: M.Expr -> Maybe String
htmlBasisTagName expression = case locatedValue expression of
  M.EApp function _ -> htmlBasisTagName function
  M.EFfi "Basis" name _
    | name `notElem` ["tag", "join", "cdata", "null", "noStyle"] -> Just name
  M.EFfi _ name _ -> Just name
  _ -> Nothing

htmlElementName :: String -> String
htmlElementName name = case name of
  "tabl" -> "table"
  "cselect" -> "select"
  "coption" -> "option"
  "ctextarea" -> "textarea"
  _ | name `elem` inputControls -> "input"
  _ -> name
  where
    inputControls =
      [ "textbox", "ctextbox", "password", "cpassword", "email", "cemail"
      , "search", "csearch", "url_", "curl", "tel", "ctel", "color", "ccolor"
      , "number", "cnumber", "range", "crange", "date", "cdate", "datetime"
      , "cdatetime", "datetime_local", "cdatetime_local", "month", "cmonth"
      , "week", "cweek", "timeInput", "ctime", "checkbox", "ccheckbox"
      , "radioOption", "cradio", "hidden", "upload", "submit", "image"
      ]

sinkLet :: Span -> String -> M.Type -> M.Expr -> M.Expr -> M.Expr
sinkLet at name typ value body = case locatedValue body of
  M.ESeq first second
    | relativeUses 0 first == 0 -> Located at
        (M.ESeq
          (substituteExpression 0 (Located at (M.ERecord [])) first)
          (sinkLet at name typ value second))
    | relativeUses 0 second == 0 -> Located at
        (M.ESeq
          (sinkLet at name typ value first)
          (substituteExpression 0 (Located at (M.ERecord [])) second))
  _ -> Located at (M.ELet name typ value body)

relativeUses :: Int -> M.Expr -> Int
relativeUses target expression = case locatedValue expression of
  M.ERel index -> if index == target then 1 else 0
  M.ECon _ _ payload -> maybe 0 (relativeUses target) payload
  M.ESome _ value -> recurse value
  M.EFfiApp _ _ _ arguments -> sum [recurse value | (value, _) <- arguments]
  M.EApp function argument -> recurse function + recurse argument
  M.EAbs _ _ _ body -> relativeUses (target + 1) body
  M.EStaticApp function _ -> recurse function
  M.EUnop _ value -> recurse value
  M.EBinop _ _ left right -> recurse left + recurse right
  M.ERecord fields -> sum [recurse value | (_, value, _) <- fields]
  M.EField record _ -> recurse record
  M.ERecordConcat left right -> recurse left + recurse right
  M.ERecordCut record _ -> recurse record
  M.ECase scrutinee branches _ _ -> recurse scrutinee
    + sum [relativeUses (target + patternBindingCount pattern') body | (pattern', body) <- branches]
  M.EStrcat left right -> recurse left + recurse right
  M.EError value _ -> recurse value
  M.EReturnBlob content mime _ -> maybe 0 recurse content + recurse mime
  M.ERedirect value _ -> recurse value
  M.EWrite value -> recurse value
  M.ESeq first second -> recurse first + recurse second
  M.ELet _ _ value body -> recurse value + relativeUses (target + 1) body
  M.EClosure _ captures -> sum (map recurse captures)
  M.EQuery _ _ _ query body initial ->
    recurse query + relativeUses (target + 2) body + recurse initial
  M.EDml value _ -> recurse value
  M.ENextval value -> recurse value
  M.ESetval sequence' value -> recurse sequence' + recurse value
  M.EUnurlify value _ _ -> recurse value
  M.EJavaScript _ value -> recurse value
  M.ESignalReturn value -> recurse value
  M.ESignalBind signal continuation -> recurse signal + recurse continuation
  M.ESignalSource value -> recurse value
  M.EServerCall call _ _ _ -> recurse call
  M.ERecv channel _ -> recurse channel
  M.ESleep value -> recurse value
  M.ESpawn value -> recurse value
  M.ESqlCache _ _ keys action -> sum (map recurse keys) + recurse action
  M.ESqlCacheFlush _ flushes action ->
    sum
      [ maybe 0 recurse key
      | flush <- flushes
      , key <- M.sqlCacheFlushKeys flush
      ]
      + recurse action
  _ -> 0
  where
    recurse = relativeUses target

relativeUseUnderLambda :: Int -> M.Expr -> Bool
relativeUseUnderLambda target = walk target False
  where
    walk sought under expression = case locatedValue expression of
      M.ERel index -> under && index == sought
      M.EAbs _ _ _ body -> walk (sought + 1) True body
      M.ELet _ _ value body -> walk sought under value || walk (sought + 1) under body
      M.ECase scrutinee branches _ _ -> walk sought under scrutinee
        || or [walk (sought + patternBindingCount pattern') under body | (pattern', body) <- branches]
      M.EQuery _ _ _ query body initial ->
        walk sought under query || walk (sought + 2) under body || walk sought under initial
      _ -> any (walk sought under) (expressionChildren expression)

expressionChildren :: M.Expr -> [M.Expr]
expressionChildren expression = case locatedValue expression of
  M.ECon _ _ payload -> maybe [] pure payload
  M.ESome _ value -> [value]
  M.EFfiApp _ _ _ arguments -> [value | (value, _) <- arguments]
  M.EApp function argument -> [function, argument]
  M.EStaticApp function _ -> [function]
  M.EUnop _ value -> [value]
  M.EBinop _ _ left right -> [left, right]
  M.ERecord fields -> [value | (_, value, _) <- fields]
  M.EField record _ -> [record]
  M.ERecordConcat left right -> [left, right]
  M.ERecordCut record _ -> [record]
  M.EStrcat left right -> [left, right]
  M.EError value _ -> [value]
  M.EReturnBlob content mime _ -> maybe [] pure content <> [mime]
  M.ERedirect value _ -> [value]
  M.EWrite value -> [value]
  M.ESeq first second -> [first, second]
  M.EClosure _ captures -> captures
  M.EDml value _ -> [value]
  M.ENextval value -> [value]
  M.ESetval sequence' value -> [sequence', value]
  M.EUnurlify value _ _ -> [value]
  M.EJavaScript _ value -> [value]
  M.ESignalReturn value -> [value]
  M.ESignalBind signal continuation -> [signal, continuation]
  M.ESignalSource value -> [value]
  M.EServerCall call _ _ _ -> [call]
  M.ERecv channel _ -> [channel]
  M.ESleep value -> [value]
  M.ESpawn value -> [value]
  M.ESqlCache _ _ keys action -> keys <> [action]
  M.ESqlCacheFlush _ flushes action ->
    [key | flush <- flushes, Just key <- M.sqlCacheFlushKeys flush] <> [action]
  _ -> []

rewriteFusedCall :: Map.Map M.GlobalId M.GlobalId -> M.Expr -> Maybe M.Expr
rewriteFusedCall fusedIds source = do
  let (function, arguments) = collectApplications source
  original <- case locatedValue function of
    M.ENamed identifier -> Just identifier
    _ -> Nothing
  fused <- Map.lookup original fusedIds
  let function' = function {locatedValue = M.ENamed fused}
  pure (foldl apply function' arguments)
  where
    apply function argument = Located (locatedSpan function) (M.EApp function argument)

collectApplications :: M.Expr -> (M.Expr, [M.Expr])
collectApplications expression = go expression []
  where
    go source@(Located _ value) arguments = case value of
      M.EApp function argument -> go function (argument : arguments)
      _ -> (source, arguments)

rewriteDeclaration :: ForeignTypes -> Map.Map M.GlobalId M.GlobalId -> M.Decl -> M.Decl
rewriteDeclaration foreignTypes fusedIds (Located at declaration) = Located at $ case declaration of
  M.DVal name identifier typ expression path ->
    M.DVal name identifier typ (optimize expression) path
  M.DValRec bindings -> M.DValRec
    [ (name, identifier, typ, optimize expression, path)
    | (name, identifier, typ, expression, path) <- bindings
    ]
  M.DExport kind path identifier arguments result needsSignature
    | not (isRpc kind)
    , Just fused <- Map.lookup identifier fusedIds ->
        M.DExport kind path fused arguments result needsSignature
  M.DTable name fields primary constraints ->
    M.DTable name fields (optimize primary) (optimize constraints)
  M.DView name fields query ->
    M.DView name fields (optimize query)
  M.DIndexDynamic table modes ->
    M.DIndexDynamic (optimize table) (optimize modes)
  M.DTask schedule body ->
    M.DTask (optimize schedule) (optimize body)
  M.DPolicy policy -> M.DPolicy (optimizePolicy policy)
  M.DPolicyRaw expression -> M.DPolicyRaw (optimize expression)
  M.DOnError identifier ->
    M.DOnError (Map.findWithDefault identifier identifier fusedIds)
  other -> other
  where
    -- MonoOpt is a whole-program pass in Ur/Web, rather than an optimization
    -- reserved for page-producing functions.  In particular, elaboration
    -- represents overloaded primitives by applying a selector lambda to a
    -- concrete instance record.  Reducing every declaration here erases that
    -- resolved dictionary before either backend allocates its record and
    -- curried closures at run time.
    optimize = normalizeWrites
      . reduceExpression foreignTypes
      . rewriteExpression foreignTypes fusedIds
      . reduceExpression foreignTypes

    optimizePolicy policy = case policy of
      M.PolicyClient expression -> M.PolicyClient (optimize expression)
      M.PolicyInsert expression -> M.PolicyInsert (optimize expression)
      M.PolicyDelete expression -> M.PolicyDelete (optimize expression)
      M.PolicyUpdate expression -> M.PolicyUpdate (optimize expression)
      M.PolicySequence expression -> M.PolicySequence (optimize expression)

isRpc :: ExportKind -> Bool
isRpc kind = case kind of
  Rpc _ -> True
  _ -> False

rewriteExpression :: ForeignTypes -> Map.Map M.GlobalId M.GlobalId -> M.Expr -> M.Expr
rewriteExpression foreignTypes fusedIds (Located at expression) =
  Located at $ case expression of
  M.ECon kind constructor payload -> M.ECon kind constructor (recurse <$> payload)
  M.ESome typ value -> M.ESome typ (recurse value)
  M.EFfiApp moduleName member staticArguments arguments ->
    M.EFfiApp moduleName member staticArguments
      [(recurse value, typ) | (value, typ) <- arguments]
  M.EApp function argument -> M.EApp (recurse function) (recurse argument)
  M.EAbs name domain range body -> M.EAbs name domain range (recurse body)
  M.EStaticApp function argument -> M.EStaticApp (recurse function) argument
  M.EUnop operator value -> M.EUnop operator (recurse value)
  M.EBinop intness operator left right ->
    M.EBinop intness operator (recurse left) (recurse right)
  M.ERecord fields -> M.ERecord
    [(name, recurse value, typ) | (name, value, typ) <- fields]
  M.EField record field -> M.EField (recurse record) field
  M.ERecordConcat left right -> M.ERecordConcat (recurse left) (recurse right)
  M.ERecordCut record fields -> M.ERecordCut (recurse record) fields
  M.ECase scrutinee branches input result -> M.ECase
    (recurse scrutinee)
    [(pattern', recurse body) | (pattern', body) <- branches]
    input result
  M.EStrcat left right -> M.EStrcat (recurse left) (recurse right)
  M.EError value typ -> M.EError (recurse value) typ
  M.EReturnBlob content mime typ ->
    M.EReturnBlob (recurse <$> content) (recurse mime) typ
  M.ERedirect value typ -> M.ERedirect (recurse value) typ
  M.EWrite value -> locatedValue
    (writeExpression foreignTypes fusedIds (reduceExpression foreignTypes value))
  M.ESeq first second -> M.ESeq (recurse first) (recurse second)
  M.ELet name typ value body -> M.ELet name typ (recurse value) (recurse body)
  M.EClosure identifier captures -> M.EClosure identifier (map recurse captures)
  M.EQuery fields tables state query body initial ->
    M.EQuery fields tables state (recurse query) (recurse body) (recurse initial)
  M.EDml value failure -> M.EDml (recurse value) failure
  M.ENextval value -> M.ENextval (recurse value)
  M.ESetval sequence' value -> M.ESetval (recurse sequence') (recurse value)
  M.EUnurlify value typ optional -> M.EUnurlify (recurse value) typ optional
  M.EJavaScript mode value -> M.EJavaScript mode (recurse value)
  M.ESignalReturn value -> M.ESignalReturn (recurse value)
  M.ESignalBind signal continuation -> M.ESignalBind (recurse signal) (recurse continuation)
  M.ESignalSource value -> M.ESignalSource (recurse value)
  M.EServerCall call typ effect failure -> M.EServerCall (recurse call) typ effect failure
  M.ERecv channel typ -> M.ERecv (recurse channel) typ
  M.ESleep value -> M.ESleep (recurse value)
  M.ESpawn value -> M.ESpawn (recurse value)
  M.ESqlCache index typ keys action ->
    M.ESqlCache index typ (map recurse keys) (recurse action)
  M.ESqlCacheFlush typ flushes action -> M.ESqlCacheFlush typ
    [ flush {M.sqlCacheFlushKeys = map (fmap recurse) (M.sqlCacheFlushKeys flush)}
    | flush <- flushes
    ]
    (recurse action)
  leaf -> leaf
  where
    recurse = rewriteExpression foreignTypes fusedIds

maximumIdentifier :: M.File -> Int
maximumIdentifier file = maximum (0 : modeIds <> concatMap declarationIds (M.fileDeclarations file))
  where
    modeIds = [M.unGlobalId identifier | (identifier, _, _) <- M.fileFunctionModes file]
    declarationIds (Located _ declaration) = case declaration of
      M.DDatatype datatypes ->
        [ M.unGlobalId identifier
        | (_, datatype, constructors) <- datatypes
        , identifier <- datatype : [constructor | (_, constructor, _) <- constructors]
        ]
      M.DVal _ identifier _ _ _ -> [M.unGlobalId identifier]
      M.DValRec bindings -> [M.unGlobalId identifier | (_, identifier, _, _, _) <- bindings]
      M.DExport _ _ identifier _ _ _ -> [M.unGlobalId identifier]
      M.DDatabase info ->
        [ M.unGlobalId (M.databaseExpunge info)
        , M.unGlobalId (M.databaseInitialize info)
        ]
      M.DOnError identifier -> [M.unGlobalId identifier]
      _ -> []
