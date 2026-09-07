-- | Stable, span-free rendering of the target-neutral Mono IR.
module Vr.Mono.Pretty
  ( prettyFile
  , prettyProjectFile
  , prettyDeclaration
  ) where

import Data.List (intercalate)
import System.FilePath (normalise)
import qualified Vr.Mono.Syntax as Mono
import Vr.Source (Located (..), Span (..))

prettyFile :: Mono.File -> String
prettyFile monoFile =
  unlines
    ( [ "Mono.File"
      , "  declarations: " <> show (length declarations)
      , "  function modes: " <> show (length modes)
      ]
        <> map (indent 2 . renderDecl) declarations
        <> ["  modes:", indent 4 (renderList renderMode modes)]
    )
  where
    declarations = Mono.fileDeclarations monoFile
    modes = Mono.fileFunctionModes monoFile

prettyProjectFile :: [FilePath] -> Mono.File -> String
prettyProjectFile targets monoFile =
  unlines
    ( [ "Mono.File (project declarations)"
      , "  complete declarations: " <> show (length declarations)
      , "  complete function modes: " <> show (length allModes)
      , "  source/foreign declarations: " <> show (length selected)
      ]
        <> map (indent 2 . renderDecl) selected
        <> ["  generated declarations referenced by source: " <> show (length generatedRelated)]
        <> map (indent 2 . renderDeclForIds selectedReferences) generatedRelated
        <> ["  source function modes:", indent 4 (renderList renderMode modes)]
    )
  where
    declarations = Mono.fileDeclarations monoFile
    allModes = Mono.fileFunctionModes monoFile
    fromTarget declaration =
      normalise (spanFile (locatedSpan declaration)) `elem` map normalise targets
    selected = filter (\declaration -> fromTarget declaration || isForeign declaration) declarations
    isForeign declaration = case locatedValue declaration of
      Mono.DForeign {} -> True
      _ -> False
    selectedReferences = concatMap declarationReferences selected
    generatedRelated =
      filter
        (\declaration -> not (fromTarget declaration) && any (`elem` selectedReferences) (declarationIds declaration))
        declarations
    selectedIds = concatMap declarationIds selected
    modes = filter (\(identifier, _, _) -> identifier `elem` (selectedIds <> selectedReferences)) allModes

prettyDeclaration :: Mono.Decl -> String
prettyDeclaration = renderDecl

renderDecl :: Mono.Decl -> String
renderDecl (Located _ declaration) = case declaration of
  Mono.DForeign moduleName name typ ->
    node "foreign" [moduleName <> "." <> name, renderType typ]
  Mono.DDatatype definitions ->
    node "datatype-group" (map renderDatatype definitions)
  Mono.DVal name identifier typ value url ->
    node "value" [name, renderId identifier, renderType typ, renderExpr value, show url]
  Mono.DValRec bindings ->
    node "value-rec" (map renderBinding bindings)
  Mono.DExport kind url identifier arguments result protected ->
    node "export" [show kind, show url, renderId identifier, renderList renderType arguments, renderType result, show protected]
  Mono.DTable name fields primary constraints ->
    node "table" [show name, renderList renderField fields, renderExpr primary, renderExpr constraints]
    where renderField (field, typ) = node "field" [show field, renderType typ]
  Mono.DSequence name -> node "sequence-declaration" [show name]
  Mono.DView name fields expression ->
    node "view" [show name, renderList renderField fields, renderExpr expression]
    where renderField (field, typ) = node "field" [show field, renderType typ]
  Mono.DIndex name fields ->
    node "index" [show name, renderList (\(field, mode) -> node "field" [show field, show mode]) fields]
  Mono.DIndexDynamic table modes -> node "dynamic-index" [renderExpr table, renderExpr modes]
  Mono.DDatabase information ->
    node "database"
      [ show (Mono.databaseName information)
      , renderId (Mono.databaseExpunge information)
      , renderId (Mono.databaseInitialize information)
      , show (Mono.databaseUsesSimilar information)
      ]
  Mono.DDatabaseRaw connection -> node "database-raw" [show connection]
  Mono.DJavaScript source -> node "javascript-declaration" [show source]
  Mono.DCookie name -> node "cookie" [show name]
  Mono.DStyle name -> node "style" [show name]
  Mono.DTask schedule body -> node "task" [renderExpr schedule, renderExpr body]
  Mono.DPolicy policy -> node "policy" [renderPolicy policy]
  Mono.DPolicyRaw expression -> node "policy-raw" [renderExpr expression]
  Mono.DOnError identifier -> node "on-error" [renderId identifier]

renderPolicy :: Mono.Policy -> String
renderPolicy policy = case policy of
  Mono.PolicyClient expression -> node "client" [renderExpr expression]
  Mono.PolicyInsert expression -> node "insert" [renderExpr expression]
  Mono.PolicyDelete expression -> node "delete" [renderExpr expression]
  Mono.PolicyUpdate expression -> node "update" [renderExpr expression]
  Mono.PolicySequence expression -> node "sequence" [renderExpr expression]

renderDeclForIds :: [Mono.GlobalId] -> Mono.Decl -> String
renderDeclForIds identifiers source@(Located _ declaration) = case declaration of
  Mono.DValRec bindings ->
    node "value-rec-fragment" (map renderBinding (filter (\(_, identifier, _, _, _) -> identifier `elem` identifiers) bindings))
  _ -> renderDecl source

renderDatatype :: (String, Mono.GlobalId, [(String, Mono.GlobalId, Maybe Mono.Type)]) -> String
renderDatatype (name, identifier, constructors) =
  node "datatype" [name, renderId identifier, renderList renderConstructor constructors]
  where
    renderConstructor (constructorName, constructorId, payload) =
      node "constructor" [constructorName, renderId constructorId, maybe "nullary" renderType payload]

renderBinding :: (String, Mono.GlobalId, Mono.Type, Mono.Expr, String) -> String
renderBinding (name, identifier, typ, value, url) =
  node "binding" [name, renderId identifier, renderType typ, renderExpr value, show url]

renderType :: Mono.Type -> String
renderType (Located _ typ) = case typ of
  Mono.TFun domain range -> node "function" [renderType domain, renderType range]
  Mono.TRecord fields -> node "record-type" [renderList renderField fields]
    where renderField (name, fieldType) = node "field" [show name, renderType fieldType]
  Mono.TDatatype identifier -> node "datatype-type" [renderId identifier]
  Mono.TFfi moduleName name -> node "ffi-type" [moduleName <> "." <> name]
  Mono.TOption element -> node "option-type" [renderType element]
  Mono.TList element -> node "list-type" [renderType element]
  Mono.TSource -> "source-type"
  Mono.TSignal element -> node "signal-type" [renderType element]

renderPatCon :: Mono.PatCon -> String
renderPatCon constructor = case constructor of
  Mono.PConVar identifier -> node "constructor-id" [renderId identifier]
  Mono.PConFfi moduleName datatypeName name payload ->
    node "ffi-constructor" [moduleName <> "." <> datatypeName <> "." <> name, maybe "nullary" renderType payload]

renderPattern :: Mono.Pattern -> String
renderPattern (Located _ pattern') = case pattern' of
  Mono.PVar name typ -> node "variable-pattern" [name, renderType typ]
  Mono.PPrim primitive -> node "primitive-pattern" [show primitive]
  Mono.PCon classification constructor payload ->
    node "constructor-pattern" [show classification, renderPatCon constructor, maybe "nullary" renderPattern payload]
  Mono.PRecord fields -> node "record-pattern" [renderList renderField fields]
    where renderField (name, nested, typ) = node "field" [show name, renderPattern nested, renderType typ]
  Mono.PNone typ -> node "none-pattern" [renderType typ]
  Mono.PSome typ nested -> node "some-pattern" [renderType typ, renderPattern nested]

renderStatic :: Mono.StaticArg -> String
renderStatic argument = case argument of
  Mono.StaticType typ -> node "static-type" [renderType typ]
  Mono.StaticName name -> node "static-name" [show name]
  Mono.StaticRow fields -> node "static-row" [renderList (\(name, value) -> node "field" [renderStatic name, renderStatic value]) fields]
  Mono.StaticTuple elements -> node "static-tuple" (map renderStatic elements)
  Mono.StaticFfi moduleName name arguments -> node "static-ffi" ((moduleName <> "." <> name) : map renderStatic arguments)
  Mono.StaticMap -> "static-map"
  Mono.StaticBound index -> node "static-bound" [show index]
  Mono.StaticLambda body -> node "static-lambda" [renderStatic body]
  Mono.StaticApply function argument' -> node "static-apply" [renderStatic function, renderStatic argument']
  Mono.StaticProject tuple index -> node "static-project" [renderStatic tuple, show index]
  Mono.StaticConcat left right -> node "static-concat" [renderStatic left, renderStatic right]
  Mono.StaticUnit -> "static-unit"

renderExpr :: Mono.Expr -> String
renderExpr (Located _ expression) = case expression of
  Mono.EPrim primitive -> node "primitive" [show primitive]
  Mono.ERel index -> node "local" [show index]
  Mono.ENamed identifier -> node "global" [renderId identifier]
  Mono.ECon classification constructor payload ->
    node "construct" [show classification, renderPatCon constructor, maybe "nullary" renderExpr payload]
  Mono.ENone typ -> node "none" [renderType typ]
  Mono.ESome typ value -> node "some" [renderType typ, renderExpr value]
  Mono.EFfi moduleName name staticArguments ->
    node "ffi" ((moduleName <> "." <> name) : map renderStatic staticArguments)
  Mono.EFfiApp moduleName name staticArguments arguments ->
    node "ffi-call"
      [ moduleName <> "." <> name
      , renderList renderStatic staticArguments
      , renderList (\(value, typ) -> node "argument" [renderExpr value, renderType typ]) arguments
      ]
  Mono.EApp function argument -> node "apply" [renderExpr function, renderExpr argument]
  Mono.EAbs name domain range body -> node "lambda" [name, renderType domain, renderType range, renderExpr body]
  Mono.EStaticApp function argument -> node "static-apply-expression" [renderExpr function, renderStatic argument]
  Mono.EUnop operator value -> node "unary" [show operator, renderExpr value]
  Mono.EBinop intness operator left right -> node "binary" [show intness, show operator, renderExpr left, renderExpr right]
  Mono.ERecord fields -> node "record" [renderList renderField fields]
    where renderField (name, value, typ) = node "field" [renderStatic name, renderExpr value, renderType typ]
  Mono.EField record name -> node "project" [renderExpr record, renderStatic name]
  Mono.ERecordConcat left right -> node "record-concat" [renderExpr left, renderExpr right]
  Mono.ERecordCut record names -> node "record-cut" [renderExpr record, renderList renderStatic names]
  Mono.ECase scrutinee branches input result ->
    node "case"
      [ renderExpr scrutinee
      , renderList (\(pattern', body) -> node "branch" [renderPattern pattern', renderExpr body]) branches
      , renderType input
      , renderType result
      ]
  Mono.EStrcat left right -> node "string-concat" [renderExpr left, renderExpr right]
  Mono.EError value typ -> node "error" [renderExpr value, renderType typ]
  Mono.EReturnBlob content value typ -> node "return-blob" [maybe "none" renderExpr content, renderExpr value, renderType typ]
  Mono.ERedirect value typ -> node "redirect" [renderExpr value, renderType typ]
  Mono.EWrite value -> node "write" [renderExpr value]
  Mono.ESeq first second -> node "sequence" [renderExpr first, renderExpr second]
  Mono.ELet name typ value body -> node "let" [name, renderType typ, renderExpr value, renderExpr body]
  Mono.EClosure identifier captures -> node "closure" (renderId identifier : map renderExpr captures)
  Mono.EQuery fields tables state query body initial ->
    node "query" [show (map fst fields), show (map fst tables), renderType state, renderExpr query, renderExpr body, renderExpr initial]
  Mono.EDml value failure -> node "dml" [renderExpr value, show failure]
  Mono.ENextval value -> node "nextval" [renderExpr value]
  Mono.ESetval sequence' value -> node "setval" [renderExpr sequence', renderExpr value]
  Mono.EUnurlify value typ fromPost -> node "unurlify" [renderExpr value, renderType typ, show fromPost]
  Mono.EJavaScript mode value -> node "javascript" [show mode, renderExpr value]
  Mono.ESignalReturn value -> node "signal-return" [renderExpr value]
  Mono.ESignalBind signal continuation -> node "signal-bind" [renderExpr signal, renderExpr continuation]
  Mono.ESignalSource value -> node "signal-source" [renderExpr value]
  Mono.EServerCall call typ effect failure -> node "server-call" [renderExpr call, renderType typ, show effect, show failure]
  Mono.ERecv channel typ -> node "receive" [renderExpr channel, renderType typ]
  Mono.ESleep value -> node "sleep" [renderExpr value]
  Mono.ESpawn value -> node "spawn" [renderExpr value]
  Mono.ESqlCache index typ keys action -> node "sql-cache"
    [show index, renderType typ, renderList id (map renderExpr keys), renderExpr action]
  Mono.ESqlCacheFlush typ flushes action -> node "sql-cache-flush"
    [ renderType typ
    , renderList id
        [ node "cache"
            [ show (Mono.sqlCacheFlushIndex flush)
            , renderList id [maybe "*" renderExpr key | key <- Mono.sqlCacheFlushKeys flush]
            ]
        | flush <- flushes
        ]
    , renderExpr action
    ]

declarationIds :: Mono.Decl -> [Mono.GlobalId]
declarationIds (Located _ declaration) = case declaration of
  Mono.DVal _ identifier _ _ _ -> [identifier]
  Mono.DValRec bindings -> [identifier | (_, identifier, _, _, _) <- bindings]
  _ -> []

declarationReferences :: Mono.Decl -> [Mono.GlobalId]
declarationReferences (Located _ declaration) = case declaration of
  Mono.DVal _ _ _ value _ -> expressionReferences value
  Mono.DValRec bindings -> concatMap (\(_, _, _, value, _) -> expressionReferences value) bindings
  _ -> []

expressionReferences :: Mono.Expr -> [Mono.GlobalId]
expressionReferences (Located _ expression) = case expression of
  Mono.ENamed identifier -> [identifier]
  Mono.ECon _ constructor payload -> patConReference constructor <> maybe [] expressionReferences payload
  Mono.ESome _ value -> expressionReferences value
  Mono.EFfiApp _ _ _ arguments -> concatMap (expressionReferences . fst) arguments
  Mono.EApp function argument -> expressionReferences function <> expressionReferences argument
  Mono.EAbs _ _ _ body -> expressionReferences body
  Mono.EStaticApp function _ -> expressionReferences function
  Mono.EUnop _ value -> expressionReferences value
  Mono.EBinop _ _ left right -> expressionReferences left <> expressionReferences right
  Mono.ERecord fields -> concatMap (\(_, value, _) -> expressionReferences value) fields
  Mono.EField record _ -> expressionReferences record
  Mono.ERecordConcat left right -> expressionReferences left <> expressionReferences right
  Mono.ERecordCut record _ -> expressionReferences record
  Mono.ECase scrutinee branches _ _ -> expressionReferences scrutinee <> concatMap (expressionReferences . snd) branches
  Mono.EStrcat left right -> expressionReferences left <> expressionReferences right
  Mono.EError value _ -> expressionReferences value
  Mono.EReturnBlob content value _ -> maybe [] expressionReferences content <> expressionReferences value
  Mono.ERedirect value _ -> expressionReferences value
  Mono.EWrite value -> expressionReferences value
  Mono.ESeq first second -> expressionReferences first <> expressionReferences second
  Mono.ELet _ _ value body -> expressionReferences value <> expressionReferences body
  Mono.EClosure identifier captures -> identifier : concatMap expressionReferences captures
  Mono.EQuery _ _ _ query body initial -> expressionReferences query <> expressionReferences body <> expressionReferences initial
  Mono.EDml value _ -> expressionReferences value
  Mono.ENextval value -> expressionReferences value
  Mono.ESetval sequence' value -> expressionReferences sequence' <> expressionReferences value
  Mono.EUnurlify value _ _ -> expressionReferences value
  Mono.EJavaScript _ value -> expressionReferences value
  Mono.ESignalReturn value -> expressionReferences value
  Mono.ESignalBind signal continuation -> expressionReferences signal <> expressionReferences continuation
  Mono.ESignalSource value -> expressionReferences value
  Mono.EServerCall call _ _ _ -> expressionReferences call
  Mono.ERecv channel _ -> expressionReferences channel
  Mono.ESleep value -> expressionReferences value
  Mono.ESpawn value -> expressionReferences value
  Mono.ESqlCache _ _ keys action ->
    concatMap expressionReferences keys <> expressionReferences action
  Mono.ESqlCacheFlush _ flushes action ->
    concat
      [ maybe [] expressionReferences key
      | flush <- flushes
      , key <- Mono.sqlCacheFlushKeys flush
      ]
      <> expressionReferences action
  _ -> []

patConReference :: Mono.PatCon -> [Mono.GlobalId]
patConReference constructor = case constructor of
  Mono.PConVar identifier -> [identifier]
  Mono.PConFfi {} -> []

renderMode :: (Show a, Show b) => (Mono.GlobalId, a, b) -> String
renderMode (identifier, sidedness, database) =
  renderId identifier <> ":" <> show sidedness <> ":" <> show database

renderId :: Mono.GlobalId -> String
renderId = ('#' :) . show . Mono.unGlobalId

renderList :: (a -> String) -> [a] -> String
renderList render values
  | null rendered = "[]"
  | compactLength <= 88 && all singleLine rendered = "[" <> intercalate ", " rendered <> "]"
  | otherwise = "[\n" <> intercalate ",\n" (map (indent 2) rendered) <> "\n]"
  where
    rendered = map render values
    compactLength = sum (map length rendered) + 2 * length rendered

node :: String -> [String] -> String
node name fields
  | null fields = "(" <> name <> ")"
  | compactLength <= 88 && all singleLine fields = "(" <> unwords (name : fields) <> ")"
  | otherwise = "(" <> name <> "\n" <> intercalate "\n" (map (indent 2) fields) <> "\n)"
  where
    compactLength = length name + sum (map length fields) + length fields + 2

singleLine :: String -> Bool
singleLine = notElem '\n'

indent :: Int -> String -> String
indent amount value = intercalate "\n" [replicate amount ' ' <> line | line <- lines value]
