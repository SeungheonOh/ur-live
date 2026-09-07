{-# LANGUAGE DerivingStrategies #-}

-- | A small, generated Node N-API bridge for custom C FFI values used by the
-- direct-JavaScript server.  The bridge deliberately accepts only ABI shapes
-- whose C and JavaScript representations are explicit here.
module Vr.Backend.NodeAddon
  ( ForeignBinding (..)
  , ForeignCodec (..)
  , collectForeignBindings
  , collectNativeShimBindings
  , collectForeignCodecs
  , renderNodeAddon
  , renderNativeShim
  ) where

import Data.Char (isAlphaNum, isAscii, toUpper)
import Data.List (intercalate, nub)
import qualified Data.Set as Set
import qualified Vr.Mono.Server as Server
import qualified Vr.Mono.Syntax as M
import Vr.Project (ProjectDirective (..), ProjectPlan (..))
import Vr.Source
  ( Diagnostic
  , DiagnosticPhase (BackendPhase)
  , Located (..)
  , diagnostic
  , noSpan
  )

data ForeignBinding = ForeignBinding
  { foreignBindingId :: !Int
  , foreignBindingModule :: !String
  , foreignBindingMember :: !String
  , foreignBindingDomains :: ![M.Type]
  , foreignBindingResult :: !M.Type
  , foreignBindingTransactional :: !Bool
  }
  deriving stock (Eq, Show)

-- | A project-declared C codec for an abstract foreign datatype.  IDs are
-- stable in project-directive order and are shared by generated JavaScript
-- and the N-API dispatch table.
data ForeignCodec = ForeignCodec
  { foreignCodecId :: !Int
  , foreignCodecModule :: !String
  , foreignCodecType :: !String
  }
  deriving stock (Eq, Show)

collectForeignCodecs :: ProjectPlan -> [ForeignCodec]
collectForeignCodecs plan = zipWith make [0 ..] names
  where
    names = nub
      [ (moduleName, typeName)
      | directive <- projectDirectives plan
      , projectDirectiveName directive == "clientToServer"
      , let (moduleName, suffix) = break (== '.') (projectDirectiveArgument directive)
      , '.' : typeName <- [suffix]
      , moduleName /= "Basis"
      , not (null moduleName)
      , not (null typeName)
      ]
    make identifier (moduleName, typeName) = ForeignCodec identifier moduleName typeName

data AbiType
  = AbiInt
  | AbiFloat
  | AbiBool
  | AbiChar
  | AbiString
  | AbiTime
  | AbiBlob
  | AbiFile
  | AbiPostBody
  | AbiClient
  | AbiChannel
  | AbiUnit
  | AbiOpaque !String !String
  deriving stock (Eq, Show)

-- | Collect only custom foreign symbols reachable from server roots.  The
-- numeric IDs follow declaration order and are shared by generated JS and C.
collectForeignBindings :: ProjectPlan -> M.File -> Either [Diagnostic] [ForeignBinding]
collectForeignBindings plan file =
  if null problems then Right bindings else Left problems
  where
    wanted = Server.serverForeignNames plan file
    transactional = directiveNames "ffiTransaction" plan
    declarations =
      [ (locatedSpan declaration, moduleName, member, typ)
      | declaration <- M.fileDeclarations file
      , M.DForeign moduleName member typ <- [locatedValue declaration]
      , Set.member (moduleName, member) wanted
      ]
    declaredNames = Set.fromList [(moduleName, member) | (_, moduleName, member, _) <- declarations]
    missing = Set.toAscList (Set.difference wanted declaredNames)
    missingProblems =
      [ diagnostic BackendPhase "javascript-ffi-signature" noSpan
          ("Server FFI has no preserved monomorphic signature: " <> moduleName <> "." <> member)
      | (moduleName, member) <- missing
      ]
    checked = zipWith check [0 ..] declarations
    problems = missingProblems <> [problem | Left problem <- checked]
    bindings = [binding | Right binding <- checked]
    check identifier (location, moduleName, member, typ) = do
      let (allDomains, result) = unwind typ
          isTransactional = Set.member (moduleName, member) transactional
      domains <- if isTransactional
        then case reverse allDomains of
          finalUnit : rest | isUnit finalUnit -> Right (reverse rest)
          _ -> Left (diagnostic BackendPhase "javascript-ffi-transaction" location
            (moduleName <> "." <> member
              <> " is transactional but its foreign signature has no final unit argument"))
        else Right allDomains
      mapM_ validateAbiType (domains <> [result])
      Right ForeignBinding
        { foreignBindingId = identifier
        , foreignBindingModule = moduleName
        , foreignBindingMember = member
        , foreignBindingDomains = domains
        , foreignBindingResult = result
        , foreignBindingTransactional = isTransactional
        }
    unwind typ = case locatedValue typ of
      M.TFun domain range -> let (domains, result) = unwind range in (domain : domains, result)
      _ -> ([], typ)

-- | Collect the reachable native FFI calls that need a generated C ABI
-- adapter.  Unlike 'collectForeignBindings', this deliberately ignores calls
-- without custom abstract values: the native backend supports more C ABI
-- shapes than the Node bridge, and generating the shim must not impose the
-- direct-JavaScript bridge's restrictions on those calls.
collectNativeShimBindings :: ProjectPlan -> M.File -> Either [Diagnostic] [ForeignBinding]
collectNativeShimBindings plan file =
  if null problems then Right bindings else Left problems
  where
    wanted = Server.serverForeignNames plan file
    transactional = directiveNames "ffiTransaction" plan
    declarations =
      [ (locatedSpan declaration, moduleName, member, typ)
      | declaration <- M.fileDeclarations file
      , M.DForeign moduleName member typ <- [locatedValue declaration]
      , Set.member (moduleName, member) wanted
      , signatureHasOpaque typ
      ]
    checked = zipWith check [0 ..] declarations
    problems = [problem | Left problem <- checked]
    bindings = [binding | Right binding <- checked]
    check identifier (location, moduleName, member, typ) = do
      let (allDomains, result) = unwind typ
          isTransactional = Set.member (moduleName, member) transactional
      domains <- if isTransactional
        then case reverse allDomains of
          finalUnit : rest | isUnit finalUnit -> Right (reverse rest)
          _ -> Left (diagnostic BackendPhase "native-ffi-transaction" location
            (moduleName <> "." <> member
              <> " is transactional but its foreign signature has no final unit argument"))
        else Right allDomains
      mapM_ validateNativeShimType (domains <> [result])
      Right ForeignBinding
        { foreignBindingId = identifier
        , foreignBindingModule = moduleName
        , foreignBindingMember = member
        , foreignBindingDomains = domains
        , foreignBindingResult = result
        , foreignBindingTransactional = isTransactional
        }
    unwind typ = case locatedValue typ of
      M.TFun domain range -> let (domains, result) = unwind range in (domain : domains, result)
      _ -> ([], typ)

signatureHasOpaque :: M.Type -> Bool
signatureHasOpaque typ = case locatedValue typ of
  M.TFun domain range -> signatureHasOpaque domain || signatureHasOpaque range
  M.TFfi moduleName _ -> moduleName /= "Basis"
  _ -> False

validateNativeShimType :: M.Type -> Either Diagnostic ()
validateNativeShimType typ = case abiType typ of
  Just _ -> Right ()
  Nothing -> Left (diagnostic BackendPhase "native-ffi-shim-type" (locatedSpan typ)
    ("A native C FFI signature containing an abstract value also contains "
      <> describeType typ <> ", whose portable C ABI is not defined"))

validateAbiType :: M.Type -> Either Diagnostic ()
validateAbiType typ = case abiType typ of
  Just _ -> Right ()
  Nothing -> Left (diagnostic BackendPhase "javascript-ffi-type" (locatedSpan typ)
    ("The direct-JavaScript C FFI does not support ABI type " <> describeType typ))

abiType :: M.Type -> Maybe AbiType
abiType typ = case locatedValue typ of
  M.TFfi "Basis" "int" -> Just AbiInt
  M.TFfi "Basis" "float" -> Just AbiFloat
  M.TFfi "Basis" "bool" -> Just AbiBool
  M.TFfi "Basis" "char" -> Just AbiChar
  M.TFfi "Basis" "string" -> Just AbiString
  M.TFfi "Basis" "time" -> Just AbiTime
  M.TFfi "Basis" "blob" -> Just AbiBlob
  M.TFfi "Basis" "file" -> Just AbiFile
  M.TFfi "Basis" "postBody" -> Just AbiPostBody
  M.TFfi "Basis" "client" -> Just AbiClient
  M.TFfi "Basis" "channel" -> Just AbiChannel
  M.TFfi "Basis" name
    | name `elem`
        [ "xhtml", "page", "xbody", "css_class", "queryString"
        , "requestHeader", "responseHeader", "envVar", "meta", "url"
        , "css_value", "css_property", "css_style", "id", "mimeType"
        , "data_attr"
        ] -> Just AbiString
  M.TFfi "Basis" _ -> Nothing
  M.TFfi moduleName name -> Just (AbiOpaque moduleName name)
  M.TRecord [] -> Just AbiUnit
  _ -> Nothing

isUnit :: M.Type -> Bool
isUnit typ = abiType typ == Just AbiUnit

describeType :: M.Type -> String
describeType typ = case locatedValue typ of
  M.TFun _ _ -> "a function"
  M.TRecord [] -> "unit"
  M.TRecord _ -> "a non-empty record"
  M.TDatatype _ -> "an algebraic datatype"
  M.TFfi moduleName name -> moduleName <> "." <> name
  M.TOption _ -> "option"
  M.TList _ -> "list"
  M.TSource -> "source"
  M.TSignal _ -> "signal"

-- | Render the application-specific dispatch half of the addon.  Absolute
-- include paths are supplied by project resolution and provide foreign typedefs
-- and prototypes; compatible prototypes are emitted as well for primitive-only
-- FFIs that do not need a custom typedef.
renderNodeAddon
  :: [FilePath]
  -> [ForeignBinding]
  -> [ForeignCodec]
  -> [Server.ForeignConstructor]
  -> String
renderNodeAddon includes bindings codecs constructors = unlines
  ( [ "#include <stdlib.h>"
    , "#include \"vr_napi_ffi.h\""
    ]
      <> map renderInclude includes
      <> [""]
      <> map renderPrototype bindings
      <> [""]
      <> concatMap renderWrapper bindings
      <> concatMap renderCodecWrapper codecs
      <> concatMap renderForeignConstructorHelpers constructors
      <> concatMap renderForeignConstructorWrapper constructors
      <> [ "napi_value vr_napi_dispatch(napi_env env, vr_napi_context *context,"
         , "                            int32_t binding_id, napi_value arguments) {"
         , "  switch (binding_id) {"
         ]
      <> [ "    case " <> show (foreignBindingId binding) <> ": return vr_ffi_call_"
             <> show (foreignBindingId binding) <> "(env, context, arguments);"
         | binding <- bindings
         ]
      <> [ "    default: return vr_napi_throw(env, \"Unknown generated foreign binding\");"
         , "  }"
         , "}"
         , ""
         , "napi_value vr_napi_urlify_dispatch(napi_env env, vr_napi_context *context,"
         , "                                    int32_t codec_id, napi_value value) {"
         , "  switch (codec_id) {"
         ]
      <> [ "    case " <> show (foreignCodecId codec) <> ": return vr_codec_urlify_"
             <> show (foreignCodecId codec) <> "(env, context, value);"
         | codec <- codecs
         ]
      <> [ "    default: return vr_napi_throw(env, \"Unknown generated foreign codec\");"
         , "  }"
         , "}"
         , ""
         , "napi_value vr_napi_unurlify_dispatch(napi_env env, vr_napi_context *context,"
         , "                                      int32_t codec_id, napi_value value) {"
         , "  switch (codec_id) {"
         ]
      <> [ "    case " <> show (foreignCodecId codec) <> ": return vr_codec_unurlify_"
             <> show (foreignCodecId codec) <> "(env, context, value);"
         | codec <- codecs
         ]
      <> [ "    default: return vr_napi_throw(env, \"Unknown generated foreign codec\");"
         , "  }"
         , "}"
         , ""
         , "napi_value vr_napi_constructor_dispatch(napi_env env, vr_napi_context *context,"
         , "                                        int32_t constructor_id, napi_value arguments) {"
         , "  switch (constructor_id) {"
         ]
      <> [ "    case " <> constructorIdentifier constructor <> ": return vr_constructor_make_"
             <> constructorIdentifier constructor <> "(env, context, arguments);"
         | constructor <- constructors
         ]
      <> [ "    default: return vr_napi_throw(env, \"Unknown generated foreign constructor\");"
         , "  }"
         , "}"
         , ""
         , "napi_value vr_napi_constructor_match_dispatch(napi_env env, vr_napi_context *context,"
         , "                                              int32_t constructor_id, napi_value arguments) {"
         , "  switch (constructor_id) {"
         ]
      <> [ "    case " <> constructorIdentifier constructor <> ": return vr_constructor_match_"
             <> constructorIdentifier constructor <> "(env, context, arguments);"
         | constructor <- constructors
         ]
      <> [ "    default: return vr_napi_throw(env, \"Unknown generated foreign constructor\");"
         , "  }"
         , "}"
         , ""
         , "napi_value vr_napi_constructor_payload_dispatch(napi_env env, vr_napi_context *context,"
         , "                                                int32_t constructor_id, napi_value arguments) {"
         , "  switch (constructor_id) {"
         ]
      <> [ "    case " <> constructorIdentifier constructor <> ": return vr_constructor_payload_"
             <> constructorIdentifier constructor <> "(env, context, arguments);"
         | constructor <- constructors
         , case Server.foreignConstructorPayload constructor of Just _ -> True; Nothing -> False
         ]
      <> [ "    default: return vr_napi_throw(env, \"Foreign constructor has no payload\");"
         , "  }"
         , "}"
         ])

-- | Render C ABI adapters for native LLVM calls involving an abstract foreign
-- type.  LLVM keeps every abstract value as a pointer to a box; the adapter
-- copies the actual C typedef into and out of that box.  This works for scalar,
-- aggregate, and pointer typedefs without guessing their representation.
renderNativeShim
  :: [FilePath]
  -> [ForeignBinding]
  -> [ForeignCodec]
  -> [Server.ForeignConstructor]
  -> String
renderNativeShim [] [] [] [] = ""
renderNativeShim includes bindings codecs constructors = unlines
  ([ "#include <stdint.h>"
   , "#include <stdlib.h>"
   , "#include <string.h>"
   , "#include \"urweb/urweb.h\""
   , "extern size_t vr_runtime_consumed_components(const char *, const char *, size_t);"
   ] <> map renderInclude includes <> [""]
    <> concatMap renderBinding (filter needsShim bindings)
    <> concatMap renderNativeCodec codecs
    <> concatMap renderForeignConstructorHelpers constructors)
  where
    needsShim binding = any isOpaque
      (foreignBindingResult binding : foreignBindingDomains binding)
    isOpaque typ = case abiType typ of
      Just AbiOpaque {} -> True
      _ -> False
    renderBinding binding =
      [ nativeResultType result <> " " <> nativeSymbol binding <> "("
          <> intercalate ", " ("uw_context vr_context" : zipWith nativeDomain [0 :: Int ..] domains)
          <> ") {"
      , "  " <> cType result <> " vr_result = " <> foreignSymbol binding
          <> "(vr_context" <> concat (zipWith nativeArgument [0 :: Int ..] domains) <> ");"
      ] <> nativeReturn result <> ["}", ""]
      where
        domains = foreignBindingDomains binding
        result = foreignBindingResult binding
    nativeDomain index typ = nativeCType typ <> " vr_arg_" <> show index
    nativeArgument index typ = case abiType typ of
      Just AbiOpaque {} -> ", *(" <> cType typ <> " *)vr_arg_" <> show index
      _ -> ", vr_arg_" <> show index
    nativeReturn typ = case abiType typ of
      Just AbiOpaque {} ->
        [ "  " <> cType typ <> " *vr_box = uw_malloc(vr_context, sizeof(*vr_box));"
        , "  if (vr_box == NULL) abort();"
        , "  *vr_box = vr_result;"
        , "  return vr_box;"
        ]
      _ -> ["  return vr_result;"]
    nativeResultType = nativeCType
    nativeCType typ = case abiType typ of
      Just AbiOpaque {} -> "void *"
      _ -> cType typ
    nativeSymbol binding =
      "vr_ffi_" <> sanitize (foreignBindingModule binding)
        <> "_" <> sanitize (foreignBindingMember binding)

-- The native compiler stores every non-Basis FFI value as a pointer to a box
-- containing the exact C typedef.  These helpers let LLVM construct and
-- inspect the three representations prescribed by Ur/Web without guessing a
-- typedef's size or layout.
renderForeignConstructorHelpers :: Server.ForeignConstructor -> [String]
renderForeignConstructorHelpers constructor =
  [ "void *vr_foreign_constructor_make_" <> identifier
      <> "(uw_context vr_context, void *vr_payload) {"
  ]
    <> constructValue
    <> [ "  " <> datatypeType <> " *vr_box = uw_malloc(vr_context, sizeof(*vr_box));"
       , "  if (vr_box == NULL) abort();"
       , "  *vr_box = vr_result;"
       , "  return vr_box;"
       , "}"
       , ""
       , "int32_t vr_foreign_constructor_match_" <> identifier <> "(void *vr_raw) {"
       , "  if (vr_raw == NULL) return 0;"
       , "  " <> datatypeType <> " vr_value = *(" <> datatypeType <> " *)vr_raw;"
       , "  return " <> matchExpression <> ";"
       , "}"
       , ""
       ]
    <> payloadHelper
  where
    identifier = constructorIdentifier constructor
    datatypeType = foreignDatatypeCType constructor
    constant = foreignConstructorConstant constructor
    payload = Server.foreignConstructorPayload constructor
    payloadExpression typ = "*(" <> cType typ <> " *)vr_payload"
    constructValue = case (Server.foreignConstructorKind constructor, payload) of
      (M.Enum, Nothing) ->
        ["  " <> datatypeType <> " vr_result = " <> constant <> ";"]
      (M.Option, Nothing) ->
        ["  " <> datatypeType <> " vr_result = NULL;"]
      (M.Option, Just typ)
        | cUnboxable typ ->
            ["  " <> datatypeType <> " vr_result = " <> payloadExpression typ <> ";"]
        | otherwise ->
            [ "  " <> cType typ <> " *vr_inner = uw_malloc(vr_context, sizeof(*vr_inner));"
            , "  if (vr_inner == NULL) abort();"
            , "  *vr_inner = " <> payloadExpression typ <> ";"
            , "  " <> datatypeType <> " vr_result = vr_inner;"
            ]
      (M.Default, payloadType) ->
        [ "  " <> datatypeType <> " vr_result = uw_malloc(vr_context, sizeof(struct "
            <> foreignStructName constructor <> "));"
        , "  if (vr_result == NULL) abort();"
        , "  vr_result->tag = " <> constant <> ";"
        ] <> case payloadType of
          Nothing -> []
          Just typ ->
            [ "  vr_result->data.uw_" <> sanitize (Server.foreignConstructorName constructor)
                <> " = " <> payloadExpression typ <> ";"
            ]
      (_, _) -> ["  " <> datatypeType <> " vr_result = (" <> datatypeType <> ")0;"]
    matchExpression = case Server.foreignConstructorKind constructor of
      M.Enum -> "vr_value == " <> constant
      M.Option -> case payload of
        Nothing -> "vr_value == NULL"
        Just _ -> "vr_value != NULL"
      M.Default -> "vr_value != NULL && vr_value->tag == " <> constant
    payloadHelper = case payload of
      Nothing -> []
      Just typ ->
        [ "void *vr_foreign_constructor_payload_" <> identifier
            <> "(uw_context vr_context, void *vr_raw) {"
        , "  " <> datatypeType <> " vr_value = *(" <> datatypeType <> " *)vr_raw;"
        , "  " <> cType typ <> " vr_result = " <> extractedPayload typ <> ";"
        , "  " <> cType typ <> " *vr_box = uw_malloc(vr_context, sizeof(*vr_box));"
        , "  if (vr_box == NULL) abort();"
        , "  *vr_box = vr_result;"
        , "  return vr_box;"
        , "}"
        , ""
        ]
    extractedPayload typ = case Server.foreignConstructorKind constructor of
      M.Option | cUnboxable typ -> "vr_value"
      M.Option -> "*vr_value"
      M.Default -> "vr_value->data.uw_" <> sanitize (Server.foreignConstructorModule constructor)
        <> "_" <> sanitize (Server.foreignConstructorName constructor)
      M.Enum -> "*(" <> cType typ <> " *)0"

renderForeignConstructorWrapper :: Server.ForeignConstructor -> [String]
renderForeignConstructorWrapper constructor =
  [ "static napi_value vr_constructor_make_" <> identifier
      <> "(napi_env env, vr_napi_context *context, napi_value arguments) {"
  , "  if (!vr_napi_expect_arity(env, arguments, " <> show arity <> ")) return NULL;"
  ]
    <> argument
    <> [ "  void *vr_raw = vr_foreign_constructor_make_" <> identifier
           <> "((uw_context)context, " <> payloadAddress <> ");"
       , "  return vr_napi_make_opaque(env, context, \"" <> cString typeTag <> "\", vr_raw);"
       , "}"
       , ""
       , "static napi_value vr_constructor_match_" <> identifier
           <> "(napi_env env, vr_napi_context *context, napi_value arguments) {"
       , "  (void)context;"
       , "  if (!vr_napi_expect_arity(env, arguments, 1)) return NULL;"
       , "  void *vr_raw = NULL;"
       , "  if (!vr_napi_get_opaque(env, arguments, 0, \"" <> cString typeTag
           <> "\", &vr_raw)) return NULL;"
       , "  return vr_napi_make_bool(env, vr_foreign_constructor_match_" <> identifier
           <> "(vr_raw));"
       , "}"
       , ""
       ]
    <> payloadWrapper
  where
    identifier = constructorIdentifier constructor
    typeTag = Server.foreignConstructorModule constructor <> "."
      <> Server.foreignConstructorDatatype constructor
    payload = Server.foreignConstructorPayload constructor
    arity = case payload of Nothing -> 0 :: Int; Just _ -> 1
    argument = case payload of
      Nothing -> []
      Just typ -> renderArgument 0 typ
    payloadAddress = case payload of Nothing -> "NULL"; Just _ -> "&vr_arg_0"
    payloadWrapper = case payload of
      Nothing -> []
      Just typ ->
        [ "static napi_value vr_constructor_payload_" <> identifier
            <> "(napi_env env, vr_napi_context *context, napi_value arguments) {"
        , "  if (!vr_napi_expect_arity(env, arguments, 1)) return NULL;"
        , "  void *vr_raw = NULL;"
        , "  if (!vr_napi_get_opaque(env, arguments, 0, \"" <> cString typeTag
            <> "\", &vr_raw)) return NULL;"
        , "  void *vr_payload = vr_foreign_constructor_payload_" <> identifier
            <> "((uw_context)context, vr_raw);"
        , "  " <> cType typ <> " vr_result = *(" <> cType typ <> " *)vr_payload;"
        , "  " <> renderResult typ
        , "}"
        , ""
        ]

constructorIdentifier :: Server.ForeignConstructor -> String
constructorIdentifier = show . Server.foreignConstructorId

foreignStructName :: Server.ForeignConstructor -> String
foreignStructName constructor =
  "uw_" <> sanitize (Server.foreignConstructorModule constructor)
    <> "_" <> sanitize (Server.foreignConstructorDatatype constructor)

foreignDatatypeCType :: Server.ForeignConstructor -> String
foreignDatatypeCType = foreignStructName

foreignConstructorConstant :: Server.ForeignConstructor -> String
foreignConstructorConstant constructor =
  "uw_" <> sanitize (Server.foreignConstructorModule constructor)
    <> "_" <> sanitize (Server.foreignConstructorName constructor)

cUnboxable :: M.Type -> Bool
cUnboxable typ = case locatedValue typ of
  M.TFfi "Basis" name -> name `elem` ["string", "queryString"]
  M.TDatatype {} -> True
  _ -> False

renderNativeCodec :: ForeignCodec -> [String]
renderNativeCodec codec =
  [ "void *" <> nativeCodecDecodeSymbol codec
      <> "(uw_context vr_context, const char *vr_encoded, int64_t *vr_consumed) {"
  , "  size_t vr_length = strlen(vr_encoded);"
  , "  char *vr_copy = uw_malloc(vr_context, vr_length + 1);"
  , "  memcpy(vr_copy, vr_encoded, vr_length + 1);"
  , "  char *vr_cursor = vr_copy;"
  , "  " <> codecCType codec <> " vr_result = " <> codecUnurlifySymbol codec
      <> "(vr_context, &vr_cursor);"
  , "  *vr_consumed = (int64_t)vr_runtime_consumed_components(vr_copy, vr_cursor, vr_length);"
  , "  " <> codecCType codec <> " *vr_box = uw_malloc(vr_context, sizeof(*vr_box));"
  , "  *vr_box = vr_result;"
  , "  return vr_box;"
  , "}"
  , ""
  , "char *" <> nativeCodecEncodeSymbol codec <> "(uw_context vr_context, void *vr_value) {"
  , "  return " <> codecUrlifySymbol codec <> "(vr_context, *(" <> codecCType codec <> " *)vr_value);"
  , "}"
  , ""
  ]

renderCodecWrapper :: ForeignCodec -> [String]
renderCodecWrapper codec =
  [ "static napi_value vr_codec_urlify_" <> identifier
      <> "(napi_env env, vr_napi_context *context, napi_value value) {"
  , "  void *vr_raw = NULL;"
  , "  if (!vr_napi_get_opaque_value(env, value, \"" <> cString typeTag
      <> "\", &vr_raw)) return NULL;"
  , "  char *vr_encoded = " <> codecUrlifySymbol codec
      <> "((uw_context)context, *(" <> codecCType codec <> " *)vr_raw);"
  , "  return vr_napi_make_string(env, vr_encoded);"
  , "}"
  , ""
  , "static napi_value vr_codec_unurlify_" <> identifier
      <> "(napi_env env, vr_napi_context *context, napi_value value) {"
  , "  char *vr_copy = NULL;"
  , "  size_t vr_length = 0;"
  , "  if (!vr_napi_get_string_value(env, context, value, &vr_copy, &vr_length)) return NULL;"
  , "  char *vr_cursor = vr_copy;"
  , "  " <> codecCType codec <> " vr_result = " <> codecUnurlifySymbol codec
      <> "((uw_context)context, &vr_cursor);"
  , "  " <> codecCType codec <> " *vr_box = vr_napi_allocate_opaque(context, sizeof(*vr_box));"
  , "  *vr_box = vr_result;"
  , "  napi_value vr_value = vr_napi_make_opaque(env, context, \"" <> cString typeTag
      <> "\", vr_box);"
  , "  if (vr_value == NULL) return NULL;"
  , "  return vr_napi_make_decoded(env, vr_value,"
  , "    vr_napi_consumed_components(vr_copy, vr_cursor, vr_length));"
  , "}"
  , ""
  ]
  where
    identifier = show (foreignCodecId codec)
    typeTag = foreignCodecModule codec <> "." <> foreignCodecType codec

codecCType :: ForeignCodec -> String
codecCType codec =
  "uw_" <> sanitize (foreignCodecModule codec) <> "_" <> sanitize (foreignCodecType codec)

codecUrlifySymbol :: ForeignCodec -> String
codecUrlifySymbol codec =
  "uw_" <> sanitize (foreignCodecModule codec) <> "_urlify" <> capitalize (foreignCodecType codec)

codecUnurlifySymbol :: ForeignCodec -> String
codecUnurlifySymbol codec =
  "uw_" <> sanitize (foreignCodecModule codec) <> "_unurlify" <> capitalize (foreignCodecType codec)

nativeCodecEncodeSymbol :: ForeignCodec -> String
nativeCodecEncodeSymbol codec =
  "vr_codec_encode_" <> sanitize (foreignCodecModule codec) <> "_" <> sanitize (foreignCodecType codec)

nativeCodecDecodeSymbol :: ForeignCodec -> String
nativeCodecDecodeSymbol codec =
  "vr_codec_decode_" <> sanitize (foreignCodecModule codec) <> "_" <> sanitize (foreignCodecType codec)

capitalize :: String -> String
capitalize [] = []
capitalize (first : rest) = toUpper first : rest

renderInclude :: FilePath -> String
renderInclude path = "#include \"" <> concatMap escape path <> "\""
  where
    escape '"' = "\\\""
    escape '\\' = "\\\\"
    escape character = [character]

renderPrototype :: ForeignBinding -> String
renderPrototype binding =
  "extern " <> cType (foreignBindingResult binding) <> " " <> foreignSymbol binding
    <> "(" <> intercalate ", " ("uw_context" : map cType (foreignBindingDomains binding)) <> ");"

renderWrapper :: ForeignBinding -> [String]
renderWrapper binding =
  [ "static napi_value vr_ffi_call_" <> identifier <> "(napi_env env, vr_napi_context *context, napi_value arguments) {"
  , "  if (!vr_napi_expect_arity(env, arguments, " <> show (length domains) <> ")) return NULL;"
  ]
    <> concat (zipWith renderArgument [0 :: Int ..] domains)
    <> renderCall binding
    <> ["}", ""]
  where
    identifier = show (foreignBindingId binding)
    domains = foreignBindingDomains binding

renderArgument :: Int -> M.Type -> [String]
renderArgument index typ = case abiType typ of
  Just AbiInt -> converted "uw_Basis_int" "vr_napi_get_int" ""
  Just AbiFloat -> converted "uw_Basis_float" "vr_napi_get_float" ""
  Just AbiBool -> converted "uw_Basis_bool" "vr_napi_get_bool" ""
  Just AbiChar -> converted "uw_Basis_char" "vr_napi_get_char" ""
  Just AbiString -> converted "uw_Basis_string" "vr_napi_get_string" ""
  Just AbiTime -> converted "uw_Basis_time" "vr_napi_get_time" ""
  Just AbiBlob -> converted "uw_Basis_blob" "vr_napi_get_blob" ""
  Just AbiFile -> converted "uw_Basis_file" "vr_napi_get_file" ""
  Just AbiPostBody -> converted "uw_Basis_postBody" "vr_napi_get_post_body" ""
  Just AbiClient -> converted "uw_Basis_client" "vr_napi_get_client" ""
  Just AbiChannel -> converted "uw_Basis_channel" "vr_napi_get_channel" ""
  Just AbiUnit ->
    [ "  uw_Basis_unit " <> name <> " = 0;"
    , "  if (!vr_napi_get_unit(env, arguments, " <> show index <> ")) return NULL;"
    ]
  Just (AbiOpaque moduleName typeName) ->
    [ "  void *" <> name <> "_raw = NULL;"
    , "  if (!vr_napi_get_opaque(env, arguments, " <> show index <> ", \""
        <> cString (moduleName <> "." <> typeName) <> "\", &" <> name <> "_raw)) return NULL;"
    , "  " <> cType typ <> " " <> name <> " = *(" <> cType typ <> " *)" <> name <> "_raw;"
    ]
  Nothing -> []
  where
    name = "vr_arg_" <> show index
    converted typName helper suffix =
      [ "  " <> typName <> " " <> name <> suffix <> ";"
      , "  if (!" <> helper <> "(env, context, arguments, " <> show index <> ", &"
          <> name <> suffix <> ")) return NULL;"
      ]

renderCall :: ForeignBinding -> [String]
renderCall binding =
  [ "  " <> cType result <> " vr_result = " <> foreignSymbol binding
      <> "((uw_context)context" <> concat [", vr_arg_" <> show index | index <- [0 .. length domains - 1]] <> ");"
  , "  " <> renderResult result
  ]
  where
    domains = foreignBindingDomains binding
    result = foreignBindingResult binding

renderResult :: M.Type -> String
renderResult typ = case abiType typ of
  Just AbiInt -> "return vr_napi_make_int(env, vr_result);"
  Just AbiFloat -> "return vr_napi_make_float(env, vr_result);"
  Just AbiBool -> "return vr_napi_make_bool(env, vr_result);"
  Just AbiChar -> "return vr_napi_make_char(env, vr_result);"
  Just AbiString -> "return vr_napi_make_string(env, vr_result);"
  Just AbiTime -> "return vr_napi_make_time(env, vr_result);"
  Just AbiBlob -> "return vr_napi_make_blob(env, vr_result);"
  Just AbiFile -> "return vr_napi_make_file(env, vr_result);"
  Just AbiPostBody -> "return vr_napi_make_post_body(env, vr_result);"
  Just AbiClient -> "return vr_napi_make_client(env, vr_result);"
  Just AbiChannel -> "return vr_napi_make_channel(env, vr_result);"
  Just AbiUnit -> "return vr_napi_make_unit(env);"
  Just (AbiOpaque moduleName typeName) ->
    cType typ <> " *vr_box = vr_napi_allocate_opaque(context, sizeof(*vr_box)); "
      <> "if (vr_box == NULL) return vr_napi_throw(env, \"Unable to allocate a foreign abstract value\"); "
      <> "*vr_box = vr_result; return vr_napi_make_opaque(env, context, \""
      <> cString (moduleName <> "." <> typeName) <> "\", vr_box);"
  Nothing -> "return vr_napi_throw(env, \"Unsupported generated foreign result\");"

cType :: M.Type -> String
cType typ = case abiType typ of
  Just AbiInt -> "uw_Basis_int"
  Just AbiFloat -> "uw_Basis_float"
  Just AbiBool -> "uw_Basis_bool"
  Just AbiChar -> "uw_Basis_char"
  Just AbiString -> "uw_Basis_string"
  Just AbiTime -> "uw_Basis_time"
  Just AbiBlob -> "uw_Basis_blob"
  Just AbiFile -> "uw_Basis_file"
  Just AbiPostBody -> "uw_Basis_postBody"
  Just AbiClient -> "uw_Basis_client"
  Just AbiChannel -> "uw_Basis_channel"
  Just AbiUnit -> "uw_Basis_unit"
  Just (AbiOpaque moduleName name) -> "uw_" <> sanitize moduleName <> "_" <> sanitize name
  Nothing -> "void *"

foreignSymbol :: ForeignBinding -> String
foreignSymbol binding =
  "uw_" <> sanitize (foreignBindingModule binding) <> "_" <> sanitize (foreignBindingMember binding)

sanitize :: String -> String
sanitize = concatMap convert
  where
    convert '\'' = "PRIME"
    convert character
      | isAscii character && (isAlphaNum character || character == '_') = [character]
      | otherwise = "_"

cString :: String -> String
cString = concatMap escape
  where
    escape '"' = "\\\""
    escape '\\' = "\\\\"
    escape '\n' = "\\n"
    escape '\r' = "\\r"
    escape '\t' = "\\t"
    escape character = [character]

directiveNames :: String -> ProjectPlan -> Set.Set Server.ForeignName
directiveNames wanted plan = Set.fromList
  [ (moduleName, member)
  | directive <- projectDirectives plan
  , projectDirectiveName directive == wanted
  , let (moduleName, suffix) = break (== '.') (projectDirectiveArgument directive)
  , '.' : member <- [suffix]
  , not (null moduleName)
  , not (null member)
  ]
