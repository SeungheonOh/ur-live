module Vr.Parse.Declaration
  ( parseDeclarationsUntil
  , parseSignatureItemsUntil
  ) where

import Control.Monad (when)
import qualified Data.ByteString.Char8 as B8
import Vr.Parse.Core
import Vr.Parse.Expression
import Vr.Parse.Expression.SQL
import Vr.Parse.Lexer
import Vr.Parse.Pattern
import Vr.Parse.Type
import Vr.Source
parseDeclarationsUntil :: [String] -> Parser [SDecl]
parseDeclarationsUntil terminators = do
  stopped <- atAny terminators
  done <- atEOF
  if stopped || done
    then pure []
    else do
      declarations <- parseDeclaration
      rest <- parseDeclarationsUntil terminators
      pure (declarations <> rest)

parseDeclaration :: Parser [SDecl]
parseDeclaration = do
  next <- peekText
  case next of
    Just "con" -> (: []) <$> parseConDeclaration False
    Just "type" -> (: []) <$> parseConDeclaration True
    Just "datatype" -> (: []) <$> parseDatatypeDeclaration
    Just "val" -> (: []) <$> parseValueDeclaration
    Just "fun" -> (: []) <$> parseFunctionDeclaration
    Just "signature" -> (: []) <$> parseSignatureDeclaration
    Just "structure" -> (: []) <$> parseStructureDeclaration
    Just "functor" -> (: []) <$> parseFunctorDeclaration
    Just "open" -> parseOpenDeclaration
    Just "constraint" -> (: []) <$> parseConstraintDeclaration
    Just "export" -> (: []) <$> parseExportDeclaration
    Just "table" -> (: []) <$> parseTableDeclaration
    Just "ensure_index" -> (: []) <$> parseIndexDeclaration
    Just "sequence" -> (: []) <$> parseSequenceDeclaration
    Just "view" -> (: []) <$> parseViewDeclaration
    Just "cookie" -> (: []) <$> parseCookieDeclaration
    Just "style" -> (: []) <$> parseStyleDeclaration
    Just "task" -> (: []) <$> parseTaskDeclaration
    Just "policy" -> (: []) <$> parsePolicyDeclaration
    Just "ffi" -> (: []) <$> parseFfiDeclaration
    _ -> parseFailure "declaration" "Expected a declaration"

parseConDeclaration :: Bool -> Parser SDecl
parseConDeclaration isType = do
  start <- expectText (if isType then "type" else "con")
  (name, _) <- expectIdentifier
  binders <- parseConDeclarationBinders
  kind <- if isType then pure Nothing else parseOptionalKind
  _ <- expectText "="
  body <- parseCon
  let at = mergeSpans (tokenSpan start) (locatedSpan body)
      baseKind = maybe (Located at SKWild) id kind
      (wrappedBody, wrappedKind) = foldr (wrapConBinder at) (body, baseKind) binders
  pure (Located at (SDCon name (Just wrappedKind) wrappedBody))

parseConDeclarationBinders :: Parser [ConBinder]
parseConDeclarationBinders = do
  next <- peekKind
  following <- peekKindN 1
  case (next, following) of
    (Just (TokenIdentifier name), Just (TokenPunctuation punctuation'))
      | punctuation' `elem` ["::", "::_", ":::", ":::_"] -> do
          _ <- consumeToken
          binder <- parseConBinderAfterName name
          (binder :) <$> parseConDeclarationBinders
    (Just (TokenIdentifier name), _) -> do
      _ <- consumeToken
      (ConBinder name Nothing :) <$> parseConDeclarationBinders
    (Just (TokenPunctuation "_"), _) -> do
      _ <- consumeToken
      (ConBinder "_" Nothing :) <$> parseConDeclarationBinders
    (Just (TokenPunctuation "("), Just (TokenIdentifier _)) -> do
      _ <- consumeToken
      group <- parseConBinderGroup
      _ <- expectText ")"
      rest <- parseConDeclarationBinders
      pure (ConTupleBinder group : rest)
    _ -> pure []

parseConBinderGroup :: Parser [ConBinder]
parseConBinderGroup = do
  (name, _) <- expectIdentifier
  kind <- parseOptionalKind
  let binder = ConBinder name kind
  more <- acceptText ","
  if more then (binder :) <$> parseConBinderGroup else pure [binder]

parseConBinderAfterName :: String -> Parser ConBinder
parseConBinderAfterName name = do
  punctuation' <- expectOneOf ["::", "::_", ":::", ":::_"]
  if tokenText punctuation' `elem` [Just "::_", Just ":::_"]
    then pure (ConBinder name Nothing)
    else ConBinder name . Just <$> parseKind

parseDatatypeDeclaration :: Parser SDecl
parseDatatypeDeclaration = do
  start <- expectText "datatype"
  first <- parseDatatypeDefinition
  case first of
    DatatypeImported name modules importedName endAt ->
      pure (Located (mergeSpans (tokenSpan start) endAt) (SDDatatypeImp name modules importedName))
    DatatypeDefined definition _ -> do
      rest <- parseSeparated "and" parseDefinedDatatype
      let definitions = definition : map fst rest
          endAt = maybe (datatypeDefinitionSpan first) snd (lastMaybe rest)
      pure (Located (mergeSpans (tokenSpan start) endAt) (SDDatatype definitions))
  where
    parseDefinedDatatype = do
      definition <- parseDatatypeDefinition
      case definition of
        DatatypeDefined value at -> pure (value, at)
        DatatypeImported _ _ _ at -> parseFailureAt at "datatype-import" "Imported datatype cannot appear after 'and'"

data DatatypeDefinition
  = DatatypeDefined !(String, [String], [(String, Maybe SCon)]) !Span
  | DatatypeImported !String ![String] !String !Span

datatypeDefinitionSpan :: DatatypeDefinition -> Span
datatypeDefinitionSpan definition = case definition of
  DatatypeDefined _ at -> at
  DatatypeImported _ _ _ at -> at

parseDatatypeDefinition :: Parser DatatypeDefinition
parseDatatypeDefinition = do
  (name, nameToken) <- expectIdentifier
  arguments <- parseWhileIdentifier
  _ <- expectText "="
  imported <- acceptText "datatype"
  if imported
    then do
      -- Datatype replication is rooted at a structure but its final type
      -- component is conventionally lowercase (for example Basis.list).
      path <- parseValuePath
      let at = mergeSpans (tokenSpan nameToken) (pathSpan path)
      if null arguments
        then case reverse (pathPieces path) of
          importedName : reversedModules -> pure (DatatypeImported name (reverse reversedModules) importedName at)
          [] -> parseFailureAt at "datatype-import" "Empty imported datatype path"
        else parseFailureAt at "datatype-import" "Arguments specified for imported datatype"
    else do
      _ <- acceptText "|"
      firstConstructor <- parseDatatypeConstructor
      restConstructors <- parseSeparated "|" parseDatatypeConstructor
      let constructors = firstConstructor : restConstructors
          at = mergeSpans (tokenSpan nameToken) (snd (last constructors))
      pure (DatatypeDefined (name, arguments, map fst constructors) at)

parseDatatypeConstructor :: Parser ((String, Maybe SCon), Span)
parseDatatypeConstructor = do
  (name, token) <- expectConstructor
  hasPayload <- acceptText "of"
  if hasPayload
    then do
      payload <- parseCon
      pure ((name, Just payload), mergeSpans (tokenSpan token) (locatedSpan payload))
    else pure ((name, Nothing), tokenSpan token)

parseValueDeclaration :: Parser SDecl
parseValueDeclaration = do
  start <- expectText "val"
  recursive <- acceptText "rec"
  if recursive
    then do
      definitions <- parseValueDefinitions
      let endAt = expressionSpanOfDefinition (last definitions)
      pure (Located (mergeSpans (tokenSpan start) endAt) (SDValRec definitions))
    else do
      pattern' <- parsePattern
      arguments <- parseValueArguments
      resultType <- parseOptionalTypeAnnotation
      _ <- expectText "="
      body <- parseExpr
      let at = mergeSpans (tokenSpan start) (locatedSpan body)
          wrapped = foldr (wrapLambdaArgument at) body arguments
          finalPattern = case resultType of
            Nothing -> pattern'
            Just annotation -> Located at (SPAnnot pattern' (foldr (lambdaArgumentType at) annotation arguments))
      pure (Located at (SDVal finalPattern wrapped))

parseFunctionDeclaration :: Parser SDecl
parseFunctionDeclaration = do
  start <- expectText "fun"
  definitions <- parseValueDefinitions
  let endAt = expressionSpanOfDefinition (last definitions)
  pure (Located (mergeSpans (tokenSpan start) endAt) (SDValRec definitions))

parseSignatureDeclaration :: Parser SDecl
parseSignatureDeclaration = do
  start <- expectText "signature"
  (name, _) <- expectConstructor
  _ <- expectText "="
  signature <- parseSgn
  pure (Located (mergeSpans (tokenSpan start) (locatedSpan signature)) (SDSgn name signature))

parseStructureDeclaration :: Parser SDecl
parseStructureDeclaration = do
  start <- expectText "structure"
  (name, _) <- expectConstructor
  ascription <- ifM (acceptText ":") (Just <$> parseSgn) (pure Nothing)
  _ <- expectText "="
  structure <- parseStructure
  pure (Located (mergeSpans (tokenSpan start) (locatedSpan structure)) (SDStr name ascription Nothing structure False))

parseFunctorDeclaration :: Parser SDecl
parseFunctorDeclaration = do
  start <- expectText "functor"
  (name, _) <- expectConstructor
  _ <- expectText "("
  (parameter, _) <- expectConstructor
  _ <- expectText ":"
  domain <- parseSgn
  _ <- expectText ")"
  result <- ifM (acceptText ":") (Just <$> parseSgn) (pure Nothing)
  _ <- expectText "="
  body <- parseStructure
  let at = mergeSpans (tokenSpan start) (locatedSpan body)
      functorBody = Located at (SStrFun parameter domain result body)
  pure (Located at (SDStr name Nothing Nothing functorBody False))

parseOpenDeclaration :: Parser [SDecl]
parseOpenDeclaration = do
  start <- expectText "open"
  constraints <- acceptText "constraints"
  path <- parseModulePath
  let at = mergeSpans (tokenSpan start) (pathSpan path)
      pieces = pathPieces path
  case pieces of
    [] -> parseFailureAt at "module-path" "Empty module path"
    first : rest ->
      if constraints
        then pure [Located at (SDOpenConstraints first rest)]
        else do
          application <- acceptText "("
          if application
            then do
              argument <- parseStructure
              end <- expectText ")"
              let functorStructure = pathToStructure path
                  appAt = mergeSpans at (tokenSpan end)
                  anonymous = Located appAt (SStrApp functorStructure argument)
              pure [Located appAt (SDStr "anon" Nothing Nothing anonymous False), Located appAt (SDOpen "anon" [])]
            else pure [Located at (SDOpen first rest)]

parseConstraintDeclaration :: Parser SDecl
parseConstraintDeclaration = do
  start <- expectText "constraint"
  left <- parseConTerm
  _ <- expectText "~"
  right <- parseConTerm
  pure (Located (mergeSpans (tokenSpan start) (locatedSpan right)) (SDConstraint left right))

parseExportDeclaration :: Parser SDecl
parseExportDeclaration = do
  start <- expectText "export"
  structure <- parseStructurePath
  pure (Located (mergeSpans (tokenSpan start) (locatedSpan structure)) (SDExport structure))

parseTableDeclaration :: Parser SDecl
parseTableDeclaration = do
  start <- expectText "table"
  (name, _) <- expectIdentifier
  _ <- expectText ":"
  rowType <- parseConTerm
  primary <- parsePrimaryKey (locatedSpan rowType)
  _ <- acceptText ","
  constraints <- parseTableConstraints (locatedSpan rowType)
  let endAt = locatedSpan constraints
      at = mergeSpans (tokenSpan start) endAt
  pure (Located at (SDTable name (entable rowType) primary constraints))

parsePrimaryKey :: Span -> Parser SExpr
parsePrimaryKey at = do
  present <- acceptText "PRIMARY"
  if not present
    then pure (basisVar at "no_primary_key")
    else do
      _ <- expectText "KEY"
      supplied <- atText "{"
      if supplied
        then do
          _ <- expectText "{"
          _ <- expectText "{"
          expression <- parseExpr
          _ <- expectText "}"
          _ <- expectText "}"
          pure expression
        else do
          names <- parseSchemaNames
          case names of
            [] -> parseFailure "primary-key" "A primary key must name at least one field"
            first : rest -> do
              let restRow = Located at (SCRecord [(name, Located at (SCWild (Located at SKType))) | name <- rest])
                  head1 = Located at (SECApp (Located at (SECApp (Located at (SEVar ["Basis"] "primary_key" TypesOnly)) first)) restRow)
                  constrained = Located at (SEDisjointApp (Located at (SEDisjointApp head1)))
                  witness = Located at (SERecord [(name, Located at SEWild) | name <- first : rest] False)
              pure (Located at (SEApp constrained witness))

parseTableConstraints :: Span -> Parser SExpr
parseTableConstraints at = do
  present <- atText "CONSTRAINT"
  if not present
    then pure (basisVar at "no_constraint")
    else do
      first <- parseTableConstraint
      rest <- parseMore
      pure (foldl' (\left right -> applyMany at (basisVar at "join_constraints") [left, right]) first rest)
  where
    parseMore = do
      comma <- acceptText ","
      if not comma
        then pure []
        else do
          next <- atText "CONSTRAINT"
          if next then (:) <$> parseTableConstraint <*> parseMore else pure []

parseTableConstraint :: Parser SExpr
parseTableConstraint = do
  start <- expectText "CONSTRAINT"
  name <- parseSqlFieldIdentifier
  body <- parseTableConstraintBody
  let at = mergeSpans (tokenSpan start) (locatedSpan body)
      headExpression = Located at (SECApp (basisVar at "one_constraint") name)
  pure (Located at (SEApp headExpression body))

parseTableConstraintBody :: Parser SExpr
parseTableConstraintBody = do
  next <- peekText
  case next of
    Just "UNIQUE" -> do
      start <- expectText "UNIQUE"
      names <- parseSchemaNames
      case names of
        [] -> parseFailure "unique-constraint" "A unique constraint must name at least one field"
        first : rest -> do
          let at = mergeSpans (tokenSpan start) (locatedSpan (last names))
              restRow = Located at (SCRecord [(name, Located at (SCWild (Located at SKType))) | name <- rest])
          pure (Located at (SECApp (Located at (SECApp (basisVar at "unique") first)) restRow))
    Just "CHECK" -> do
      start <- expectText "CHECK"
      expression <- parseSqlExpr
      let at = mergeSpans (tokenSpan start) (locatedSpan expression)
      pure (Located at (SEApp (basisVar at "check") expression))
    Just "FOREIGN" -> parseForeignKey
    Just "{" -> do
      _ <- expectText "{"
      expression <- parseExpr
      _ <- expectText "}"
      pure expression
    _ -> parseFailure "table-constraint" "Expected UNIQUE, CHECK, or FOREIGN KEY"

parseForeignKey :: Parser SExpr
parseForeignKey = do
  start <- expectText "FOREIGN"
  _ <- expectText "KEY"
  mine <- parseSchemaNames
  _ <- expectText "REFERENCES"
  foreignTable <- parseSqlDmlTable
  _ <- expectText "("
  foreignNames <- parseSchemaNameList
  _ <- expectText ")"
  modes <- parsePropagationModes
  when (length mine /= length foreignNames) (parseFailureAt (tokenSpan start) "foreign-key-arity" "Foreign-key field lists have different lengths")
  let at = foldSpans (tokenSpan start) (locatedSpan foreignTable : map locatedSpan foreignNames)
      matching = foldr (\(left, right) rest -> Located at (SEApp (Located at (SECApp (Located at (SECApp (basisVar at "mat_cons") left)) right)) rest)) (basisVar at "mat_nil") (zip mine foreignNames)
      rule kind = maybe (basisVar at "no_action") id (lookup kind modes)
      modeRecord = recordExpr at [("OnDelete", rule "DELETE"), ("OnUpdate", rule "UPDATE")]
  pure (applyMany at (basisVar at "foreign_key") [matching, foreignTable, modeRecord])

parsePropagationModes :: Parser [(String, SExpr)]
parsePropagationModes = do
  present <- acceptText "ON"
  if not present
    then pure []
    else do
      kind <- expectOneOf ["DELETE", "UPDATE"]
      rule <- parsePropagationRule
      rest <- parsePropagationModes
      pure ((maybe "" id (tokenText kind), rule) : rest)

parsePropagationRule :: Parser SExpr
parsePropagationRule = do
  next <- peekText
  case next of
    Just "NO" -> do
      start <- expectText "NO"
      end <- expectText "ACTION"
      pure (basisVar (mergeSpans (tokenSpan start) (tokenSpan end)) "no_action")
    Just "RESTRICT" -> variable "RESTRICT" "restrict"
    Just "CASCADE" -> variable "CASCADE" "cascade"
    Just "SET" -> do
      start <- expectText "SET"
      end <- expectText "NULL"
      pure (basisVar (mergeSpans (tokenSpan start) (tokenSpan end)) "set_null")
    _ -> parseFailure "propagation-rule" "Expected NO ACTION, RESTRICT, CASCADE, or SET NULL"
  where
    variable keyword name = do
      token <- expectText keyword
      pure (basisVar (tokenSpan token) name)

parseSchemaNames :: Parser [SCon]
parseSchemaNames = do
  grouped <- acceptText "("
  if grouped
    then do
      names <- parseSchemaNameList
      _ <- expectText ")"
      pure names
    else (: []) <$> parseSqlFieldIdentifier

parseSchemaNameList :: Parser [SCon]
parseSchemaNameList = do
  first <- parseSqlFieldIdentifier
  rest <- parseSeparated "," parseSqlFieldIdentifier
  pure (first : rest)

parseIndexDeclaration :: Parser SDecl
parseIndexDeclaration = do
  start <- expectText "ensure_index"
  table <- parseExprTerm
  _ <- expectText ":"
  modes <- parseExprTerm
  included <- ifM (acceptText "in") (Just <$> parseConTerm) (pure Nothing)
  let endAt = maybe (locatedSpan modes) locatedSpan included
  pure (Located (mergeSpans (tokenSpan start) endAt) (SDIndex table modes included))

parseSequenceDeclaration :: Parser SDecl
parseSequenceDeclaration = do
  start <- expectText "sequence"
  (name, token) <- expectIdentifier
  pure (Located (mergeSpans (tokenSpan start) (tokenSpan token)) (SDSequence name))

parseViewDeclaration :: Parser SDecl
parseViewDeclaration = do
  start <- expectText "view"
  (name, _) <- expectIdentifier
  _ <- expectText "="
  braced <- acceptText "{"
  expression <- if braced
    then parseExpr <* expectText "}"
    else parseSqlQuery
  pure (Located (mergeSpans (tokenSpan start) (locatedSpan expression)) (SDView name expression))

parseCookieDeclaration :: Parser SDecl
parseCookieDeclaration = do
  start <- expectText "cookie"
  (name, _) <- expectIdentifier
  _ <- expectText ":"
  valueType <- parseCon
  pure (Located (mergeSpans (tokenSpan start) (locatedSpan valueType)) (SDCookie name valueType))

parseStyleDeclaration :: Parser SDecl
parseStyleDeclaration = do
  start <- expectText "style"
  (name, token) <- expectIdentifier
  pure (Located (mergeSpans (tokenSpan start) (tokenSpan token)) (SDStyle name))

parseTaskDeclaration :: Parser SDecl
parseTaskDeclaration = do
  start <- expectText "task"
  schedule <- parseExprApplications
  _ <- expectText "="
  body <- parseExpr
  pure (Located (mergeSpans (tokenSpan start) (locatedSpan body)) (SDTask schedule body))

parsePolicyDeclaration :: Parser SDecl
parsePolicyDeclaration = do
  start <- expectText "policy"
  policy <- parseExpr
  pure (Located (mergeSpans (tokenSpan start) (locatedSpan policy)) (SDPolicy policy))

parseFfiDeclaration :: Parser SDecl
parseFfiDeclaration = do
  start <- expectText "ffi"
  (name, _) <- expectIdentifier
  modes <- parseFfiModes
  _ <- expectText ":"
  valueType <- parseCon
  pure (Located (mergeSpans (tokenSpan start) (locatedSpan valueType)) (SDFfi name modes valueType))

parseFfiModes :: Parser [SFfiMode]
parseFfiModes = do
  next <- peekKind
  case next of
    Just (TokenIdentifier "effectful") -> consumeToken *> ((FfiEffectful :) <$> parseFfiModes)
    Just (TokenIdentifier "benignEffectful") -> consumeToken *> ((FfiBenignEffectful :) <$> parseFfiModes)
    Just (TokenIdentifier "clientOnly") -> consumeToken *> ((FfiClientOnly :) <$> parseFfiModes)
    Just (TokenIdentifier "serverOnly") -> consumeToken *> ((FfiServerOnly :) <$> parseFfiModes)
    Just (TokenIdentifier "jsFunc") -> do
      _ <- consumeToken
      (javascriptName, _) <- expectString
      (FfiJsFunc (B8.unpack javascriptName) :) <$> parseFfiModes
    _ -> pure []

parseSgn :: Parser SSignature
parseSgn = do
  next <- peekText
  base <- case next of
    Just "sig" -> do
      start <- expectText "sig"
      items <- parseSignatureItemsUntil ["end"]
      end <- expectText "end"
      pure (Located (mergeSpans (tokenSpan start) (tokenSpan end)) (SSigConst items))
    Just "functor" -> do
      start <- expectText "functor"
      _ <- expectText "("
      (parameter, _) <- expectConstructor
      _ <- expectText ":"
      domain <- parseSgn
      _ <- expectText ")"
      _ <- expectText ":"
      range <- parseSgn
      pure (Located (mergeSpans (tokenSpan start) (locatedSpan range)) (SSigFun parameter domain range))
    Just "(" -> do
      start <- expectText "("
      inner <- parseSgn
      end <- expectText ")"
      pure inner {locatedSpan = mergeSpans (tokenSpan start) (tokenSpan end)}
    _ -> parseSignaturePath
  parseWhereConstraints base

parseWhereConstraints :: SSignature -> Parser SSignature
parseWhereConstraints signature = do
  hasWhere <- acceptText "where"
  if not hasWhere
    then pure signature
    else do
      kind <- expectOneOf ["con", "type"]
      path <- parseValuePath
      _ <- expectText "="
      constructor <- parseCon
      let pieces = pathPieces path
          at = mergeSpans (locatedSpan signature) (locatedSpan constructor)
      case reverse pieces of
        [] -> parseFailureAt (tokenSpan kind) "where-path" "Empty where-constructor path"
        name : reversedModules -> parseWhereConstraints (Located at (SSigWhere signature (reverse reversedModules) name constructor))

parseSignaturePath :: Parser SSignature
parseSignaturePath = do
  path <- parseModulePath
  case pathPieces path of
    [name] -> pure (Located (pathSpan path) (SSigVar name))
    first : rest -> case reverse rest of
      [] -> pure (Located (pathSpan path) (SSigVar first))
      name : reversedMiddle -> pure (Located (pathSpan path) (SSigProj first (reverse reversedMiddle) name))
    [] -> parseFailureAt (pathSpan path) "signature-path" "Empty signature path"

parseSignatureItemsUntil :: [String] -> Parser [SSigItem]
parseSignatureItemsUntil terminators = do
  stopped <- atAny terminators
  done <- atEOF
  if stopped || done
    then pure []
    else do
      item <- parseSignatureItem
      rest <- parseSignatureItemsUntil terminators
      pure (item : rest)

parseSignatureItem :: Parser SSigItem
parseSignatureItem = do
  next <- peekText
  case next of
    Just "type" -> parseSignatureCon True
    Just "con" -> parseSignatureCon False
    Just "datatype" -> parseSignatureDatatype
    Just "val" -> parseSignatureValue
    Just "structure" -> parseSignatureStructure
    Just "signature" -> parseNestedSignature
    Just "functor" -> parseSignatureFunctor
    Just "include" -> parseSignatureInclude
    Just "constraint" -> parseSignatureConstraint
    Just "table" -> parseSignatureTable
    Just "sequence" -> parseSignatureSequence
    Just "view" -> parseSignatureView
    Just "class" -> parseSignatureClass
    Just "cookie" -> parseSignatureCookie
    Just "style" -> parseSignatureStyle
    _ -> parseFailure "signature-item" "Expected a signature item"

parseSignatureCon :: Bool -> Parser SSigItem
parseSignatureCon isType = do
  start <- expectText (if isType then "type" else "con")
  (name, _) <- expectIdentifier
  binders <- parseConDeclarationBinders
  kind <- if isType then pure Nothing else parseOptionalKind
  definition <- ifM (acceptText "=") (Just <$> parseCon) (pure Nothing)
  let endAt = maybe (maybe (tokenSpan start) locatedSpan kind) locatedSpan definition
      at = mergeSpans (tokenSpan start) endAt
      baseKind = maybe (Located at (if isType then SKType else SKWild)) id kind
  case definition of
    Nothing ->
      let dummy = Located at SCUnit
          abstractKind = foldr (\binder result -> snd (wrapConBinder at binder (dummy, result))) baseKind binders
       in pure (Located at (SSIConAbs name abstractKind))
    Just body ->
      let (wrappedBody, wrappedKind) = foldr (wrapConBinder at) (body, baseKind) binders
       in pure (Located at (SSICon name (Just wrappedKind) wrappedBody))

parseSignatureDatatype :: Parser SSigItem
parseSignatureDatatype = do
  start <- expectText "datatype"
  first <- parseDatatypeDefinition
  case first of
    DatatypeImported name modules importedName endAt ->
      pure (Located (mergeSpans (tokenSpan start) endAt) (SSIDatatypeImp name modules importedName))
    DatatypeDefined definition _ -> do
      rest <- parseSeparated "and" parseDefinedDatatype
      let definitions = definition : map fst rest
          endAt = maybe (datatypeDefinitionSpan first) snd (lastMaybe rest)
      pure (Located (mergeSpans (tokenSpan start) endAt) (SSIDatatype definitions))
  where
    parseDefinedDatatype = do
      definition <- parseDatatypeDefinition
      case definition of
        DatatypeDefined value at -> pure (value, at)
        DatatypeImported _ _ _ at -> parseFailureAt at "datatype-import" "Imported datatype cannot appear after 'and'"

parseSignatureValue :: Parser SSigItem
parseSignatureValue = do
  start <- expectText "val"
  (name, _) <- expectIdentifier
  _ <- expectText ":"
  valueType <- parseCon
  pure (Located (mergeSpans (tokenSpan start) (locatedSpan valueType)) (SSIVal name valueType))

parseSignatureStructure :: Parser SSigItem
parseSignatureStructure = do
  start <- expectText "structure"
  (name, _) <- expectConstructor
  _ <- expectText ":"
  signature <- parseSgn
  pure (Located (mergeSpans (tokenSpan start) (locatedSpan signature)) (SSIStr name signature))

parseNestedSignature :: Parser SSigItem
parseNestedSignature = do
  start <- expectText "signature"
  (name, _) <- expectConstructor
  _ <- expectText "="
  signature <- parseSgn
  pure (Located (mergeSpans (tokenSpan start) (locatedSpan signature)) (SSISgn name signature))

parseSignatureFunctor :: Parser SSigItem
parseSignatureFunctor = do
  start <- expectText "functor"
  (name, _) <- expectConstructor
  _ <- expectText "("
  (parameter, _) <- expectConstructor
  _ <- expectText ":"
  domain <- parseSgn
  _ <- expectText ")"
  _ <- expectText ":"
  range <- parseSgn
  let at = mergeSpans (tokenSpan start) (locatedSpan range)
  pure (Located at (SSIStr name (Located at (SSigFun parameter domain range))))

parseSignatureInclude :: Parser SSigItem
parseSignatureInclude = do
  start <- expectText "include"
  signature <- parseSgn
  pure (Located (mergeSpans (tokenSpan start) (locatedSpan signature)) (SSIInclude signature))

parseSignatureConstraint :: Parser SSigItem
parseSignatureConstraint = do
  start <- expectText "constraint"
  left <- parseConTerm
  _ <- expectText "~"
  right <- parseConTerm
  pure (Located (mergeSpans (tokenSpan start) (locatedSpan right)) (SSIConstraint left right))

parseSignatureTable :: Parser SSigItem
parseSignatureTable = do
  start <- expectText "table"
  (name, _) <- expectIdentifier
  _ <- expectText ":"
  valueType <- parseConTerm
  primary <- parsePrimaryKey (locatedSpan valueType)
  _ <- acceptText ","
  constraints <- parseTableConstraints (locatedSpan valueType)
  let at = mergeSpans (tokenSpan start) (locatedSpan constraints)
  pure (Located at (SSITable name (entable valueType) primary constraints))

parseSignatureSequence :: Parser SSigItem
parseSignatureSequence = do
  start <- expectText "sequence"
  (name, token) <- expectIdentifier
  let at = mergeSpans (tokenSpan start) (tokenSpan token)
  pure (Located at (SSIVal name (Located at (SCVar ["Basis"] "sql_sequence"))))

parseSignatureView :: Parser SSigItem
parseSignatureView = do
  start <- expectText "view"
  (name, _) <- expectIdentifier
  _ <- expectText ":"
  row <- parseCon
  let at = mergeSpans (tokenSpan start) (locatedSpan row)
      viewHead = Located at (SCVar ["Basis"] "sql_view")
  pure (Located at (SSIVal name (Located at (SCApp viewHead (entable row)))))

parseSignatureClass :: Parser SSigItem
parseSignatureClass = do
  start <- expectText "class"
  (name, _) <- expectIdentifier
  next <- peekText
  case next of
    Just "::" -> do
      _ <- expectText "::"
      kind <- parseKind
      definition <- ifM (acceptText "=") (Just <$> parseCon) (pure Nothing)
      let at = mergeSpans (tokenSpan start) (maybe (locatedSpan kind) locatedSpan definition)
      pure (Located at (maybe (SSIClassAbs name kind) (SSIClass name kind) definition))
    Just "=" -> do
      _ <- expectText "="
      definition <- parseCon
      let at = mergeSpans (tokenSpan start) (locatedSpan definition)
      pure (Located at (SSIClass name (Located at SKWild) definition))
    _ -> do
      let at = mergeSpans (tokenSpan start) (tokenSpan start)
          kind = Located at (SKArrow (Located at SKType) (Located at SKType))
      pure (Located at (SSIClassAbs name kind))

parseSignatureCookie :: Parser SSigItem
parseSignatureCookie = do
  start <- expectText "cookie"
  (name, _) <- expectIdentifier
  _ <- expectText ":"
  payload <- parseCon
  let at = mergeSpans (tokenSpan start) (locatedSpan payload)
      headType = Located at (SCVar ["Basis"] "http_cookie")
  pure (Located at (SSIVal name (Located at (SCApp headType (entable payload)))))

parseSignatureStyle :: Parser SSigItem
parseSignatureStyle = do
  start <- expectText "style"
  (name, token) <- expectIdentifier
  let at = mergeSpans (tokenSpan start) (tokenSpan token)
  pure (Located at (SSIVal name (Located at (SCVar ["Basis"] "css_class"))))

parseStructure :: Parser SStructure
parseStructure = do
  next <- peekText
  case next of
    Just "struct" -> do
      start <- expectText "struct"
      declarations <- parseDeclarationsUntil ["end"]
      end <- expectText "end"
      pure (Located (mergeSpans (tokenSpan start) (tokenSpan end)) (SStrConst declarations))
    Just "functor" -> do
      start <- expectText "functor"
      _ <- expectText "("
      (parameter, _) <- expectConstructor
      _ <- expectText ":"
      domain <- parseSgn
      _ <- expectText ")"
      result <- ifM (acceptText ":") (Just <$> parseSgn) (pure Nothing)
      _ <- expectText "=>"
      body <- parseStructure
      pure (Located (mergeSpans (tokenSpan start) (locatedSpan body)) (SStrFun parameter domain result body))
    _ -> do
      function <- parseStructurePath
      applied <- acceptText "("
      if applied
        then do
          argument <- parseStructure
          end <- expectText ")"
          pure (Located (mergeSpans (locatedSpan function) (tokenSpan end)) (SStrApp function argument))
        else pure function

parseStructurePath :: Parser SStructure
parseStructurePath = pathToStructure <$> parseModulePath

pathToStructure :: ParsedPath -> SStructure
pathToStructure path = case pathPieces path of
  [] -> Located (pathSpan path) (SStrVar "")
  first : rest -> foldl' (\structure name -> Located (pathSpan path) (SStrProj structure name)) (Located (pathSpan path) (SStrVar first)) rest
