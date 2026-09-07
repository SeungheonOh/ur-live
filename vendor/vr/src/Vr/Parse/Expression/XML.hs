module Vr.Parse.Expression.XML
  ( parseRecordExpr
  , parseXmlRoot
  , emptyXml
  ) where

import Control.Monad (unless, when)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8
import {-# SOURCE #-} Vr.Parse.Expression (parseExpr)
import Vr.Parse.CSS (xmlClassExpression, xmlStyleExpression)
import Vr.Parse.Core
import Vr.Parse.Lexer
import Vr.Parse.Type
import Vr.Source
parseRecordExpr :: Parser SExpr
parseRecordExpr = do
  start <- expectText "{"
  empty <- acceptText "}"
  if empty
    then pure (Located (tokenSpan start) (SERecord [] False))
    else do
      flexible <- acceptText "..."
      if flexible
        then do
          end <- expectText "}"
          pure (Located (mergeSpans (tokenSpan start) (tokenSpan end)) (SERecord [] True))
        else do
          name <- parseRowLabel
          _ <- expectText "="
          value <- parseExpr
          (rest, isFlexible) <- parseMoreRecordExprFields
          end <- expectText "}"
          pure (Located (mergeSpans (tokenSpan start) (tokenSpan end)) (SERecord ((name, value) : rest) isFlexible))

parseMoreRecordExprFields :: Parser ([(SCon, SExpr)], Bool)
parseMoreRecordExprFields = do
  comma <- acceptText ","
  if not comma
    then pure ([], False)
    else do
      flexible <- acceptText "..."
      if flexible
        then pure ([], True)
        else do
          name <- parseRowLabel
          _ <- expectText "="
          value <- parseExpr
          (rest, isFlexible) <- parseMoreRecordExprFields
          pure ((name, value) : rest, isFlexible)

parseXmlRoot :: String -> Parser SExpr
parseXmlRoot tag = do
  start <- consumeToken
  unless (tag == "xml")
    (parseFailureAt (tokenSpan start) "xml-root" "Initial XML tag pair must both be tagged <xml>")
  fragments <- parseXmlFragments
  end <- expectXmlEnd
  let at = mergeSpans (tokenSpan start) (tokenSpan end)
  pure (foldXml at fragments)

parseXmlFragments :: Parser [SExpr]
parseXmlFragments = do
  next <- peekKind
  case next of
    Just TokenXmlEnd -> pure []
    Just (TokenEndTag _) -> pure []
    Just (TokenXmlText bytes) -> do
      token <- consumeToken
      rest <- parseXmlFragments
      pure (xmlText (tokenSpan token) bytes : rest)
    Just (TokenBeginTag tag) -> do
      fragment <- parseXmlTag tag
      (fragment :) <$> parseXmlFragments
    Just (TokenPunctuation "{") -> do
      _ <- consumeToken
      printed <- acceptText "["
      expression <- parseExpr
      when printed (expectText "]" >> pure ())
      _ <- expectText "}"
      let fragment = if printed then Located (locatedSpan expression) (SEApp (topVar (locatedSpan expression) "txt") expression) else expression
      (fragment :) <$> parseXmlFragments
    _ -> parseFailure "xml-fragment" "Unsupported or malformed XML fragment"

data XmlAttributes = XmlAttributes
  { xmlClass :: !(Maybe SExpr)
  , xmlDynamicClass :: !(Maybe SExpr)
  , xmlStyle :: !(Maybe SExpr)
  , xmlDynamicStyle :: !(Maybe SExpr)
  , xmlIdentifier :: !(Maybe SExpr)
  , xmlDataAttributes :: ![(String, String, SExpr)]
  , xmlNormalAttributes :: ![(SCon, SExpr)]
  }

emptyXmlAttributes :: XmlAttributes
emptyXmlAttributes = XmlAttributes Nothing Nothing Nothing Nothing Nothing [] []

parseXmlTag :: String -> Parser SExpr
parseXmlTag rawName = do
  start <- consumeToken
  tagHead <- parseXmlTagHead (tokenSpan start) (tagInternalName rawName)
  attributes <- parseXmlAttributes emptyXmlAttributes
  selfClosing <- acceptText "/"
  end <- expectText ">"
  let openSpan = mergeSpans (tokenSpan start) (tokenSpan end)
  if selfClosing
    then
      let content
            | tagInternalName rawName `elem` ["submit", "dyn"] = emptyXmlWithEmptyUse openSpan
            | otherwise = emptyXml openSpan
       in pure (applyXmlTag openSpan rawName tagHead attributes content)
    else do
      fragments <- parseXmlFragments
      closing <- consumeToken
      closingName <- case tokenKind closing of
        TokenEndTag name -> pure name
        _ -> parseFailureAt (tokenSpan closing) "xml-end-tag" ("Expected closing tag for <" <> rawName <> ">")
      unless (tagInternalName closingName == tagInternalName rawName) $
        parseFailureAt (tokenSpan closing) "xml-tag-mismatch" ("Begin tag <" <> rawName <> "> and end tag </" <> closingName <> "> do not match")
      let at = mergeSpans (tokenSpan start) (tokenSpan closing)
      pure (applyXmlTag at rawName tagHead attributes (foldXml at fragments))

parseXmlTagHead :: Span -> String -> Parser SExpr
parseXmlTagHead at name = go (Located at (SEVar [] name Infer))
  where
    go expression = do
      application <- acceptText "{"
      if not application
        then pure expression
        else do
          argument <- parseCon
          end <- expectText "}"
          go (Located (mergeSpans at (tokenSpan end)) (SECApp expression argument))

parseXmlAttributes :: XmlAttributes -> Parser XmlAttributes
parseXmlAttributes attributes = do
  next <- peekKind
  case next of
    Just (TokenIdentifier name) -> do
      token <- consumeToken
      hasValue <- acceptText "="
      value <- if hasValue then parseXmlAttributeValue else pure (basisVar (tokenSpan token) "True")
      let at = mergeSpans (tokenSpan token) (locatedSpan value)
          literalBless function expression = case locatedValue expression of
            SEPrim {} -> Located at (SEApp (basisVar at function) expression)
            _ -> expression
          normalName = xmlAttributeName name
          normalValue
            | normalName `elem` ["Href", "Src"] = literalBless "bless" value
            | normalName == "Nam" = literalBless "blessMeta" value
            | otherwise = value
          updated = case name of
            "class" -> attributes {xmlClass = Just value}
            "dynClass" -> attributes {xmlDynamicClass = Just value}
            "style" -> attributes {xmlStyle = Just value}
            "dynStyle" -> attributes {xmlDynamicStyle = Just value}
            _ | Just suffix <- stripXmlPrefix "data-" name -> attributes {xmlDataAttributes = xmlDataAttributes attributes <> [("data", suffix, value)]}
              | Just suffix <- stripXmlPrefix "aria-" name -> attributes {xmlDataAttributes = xmlDataAttributes attributes <> [("aria", suffix, value)]}
              | otherwise ->
                  let field = Located (tokenSpan token) (SCName normalName)
                   in attributes
                        { xmlIdentifier = if normalName == "Id" then Just normalValue else xmlIdentifier attributes
                        , xmlNormalAttributes = xmlNormalAttributes attributes <> [(field, normalValue)]
                        }
      parseXmlAttributes updated
    _ -> pure attributes

parseXmlAttributeValue :: Parser SExpr
parseXmlAttributeValue = do
  next <- peekKind
  case next of
    Just (TokenInt value) -> primitive (PrimInt value)
    Just (TokenFloat value) -> primitive (PrimFloat value)
    Just (TokenString value) -> primitive (PrimString NormalString value)
    Just (TokenPunctuation "{") -> do
      _ <- consumeToken
      expression <- parseExpr
      _ <- expectText "}"
      pure expression
    _ -> parseFailure "xml-attribute" "Expected an XML attribute value"
  where
    primitive value = do
      token <- consumeToken
      pure (Located (tokenSpan token) (SEPrim value))

applyXmlTag :: Span -> String -> SExpr -> XmlAttributes -> SExpr -> SExpr
applyXmlTag at rawName tagHead attributes content
  | internal == "form" = applyMany at (basisVar at "form") [optionalExpression at (xmlIdentifier attributes), optionalExpression at (fmap (xmlClassExpression at) (xmlClass attributes)), content]
  | internal `elem` ["subform", "subforms"] = Located at (SEApp tagHead content)
  | internal == "entry" = Located at (SEApp (basisVar at "entry") content)
  | otherwise = Located at (SEApp assembled content)
  where
    internal = tagInternalName rawName
    classExpression = maybe (basisVar at "null") (xmlClassExpression at) (xmlClass attributes)
    dynamicClass = optionalExpression at (xmlDynamicClass attributes)
    styleExpression = maybe (basisVar at "noStyle") (xmlStyleExpression at) (xmlStyle attributes)
    dynamicStyle = optionalExpression at (xmlDynamicStyle attributes)
    dataFields = case xmlDataAttributes attributes of
      [] -> []
      first : rest ->
        let one (kind, name, value) = applyMany at (basisVar at "data_attr") [basisVar at (kind <> "_kind"), Located at (SEPrim (PrimString NormalString (B8.pack name))), value]
            combined = foldl' (\left right -> applyMany at (basisVar at "data_attrs") [left, one right]) (one first) rest
         in [(Located at (SCName "Data"), combined)]
    attributeRecord = Located at (SERecord (dataFields <> xmlNormalAttributes attributes) False)
    tagValue = Located at (SEApp tagHead (Located at (SERecord [] False)))
    assembled = applyMany at (basisVar at "tag") [classExpression, dynamicClass, styleExpression, dynamicStyle, attributeRecord, tagValue]

optionalExpression :: Span -> Maybe SExpr -> SExpr
optionalExpression at = maybe (basisVar at "None") (\value -> Located at (SEApp (basisVar at "Some") value))

xmlAttributeName :: String -> String
xmlAttributeName name = case name of
  "type" -> "Typ"
  "name" -> "Nam"
  _ -> capitalize (map (\character -> if character == '-' then '_' else character) name)

tagInternalName :: String -> String
tagInternalName name = case name of
  "table" -> "tabl"
  "url" -> "url_"
  "datetime-local" -> "datetime_local"
  "cdatetime-local" -> "cdatetime_local"
  _ -> name

stripXmlPrefix :: String -> String -> Maybe String
stripXmlPrefix prefix value
  | take (length prefix) value == prefix = Just (drop (length prefix) value)
  | otherwise = Nothing

foldXml :: Span -> [SExpr] -> SExpr
foldXml at [] = emptyXml at
foldXml _ [fragment] = fragment
foldXml at (fragment : rest) = Located at (SEApp (Located at (SEApp (basisVar at "join") fragment)) (foldXml at rest))

xmlText :: Span -> BS.ByteString -> SExpr
xmlText at bytes = Located at (SEApp (basisVar at "cdata") (Located at (SEPrim (PrimString HtmlString bytes))))

emptyXml :: Span -> SExpr
emptyXml at = xmlText at BS.empty

-- Submit and dynamic tags consume the surrounding form-use row themselves.
-- Ur/Web's surface translation therefore fixes their empty child to have an
-- empty use row instead of allowing normal implicit-argument inference to
-- assign that row to the child.
emptyXmlWithEmptyUse :: Span -> SExpr
emptyXmlWithEmptyUse at =
  let cdata = Located at (SEVar ["Basis"] "cdata" DontInfer)
      context = Located at (SCWild (Located at SKWild))
      use = Located at (SCRecord [])
      specialized = Located at (SECApp (Located at (SECApp cdata context)) use)
   in Located at (SEApp specialized (Located at (SEPrim (PrimString HtmlString BS.empty))))
