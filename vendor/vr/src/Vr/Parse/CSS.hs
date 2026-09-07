module Vr.Parse.CSS
  ( desugarSpecialApplication
  , xmlClassExpression
  , xmlStyleExpression
  ) where

import qualified Data.ByteString.Char8 as B8
import Data.Char (isSpace)
import Vr.Parse.Core (applyMany, basisVar)
import Vr.Source

-- Ur/Web represents classes and styles as abstract source types, but literal
-- CLASS/STYLE applications are syntax whose components are checked by Basis
-- constructors. XML attributes and explicit uppercase applications must use
-- this same path.
desugarSpecialApplication :: SExpr -> SExpr
desugarSpecialApplication expression = case locatedValue expression of
  SEApp function argument
    | SEVar [] "STYLE" _ <- locatedValue function
    , SEPrim (PrimString _ bytes) <- locatedValue argument -> styleLiteral at bytes
    | SEVar [] "CLASS" _ <- locatedValue function
    , SEPrim (PrimString _ bytes) <- locatedValue argument -> classLiteral at bytes
  _ -> expression
  where
    at = locatedSpan expression

xmlClassExpression :: Span -> SExpr -> SExpr
xmlClassExpression at expression = case locatedValue expression of
  SEPrim (PrimString _ bytes) -> classLiteral at bytes
  _ -> expression

xmlStyleExpression :: Span -> SExpr -> SExpr
xmlStyleExpression at expression = case locatedValue expression of
  SEPrim (PrimString _ bytes) -> styleLiteral at bytes
  _ -> expression

classLiteral :: Span -> B8.ByteString -> SExpr
classLiteral at bytes = case words (B8.unpack bytes) of
  [] -> basisVar at "null"
  first : rest -> foldl' combine (className first) rest
  where
    combine classes name = applyMany at (basisVar at "classes") [classes, className name]
    className name = Located at (SEVar [] (map normalize (if name == "table" then "tabl" else name)) Infer)
    normalize '-' = '_'
    normalize character = character

styleLiteral :: Span -> B8.ByteString -> SExpr
styleLiteral at bytes = foldl' addProperty (basisVar at "noStyle") properties
  where
    properties = filter (not . null) (splitOnChar ';' (B8.unpack bytes))
    addProperty style source = case break (== ':') source of
      (name, ':' : values) ->
        let property = applyMany at (basisVar at "property") [stringValue (dropWhile isSpace name)]
            withValues = foldl' (\current value -> applyMany at (basisVar at "value") [current, cssValue value]) property (words values)
         in applyMany at (basisVar at "oneProperty") [style, withValues]
      _ -> applyMany at (basisVar at "oneProperty") [style, stringValue ""]
    cssValue value
      | length value >= 5
      , take 4 value == "url("
      , last value == ')' =
          let raw = init (drop 4 value)
              url = stripCssQuotes raw
           in applyMany at (basisVar at "css_url")
                [applyMany at (basisVar at "bless") [stringValue url]]
      | otherwise = applyMany at (basisVar at "atom") [stringValue value]
    stringValue value = Located at (SEPrim (PrimString NormalString (B8.pack value)))

stripCssQuotes :: String -> String
stripCssQuotes raw = case raw of
  quote : rest | quote == '"' || quote == '\'' -> case reverse rest of
    closing : reversed | closing == quote -> reverse reversed
    _ -> raw
  _ -> raw

splitOnChar :: Char -> String -> [String]
splitOnChar separator = foldr step [[]]
  where
    step character groups@(group : rest)
      | character == separator = [] : groups
      | otherwise = (character : group) : rest
    step _ [] = []
