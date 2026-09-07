{-# LANGUAGE DerivingStrategies #-}

module Vr.Parse.Lexer
  ( Token (..)
  , TokenKind (..)
  , lexSource
  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8
import Data.Char (chr, ord)
import Data.Int (Int64)
import Data.List (find)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Word (Word8)
import Text.Read (readMaybe)
import Vr.Source
data Token = Token
  { tokenSpan :: !Span
  , tokenKind :: !TokenKind
  }
  deriving stock (Eq, Ord, Show)

data TokenKind
  = TokenEOF
  | TokenString !BS.ByteString
  | TokenInt !Int64
  | TokenFloat !Double
  | TokenChar !Word8
  | TokenIdentifier !String
  | TokenConstructor !String
  | TokenKeyword !String
  | TokenPunctuation !String
  | TokenUnit
  | TokenBacktickPath !String
  | TokenXmlBegin !String
  | TokenXmlBeginEnd !String
  | TokenXmlEnd
  | TokenBeginTag !String
  | TokenEndTag !String
  | TokenXmlText !BS.ByteString
  deriving stock (Eq, Ord, Show)

data LexMode = LexNormal | LexXml | LexXmlTag
  deriving stock (Eq, Show)

data BraceReturn = BraceReturn
  { braceReturnMode :: !LexMode
  , braceDepth :: !Int
  }
  deriving stock (Eq, Show)

data LexerState = LexerState
  { lexerFile :: !FilePath
  , lexerRemaining :: ![Word8]
  , lexerPosition :: !SourcePos
  , lexerLineStart :: !Int
  , lexerMode :: !LexMode
  , lexerReturns :: ![BraceReturn]
  , lexerXmlRoots :: ![String]
  , lexerTokensRev :: ![Token]
  , lexerDiagnosticsRev :: ![Diagnostic]
  }
  deriving stock (Show)

lexSource :: FilePath -> BS.ByteString -> ([Token], [Diagnostic])
lexSource file bytes =
  let start = SourcePos 0 1 0
      initial =
        LexerState
          { lexerFile = file
          , lexerRemaining = BS.unpack bytes
          , lexerPosition = start
          , lexerLineStart = 0
          , lexerMode = LexNormal
          , lexerReturns = []
          , lexerXmlRoots = []
          , lexerTokensRev = []
          , lexerDiagnosticsRev = []
          }
      final = lexLoop initial
      eof = Token (pointSpan file (lexerPosition final)) TokenEOF
   in (reverse (eof : lexerTokensRev final), reverse (lexerDiagnosticsRev final))

lexLoop :: LexerState -> LexerState
lexLoop state
  | null (lexerRemaining state) = state
  | otherwise = lexLoop $ case lexerMode state of
      LexNormal -> lexNormal state
      LexXml -> lexXml state
      LexXmlTag -> lexXmlTag state

lexNormal :: LexerState -> LexerState
lexNormal state
  | startsWith "(*" state = skipComment LexNormal state
  | startsWith "*)" state = addLexError "unbalanced-comment" "Unbalanced comments" (advanceN 2 state) state
  | Just count <- whitespacePrefix state = advanceN count state
  | startsWith "#\"" state = lexQuoted True 34 (advanceN 2 state) state
  | startsWith "\"" state = lexQuoted False 34 (advanceOne state) state
  | startsWith "'" state = lexQuoted False 39 (advanceOne state) state
  | startsWith "`" state = lexBacktick state
  | Just (tag, selfClosing, width) <- xmlRootPrefix state =
      let after = advanceN width state
          kind = if selfClosing then TokenXmlBeginEnd tag else TokenXmlBegin tag
          switched = if selfClosing then after else after {lexerMode = LexXml, lexerXmlRoots = tag : lexerXmlRoots state}
       in emitFrom state kind switched
  | Just width <- identifierPrefix state
  , width > 1
  , take 1 (lexerRemaining state) == [ascii '_']
  , take 2 (lexerRemaining state) /= map ascii "__" = lexIdentifier width state
  | Just (spelling, width) <- punctuationPrefix state = lexPunctuation spelling width state
  | Just width <- identifierPrefix state = lexIdentifier width state
  | Just (kind, width) <- numberPrefix state = emitFrom state kind (advanceN width state)
  | otherwise =
      let offending = take 1 (lexerRemaining state)
          after = advanceOne state
       in addLexError "illegal-character" ("illegal character: " <> showBytes offending) after state

lexXml :: LexerState -> LexerState
lexXml state
  | startsWith "(*" state = skipComment LexXml state
  | startsWith "<!--" state = skipXmlComment state
  | startsWith "\n" state = emitFrom state (TokenXmlText (B8.singleton '\n')) (advanceOne state)
  | Just (tag, width) <- xmlEndPrefix state =
      let after = advanceN width state
       in case lexerXmlRoots state of
            root : rest | root == tag -> emitFrom state TokenXmlEnd (after {lexerMode = LexNormal, lexerXmlRoots = rest})
            _ -> emitFrom state (TokenEndTag tag) after
  | Just (tag, width) <- beginTagPrefix state =
      emitFrom state (TokenBeginTag tag) ((advanceN width state) {lexerMode = LexXmlTag})
  | startsWith "{" state =
      let after = advanceOne state
       in emitFrom state (TokenPunctuation "{") (after {lexerMode = LexNormal, lexerReturns = BraceReturn LexXml 1 : lexerReturns state})
  | otherwise = lexXmlText state

lexXmlTag :: LexerState -> LexerState
lexXmlTag state
  | startsWith "(*" state = skipComment LexXmlTag state
  | Just count <- whitespacePrefix state = advanceN count state
  | startsWith "/" state = emitFrom state (TokenPunctuation "/") (advanceOne state)
  | startsWith ">" state = emitFrom state (TokenPunctuation ">") ((advanceOne state) {lexerMode = LexXml})
  | startsWith "=" state = emitFrom state (TokenPunctuation "=") (advanceOne state)
  | startsWith "\"" state = lexXmlQuoted (advanceOne state) state
  | startsWith "{" state =
      let after = advanceOne state
       in emitFrom state (TokenPunctuation "{") (after {lexerMode = LexNormal, lexerReturns = BraceReturn LexXmlTag 1 : lexerReturns state})
  | startsWith "(" state =
      let after = advanceOne state
       in emitFrom state (TokenPunctuation "(") (after {lexerMode = LexNormal, lexerReturns = BraceReturn LexXmlTag 1 : lexerReturns state})
  | Just width <- xmlIdentifierPrefix state =
      let (raw, after) = takeBytes width state
       in emitFrom state (TokenIdentifier (B8.unpack (BS.pack raw))) after
  | Just (kind, width) <- numberPrefix state = emitFrom state kind (advanceN width state)
  | otherwise =
      let offending = take 1 (lexerRemaining state)
          after = advanceOne state
       in addLexError "illegal-xml-tag-character" ("illegal XML tag character: " <> showBytes offending) after state

lexPunctuation :: String -> Int -> LexerState -> LexerState
lexPunctuation spelling width state =
  let after0 = advanceN width state
      after = case spelling of
        "{" -> after0 {lexerReturns = incrementBrace (lexerReturns state)}
        "}" -> closeBrace after0 state
        _ -> after0
      kind = if spelling == "()" then TokenUnit else TokenPunctuation spelling
   in emitFrom state kind after

incrementBrace :: [BraceReturn] -> [BraceReturn]
incrementBrace [] = []
incrementBrace (context : rest) = context {braceDepth = braceDepth context + 1} : rest

closeBrace :: LexerState -> LexerState -> LexerState
closeBrace after before = case lexerReturns before of
  [] -> after
  context : rest
    | braceDepth context <= 1 -> after {lexerMode = braceReturnMode context, lexerReturns = rest}
    | otherwise -> after {lexerReturns = context {braceDepth = braceDepth context - 1} : rest}

lexIdentifier :: Int -> LexerState -> LexerState
lexIdentifier width state =
  let (raw, after) = takeBytes width state
      spelling = B8.unpack (BS.pack raw)
      kind
        | spelling == "_LOC_" = TokenString (B8.pack (renderSpan (spanFrom state after)))
        | Set.member spelling keywords = TokenKeyword spelling
        | firstIsUpper raw = TokenConstructor spelling
        | otherwise = TokenIdentifier spelling
   in emitFrom state kind after
  where
    firstIsUpper (first : _) = isAsciiUpper first
    firstIsUpper [] = False

lexBacktick :: LexerState -> LexerState
lexBacktick state =
  let body = takeWhile (/= ascii '`') (drop 1 (lexerRemaining state))
      width = length body + 2
   in if length (lexerRemaining state) >= width && validBacktick body
        then emitFrom state (TokenBacktickPath (B8.unpack (BS.pack body))) (advanceN width state)
        else addLexError "illegal-backtick" "Malformed backtick path" (advanceOne state) state

validBacktick :: [Word8] -> Bool
validBacktick bytes = case splitByte (ascii '.') bytes of
  [] -> False
  pieces -> all validUpperPiece (init pieces) && validLowerPiece (last pieces)
  where
    validUpperPiece (first : rest) = isAsciiUpper first && all isIdentifierRest rest
    validUpperPiece [] = False
    validLowerPiece (first : rest) = isIdentifierStart first && all isIdentifierRest rest
    validLowerPiece [] = False

lexQuoted :: Bool -> Word8 -> LexerState -> LexerState -> LexerState
lexQuoted isCharacter ender contentStart tokenStart =
  let (payload, after, terminated, problems) = scanQuoted ender contentStart
      withProblems = foldl' (flip addDiagnostic) after problems
   in if not terminated
        then addLexError "unterminated-literal" "Unterminated string or character constant" withProblems tokenStart
        else
          if isCharacter
            then case payload of
              [byte] -> emitFrom tokenStart (TokenChar byte) withProblems
              _ -> addLexError "character-length" "Character constant is zero or multiple characters" withProblems tokenStart
            else emitFrom tokenStart (TokenString (BS.pack payload)) withProblems

lexXmlQuoted :: LexerState -> LexerState -> LexerState
lexXmlQuoted contentStart tokenStart =
  let (payload, after, terminated, problems) = scanQuoted 34 contentStart
      withProblems = foldl' (flip addDiagnostic) after problems
      restored = withProblems {lexerMode = LexXmlTag}
   in if terminated
        then emitFrom tokenStart (TokenString (BS.pack payload)) restored
        else addLexError "unterminated-xml-attribute" "Unterminated XML attribute string" restored tokenStart

scanQuoted :: Word8 -> LexerState -> ([Word8], LexerState, Bool, [Diagnostic])
scanQuoted ender = go [] []
  where
    go output problems state = case lexerRemaining state of
      [] -> (reverse output, state, False, reverse problems)
      byte : _
        | byte == ender -> (reverse output, advanceOne state, True, reverse problems)
        | startsWith "\\\"" state -> go (ascii '"' : output) problems (advanceN 2 state)
        | startsWith "\\'" state -> go (ascii '\'' : output) problems (advanceN 2 state)
        | startsWith "\\n" state -> go (ascii '\n' : output) problems (advanceN 2 state)
        | startsWith "\\r" state -> go (ascii '\r' : output) problems (advanceN 2 state)
        | startsWith "\\\\" state -> go (ascii '\\' : output) problems (advanceN 2 state)
        | startsWith "\\t" state -> go (ascii '\t' : output) problems (advanceN 2 state)
        | Just (value, width) <- octalEscape state -> go (value : output) problems (advanceN width state)
        | Just (value, width) <- hexadecimalEscape state -> go (value : output) problems (advanceN width state)
        | otherwise -> go (byte : output) problems (advanceOne state)

octalEscape :: LexerState -> Maybe (Word8, Int)
octalEscape state = case lexerRemaining state of
  slash : a : b : c : _
    | slash == ascii '\\' && all isOctal [a, b, c] ->
        let value = fromIntegral ((digitValue a * 64) + (digitValue b * 8) + digitValue c)
         in Just (value, 4)
  _ -> Nothing

hexadecimalEscape :: LexerState -> Maybe (Word8, Int)
hexadecimalEscape state = case lexerRemaining state of
  slash : marker : a : b : _
    | slash == ascii '\\' && marker == ascii 'x' && all isHex [a, b] ->
        Just (fromIntegral (hexValue a * 16 + hexValue b), 4)
  _ -> Nothing

skipComment :: LexMode -> LexerState -> LexerState
skipComment returnMode start = go 1 (advanceN 2 start)
  where
    go :: Int -> LexerState -> LexerState
    go depth state
      | null (lexerRemaining state) =
          addLexError "unterminated-comment" "Unterminated comment" (state {lexerMode = returnMode}) start
      | startsWith "(*" state = go (depth + 1) (advanceN 2 state)
      | startsWith "*)" state =
          let after = advanceN 2 state
           in if depth == 1 then after {lexerMode = returnMode} else go (depth - 1) after
      | otherwise = go depth (advanceOne state)

skipXmlComment :: LexerState -> LexerState
skipXmlComment start = go (advanceN 4 start)
  where
    go state
      | null (lexerRemaining state) = addLexError "unterminated-xml-comment" "Unterminated XML comment" state start
      | startsWith "-->" state = (advanceN 3 state) {lexerMode = LexXml}
      | otherwise = go (advanceOne state)

lexXmlText :: LexerState -> LexerState
lexXmlText state =
  let width = xmlTextWidth (lexerRemaining state)
   in if width == 0
        then
          let offending = take 1 (lexerRemaining state)
              after = advanceOne state
           in addLexError "illegal-xml-character" ("illegal XML character: " <> showBytes offending) after state
        else
          let (raw, after) = takeBytes width state
              at = spanFrom state after
              (decoded, problems) = decodeEntities at raw
              withProblems = foldl' (flip addDiagnostic) after problems
           in emitFrom state (TokenXmlText (BS.pack decoded)) withProblems

xmlTextWidth :: [Word8] -> Int
xmlTextWidth = go 0
  where
    go count [] = count
    go count (byte : rest)
      | byte == ascii '<' || byte == ascii '{' || byte == ascii '\n' = count
      | byte == ascii '(' && take 1 rest == [ascii '*'] = count
      | otherwise = go (count + 1) rest

decodeEntities :: Span -> [Word8] -> ([Word8], [Diagnostic])
decodeEntities at = go [] []
  where
    go output problems [] = (reverse output, reverse problems)
    go output problems (byte : rest)
      | byte /= ascii '&' = go (byte : output) problems rest
      | otherwise =
          let (code, suffix) = break (== ascii ';') rest
           in case suffix of
                [] ->
                  ( reverse output
                  , reverse (diagnostic LexPhase "xml-entity-semicolon" at "Missing ';' after '&'" : problems)
                  )
                _semicolon : remaining ->
                  case entityValue code of
                    Nothing ->
                      go output (diagnostic LexPhase "xml-entity" at ("Unsupported XML character entity " <> B8.unpack (BS.pack code)) : problems) remaining
                    Just scalar -> go (reverse (encodeUtf8 scalar) <> output) problems remaining

entityValue :: [Word8] -> Maybe Int
entityValue (marker : digits)
  | marker == ascii '#' && not (null digits) && all isAsciiDigit digits = readMaybe (map (chr . fromIntegral) digits)
entityValue bytes = Map.lookup (B8.unpack (BS.pack bytes)) namedEntities

namedEntities :: Map.Map String Int
namedEntities =
  Map.fromList
    [ ("nbsp", 160)
    , ("iexcl", 161)
    , ("cent", 162)
    , ("pound", 163)
    , ("curren", 164)
    , ("yen", 165)
    , ("brvbar", 166)
    , ("sect", 167)
    , ("uml", 168)
    , ("copy", 169)
    , ("ordf", 170)
    , ("laquo", 171)
    , ("not", 172)
    , ("shy", 173)
    , ("reg", 174)
    , ("macr", 175)
    , ("deg", 176)
    , ("plusmn", 177)
    , ("sup2", 178)
    , ("sup3", 179)
    , ("acute", 180)
    , ("micro", 181)
    , ("para", 182)
    , ("middot", 183)
    , ("cedil", 184)
    , ("sup1", 185)
    , ("ordm", 186)
    , ("raquo", 187)
    , ("frac14", 188)
    , ("frac12", 189)
    , ("frac34", 190)
    , ("iquest", 191)
    , ("Agrave", 192)
    , ("Aacute", 193)
    , ("Acirc", 194)
    , ("Atilde", 195)
    , ("Auml", 196)
    , ("Aring", 197)
    , ("AElig", 198)
    , ("Ccedil", 199)
    , ("Egrave", 200)
    , ("Eacute", 201)
    , ("Ecirc", 202)
    , ("Euml", 203)
    , ("Igrave", 204)
    , ("Iacute", 205)
    , ("Icirc", 206)
    , ("Iuml", 207)
    , ("ETH", 208)
    , ("Ntilde", 209)
    , ("Ograve", 210)
    , ("Oacute", 211)
    , ("Ocirc", 212)
    , ("Otilde", 213)
    , ("Ouml", 214)
    , ("times", 215)
    , ("Oslash", 216)
    , ("Ugrave", 217)
    , ("Uacute", 218)
    , ("Ucirc", 219)
    , ("Uuml", 220)
    , ("Yacute", 221)
    , ("THORN", 222)
    , ("szlig", 223)
    , ("agrave", 224)
    , ("aacute", 225)
    , ("acirc", 226)
    , ("atilde", 227)
    , ("auml", 228)
    , ("aring", 229)
    , ("aelig", 230)
    , ("ccedil", 231)
    , ("egrave", 232)
    , ("eacute", 233)
    , ("ecirc", 234)
    , ("euml", 235)
    , ("igrave", 236)
    , ("iacute", 237)
    , ("icirc", 238)
    , ("iuml", 239)
    , ("eth", 240)
    , ("ntilde", 241)
    , ("ograve", 242)
    , ("oacute", 243)
    , ("ocirc", 244)
    , ("otilde", 245)
    , ("ouml", 246)
    , ("divide", 247)
    , ("oslash", 248)
    , ("ugrave", 249)
    , ("uacute", 250)
    , ("ucirc", 251)
    , ("uuml", 252)
    , ("yacute", 253)
    , ("thorn", 254)
    , ("yuml", 255)
    , ("quot", 34)
    , ("amp", 38)
    , ("lt", 60)
    , ("gt", 62)
    , ("apos", 39)
    , ("OElig", 338)
    , ("oelig", 339)
    , ("Scaron", 352)
    , ("scaron", 353)
    , ("Yuml", 376)
    , ("circ", 710)
    , ("tilde", 732)
    , ("ensp", 8194)
    , ("emsp", 8195)
    , ("thinsp", 8201)
    , ("zwnj", 8204)
    , ("zwj", 8205)
    , ("lrm", 8206)
    , ("rlm", 8207)
    , ("ndash", 8211)
    , ("mdash", 8212)
    , ("lsquo", 8216)
    , ("rsquo", 8217)
    , ("sbquo", 8218)
    , ("ldquo", 8220)
    , ("rdquo", 8221)
    , ("bdquo", 8222)
    , ("dagger", 8224)
    , ("Dagger", 8225)
    , ("permil", 8240)
    , ("lsaquo", 8249)
    , ("rsaquo", 8250)
    , ("euro", 8364)
    , ("fnof", 402)
    , ("Alpha", 913)
    , ("Beta", 914)
    , ("Gamma", 915)
    , ("Delta", 916)
    , ("Epsilon", 917)
    , ("Zeta", 918)
    , ("Eta", 919)
    , ("Theta", 920)
    , ("Iota", 921)
    , ("Kappa", 922)
    , ("Lambda", 923)
    , ("Mu", 924)
    , ("Nu", 925)
    , ("Xi", 926)
    , ("Omicron", 927)
    , ("Pi", 928)
    , ("Rho", 929)
    , ("Sigma", 931)
    , ("Tau", 932)
    , ("Upsilon", 933)
    , ("Phi", 934)
    , ("Chi", 935)
    , ("Psi", 936)
    , ("Omega", 937)
    , ("alpha", 945)
    , ("beta", 946)
    , ("gamma", 947)
    , ("delta", 948)
    , ("epsilon", 949)
    , ("zeta", 950)
    , ("eta", 951)
    , ("theta", 952)
    , ("iota", 953)
    , ("kappa", 954)
    , ("lambda", 955)
    , ("mu", 956)
    , ("nu", 957)
    , ("xi", 958)
    , ("omicron", 959)
    , ("pi", 960)
    , ("rho", 961)
    , ("sigmaf", 962)
    , ("sigma", 963)
    , ("tau", 964)
    , ("upsilon", 965)
    , ("phi", 966)
    , ("chi", 967)
    , ("psi", 968)
    , ("omega", 969)
    , ("thetasym", 977)
    , ("upsih", 978)
    , ("piv", 982)
    , ("bull", 8226)
    , ("hellip", 8230)
    , ("prime", 8242)
    , ("Prime", 8243)
    , ("oline", 8254)
    , ("frasl", 8260)
    , ("weierp", 8472)
    , ("image", 8465)
    , ("real", 8476)
    , ("trade", 8482)
    , ("alefsym", 8501)
    , ("larr", 8592)
    , ("uarr", 8593)
    , ("rarr", 8594)
    , ("darr", 8595)
    , ("harr", 8596)
    , ("crarr", 8629)
    , ("lArr", 8656)
    , ("uArr", 8657)
    , ("rArr", 8658)
    , ("dArr", 8659)
    , ("hArr", 8660)
    , ("forall", 8704)
    , ("part", 8706)
    , ("exist", 8707)
    , ("empty", 8709)
    , ("nabla", 8711)
    , ("isin", 8712)
    , ("notin", 8713)
    , ("ni", 8715)
    , ("prod", 8719)
    , ("sum", 8721)
    , ("minus", 8722)
    , ("lowast", 8727)
    , ("radic", 8730)
    , ("prop", 8733)
    , ("infin", 8734)
    , ("ang", 8736)
    , ("and", 8743)
    , ("or", 8744)
    , ("cap", 8745)
    , ("cup", 8746)
    , ("int", 8747)
    , ("there4", 8756)
    , ("sim", 8764)
    , ("cong", 8773)
    , ("asymp", 8776)
    , ("ne", 8800)
    , ("equiv", 8801)
    , ("le", 8804)
    , ("ge", 8805)
    , ("sub", 8834)
    , ("sup", 8835)
    , ("nsub", 8836)
    , ("sube", 8838)
    , ("supe", 8839)
    , ("oplus", 8853)
    , ("otimes", 8855)
    , ("perp", 8869)
    , ("sdot", 8901)
    , ("lceil", 8968)
    , ("rceil", 8969)
    , ("lfloor", 8970)
    , ("rfloor", 8971)
    , ("lang", 9001)
    , ("rang", 9002)
    , ("loz", 9674)
    , ("spades", 9824)
    , ("clubs", 9827)
    , ("hearts", 9829)
    , ("diams", 9830)
    ]

encodeUtf8 :: Int -> [Word8]
encodeUtf8 scalar
  | scalar < 0 || scalar > 0x10FFFF || scalar >= 0xD800 && scalar <= 0xDFFF = []
  | scalar <= 0x7F = [fromIntegral scalar]
  | scalar <= 0x7FF =
      [ fromIntegral (0xC0 + scalar `div` 0x40)
      , fromIntegral (0x80 + scalar `mod` 0x40)
      ]
  | scalar <= 0xFFFF =
      [ fromIntegral (0xE0 + scalar `div` 0x1000)
      , fromIntegral (0x80 + scalar `div` 0x40 `mod` 0x40)
      , fromIntegral (0x80 + scalar `mod` 0x40)
      ]
  | otherwise =
      [ fromIntegral (0xF0 + scalar `div` 0x40000)
      , fromIntegral (0x80 + scalar `div` 0x1000 `mod` 0x40)
      , fromIntegral (0x80 + scalar `div` 0x40 `mod` 0x40)
      , fromIntegral (0x80 + scalar `mod` 0x40)
      ]

numberPrefix :: LexerState -> Maybe (TokenKind, Int)
numberPrefix state = case lexerRemaining state of
  first : _ | isAsciiDigit first ->
    let bytes = lexerRemaining state
        digits = takeWhile isAsciiDigit bytes
        decimalWidth = length digits
     in if take 2 bytes == map ascii "0x"
          then
            let hexDigits = takeWhile isUpperHex (drop 2 bytes)
             in if null hexDigits
                  then decimalToken digits
                  else case readHexInt64 hexDigits of
                    Nothing -> Nothing
                    Just value -> Just (TokenInt value, 2 + length hexDigits)
          else case drop decimalWidth bytes of
            dot : suffix | dot == ascii '.' ->
              let fraction = takeWhile isAsciiDigit suffix
                  spelling = map (chr . fromIntegral) (digits <> [dot] <> fraction)
                  readable = if null fraction then spelling <> "0" else spelling
               in (, decimalWidth + 1 + length fraction) . TokenFloat <$> readMaybe readable
            _ -> decimalToken digits
  _ -> Nothing
  where
    decimalToken digits = (, length digits) . TokenInt <$> readMaybe (map (chr . fromIntegral) digits)

readHexInt64 :: [Word8] -> Maybe Int64
readHexInt64 digits =
  let value = foldl' (\total digit -> total * 16 + toInteger (hexValue digit)) 0 digits
   in if value <= toInteger (maxBound :: Int64) then Just (fromInteger value) else Nothing

identifierPrefix :: LexerState -> Maybe Int
identifierPrefix state = case lexerRemaining state of
  first : rest
    | isIdentifierStart first || isAsciiUpper first -> Just (1 + length (takeWhile isIdentifierRest rest))
  _ -> Nothing

xmlIdentifierPrefix :: LexerState -> Maybe Int
xmlIdentifierPrefix state = case lexerRemaining state of
  first : rest
    | isAsciiLetter first -> Just (1 + length (takeWhile isXmlIdentifierRest rest))
  _ -> Nothing

xmlRootPrefix :: LexerState -> Maybe (String, Bool, Int)
xmlRootPrefix state = case lexerRemaining state of
  less : rest | less == ascii '<' -> case xmlName rest of
    Nothing -> Nothing
    Just (nameBytes, suffix) ->
      let consumedName = 1 + length nameBytes
          name = B8.unpack (BS.pack nameBytes)
       in if take 2 suffix == map ascii "/>"
            then Just (name, True, consumedName + 2)
            else if take 1 suffix == [ascii '>']
              then Just (name, False, consumedName + 1)
              else Nothing
  _ -> Nothing

xmlEndPrefix :: LexerState -> Maybe (String, Int)
xmlEndPrefix state = case lexerRemaining state of
  less : slash : rest | less == ascii '<' && slash == ascii '/' -> case xmlName rest of
    Just (nameBytes, suffix) | take 1 suffix == [ascii '>'] ->
      Just (B8.unpack (BS.pack nameBytes), 3 + length nameBytes)
    _ -> Nothing
  _ -> Nothing

beginTagPrefix :: LexerState -> Maybe (String, Int)
beginTagPrefix state = case lexerRemaining state of
  less : rest | less == ascii '<' -> case xmlName rest of
    Just (nameBytes, _) -> Just (B8.unpack (BS.pack nameBytes), 1 + length nameBytes)
    Nothing -> Nothing
  _ -> Nothing

xmlName :: [Word8] -> Maybe ([Word8], [Word8])
xmlName bytes = case bytes of
  first : rest | isAsciiLetter first ->
    let tailBytes = takeWhile isXmlIdentifierRest rest
        width = 1 + length tailBytes
     in Just (take width bytes, drop width bytes)
  _ -> Nothing

punctuationPrefix :: LexerState -> Maybe (String, Int)
punctuationPrefix state =
  fmap (\spelling -> (spelling, length spelling))
    (find (\spelling -> startsWith spelling state) punctuation)

punctuation :: [String]
punctuation =
  [ ":::_", "---", "-->", "==>", "<<<", ">>>", "::_", ":::"
  , "<->", "->", "=>", "++", "--", "&&", "||", "<|", "|>"
  , "<>", "<=", ">=", "<-", "...", "::", "()"
  , "(", ")", "[", "]", "{", "}", "=", "<", ">", ",", ":"
  , ".", "$", "#", "__", "_", "~", "|", "*", ";", "!", "+"
  , "-", "/", "%", "@", "^"
  ]

keywords :: Set.Set String
keywords =
  Set.fromList
    [ "con", "type", "datatype", "of", "val", "rec", "and", "fun", "fn"
    , "map", "case", "if", "then", "else", "structure", "signature", "struct"
    , "sig", "let", "in", "end", "functor", "where", "include", "open"
    , "constraint", "constraints", "export", "table", "sequence", "view"
    , "ensure_index", "class", "cookie", "style", "task", "policy", "ffi"
    , "SELECT", "DISTINCT", "FROM", "AS", "WHERE", "SQL", "GROUP", "ORDER"
    , "BY", "HAVING", "LIMIT", "OFFSET", "ALL", "SELECT1", "JOIN", "INNER"
    , "CROSS", "OUTER", "LEFT", "RIGHT", "FULL", "UNION", "INTERSECT"
    , "EXCEPT", "TRUE", "FALSE", "AND", "OR", "NOT", "COUNT", "AVG", "SUM"
    , "MIN", "MAX", "RANK", "PARTITION", "OVER", "IF", "THEN", "ELSE", "ASC"
    , "DESC", "RANDOM", "INSERT", "INTO", "VALUES", "UPDATE", "SET", "DELETE"
    , "NULL", "IS", "COALESCE", "LIKE", "CONSTRAINT", "UNIQUE", "CHECK"
    , "PRIMARY", "FOREIGN", "KEY", "ON", "NO", "ACTION", "RESTRICT", "CASCADE"
    , "REFERENCES", "CURRENT_TIMESTAMP"
    ]

whitespacePrefix :: LexerState -> Maybe Int
whitespacePrefix state =
  let width = length (takeWhile isWhitespaceByte (lexerRemaining state))
   in if width == 0 then Nothing else Just width

isWhitespaceByte :: Word8 -> Bool
isWhitespaceByte byte = byte `elem` map ascii [' ', '\t', '\f', '\r', '\n']

isIdentifierStart :: Word8 -> Bool
isIdentifierStart byte = byte == ascii '_' || byte >= ascii 'a' && byte <= ascii 'z'

isIdentifierRest :: Word8 -> Bool
isIdentifierRest byte = isAsciiLetter byte || isAsciiDigit byte || byte == ascii '_' || byte == ascii '\''

isXmlIdentifierRest :: Word8 -> Bool
isXmlIdentifierRest byte = isAsciiLetter byte || isAsciiDigit byte || byte == ascii '_' || byte == ascii '-'

isAsciiLetter :: Word8 -> Bool
isAsciiLetter byte = byte >= ascii 'a' && byte <= ascii 'z' || isAsciiUpper byte

isAsciiUpper :: Word8 -> Bool
isAsciiUpper byte = byte >= ascii 'A' && byte <= ascii 'Z'

isAsciiDigit :: Word8 -> Bool
isAsciiDigit byte = byte >= ascii '0' && byte <= ascii '9'

isOctal :: Word8 -> Bool
isOctal byte = byte >= ascii '0' && byte <= ascii '7'

isHex :: Word8 -> Bool
isHex byte = isAsciiDigit byte || byte >= ascii 'a' && byte <= ascii 'f' || isUpperHex byte

isUpperHex :: Word8 -> Bool
isUpperHex byte = byte >= ascii 'A' && byte <= ascii 'F'

digitValue :: Word8 -> Int
digitValue byte = fromIntegral (byte - ascii '0')

hexValue :: Word8 -> Int
hexValue byte
  | isAsciiDigit byte = digitValue byte
  | byte >= ascii 'a' && byte <= ascii 'f' = 10 + fromIntegral (byte - ascii 'a')
  | otherwise = 10 + fromIntegral (byte - ascii 'A')

ascii :: Char -> Word8
ascii = fromIntegral . ord

startsWith :: String -> LexerState -> Bool
startsWith spelling state = match spelling (lexerRemaining state)
  where
    match [] _ = True
    match (character : rest) (byte : bytes) = ascii character == byte && match rest bytes
    match _ [] = False

takeBytes :: Int -> LexerState -> ([Word8], LexerState)
takeBytes width state = (take width (lexerRemaining state), advanceN width state)

advanceN :: Int -> LexerState -> LexerState
advanceN count state
  | count <= 0 = state
  | otherwise = advanceN (count - 1) (advanceOne state)

advanceOne :: LexerState -> LexerState
advanceOne state = case lexerRemaining state of
  [] -> state
  byte : rest ->
    let old = lexerPosition state
        offset = sourceOffset old + 1
     in if byte == ascii '\n'
          then
            state
              { lexerRemaining = rest
              , lexerPosition = SourcePos offset (sourceLine old + 1) 0
              , lexerLineStart = offset
              }
          else
            state
              { lexerRemaining = rest
              , lexerPosition = SourcePos offset (sourceLine old) (offset - lexerLineStart state)
              }

emitFrom :: LexerState -> TokenKind -> LexerState -> LexerState
emitFrom start kind after =
  after {lexerTokensRev = Token (spanFrom start after) kind : lexerTokensRev after}

spanFrom :: LexerState -> LexerState -> Span
spanFrom start end = Span (lexerFile start) (lexerPosition start) (lexerPosition end)

addLexError :: String -> String -> LexerState -> LexerState -> LexerState
addLexError code message after start =
  addDiagnostic (diagnostic LexPhase code (spanFrom start after) message) after

addDiagnostic :: Diagnostic -> LexerState -> LexerState
addDiagnostic problem state = state {lexerDiagnosticsRev = problem : lexerDiagnosticsRev state}

showBytes :: [Word8] -> String
showBytes bytes = show (B8.unpack (BS.pack bytes))

renderSpan :: Span -> String
renderSpan at =
  spanFile at
    <> ":"
    <> show (sourceLine (spanStart at))
    <> ":"
    <> show (sourceColumn (spanStart at))
    <> "-"
    <> show (sourceLine (spanEnd at))
    <> ":"
    <> show (sourceColumn (spanEnd at))

splitByte :: Word8 -> [Word8] -> [[Word8]]
splitByte separator = foldr step [[]]
  where
    step byte groups@(group : rest)
      | byte == separator = [] : groups
      | otherwise = (byte : group) : rest
    step _ [] = error "splitByte invariant"
