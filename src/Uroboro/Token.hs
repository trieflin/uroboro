module Uroboro.Token where

import qualified Text.Parsec.Token as T
import Text.Parsec.Language (emptyDef)
import Text.Parsec.Prim

-- | Parser without user state. 
-- | Parser a = ParsecT String () Identity a
-- |    streams Strings, has user state type Unit, underlying monad Identity and return type a

type Parser = Parsec String ()

languageDef :: T.LanguageDef ()
languageDef = emptyDef
    { T.commentStart = "{-"
    , T.commentEnd = "-}"
    , T.commentLine = "--"
    , T.reservedNames = ["data", "codata", "function", "where"]
    , T.nestedComments = True
    }
 
lexer :: T.TokenParser ()
lexer = T.makeTokenParser languageDef

whiteSpace :: Parser ()
whiteSpace = T.whiteSpace lexer

reserved :: String -> Parser ()
reserved = T.reserved lexer

identifier :: Parser String
identifier = T.identifier lexer

commaSep :: Parser a -> Parser [a]
commaSep = T.commaSep lexer

colon :: Parser String
colon = T.colon lexer

dot :: Parser String
dot = T.dot lexer

eq :: Parser String
eq = T.symbol lexer "="
--symbol = T.symbol lexer     -- = 

parens :: Parser a -> Parser a
parens = T.parens lexer     -- ()

angles :: Parser a -> Parser a
angles = T.angles lexer     -- <>

brackets :: Parser a -> Parser a
brackets = T.brackets lexer -- []

--braces = T.braces lexer     -- {}
