module Uroboro.Parser where --(parseFile, parseExpression, uroparse)

import Text.Parsec (many, many1, choice, eof, getPosition, parse, try, (<?>), option) -- instead of (<|>): choice
import Control.Arrow (left)
import Control.Monad (liftM) --foldMap)
--import Control.Applicative(<*>)

import Uroboro.Token
import Uroboro.Location
import Uroboro.Error
import Uroboro.ExternalSyntax

-- | Parser without user state. 
-- | Parser a = ParsecT String () Identity a
-- |    streams Strings, has user state type Unit, underlying monad Identity and return type is type Parser a = Parsec String () a

-- | Parse whole file.
parseFile :: FilePath -> String -> Either Error [Def]
parseFile = uroparse $ whiteSpace *> parseDef <* eof 

-- | Parse expression.
parseExpression :: FilePath -> String -> Either Error Exp
parseExpression = uroparse $ whiteSpace *> parseExp <* eof 

-- | Parse something. --TODO inline ?
uroparse :: Parser a -> FilePath -> String -> Either Error a
uroparse parser fname input = left convertError $ parse parser fname input

-- |Parse "(p, ...)".
args :: Parser a -> Parser [a]
args p = parens (commaSep p) <?> "( arguments )"

-- |Parse "<p, ...>". : [String]
--typeabss :: Parser a -> Parser [a]
typeabss = angles (commaSep abst) <?> "< type abstractions >"

-- |Parse "[p, ...]". : [Type]
--typeapps :: Parser a -> Parser [a]
typeapps = brackets (commaSep ttyp) <?> "[ type applications ]"

ttyp :: Parser Type
ttyp = choice [try typt, typvar] <?> "type (typet or typevar)"  
typt :: Parser Type 
typt = liftLoc TypeT tau <*> typeapps <?> "type t"
typvar :: Parser Type
typvar = liftLoc TypeVar identifier <?> "typevariable"
abst :: Parser Abs
abst = liftLoc Abs identifier <?> "abs"
tau :: Parser Tau
tau = liftLoc Tau identifier <?> "tau" 
ident :: Parser Identifier
ident = liftLoc Identifier identifier <?> "identifier"

typeabsopt = option [] typeabss
typeappopt = option [] typeapps

-- |Parse top-level definition (data, codata or function)
parseDef :: Parser [Def]
parseDef =  many (choice [datdef, codef,  fundef] <?> "top level definition" )
    where
        datdef = liftLoc (toDatDef Def) (reserved "data" *> tau) <*> typeabsopt <*> where1 conSig <?> "data type definition"
        codef  = liftLoc (toCodDef Def) (reserved "codata" *> tau) <*> typeabsopt <*> where1 desSig <?> "codata type definition"           
        fundef = liftLoc (toFunDef Def) (reserved "function" *> typeabsopt) <*> funSig <*> where1 rule <?> "function definition"
        
        toDatDef make l t a s = make l a (DatDefNature t s)
        toCodDef make l t a s = make l a (CodDefNature t s)
        toFunDef make l a s r = make l a (FunDefNature s r)
                                      
        where1 a = reserved "where" *> many a
        
        conSig = liftLoc (toConSig ConSig) ident <*> args ttyp <*> (colon *> tauToType) <?> "constructor signature"
        desSig = liftLoc (toDesSig DesSig) (tauToType <* dot) <*> ident <*> args ttyp <*> (colon *> ttyp) <?> "destructor signature"
        funSig = liftLoc (toFunSig FunSig) ident <*> args ttyp <*> (colon *> ttyp) <?> "function signature"
        tauToType = liftLoc TypeT tau <*> typeappopt 
                 
        rule = liftLoc Rule parseCoPat <*> (eq *> parseExp) <?> "rule"

        toConSig make l id args ret = make l id args ret ConSigNature
        toDesSig make l t id args ret = make l id args ret (DesSigNature t)
        toFunSig make l id args ret = make l id args ret FunSigNature
        
-- |Parse copattern.
parseCoPat :: Parser Cop
parseCoPat = choice [try descop,appcop] <?> "copattern"
    where 
    descop = liftLoc (toDesCop Cop) ident <*> args parsePat <*> many1 (parseDApsCop DApsCop parsePat) <?> "destructor application" 
    appcop = liftLoc (toAppCop Cop) ident <*> args parsePat <?> "function/constructor application" 

    parseDApsCop :: (Location -> Identifier -> TypeApplications -> [Pat] -> DApsCop) -> Parser Pat -> Parser DApsCop
    parseDApsCop make b  = dot *> liftLoc make ident <*> typeappopt <*> args b  <?> "dot application in left hand side of rule"

    toDesCop make loc ident pats dcops = make loc ident pats (DesCopNature dcops)
    toAppCop make loc ident pats = make loc ident pats AppCopNature

-- |Parse pattern.
parsePat :: Parser Pat
parsePat = choice [try con, var] <?> "pattern"
  where
    con = liftLoc AppPat ident <*> typeappopt <*> args parsePat <?> "application pattern" 
    var = liftLoc VarPat ident <?> "variable pattern"
    

-- |Parse expression
parseExp :: Parser Exp
parseExp = choice [des, app, var] <?> "expression" 
  where 
    des = try (liftLoc DesExp (choice [app, var]) <*> many1 (dot *> liftLoc DExp ident <*> typeappopt <*> args parseExp) <?> "des-exp")
    app = try (liftLoc AppExp ident <*> typeappopt <*> args parseExp <?> "app-exp")
    var = liftLoc VarExp ident <?> "var-exp"
    
-- |Variant of liftM that also stores the current location
-- constructs intern types for external abstract syntax tree
-- fetching sourcepos for exception messages
liftLoc :: (Location -> a -> b) -> Parser a -> Parser b
liftLoc dtcon parser = do
    pos <- getPosition
    arg <- parser -- Parser returns its argument
    return (dtcon (convertLocation pos) arg) 
