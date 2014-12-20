import Control.Monad (foldM, foldM_, zipWithM)
import System.Environment (getArgs)
import System.Exit (exitFailure)

import Text.Parsec (parse)

import Uroboro.Checker (rules, emptyProgram, checkPT, inferPExp)
import Uroboro.Interpreter (eval)
import Uroboro.Parser (Parser, parseDef, parseExp)
import Uroboro.Tree

data Mode = Help
          | Typecheck [FilePath]
          | Evaluate  [FilePath] String deriving (Eq, Show)

-- |Parse command line options.
getOpt :: [String] -> Mode
getOpt args = case break (== "--") args of
    ([], _)     -> Help
    (x, [])     -> Typecheck x
    (x, [_, y]) -> Evaluate x y
    _           -> Help

eitherIO :: Show a => Either a b -> IO b
eitherIO (Left e)  = do
    print e
    exitFailure
eitherIO (Right b) = return b

-- |Switch monads.
parseIO :: Parser a -> String -> String -> IO a
parseIO parser fname input = eitherIO $ parse parser fname input

-- |Load libraries.
parseFiles :: [FilePath] -> IO [PT]
parseFiles paths = do
    lol <- mapM readFile paths >>= zipWithM (parseIO parseDef) paths
    return $ concat lol

main :: IO ()
main = do
    args <- getArgs
    case getOpt args of
        Evaluate paths input -> do
            defs  <- parseFiles paths
            pexp  <- eitherIO $ parse parseExp "command line" input

            prog <- eitherIO $ foldM checkPT emptyProgram defs
            texp  <- eitherIO $ inferPExp prog [] pexp

            print $ eval (rules prog) texp
        Typecheck paths -> do
            defs  <- parseFiles paths
            eitherIO $ foldM_ checkPT emptyProgram defs     -- Success is silent.
        Help -> do
            putStrLn "USAGE: uroboro FILES [-- EXPRESSION]"
            exitFailure
