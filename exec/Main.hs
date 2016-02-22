module Main where

import Control.Monad (forM) 
import System.Environment (getArgs)
import System.Exit (exitFailure)

import Uroboro.ExternalSyntax (Def)
import Uroboro.InternalSyntax
import Uroboro.Parser (parseFile, parseExpression)
import Uroboro.Checker (typecheck)
import Uroboro.Interpreter (eval)
import Uroboro.PrettyPrinter (render)
import Uroboro.FillRules (inferExp)

-- |How the program operates, and on what data.
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


-- |For a left value, print it and set the exit code.
eitherIO :: Show a => Show b => Either a b -> IO b
eitherIO (Left l) = do
    putStrLn ("Exception " ++ show l)
    exitFailure
eitherIO (Right r) = do 
 --   print r 
    return r

-- |Load libraries.
parseFiles :: [FilePath] -> IO [Def]
parseFiles paths = do
    lol <- forM paths $ \path -> do
      input <- readFile path
      eitherIO $ parseFile path input
    return $ concat lol
    
uroLib' = ["bool.uro", "nat.uro", "function.uro", "list.uro", "tree.uro", "stream.uro"] 
uroLib = map (\a -> "samples/lib/" ++ a) uroLib'
 
-- | parse uro-files (parsing, typechecking, running)
main::IO()
main = do
    args <- getArgs
    case getOpt args of
        Evaluate paths input -> do
            defs <- parseFiles (paths ++ uroLib)
            prog <- eitherIO $ typecheck defs
            pexp <- eitherIO $ parseExpression "command line" input
            texp <- eitherIO $ inferExp prog emptyContext pexp
            putStrLn (render $ eval (prgRules prog) texp)
            exitFailure
        Typecheck paths -> do
            defs <- parseFiles (paths ++ uroLib)
            prog <- eitherIO (typecheck defs)
            putStrLn "Typechecking successfull."
        Help -> do
            putStrLn "USAGE: uroboro FILES [-- EXPRESSION]"
            exitFailure
