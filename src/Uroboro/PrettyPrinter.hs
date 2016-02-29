module Uroboro.PrettyPrinter where

import Data.List (intercalate)
import Uroboro.InternalSyntax

parens :: String -> String
parens s = "(" ++ s ++ ")"

angles :: String -> String
angles s = "<" ++ s ++ ">"

brackets :: String -> String
brackets s = "[" ++ s ++ "]"

commaSep :: [String] -> String
commaSep = intercalate ", " -- sls

args :: [Exp] -> String
args es = parens (commaSep (map render es))

render :: Exp -> String
render (Exp _ (Identifier _ n,t) VarExp) = n
render (Exp _ (Identifier _ n,t) (SExp as)) = n ++ args as
--render (DesExp _ d as inner) = render inner ++ "." ++ d ++ args as
