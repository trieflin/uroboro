module Uroboro.PrettyPrinterEST where

import Data.List (intercalate)
import Uroboro.ExternalSyntax

parens :: [String]  -> String
parens s = "(" ++ commaSep s ++ ")"

opt fun ls = if null ls then "" else fun ls

angles :: [Abs]  -> String
angles s = "<" ++ commaSep (map absAbs s) ++ ">"

brackets :: [Type]  -> String
brackets s = "[" ++ commaSep (map renderType s) ++ "]"

commaSep :: [String] -> String
commaSep = intercalate ", " -- sls


sid id taps fun args = idId id ++ opt brackets taps ++ parens (map fun args)

renderType :: Type -> String
renderType (TypeVar _ id) = id
renderType (TypeT _ tau taps) = tauTau tau ++ brackets taps

renderDef :: Def -> String
renderDef def = 
    let abss = defAbs def in
    let (keyword, top, ls) = case defNature def of 
               DatDefNature tau cSigs  -> ("data", tauTau tau ++ opt angles abss, map renderSig cSigs)
               CodDefNature tau dSigs  -> ("codata", tauTau tau ++ opt angles abss, map renderSig dSigs)
               FunDefNature fSig rules -> ("function", opt angles abss ++ renderSig fSig, map renderRule rules)
    in keyword ++ " " ++ top ++ " where\n" ++ foldl (\l x -> l ++ "    " ++ x ++ "\n") "" ls

renderSig :: Sig a => a -> String
renderSig sig = 
    let prefix = case sigNature sig of 
                   DesSigNature fst -> renderType fst ++ "."
                   _                -> ""
    in prefix ++ idId (sigId sig) ++ parens (map renderType (sigArgs sig)) ++ " : "  ++ renderType (sigRet sig)

renderRule :: Rule -> String
renderRule rule = 
    let cop = ruleCop rule in
    let exp = ruleExp rule in
    let dcopsopt = case copNature cop of 
                     AppCopNature -> ""
                     DesCopNature dcops -> foldl (\l (DApsCop _ id taps pats) -> l ++ "." ++ sid id taps renderPat pats) "" dcops
                     in
    idId (copId cop) ++ parens (map renderPat (copArgs cop)) ++ dcopsopt ++ " = " ++ renderExp (ruleExp rule)

renderPat :: Pat -> String
renderPat (VarPat _ id) = idId id
renderPat (AppPat _ id taps pats) = sid id taps renderPat pats

renderExp :: Exp -> String
renderExp (Expr e) = renderExpF e
renderExp (DesExp _ expF dexps) = renderExpF expF ++ foldl (\l (DExp _ id taps exps) -> l ++ "." ++ sid id taps renderExp exps) "" dexps 

renderExpF :: ExpF -> String
renderExpF (VarExp _ id) = idId id
renderExpF (AppExp _ id taps exps) = sid id taps renderExp exps
