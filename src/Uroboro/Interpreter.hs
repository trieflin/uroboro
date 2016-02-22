{-|
Description : Evaluate Uroboro
Define the operational semantics and reduce terms.
-}
--module Uroboro.Interpreter
module Uroboro.Interpreter 
    ( 
      eval
    , pmatch
    ) where

import Control.Monad (foldM, zipWithM)
import Data.Either (rights)

import Uroboro.InternalSyntax

-- |Evaluation contexts.
data E = EApp Type [Exp]
       | EDes Type Identifier [Exp] E deriving (Show, Eq)

-- |Result of a pattern match.
type Substitution = [(Identifier, Exp)]

-- |Pattern matching.
pmatch :: Exp -> Pat -> Either String Substitution
pmatch (Exp _ _ VarExp) _    = error "Substitute variables before trying to match"
pmatch term (Pat _ (x,r) VarPat)
    | snd (expIdTy term) /= r   = Left "Type Mismatch"
    | otherwise              = return [(x, term)]
pmatch (Exp _ (c,r) (SExp ts)) (Pat _ (c',r') (AppPat ps))--(ConExp r c ts) (ConPat r' c' ps)
    | r /= r'                = Left "Type Mismatch"
    | c /= c'                = Left $
        "Name Mismatch: constructor " ++ (idId c') ++ " doesn't match pattern " ++ (idId c)
    | length ts /= length ps = Left "Argument Length Mismatch" --should not occur -> typing
    | otherwise              = zipWithM pmatch ts ps >>= return . concat
pmatch _ _                   = Left "Not Comparable"

-- |Copattern matching.
qmatch :: E -> Cop -> Either String Substitution
qmatch (EApp r as) (Cop _ (_, r') ps AppCop)
    | r /= r'                = error "Type checker guarantees hole type"
    | length as /= length ps = Left "Argument Length Mismatch"
    | otherwise              = zipWithM pmatch as ps >>= return . concat
qmatch (EDes r d as inner) (Cop _ (d',r') ps (DesCop inner'))
    | r /= r'                = Left "Type Mismatch"
    | d /= d'                = Left "Name Mismatch"
    | length as /= length ps = Left "Argument Length Mismatch"
    | otherwise              = do
        is <- qmatch inner (head inner') --TODO
        ss <- zipWithM pmatch as ps
        return $ is ++ concat ss
qmatch _ _                   = Left "Not Comparable"

-- |Substitute all occurences.
subst :: Exp -> (Identifier, Exp) -> Exp
subst t@(Exp _ (n',_) VarExp) (n, term)
    | n == n'               = term
    | otherwise             = t
subst (Exp t n (SExp as)) s       = Exp t n (SExp (map (flip subst s) as))

-- |If context matches rule, apply it.
contract :: E -> Rule -> Either String Exp
contract hole (abss, cop, term) = do
    s <- qmatch hole cop
    return $ foldl subst term s

-- |Find hole.
reducible :: Exp -> Either String (E, Identifier)  -- Could be Maybe.
reducible (Exp _ (f,r) (SExp args)) = return (EApp r args, f)
reducible (Exp _ (d,r) (SExp (inner:args))) = do
    (inner', f) <- reducible inner
    return (EDes r d args inner', f)
reducible t = Left $ "Not a redex: " ++ show t

-- |Star reduction.
eval :: [Rule] -> Exp -> Exp
eval _ e@(Exp _ _ VarExp)  = e
eval r (Exp l (c, t) (SExp as)) = Exp l (c, t) (SExp (map (eval r) as))
eval r (Exp l (f, t) (SExp as)) = 
    let rf = [ rule | rule@(tabs,cop,exp) <- r, fst (copIdTy cop) == f] in
    case rights $ map (contract con) rf of
        (e':_) -> eval r e'
        _    -> es
-- case lookup f r of
--    Nothing -> error "Did you type-check?"
 --   Just rf -> case rights $ map (contract con) rf of
   --     (e':_) -> eval r e'
     --   _    -> es
  where
    as' = map (eval r) as
    es  = Exp l (f,t) (SExp as')
    con = EApp t as'
eval r (Exp l (n,t) (SExp (inner:args))) = case reducible es of     -- TODO factor out.
    Left _         -> error "Did you type-check?"
    Right (con, f) -> 
     let rf = [ rule | rule@(tabs,cop,exp) <- r, fst (copIdTy cop) == f] in
     case rights $ map (contract con) rf of
            (e':_) -> eval r e'
            _    -> es
  where
    args'  = map (eval r) args
    inner' = eval r inner
    es     = Exp l (n, t) (SExp (inner':args'))