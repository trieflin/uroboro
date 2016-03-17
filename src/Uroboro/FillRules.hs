module Uroboro.FillRules where

import Data.List (find, elemIndex)

import Control.Monad (foldM, zipWithM)
import qualified Uroboro.ExternalSyntax as EST
import Uroboro.InternalSyntax
import Uroboro.TransformExtToInt 
import Uroboro.Error
import Uroboro.Location


typingError loc = failAt (unhide loc) "TypingError" -- msg
tyErrIdMismatch loc expId actId = 
    typingError loc $ "Definition Mismatch in rule: \n"
                   ++ "expected identifier " ++ show expId ++"\n"
                   ++ "actual identifier " ++ show actId
tyErrTyMismatch loc expTy actTy = 
    typingError loc $ "Type Mismatch: \n"
                   ++ "expected type " ++ show expTy ++"\n"
                   ++ "actual type " ++ show actTy ++ "."
tyErrUnbound loc var = 
    typingError loc $ "Not in scope: " ++ show var ++ "."
tyErrLenMismatch loc = typingError loc "Length Mismatch in arguments"

-- typingError loc $ "The function ‘" ++ (sigName sig) ++ "’ is applied to " ++ act ++" arguments, but its type " ++ sig ++ " has only " ++ (length (sigArgs sig))


-- each rule is checked and inserted if valid          
fillRules :: Program -> EST.Def -> Either Error Program
fillRules prog (EST.Def _ abss (EST.FunDefNature (EST.FunSig _ estId _ _ _) ruls))
    = foldM (fillRule (map toAbs abss)) prog ruls 
fillRules prog _ = Right prog

-- precondition: sigma is filled: all types are known
fillRule :: TypeAbstractions -> Program -> EST.Rule -> Either Error Program
fillRule abss prog (EST.Rule _ cop exps) = do  
    let absctx = map TypeBind abss -- abstractions inserted in typing context
    (tcop,copctx) <- fillCop (prgSigma prog) absctx cop -- check all subexpressions of left hand side and extend the corresponding context
    let retTy = case copNature tcop of
                AppCop       -> snd (copIdTy tcop)
                DesCop dcops -> snd (copIdTy (last dcops))
    texp <- fillExp (prgSigma prog) copctx retTy exps
    return prog { prgRules = (abss, tcop, texp) : prgRules prog }

-- |Typecheck a copattern. Takes hole type.            
fillCop :: Sigma -> Context -> EST.Cop -> Either Error (Cop, Context)   
fillCop sgm ctx cop = do
-- (ident, expArgTypes, expRetTy) <- getTyInfos sgm estId (map fromAbs2Typevar abss)
    let ident = toIdent (EST.copId cop)
    (expArgTypes, expRetTy) <- maybeToEither (lookupTypInfosForId sgm) ident 
    (pargs, ctx1) <- zipArgsWithItsTypes (EST.copLoc cop) (fillPat sgm) ctx (EST.copArgs cop) expArgTypes
--  eval(Exp[A]) : A
    sgm1 <- checkIsSameType (EST.copLoc cop) sgm ctx expRetTy expRetTy -- GADT: latest: inferred by eq in ctx or extra ret ty?
    case EST.copNature cop of 
        EST.AppCopNature -> return (Cop (EST.copLoc cop) (ident, expRetTy) pargs AppCop, ctx1)
        EST.DesCopNature dcops -> do
            (inners, ctx2, rt) <- foldM (fillDCop sgm) ([], ctx1, expRetTy) dcops  
            return (Cop (EST.copLoc cop) (ident, rt) pargs (DesCop (reverse inners)), ctx2)

fillDCop :: Sigma -> ([Cop], Context, Type) -> EST.DApsCop -> Either Error ([Cop], Context, Type)
fillDCop sgm (cps, ctx, t) (EST.DApsCop loc estId estApss args) = do
    (ident, expArgTypes, expRetTy) <- getTyInfos sgm estId estApss
    (pargs, ctx1) <- zipArgsWithItsTypes loc (fillPat sgm) ctx args (tail expArgTypes)    
    sgm1 <- checkIsSameType loc sgm ctx1 t (head expArgTypes) 
  --  sgm2 <- checkIsNegType sgm ident      
    return (Cop loc (ident, expRetTy) pargs AppCop : cps, ctx1, expRetTy)
-- TODO: merge together

-- |Typecheck a pattern
fillPat :: Sigma -> Context -> Type -> EST.Pat -> Either Error (Pat, Context)
fillPat sgm ctx expTy (EST.VarPat loc estId) = do
    let ident = toIdent estId
    let ctx1 = addFrame2Ctx (TermBind (ident, expTy)) ctx
    -- ident already in ctx with different type as actTy?
    actTy <- getActTy ident ctx1
    sgm1 <- checkIsSameType loc sgm ctx1 expTy actTy
    return (Pat loc (ident, expTy) VarPat, ctx1)       
fillPat sgm ctx expTy (EST.AppPat loc estId estApss args) = do
    (ident, expArgTypes, expRetTy) <- getTyInfos sgm estId estApss
    sgm1 <- checkIsSameType loc sgm ctx expTy expRetTy
    (pargs,ctx1) <- zipArgsWithItsTypes loc (fillPat sgm1) ctx args expArgTypes
    return (Pat loc (ident, expRetTy) (AppPat pargs), ctx1)
        
fillExp :: Sigma -> Context -> Type -> EST.Exp -> Either Error Exp
fillExp sgm ctx ty (EST.Expr (EST.VarExp loc estId)) = do 
    let ident = toIdent estId
    t <- getActTy ident ctx
    sgm1 <- checkIsSameType loc sgm ctx t ty
    return $ Exp loc (ident, ty) VarExp
fillExp sgm ctx ty (EST.Expr (EST.AppExp loc estId estApss args)) = do
    (ident,expArgTypes, expRetTy) <- getTyInfos sgm estId estApss
    pargs <- zipArgsWithItsTypesMap loc (fillExp sgm ctx) args expArgTypes
    sgm1 <- checkIsSameType loc sgm ctx ty expRetTy
    return $ Exp loc (ident, expRetTy) (SExp pargs)
fillExp sgm ctx ty (EST.DesExp loc fst dess@((EST.DExp l estId estApss estArgs):lst)) = do
    (ident, expArgTypes, expRetTy) <- getTyInfos sgm estId estApss --TODO expRetTy?
    ist_fst <- fillExp sgm ctx (head expArgTypes) (EST.Expr fst)
    exp <- foldM (fillDExp sgm ctx) ist_fst dess
    sgm1 <- checkIsSameType loc sgm ctx ty (snd (expIdTy exp))       
    return exp

fillDExp :: Sigma -> Context -> Exp -> EST.DExp -> Either Error Exp
fillDExp sgm ctx ist_fst@(Exp eLoc eIdTy eNature) (EST.DExp loc estId estApss args) = do
    (ident, expArgTypes, expRetTy) <- getTyInfos sgm estId estApss
    pargs <- zipArgsWithItsTypesMap loc (fillExp sgm ctx) args (tail expArgTypes)    
    sgm1 <- checkIsSameType loc sgm ctx (snd eIdTy) (head expArgTypes)         
    return (Exp loc (ident, expRetTy) (SExp (ist_fst : pargs))) 

-- |Infer the type of a term.
inferExp :: Program -> Context -> EST.Exp -> Either Error Exp
inferExp _ ctx (EST.Expr (EST.VarExp loc name)) = do
    let ident = toIdent name
    ty <- getActTy ident ctx
    return (Exp loc (ident,ty) VarExp)
inferExp prog ctx (EST.Expr (EST.AppExp loc estId estApss args)) = do
    let sgm = prgSigma prog
    (ident, expArgTypes, expRetTy) <- getTyInfos sgm estId estApss
    pargs <- zipArgsWithItsTypesMap loc (fillExp sgm ctx) args expArgTypes
    return $ Exp loc (ident, expRetTy) (SExp pargs)
inferExp prog ctx (EST.DesExp loc fst dess@((EST.DExp l estId estApss estArgs):lst)) = do
    let sgm = prgSigma prog
    (ident, expArgTypes, expRetTy) <- getTyInfos sgm estId estApss
    ist_fst <- fillExp sgm ctx (head expArgTypes) (EST.Expr fst)
    foldM (fillDExp sgm ctx) ist_fst dess
    

-- left to right evaluation for context
zipStrict :: Hidden Location -> [a] -> [b] -> Either Error [(a,b)]
zipStrict loc as bs 
    | length as == length bs = return $ zip as bs
    | otherwise              = tyErrLenMismatch loc

zipArgsWithItsTypes :: Hidden Location -> (Context -> Type -> a -> Either Error (b,Context)) -> Context -> [a] -> [Type] -> Either Error ([b], Context)          
zipArgsWithItsTypes loc f ctx as ts = do
    asts <- zipStrict loc as ts
    foldM (\(ps,c) (a,t) -> do (p,c2) <- f c t a; return (p:ps,c2)) ([], ctx) asts 

zipArgsWithItsTypesMap' :: Hidden Location -> (Context -> Type -> a -> Either Error b) -> Context -> [a] -> [Type] -> Either Error ([b], Context)     
zipArgsWithItsTypesMap' loc f ctx as ts = do
    asts <- zipStrict loc as ts
    targs <- mapM (\(a,t) -> f ctx t a) asts
    return (targs,ctx)


zipArgsWithItsTypesMap :: Hidden Location -> (Type -> a -> Either Error b) -> [a] -> [Type] -> Either Error [b]        
zipArgsWithItsTypesMap loc f as ts = do
    asts <- zipStrict loc as ts
    mapM (\(a,t) -> f t a) asts

replaceTyAbs :: TypeAbstractions -> [Type] -> Type -> Either Error Type
replaceTyAbs abss apss t@(Typevar loc x) = case elemIndex t (map fromAbs2Typevar abss) of
    Nothing             -> return t
    Just i 
      | length abss /= length apss -> tyErrLenMismatch loc
      | otherwise                  -> return ((!!) apss i)
replaceTyAbs abss apss t@(TypeT loc tau aps) = do 
    repAbs <- mapM (replaceTyAbs abss apss) aps
    return $ TypeT loc tau repAbs

replaceByIdAps :: Sigma -> Identifier -> TypeApplications -> Either Error ([Type] , Type)
replaceByIdAps sgm ident apss = do -- empty []; sig=<T> empty() : List[T]
    sig     <- maybeToEither (lookup1Sig sgm) ident
    repArgs <- mapM (replaceTyAbs (sigAbs sig) apss) (sigArgs sig)
    repRet  <- replaceTyAbs (sigAbs sig) apss (sigRet sig)
    return (repArgs, repRet)

maybeToEither :: (Identifier -> Maybe a) -> Identifier -> Either Error a
maybeToEither lookupFun ident
    | Just val <- lookupFun ident = return val
    | otherwise                   = tyErrUnbound (idLoc ident) ident

getTyInfos sgm estId estApss = do
    let ident = toIdent estId 
    let apss = map ( transformType sgm [] . toType) estApss
    (expArgTypes, expRetTy) <- replaceByIdAps sgm ident apss
    return (ident, expArgTypes, expRetTy)

getActTy ident ctx = do
  (ident, t) <- maybeToEither (lookupCtxTyBind ctx) ident
  return t
  
checkIsSameType :: Hidden Location -> Sigma -> Context -> Type -> Type -> Either Error Sigma
checkIsSameType loc sgm ctx expTy actTy = case (expTy, actTy) of
    (TypeT _ tau1 taps1, TypeT _ tau2 taps2)  
        | tau1 /= tau2 -> tyErrTyMismatch loc expTy actTy 
        | otherwise    -> do _ <- zipArgsWithItsTypesMap loc (checkIsSameType loc sgm ctx) taps2 taps1
                             return sgm
    (Typevar _ v1, Typevar _ v2) 
        | actTy `notElem` [ fromAbs2Typevar x | TypeBind x <- ctx] 
                       -> tyErrTyMismatch loc expTy actTy 
        | otherwise    -> return sgm
    _                  -> tyErrTyMismatch loc expTy actTy 
                                    