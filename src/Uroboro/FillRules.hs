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


-- every rule in the program is checked and inserted if valid          
fillRules :: Program -> EST.Def -> Either Error Program
fillRules prog (EST.Def _ abss (EST.FunDefNature (EST.FunSig _ estId _ _ _) ruls))
    = foldM (fillCheckedRule (map toAbs abss)) prog  ruls 
    where 
        fillCheckedRule absls p r@(EST.Rule locr cop _) 
            = do mismatchCop p locr (EST.copId cop); fillRule absls p r
        mismatchCop prg locr copId -- not needed if mismatch' from FillSigma is used
            | estId /= copId = tyErrIdMismatch locr estId copId
            | otherwise = Right prg        
fillRules prog _ = Right prog

-- precondition: sigma is filled, so all types are known
fillRule :: TypeAbstractions -> Program -> EST.Rule -> Either Error Program
fillRule abss prog (EST.Rule _ cop exps) = do  
    let absctx = map TypeBind abss -- abstractions inserted in typing context
    (tcop,copctx) <- fillCop (prgSigma prog) absctx cop -- check all subexpressions of left hand side and extend the corresponding context
    let retTy = case copNature tcop of
                AppCop       -> snd (copIdTy tcop)
                DesCop dcops -> snd (copIdTy (last dcops))
    texp <- fillExp (prgSigma prog) copctx retTy exps
    return prog { prgRules = (abss, tcop, texp) : prgRules prog }

transformTypevarToTypeT :: Sigma -> Type -> Type    
transformTypevarToTypeT sgm ty = case ty of
    Typevar lt tv ->
                if tv `elem` [tauTau tau | TauAbs tau _ <- sgmTypeNames sgm]
                then TypeT lt (Tau lt tv) []   
                else ty
    TypeT lt tau aps -> TypeT lt tau $ map (transformTypevarToTypeT sgm) aps


-- |Typecheck a copattern. Takes hole type.            
fillCop :: Sigma -> Context -> EST.Cop -> Either Error (Cop, Context)   
fillCop sgm ctx cop = do
    let ident = toIdent (EST.copId cop)
    (expectedArgsTypes, expectedRetTy) <- getTypeInfos sgm ident (EST.copLoc cop)
    (pargs, ctx1) <- zipArgsWithItsTypes (EST.copLoc cop) (fillPat sgm) ctx (EST.copArgs cop) expectedArgsTypes
    case EST.copNature cop of 
                EST.AppCopNature -> return (Cop (EST.copLoc cop) (ident, expectedRetTy) pargs AppCop, ctx1)
                EST.DesCopNature dcops -> do
                                (inners, ctx2, rt) <- foldM (fillDCop sgm) ([], ctx1, expectedRetTy) dcops  
                                return (Cop (EST.copLoc cop) (ident, rt) pargs (DesCop (reverse inners)), ctx2)
--f().d1().d2().d3()
--fret [d1,d2,d3]

fillDCop :: Sigma -> ([Cop], Context, Type) -> EST.DApsCop -> Either Error ([Cop], Context, Type)
fillDCop sgm (cps, ctx, t) (EST.DApsCop loc estid estapss args) = do
    let ident = toIdent estid 
    let apss = map (transformTypevarToTypeT sgm . toType) estapss
    (expectedArgsTypes, expectedRetTy) <- replaceByIdAps sgm ident apss
    (pargs, ctx1) <- zipArgsWithItsTypes loc (fillPat sgm) ctx args (tail expectedArgsTypes)    
    sgm1 <- checkIsSameType loc sgm ctx1 t (head expectedArgsTypes) 
  --  sgm2 <- checkIsNegType sgm ident      
    return (Cop loc (ident, expectedRetTy) pargs AppCop : cps, ctx1, expectedRetTy)
-- TODO: merge together

--checkIsNegType :: Sigma -> Identifier -> Either Error Sigma
--checkIsNegType sgm ident = case lookup1SigAps sgm ident of
  --    Just sig -> do
    --    if (sigNature sig) == Neg
      --  then return sgm
     --   else tyErrUnbound (idLoc ident) "TODO: new error message..."
    --  Nothing -> tyErrUnbound (idLoc ident) (idId ident)


-- |Typecheck a pattern
fillPat :: Sigma -> Context -> Type -> EST.Pat -> Either Error (Pat, Context)
fillPat sgm ctx expTy (EST.VarPat loc estId) = do
    let ident = toIdent estId
    let ctx1 = addFrame2Ctx (TermBind (ident, expTy)) ctx
    -- estId already in ctx with different type named as actTy?
    actTy <- case lookupCtxTyBind ctx1 ident of
                  Nothing     -> tyErrUnbound loc ident
                  Just (id,t) -> return t
    sgm1 <- checkIsSameType loc sgm ctx1 expTy actTy
    return (Pat loc (ident, expTy) VarPat, ctx1)       
fillPat sgm ctx expTy (EST.AppPat loc estid estapss args) = do
    let ident = toIdent estid
    let apss = map ((transformTypevarToTypeT sgm). toType)  estapss
    (rargs, rret) <- replaceByIdAps sgm ident apss
    sgm1 <- checkIsSameType loc sgm ctx expTy rret
    (pargs,ctx1) <- zipArgsWithItsTypes loc (fillPat sgm1) ctx args rargs
    return (Pat loc (ident, rret) (AppPat pargs), ctx1)

        
fillExp :: Sigma -> Context -> Type -> EST.Exp -> Either Error Exp
fillExp sgm ctx ty (EST.Expr (EST.VarExp loc estId)) = do 
    let ident = toIdent estId
    case lookupCtxTyBind ctx ident of
        Nothing -> tyErrUnbound loc ident
        Just (id, ty') -> do 
            sgm1 <- checkIsSameType loc sgm ctx ty ty
            return $ Exp loc (ident, ty) VarExp
fillExp sgm ctx ty (EST.Expr (EST.AppExp loc estId estApss args)) = do
    let ident = toIdent estId
    let apss = map ((transformTypevarToTypeT sgm). toType) estApss
    (rargs, rret) <- replaceByIdAps sgm ident apss
    pargs <- zipArgsWithItsTypesMap loc (fillExp sgm ctx) args rargs
    sgm1 <- checkIsSameType loc sgm ctx ty rret
    return $ Exp loc (ident, ty) (SExp pargs)
fillExp sgm ctx ty (EST.DesExp loc fst dess@((EST.DExp l' id' apss' args'):lst)) = do
    let ident = toIdent id'
    let apss = map ((transformTypevarToTypeT sgm). toType)  apss'
    (expectedArgsTypes, _) <- replaceByIdAps sgm ident apss
    ist_fst <- fillExp sgm ctx (head expectedArgsTypes) (EST.Expr fst)
    exp <- foldM (fillDExp sgm ctx) ist_fst dess
    sgm1 <- checkIsSameType loc sgm ctx ty (snd (expIdTy exp))       
    return exp

fillDExp :: Sigma -> Context -> Exp -> EST.DExp -> Either Error Exp
fillDExp sgm ctx ist_fst@(Exp eLoc eIdTy eNature) (EST.DExp loc estid estapss args) = do
    let ident = toIdent estid
    let apss = map ((transformTypevarToTypeT sgm). toType) estapss
    (expectedArgsTypes, expectedRetTy) <- replaceByIdAps sgm ident apss
    pargs <- zipArgsWithItsTypesMap loc (fillExp sgm ctx) args (tail expectedArgsTypes)    
    sgm1 <- checkIsSameType loc sgm ctx (snd eIdTy) (head expectedArgsTypes)         
    return (Exp loc (ident, expectedRetTy) (SExp (ist_fst : pargs))) 

-- |Infer the type of a term.
inferExp :: Program -> Context -> EST.Exp -> Either Error Exp
inferExp _ ctx (EST.Expr (EST.VarExp loc name)) = do
    let ident = toIdent name
    case lookupCtxTyBind ctx ident of
        Nothing  -> tyErrUnbound loc ident
        Just idty -> return (Exp loc idty VarExp)
inferExp prog ctx (EST.Expr (EST.AppExp loc estId estApss args)) = do
    let sgm = prgSigma prog
    let ident = toIdent estId
    let apss = map ((transformTypevarToTypeT sgm). toType)  estApss
    (rargs, rret) <- replaceByIdAps sgm ident apss
    pargs <- zipArgsWithItsTypesMap loc (fillExp sgm ctx) args rargs
    return $ Exp loc (ident, rret) (SExp pargs)
inferExp prog ctx (EST.DesExp loc fst dess@((EST.DExp l' id' apss' args'):lst)) = do
    let sgm = prgSigma prog
    let ident = toIdent id'
    let apss = map ((transformTypevarToTypeT sgm). toType)  apss'
    (expectedArgsTypes, _) <- replaceByIdAps sgm ident apss
    ist_fst <- fillExp sgm ctx (head expectedArgsTypes) (EST.Expr fst)
    exp <- foldM (fillDExp sgm ctx) ist_fst dess
    return exp


-- left to right evaluation for context
zipStrict :: Hidden Location -> [a] -> [b] -> Either Error [(a,b)]
zipStrict loc as bs 
    | length as == length bs = return $ zip as bs
    | otherwise              = tyErrLenMismatch loc


zipArgsWithItsTypes :: Hidden Location -> (Context -> Type -> a -> Either Error (b,Context)) -> Context -> [a] -> [Type] -> Either Error ([b], Context)          
zipArgsWithItsTypes loc f ctx as ts = do
    asts <- zipStrict loc as ts
    foldM (\(ps,c) (a,t) -> do (p,c2) <- f c t a; return (p:ps,c2)) ([], ctx) asts 

zipArgsWithItsTypesMap :: Hidden Location -> (Type -> a -> Either Error b) -> [a] -> [Type] -> Either Error [b]        
zipArgsWithItsTypesMap loc f as ts = do
    asts <- zipStrict loc as ts
    mapM (\(a,t) -> f t a) asts

replaceTyAbs :: TypeAbstractions -> [Type] -> Type -> Either Error Type
replaceTyAbs abss apss t 
    = case t of
        Typevar loc x -> case elemIndex t (map fromAbs2Typevar abss) of
                        Nothing -> return t
                        Just i -> if length apss < i
                                  then tyErrLenMismatch loc
                                  else return ((!!) apss i)
        TypeT loc tau aps -> do
            repAbs <- mapM (replaceTyAbs abss apss) aps
            return $ TypeT loc tau repAbs

replaceByIdAps :: Sigma -> Identifier -> TypeApplications -> Either Error ([Type] , Type)
replaceByIdAps sgm ident apss = 
    case (lookupTypInfosForId sgm ident, getLookup1For sigAbs sgm ident) of
      (Just (targs, ret), Just abss) -> do
        repArgs <- mapM (replaceTyAbs abss apss) targs
        repRet <- replaceTyAbs abss apss ret
        return (repArgs, repRet)
      (_,_) -> tyErrUnbound (idLoc ident) ident


getTypeInfos sgm ident loc = 
    case lookupTypInfosForId sgm ident of
        Just (expectedArgsTypes, expectedRetTy) -> Right (expectedArgsTypes, expectedRetTy)
        Nothing -> tyErrUnbound loc ident


checkIsSameType :: Hidden Location -> Sigma -> Context -> Type -> Type -> Either Error Sigma
checkIsSameType loc sgm ctx expTy actTy
    = case (expTy, actTy) of
        (TypeT _ tau1 taps1, TypeT _ tau2 taps2) -> if tau1 /= tau2
                then tyErrTyMismatch loc expTy actTy 
                else do _ <- zipArgsWithItsTypesMap loc (checkIsSameType loc sgm ctx) taps2 taps1
                        return sgm
        (Typevar _ v1, Typevar _ v2) -> 
                if actTy `notElem` [ fromAbs2Typevar x | TypeBind x <- ctx]
                then tyErrTyMismatch loc expTy actTy 
                else return sgm
        (_,_) -> tyErrTyMismatch loc expTy actTy 
                                    