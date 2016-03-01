module Uroboro.FillSigma where

import Control.Monad (foldM)
import qualified Uroboro.ExternalSyntax as EST
import Uroboro.InternalSyntax
import Uroboro.TransformExtToInt 
import Uroboro.Error
import Uroboro.Location

typingError loc = failAt (unhide loc) "TypingError" 
tyErrDuplTySigs loc ident locs = typingError loc $ "Duplicate type signatures for ‘" ++ show ident ++ "’. Declared at:\n " ++ show locs ++ "."
tyErrUnbound loc unbound = typingError loc $ "Not in scope: " ++ show unbound
tyErrDefMismatch loc def exp act = typingError loc $ "Definition Mismatch in " ++ show def ++ ".\n  Expected " ++ show exp ++ "\n  but is " ++ show act ++ "."
tyErrLenMismatch loc exp act = typingError loc $ "Typing Argument Mismatch, expected " ++ show exp ++ " arguments, but got " ++ show act ++ "."
tyErrAbs loc abss ident = typingError loc $ "Shadowed type abstractions (" ++ show abss ++ ") by " ++ show ident ++ "."
tyErrTauIsTypevar loc tau tyvar = typingError loc $ "Mismatch between type variable " ++ show tyvar ++ " and type name " ++ show tau ++ "."
 
fillSigma :: Sigma -> EST.Def -> Either Error Sigma
fillSigma sgm def = do
    sgm0 <- shadowedTauSig sgm def
    mismatch' sgm0 def

shadowedTauSig :: Sigma -> EST.Def -> Either Error Sigma
shadowedTauSig sgm def@(EST.Def loc abss nature) = do
    let addTauToSgm tau = sgm{sgmTypeNames = toTauAbs tau abss : sgmTypeNames sgm } 
    let calcShadowedList tau = lookupNameForLoc sgm (EST.tauTau tau)
    let (shadowedList, sgm0, name) = case nature of
            EST.DatDefNature tau sigs  -> (calcShadowedList tau, foldM (shadowedSig abss True) (addTauToSgm tau) sigs, EST.tauTau tau)
            EST.CodDefNature tau sigs  -> (calcShadowedList tau, foldM (shadowedSig abss False) (addTauToSgm tau) sigs, EST.tauTau tau)
            EST.FunDefNature sig rules -> ([], shadowedSig abss (any EST.checkNeg rules) sgm sig, EST.idId (EST.sigId sig))   
    if not $ null shadowedList 
    then tyErrDuplTySigs loc name shadowedList
    else sgm0
    
shadowedSig :: EST.Sig a => EST.TypeAbstractions -> Bool -> Sigma -> a -> Either Error Sigma
shadowedSig abss isS0 sgm estSig
    | not $ null shadowedList = tyErrDuplTySigs (EST.sigLoc estSig) (EST.sigId estSig) shadowedList
    | otherwise = return sgm{ sgmSigs = toSig isS0 abss estSig : sgmSigs sgm }
    where
        shadowedList = lookupNameForLoc sgm (EST.idId (EST.sigId estSig))

mismatch' :: Sigma -> EST.Def -> Either Error Sigma
mismatch' sgm def 
    = case def of 
        EST.Def loc abss (EST.DatDefNature tau sigs) -> mis (loc, fromTauAbs2Type tau abss, map (toType . EST.cSigRet) sigs)
        EST.Def loc abss (EST.CodDefNature tau sigs) -> mis (loc, fromTauAbs2Type tau abss, map toType [t | EST.DesSigNature t <- map EST.dSigNature sigs])
        EST.Def loc _ (EST.FunDefNature (EST.FunSig _ ident _ _ _) ruls) -> mis (loc, ident, map (EST.copId . EST.ruleCop) ruls)
    where 
        mis :: Eq a => Show a => (Hidden Location , a , [a]) -> Either Error Sigma
        mis(loc, fact, check) = let mismatchls = filter (/= fact) check in
                                if null mismatchls
                                then return sgm
                                else tyErrDefMismatch loc def fact mismatchls

        
checkSigma :: Sigma -> Either Error Sigma    
checkSigma sgm0 = do
    let sgm = transformTypevarToTypeT sgm0
    foldM checkSig sgm (sgmSigs sgm)
    where 
        checkSig sgma Sig{sigAbs = abss, sigLoc=loc, sigArgs=args, sigRet=ret} = foldM (checkIsType loc abss) sgma (ret:args)

transformTypevarToTypeT :: Sigma -> Sigma    
transformTypevarToTypeT sgm = sgm{ sgmSigs = map transformSig (sgmSigs sgm) }
    where
        transformSig sig@Sig{sigArgs=args, sigRet=ret, sigAbs=abss} = 
            let sabs = map absAbs abss in 
            sig{sigArgs=map (transformType sabs) args, sigRet=transformType sabs ret}
        transformType sabs ty = case ty of
            Typevar lt tv ->
                if tv `notElem` sabs &&  tv `elem` [tauTau tau | TauAbs tau _ <- sgmTypeNames sgm]
                then TypeT lt (Tau lt tv) []   
                else ty
            TypeT lt tau aps -> TypeT lt tau $ map (transformType sabs) aps
            
checkIsType :: Hidden Location -> TypeAbstractions -> Sigma -> Type -> Either Error Sigma
checkIsType loc abss sgm ty 
    = case ty of 
        Typevar _ tv -> 
            if ty `notElem` map fromAbs2Typevar abss 
            then tyErrUnbound loc ty
            else return sgm
        TypeT _ tau aps -> case lookup1TauAbs sgm tau of
            Nothing -> tyErrUnbound loc ty
            Just (TauAbs _ tabss) ->
                 if length tabss /= length aps 
                 then tyErrLenMismatch loc (length tabss) (length aps)
                 else if tauTau tau `elem` map absAbs tabss
                      then tyErrAbs loc tabss (tauTau tau)
                      else foldM (checkIsType loc abss) sgm aps 