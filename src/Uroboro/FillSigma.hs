module Uroboro.FillSigma where

import Control.Monad (foldM)
import qualified Uroboro.ExternalSyntax as EST
import Uroboro.InternalSyntax
import Uroboro.TransformExtToInt 
import Uroboro.Error
import Uroboro.Location

typingError loc = failAt loc "TypingError" 
tyErrMultDecl loc def locs = typingError loc $ "Multiple declarations of ‘" ++ def ++ "’. Declared at:\n " ++ locs ++ "."
tyErrDuplTySigs loc ident locs = typingError loc $ "Duplicate type signatures for ‘" ++ ident ++ "’. Declared at:\n " ++ locs ++ "."
tyErrUnbound loc unbound = typingError loc $ "Not in scope: " ++ unbound
tyErrDefMismatch loc def exp act = typingError loc $ "Definition Mismatch in " ++ def ++ ".\n  Expected " ++ exp ++ "\n  but is " ++ act ++ "."
tyErrLenMismatch loc exp act = typingError loc $ "Typing Argument Mismatch, expected " ++ exp ++ " arguments, but got " ++ act ++ "."
tyErrAbs loc abss ident = typingError loc $ "Shadowed type abstractions (" ++ show abss ++ ") by " ++ ident ++ "."
tyErrTauIsTypevar loc tau tyvar = typingError loc $ "Mismatch between type variable " ++ tyvar ++ " and type name " ++ tau ++ "."
 
fillSigma :: Sigma -> EST.Def -> Either Error Sigma
fillSigma sgm def = do
    sgm0 <- shadowedTauSig sgm def
    mismatch' sgm0 def

shadowedAbs :: Sigma -> Location -> TypeAbstractions -> String -> Either Error Sigma
shadowedAbs sgm loc abss ident 
    | ident `elem` map absAbs abss = tyErrAbs loc abss ident
    | otherwise                    = return sgm

--tauIsInTypevar :: String -> Sigma -> EST.Type -> Either Error Sigma
--tauIsInTypevar tau sgm ty = case ty of
  --  EST.TypeVar loc tv -> if tau == tv 
    --                  then tyErrTauIsTypevar loc tau tv
      --                else return sgm
  --  EST.TypeT _ tau apss  -> foldM (tauIsInTypevar tau) sgm apss                
--

shadowedTauSig :: Sigma -> EST.Def -> Either Error Sigma
shadowedTauSig sgm def@(EST.Def loc abss (EST.DatDefNature tau sigs))
    | not $ null shadowedList = tyErrMultDecl loc (show def) (show shadowedList)
    | otherwise = do
        sgm0 <- shadowedAbs sgm loc (map toAbs abss) (EST.tauTau tau)
        sgm1 <- foldM (shadowedConSig abss) sgm0 sigs
        return sgm1{sgmTypeNames = toTauAbs tau abss : sgmTypeNames sgm1 }
    where 
        shadowedList = lookupNameForLoc sgm (EST.tauTau tau)--(EST.tauAbsTau tauabs)
shadowedTauSig sgm def@(EST.Def loc abss (EST.CodDefNature tau sigs))
    | not $ null shadowedList = tyErrMultDecl loc (show def) (show shadowedList)
    | otherwise = do
        sgm0 <- shadowedAbs sgm loc (map toAbs abss) (EST.tauTau tau)
        sgm1 <- foldM (shadowedDesSig abss) sgm0 sigs
        return sgm1{sgmTypeNames = toTauAbs tau abss : sgmTypeNames sgm1 }
    where 
        shadowedList = lookupNameForLoc sgm (EST.tauTau tau)
shadowedTauSig sgm def@(EST.Def loc abss (EST.FunDefNature sig@(EST.FunSig _ estId _ _ _) rules))
    | not $ null shadowedList = tyErrMultDecl loc (show def) (show shadowedList)
    | otherwise = do
        sgm0 <- shadowedAbs sgm loc (map toAbs abss) (EST.idId estId)
        shadowedFunSig abss sgm sig rules
    where 
        shadowedList = lookupNameForLoc sgm (EST.idId estId)

shadowedConSig :: EST.TypeAbstractions -> Sigma -> EST.ConSig -> Either Error Sigma
shadowedConSig abss sgm estSig@(EST.ConSig loc ident args ret _)
    | not $ null shadowedList = tyErrDuplTySigs loc (EST.idId ident) (show shadowedList)
    | otherwise = return sgm{ sgmSigs = toConSigs True abss estSig : sgmSigs sgm }
    where
        shadowedList = lookupNameForLoc sgm (EST.idId ident)              
shadowedDesSig :: EST.TypeAbstractions -> Sigma -> EST.DesSig -> Either Error Sigma
shadowedDesSig abss sgm estSig@(EST.DesSig loc ident _ _ _)
    | not $ null shadowedList = tyErrDuplTySigs loc (EST.idId ident) (show shadowedList)
    | otherwise = return sgm{ sgmSigs = toDesSigs True abss estSig : sgmSigs sgm }
    where
        shadowedList = lookupNameForLoc sgm (EST.idId ident) 
shadowedFunSig :: EST.TypeAbstractions -> Sigma -> EST.FunSig -> [EST.Rule]  -> Either Error Sigma
shadowedFunSig abss sgm estSig@(EST.FunSig loc ident _ _ _) rules
    | not $ null shadowedList =tyErrDuplTySigs loc (EST.idId ident) (show shadowedList)
    | otherwise = Right sgm{ sgmSigs = toFunSigs (any EST.checkNeg rules) abss estSig : sgmSigs sgm }
    where
        shadowedList = lookupNameForLoc sgm (EST.idId ident)     

mismatch' :: Sigma -> EST.Def -> Either Error Sigma
mismatch' sgm def 
    = case def of
        EST.Def loc abss (EST.DatDefNature tau sigs) -> mis (loc, fromTauAbs2Type tau abss, map (toType . EST.cSigRet) sigs)
        EST.Def loc abss (EST.CodDefNature tau sigs)  -> mis (loc, fromTauAbs2Type tau abss, map toType [t | EST.DesSigNature t <- (map EST.dSigNature sigs)])
        EST.Def loc _ (EST.FunDefNature (EST.FunSig _ ident _ _ _) ruls) -> mis (loc, ident, map (EST.copId . EST.ruleCop) ruls)
    where 
        mis :: Eq a => Show a => (Location , a , [a]) -> Either Error Sigma
        mis(loc, fact, check) = let mismatchls = filter (/= fact) check in
                                if null mismatchls
                                then return sgm
                                else tyErrDefMismatch loc (show def) (show fact) (show mismatchls)

        
checkSigma :: Sigma -> Either Error Sigma    
checkSigma sgm0 = do
    let sgm = transformTypevarToTypeT sgm0
    foldM checkSig sgm (sgmSigs sgm)
    where 
        checkSig sgma Sig{sigAbs = abss, sigLoc=loc, sigArgs=args, sigRet=ret} = foldM (checkIsType loc abss) sgma (ret:args)

transformTypevarToTypeT :: Sigma -> Sigma    
transformTypevarToTypeT sgm = sgm{ sgmSigs = map transformSig (sgmSigs sgm) }
    where
        transformSig sig@Sig{sigArgs=args, sigRet=ret} = sig{sigArgs=map transformType args, sigRet=transformType ret}
        transformType ty = case ty of
            Typevar lt tv ->
                if tv `elem` [tauTau tau | TauAbs tau _ <- sgmTypeNames sgm]
                then TypeT lt (Tau lt tv) []   
                else ty
            TypeT lt tau aps -> TypeT lt tau $ map transformType aps

checkIsType :: Location -> TypeAbstractions -> Sigma -> Type -> Either Error Sigma
checkIsType loc abss sgm ty 
    = case ty of 
        Typevar _ tv -> 
            if ty `notElem` map fromAbs2Typevar abss 
            then tyErrUnbound loc (show ty)
            else return sgm
                --if tv `elem` map absAbs abss 
                 --then tyErrAbs loc abss tv
                 --else return sgm
        TypeT _ tau aps -> case lookup1TauAbs sgm tau of
            Nothing -> tyErrUnbound loc (show ty) 
            Just (TauAbs _ tabss) ->
                 if length tabss /= length aps 
                 then tyErrLenMismatch loc (show (length tabss)) (show (length aps))
                 else if tauTau tau `elem` map absAbs tabss
                      then tyErrAbs loc tabss (tauTau tau)
                      else foldM (checkIsType loc abss) sgm aps 