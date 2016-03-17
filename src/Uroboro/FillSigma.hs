module Uroboro.FillSigma where

import Data.List (nub,(\\))
import Control.Monad (foldM)
import qualified Uroboro.ExternalSyntax as EST
import Uroboro.InternalSyntax
import Uroboro.TransformExtToInt 
import Uroboro.Error
import Uroboro.Location

typingError loc = failAt (unhide loc) "TypingError" 
tyErrDuplTySigs loc ident {- tau/identifier -} locs = typingError loc $ "Duplicate type signatures for ‘" ++ show ident ++ "’. Declared at:\n " ++ show locs ++ "."
tyErrDefMismatch loc exp act = typingError loc $ "Definition Mismatch.\n  Expected " ++ show exp ++ "\n  but is " ++ show act ++ "."
tyErrUnbound loc unbound {- type -} = typingError loc $ "Not in scope: " ++ show unbound
tyErrLenMismatch loc exp act = typingError loc $ "Typing Argument Mismatch, expected " ++ show exp ++ " arguments, but got " ++ show act ++ "."
tyErrAbs loc abss ident = typingError loc $ "Shadowed type abstractions (" ++ show abss ++ ") by " ++ show ident ++ "."
 
fillSigma :: Sigma -> EST.Def -> Either Error Sigma
fillSigma sgm def@(EST.Def loc abss nature)
    | not $ null shadowedList = tyErrDuplTySigs loc name shadowedList -- tau is not already a type
    | not $ null nubedabss    = tyErrAbs loc abss (head nubedabss) 
    | name `elem` map EST.absAbs abss = tyErrAbs loc abss name
    | otherwise               = sgm0
    where
      nubedabss = abss \\ nub abss
      addTauToSgm tau = sgm{sgmTypeNames = toTauAbs tau abss : sgmTypeNames sgm } 
      calcShadowedList tau = lookupNameForLoc sgm (EST.tauTau tau)
      fromTauAbs2Type estTau abss = TypeT (EST.tauLoc estTau) (toTau estTau) (map (fromAbs2Typevar . toAbs) abss)
      (shadowedList, name, sgm0) = case nature of
            EST.DatDefNature tau sigs  -> (calcShadowedList tau, EST.tauTau tau, foldM (fillSig abss True (fromTauAbs2Type tau abss) (map (toType . EST.cSigRet) sigs)) (addTauToSgm tau) sigs)
            EST.CodDefNature tau sigs  -> (calcShadowedList tau, EST.tauTau tau, foldM (fillSig abss False (fromTauAbs2Type tau abss) (map toType [t | EST.DesSigNature t <- map EST.dSigNature sigs])) (addTauToSgm tau) sigs)
            EST.FunDefNature sig rules -> ([],         EST.idId (EST.sigId sig),        fillSig abss (any EST.checkNeg rules) (EST.sigId sig) (map (EST.copId . EST.ruleCop) rules) sgm sig)

fillSig :: EST.Sig a => Eq b => Show b => EST.TypeAbstractions -> Bool -> b -> [b] -> Sigma -> a -> Either Error Sigma
fillSig abss isS0 fact check sgm estSig -- unique signature names
    | not $ null shadowedList = tyErrDuplTySigs (EST.sigLoc estSig) (EST.sigId estSig) shadowedList
    | not $ null mismatchls   = tyErrDefMismatch (EST.sigLoc estSig) fact mismatchls
    | otherwise = return sgm{ sgmSigs = toSig isS0 abss estSig : sgmSigs sgm }
    where
        shadowedList = lookupNameForLoc sgm (EST.idId (EST.sigId estSig))
        mismatchls = filter (/= fact) check 
  
        
checkSigma :: Sigma -> Either Error Sigma    
checkSigma sgm0 = do
    let sgm = transformTypevarToTypeT sgm0
    let checkSig sgma sig = foldM (checkIsType (sigLoc sig) (sigAbs sig)) sgma (sigRet sig:sigArgs sig) 
    foldM checkSig sgm (sgmSigs sgm)

transformTypevarToTypeT :: Sigma -> Sigma    
transformTypevarToTypeT sgm = 
    let transformSig sig = sig{sigArgs=map (transformType sgm (map absAbs (sigAbs sig))) (sigArgs sig), 
                               sigRet=transformType sgm (map absAbs (sigAbs sig)) (sigRet sig)}
    in sgm{ sgmSigs = map transformSig (sgmSigs sgm) }
  
checkIsType :: Hidden Location -> TypeAbstractions -> Sigma -> Type -> Either Error Sigma
checkIsType loc abss sgm ty@(Typevar _ tv)
    | ty `notElem` map fromAbs2Typevar abss = tyErrUnbound loc ty
    | otherwise                             = return sgm
checkIsType loc abss sgm ty@(TypeT _ tau aps) = case lookup1TauAbs sgm tau of
    Nothing -> tyErrUnbound loc ty        
    Just (TauAbs _ tabss) 
        | length tabss /= length aps         -> tyErrLenMismatch loc (length tabss) (length aps)
        | tauTau tau `elem` map absAbs tabss -> tyErrAbs loc tabss (tauTau tau)
        | otherwise                          -> foldM (checkIsType loc abss) sgm aps 
      