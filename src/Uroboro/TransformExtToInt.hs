module Uroboro.TransformExtToInt where

import qualified Uroboro.ExternalSyntax as EST
import Uroboro.InternalSyntax

toType :: EST.Type -> Type
toType (EST.TypeVar loc typname) = Typevar loc typname
toType (EST.TypeT loc tau aps) = TypeT loc (toTau tau) (map toType aps)

toAbs :: EST.Abs -> Abs
toAbs (EST.Abs loc abss) = Abs loc abss

toTau :: EST.Tau -> Tau
toTau (EST.Tau loc tau) = Tau loc tau

toIdent :: EST.Identifier -> Identifier
toIdent (EST.Identifier loc ident) = Identifier loc ident

toTauAbs :: EST.Tau -> EST.TypeAbstractions -> TauAbs
toTauAbs tau abss = TauAbs (toTau tau) (map toAbs abss)

fromTauAps2Type :: EST.Tau -> EST.TypeApplications -> Type
fromTauAps2Type tau@(EST.Tau loc _) aps  = TypeT loc (toTau tau) (map toType aps)

fromTauAbs2Type :: EST.Tau -> EST.TypeAbstractions -> Type
fromTauAbs2Type estTau abss = tau2Type (toTauAbs estTau abss)

toSig :: EST.Sig a => Bool -> [EST.Abs] -> a -> Sig 
--TODO rename isS0
toSig b abss sig = Sig (EST.sigLoc sig) (toIdent (EST.sigId sig)) (map toType args') (toType (EST.sigRet sig)) posneg b (map toAbs abss)
    where
        args = EST.sigArgs sig
        (posneg, args') = case EST.sigNature sig of 
            EST.ConSigNature   -> (Pos, args)
            EST.DesSigNature t -> (Neg, t:args)
            EST.FunSigNature   -> (if b then Neg else Pos, args)
            
toConSigs :: Bool -> [EST.Abs] -> EST.ConSig -> Sig
toConSigs _ abss (EST.ConSig loc ident args ret nature) = 
    Sig loc (toIdent ident) (map toType args) (toType ret) Pos True (map toAbs abss)
toDesSigs :: Bool -> [EST.Abs] -> EST.DesSig -> Sig
toDesSigs _ abss (EST.DesSig loc ident args ret (EST.DesSigNature t)) = 
    Sig loc (toIdent ident) (map toType (t:args)) (toType ret) Neg False (map toAbs abss)
toFunSigs :: Bool -> [EST.Abs] -> EST.FunSig -> Sig
toFunSigs isS0 abss (EST.FunSig loc ident args ret nature) = 
    Sig loc (toIdent ident) (map toType args) (toType ret) (if isS0 then Neg else Pos) isS0 (map toAbs abss)