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

toSig :: EST.Sig a => Bool -> [EST.Abs] -> a -> Sig 
toSig b abss sig = Sig (EST.sigLoc sig) (toIdent (EST.sigId sig)) (map toType args') (toType (EST.sigRet sig)) posneg b (map toAbs abss)
    where
        args = EST.sigArgs sig
        (posneg, args') = case EST.sigNature sig of 
            EST.ConSigNature   -> (Pos, args)
            EST.DesSigNature t -> (Neg, t:args)
            EST.FunSigNature   -> (if b then Neg else Pos, args)
