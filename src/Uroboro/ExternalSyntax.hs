{-| Description : Parse tree produced by parser - not typechecked yet -}

module Uroboro.ExternalSyntax where

import Uroboro.Location

data Tau = Tau {
    tauLoc :: Hidden Location         -- location in source
  , tauTau :: String              -- name of tau 
  } deriving (Show, Eq)
  
data Identifier = Identifier {
    idLoc :: Hidden Location -- location in source
  , idId  :: String   -- name of identifier    
  } deriving (Show, Eq)
  
data Abs = Abs {
    absLoc :: Hidden Location -- location in source
  , absAbs :: String   -- abstraction variable
  } deriving (Show, Eq)
  
type TypeAbstractions = [Abs]    
type TypeApplications = [Type]

data Type 
    = TypeVar (Hidden Location) String
    | TypeT (Hidden Location) Tau TypeApplications 
    deriving (Show, Eq)
    
-- |Definition.
data Def = Def { 
    defLoc  :: Hidden Location
  , defAbs  :: TypeAbstractions
  , defNature :: DefNature
} deriving (Show, Eq)

data DefNature  
    -- |Data type.
    = DatDefNature Tau [ConSig]
    -- |Codata type.
    | CodDefNature Tau [DesSig]
    -- |Function 
    | FunDefNature FunSig [Rule] 
    deriving (Show, Eq)

-- | Signature.
class Sig a where 
    sigLoc    :: a -> Hidden Location
    sigId     :: a -> Identifier
    sigArgs   :: a -> [Type] 
    sigRet    :: a -> Type
    sigNature :: a -> SigNature

data SigNature 
    = ConSigNature
    | DesSigNature Type -- tau application?
    | FunSigNature
    deriving (Show, Eq)

data ConSig = ConSig {
    cSigLoc    :: Hidden Location
  , cSigId     :: Identifier
  , cSigArgs   :: [Type] 
  , cSigRet    :: Type
  , cSigNature :: SigNature -- ConSigNature
  } deriving (Show,Eq)
instance Sig ConSig where
    sigLoc    = cSigLoc
    sigId     = cSigId
    sigArgs   = cSigArgs
    sigRet    = cSigRet
    sigNature = cSigNature
 
data DesSig = DesSig {
    dSigLoc    :: Hidden Location
  , dSigId     :: Identifier
  , dSigArgs   :: [Type] 
  , dSigRet    :: Type
  , dSigNature :: SigNature -- DesSigNature TauAps
  } deriving (Show,Eq)
instance Sig DesSig where
    sigLoc = dSigLoc
    sigId = dSigId
    sigArgs = dSigArgs
    sigRet = dSigRet
    sigNature = dSigNature
      
data FunSig = FunSig {
    fSigLoc  :: Hidden Location
  , fSigId   :: Identifier
  , fSigArgs :: [Type] 
  , fSigRet  :: Type
  , fSigNature :: SigNature -- FunSigNature
  } deriving (Show,Eq)
instance Sig FunSig where
    sigLoc = fSigLoc
    sigId = fSigId
    sigArgs = fSigArgs
    sigRet = fSigRet
    sigNature = fSigNature
    
-- |Part of a function definition.
data Rule = Rule {
    ruleLoc :: Hidden Location -- location in source
  , ruleCop :: Cop      -- copattern (lhs)        
  , ruleExp :: Exp      -- expression (rhs)
  } deriving (Show,Eq)

-- |Copattern.
-- f(args_f).d_1(args_d1). ... .d_n(args_dn)
data Cop = Cop {
    copLoc    :: Hidden Location   -- location in source
  , copId     :: Identifier -- name       
  , copArgs   :: [Pat]      -- args 
  , copNature :: CopNature
}  deriving (Show,Eq)

data CopNature 
    = AppCopNature
    | DesCopNature [DApsCop] 
    deriving (Show, Eq)

data DApsCop = DApsCop {
    dapsLoc   :: Hidden Location 
  , dapsId    :: Identifier
  , dapsAps   :: TypeApplications         
  , dapsPats  :: [Pat]    -- args
  } deriving (Show, Eq)
  
-- |Pattern.
data Pat -- concerning args in f.d_1. ... .d_n(args)
    -- |Variable pattern.
    = VarPat (Hidden Location) Identifier
    -- |Application pattern (constructor/functions)
    | AppPat (Hidden Location) Identifier TypeApplications [Pat] 
    deriving (Show, Eq)

-- |Expression.
data ExpF
    -- |Variable.
    = VarExp (Hidden Location) Identifier
    -- |Constructor or function application.
    | AppExp (Hidden Location) Identifier TypeApplications [Exp]
    deriving (Show, Eq)

data Exp =
    -- |Variable, constructor or function application
    Expr ExpF   
    -- |Destructor application (Selection) with the form expF.IdAps(Exp*)* 
    | DesExp (Hidden Location) ExpF [DExp] 
    deriving (Show, Eq)

data DExp = DExp (Hidden Location) Identifier TypeApplications [Exp] deriving (Show, Eq)


checkNeg :: Rule -> Bool
checkNeg (Rule _ (Cop{copNature=AppCopNature }) _) = False
checkNeg (Rule _ (Cop{copNature=DesCopNature _ }) _) = True
