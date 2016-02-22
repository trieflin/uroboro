{-| Description : Parse tree produced by parser - not typechecked yet -}

module Uroboro.ExternalSyntax where

import Uroboro.Location

data Tau = Tau {
    tauLoc :: Location         -- location in source
  , tauTau :: String              -- name of tau 
  } deriving (Show)
instance Eq Tau where
    Tau _ x == Tau _ y = x == y 
    
data Identifier = Identifier {
    idLoc :: Location -- location in source
  , idId  :: String   -- name of identifier    
  } deriving (Show)
instance Eq Identifier where
    Identifier _ x == Identifier _ y = x == y 

data Abs = Abs {
    absLoc :: Location -- location in source
  , absAbs :: String   -- abstraction variable
  } deriving (Show)
instance Eq Abs where
    Abs _ x == Abs _ y = x == y     
    
type TypeAbstractions = [Abs]    
type TypeApplications = [Type]

data Type 
    = TypeVar Location String
    | TypeT Location Tau TypeApplications 
    deriving (Show)
instance Eq Type where
    TypeVar _ x1 == TypeVar _ x2   = x1 == x2
    TypeT _ x1 a1 == TypeT _ x2 a2 = x1 == x2 && a1 == a2
    _ == _                         = False

-- |Definition.
data Def = Def { 
    defLoc  :: Location
  , defAbs  :: TypeAbstractions
  , defNature :: DefNature
} deriving (Show)

data DefNature  
    -- |Data type.
    = DatDefNature Tau [ConSig]
    -- |Codata type.
    | CodDefNature Tau [DesSig]
    -- |Function 
    | FunDefNature FunSig [Rule] 
    deriving (Show)

-- | Signature.
class Sig a where 
    sigLoc    :: a -> Location
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
    cSigLoc    :: Location
  , cSigId     :: Identifier
  , cSigArgs   :: [Type] 
  , cSigRet    :: Type
  , cSigNature :: SigNature -- ConSigNature
  } deriving (Show)
instance Sig ConSig where
    sigLoc    = cSigLoc
    sigId     = cSigId
    sigArgs   = cSigArgs
    sigRet    = cSigRet
    sigNature = cSigNature
 
data DesSig = DesSig {
    dSigLoc    :: Location
  , dSigId     :: Identifier
  , dSigArgs   :: [Type] 
  , dSigRet    :: Type
  , dSigNature :: SigNature -- DesSigNature TauAps
  } deriving (Show)
instance Sig DesSig where
    sigLoc = dSigLoc
    sigId = dSigId
    sigArgs = dSigArgs
    sigRet = dSigRet
    sigNature = dSigNature
      
data FunSig = FunSig {
    fSigLoc  :: Location
  , fSigId   :: Identifier
  , fSigArgs :: [Type] 
  , fSigRet  :: Type
  , fSigNature :: SigNature -- FunSigNature
  } deriving (Show)
instance Sig FunSig where
    sigLoc = fSigLoc
    sigId = fSigId
    sigArgs = fSigArgs
    sigRet = fSigRet
    sigNature = fSigNature
    
-- |Part of a function definition.
data Rule = Rule {
    ruleLoc :: Location -- location in source
  , ruleCop :: Cop      -- copattern (lhs)        
  , ruleExp :: Exp      -- expression (rhs)
  } deriving (Show)

-- |Copattern.
-- f(args_f).d_1(args_d1). ... .d_n(args_dn)
data Cop = Cop {
    copLoc    :: Location   -- location in source
  , copId     :: Identifier -- name       
  , copArgs   :: [Pat]      -- args 
  , copNature :: CopNature
}  deriving (Show)
instance Eq Cop where
    Cop _ t1 a1 d1 == Cop _ t2 a2 d2 = t1 == t2 && a1 == a2 && d1 == d2

data CopNature 
    = AppCopNature
    | DesCopNature [DApsCop] 
    deriving (Show, Eq)

data DApsCop = DApsCop {
    dapsLoc   :: Location 
  , dapsId    :: Identifier
  , dapsAps   :: TypeApplications         
  , dapsPats  :: [Pat]    -- args
  } deriving (Show)
instance Eq DApsCop where
    DApsCop _ t1 a1 p1 == DApsCop _ t2 a2 p2 = t1 == t2 && a1 == a2 && p1 == p2   
    
-- |Pattern.
data Pat -- concerning args in f.d_1. ... .d_n(args)
    -- |Variable pattern.
    = VarPat Location Identifier
    -- |Application pattern (constructor/positive? functions)
    | AppPat Location Identifier TypeApplications [Pat] 
    deriving (Show)
instance Eq Pat where
    VarPat _ x1 == VarPat _ x2 = x1 == x2 
    AppPat _ x1 a1 p1 == AppPat _ x2 a2 p2 = x1 == x2 && a1 == a2 && p1 == p2
    _ == _ = False     

-- |Expression (Term).
data Exp
    -- |Variable.
    = VarExp Location Identifier
    -- |Constructor or function application.
    | AppExp Location Identifier TypeApplications [Exp]
    -- |Destructor application (Selection).
    -- Exp.IdAps(Exp*) 
    | DesExp Location Exp [DExp] 
    deriving (Show)

data DExp = DExp Location Identifier TypeApplications [Exp] deriving (Show)


checkNeg :: Rule -> Bool
checkNeg (Rule _ (Cop{copNature=AppCopNature }) _) = False
checkNeg (Rule _ (Cop{copNature=DesCopNature _ }) _) = True
