{-|
Description : Abstract syntax tree.

Representation of Uroboro programs as abstract syntax tree with
type annotations. This is the "internal" program representation
produced by the type checker.
-}


module Uroboro.InternalSyntax where

import Uroboro.Location

-- Type
data Tau = Tau { 
      tauLoc :: Hidden Location
    , tauTau :: String
    } deriving (Show)
instance Eq Tau where
    Tau _ x1 == Tau _ x2  = x1 == x2

data Type 
    = Typevar (Hidden Location) String   -- typevariable
    | TypeT (Hidden Location) Tau TypeApplications  --TauAps
        deriving (Show)
instance Eq Type where
    Typevar _ x1 == Typevar _ x2        = x1 == x2
    TypeT _ x1 aps1  == TypeT _ x2 aps2 = x1 == x2 && aps1 == aps2
    _ == _                              = False        

data Abs = Abs {
    absLoc :: Hidden Location -- location in source
  , absAbs :: String   -- abstraction variable
  } deriving (Show)
instance Eq Abs where
    Abs {absAbs = x} == Abs {absAbs = y} = x == y     
    
type TypeAbstractions = [Abs]    
type TypeApplications = [Type]
 
data Identifier = Identifier {
      idLoc :: Hidden Location 
    , idId :: String 
    } deriving (Show)
instance Eq Identifier where
    Identifier _ x1 == Identifier _ x2  = x1 == x2

type IdType = (Identifier, Type)

-- Context & Sigma
data Frame 
    = TermBind IdType
    | TypeBind Abs -- type variable
    deriving (Show, Eq)
   
type Context = [Frame]

-- TODO: rename sigIsS0
data Sig = Sig {
    sigLoc  :: Hidden Location   -- location in source
  , sigName :: Identifier -- identifier (con, fun-)
  , sigArgs :: [Type]     -- args (fst, ...)
  , sigRet  :: Type       -- return type
  , sigNature :: TypeNature   -- pos/neg
  , sigIsS0 :: Bool       -- isSig0?
  , sigAbs  :: TypeAbstractions
} deriving (Show)

data TypeNature = Pos
    | Neg deriving (Show, Eq)

data TauAbs = TauAbs {
    tauAbsTau :: Tau              -- name of tau 
  , tauAbsAbs :: TypeAbstractions -- forall abstractions
  } deriving (Show)
instance Eq TauAbs where
    TauAbs {tauAbsTau = t1, tauAbsAbs = a1} == TauAbs {tauAbsTau = t2, tauAbsAbs = a2} = t1 == t2 && a1 == a2   

data Sigma = Sigma {
      sgmTypeNames :: [TauAbs]  
    , sgmSigs   :: [Sig]
} deriving (Show)


-- Program
data Program = Program {
      prgSigma    :: Sigma 
    , prgRules    :: [Rule]
    --, main :: Rule
    } deriving (Show)

type Rule = (TypeAbstractions, Cop, Exp)

-- |Copattern with type annotations.
data Cop = Cop {
    copLoc  :: Hidden Location -- location in source
  , copIdTy :: IdType   -- name with type      
  , copArgs :: [Pat]    -- args 
  , copNature :: CopNature
} deriving (Show)
instance Eq Cop where
    Cop _ x1 a1 k1 == Cop _ x2 a2 k2 = x1 == x2 && a1 == a2 && k1 == k2

data CopNature = AppCop
    | DesCop [Cop] deriving (Show)
instance Eq CopNature where
    AppCop == AppCop             = True
    DesCop cops1 == DesCop cops2 = cops1 == cops2
    _ == _                       = False

-- |Pattern with type annotations.
data Pat = Pat {
      patLoc :: Hidden Location 
    , patIdTy :: IdType
    , patNature :: PatNature
} deriving (Show)
instance Eq Pat where
    Pat _ x1 k1 == Pat _ x2 k2 = x1 == x2 && k1 == k2

data PatNature = VarPat
    | AppPat [Pat] deriving (Show)
instance Eq PatNature where
    VarPat == VarPat         = True
    AppPat pats1 == AppPat pats2 = pats1 == pats2
    _ == _                   = False


-- |Expression with type annotations.
data Exp = Exp { 
      expLoc :: Hidden Location 
    , expIdTy :: IdType
    , expNature :: ExpNature
} deriving (Show)
instance Eq Exp where
    Exp _ x1 k1 == Exp _ x2 k2 = x1 == x2 && k1 == k2

data ExpNature = 
    -- |Variable.
    VarExp
    -- |Application (des-exp: size[exp] >= 1)
    | SExp [Exp] deriving (Show)
instance Eq ExpNature where
    VarExp == VarExp         = True
    SExp exps1 == SExp exps2 = exps1 == exps2
    _ == _                   = False


-- |Start value for folds.
emptyContext :: Context
emptyContext = []

addFrame2Ctx :: Frame -> Context -> Context
addFrame2Ctx frame ctx
    | newFrameBind `elem` bindLs = ctx
    | otherwise = frame : ctx
    where (newFrameBind, bindLs) = case frame of 
            TermBind (ident, _) -> (idId ident, [idId x | TermBind (x,_) <- ctx])
            TypeBind (Abs _ var) -> (var, [x | TypeBind (Abs _ x) <- ctx])

emptySigma :: Sigma 
emptySigma = Sigma [][]

emptyProgram :: Sigma -> Program
emptyProgram sgm = Program sgm []

-- lookup name in sigmas type names and signature names
lookupNameForLoc :: Sigma -> String -> [Location]
lookupNameForLoc sgm name = 
    map (\(TauAbs t a) -> unhide (tauLoc t)) (filter (\tauabs -> name == tauTau (tauAbsTau tauabs)) (sgmTypeNames sgm)) 
    ++ map (unhide . sigLoc) (filter (\sig -> name == idId (sigName sig)) (sgmSigs sgm))         

-- lookup type stored in sigma
lookupTauAbs :: Sigma -> Tau -> Maybe [TauAbs] 
lookupTauAbs sgm tau 
    | null ls = Nothing
    | otherwise = Just ls 
    where ls = filter (\tauabs -> tau == tauAbsTau tauabs) (sgmTypeNames sgm)

lookup1TauAbs :: Sigma -> Tau -> Maybe TauAbs
lookup1TauAbs sgm tau = do
    tauabsls <- lookupTauAbs sgm tau
    Just (head tauabsls)

-- lookup id in sig
lookupSig :: Sigma -> Identifier -> Maybe [Sig] 
lookupSig sgm ident 
    | null ls = Nothing
    | otherwise = Just ls 
    where ls = filter (\Sig{sigName=n} -> ident == n) (sgmSigs sgm)

getLookup1For :: (Sig -> b) -> Sigma -> Identifier -> Maybe b
getLookup1For fun sgm ident = do
    sigls <- lookupSig sgm ident
    Just $ fun (head sigls) -- instead of head could be another function to choose sig...
   
lookup1Sig :: Sigma -> Identifier -> Maybe Sig
lookup1Sig = getLookup1For id 
    
lookupRetTy :: Sigma -> Identifier -> Maybe Type
lookupRetTy = getLookup1For sigRet
       
lookupArgTypes :: Sigma -> Identifier -> Maybe [Type]
lookupArgTypes = getLookup1For sigArgs

lookupTypInfosForId :: Sigma -> Identifier -> Maybe ([Type], Type)
lookupTypInfosForId sgm ident = do 
    targs <- lookupArgTypes sgm ident
    ret <- lookupRetTy sgm ident
    return (targs, ret)    

-- lookup id in context (only term bind identifiers)
lookupCtxTyBind :: Context -> Identifier -> Maybe IdType
lookupCtxTyBind ctx ident 
    | null teBindLs = Nothing
    | otherwise = Just (head teBindLs)
    where 
        teBindLs = [(x,t) | TermBind (x,t) <- ctx, x == ident]

-- type transformations
tau2Type :: TauAbs -> Type
tau2Type (TauAbs tau abss) = TypeT (tauLoc tau) tau (map fromAbs2Typevar abss)

fromAbs2Typevar :: Abs -> Type
fromAbs2Typevar (Abs loc abss)= Typevar loc abss
