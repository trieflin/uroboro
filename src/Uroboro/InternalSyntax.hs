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
    } deriving (Show, Eq)
    
data Type 
    = Typevar (Hidden Location) String   -- typevariable
    | TypeT (Hidden Location) Tau TypeApplications  --TauAps
        deriving (Show, Eq)
        
data Abs = Abs {
    absLoc :: Hidden Location -- location in source
  , absAbs :: String   -- abstraction variable
  } deriving (Show, Eq)
  
type TypeAbstractions = [Abs]    
type TypeApplications = [Type]
 
data Identifier = Identifier {
      idLoc :: Hidden Location 
    , idId :: String 
    } deriving (Show, Eq)

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
} deriving (Show,Eq)

data TypeNature 
    = Pos
    | Neg deriving (Show, Eq)

data TauAbs = TauAbs {
    tauAbsTau :: Tau              -- name of tau 
  , tauAbsAbs :: TypeAbstractions -- forall abstractions
  } deriving (Show, Eq)

data Sigma = Sigma {
      sgmTypeNames :: [TauAbs]  
    , sgmSigs   :: [Sig]
} deriving (Show,Eq)


-- Program
data Program = Program {
      prgSigma    :: Sigma 
    , prgRules    :: [Rule]
    --, main :: Rule
    } deriving (Show,Eq)

type Rule = (TypeAbstractions, Cop, Exp)

-- |Copattern with type annotations.
data Cop = Cop {
    copLoc  :: Hidden Location -- location in source
  , copIdTy :: IdType   -- name with type      
  , copArgs :: [Pat]    -- args 
  , copNature :: CopNature
} deriving (Show, Eq)

data CopNature 
    = AppCop
    | DesCop [Cop] deriving (Show, Eq)

-- |Pattern with type annotations.
data Pat = Pat {
      patLoc :: Hidden Location 
    , patIdTy :: IdType
    , patNature :: PatNature
} deriving (Show,Eq)

data PatNature 
    = VarPat
    | AppPat [Pat] deriving (Show,Eq)
    

-- |Expression with type annotations.
data Exp = Exp { 
      expLoc :: Hidden Location 
    , expIdTy :: IdType
    , expNature :: ExpNature
} deriving (Show,Eq)

data ExpNature = 
    -- |Variable.
    VarExp
    -- |Application (des-exp: size[exp] >= 1)
    | SExp [Exp] deriving (Show, Eq)

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
fromAbs2Typevar :: Abs -> Type
fromAbs2Typevar (Abs loc abss)= Typevar loc abss
