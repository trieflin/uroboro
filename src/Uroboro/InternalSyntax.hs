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
    } deriving ( Eq)
instance Show Tau where
  show (Tau l t) = t 
    
data Type 
    = Typevar (Hidden Location) String   -- typevariable
    | TypeT (Hidden Location) Tau TypeApplications  --TauAps
    deriving (Eq)
instance Show Type where
  show (Typevar _ v)   = v
  show (TypeT _ t aps) = show t ++ show aps
        
data Abs = Abs {
    absLoc :: Hidden Location -- location in source
  , absAbs :: String   -- abstraction variable
  } deriving (Eq)
instance Show Abs where
  show (Abs _ a) = a
  
type TypeAbstractions = [Abs]    
type TypeApplications = [Type]
 
data Identifier = Identifier {
      idLoc :: Hidden Location 
    , idId :: String 
    } deriving (Eq)
instance Show Identifier where
  show (Identifier _ i) = i

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
} deriving (Eq)
instance Show Sig where
  show (Sig _ n as r nt s0 abs) = 
    let (pre,args) = if nt == Pos || s0 then ("", show as) else (show (head as) ++ ".", show (tail as))
    in show nt ++ show s0 ++ " <" ++ show abs ++ "> " ++ pre ++ show n ++ "(" ++ show args ++ "):" ++ show r

data TypeNature 
    = Pos
    | Neg deriving (Show, Eq)

data TauAbs = TauAbs {
    tauAbsTau :: Tau              -- name of tau 
  , tauAbsAbs :: TypeAbstractions -- forall abstractions
  } deriving (Eq)
instance Show TauAbs where
  show (TauAbs t abs) = show t ++ "<" ++ show abs ++ ">"

data Sigma = Sigma {
      sgmTypeNames :: [TauAbs]  
    , sgmSigs   :: [Sig]
} deriving (Eq)
instance Show Sigma where
  show (Sigma tn sigs) = "SGM TypeNames\n" ++ foldr (\ta acu -> acu ++ "  " ++ show ta ++ "\n") "" tn
                      ++ "SGM Sigs\n"  ++ foldr (\x acu -> acu ++ "  " ++ show x ++ "\n") "" sigs

-- Program
data Program = Program {
      prgSigma    :: Sigma 
    , prgRules    :: [Rule]
    --, main :: Rule
    } deriving (Eq)
instance Show Program where
  show (Program sgm rls) = show sgm ++ "\n RULES \n" ++ show rls

type Rule = (TypeAbstractions, Cop, Exp)

-- |Copattern with type annotations.
data Cop = Cop {
    copLoc  :: Hidden Location -- location in source
  , copIdTy :: IdType   -- name with type      
  , copArgs :: [Pat]    -- args 
  , copNature :: CopNature
} deriving (Eq)
instance Show Cop where
  show (Cop _ (i,t) as n) = show i ++ "(" ++ show as ++ ") " ++ show n ++ ":" ++ show t

data CopNature 
    = AppCop
    | DesCop [Cop] 
    deriving (Eq)
instance Show CopNature where
  show AppCop       = ""
  show (DesCop dcs) = foldr (\x acu -> acu ++ "." ++ show x) "" dcs

-- |Pattern with type annotations.
data Pat = Pat {
      patLoc :: Hidden Location 
    , patIdTy :: IdType
    , patNature :: PatNature
} deriving (Eq)
instance Show Pat where
  show (Pat _ (i,t) n) = show i ++ show n ++ ":" ++ show t

data PatNature 
    = VarPat
    | AppPat [Pat] 
    deriving (Eq)
instance Show PatNature where
  show (VarPat)     = ""
  show (AppPat pts) = "(" ++ show pts ++ ")"
    

-- |Expression with type annotations.
data Exp = Exp { 
      expLoc :: Hidden Location 
    , expIdTy :: IdType
    , expNature :: ExpNature
} deriving (Eq)
instance Show Exp where
  show (Exp _ (i,t) n) = show i ++ show n ++ ":" ++ show t

data ExpNature = 
    -- |Variable.
    VarExp
    -- |Application (des-exp: size[exp] >= 1)
    | SExp [Exp] 
    deriving (Eq)
instance Show ExpNature where
  show (VarExp)  = ""
  show (SExp es) = "(" ++ show es ++ ")"


-- |Start value for folds.
emptySigma :: Sigma 
emptySigma = Sigma [][]

emptyProgram :: Sigma -> Program
emptyProgram sgm = Program sgm []

emptyContext :: Context
emptyContext = []

addFrame2Ctx :: Frame -> Context -> Context
addFrame2Ctx frame ctx
    | newFrameBind `elem` bindLs = ctx
    | otherwise = frame : ctx
    where (newFrameBind, bindLs) = case frame of 
            TermBind (ident, _) -> (idId ident, [idId x | TermBind (x,_) <- ctx])
            TypeBind (Abs _ var) -> (var, [x | TypeBind (Abs _ x) <- ctx])

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
fromAbs2Typevar (Abs loc abss) = Typevar loc abss

transformType :: Sigma -> [String] -> Type -> Type
transformType sgm sabs ty@(Typevar lt tv) --transformTypevarToTypeT
    | tv `notElem` sabs && tv `elem` [tauTau tau | TauAbs tau _ <- sgmTypeNames sgm]
                = TypeT lt (Tau lt tv) [] 
    | otherwise = ty
transformType sgm sabs (TypeT lt tau aps) = TypeT lt tau $ map (transformType sgm sabs) aps
