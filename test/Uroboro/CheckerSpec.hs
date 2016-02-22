module Uroboro.CheckerSpec where

import Utils
import SpecHelper

import Uroboro.Location
import Uroboro.InternalSyntax

import Uroboro.FillSigma
import Uroboro.FillRules

import Control.Monad (forM, foldM) 
import Data.Either (isLeft, isRight)

uroLib' =  ["bool.uro", "nat.uro", "function.uro", "list.uro", "tree.uro", "stream.uro", "conat.uro"]
uroLib = map (\a -> "samples/lib/" ++ a) uroLib'
   
parseFiles paths = do
    lol <- forM paths $ \path -> do
        input <- readFile path
        case uroparse (exactly parseDef) path input of
            Left _ -> fail "Parser"
            Right defs -> return defs
    case typecheck (concat lol) of 
            Left _ -> fail "Checker"
            Right p -> return p
      
prelude :: IO Program
prelude = parseFiles uroLib
    
-- |Context using prelude
locUndef = MakeLocation "undef" 0 0
c :: Context
c = [ TermBind (Identifier locUndef "i", TypeT locUndef (Tau locUndef "Int") [])
    , TermBind (Identifier locUndef "f", TypeT locUndef (Tau locUndef "IntToInt") [])
    , TermBind (Identifier locUndef "g", TypeT locUndef (Tau locUndef "TwoIntToInt") [])
    , TermBind (Identifier locUndef "l", TypeT locUndef (Tau locUndef "ListOfInt") [])
    , TermBind (Identifier locUndef "s", TypeT locUndef (Tau locUndef "StreamOfInt") [])
    , TypeBind (Abs locUndef "X")
    , TypeBind (Abs locUndef "Y")
    ]

tyErrAbsMsg           = "Shadowed type abstractions "
tyErrTauIsTypevarMsg  = "Mismatch between type variable "
tyErrMultDeclMsg      = "Multiple declarations of "
tyErrDuplTySigsMsg    = "Duplicate type signatures for " 
tyErrDefMismatchMsg   = "Definition Mismatch in " 
tyErrTyLenMismatchMsg = "Typing Argument Mismatch, expected "
tyErrUnboundMsg       = "Not in scope: " 
tyErrIdMismatchMsg    = "Definition Mismatch in rule: \n" ++ "expected identifier " 
tyErrTyMismatchMsg    = "Type Mismatch: \n" ++ "expected type " 
tyErrLenMismatchMsg   = "Length Mismatch in arguments"


eitherIO fun = case fun of
                    Left e -> fail "Checker"
                    Right s -> return s

spec :: Spec
spec = do
    describe "prevent duplicates" $ do
        it "for data" $ do
            defs <- parseString parseDef $ unlines
                [ "data A where a(): A"
                , "data A where b(): A"
                ]
            foldM fillSigma emptySigma defs `shouldFail` tyErrMultDeclMsg
            
            defs' <- parseString parseDef $ unlines
                [ "data A where a(): A" 
                , "             a(): A"
                ]
            foldM fillSigma emptySigma defs' `shouldFail` tyErrDuplTySigsMsg   
            
            defs'' <- parseString parseDef $ unlines
                [ "data A where a(): A"
                , "data B where a(): B"
                ]
            foldM fillSigma emptySigma defs'' `shouldFail` tyErrDuplTySigsMsg
        it "for codata" $ do
            defs <- parseString parseDef $ unlines
                [ "codata A where A.a(): Nat"
                , "codata A where A.b(): A"
                ]
            foldM fillSigma emptySigma defs `shouldFail` tyErrMultDeclMsg
            
            defs' <- parseString parseDef $ unlines
                [ "codata A where A.a(): Nat" 
                , "               A.a(): Nat"
                ]
            foldM fillSigma emptySigma defs' `shouldFail` tyErrDuplTySigsMsg   
            
            defs'' <- parseString parseDef $ unlines
                [ "codata A where A.a(): A"
                , "codata B where B.a(): B"
                ]
            foldM fillSigma emptySigma defs'' `shouldFail` tyErrDuplTySigsMsg
        it "for functions" $ do
            defs <- parseString parseDef $ unlines
                [ "function a() : Nat where "
                , "function a() : Nat where "
                ]
            foldM fillSigma emptySigma defs `shouldFail` tyErrMultDeclMsg
            
            defs' <- parseString parseDef $ unlines
                [ "function a() : Nat where"
                , "function a() : Bool where"
                ]
            foldM fillSigma emptySigma defs' `shouldFail` tyErrMultDeclMsg
            
-- if overloading is desired -> accept this test and expand it            
            defs' <- parseString parseDef $ unlines
                [ "function a(Nat) : Nat where "
                , "function a() : Nat where "
                , "function a(Bool) : Bool where"
                ]
            foldM fillSigma emptySigma defs' `shouldFail` tyErrMultDeclMsg
    describe "prevent mismatches " $ do
        it "checks return types for data" $ do
            defs <- parseString parseDef $ unlines
                [ "data Float where "
                , "data Int where intZero() : Float"
                ]
            foldM fillSigma emptySigma defs `shouldFail` tyErrDefMismatchMsg
        it "checks destructor type for codata" $ do
            defs <- parseString parseDef $ unlines
                [ "codata CoFloat where "
                , "codata CoInt where A.coIntZero() : CoFloat"
                ]
            foldM fillSigma emptySigma defs `shouldFail` tyErrDefMismatchMsg
            defs <- parseString parseDef $ unlines
                [ "codata CoFloat where "
                , "codata CoInt where CoFloat.coIntZero() : CoFloat"
                ]
            foldM fillSigma emptySigma defs `shouldFail` tyErrDefMismatchMsg
    describe "check Sigma " $ do
        it "checks argument and return types for data" $ do
            defs <- parseString parseDef $ unlines
                [ "data Int where intSucc(Intt) : Int"
                ]
            sgm <- eitherIO $ foldM fillSigma emptySigma defs
            checkSigma sgm `shouldFail` tyErrUnboundMsg
            
            defs' <- parseString parseDef $ unlines
                [ "data Int where intSucc(Int, List[Int,Int]) : Int"
                ]
            sgm <- eitherIO $ foldM fillSigma emptySigma defs
            checkSigma sgm `shouldFail` tyErrUnboundMsg
            
            defs'' <- parseString parseDef $ unlines
                [ "data Int where intSucc(Int, List[Int,Int]) : Intt"
                ]
            sgm <- eitherIO$  foldM fillSigma emptySigma defs 
            checkSigma sgm `shouldFail` tyErrUnboundMsg
        it "checks argument and return types for codata" $ do
            defs <- parseString parseDef $ unlines
                [ "codata CoInt where CoInt.intSucc(CoIntt) : CoInt"
                ]
            sgm <- eitherIO $ foldM fillSigma emptySigma defs 
            checkSigma sgm `shouldFail` tyErrUnboundMsg
            
            defs' <- parseString parseDef $ unlines
                [ "codata CoInt where CoInt.intSucc(CoIntt) : CoIntt"
                ]
            sgm <- eitherIO $ foldM fillSigma emptySigma defs 
            checkSigma sgm `shouldFail` tyErrUnboundMsg
            
            defs'' <- parseString parseDef $ unlines
                [ "codata CoInt where CoInt.intSucc(CoInt[CoInt]) : CoInt"
                ]
            sgm <- eitherIO $ foldM fillSigma emptySigma defs
            checkSigma sgm `shouldFail` tyErrUnboundMsg                        
    describe "accepts definitions for " $ do
        it "data types" $ do
            x:_ <- parseString parseDef "data Int where intZero() : Int"
            fillSigma emptySigma x `shouldSatisfy` isRight --TODO
        it "allows multiple arguments with the same type" $ do
            x:_ <- parseString parseDef "data A where a(A, A): A"
            fillSigma emptySigma x `shouldSatisfy` isRight       
            x':_ <- parseString parseDef "data A where a(A[], A): A"
            fillSigma emptySigma x' `shouldSatisfy` isRight --TODO 
    describe "fillRules (codata)" $ do
        let stream = "codata StreamOfInt where StreamOfInt.headc(): Int"
        it "prevents duplicates" $ do
            defs <- parseString parseDef $ unlines [stream, stream]
            foldM fillSigma emptySigma defs `shouldFail` tyErrMultDeclMsg
        it "checks argument types" $ do
            x:_ <- parseString parseDef "codata IntToInt where IntToInt.apply(Int): Int"
            sgm <- eitherIO $ fillSigma emptySigma x 
            checkSigma sgm `shouldFail` tyErrUnboundMsg
        it "allows codata types" $ do
            x:_ <- parseString parseDef stream
            fillSigma emptySigma x `shouldSatisfy` isRight
        it "allows multiple arguments with the same type" $ do
            x:_ <- parseString parseDef "codata A where A.a(A, A): A"
            fillSigma emptySigma x `shouldSatisfy` isRight
    describe "argument mismatch (length and types)" $ do
        it "calls (data)" $ do
            p <- prelude
            e <- parseString parseExp "succ()"
            fillExp (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "Nat") []) e `shouldFail` tyErrLenMismatchMsg
            
            e' <- parseString parseExp "succ(zero(),true())"
            fillExp (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "Nat")  []) e' `shouldFail` tyErrLenMismatchMsg
            
            e'' <- parseString parseExp "succ(true())"
            fillExp (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "Nat")  []) e'' `shouldFail` tyErrTyMismatchMsg
        it "calls (function)" $ do
            p <- prelude
            e <- parseString parseExp "add()"
            fillExp (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "Nat")  []) e `shouldFail` tyErrLenMismatchMsg
                        
            e' <- parseString parseExp "add(zero(),zero(),zero())"
            fillExp (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "Nat")  []) e' `shouldFail` tyErrLenMismatchMsg
            
            e'' <- parseString parseExp "add(zero(),true())"
            fillExp (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "Nat")  []) e'' `shouldFail` tyErrTyMismatchMsg
        it "calls (codata function)" $ do
            p <- prelude
            e <- parseString parseExp "coSucc().coAdd(coZero())"
            fillExp (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "CoNat")  []) e `shouldFail` tyErrLenMismatchMsg
            
            e' <- parseString parseExp "coSucc(coZero(),coZero()).coAdd(coZero())"
            fillExp (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "Nat")  []) e' `shouldFail` tyErrLenMismatchMsg
            
            e'' <- parseString parseExp "coSucc(coZero().coOdd()).coAdd(coZero())"
            fillExp (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "Nat")  []) e'' `shouldFail` tyErrTyMismatchMsg
        it "calls (codata selector)" $ do
            p <- prelude
            e <- parseString parseExp "coSucc(coZero()).coAdd()"
            fillExp (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "CoNat")  []) e `shouldFail` tyErrLenMismatchMsg
            
            e' <- parseString parseExp "coSucc(coZero()).coAdd(coZero(),coZero())"
            fillExp (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "Nat")  []) e' `shouldFail` tyErrLenMismatchMsg
            
            e'' <- parseString parseExp "coSucc(coZero()).coAdd(coZero().coOdd())"
            fillExp (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "Nat")  []) e'' `shouldFail` tyErrTyMismatchMsg
    describe "checkPattern " $ do
        it "with variables" $ do
            p <- prelude
            e <- parseString parsePat "x"
            res <- return $ fillPat (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "Nat")  []) e
            res `shouldSatisfy` (\x -> case x of
              Right (Pat _ (Identifier _ "x", TypeT _ (Tau locUndef "Nat")  []) VarPat, ctx) -> True
              _ -> False)
        it "with applications" $ do
            p <- prelude
            e <- parseString parsePat "zero()"
            res <- return $ fillPat (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "Nat")  []) e 
            res `shouldSatisfy` (\x -> case x of
              Right (Pat _ (Identifier _ "zero", TypeT _ (Tau locUndef "Nat")  []) (AppPat []), ctx)  -> True
              _ -> False)
            
            e' <- parseString parsePat "succ(n)"
            res' <- return $ fillPat (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "Nat")  []) e' 
            res' `shouldSatisfy` (\x -> case x of
              Right (Pat _ (Identifier _  "succ", TypeT _ (Tau _ "Nat")  []) (AppPat [Pat _ (Identifier _ "n", TypeT _ (Tau _ "Nat")  []) VarPat]), ctx)  -> True
              _ -> False)
            
            e'' <- parseString parsePat "succ(n)"
            res'' <- return $ fillPat (prgSigma p) [TermBind (Identifier locUndef "n", TypeT locUndef (Tau locUndef "Int") [])] (TypeT locUndef (Tau locUndef "Nat")  []) e'' 
            res'' `shouldFail` tyErrTyMismatchMsg
            
          
    describe "checkExp" $ do
        it "infers construction" $ do
            p <- prelude
            e <- parseString parseExp "empty[Nat]()"
            fillExp (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "List") [TypeT locUndef (Tau locUndef "Nat") []]) e `shouldSatisfy` (\x -> case x of
              Right (Exp _ (Identifier _ "empty", TypeT _ (Tau _ "List")  [TypeT _ (Tau _ "Nat")  []]) (SExp [])) -> True
              _ -> False)
        it "infers applications" $ do
            p <- prelude
            e <- parseString parseExp "map[Nat,Nat](f, l)"
            fillExp (prgSigma p) c (TypeT locUndef (Tau locUndef "List")  [TypeT locUndef (Tau locUndef "Nat")  []]) e `shouldSatisfy` (\x -> case x of
              Right (Exp _ (Identifier _ "map", TypeT _ (Tau _ "List")  [TypeT _ (Tau _ "Nat")  []]) (SExp  
                [Exp _ (Identifier _ "f", TypeT _ (Tau _ "Function")  [TypeT _ (Tau _ "Nat")  [], TypeT _ (Tau _ "Nat")  []]) VarExp, Exp _ (Identifier _ "l", TypeT _ (Tau _ "List")  [TypeT _ (Tau _ "Nat")  []]) VarExp])) -> True
              _ -> False)
    describe "inferPExp" $ do
        it "infers construction" $ do
            p <- prelude
            e <- parseString parseExp "empty[Nat]()"
            inferExp p [] e `shouldSatisfy` (\x -> case x of
              Right (Exp _ (Identifier _ "empty", TypeT _ (Tau _ "List")  [TypeT _ (Tau locUndef "Nat")  []]) (SExp [])) -> True
              _ -> False)
        it "infers applications" $ do
            p <- prelude
            e <- parseString parseExp "map[Nat,Nat](f, l)"
            inferExp p c e `shouldSatisfy` (\x -> case x of
              Right (Exp _ (Identifier _ "map", TypeT _ (Tau _ "List") [TypeT _ (Tau _ "Nat")  []]) (SExp  
                [Exp _ (Identifier _ "f", TypeT _ (Tau _ "Function")  [TypeT _ (Tau _ "Nat")  [], TypeT _ (Tau _ "Nat")  []]) VarExp, Exp _ (Identifier _ "l", TypeT _ (Tau _ "List")  [TypeT _ (Tau _ "Nat") []]) VarExp])) -> True
              _ -> False)            