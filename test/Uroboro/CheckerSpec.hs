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
            Left l -> fail $ "Parser (" ++ show l ++ ")"
            Right defs -> return defs
    case typecheck (concat lol) of 
            Left _ -> fail "Checker"
            Right p -> return p
      
prelude :: IO Program
prelude = parseFiles uroLib


--sFailCodDes = "codata <T> Stream[T] where Stream.head() :: A"
--function fib(): Stream[Nat] where
--    fib().headc[]() = zero()
 
-- |Context using prelude
locUndef = Hidden (MakeLocation "undef" 0 0)
typeNat = TypeT locUndef (Tau locUndef "Nat") []
typeList = TypeT locUndef (Tau locUndef "List") 
typeFun = TypeT locUndef (Tau locUndef "Function")
c :: Context
c = [ TermBind (Identifier locUndef "f", typeFun [typeNat, typeNat])
    , TermBind (Identifier locUndef "l", typeList [typeNat])
    , TypeBind (Abs locUndef "X")
    , TypeBind (Abs locUndef "Y")
    ]

tyErrAbsMsg           = "Shadowed type abstractions "
tyErrTauIsTypevarMsg  = "Mismatch between type variable "
tyErrDuplTySigsMsg    = "Duplicate type signatures for " 
tyErrDefMismatchMsg   = "Definition Mismatch" 
tyErrTyLenMismatchMsg = "Typing Argument Mismatch, expected "
tyErrUnboundMsg       = "Not in scope: " 
tyErrIdMismatchMsg    = "Definition Mismatch in rule: \n" ++ "expected identifier " 
tyErrTyMismatchMsg    = "Type Mismatch: \n" ++ "expected type " 
tyErrLenMismatchMsg   = "Length Mismatch in arguments"


eitherIO fun = case fun of
                    Left e -> fail "Checker"
                    Right s -> return s


checkSatDef = mapM_ (\x -> do
                             sls <- parseString parseDef x
                             foldM fillSigma emptySigma sls `shouldSatisfy` isRight) 
checkFailDef errMsg = mapM_ (\x -> do
                                        sls <- parseString parseDef x
                                        typecheck sls `shouldFail` errMsg) 

--checkFailExp prog errMsg = mapM_ (\x -> do
  --                                      pexp <- parseString parseExpression x
    --                                    inferExp prog emptyContext pexp `shouldFail` errMsg) 

spec :: Spec
spec = do
    describe "prevent duplicates" $ do
        it "for data (type and constructor names)" $ 
          checkFailDef tyErrDuplTySigsMsg [ 
            unlines [ "data A where a(): A"
                    , "data A where b(): A" ] ,
            unlines [ "data A where a(): A" 
                    , "             a(): A" ] ,
            unlines [ "data A where a(): A"
                    , "data B where a(): B" ]
            ]
        it "for codata (type and destructor names)" $ 
          checkFailDef tyErrDuplTySigsMsg [ 
            unlines [ "codata A where A.a(): Nat"
                    , "codata A where A.b(): A" ] ,
            unlines [ "codata A where A.a(): Nat" 
                    , "               A.a(): Nat" ] ,
            unlines [ "codata A where A.a(): A"
                    , "codata B where B.a(): B" ] ,
            unlines [ "data A where a(): A"
                    , "codata A where A.c(): A" ] ,
            unlines [ "data A where a(): A"
                    , "codata B where B.a(): B" ]  
            ]  
        it "for functions (function names)" $ 
          checkFailDef tyErrDuplTySigsMsg [ 
            unlines [ "function a() : Nat where "
                    , "function a() : Nat where " ] ,
            unlines [ "function a() : Nat where"
                    , "function a() : Bool where" ] ,
            unlines [ "data A where a() : A"
                    , "function a() : Bool where" ] ,
            unlines [ "codata A where A.a() : A"
                    , "function a() : Bool where" ] ,                  
            -- if overloading is desired -> accept this test and expand it            
            unlines [ "function a(Nat) : Nat where "
                    , "function a() : Nat where "
                    , "function a(Bool) : Bool where" ]
           ]
    describe "prevent mismatches " $ 
        it "checks return types for data, destructor type for codata and function name in rules" $ 
          checkFailDef tyErrDefMismatchMsg [
            unlines [ "data Float where "
                    , "data Int where intZero() : Float" ] ,
            unlines [ "codata CoFloat where "
                    , "codata CoInt where CoFloat.coIntZero() : CoFloat" ] ,
            unlines [ "function fun() : Int where"  
                    , "  abc() = zero()" ]                           
            ]        
    describe "check sigma " $ do
        it "checks argument types for data" $ 
            checkFailDef tyErrUnboundMsg [
              unlines [ "data Int where intSucc(Intt) : Int" ] ,
              unlines [ "data Int where intSucc(Int, Intt) : Int" ] 
              ]
        it "checks argument and return types for codata" $ 
            checkFailDef tyErrUnboundMsg [
              unlines [ "codata CoInt where CoInt.intSucc(CoIntt) : CoInt" ],
              unlines [ "codata CoInt where CoInt.intSucc(CoInt) : CoIntt" ]
              ] 
        it "checks argument and return types for functions" $ 
            checkFailDef tyErrUnboundMsg [
              unlines [ "function fun() : Intt where " ] ,
              unlines [ "data Int where zer() : Int" 
                      , "function fun(Intt): Int where" ]    
              ]
    describe "satisfiable sigma" $ do
        it "for data types" $ 
            checkSatDef [ 
              unlines [ "data Int where" ] ,
              unlines [ "data Int where"
                      , "  intZero() : Int"
                      , "  intSucc(Int) : Int" ] ,
              unlines [ "data A where a(A, A): A" ] 
              ]
        it "for codata types" $ 
            checkSatDef [ 
              unlines [ "codata CoInt where" ] ,
              unlines [ "data Int where"
                      , "codata StreamOfInt where StreamOfInt.headc(): Int" ] ,
              unlines [ "codata A where A.a(A, A): A" ] 
              ]
        it "for functions" $ do
            let intdata = "data Int where"
            checkSatDef [ 
              unlines [ intdata, "function fun() : Int where" ] ,
              unlines [ intdata, "function fun(Int) : Int where" ] ,
              unlines [ intdata, "function fun(Int, Int) : Int where" ] ,
              unlines [ intdata, "function fun(Int) : Int where fun(a) = a" ]  
              ]            
    describe "check polymorphism (type variables) " $ do
        it "accept wellformed definitions" $ do
            let intdata = "data Int where intzero() : Int"
            checkSatDef [ 
              unlines [ "data Data <> where" ] ,
              unlines [ "data Data <> where d() : Data" ] ,
              unlines [ "data Data <> where d() : Data[]" ] ,
              unlines [ "data Data where d(Data[], Data): Data" ] ,
 
              unlines [ "data Data <X> where" ] , 
              unlines [ "data Data <X> where d(X) : Data[X]" ] ,
              unlines [ intdata, "data Data <X> where d(Int) : Data[X]" ] ,
                 
              unlines [ "data Data <X,Y,Z> where" ] ,
              unlines [ "data Data <X,Y,Z> where d(X) : Data[X,Y,Z]" ] ,
              unlines [ intdata, "data Data <X,Y,Z> where d(Int) : Data[X,Y,Z]" ] ,
              
              unlines [ "codata Codata <> where" ] ,
              unlines [ "codata Codata <> where Codata.d() : Codata" ] ,
              unlines [ "codata Codata <> where Codata[].d() : Codata[]" ] ,
              
              unlines [ "codata Codata <X> where" ] ,
              unlines [ "codata Codata <X> where Codata[X].d(X) : Codata[X]" ] ,
              unlines [ intdata, "codata Codata <X> where Codata[X].d(Int) : Codata[X]" ] ,
                 
              unlines [ "codata Codata <X,Y,Z> where" ] ,
              unlines [ "codata Codata <X,Y,Z> where Codata[X,Y,Z].d(X) : Codata[Z,X,Y]" ] ,
              unlines [ intdata, "codata Codata <X,Y,Z> where Codata[X,Y,Z].d(Int) : Codata[Int,Int,X]" ] ,
              
              unlines [ intdata, "function <> fun() : Int where" ] ,
              unlines [ intdata, "function <> fun() : Int where fun() = intzero()" ] ,
              unlines [ intdata, "function <> fun() : Int where fun() = intzero[]()" ] ,
                        
              unlines [ intdata, "function <X> fun() : Int where" ] ,
              unlines [ intdata, "function <X> fun(X) : Int where fun(x) = intzero()" ] ,
              unlines [ intdata, "function <X> fun(X) : X where fun(x) = x" ] ,
              unlines [ intdata, "function <X> fun(Int) : X where" ] , 
             
              unlines [ intdata, "function <X,Y,Z> fun(X,Int,Y) : Z where" ] , 
              unlines [ intdata, "function <X,Y,Z> fun(X,Y) : X where fun(x,y) = x" ] ,
              unlines [ intdata, "function <X,Y,Z> fun(X,Y,Z) : Z where fun(x,y,z) = z" ] ,
               
              unlines [ "data A <X> where a(X):A[X]", "codata X where X.d() : X" ] -- shadowed type variables 
              ]
        it "reject unbound type variables" $ do
            checkFailDef tyErrDefMismatchMsg [
              unlines [ "data Data where d(X) : Data[X]" ] , 
              unlines [ "data Data <X> where d(X) : Data[Y]" ] , 
              unlines [ "codata Codata where Codata[X].d(X) : X" ] ,
              unlines [ "codata Codata <X> where Codata[Y].d(X) : X" ]             
              ]
            checkFailDef tyErrUnboundMsg [
              unlines [ "data Data <X> where d(Y) : Data[X]" ] ,
              unlines [ "data List <X> where"
                      , "function fun() : List[X] where"] ,
              unlines [ "codata Codata <X> where Codata[X].d(Y) : X" ] ,
              unlines [ "codata Codata <X> where Codata[X].d(X) : Y" ] ,
              unlines [ "function <X> fun(Y) : X where " ] ,
              unlines [ "function <X> fun(X) : Y where " ] 
              ]
            checkFailDef tyErrAbsMsg [
              unlines [ "data X <X> where" ] ,
              unlines [ "data X <X> where c(X) : X[X]" ] ,
              unlines [ "data Dat <X,X> where " ] ,
              unlines [ "codata CoDat <X,Y,X> where " ] ,            
              unlines [ "function <X,X> fun(X) : X where " ]
              ]
    describe "check rules" $ do
        let intdata = "data Int where   intZero() : Int    intSucc(Int) : Int"
        it "checks number of argument" $ 
            checkFailDef tyErrLenMismatchMsg [
              unlines [ intdata
                      , "function f(Int) : Int where"
                      , "  f() = intZero()" ] ,
              unlines [ intdata
                      , "function f(Int) : Int where"
                      , "  f(a,a) = a" ] ,                             
              unlines [intdata
                      , "function f() : Int where"
                      , "  f() = intSucc()" ] ,
              unlines [ intdata
                      , "function f(Int) : Int where"
                      , "  f(a) = intSucc(a,a)" ] 
              ]
        it "checks boundness" $
            checkFailDef tyErrUnboundMsg [
              unlines [ intdata
                      , "function fun(Int): Int where"
                      , "  fun(a) = g()" ] ,
              unlines [ intdata
                      , "function fun(Int): Int where"
                      , "  fun(a) = b" ] ,
              unlines [ intdata
                      , "function fun(Int): Int where"
                      , "  fun(a) = fun(b)" ] ,
              unlines [ intdata, "codata C where C.d() : Int"
                      , "function fun(C): Int where"
                      , "  fun(c) = c.e()" ] ,
              unlines [ intdata, "codata C where C.d() : Int"
                      , "function fun(C): Int where"
                      , "  fun(c) = b.d()" ] ,
              unlines [ intdata, "codata C where C.d(Int) : Int"
                      , "function fun(C,Int): Int where"
                      , "  fun(c,a) = c.d(b)" ]         
              ]
        it "type mismatch" $ do
            let booldata = "data Bool where   true() : Bool    false() : Bool"
            let listdata = "data List<T> where empty() : List[T]   cons(T,List[T]) : List[T]"
            checkFailDef tyErrTyMismatchMsg [
              unlines [ intdata, booldata
                      , "function fun(Bool): Int where"
                      , "  fun(a) = a" ] ,
              unlines [ intdata, listdata
                      , "function fun(Int): List[List[Int]] where"
                      , "  fun(a) = cons[Int] (intZero(), empty[Int]())" ] ,
              unlines [ intdata, listdata, booldata
                      , "function fun(Int): List[Int] where"
                      , "  fun(a) = cons[Bool] (intZero(), empty[Int]())" ] ,
              unlines [ intdata, listdata, booldata
                      , "function fun(Int): List[Int] where"
                      , "  fun(a) = cons[Int] (intZero(), empty[Bool]())" ] ,
              unlines [ intdata, listdata, booldata
                      , "function fun(Int): List[Int] where"
                      , "  fun(a) = cons[Int] (true(), empty[Int]())" ] 
              ]
    describe "check polymorphism (type applications) " $ do
        let listdata = "data List <T> where empty() : List[T]" --  cons(T,List[T]) : List[T]"
        it "type argument mismatch (length)" $ do
            checkFailDef tyErrLenMismatchMsg [
              unlines [ listdata, "function <X> fun(List[X]) : List[X] where"
                      , "  fun(empty[]()) = empty[X]()" ] ,
              unlines [ listdata, "function <X> fun() : List[X] where"
                      , "  fun(empty[X,X]()) = empty[X]()" ] ,            
              unlines [ listdata, "function <X> fun() : List[X] where"
                      , "  fun() = empty[]()" ] ,
              unlines [ listdata, "function <X> fun() : List[X] where"
                      , "  fun() = empty[X,X]()" ] 
              ]
            checkFailDef tyErrTyMismatchMsg [
              unlines [ listdata, "function <X> fun() : List[X] where"
                      , "  fun() = empty[Y]()" ] ,
              unlines [ listdata, "function <X> fun() : List[X] where"
                      , "  fun() = empty[List[X]]()" ]
              ] 
    describe "argument mismatch (length and types)" $ do
        it "calls (codata selector)" $ do
            p <- prelude
            e <- parseString parseExp "coSucc(coZero()).coAdd()"
            fillExp (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "CoNat")  []) e `shouldFail` tyErrLenMismatchMsg
            
            e' <- parseString parseExp "coSucc(coZero()).coAdd(coZero(),coZero())"
            fillExp (prgSigma p) emptyContext typeNat e' `shouldFail` tyErrLenMismatchMsg
            
            e'' <- parseString parseExp "coSucc(coZero()).coAdd(coZero().coOdd())"
            fillExp (prgSigma p) emptyContext typeNat e'' `shouldFail` tyErrTyMismatchMsg
    describe "checkPattern " $ do
        it "with variables" $ do
            p <- prelude
            e <- parseString parsePat "x"
            res <- return $ fillPat (prgSigma p) emptyContext typeNat e
            res `shouldSatisfy` (\x -> case x of
              Right (Pat _ (Identifier _ "x",typeNat) VarPat, ctx) -> True
              _ -> False)
        it "with applications" $ do
            p <- prelude
            e <- parseString parsePat "zero()"
            res <- return $ fillPat (prgSigma p) emptyContext typeNat e 
            res `shouldSatisfy` (\x -> case x of
              Right (Pat _ (Identifier _ "zero", typeNat) (AppPat []), ctx)  -> True
              _ -> False)
            
            e' <- parseString parsePat "succ(n)"
            res' <- return $ fillPat (prgSigma p) emptyContext typeNat e' 
            res' `shouldSatisfy` (\x -> case x of
              Right (Pat _ (Identifier _  "succ", typeNat) (AppPat [Pat _ (Identifier _ "n", TypeT _ (Tau _ "Nat")  []) VarPat]), ctx)  -> True
              _ -> False)
            
            e'' <- parseString parsePat "succ(n)"
            res'' <- return $ fillPat (prgSigma p) [TermBind (Identifier locUndef "n", TypeT locUndef (Tau locUndef "Int") [])] typeNat e'' 
            res'' `shouldFail` tyErrTyMismatchMsg
            
          
    describe "checkExp" $ do
        it "infers construction" $ do
            p <- prelude
            e <- parseString parseExp "empty[Nat]()"
            fillExp (prgSigma p) emptyContext (TypeT locUndef (Tau locUndef "List") [typeNat]) e `shouldSatisfy` (\x -> case x of
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
    describe "polymorphism" $ do
        it "TODO" $ do
            p <- prelude    
            defs <- parseString parseDef $ unlines
                [ "function <X> myid(X) : X where myid(x) = x"
                , "function natId(Nat) : Nat where natId(x) = myid[Nat](x)"
                ]
         --   print  $ foldM fillSigma (prgSigma p) defs   
            sgm <- eitherIO $ foldM fillSigma (prgSigma p) defs
            checkSigma sgm `shouldSatisfy` (\x -> case x of
                Right _ -> True
                _ -> False)
      --  unlines  [ "function a(A[B]) : B where "
        --            , " a(A[Nat]) : Nat where "
        --            , " a(A[Bool]) : Bool where "
          --          , " a(A[C]) : C where" ]
          
          -- List[Int,Int], A[A]
          -- shadowed fun<A>... data A