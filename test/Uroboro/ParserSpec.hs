module Uroboro.ParserSpec where

import Utils
import SpecHelper

import Data.Either (isRight)
import Text.Parsec (eof)

import Uroboro.Error
import Uroboro.ExternalSyntax

uroparseSat parser string res = 
    uroparse' parser string `shouldSatisfy` (\x ->
        case x of
            Right res -> True
            _         -> False)

spec :: Spec
spec = do
    describe "uroparse" $ do
        it "parses a file.uro, here samples/lib/bool.uro" $ do
            fname <- return "samples/lib/bool.uro"
            input <- readFile fname
            uroparse parseDef fname input `shouldSatisfy` isRight
        it "parse file, see above" $ do
            fname <- return "samples/lib/bool.uro"
            input <- readFile fname
            parseFile fname input `shouldSatisfy` isRight
        it "parse expressions" $ do
            parseExpression "" "true()" `shouldSatisfy` isRight
            parseExpression "" "succ(zero())" `shouldSatisfy` isRight
            parseExpression "" "f(a).headc[Nat](b,c.d[Bool]())" `shouldSatisfy` isRight
            uroparse' parseExp "true()" `shouldSatisfy` isRight
            uroparse' parseExp "succ(zero())" `shouldSatisfy` isRight
            uroparse' parseExp "f(a).head[Nat](b,c.d[Bool]())" `shouldSatisfy` isRight                    
    describe "parsePat" $ do
        it "parse patterns" $ do 
            uroparse' parsePat "a" `shouldSatisfy` isRight
            uroparse' parsePat "succ(n)" `shouldSatisfy` isRight
            uroparse' parsePat "fun(a,fun(b,c))" `shouldSatisfy` isRight
            uroparse' parsePat "x.fun(b)" `shouldNotSatisfy` isRight 
            uroparse' parsePat "fun().a()" `shouldNotSatisfy` isRight
            uroparse' parsePat "fun(fun2().b())" `shouldNotSatisfy` isRight       
    describe "parseCoPat" $ do
        it "gets selector order right" $ do
            uroparse' parseCoPat "fib().tailc[Nat[]]().headc[Nat[]]()" `shouldSatisfy` (\x ->
              case x of
                Right (Cop _ (Identifier _ "fib") [] (DesCopNature [
                    DApsCop _ (Identifier _ "tailc") [TypeT _ (Tau _ "Nat") []] [], 
                    DApsCop _ (Identifier _ "headc") [TypeT _ (Tau _ "Nat") []] [] 
                                            ] )) -> True
                _ -> False)
        it "application pattern" $
            uroparse' parseCoPat "add(x, succ(y))" `shouldSatisfy` (\x ->
              case x of
                Right (Cop _ (Identifier _ "add") 
                         [VarPat _ (Identifier _ "x"), AppPat _ (Identifier _ "succ") [] [VarPat _ (Identifier _ "y")] ] AppCopNature) -> True
                _ -> False)
    describe "signature" $ do
        it "observes argument order (constructor)" $ do
            let source = "data Int where zero(): Int[]"
            uroparse parseDef "" source `shouldSatisfy` (\x -> case x of
              Right [Def _ [] (DatDefNature (Tau _ "Int")  [ConSig _ (Identifier _ "zero") [] (TypeT _ (Tau _ "Int") []) ConSigNature ])] -> True
              _ -> False)
        it "observes argument order (destructor)" $ do
            let source = "codata Stream<T> where Stream[T].head(): T"
            uroparse parseDef "" source `shouldSatisfy` (\x -> case x of  
              Right [Def _ [Abs _ "T"] 
                      (CodDefNature (Tau _"Stream") 
                                    [DesSig _ (Identifier _ "head") [] (TypeVar _ "T") (DesSigNature (TypeT _ (Tau _"Stream") [TypeVar _ "T"])) ])] -> True
              _ -> False)
        it "accepts empty functions" $ do
            let source = "function foo() : Foo[] where"
            uroparse parseDef "" source `shouldSatisfy` (\x -> case x of
              Right [Def _ [] (FunDefNature (FunSig _ (Identifier _ "foo") [] (TypeT _ (Tau _ "Foo") []) FunSigNature) [])] -> True
              _ -> False)
        it "accepts empty data types" $ do
            let source = "data Foo where"
            uroparse parseDef "" source `shouldSatisfy` (\x -> case x of
              Right [Def _ [] (DatDefNature (Tau _ "Foo") [] ) ] -> True
              _ -> False)
        it "accepts empty codata types" $ do
            let source = "codata Foo where"
            uroparse' parseDef source `shouldSatisfy` (\x -> case x of
              Right [Def _ _ (CodDefNature (Tau _ "Foo") []) ] -> True
              _ -> False)
    describe "command line" $ do
        it "ignores whitespace" $ do
            parseExpression "" "  x  " `shouldSatisfy` (\x -> case x of
              Right (VarExp _ (Identifier _ "x")) -> True
              _ -> False)
        it "uses the longest match" $ do
            parseExpression "" "x()" `shouldSatisfy` (\x -> case x of
              Right (AppExp _ (Identifier _ "x") [] []) -> True
              _ -> False)              