module Uroboro.ParserSpec where

import Utils
import SpecHelper

import Data.Either (isRight)
import Text.Parsec (eof)

import Uroboro.Error
import Uroboro.ExternalSyntax

-- these strings can be parsed by
sVar = "a" -- pat, expr
sTrue = "true()" -- pat, expr (cop <- no typechecking)
sSucc = "succ(n)" -- pat, expr (cop <- no typechecking)
sFun0 = "f()" -- cop, pat, expr
sFun2 = "f(a,b)" -- cop, pat, expr
sFunNested = "f(b())"  -- cop, pat, expr
sDesApp1 = "fd().d()" -- cop, expr
sDesApp2 = "fd(a,b).d0().d2(c,d)" -- cop, expr
sVarDesApp = "x.fd()" -- expr

-- these cannot be parsed in general
sFailArg = "f(a).hc(b,ca.des())" -- negative argument

-- syntactic errors
sFailL = "f(a"
sFailR = "f)"
sFailB = "f)("
sFailP = "f(a)..(a)"
sFailRuleL = "a() = "
sFailRuleR = "= a"
sFailRuleB = "a = a"

sFailWhere = "data Empty whre"
sFailWithoutD = "data where"
sFailWithoutC = "codata where"
sFailWithoutF = "function where"
sFailDataEmpty = "dat Empty where"
sFailCodEmpty = "codta CEmpty where"
sFailFunEmpty = "fnction empty() where"
sFailFunEmpty2 = "function empty where"
sFailFunEmptyL = "function empty( where"
sFailFunEmptyR = "function empty) where"
sFailFunEmptyW = "function empty()"


listSyntaxErr = [sFailL,sFailR,sFailB,sFailP,sFailRuleL,sFailRuleR,sFailRuleB] 
 ++ [sFailWhere, sFailWithoutD, sFailWithoutC, sFailWithoutF, sFailDataEmpty, sFailCodEmpty, sFailFunEmpty, sFailFunEmpty2,sFailFunEmptyL, sFailFunEmptyR, sFailFunEmptyW]

sFailDataL = "data Em[() where"
sFailDataR = "data Em]() where"
sFailCodL = "codata <T Stream[] where"
sFailCodR = "codata > Stream[] where"
sFailFun = "function <A> fun() : A where fun() = fun[A]"

listSyntaxErrPoly = [sFailDataL, sFailDataR, sFailCodL, sFailCodR, sFailFun ]

-- pat < exp
listPatCop = [sTrue, sSucc, sFun0, sFun2, sFunNested]
listNotPatNotCop = [sFailArg,sVarDesApp]

listPat = sVar : listPatCop
listNotPat = listNotPatNotCop ++ [sDesApp1, sDesApp2]

-- cop < exp (cop = pat / id + desapp)
listCop = listPatCop++ [sDesApp1, sDesApp2]
listNotCop = sVar : listNotPatNotCop

-- exp
listExp = sVarDesApp : (listPat ++ listCop)
listNotExp = [sFailArg]

-- parseRule
toRules lhsLs rhsLs = [ a ++ " = " ++ b | a <- lhsLs, b <- rhsLs]
listRule = toRules listCop listExp
listNotRule = toRules listNotCop listExp ++ toRules listCop listNotExp ++ toRules listNotCop listNotExp


sDataEmpty = "data Empty where"
sCodEmpty = "codata CEmpty where"
sFunEmpty = "function empty() : X where"
listDefEmpty = [ sDataEmpty, sCodEmpty, sFunEmpty ]

sDataInt = "data Int where"
        ++ "  zero(): Int"
        ++ "  succ(Int): Int"

sCodInt = "codata CoInt where"
       ++ "  CoInt.add(CoInt) : CoInt"
       ++ "  CoInt.even() : CoBool"

sFunInt = "function fun(A,Int) : Int where"
       ++ "  fun(x,zero()) = zero()"
       ++ "  fun(x,succ(n)) = zero()"
listDefInt = [ sDataInt, sCodInt, sFunInt ]
  
                                         
sDataPoly = "data List<T> where"
         ++ "  empty(): List[T]"
         ++ "  cons(T,List[T]): List[T]"            
sCodPoly = "codata Stream<T> where"
       ++ "  Stream[T].head(): T"
       ++ "  Stream[T].tail(): T"

sFunPoly = "function <A,B> idFst(A, B) : List[A] where"
        ++ "  idFst(a,b) = cons[A](a,empty[A]())"
sFunNegPoly = "function <A,B> idFst(A, B) : List[A] where"
        ++ "  idFst(a,b).tail[]().tail[R]().head() = cons[A](a,empty[A]())"

sNonsensePoly = "function <A,T,Z> xy(C, B[T]) : X where"
                ++ " xy1zz0() = a1[D,E,F](x)"
listDefPoly =  [ sDataPoly, sCodPoly, sFunPoly, sFunsNegPoly, sNonsensePoly ]


uroparseSat parser ls = mapM_ (\x -> parser `shouldAccept` x) ls
uroparseRej parser ls = mapM_ (\x -> parser `shouldReject` x) ls

parseExpressionTestcase = parseExpression "<testcase>"
uroparseExp   = parseTestcase parseExp
uroparsePat   = parseTestcase parsePat
uroparseCoPat = parseTestcase parseCoPat
uroparseDef   = parseTestcase parseDef

spec :: Spec
spec = do
    describe "illformed syntax" $ 
        it "results in parsing error" $ do
            uroparseRej parsePat listSyntaxErr
            uroparseRej parseCoPat listSyntaxErr
            uroparseRej parseExp listSyntaxErr
            uroparseRej parseRule listSyntaxErr
            uroparseRej parseDef listSyntaxErr
    describe "parsePat" $ do
        it "parses patterns (positive arguments)" $ 
            uroparseSat parsePat listPat
        it "cannot parse illformed pattern" $ 
            uroparseRej parsePat listNotPat
        it "keeps argument order right" $ 
            uroparsePat "f(a,b)" `shouldSatisfy` (\x ->
              case x of
                Right (AppPat _ (Identifier _ "f") []  [
                    VarPat _ (Identifier _ "a"), 
                    VarPat _ (Identifier _ "b") 
                                            ] ) -> True
                _ -> False)   
    describe "parseCoPat" $ do
        it "parses copatterns" $ 
            uroparseSat parseCoPat listCop
        it "cannot parse illformed copattern" $ 
            uroparseRej parseCoPat listNotCop               
        it "keeps selector order right" $ 
            uroparseCoPat "f().t().h()" `shouldSatisfy` (\x ->
              case x of
                Right (Cop _ (Identifier _ "f") [] (DesCopNature [
                    DApsCop _ (Identifier _ "t") [] [], 
                    DApsCop _ (Identifier _ "h") [] [] 
                                            ] )) -> True
                _ -> False)
    describe "parseExp" $ do
        it "parses expressions with variables, functions and destructor calls" $ 
            uroparseSat parseExp listExp
        it "cannot parse illformed expressions" $ 
            uroparseRej parseExp listNotExp 
    describe "parseRules" $ do   
        it "parses rules" $ 
            uroparseSat parseRule listRule
        it "cannot parse illformed rules" $
            uroparseRej parseRule listNotRule
    describe "definitions" $ do
        it "accepts empty definitions" $ 
            uroparseSat parseDef listDefEmpty
        it "accepts definitions with signatures" $ 
            uroparseSat parseDef listDefInt           
        it "keeps constructor order right" $ do
            uroparseDef sDataInt `shouldSatisfy` (\x -> case x of
              Right [Def _ [] (DatDefNature (Tau _ "Int")  
                      [ConSig _ (Identifier _ "zero") [] (TypeT _ (Tau _ "Int") []) ConSigNature,
                       ConSig _ (Identifier _ "succ") _ (TypeT _ (Tau _ "Int") []) ConSigNature])] -> True
              _ -> False)
            let sourcePoly = "codata Stream<T> where Stream[T].head(): T"
            uroparseDef sourcePoly `shouldSatisfy` (\x -> case x of  
              Right [Def _ [Abs _ "T"] 
                      (CodDefNature (Tau _"Stream") 
                                    [DesSig _ (Identifier _ "head") [] (TypeVar _ "T") (DesSigNature (TypeT _ (Tau _"Stream") [TypeVar _ "T"])) ])] -> True
              _ -> False)
    describe "polymorphism"
        it "accepts wellformed definitions" $ 
            uroparseSat parseDef listDefPoly
        it "rejects" $ 
            uroparseRej parseRule listSyntaxErrPoly
    describe "command line" $ do
        it "ignores whitespace" $ 
            parseExpression "" "  x  " `shouldSatisfy` (\x -> case x of
              Right (Expr (VarExp _ (Identifier _ "x"))) -> True
              _ -> False)
        it "uses the longest match" $ 
            parseExpression "" "x()" `shouldSatisfy` (\x -> case x of
              Right (Expr (AppExp _ (Identifier _ "x") [] [])) -> True
              _ -> False)
    describe "uroparse" $ do
        it "parses a file (here samples/lib/bool.uro)" $ do
            fname <- return "samples/lib/bool.uro"
            input <- readFile fname
            parseFile fname input `shouldSatisfy` isRight
        it "parse expressions" $ do
            parseExpressionTestcase "true()" `shouldSatisfy` isRight
            parseExpressionTestcase "succ(zero())" `shouldSatisfy` isRight
            parseExpressionTestcase "f(a).hc(b,ca())" `shouldSatisfy` isRight
            