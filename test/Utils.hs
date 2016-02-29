module Utils where

import Control.Applicative ((<*))
import Test.Hspec
import Text.Parsec (eof)
import Uroboro.Token
import Uroboro.Parser 
import Uroboro.Error
 
parseTestcase :: Parser a -> String -> Either Error a
parseTestcase parser = uroparse (exactly parser) "<testcase>" -- input

-- |Exceptions instead of Either.
parseString :: Parser a -> String -> IO a
parseString parser input = case parseTestcase parser input of
    Left l -> ioError $ userError (show l ++ " (in parseString)")
    Right v -> return v


-- for TokenSpec and ParserSpec
shouldAccept :: Parser a -> String -> Expectation
shouldAccept p s = case parseTestcase p s of
  Left e -> expectationFailure (show e)
  Right _ -> return ()

shouldReject :: Show a => Parser a -> String -> Expectation
shouldReject p s = case parseTestcase p s of
  Left _ -> return ()
  Right x -> expectationFailure $
               "Parsing \"" ++ s ++ "\" succeded with result " ++ show x ++ "."

           
shouldReportLocation :: Either Error a -> String -> Expectation
shouldReportLocation (Left e) loc = show e `shouldContain` loc
shouldReportLocation (Right _) _ = expectationFailure "Parsing succeeded."

-- |Assert error message
shouldFail :: Show a => Either Error a -> String -> Expectation
Left (MakeError _ errtype msg) `shouldFail` prefix = --do print msg;
                                                        msg `shouldStartWith` prefix
Right x                `shouldFail` prefix = expectationFailure 
        ("expected: " ++ prefix ++ "\n but got: " ++ show x)

failingAfter :: FilePath -> String -> Either Error a
failingAfter = uroparse (exactly (fail ""))
