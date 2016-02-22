module Utils where

import Control.Applicative ((<*))
import Test.Hspec
import Text.Parsec (eof)
import Uroboro.Token
import Uroboro.Parser 
import Uroboro.Error

-- | Use up all input for one parser.
exactly :: Parser a -> Parser a
exactly parser = whiteSpace *> parser <* eof
 
uroparse' :: Parser a  -> String -> Either Error a
uroparse' parser input = uroparse (exactly parser) "" input

-- |Exceptions instead of Either.
parseString :: Parser a -> String -> IO a
parseString parser input = case uroparse' parser input of
    Left l -> ioError $ userError ((show l) ++ " (in parseString)")
    Right v -> return v
    
shouldAccept :: Parser a -> String -> Expectation
shouldAccept p s = case uroparse (p <* eof) "<testcase>" s of
  Left e -> expectationFailure (show e)
  Right _ -> return ()

shouldReject :: Show a => Parser a -> String -> Expectation
shouldReject p s = case uroparse (p <* eof) "<testcase>" s of
  Left _ -> return ()
  Right x -> expectationFailure $
               "Parsing \"" ++ s ++ "\" succeded with result " ++ show x ++ "."

shouldSat :: (Eq a, Show a) => Parser a -> String -> a -> Expectation
shouldSat p s x = case uroparse (p <* eof) "<testcase>" s of
  Left e -> expectationFailure (show e)
  Right r -> if r == x then return () else expectationFailure (show r)
           
shouldReportLocation :: Either Error a -> String -> Expectation
shouldReportLocation (Left e) loc = show e `shouldContain` loc
shouldReportLocation (Right _) _ = expectationFailure "Parsing succeeded."

-- |Assert error message
shouldFail :: Show a => Either Error a -> String -> Expectation
Left (MakeError _ errtype msg) `shouldFail` prefix = --do print msg;
                                                        msg `shouldStartWith` prefix  --takeWhile (/= ':') msg `shouldBe` prefix
Right x                `shouldFail` prefix = expectationFailure 
        ("expected: " ++ prefix ++ "\n but got: " ++ show x)

failingAfter :: FilePath -> String -> Either Error a
failingAfter = uroparse (exactly (fail ""))
