module Uroboro.Error where

import Data.List (intercalate)
import Text.Parsec.Error (ParseError, errorPos, showErrorMessages, errorMessages)

import Uroboro.Location

data Error = MakeError Location String String
  
-- |Fail the monad, but with location.
failAt :: Location -> String -> String -> Either Error a
failAt pos errorType message = Left $ MakeError pos errorType message

-- | Convert error to custom error type
convertError :: ParseError -> Error
convertError err = MakeError location "ParseError" messages where
  pos = errorPos err
  location = convertLocation pos
  messages = showErrorMessages
               "or" "unknown parse error" "expecting"
               "unexpected" "end of input"
               (errorMessages err)

-- intercalate xs xss: 
-- inserts list xs in between lists in xss and concatenates the result

instance Show Error where
  show (MakeError location errorType message) =
    intercalate ":"
      [ show location
      , " " ++ errorType
      ] ++ (unlines $ map ("  " ++) $ lines $ message)

            