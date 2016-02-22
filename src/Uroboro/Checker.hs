module Uroboro.Checker where

import Control.Monad (foldM) 
import qualified Uroboro.ExternalSyntax as EST
import Uroboro.InternalSyntax 
import Uroboro.TransformExtToInt 
import Uroboro.Error
import Uroboro.FillSigma
import Uroboro.FillRules

-- |Typecheck external syntax tree (parser output)
typecheck :: [EST.Def] -> Either Error Program
typecheck defs = do 
    sgm1 <- foldM fillSigma emptySigma defs
    sgm2 <- checkSigma sgm1
    -- for having typed rules we need complete sigma
    foldM fillRules (emptyProgram sgm2) defs
