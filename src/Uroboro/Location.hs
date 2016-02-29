module Uroboro.Location where

import Text.Parsec.Pos (SourcePos,sourceName, sourceLine, sourceColumn)
import Data.List (intercalate)

data Location = MakeLocation FilePath Int Int deriving (Eq)

-- | Convert location to custom location type
convertLocation :: SourcePos -> Location
convertLocation pos = MakeLocation name line column where
  name = sourceName pos
  line = sourceLine pos
  column = sourceColumn pos
  
-- intercalate xs xss: 
-- inserts list xs in between lists in xss and concatenates the result
instance Show Location where
  show (MakeLocation name line column) =
    intercalate ":"
      [ name
      , show line
      , show column
      ]

newtype Hidden a = Hidden a     
instance Eq (Hidden a) where
    Hidden x == Hidden y = True
instance Show a => Show (Hidden a) where
    show (Hidden a) = show a
    