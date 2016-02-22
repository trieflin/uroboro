module Uroboro.TokenSpec where

import Utils
import SpecHelper

import Uroboro.Error

spec :: Spec
spec = do
  describe "Token" $ do
    context "when looking for comments" $ do
        it "recognizes end-of-line comments starting with --" $ do
            whiteSpace `shouldAccept` "-- comment \n"
            whiteSpace `shouldReject` "-- comment \nfoo"
        it "recognizes comments between {- and -}" $ do
            whiteSpace `shouldAccept` "{- comment -}"
            whiteSpace `shouldReject` "{- comment -}foo"
        it "recognizes nested comments" $ do
            whiteSpace `shouldAccept` "{- {- -} -}"
            whiteSpace `shouldReject` "{- {- -}"
        it "recognizes {-# LINE #-} pragmas" $ do
            whiteSpace `shouldAccept` "{-# LINE 5 \"foo\" #-}\n"
        it "recognizes invalid pragmas as comments" $ do
            whiteSpace `shouldAccept` "{-# #-}"
            whiteSpace `shouldAccept` "{-# FOO #-}"
            whiteSpace `shouldAccept` "{-# FOO -}"
            whiteSpace `shouldAccept` "{- FOO #-}"
            whiteSpace `shouldAccept` "{-# LINE #-}"
            whiteSpace `shouldAccept` "{-# LINE 5 foo #-}"
            whiteSpace `shouldAccept` "{-# LINE 5 \"foo #-}"
            whiteSpace `shouldAccept` "{-# LINE \"foo\" #-}"
    context "when looking for a keyword" $ do
        it "accepts the keyword" $ do
            reserved "codata" `shouldAccept` "codata"
            reserved "data" `shouldAccept` "data"
            reserved "function" `shouldAccept` "function"
            reserved "where" `shouldAccept` "where"
        it "rejects identifiers starting with the keyword" $ do
            reserved "codata" `shouldReject` "codatatype"
            reserved "data" `shouldReject` "datatype"
            reserved "function" `shouldReject` "functional"
            reserved "where" `shouldReject` "whereas"
    context "when looking for identifiers" $ do
        it "rejects keywords" $ do
            identifier `shouldReject` "codata"
            identifier `shouldReject` "data"
            identifier `shouldReject` "function"
            identifier `shouldReject` "where"
        it "accepts identifiers starting with keywords" $ do
            identifier `shouldAccept` "codatatype"
            identifier `shouldAccept` "datatype"
            identifier `shouldAccept` "functional"
            identifier `shouldAccept` "whereas"
    context "when looking for brackets" $ do
        it "accepts bracket-pairs" $ do
            parens (commaSep identifier) `shouldAccept` "()"
            parens (commaSep identifier) `shouldAccept` "(a,b,c)"
            parens (commaSep identifier) `shouldReject` ")("
            parens (commaSep identifier) `shouldReject` "("
            parens (commaSep identifier) `shouldReject` ")"
            parens (commaSep identifier) `shouldReject` "(,b,c)"
            angles (commaSep identifier) `shouldAccept` "<>"
            angles (commaSep identifier) `shouldAccept` "<a,b,c>"
            angles (commaSep identifier) `shouldReject` "><"
            angles (commaSep identifier) `shouldReject` ">"
            angles (commaSep identifier) `shouldReject` ">"
            angles (commaSep identifier) `shouldReject` "<,b,c>"
            brackets (commaSep identifier) `shouldAccept` "[]"
            brackets (commaSep identifier) `shouldAccept` "[a,b,c]"
            brackets (commaSep identifier) `shouldReject` "]["     
            brackets (commaSep identifier) `shouldReject` "["
            brackets (commaSep identifier) `shouldReject` "]"
            brackets (commaSep identifier) `shouldReject` "[,b,c]"      
    context "when looking for symbols" $ do
        it "accepts dot, colon, eq" $ do
            colon `shouldAccept` ":"
            dot `shouldAccept` "."
            eq  `shouldAccept` "="      
    context "when reporting errors" $ do
        it "includes location information" $ do
            failingAfter "foo" ""
              `shouldReportLocation` "foo:1:1"
            failingAfter "foo" "   "
              `shouldReportLocation` "foo:1:4"
            failingAfter "foo" "\n  "
              `shouldReportLocation` "foo:2:3"
--        it "processes pragmas" $ do
--            failingAfter "foo" "{-# LINE 1 \"bar\" #-}\n"
--              `shouldReportLocation` "bar:1:1"
--            failingAfter "foo" "{-# LINE 1 \"bar\" #-}\n   "
--              `shouldReportLocation` "bar:1:4"
--            failingAfter "foo" "{-# LINE 1 \"bar\" #-}\n\n  "
--              `shouldReportLocation` "bar:2:3"
--            failingAfter "foo" "\n{-# LINE 5 \"bar\" #-}\n"
--              `shouldReportLocation` "bar:5:1"
--            failingAfter "foo" "\n{-# LINE 5 \"bar\" #-}\n\n"
--              `shouldReportLocation` "bar:6:1"
  