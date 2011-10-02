module Main(main) where

import NewTestData
import PERWriter
import ASNTYPE
import NewPretty

import qualified Data.ByteString.Lazy as BL
import qualified Data.Binary.BitBuilder as BB

test t v = BL.unpack $ BB.toLazyByteString $ selectOutput $ extractValue $ encode t [] v

roundTrip t v = runDecode t (runEncode t v)

main = putStrLn "Hello"