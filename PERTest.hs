module Main(main) where

import NewTestData
import PER
import ASNTYPE
import NewPretty
import Run

import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import Data.Binary.BitPut
import Data.Binary.Strict.BitGet
import Control.Monad.Error
import Data.Bits
import Test.HUnit

{- FIXME: This will do for now until we have the correct               -}
{- decoding monad (with the using a custom class constraint).          -}
decodeEncode :: ASNType a -> a -> a
decodeEncode t x =
   do let (possibleError, encoding) = extractValue (encode t [] x)
      case possibleError of
         Left e -> error (show e)
         Right y -> let bs = B.pack . BL.unpack . runBitPut . mapM_ (putNBits 1) $ encoding
                    in 
                       case runBitGet bs (runErrorT (fromPER t)) of
                       Left s -> error s
                       Right x -> case x of
                                  Left f -> error (show f)
                                  Right y -> y

dESibDataVariableValue = decodeEncode sibDataVariableType sibDataVariableValue

test2 = TestCase (do let v = Val (2^100)
                     e <- encodeTest "urk" rt1 v
                     assertEqual "INTEGER Inter-operability test 1" v (Val e))

bitStringConsTest1 =
   TestCase (
      assertEqual "Constrained BIT STRING Test 1" sibDataVariableValue dESibDataVariableValue
   )

tests =
   [ bitStringConsTest1
   , test2
   ]

main = runTestTT (TestList tests)