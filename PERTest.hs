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

import Distribution.Version
import Paths_PER (version)
import Text.PrettyPrint

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

deVInteger2 = decodeEncode tInteger2 vInteger2

test2 = TestCase (do let v = Val (2^100)
                     e <- encodeTest "urk" rt1 v
                     assertEqual "INTEGER Inter-operability test 1" v (Val e))

test3 = TestCase (do let v = Val 0
                     e <- encodeTest "urk" rt1 v
                     assertEqual "INTEGER Inter-operability test 2" v (Val e))


bitStringConsTest1 =
   TestCase (
      assertEqual "Constrained BIT STRING Test 1" sibDataVariableValue dESibDataVariableValue
   )

integerConsTest1 =
   TestCase (
      assertEqual "Constrained INTEGER Test1" vInteger2 deVInteger2
   )

tests =
   [ bitStringConsTest1
   , integerConsTest1  
   , test2
   , test3
   ]

main = do
   putStrLn ("Running tests for PER " ++ (render $ hcat $ punctuate (text ".") $ map int $ versionBranch $ version))
   runTestTT (TestList tests)