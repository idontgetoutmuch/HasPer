module Main (main) where

import Test.HUnit hiding (Test)
import Test.QuickCheck hiding ((.&.))
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.Framework.Providers.HUnit

import NewTestData
import PERWriter
import ASNTYPE
import NewPretty

roundTrip t v = runDecode t (runEncode t v)

refIntTest1 = roundTrip rt1 v1 @?= v1

refSeqTest1 = roundTrip rt3 v3 @?= v3

foo1 = roundTrip sibDataVariableType sibDataVariableValue @?= sibDataVariableValue

tests :: [Test]
tests =
    [ testCase "Referenced unconstrained INTEGER" refIntTest1
    , testCase "Referenced SEQUENCE" refSeqTest1
    , testCase "Foo" foo1
    ]

main = defaultMain tests
