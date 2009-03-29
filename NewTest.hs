module Main(main) where

import NewTestData
import PER
import ASNTYPE
import NewPretty

t = encode sibDataVariableType [] sibDataVariableValue
t' = encode' sibDataVariableType [] sibDataVariableValue

main = undefined