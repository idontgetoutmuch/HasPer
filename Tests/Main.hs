module Main where

import qualified Tests.QuickCheck.Integer as QC
import qualified Tests.SmallCheck.Integer as SC

main =
   do SC.tests
      QC.tests