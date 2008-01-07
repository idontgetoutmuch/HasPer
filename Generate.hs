module Generate where

import System.IO
import Text.PrettyPrint
import QuickTest

test1 fileName =
   do d <- genModule
      writeFile fileName (render d)


