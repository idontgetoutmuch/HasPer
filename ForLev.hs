module Main(main) where

import Asn1cTest
import UnitTest hiding (main)
import Text.PrettyPrint

main =
   do writeFile "generated.c" (render (genC type9 val91))