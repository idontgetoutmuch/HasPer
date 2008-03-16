module Main(main) where

import System.Process
import System.Exit
import Asn1cTest
import Data.Time
import System.Directory
import Text.PrettyPrint
import Pretty
import ConstrainedType
import qualified Data.ByteString as B
import qualified Data.Binary.Strict.BitGet as BG
import Control.Monad.State
import Control.Monad.Error
import UnitTest (type9, val9, val91)
import IO
import TestData

runTest f =
   runCommands [
      ("asn1c -gen-PER " ++ f, "Failure in asn1c"),
      ("mv converter-sample.c converter-sample.c.old", "Failure in mv of converter-sample.c"),
      ("gcc -I. -o test *.c",  "Failure in gcc"),
      ("./test generated.per", "Failure in ./test")
   ]

runCommands [] =
   return "Success"
runCommands ((c,e):xs) =
   do h <- runCommand c
      d <- waitForProcess h 
      case d of
         ExitSuccess ->
            runCommands xs
         ExitFailure n ->
            return (e ++ ": " ++ show n)

genASN1 :: NamedType a -> Doc
genASN1 t =
   let (NamedType n _ u) = t in 
      text "FooBar {1 2 3 4 5 6} DEFINITIONS ::=" $$
      nest 3 (
         text "BEGIN" $$
         nest 3 (
            text n <> text " ::= " $$
            nest 3 (
               prettyType u
               ) 
           ) $$
        text "END"
        )

main = 
   do d <- getCurrentDirectory
      t <- getCurrentTime
      let u = "asn1c." ++ show (utctDay t) ++ "." ++ show (utctDayTime t)
      createDirectory u
      setCurrentDirectory u
      c <- getCurrentDirectory
      putStrLn c
      writeASN1AndC "generated.asn1" "generated.c" integerType8' integerVal81
      runTest "generated.asn1"
      readGen "generated.per" integerType8'
      setCurrentDirectory d

readGen :: String -> ASNType a -> IO ()
readGen perFile t =
   do h <- openFile perFile ReadMode
      b <- B.hGetContents h
      let d = BG.runBitGet b (mFromPer' t)
      case d of
         Left s  -> putStrLn ("Left " ++ show s)
         Right x -> putStrLn ("Right " ++ render (prettyTypeVal t x))
