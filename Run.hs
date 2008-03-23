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
import qualified Control.Exception as CE
import UnitTest (type9, val9, val91)
import IO
import TestData
import System.FilePath
import System.Info

skeletons = "c:\\Users\\Dom\\asn1c-0.9.21\\skeletons"

asn1c = "asn1c -gen-PER -fnative-types -S c:\\Users\\Dom\\asn1c-0.9.21\\skeletons "

cc = "lcc"
cIncludes = "-I" ++ skeletons

compile f = (cc ++ " " ++ cIncludes ++ " " ++ f, "Failure compiling " ++ f)

runas1nc f =
   runCommands [
      (asn1c ++ f, "Failure in asn1c")
   ]

runTest f =
   runCommands [
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

test ty@(TYPEASS name _ _) val =
   do d <- getCurrentDirectory
      t <- getCurrentTime
      let u = "asn1c." ++ show (utctDay t) ++ "." ++ show (utctDayTime t)
      createDirectory u
      setCurrentDirectory u
      CE.catch (do writeASN1AndC "generated.asn1" "generated.c" ty val
                   runas1nc "generated.asn1"
                   d <- getCurrentDirectory
                   fs <- getDirectoryContents d
                   let cFiles = 
                          case os of
                             "mingw32" -> 
                                cFiles' ".c.lnk" fs
                             _ ->
                                cFiles' ".c" fs
                   putStrLn (show cFiles)
                   runCommands (map compile cFiles)
                   return ())
               (\e -> hPutStrLn stderr ("Problem with generating / compiling " ++ show e))
      setCurrentDirectory d
   where
      cFiles' suffix =
         map (skeletons </>) .
         filter (/= "converter-sample.c") .
         map (flip addExtension ".c") . 
         map fst . 
         filter ((== suffix). snd) . 
         (map splitExtensions)
test _ _ = error "Can only test type assignments"

main = test tSequence6' tSeqVal61

readGen :: String -> ASNType a -> IO ()
readGen perFile t =
   do h <- openFile perFile ReadMode
      b <- B.hGetContents h
      let d = BG.runBitGet b (mFromPer' t)
      case d of
         Left s  -> putStrLn ("Left " ++ show s)
         Right x -> putStrLn ("Right " ++ render (prettyTypeVal t x))
