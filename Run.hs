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

skeletons = "c:\\Users\\Dom\\asn1c-0.9.21\\skeletons"

asn1c = "asn1c -gen-PER -fnative-types -S c:\\Users\\Dom\\asn1c-0.9.21\\skeletons "

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

test ty val =
   do d <- getCurrentDirectory
      t <- getCurrentTime
      let u = "asn1c." ++ show (utctDay t) ++ "." ++ show (utctDayTime t)
      createDirectory u
      setCurrentDirectory u
{-
      CE.catch (do writeASN1AndC "generated.asn1" "generated.c" ty val
                   runas1nc "generated.asn1"
                   renameFile "converter-sample.c" "converter-sample.c.old"
                   runTest "generated.asn1"
                   readGen "generated.per" ty)
               (\e -> hPutStrLn stderr ("Problem with generating / compiling " ++ show e))
-}
      CE.catch (do writeASN1AndC "generated.asn1" "generated.c" ty val
                   runas1nc "generated.asn1"
                   d <- getCurrentDirectory
                   fs <- getDirectoryContents d
                   let cfiles = map (skeletons </>) .
                                map (flip addExtension ".c") . 
                                map fst . 
                                filter ((== ".c.lnk"). snd) . 
                                (map splitExtensions) $ 
                                fs
                   putStrLn (show cfiles))
               (\e -> hPutStrLn stderr ("Problem with generating / compiling " ++ show e))
      setCurrentDirectory d

main = test tSequence6' tSeqVal61

foo = 
   do d <- getCurrentDirectory
      fs <- getDirectoryContents d
      putStrLn (show fs)
      let cfiles = map (flip addExtension ".c") . map fst . filter ((== ".c.lnk"). snd) . (map splitExtensions) $ fs
      putStrLn (show cfiles)
      let (n,e) = splitExtensions (fs!!4)
      h <- openFile (skeletons </> (n <.> "c")) ReadMode
      b <- hGetContents h
      putStrLn (show b)

readGen :: String -> ASNType a -> IO ()
readGen perFile t =
   do h <- openFile perFile ReadMode
      b <- B.hGetContents h
      let d = BG.runBitGet b (mFromPer' t)
      case d of
         Left s  -> putStrLn ("Left " ++ show s)
         Right x -> putStrLn ("Right " ++ render (prettyTypeVal t x))
