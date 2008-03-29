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
import IO
import TestData
import System.FilePath
import System.Info

-- Uncomment the line below for Windows
-- skeletons = "c:\\Users\\Dom\\asn1c-0.9.21\\skeletons"

-- Comment the line below for Windows
skeletons = "/usr/local/share/asn1c"

asn1c = "asn1c"
asn1cOptions = "-gen-PER -fnative-types -S"

cc = 
   case os of
      "mingw32" -> "lcc"
      _         -> "gcc"

linker =
   case os of
      "mingw32" -> "lcclnk"
      _         -> "gcc"

objectSuffix =
   case os of
      "mingw32" -> "obj"
      _         -> "o"
      

cIncludes = 
   case os of
      "mingw32" -> "-I" ++ skeletons
      _         -> "-I" ++ skeletons

ccOptions =
   case os of
      "mingw32" -> ""
      _         -> "-c"

compile f = (cc ++ " " ++ ccOptions ++ " " ++ cIncludes ++ " " ++ f, "Failure compiling " ++ f)

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

test genFile ty@(TYPEASS name _ _) val =
   do d <- getCurrentDirectory
      t <- getCurrentTime
      let u = "asn1c." ++ show (utctDay t) ++ "." ++ show (utctDayTime t)
      createDirectory u
      setCurrentDirectory u
      CE.catch (do writeASN1AndC (genFile <.> "asn1") (genFile <.> "c") ty val
                   runCommands [(asn1c ++ " " ++ asn1cOptions ++ " " ++ skeletons ++ " " ++ (genFile <.> "asn1"), "Failure in asn1c")]
                   d <- getCurrentDirectory
                   fs <- getDirectoryContents d
                   let cFiles = 
                          case os of
                             "mingw32" -> 
                                (genFile <.> "c"):(name <.> "c"):(cFiles' ["converter-sample.c"] ".c.lnk" fs)
                             _ ->
                                (genFile <.> "c"):(name <.> "c"):(cFiles' [genFile <.> "c", name <.> "c", "converter-sample" <.> "c"] ".c" fs)
                   putStrLn (show cFiles)
                   putStrLn (show (map compile cFiles))
                   runCommands (map compile cFiles)
                   putStrLn (linker ++ " " ++ linkerOut genFile ++ " " ++ ("*" <.> objectSuffix))
                   runCommands [
                      (linker ++ " " ++ linkerOut genFile ++ " " ++ ("*" <.> objectSuffix), "Failure linking"),
                      ((executable genFile) ++ " " ++ (genFile <.> "per"), "Failure executing")
                      ]
                   readGen (genFile <.> "per") ty)
               (\e -> hPutStrLn stderr ("Problem with generating / compiling\n" ++ show e))
      setCurrentDirectory d
   where
      cFiles' excls suffix =
         map (skeletons </>) .
         filters (map (/=) excls) . 
         map (<.> ".c") . 
         map fst . 
         filter ((== suffix). snd) . 
         (map splitExtensions)
      filters = flip (foldr filter)
      linkerOut f = 
         case os of
            "mingw32" -> "-o " ++ (f <.> "exe")
            _         -> "-o " ++ f
      executable f = 
         case os of
            "mingw32" -> f <.> "exe"
            _         -> joinPath [".",f]
test _ _ _  = error "Can only test type assignments"
    
readGen :: String -> ASNType a -> IO ()
readGen perFile t =
   do h <- openFile perFile ReadMode
      b <- B.hGetContents h
      let d = BG.runBitGet b (mFromPer' t)
      case d of
         Left s  -> putStrLn ("Left " ++ show s)
         Right x -> putStrLn ("Right " ++ render (prettyTypeVal t x))

main = test "generated" bigIntSeq1Type' bigIntSeq1Val 

