{-# OPTIONS_GHC -fwarn-unused-imports -fwarn-incomplete-patterns
                -XScopedTypeVariables
#-}

module Run(encodeTest) where

import System.Process
import System.Exit
import Data.Time
import System.Directory
import Text.PrettyPrint
import Control.Monad.Error
import qualified Control.Exception as CE
import IO
import System.FilePath
import System.Info
import Data.List
import Control.Arrow

import Text.HTML.TagSoup

import qualified Data.ByteString as B
import qualified Data.Binary.Strict.BitGet as BG
import qualified Data.ByteString.Lazy as BL
import qualified Data.Binary.BitPut as BP

import Language.ASN1.PER.GenerateC
import GenerateModule
import ASNTYPE
import PER
import NewTestData -- FIXME: Temporary?
import NewPretty

skeletons = 
   case os of
      "mingw32" -> "c:\\Users\\Dom\\asn1c-0.9.21\\skeletons"
      _         -> "/usr/local/share/asn1c"

asn1c = "asn1c"
asn1cOptions = "-gen-PER -S"
-- asn1cOptions = "-gen-PER -fnative-types -S"

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
            fail (e ++ ": " ++ show n)

writeASN1AndC asn1File cFile t v =
   do writeFile asn1File (render (prettyModule t))
      c <- generateC t v
      writeFile cFile (render c)

writeASN1AndCRead asn1File cFile t v =
   do writeFile asn1File (render (prettyModule t))
      c <- generateCRead t v
      writeFile cFile (render c)

test genFile ty val =
   do d <- getCurrentDirectory
      t <- getCurrentTime
      let u = "asn1c." ++ show (utctDay t) ++ "." ++ show (utctDayTime t)
      createDirectory u
      setCurrentDirectory u
      CE.catch (do c <- generateC ty val
                   writeASN1AndC (genFile <.> "asn1") (genFile <.> "c") ty val
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
               (\e -> hPutStrLn stderr ("Problem with generating / compiling\n" ++ show (e :: CE.IOException)))
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
      name = referenceTypeName ty
      referenceTypeName (ReferencedType r _) = ref r
test _ _ _  = error "Can only test type assignments"
    
readGen perFile t =
   do h <- openFile perFile ReadMode
      b <- B.hGetContents h
      let d = BG.runBitGet b (runErrorT (fromPER t))
      case d of
         Left s  -> putStrLn ("BitGet error: " ++ show s)
         Right x -> case x of
                       Left e  -> putStrLn ("ASN.1 decoding error: " ++ show e)
                       Right y -> putStrLn (render (prettyTypeVal t y))

{-
example = runErrorT (fromPER rt3)
example1 = 
   case perEncode rt3 [] v3 of
      Left errorMessage -> 
         error errorMessage
      Right x ->
         BP.runBitPut x
-}

main = encodeTest "urk" rt1 (Val 7)

encodeTest genFile ty val = do
   CE.bracketOnError
      getCurrentDirectory
      (\currDir -> setCurrentDirectory currDir) 
      (\currDir -> do t <- getCurrentTime
                      let u = "asn1c." ++ show (utctDay t) ++ "." ++ show (utctDayTime t)
                      createDirectory u
                      setCurrentDirectory u
                      do writeASN1AndCRead (genFile <.> "asn1") (genFile <.> "c") ty val
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
                              (linker ++ " " ++ linkerOut genFile ++ " " ++ ("*" <.> objectSuffix), "Failure linking")
                            ]
                         B.writeFile (genFile <.> "per") (f ty val)
                         (code, out, err) <- readProcessWithExitCode (executable genFile) [genFile <.> "per"] ""
                         putStrLn (show code)
                         putStrLn out
                         putStrLn err
                         let x = parseTags out
                         putStrLn (show x)
                         let y = fromTagText (x!!1)
                             z = if ':' `elem` y
                                    then "0x" ++ (concat $ g $ y)
                                    else  y
                         putStrLn (show ((read z) :: Integer))
{-
                         runCommands [
                              ((executable genFile) ++ " " ++ (genFile <.> "per"), "Failure executing")
                            ]
-}
                         setCurrentDirectory currDir
                         return ((read z) :: Integer)
      )
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
      name = referenceTypeName ty
      referenceTypeName (ReferencedType r _) = ref r
      f t x =
         case possibleError of
            Left e -> error (show e)
            Right y -> B.pack . BL.unpack . BP.runBitPut . mapM_ (BP.putNBits 1) $ encoding
         where (possibleError, encoding) = extractValue (encode t [] x) 

f [] = Nothing
f xs = Just (second (drop 1) . break (== ':') $ xs)

g = unfoldr f

h [] = Nothing
h xs = Just . second (drop 1) . break (== ':') $ xs