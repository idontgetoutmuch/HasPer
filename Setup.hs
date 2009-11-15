module Main where

import System.Info
import System.Process

import Distribution.Simple
import Distribution.Simple.Program
import Distribution.Simple.Setup
import Distribution.PackageDescription
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Configure
import Distribution.Verbosity
import Distribution.Simple.Utils

main :: IO ()
main = do 
  defaultMainWithHooks perHooks

cCompilerName =
   case os of
      "mingw32" -> "lcc"
      _         -> "gcc"

perHooks =
   simpleUserHooks {
         hookedPrograms = [
              simpleProgram "pdflatex"
            , simpleProgram "asn1c"
            , simpleProgram cCompilerName
          ]
      , postConf = perPostConf
      , runTests = myTests
   }

perPostConf :: Args -> ConfigFlags -> PackageDescription  -> LocalBuildInfo -> IO ()
perPostConf a cfs pd lbi =
   do let v       = fromFlagOrDefault normal (configVerbosity cfs)
          pdfSP   = simpleProgram "pdflatex"
          mPdf    = lookupProgram pdfSP (withPrograms lbi)
          asn1cSP = simpleProgram "asn1c"
          mAsn1c  = lookupProgram  asn1cSP (withPrograms lbi)
          cSP     = simpleProgram cCompilerName
          mC      = lookupProgram cSP (withPrograms lbi)
      case mPdf of
         Nothing -> 
            warn v "Full documentation cannot be built without pdflatex" >> return ()
         Just _ -> do
  --          reportProgram v pdfSP mPdf
            return ()
      case mAsn1c of
         Nothing -> 
            warn v "Full inter-operability testing cannot be performed without asn1c" >> return ()
         Just _ -> do
 --           reportProgram v asn1cSP mAsn1c
            return ()
      case mC of
         Nothing -> 
            warn v ("Full inter-operability testing cannot be performed without " ++ cCompilerName) >> return ()
         Just cp -> do
 --           reportProgram v cSP mC
            return ()

myTests _ _ _ _ = do
   (code, out, err) <- readProcessWithExitCode "runghc" ["-idist/build/autogen/", "PERTest.hs"] ""
   putStrLn (show code)
   putStrLn ("Stdout: " ++ out)
   putStrLn ("Stderr: " ++ err)
