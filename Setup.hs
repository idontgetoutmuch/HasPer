module Main where

import System.Info
import Distribution.Simple
import Distribution.Simple.Program
import Distribution.Simple.Setup
import Distribution.PackageDescription
import Distribution.Simple.LocalBuildInfo
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
   }

perPostConf :: Args -> ConfigFlags -> PackageDescription  -> LocalBuildInfo -> IO ()
perPostConf a cfs pd lbi =
   do let v      = fromFlagOrDefault normal (configVerbosity cfs)
          mPdf   = lookupProgram (simpleProgram "pdflatex") (withPrograms lbi)
          mAsn1c = lookupProgram (simpleProgram "asn1c") (withPrograms lbi)
          mC     = lookupProgram (simpleProgram cCompilerName) (withPrograms lbi)
      case mPdf of
         Nothing -> 
            warn v "Full documentation cannot be built without pdflatex" >> return ()
         Just _ ->
            return ()
      case mAsn1c of
         Nothing -> 
            warn v "Full inter-operability testing cannot be performed without asn1c" >> return ()
         Just _ ->
            return ()
      case mC of
         Nothing -> 
            warn v ("Full inter-operability testing cannot be performed without " ++ cCompilerName) >> return ()
         Just cp -> do
            info v (show cp)
            return ()
       