\documentclass{article}
%include polycode.fmt
\begin{document}

\section{Introduction}

\begin{code}

module Main(main) where

import System.Process
import System.Exit
import Asn1cTest
import Data.Time
import System.Directory
import Text.PrettyPrint
import Pretty
import ConstrainedType
import qualified Data.ByteString.Lazy as B
import Control.Monad.State
import Control.Monad.Error
import Test (type9, val9, val91)
import IO

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
      writeFile "generated.asn1" (render (genASN1 type9))
      writeFile "generated.c" (render (genC type9 val91))
      runTest "generated.asn1"
      r <- readGen type7
      putStrLn r
      setCurrentDirectory d

readGen (NamedType _ _ t) =
   do h <- openFile "generated.per" ReadMode
      b <- B.hGetContents h
      let d = runState (runErrorT (mFromPer t)) (b,0)
      case d of
         (Left e,s)  -> return (e ++ " " ++ show s)
         (Right n,s) -> return (show n ++ " " ++ show s)

\end{code}

\end{document}

