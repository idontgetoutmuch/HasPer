\documentclass{article}
%include polycode.fmt

\newcommand{\bottom}{\perp}

\begin{document}

\section{Introduction}

Testing encoding for UNALIGNED PER

\begin{code}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -XFlexibleContexts #-}

module TestCTR where

import CTRestruct
import Text.PrettyPrint
import NewPretty
import qualified Data.ByteString as B
import qualified Data.Binary.Strict.BitGet as BG
import qualified Data.Binary.Strict.BitPut as BP
import Control.Monad.Error

import qualified LatticeMod as L

sc1 = UNION (UC (IC (ATOM (E (V (R (245,249)))))) (ATOM (E (V (R (251,255))))))
sc2 = UNION (IC (INTER (ATOM (E (V (R (270,273))))) (E (V (R (271,276))))))

con1 = RE (UNION (IC (ATOM (E (V (R (250,253)))))))
con2 = RE (UNION (IC (ATOM (E (V (R (245,253)))))))
con3 = RE sc1
con4 = EXT sc1
con5 = EXTWITH sc1 sc2

t1 = ConsT (BT INTEGER) con1
t2 = ConsT t1 con2
t3 = ConsT (ConsT (BT INTEGER) con2) con1
t4 = ConsT (BT INTEGER) con3
t5 = ConsT (BT INTEGER) con4
t6 = ConsT (BT INTEGER) con5
t7 = ConsT (ConsT (BT INTEGER) con5) con1

ec1 = applyIntCons (Left (Just (minBound,maxBound))) [con1]

test1 = encode t1 252 []
test2 = encode t2 250 []
test3 = encode t3 250 []
test4 = encode t4 247 []
test5 = encode t5 247 []
test6 = encode t6 247 []
test7 = encode t6 272 []
test8 = encode t6 274 []
test9 = encode t7 251 []
test10 = encode t7 271 []
\end{code}

Examples from 13.6.1 of Dubuisson:

\begin{code}
dash  = ATOM (E (S (SV (PrintableString "-"))))
dot   = ATOM (E (S (SV (PrintableString "."))))
blank = ATOM (E (S (SV (PrintableString " "))))

morseChars = RE (UNION (UC (UC (IC dash) dot) blank))

morseAlphabet = ConsT (BT PRINTABLESTRING) morseChars

morse = ConsT (BT PRINTABLESTRING ) (RE (UNION (IC (ATOM ((E (P (FR morseChars))))))))

-- Note that the outer monad is BitGet and the inner monad is the Error

thereAndBack x = flip (BG.runBitGet . BP.runBitPut . bitPutify . encodeUInt ) (runErrorT decodeUInt) x

mySc1 = UNION (UC (IC (ATOM (E (V (R (245,249)))))) (ATOM (E (V (R (251,255))))))
mySc2 = UNION (IC (INTER (ATOM (E (V (R (270,273))))) (E (V (R (271,276))))))

myCon1 = RE (UNION (IC (ATOM (E (V (R (250,253)))))))
myCon2 = RE (UNION (IC (ATOM (E (V (R (245,253)))))))
myCon3 = RE mySc1
myCon4 = EXT mySc1
myCon5 = EXTWITH mySc1 mySc2

mt1 = ConsT (BT MYINTEGER) myCon1
mt2 = ConsT mt1 myCon2
mt3 = ConsT (ConsT (BT MYINTEGER) myCon2) myCon1
mt4 = ConsT (BT MYINTEGER) myCon3
mt5 = ConsT (BT MYINTEGER) myCon4
mt6 = ConsT (BT MYINTEGER) myCon5
mt7 = ConsT (ConsT (BT MYINTEGER) myCon5) myCon1

myTest t x =
   case lEncode t x [] of
      Left s  -> s
      Right m -> show (B.unpack (BP.runBitPut m))

dansTest t x =
   case encode t x [] of
      Right s -> s
      Left x -> show x

type Foo a = ErrorT String BG.BitGet a

foo :: (MonadError String m, L.Lattice (m L.MyLatConstraint)) => ASNType a -> [ElementSetSpecs a] -> m (ErrorT String BG.BitGet a)
foo x ss = decode2 x ss

bar = case foo mt1 [] of Left s -> undefined; Right x -> runErrorT x    

baz = case decode2 mt1 [] of Left s -> undefined; Right x -> runErrorT x    

\end{code}

\end{document}
