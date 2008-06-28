\documentclass{article}
%include polycode.fmt

\newcommand{\bottom}{\perp}

\begin{document}

\section{Introduction}

Testing encoding for UNALIGNED PER

\begin{code}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module TestCTR where

import CTRestruct
import Text.PrettyPrint
import NewPretty

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

thereAndBack = flip (BG.runBitGet . BP.runBitPut . bitPutify . encodeUInt) decodeUInt (-1)

\end{code}

\end{document}
