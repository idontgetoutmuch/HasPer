import Rename
import Relabel
import Pretty
import TestData
import Asn1cTest hiding (type12, type12', val12a, val12b)
import ConstrainedType
import Text.PrettyPrint
import Control.Arrow hiding ((<+>))

prettyModuleValsBody xs ys =
   vcat (map (uncurry ($$)) (prefixPairs (map valueTypeName prefixes) tsvs))
   where
      tsvs = map (\(x,y) -> (prettyType x, prettyTypeVal x y)) (zipWith (,) xs ys)
      typeNames = (text "Type" <>) . text 
      valueNames = (text "value" <>) . text 
      prefixes = map ((typeNames &&& valueNames) . show) [1..]
      valueTypeName (t,v) = (t <+> text "::=", v <+> t <+> text "::=")
      prefixPairs ps xs = zipWith (\(p1,p2) (t,v) -> ((p1 <+> t), (p2 <+> v))) ps tsvs

t = prettyModuleValsBody [type12] [val12a]

u = genC type12' val12a

prettyModuleWithVals xs ys =
   text "FooBar {1 2 3 4 5 6} DEFINITIONS ::="
   $$
   nest 2 (text "BEGIN")
   $$
   nest 4 (prettyModuleValsBody xs ys)
   $$
   nest 2 (text "END")

genAss :: [ASNType a] -> [ASNType a]
genAss ts = zipWith ($) (map (\t -> \n -> TYPEASS ("Type" ++ (show n)) Nothing t) ts) [1..]

