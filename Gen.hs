-- FIXME: NewPretty and NewTestData should really be Pretty and
-- TestData.

import NewPretty
import NewTestData
import ASNTYPE
import Text.PrettyPrint

-- FIXME: For the time being we only allow one defintion in a module.
-- We probably used existential types in QuickTest. We could either
-- do this e.g. with a class that has a pretty function or maybe by
-- anoter tupling function / combinator like (:*:).
prettyModule :: ASNType a -> Doc
prettyModule xs =
   text "FooBar {1 2 3 4 5 6} DEFINITIONS ::="
   $$
   nest 2 (text "BEGIN")
   $$
   nest 4 (prettyModuleBody xs)
   $$
   nest 2 (text "END")

prettyModuleBody xs = 
   prettyType xs
