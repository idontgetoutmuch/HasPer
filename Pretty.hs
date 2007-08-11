{-# OPTIONS -fglasgow-exts -Wall -fno-warn-missing-signatures #-}


-----------------------------------------------------------------------------
-- |
-- Module      :  Pretty
-- Copyright   :  (c) Dominic Steinitz 2007
-- License     :  BSD3
--
-- Maintainer  :  dominic.steinitz@blueyonder.co.uk
-- Stability   :  experimental
-- Portability :  portable
--
-- Utilities for prettyprinting ConstrainedTypes
--
-----------------------------------------------------------------------------

module Pretty(
   prettyType
   )  where

import Text.PrettyPrint

import Attempt5
