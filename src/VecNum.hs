{-# LANGUAGE CPP, TypeOperators, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}

----------------------------------------------------------------------
-- |
-- Module      :  VecNum
-- Copyright   :  (c) Conal Elliott 2011
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Num instances for @Vec n@ and @f :^ n@.
-- Perform numeric operations elementwise.
-- 
----------------------------------------------------------------------


module VecNum where

import Control.Applicative (Applicative(..),liftA2)
import Data.Foldable (Foldable)

import Nat
import Vec
import ShowF
import ComposeFunctor

-- Generate bogus (error-producing) Enum
#define INSTANCE_Enum

#define CONSTRAINTS IsNat n,
#define APPLICATIVE (Vec n)
#include "ApplicativeNumeric-inc.hs"


#undef CONSTRAINTS
#undef APPLICATIVE

-- Generate bogus (error-producing) Show. TODO: real ones.
-- #define INSTANCE_Show

#define CONSTRAINTS IsNat n, Applicative f, Foldable f, ShowF f,
#define APPLICATIVE (f :^ n)
#include "ApplicativeNumeric-inc.hs"
