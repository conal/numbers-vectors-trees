{-# LANGUAGE CPP, TypeOperators #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}

-- Num instances for left-folding versions of `Vec n` and `f :^ n`
-- Perform numeric operations elementwise.

module LeftNum where

import Control.Applicative (Applicative(..),liftA2)
import Data.Foldable (Foldable)

import Nat
import Left

-- Generate bogus (error-producing) Enum
#define INSTANCE_Enum

#define CONSTRAINTS IsNat n,
#define APPLICATIVE (Vec n)
#include "ApplicativeNumeric-inc.hs"

#undef CONSTRAINTS
#undef APPLICATIVE

-- Generate bogus (error-producing) Show. TODO: real ones.
#define INSTANCE_Show

#define CONSTRAINTS IsNat n, Applicative f, Foldable f,
#define APPLICATIVE (f :^ n)
#include "ApplicativeNumeric-inc.hs"
