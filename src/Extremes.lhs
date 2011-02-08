 <!-- -*- markdown -*-

> {-# LANGUAGE GADTs, TypeOperators, Rank2Types #-}

> {-# OPTIONS_GHC -Wall #-}

> {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

|
Module      :  Extremes
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

Experimenting with a piece of the scan derivation

> module Extremes where

< import Control.Applicative ((<*>))

> import SEC
> import Nat
> import Pair
> import ComposeFunctor

> import qualified Left as L

 -->

 <!-- references -->
 <!-- -->

> type T m = Pair :^ m

Transform just the left-most or just the right-most in a tree:

< leftmost, rightmost :: a :-+> T m a
< leftmost  h = inC h ((first  . rightmost) h)
< rightmost h = inC h ((second . rightmost) h)

Generalizing,

> extreme :: (forall a. a :-+> f a) -> (forall a . a :-+> (f :^ m) a)
> extreme inF h = inC h ((inF . extreme inF) h)

> leftmost, rightmost :: a :-+> T m a
> leftmost  = extreme first
> rightmost = extreme second

The quantification in the type of `extreme` is delicate.
It must include `a` and exclude `f`.
