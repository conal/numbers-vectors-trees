 <!-- -*- markdown -*-

> {-# LANGUAGE GADTs, TypeOperators #-}

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

Transform just the left-most or just the right-most in a tree:

> type T m = Pair :^ m

> leftmost, rightmost :: a :-+> T m a
> leftmost  h = inC h ((first  . rightmost) h)
> rightmost h = inC h ((second . rightmost) h)

The following equivalent form doesn't pass the type-checker:

< rightmost = inC <*> (second . rightmost)

The left-folded form is exactly the same but swapping `fmap` and `rightmost`:

< rightmost h = inC h ((rightmost . second) h)

It would be easy generalize and so get first as well.
