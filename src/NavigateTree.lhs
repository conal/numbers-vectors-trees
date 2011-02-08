 <!-- -*- markdown -*-

> {-# LANGUAGE GADTs, TypeOperators #-}

> {-# OPTIONS_GHC -Wall #-}
> {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
> {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-} -- temporary, pending ghc/ghci fix

|
Module      :  NavigateTree
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

Navigating in trees of trees

> module NavigateTree where

> import Nat

> import qualified ComposeFunctor as R
> import qualified Left           as L

 -->

 <!-- references -->
 <!-- -->

A depth-$(n+m)$ tree of values can also be thought of as a depth-$n$ tree of depth-$m$ trees.
It will be easiest to combine trees of opposite orientation, with right-folded outside and left-folded inside.

> up   :: (Functor f, IsNat m) => (f L.:^ S n) ((f R.:^ m) a) -> (f L.:^ n) ((f R.:^ (S m)) a)
> up   = fmap R.SuccC . L.unSuccC
>
> down :: (Functor f, IsNat n) => (f L.:^ n) ((f R.:^ (S m)) a) -> (f L.:^ S n) ((f R.:^ m) a)
> down = L.SuccC . fmap R.unSuccC

As desired, `up` and `down` are inverses.
Proofs:

<   up . down
< == fmap R.SuccC . L.unSuccC . L.SuccC . fmap R.unSuccC
< == fmap R.SuccC . fmap R.unSuccC
< == fmap (R.SuccC . R.unSuccC)
< == fmap id
< == id

<   down . up
< == L.SuccC . fmap R.unSuccC . fmap R.SuccC . L.unSuccC
< == L.SuccC . fmap (R.unSuccC . R.SuccC) . L.unSuccC
< == L.SuccC . fmap id . L.unSuccC
< == L.SuccC . id . L.unSuccC
< == L.SuccC . L.unSuccC
< == id

I don't think it works out to reverse containment of trees (right-folded outside and left-folded inside).

These navigation operations (`up` and `down`) remind me of zippers.
