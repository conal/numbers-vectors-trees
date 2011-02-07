 <!-- -*- markdown -*-

> {-# LANGUAGE TypeFamilies #-}
> {-# OPTIONS_GHC -Wall #-}

|
Module      :  Pair
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

Simple 'Bit' type & 'Pair' functor

> module Pair where

> import Data.Monoid (Monoid(..))
> import Control.Applicative (Applicative(..),(<$>))
> import Data.Foldable (Foldable(..))
> import Data.Traversable

> import FunctorCombo.StrictMemo (HasTrie(..))

 -->

Bits and pairs
==============

> data Bit = Zero | One deriving (Eq,Ord,Show)

> data Pair a = a :# a

> instance HasTrie Bit where
>   type Trie Bit = Pair
>   trie f = f Zero :# f One
>   untrie (z :# _) Zero = z
>   untrie (_ :# o) One  = o
>   enumerate (z :# o) = [(Zero,z),(One,o)]

Other instances
===============

> instance Functor Pair where fmap f (a :# b) = (f a :# f b)

> instance Applicative Pair where
>   pure a = a :# a
>   (f :# g) <*> (x :# y) = (f x :# g y)

> instance Foldable Pair where
>   fold (a :# b) = a `mappend` b

> instance Traversable Pair where
>   sequenceA (fa :# fb) = (:#) <$> fa <*> fb

