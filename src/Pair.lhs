 <!-- -*- markdown -*-

> {-# LANGUAGE TypeFamilies #-}

> {-# OPTIONS_GHC -Wall #-}
> {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

|
Module      :  Pair
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

Simple 'Bit' type & 'Pair' functor

> module Pair where

> import Data.Monoid (Monoid(..))
> import Control.Applicative (Applicative(..),(<$>),liftA2)
> import Data.Foldable (Foldable(..),foldl',foldr',and,toList)
> import Data.Traversable

> import FunctorCombo.StrictMemo (HasTrie(..))

 -->

 <!-- references -->
 <!-- -->


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
>   pure a = (a :# a)
>   (f :# g) <*> (x :# y) = (f x :# g y)

> instance Foldable Pair where
>   foldMap h (a :# b) = h a `mappend` h b
>   foldr h e (a :# b) = a `h` (b `h` (b `h` e))
>   -- Could drop either foldMap or foldr def

> instance Traversable Pair where
>   sequenceA (fa :# fb) = (:#) <$> fa <*> fb

