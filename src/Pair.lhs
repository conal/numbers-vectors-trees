 <!-- -*- markdown -*-

> {-# LANGUAGE TypeFamilies, TypeOperators #-}
> {-# OPTIONS_GHC -Wall #-}

|
Module      :  Pair
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

Simple 'Bit' type & 'Pair' functor

> module Pair
>   ( Bit, Pair(..)
>   , pair, unpair, inPair
>   , first, second, firsts, seconds, (***)
>   )
>     where

> import Data.Monoid (Monoid(..))
> import Control.Applicative (Applicative(..),(<$>))
> import Data.Foldable (Foldable(..))
> import Data.Traversable
> import qualified Control.Arrow as Ar (first,second)

> import FunctorCombo.StrictMemo (HasTrie(..))

> import SEC
> import Scan (Scan(..))


 -->

Bits and pairs
==============

> data Bit = Off | On deriving (Eq,Ord,Show)
>
> infixl 0 :#
> data Pair a = a :# a deriving (Eq,Ord,Show)

> instance HasTrie Bit where
>   type Trie Bit = Pair
>   trie f = f Off :# f On
>   untrie (z :# _) Off = z
>   untrie (_ :# o) On  = o
>   enumerate (z :# o) = [(Off,z),(On,o)]

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

> instance Scan Pair where
>   scanL (a :# b) = ((mempty :# a), a `mappend` b)
>   scanR (a :# b) = (a `mappend` b, (b :# mempty))

I might like to use use `Bool` instead of `Bit`, and replace the current `HasTrie Bool` instance.

> pair :: (a,a) -> Pair a
> pair (a,b) = (a :# b)
>
> unpair :: Pair a -> (a,a)
> unpair (a :# b) = (a , b)

> inPair :: (a,a) :-+> Pair a
> inPair = unpair ~> pair

Like the `Arrow` `first` and `second` but for `Pair`:

> first, second :: a :-+> Pair a
> first  = inPair . Ar.first
> second = inPair . Ar.second

Also handy:

> firsts,seconds :: (Traversable f, Applicative f) => f b :-+> f (Pair b)
> firsts  = inInvert . first
> seconds = inInvert . second

Like `Arrow` `(***)`, but for `Pair`

> (***) :: Unop a -> Unop a -> Unop (Pair a)
> (f *** g) (a :# b) = (f a :# g b)

