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
> import Control.Applicative (Applicative(..),(<$>),liftA2)
> import Data.Foldable (Foldable(..))
> import Data.Traversable
> import qualified Control.Arrow as Ar (first,second)

> import FunctorCombo.StrictMemo (HasTrie(..))

> import SEC


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

< instance Monoid m => Monoid (Pair m) where 
<   mempty = mempty :# mempty
<   (a :# b) `mappend` (c :# d) = (a `mappend` c) :# (b `mappend` d)

Alternatively, use the following standard instance, which works for applicative functors.

> instance Monoid m => Monoid (Pair m) where
>   mempty  = pure mempty
>   mappend = liftA2 mappend


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
> firsts  = inDist . first
> seconds = inDist . second

Like `Arrow` `(***)`, but for `Pair`

> (***) :: Unop a -> Unop a -> Unop (Pair a)
> (f *** g) (a :# b) = (f a :# g b)
