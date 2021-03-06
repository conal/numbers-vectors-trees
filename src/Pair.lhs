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
>   ( Bit, Pair(..), fstP, sndP
>   , pair, unpair, inPair
>   , first, second, firsts, seconds, (***), (&&&)
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

> fstP, sndP :: Pair a -> a
> fstP (a :# _) = a
> sndP (_ :# a) = a

Other instances
===============

The `Functor`, `Applicative`, `Monad`, and `Monoid` instances are all determined by requiring that the semantic function `untrie` be morphisms w.r.t those classes.

> instance Functor Pair where fmap f (a :# b) = (f a :# f b)

> instance Applicative Pair where
>   pure a = a :# a
>   (f :# g) <*> (x :# y) = (f x :# g y)

> instance Monad Pair where
>   return = pure
>   m >>= k = joinP (k <$> m)
> 
> joinP :: Pair (Pair a) -> Pair a
> joinP = (fstP.fstP) &&& (sndP.sndP)

Alternatively,

< joinP pp = (fstP.fstP) pp :# (sndP.sndP) pp
<
< joinP ((a :# _) :# (_ :# d)) = a :# d

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

Like `Arrow` `(&&&)` & `(***)`, but for `Pair`

> (***) :: (a -> b) -> (a -> b) -> (Pair a -> Pair b)
> (f *** g) (a :# b) = (f a :# g b)
>
> (&&&) :: (a -> b) -> (a -> b) -> (a -> Pair b)
> (f &&& g) a = f a :# g a
