 <!-- -*- markdown -*-

> {-# LANGUAGE GADTs, KindSignatures, ScopedTypeVariables #-}
> {-# OPTIONS_GHC -Wall #-}

|
Module      :  BNat
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

Simple module for bounded unary natural numbers.
See <http://conal.net/blog/posts/type-bounded-numbers/>.

> module BNat where

> import TNat

> import Nat

 -->

Bounded natural numbers
=======================

Natural number with matching value & type:
The type `BNat n` (unary bounded by $n$) that has values corresponding to $0, ..., n-1$.

> data BNat :: * -> * where
>   BZero ::           BNat (S n)
>   BSucc :: BNat n -> BNat (S n)

In other words, $0 < n+1$ and $m < n \Rightarrow m+1 < n+1$.

Note that `BNat` is defined almost exactly like `Nat`.
For comparison,

< data Nat :: * -> * where
<   Zero ::          Nat Z
<   Succ :: Nat n -> Nat (S n)

The only difference is that `Zero` has exactly the type `Nat Z`, whereas `BZero` has every type `BNat (S n)`.

We can interpret a `BNat` as an `Integer`:

> fromBNat :: BNat n -> Integer
> fromBNat BZero     = 0
> fromBNat (BSucc n) = (succ . fromBNat) n

I wrote the second clause strangely to emphasize the following lovely property:

< fromBNat . BSucc = succ . fromBNat

Note that the type of `fromBNat` could be generalized:

< fromBNat :: (Enum a, Num a) => BNat n -> a

To present `BNat` values, convert them to integers:

> instance Show (BNat n) where show = show . fromBNat

The reverse mapping would be handy also, i.e., for a number type $n$, given an integer $m$, generate a proof $m < n$, or fail if $m >= n$.

< toBNat :: Integer -> Maybe (BNat n)

Unlike `fromBNat`, `toBNat` doesn't have a structure to crawl over.
It must create just the right structure anyway.
What can we do?

One solution is to use a type class: with instances for `Z` and `S`:

< class HasBNat n where toBNat :: Integer -> Maybe (BNat n)
<
< instance HasBNat Z where toBNat _ = Nothing
< 
< instance HasBNat n => HasBNat (S n) where
<   toBNat m | m < 1     = Just BZero
<            | otherwise = fmap BSucc (toBNat (pred m))

Alternatively (my preference), eliminate the `HasBNat` class in favor of reusing `IsNat`:

> toBNat :: forall n. IsNat n => Integer -> Maybe (BNat n)
> toBNat = loop n where
>   n = nat :: Nat n
>   loop :: Nat n' -> Integer -> Maybe (BNat n')
>   loop Zero      _ = Nothing
>   loop (Succ _)  0 = Just BZero
>   loop (Succ n') m = fmap BSucc (loop n' (pred m))

For instance,

< *BNat> toBNat 3 :: Maybe (BNat EightT)
< Just 3
< *BNat> toBNat 10 :: Maybe (BNat EightT)
< Nothing

We can also get a description of all natural numbers *greater than* a given one:

< *BNat> :ty BSucc (BSucc BZero)
< BSucc (BSucc BZero) :: BNat (S (S (S n)))

In words, the natural numbers greater than two are exactly those of the form $3 + n$, for natural numbers $n$.

Other instances
---------------

Equality and ordering are easily defined, all based on simple properties of numbers:

> instance Eq (BNat n) where
>   BZero   == BZero    = True
>   BSucc m == BSucc m' = m == m'
>   _       == _        = False

> instance Ord (BNat n) where
>   BZero   `compare` BZero    = EQ
>   BSucc m `compare` BSucc m' = m `compare` m'
>   BZero   `compare` BSucc _  = LT
>   BSucc _ `compare` BZero    = GT

