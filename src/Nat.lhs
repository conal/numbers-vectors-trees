 <!-- -*- markdown -*-

> {-# LANGUAGE GADTs, KindSignatures, EmptyDataDecls #-}
> {-# OPTIONS_GHC -Wall #-}

|
Module      :  Nat
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

Simple module for typed natural numbers

> module Nat where

> import TNat

 -->

Typed natural numbers
=====================

Natural number with matching value & type:

> data Nat :: * -> * where
>   Zero :: Nat Z
>   Succ :: IsNat n => Nat n -> Nat (S n)
>
> instance Show (Nat n) where show = show . natToZ

Interpret a `Nat` as an `Integer`

> natToZ :: Nat n -> Integer
> natToZ Zero     = 0
> natToZ (Succ n) = (succ . natToZ) n

I wrote the second clause strangely to emphasize the following lovely property:

< natToZ . Succ = succ . natToZ

We'll sometimes want to to synthesize a natural number from a type:

> class IsNat n where nat :: Nat n
> 
> instance            IsNat Z     where nat = Zero
> instance IsNat n => IsNat (S n) where nat = Succ nat


Here are some handy names for small natural numbers:

> zero :: Nat ZeroT
> zero = Zero
>
> one :: Nat OneT
> one = Succ zero
>
> two :: Nat TwoT
> two = Succ one
>
> three :: Nat ThreeT
> three = Succ two
>
> four :: Nat FourT
> four = Succ three

