 <!-- -*- markdown -*-

> {-# LANGUAGE GADTs, KindSignatures, EmptyDataDecls #-}
> {-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances #-}
> {-# OPTIONS_GHC -Wall #-}

|
Module      :  TNat
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

Type-level numbers

> module TNat where

 -->

Type-level numbers
==================

Zero and successor:

> data Z
> data S n

Some handy aliases:

> type ZeroT  = Z
> type OneT   = S ZeroT
> type TwoT   = S OneT
> type ThreeT = S TwoT
> type FourT  = S ThreeT
> type FiveT  = S FourT
> type SixT   = S FiveT
> type SevenT = S SixT
> type EightT = S SevenT
> type NineT  = S EightT
> type TenT   = S NineT

Arithmetic
----------

> infixl 6 :+:
> infixl 7 :*:

> type family n :+: m
> type instance Z   :+: m = m
> type instance S n :+: m = S (n :+: m)

> type family n :*: m
> type instance Z   :*: m = Z
> type instance S n :*: m = n :+: (n :*: m)

The last instance requires `UndecidableInstances`.
