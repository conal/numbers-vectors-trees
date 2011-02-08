 <!-- -*- markdown -*-

< {-# LANGUAGE #-}

> {-# OPTIONS_GHC -Wall #-}

> {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

|
Module      :  SEC
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

Semantic editor combinators

> module SEC ((~>), Unop, (:-+>), first, second, result) where

> import Control.Arrow (first,second)

 -->

 <!-- references -->
 <!-- -->


Some semantic editor combinators
================================

Handy:

> infixr 1 ~>
> (~>) :: (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
> (f ~> h) g = h . g . f

More generally,

< (~>) :: Category (-->) =>
<         (a' --> a) -> (b --> b') -> ((a --> b) -> (a' --> b'))

Like `second` but on function types:

> result :: (b -> b') -> ((a -> b) -> (a -> b'))
> result = (.)

Type-preserving editor:

> type Unop a = a -> a

A type-preserving [*Semantic editor combinator*]:

> type p :-+> q = Unop p -> Unop q



