---
title: Classes for scanning
tags: scan
url: http://conal.net/blog/posts/deriving-tree-scans/
...

 <!--[ -*- markdown -*-

> {-# LANGUAGE TypeOperators #-}

> {-# OPTIONS_GHC -Wall #-}

< {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

|
Module      :  Scan
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

A class for scans

> module Scan where

> import Prelude hiding (zip,unzip)

> import Data.Monoid (Monoid(..))
> import Control.Applicative (Applicative,liftA2,(<$>))
> import Control.Arrow ((&&&),first,second)

> import FunctorCombo.Functor

 ]-->

 <!-- references -->

[`scanl`]: http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-List.html#v:scanl
[`scanr`]: http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-List.html#v:scanr

[`inits`]: http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-List.html#v:inits
[`tails`]: http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-List.html#v:tails

[*Elegant memoization with higher-order types*]: http://conal.net/blog/posts/elegant-memoization-with-higher-order-types/ "blog post"

[*Deriving list scans*]: http://conal.net/blog/posts/deriving-list-scans/ "blog post"
[*Deriving tree scans*]: http://conal.net/blog/posts/deriving-tree-scans/ "blog post"

 <!-- teaser -->

The post [*Deriving list scans*] gave a simple specification of the list-scanning functions [`scanl`] and [`scanr`], and then transformed those specifications into the standard optimized implementations.
Next, the post [*Deriving tree scans*] adapted the specifications and derivations to a type of binary trees.
The resulting implementations are parallel-friendly, but not work-efficient, in that they perform $n \, \log \, n$ work vs linear work as in the best-known sequential algorithm.

Besides the work-inefficiency, I don't know how to extend the critical `initTs` and `tailTs` functions (analogs of `inits` and `tails` on lists) to depth-typed, perfectly balanced trees, of the sort I played with in [*A trie for length-typed vectors*] and [*From tries to trees*].
The difficulty I encounter is that the functions `initTs` and `tailTs` make unbalanced trees out of balanced ones, so I don't know how to adapt the specifications when types prevent the existence of unbalanced trees.

This new post explores an approach to generalized scanning via type classes.
After defining the classes and giving a simple example, I'll give a simple & general framework composed from functor combinators.

 <!--more-->


Generalizing list scans
=======================

The left and right scan functions on lists have an awkward feature.
The output list has one more element than the input list, corresponding to the fact that the number of prefixes ([`inits`]) of a list is one more than the number of elements, and similarly for suffixes ([`tails`]).

While it's easy to extend a list by adding one more element, it's not easy with other functors.
So I'll instead change the interface to produce an output of exactly the same shape, plus one extra element.
The extra element will equal a `fold` over the complete input.

Alternatively, we could remove the zero element from the scan, as in [*Deriving tree scans*].
As we go, I'll point out some advantages of each.

Define a single-method class for each of prefix and suffix scan:

> class ScanL f where
>   scanL :: Monoid m => f m -> (f m, m)
>
> class ScanR f where
>   scanR :: Monoid m => f m -> (m, f m)

Note the difference in the result types, to emphasize the intended meanings.
Prefix scans accumulate moving left-to-right, while suffix scans accumulate moving right-to-left.

A simple example: pairs
-----------------------

To get a first sense of generalized scans, let's use see how to scan over a pair functor.

< data Pair a = a :# a deriving (Eq,Ord,Show)

With GHC's `DeriveFunctor` option, we could also derive a `Functor` instance, but for clarity, define it explicitly:

< instance Functor Pair where
<   fmap f (a :# b) = (f a :# f b)

The scans:

< instance ScanL Pair where
<   scanL (a :# b) = ((mempty :# a), a `mappend` b)
<
< instance ScanR Pair where
<   scanR (a :# b) = (a `mappend` b, (b :# mempty))

As you can see, if we eliminated the `mempty` elements, we could shift to the left or right and forgo the extra result.

Naturally, there is also a `Fold` instance, and the scans produce the fold results as well sub-folds:

< instance Foldable Pair where
<   fold (a :# b) = a `mappend` b

The `Pair` functor also has unsurprising instances for `Applicative` and `Traversable`.<span></span>
 <div class=toggle>

< instance Applicative Pair where
<   pure a = a :# a
<   (f :# g) <*> (x :# y) = (f x :# g y)
<
< instance Traversable Pair where
<   sequenceA (fa :# fb) = (:#) <$> fa <*> fb

 </div>

We don't really have to figure out how to define scans for every functor separately.
We can instead look at how functors are are composed out of their essential building blocks.

Scans for functor combinators
=============================

To see how to scan over a broad range of functors, let's look at each of the functor combinators, e.g., as in [*Elegant memoization with higher-order types*].

 <!--[

< newtype Id a       = Id a
< data (f :+: g) a   = InL (f a) | InR (g a)
< data (f :*: g) a   = f a :*: g a
< newtype (g :. f) a = O (g (f a))

 ]-->

Constant
--------

The identity functor is easiest.

< newtype Const x a  = Const x

There are no values to accumulate, so the final result (fold) is `mempty`.

> instance ScanL (Const x) where
>   scanL (Const x) = (Const x, mempty)
>
> instance ScanR (Const x) where
>   scanR (Const x) = (mempty, Const x)

Identity
--------

The identity functor is nearly as easy.

> instance ScanL Id where
>   scanL (Id m) = (Id mempty, m)
>
> instance ScanR Id where
>   scanR (Id m) = (m, Id mempty)

Sum
---



> instance (ScanL f, ScanL g) => ScanL (f :+: g) where
>   scanL (InL fa) = first  InL (scanL fa)
>   scanL (InR ga) = first  InR (scanL ga)

> instance (ScanL f, ScanL g, Functor g) => ScanL (f :*: g) where
>   scanL (fa :*: ga) = (fa' :*: ((af `mappend`) <$> ga'), af `mappend` ag)
>    where (fa',af) = scanL fa
>          (ga',ag) = scanL ga

> instance (ScanL g, ScanL f, Functor f, Applicative g) => ScanL (g :. f) where
>   scanL = first (O . fmap adjustL . zip)
>         . assocL
>         . second scanL
>         . unzip
>         . fmap scanL
>         . unO

Helpers:

> unzip :: Functor g => g (a,b) -> (g a, g b)
> unzip = fmap fst &&& fmap snd
>
> zip :: Applicative g => (g a, g b) -> g (a,b)
> zip = uncurry (liftA2 (,))

> assocL :: (a,(b,c)) -> ((a,b),c)
> assocL    (a,(b,c)) =  ((a,b),c)

> adjustL :: (Functor f, Monoid m) => (f m, m) -> f m
> adjustL (ms,m) = (m `mappend`) <$> ms

Type-directed derivations:

< gofm                    :: (g :. f) m
< unO                  '' :: g (f m)
< fmap scanL           '' :: g (f m, m)
< unzip                '' :: (g (f m), g m)
< second scanL         '' :: (g (f m), (g m, m))
< assocL               '' :: ((g (f m), g m), m)
< first zip            '' :: (g (f m, m), m)
< first (fmap adjustL) '' :: (g (f m), m)
< first O              '' :: ((g :. f) m, m)


Right scans
-----------

>
> instance (ScanR f, ScanR g) => ScanR (f :+: g) where
>   scanR (InL fa) = second InL (scanR fa)
>   scanR (InR ga) = second InR (scanR ga)
>
> instance (ScanR f, ScanR g, Functor f) => ScanR (f :*: g) where
>   scanR (fa :*: ga) = (af `mappend` ag, ((`mappend` ag) <$> fa') :*: ga')
>    where (af,fa') = scanR fa
>          (ag,ga') = scanR ga
>
> instance (ScanR g, ScanR f, Functor f, Applicative g) => ScanR (g :. f) where
>   scanR = second (O . fmap adjustR . zip)
>         . assocR
>         . first scanR
>         . unzip
>         . fmap scanR
>         . unO

Helpers:

> assocR :: ((a,b),c) -> (a,(b,c))
> assocR    ((a,b),c) =  (a,(b,c))
>
> adjustR :: (Functor f, Monoid m) => (m, f m) -> f m
> adjustR (m,ms) = (`mappend` m) <$> ms

Type-directed derivation:

< gofm                     :: (g :. f) m
< unO                   '' :: g (f m)
< fmap scanR            '' :: g (m, f m)
< unzip                 '' :: (g m, g (f m))
< first scanR           '' :: ((m, g m), g (f m))
< assocR                '' :: (m, (g m, g (f m)))
< second zip            '' :: (m, (g (m, f m)))
< second (fmap adjustR) '' :: (m, (g (f m)))
< second O              '' :: (m, ((g :. f) m))

