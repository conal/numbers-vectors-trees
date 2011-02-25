---
title: Composable parallel scanning
tags: scan, functor
url: http://conal.net/blog/posts/Composable-parallel-scanning/
...

 <!--[ 

> {-# LANGUAGE TypeOperators #-}

> {-# OPTIONS_GHC -Wall #-}

< {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

|
Module      :  ParallelScan
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

A class for parallel scans, with instances for functor combinators

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
In [*Deriving tree scans*], I simply removed the `mempty` element from the scan.
In this post, I'll instead change the interface to produce an output of exactly the same shape, plus one extra element.
The extra element will equal a `fold` over the complete input.
If you recall, we had to search for that complete fold in an input subtree in order to adjust the other subtree.
(See `headT` and `lastT` and their generalizations in [*Deriving tree scans*].)
Separating out this value eliminates the search.

Define a class with methods for prefix and suffix scan:

> class ScanL f where
>   scanL, scanR :: Monoid m => f m -> (m, f m)

Prefix scans (`scanL`) accumulate moving left-to-right, while suffix scans (`scanR`) accumulate moving right-to-left.

A simple example: pairs
-----------------------

To get a first sense of generalized scans, let's use see how to scan over a pair functor.

< data Pair a = a :# a deriving (Eq,Ord,Show)

With GHC's `DeriveFunctor` option, we could also derive a `Functor` instance, but for clarity, define it explicitly:

< instance Functor Pair where
<   fmap f (a :# b) = (f a :# f b)

The scans:

< instance ScanL Pair where
<   scanL (a :# b) = (a `mappend` b, (mempty :# a))
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

< newtype Id        a = Id a
< data    (f :+: g) a = InL (f a) | InR (g a)
< data    (f :*: g) a = f a :*: g a
< newtype (g  :. f) a = O (g (f a))

 ]-->

Constant
--------

The identity functor is easiest.

< newtype Const x a  = Const x

There are no values to accumulate, so the final result (fold) is `mempty`.

> instance ScanL (Const x) where
>   scanL (Const x) = (mempty, Const x)
>   scanR           = scanL

Identity
--------

The identity functor is nearly as easy.

> instance ScanL Id where
>   scanL (Id m) = (m, Id mempty)
>   scanR        = scanL

Sum
---

Scanning in a sum is just scanning in a summand:

> instance (ScanL f, ScanL g) => ScanL (f :+: g) where
>   scanL (InL fa) = second InL (scanL fa)
>   scanL (InR ga) = second InR (scanL ga)
> 
>   scanR (InL fa) = second InL (scanR fa)
>   scanR (InR ga) = second InR (scanR ga)

Product
-------

Product scannning is a little trickier.
Scan each of the two parts separately to get, and then combine the final (`fold`) part of one result with each of the non-final elements of the other.

< instance (ScanL f, ScanL g, Functor g) => ScanL (f :*: g) where
<   scanL (fa :*: ga) = (af `mappend` ag, fa' :*: ((af `mappend`) <$> ga'))
<    where (af,fa') = scanL fa
<          (ag,ga') = scanL ga
<
<   scanR (fa :*: ga) = (af `mappend` ag, ((`mappend` ag) <$> fa') :*: ga')
<    where (af,fa') = scanR fa
<          (ag,ga') = scanR ga

Here's a variant that factors out the `mappend`-adjustments.

> instance (ScanL f, ScanL g, Functor f, Functor g) => ScanL (f :*: g) where
>   scanL (fa :*: ga) = (adjust ag, fa' :*: (adjust <$> ga'))
>    where (af,fa') = scanL fa
>          (ag,ga') = scanL ga
>          adjust   = (af `mappend`)
>
>   scanR (fa :*: ga) = (adjust af, (adjust <$> fa') :*: ga')
>    where (af,fa') = scanR fa
>          (ag,ga') = scanR ga
>          adjust   = (`mappend` ag)


Composition
-----------

Finally, composition is the trickiest.

The target signatures:

<   scanL, scanR :: Monoid m => (g :. f) m -> (m, (g :. f) m)

To find the prefix and suffix scan definitions, fiddle with types beginning at the domain type for `scanL` or `scanR` and arriving at the range type.

Some helpers:

> zip :: Applicative g => (g a, g b) -> g (a,b)
> zip = uncurry (liftA2 (,))
> 
> unzip :: Functor g => g (a,b) -> (g a, g b)
> unzip = fmap fst &&& fmap snd

> assocR :: ((a,b),c) -> (a,(b,c))
> assocR    ((a,b),c) =  (a,(b,c))

> adjustL :: (Functor f, Monoid m) => (m, f m) -> f m
> adjustL (m, ms) = (m `mappend`) <$> ms
>
> adjustR :: (Functor f, Monoid m) => (m, f m) -> f m
> adjustR (m, ms) = (`mappend` m) <$> ms

First `scanL`:

< gofm                     :: (g :. f) m
< unO                   '' :: g (f m)
< fmap scanL            '' :: g (m, f m)
< unzip                 '' :: (g m, g (f m))
< first scanL           '' :: ((m, g m), g (f m))
< assocL                '' :: (m, (g m, g (f m)))
< secon zip             '' :: (m, g (m, f m))
< second (fmap adjustL) '' :: (m, g (f m))
< second O              '' :: (m, (g :. f) m)

Then `scanR`:

< gofm                     :: (g :. f) m
< unO                   '' :: g (f m)
< fmap scanR            '' :: g (m, f m)
< unzip                 '' :: (g m, g (f m))
< first scanR           '' :: ((m, g m), g (f m))
< assocR                '' :: (m, (g m, g (f m)))
< second zip            '' :: (m, (g (m, f m)))
< second (fmap adjustR) '' :: (m, (g (f m)))
< second O              '' :: (m, ((g :. f) m))

Putting together the pieces and simplifying just a bit leads to the method definitions:

> instance (ScanL g, ScanL f, Functor f, Applicative g) => ScanL (g :. f) where
>   scanL = second (O . fmap adjustL . zip)
>         . assocR
>         . first scanL
>         . unzip
>         . fmap scanL
>         . unO
>
>   scanR = second (O . fmap adjustR . zip)
>         . assocR
>         . first scanR
>         . unzip
>         . fmap scanR
>         . unO
