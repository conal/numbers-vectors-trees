 <!-- -*- markdown -*-

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

 -->

 <!-- references -->

[`inits`]: http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-List.html#v:inits
[`tails`]: http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-List.html#v:tails


 <!-- -->

Generalizing list scans
=======================

The left and right scan functions on lists have an awkward feature.
The output list has one more element than the input list, corresponding to the fact that the number of prefixes ([`inits`]) of a list is one more than the number of elements, and similarly for suffixes ([`tails`]).

While it's easy to extend a list by adding one more element, it's not easy with other functors.
So I'll instead change the interface to produce an output of exactly the same shape, plus one extra element.
The extra element will equal a `fold` over the complete input.

Alternatively, we could remove the zero element from the scan.
As we go, I'll point out advantages of each.

Left scans
==========

Define a class for functors that support left scans.

> class ScanL f where
>   scanL :: Monoid m => f m -> (f m, m)

Instances
---------

To see how to scan over a broad range of functors, let's look at each of the essential functor building blocks.

The identity functor is easiest.

> instance ScanL Id where
>   scanL (Id m) = (Id mempty, m)

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

> class ScanR f where
>   scanR :: Monoid m => f m -> (m, f m)

Instances
---------

> instance ScanR Id where
>   scanR (Id m) = (m, Id mempty)
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

