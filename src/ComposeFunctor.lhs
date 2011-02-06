 <!-- -*- markdown -*-

> {-# LANGUAGE GADTs, KindSignatures, TypeOperators, Rank2Types #-}
> {-# OPTIONS_GHC -Wall #-}
> {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-} -- temporary, pending ghc/ghci fix

|
Module      :  ComposeFunctor
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

N-ary functor composition.
See <http://conal.net/blog/posts/a-trie-for-length-typed-vectors/>.

> module ComposeFunctor ((:^)(..),unZeroC,unSuccC) where

> import Prelude hiding (and)

> import Control.Applicative (Applicative(..),liftA2,(<$>))
> import Data.Foldable (Foldable(..),and)
> import Data.Traversable (Traversable(..))

> import TNat
> import Nat
> import ShowF

References:

[*Applicative Programming with Effects*]: http://www.soi.city.ac.uk/~ross/papers/Applicative.html "Paper by Conor McBride and Ross Paterson"

[*Lazier function definitions by merging partial values*]: http://conal.net/blog/posts/lazier-function-definitions-by-merging-partial-values/ "blog post"

[*Semantic editor combinators*]: http://conal.net/blog/posts/semantic-editor-combinators/ "blog post"

 -->

Functor composition
===================

Since composition is associative, a recursive formulation might naturally fold from the left or from the right.
In this module, we'll fold on the right.
See the module `Left` for left-folded composition.

< f :^ Z   =~ Id
< f :^ S n =~ f :. (f :^ n)

Writing as a GADT:

> data (:^) :: (* -> *) -> * -> (* -> *) where
>   ZeroC :: a -> (f :^ Z) a
>   SuccC :: IsNat n => f ((f :^ n) a) -> (f :^ (S n)) a

> unZeroC :: (f :^ Z) a -> a
> unZeroC (ZeroC a) = a

> unSuccC :: IsNat n => (f :^ (S n)) a -> f ((f :^ n) a)
> unSuccC (SuccC fsa) = fsa


> instance ShowF f => ShowF (f :^ n) where showF = show
>
> instance (Show a, ShowF f) => Show ((f :^ n) a) where
>   show (ZeroC a ) = "(ZeroC "++ show a ++")"
>   show (SuccC as) = "(SuccC "++ showF as ++")"

Functors compose into functors and applicatives into applicatives.
(See [*Applicative Programming with Effects*] (section 5) and [*Semantic editor combinators*].)
The following definitions arise from the standard instances for binary functor composition.

> instance Functor f => Functor (f :^ n) where
>   fmap h (ZeroC a)  = ZeroC (h a)
>   fmap h (SuccC fs) = SuccC ((fmap.fmap) h fs)

> instance (IsNat n, Applicative f) => Applicative (f :^ n) where
>   pure = pureN nat
>   ZeroC f  <*> ZeroC x  = ZeroC (f x)
>   SuccC fs <*> SuccC xs = SuccC (liftA2 (<*>) fs xs)

> pureN :: Applicative f => Nat n -> a -> (f :^ n) a
> pureN Zero     a = ZeroC a
> pureN (Succ _) a = SuccC ((pure . pure) a)

More explicitly:

< pureN (Succ n) a = SuccC ((pure . pureN n) a)

Using `lub`, there's a tidier definition of `(<*>)`:

<   (<*>) = inZeroC2 ($) `lub` inSuccC2 (liftA2 (<*>))

Where `inZeroC2` and `inSuccC2` are *partial* binary functions that work inside of `ZeroC` and `SuccC` as used in various of my blog posts & libraries.
This example demonstrates another notational benefit of `lub`, extending the techniques in the post [*Lazier function definitions by merging partial values*].

The `Foldable` and `Traversable` classes are also closed under composition.

> instance (Functor f, Foldable f) => Foldable (f :^ n) where
>   foldMap h (ZeroC a ) = h a
>   foldMap h (SuccC as) = fold (foldMap h <$> as)

> instance Traversable f => Traversable (f :^ n) where
>   sequenceA (ZeroC qa) = ZeroC <$> qa
>   sequenceA (SuccC as) = fmap SuccC . sequenceA . fmap sequenceA $ as

i.e.,

<   sequenceA . ZeroC = fmap ZeroC
<
<   sequenceA . SuccC = fmap SuccC . sequenceA . fmap sequenceA

Experiments
===========

< unZeroC :: (f :^ Z) a -> a
< unZeroC (ZeroC a) = a
<
< unSuccC :: IsNat n => (f :^ (S n)) a -> f ((f :^ n) a)
< unSuccC (SuccC as) = as

< inZeroC :: (a -> b)
<         -> (forall n. IsNat n => (f :^ n) a -> (f :^ n) b)
< inZeroC h (ZeroC a ) = ZeroC (h a )

< inSuccC :: (forall n. IsNat n => f ((f :^ n) a) -> f ((f :^ n) b))
<         -> (forall n. IsNat n => (f :^ n) a -> (f :^ n) b)
< inSuccC h (SuccC as) = SuccC (h as)

< inZeroC2 :: (a -> b -> c)
<          -> (forall n. IsNat n => (f :^ n) a -> (f :^ n) b -> (f :^ n) c)
< inZeroC2 h (ZeroC a ) (ZeroC b ) = ZeroC (h a  b )

< inSuccC2 :: (forall n. IsNat n => f ((f :^ n) a) -> f ((f :^ n) b) -> f ((f :^ n) c))
<          -> (forall n. IsNat n => (f :^ n) a -> (f :^ n) b -> (f :^ n) c)
< inSuccC2 h (SuccC as) (SuccC bs) = SuccC (h as bs)

With these definitions, there's a tidier definition for `(<*>)`:

<   (<*>) = inZeroC2 ($) `lub` inSuccC2 (liftA2 (<*>))

Equality and ordering
=====================

Standard forms:

> instance (Foldable f, Applicative f, IsNat n, Eq a) => Eq ((f :^ n) a) where
>   (==) = (fmap.fmap) and (liftA2 (==))
>
> instance (Foldable f, Applicative f, IsNat n, Ord a) => Ord ((f :^ n) a) where
>   compare = (fmap.fmap) fold (liftA2 compare)


