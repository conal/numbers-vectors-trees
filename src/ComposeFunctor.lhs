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

> module ComposeFunctor ((:^)(..),unZeroC,unSuccC,inC,inC2) where

> import Prelude hiding (and)

> import Control.Applicative (Applicative(..),liftA2,(<$>))
> import Data.Foldable (Foldable(..),and)
> import Data.Traversable (Traversable(..))

> import Nat
> import ShowF

References:

[*Applicative Programming with Effects*]: http://www.soi.city.ac.uk/~ross/papers/Applicative.html "Paper by Conor McBride and Ross Paterson"

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

> unSuccC :: (f :^ (S n)) a -> f ((f :^ n) a)
> unSuccC (SuccC fsa) = fsa

Operate inside the representation of `f :^ n`:

> inC :: (a -> b)
>     -> (forall n. IsNat n => f ((f :^ n) a) -> f ((f :^ n) b))
>     -> (forall n. (f :^ n) a -> (f :^ n) b)
> inC l _ (ZeroC a ) = (ZeroC (l a ))
> inC _ b (SuccC as) = (SuccC (b as))

> inC2 :: (a -> b -> c)
>      -> (forall n. IsNat n => f ((f :^ n) a) -> f ((f :^ n) b) -> f ((f :^ n) c))
>      -> (forall n. (f :^ n) a -> (f :^ n) b -> (f :^ n) c)
> inC2 l _ (ZeroC a ) (ZeroC b ) = ZeroC (l a  b )
> inC2 _ b (SuccC as) (SuccC bs) = SuccC (b as bs)

> instance ShowF f => ShowF (f :^ n) where showF = show
>
> instance (Show a, ShowF f) => Show ((f :^ n) a) where
>   show (ZeroC a ) = "(ZeroC "++ show a ++")"
>   show (SuccC as) = "(SuccC "++ showF as ++")"

Functors compose into functors and applicatives into applicatives.
(See [*Applicative Programming with Effects*] (section 5) and [*Semantic editor combinators*].)
The following definitions arise from the standard instances for binary functor composition.

> instance Functor f => Functor (f :^ n) where
>   fmap h = inC h ((fmap.fmap) h)

> instance (IsNat n, Applicative f) => Applicative (f :^ n) where
>   pure = pureN nat
>   (<*>) = inC2 ($) (liftA2 (<*>))

> pureN :: Applicative f => Nat n -> a -> (f :^ n) a
> pureN Zero     a = ZeroC a
> pureN (Succ _) a = SuccC ((pure . pure) a)

More explicitly:

< pureN (Succ n) a = SuccC ((pure . pureN n) a)

The `Foldable` and `Traversable` classes are also closed under composition.

> instance (Functor f, Foldable f) => Foldable (f :^ n) where
>   fold (ZeroC a ) = a
>   fold (SuccC as) = fold (fold <$> as)

Or

>   foldMap h (ZeroC a ) = h a
>   foldMap h (SuccC as) = fold (foldMap h <$> as)


> instance Traversable f => Traversable (f :^ n) where
>   sequenceA (ZeroC qa) = ZeroC <$> qa
>   sequenceA (SuccC as) = fmap SuccC . sequenceA . fmap sequenceA $ as

i.e.,

<   sequenceA . ZeroC = fmap ZeroC
<
<   sequenceA . SuccC = fmap SuccC . sequenceA . fmap sequenceA

Equality and ordering
=====================

Standard forms:

> instance (Foldable f, Applicative f, IsNat n, Eq a) => Eq ((f :^ n) a) where
>   (==) = (fmap.fmap) and (liftA2 (==))
>
> instance (Foldable f, Applicative f, IsNat n, Ord a) => Ord ((f :^ n) a) where
>   compare = (fmap.fmap) fold (liftA2 compare)


