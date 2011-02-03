 <!-- -*- markdown -*-

> {-# LANGUAGE GADTs, KindSignatures, TypeFamilies, TypeOperators, Rank2Types #-}
> {-# OPTIONS_GHC -Wall #-}
> {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-} -- temporary, pending ghc/ghci fix

> {-# OPTIONS_GHC -Wall #-}
> {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
> {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-} -- temporary, pending ghc/ghci fix

|
Module      :  Left
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

Left-folding versions of ComposeFunctor and Vec

> module Left where

> import Prelude hiding (foldr,foldl,last,init)

> import Control.Applicative (Applicative(..),(<$>),liftA2)
> import Data.Foldable (Foldable(..),foldl',foldr')
> import Data.Traversable
> import Control.Arrow (first)

> import FunctorCombo.StrictMemo

> import TNat
> import Nat

 -->

 <!-- references -->
 <!-- -->

N-ary functor composition
=========================

For left-folded composition, a tiny change suffices in the `S` case:

< f :^ Z   =~ Id
< f :^ S n =~ (f :^ n) :. f

which translates to a correspondingly tiny change in the `SuccC` constructor.

> data (:^) :: (* -> *) -> * -> (* -> *) where
>   ZeroC :: a -> (f :^ Z) a
>   SuccC :: IsNat n => (f :^ n) (f a) -> (f :^ (S n)) a

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


Bounded numbers
===============

Swap the constructors.
No substantive difference here, but I want to define a different `Trie` functor.

> data BNat :: * -> * where
>   BSucc :: BNat n -> BNat (S n)
>   BZero ::           BNat (S n)

Vectors
=======

> infixl 5 :>
>
> data Vec :: * -> * -> * where
>   ZVec :: Vec Z a
>   (:>) :: IsNat n => Vec n a -> a -> Vec (S n) a

> headV :: Vec (S n) a -> a
> headV (_ :> a) = a

> tailV :: Vec (S n) a -> Vec n a
> tailV (as :> _) = as

Instances
---------

> instance Functor (Vec n) where
>   fmap _ ZVec     = ZVec
>   fmap f (as :> a) = fmap f as :> f a


> instance Foldable (Vec n) where
>   foldr _  b ZVec     = b
>   foldr h b (as :> a) = a `h` foldr h b as

We can build vectors from a single element, to be repeated:

> pureV :: IsNat n => a -> Vec n a
> pureV a = fmap (const a) units

> units :: IsNat n => Vec n ()
> units = unitsN nat

> unitsN :: Nat n -> Vec n ()
> unitsN Zero     = ZVec
> unitsN (Succ n) = unitsN n :> ()

Apply functions to arguments:

> applyV :: Vec n (a -> b) -> Vec n a -> Vec n b
> ZVec      `applyV` ZVec      = ZVec
> (fs :> f) `applyV` (xs :> x) = (fs `applyV` xs) :> f x


> instance IsNat n => Applicative (Vec n) where
>   pure  = pureV
>   (<*>) = applyV

> instance IsNat n => Monad (Vec n) where
>   return  = pure
>   v >>= f = join (fmap f v)

> join :: Vec n (Vec n a) -> Vec n a
> join ZVec      = ZVec
> join (vs :> v) = join (fmap tailV vs) :> headV v

Convert between vectors and lists
---------------------------------

> fromList :: IsNat n => [a] -> Vec n a
> fromList = fromListN nat . reverse

> fromListN :: Nat n -> [a] -> Vec n a
> fromListN Zero     []     = ZVec
> fromListN (Succ n) (a:as) = fromListN n as :> a
> fromListN _        _      = error "fromListN: length mismatch"

> toList :: Vec n a -> [a]
> toList = foldl (flip (:)) []

Showing
-------

> instance Show a => Show (Vec n a) where
>   show v = "fromList " ++ show (toList v)

Vectors as tries
----------------

> instance IsNat n => HasTrie (BNat n) where
>   type Trie (BNat n) = Vec n
>   trie = trieB nat
>   untrie (_ :> a ) BZero     = a
>   untrie (as :> _) (BSucc m) = untrie as m
>   enumerate (as :> a) = (BZero,a) : map (first BSucc) (enumerate as)

> trieB :: Nat n -> (BNat n -> a) -> (BNat n :->: a)
> trieB Zero     _ = ZVec
> trieB (Succ m) f = trieB m (f . BSucc) :> f BZero


Vector tries
------------

> instance (IsNat n, HasTrie a) => HasTrie (Vec n a) where
>   type Trie (Vec n a) = Trie a :^ n
>   ZeroC b `untrie` ZVec      = b
>   SuccC t `untrie` (as :> a) = (t `untrie` as) `untrie` a

 <!--

>   enumerate = error "enumerate: not yet defined on Vec n a"

 -->

>   trie = trieN nat

> trieN :: HasTrie a => Nat n -> (Vec n a -> b) -> (Trie a :^ n) b
> trieN Zero     f = ZeroC (f ZVec)
> trieN (Succ _) f = SuccC (trie (\ as -> trie (f . (as :>))))


Some more operations
--------------------

> transpose :: IsNat n => Vec m (Vec n a) -> Vec n (Vec m a)
> transpose = sequenceA

From mux
--------

See [mux's stuff](https://bitbucket.org/mumux/stuff/src/1e9537e03f08/Vector.hs).

> last :: Vec (S n) a -> a
> last (ZVec :> x)        = x
> last (xs@(_ :> _) :> _) = last xs

> init :: Vec (S n) a -> Vec n a
> init (ZVec :> _)        = ZVec
> init (xs@(_ :> _) :> x) = init xs :> x

> instance Traversable (Vec n) where
>   traverse _ ZVec      = pure ZVec
>   traverse f (xs :> x) = (:>) <$> traverse f xs <*> f x

Mux says

 > ah, from a related bug report: "I wish this was easier to fix. The difficulty is that the type inference engine (which has a sophisticated constraint  solver) only sees one equation at a time, and hence can't check exhaustiveness). But the overlap checker (which sees all the equations at once) does not  have a sophisticated solver." from spj



