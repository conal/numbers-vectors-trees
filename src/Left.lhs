 <!-- -*- markdown -*-

> {-# LANGUAGE GADTs, KindSignatures, TypeFamilies, TypeOperators, Rank2Types
>            , ScopedTypeVariables
>   #-}
> {-# OPTIONS_GHC -Wall #-}
> {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-} -- temporary, pending ghc/ghci fix

> {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

|
Module      :  Left
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

Left-folding versions of BNat, Vec, and ComposeFunctor.
See those modules for more description.

> module Left
>   ( -- * Bounded numbers
>     BNat(..),predB,toBNat,fromBNat
>     -- * N-ary functor composition
>   , (:^)(..)
>     -- * Vectors
>   , Vec(..),headV,tailV,fromList
>   , littleEndianToZ,bigEndianToZ
>   , transpose, last, init
>   ) where

> import Prelude hiding (foldr,foldl,last,init,and)

> import Data.List (intercalate)
> import Control.Applicative (Applicative(..),(<$>),liftA2)
> import Data.Foldable (Foldable(..))
> import Data.Traversable (Traversable(..))
> import Data.Foldable (Foldable(..),foldl',foldr',and,toList)
> import Data.Traversable
> import Control.Arrow (first)

> import FunctorCombo.StrictMemo

> import TNat
> import Nat
> import ShowF

 -->

 <!-- references -->
 <!-- -->

Bounded numbers
===============

Swap the constructors.
No difference from right-folding version (other than swapping constructors), but I want to define a different `HasTrie` instance.

> data BNat :: * -> * where
>   BSucc :: BNat n -> BNat (S n)
>   BZero ::           BNat (S n)

> predB :: BNat (S n) -> BNat n
> predB (BSucc n) = n

> fromBNat :: BNat n -> Integer
> fromBNat BZero     = 0
> fromBNat (BSucc n) = (succ . fromBNat) n

> toBNat :: forall n. IsNat n => Integer -> Maybe (BNat n)
> toBNat = loop n where
>   n = nat :: Nat n
>   loop :: Nat n' -> Integer -> Maybe (BNat n')
>   loop Zero      _ = Nothing
>   loop (Succ _)  0 = Just BZero
>   loop (Succ n') m = fmap BSucc (loop n' (pred m))

Equality and ordering
---------------------

> instance Eq (BNat n) where
>   BZero   == BZero    = True
>   BSucc m == BSucc m' = m == m'
>   _       == _        = False

> instance Ord (BNat n) where
>   BZero   `compare` BZero    = EQ
>   BSucc m `compare` BSucc m' = m `compare` m'
>   BZero   `compare` BSucc _  = LT
>   BSucc _ `compare` BZero    = GT


N-ary functor composition
=========================

Shifting from right- to left-folded composition, a tiny change suffices in the `S` case:

< f :^ Z   =~ Id
< f :^ S n =~ (f :^ n) :. f

which translates to a correspondingly tiny change in the `SuccC` constructor.

> data (:^) :: (* -> *) -> * -> (* -> *) where
>   ZeroC :: a -> (f :^ Z) a
>   SuccC :: IsNat n => (f :^ n) (f a) -> (f :^ (S n)) a

The instance definitions are completely unchanged, since they are based purely on `Id` and functor composition.

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

> instance (Functor f, Foldable f) => Foldable (f :^ n) where
>   foldMap h (ZeroC a ) = h a
>   foldMap h (SuccC as) = fold (foldMap h <$> as)

> instance Traversable f => Traversable (f :^ n) where
>   sequenceA (ZeroC qa) = ZeroC <$> qa
>   sequenceA (SuccC as) = fmap SuccC . sequenceA . fmap sequenceA $ as

> instance (Functor f, Foldable f, Show a) => Show ((f :^ n) a) where
>   show x = "fromList " ++ show (toList x)

To do: A better `Show` instance, rendering the tree structure.
I haven't figured out how yet.
(See `Junk.lhs`.)

Equality and ordering
---------------------

Standard forms:

> instance (Foldable f, Applicative f, IsNat n, Eq a) => Eq ((f :^ n) a) where
>   (==) = (fmap.fmap) and (liftA2 (==))
>
> instance (Foldable f, Applicative f, IsNat n, Ord a) => Ord ((f :^ n) a) where
>   compare = (fmap.fmap) fold (liftA2 compare)



Vectors
=======

> infixl 5 :>
>
> data Vec :: * -> * -> * where
>   ZVec :: Vec Z a
>   (:>) :: IsNat n => Vec n a -> a -> Vec (S n) a

The definitions are changed systematically to reflect the reordered constructor arguments.

> headV :: Vec (S n) a -> a
> headV (_ :> a) = a

> tailV :: Vec (S n) a -> Vec n a
> tailV (as :> _) = as

Instances
---------

> instance Functor (Vec n) where
>   fmap _ ZVec      = ZVec
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

Showing
-------

> instance Show a => Show (Vec n a) where
>   -- show v = "fromList " ++ show (toList v)
>   show v = "("++ intercalate "," (fmap show (reverse (toList v))) ++")"

Equality and ordering
---------------------

> instance (IsNat n, Eq a) => Eq (Vec n a) where
>   (==) = (fmap.fmap) and (liftA2 (==))
>
> instance (IsNat n, Ord a) => Ord (Vec n a) where
>   compare = (fmap.fmap) fold (liftA2 compare)


Vectors as numbers
------------------

> type Digits k b = Vec k (BNat b)

< type Digits n b = BNat n :->: BNat b

> littleEndianToZ, bigEndianToZ :: forall k b. IsNat b => Digits k b -> Integer

> littleEndianToZ = foldr' (\ x s -> fromBNat x + b * s) 0
>  where b = natToZ (nat :: Nat b)

> bigEndianToZ    = foldl' (\ s x -> fromBNat x + b * s) 0
>  where b = natToZ (nat :: Nat b)

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

> instance Traversable (Vec n) where
>   traverse _ ZVec      = pure ZVec
>   traverse h (as :> a) = (:>) <$> traverse h as <*> h a


> last :: Vec (S n) a -> a
> last (ZVec :> a)        = a
> last (as@(_ :> _) :> _) = last as

> init :: Vec (S n) a -> Vec n a
> init (ZVec :> _)        = ZVec
> init (as@(_ :> _) :> a) = init as :> a

