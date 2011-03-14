 <!-- -*- markdown -*-

> {-# LANGUAGE GADTs, KindSignatures, EmptyDataDecls, ScopedTypeVariables #-}
> {-# LANGUAGE TypeFamilies, TypeOperators #-}  -- for trie
> {-# LANGUAGE FlexibleInstances, UndecidableInstances #-} -- for vector-space instances
>
> {-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
> {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-} -- temporary, pending ghc/ghci fix

|
Module      :  Vec
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

Simple module for length-typed vectors.
See the following blog posts:
<http://conal.net/blog/posts/fixing-lists/>, 
<http://conal.net/blog/posts/doing-more-with-length-typed-vectors/>,
<http://conal.net/blog/posts/reverse-engineering-length-typed-vectors/>, and
<http://conal.net/blog/posts/a-trie-for-length-typed-vectors/>.

> module Vec ( Vec(..),headV,tailV,fromList
>            , littleEndianToZ,bigEndianToZ
>            , transpose, last, init
>            ) where

> import Prelude hiding (foldr,foldl,last,init,and)
> import Control.Applicative (Applicative(..),(<$>),liftA2)
> import Data.AffineSpace
> import Data.Basis
> import Data.Cross
> import Data.Foldable (Foldable(..),foldl',foldr,foldr',and,toList)
> import Data.Traversable
> import Data.VectorSpace hiding (sumV)
> import Control.Arrow (first)

> import FunctorCombo.StrictMemo

> import Nat
> import BNat
> import ShowF

> import ComposeFunctor

 -->

 <!-- references -->

[type class morphism]: http://conal.net/blog/tag/type-class-morphism/ "Posts on type class morphisms"

 <!-- -->

Length-typed vectors
====================

> infixr 5 :<
>
> data Vec :: * -> * -> * where
>   ZVec :: Vec Z a
>   (:<) :: IsNat n => a -> Vec n a -> Vec (S n) a

The `headV` and `tailV` functions are like `head` and `tail` but understand lengths:

> headV :: Vec (S n) a -> a
> headV (a :< _) = a

> tailV :: Vec (S n) a -> Vec n a
> tailV (_ :< as) = as

Unlike their list counterparts, `headV` and `tailV` are *safe*, in that the precondition of non-emptiness is verified statically.


Instances
=========

> instance Functor (Vec n) where
>   fmap _ ZVec      = ZVec
>   fmap f (a :< as) = f a :< fmap f as

Folding is also straight-forward:

> instance Foldable (Vec n) where
>   foldr _  b ZVec     = b
>   foldr h b (a :< as) = a `h` foldr h b as

*Exercise*: Can you define `fmap` via `foldr`?

<div class=toggle>
I haven't seen how to.
Works easily for standard lists (variable-length, not length-typed), but the type of `foldr` appears to be too restrictive for `Vec`.
</div>

We can build vectors from a single element, to be repeated:

< pureV :: IsNat n => a -> Vec n a
< pureV = pureN nat

< pureN :: Nat n -> a -> Vec n a
< pureN Zero     _ = ZVec
< pureN (Succ n) a = a :< pureN n a

Alternatively, build `pureV` out of `units`, which makes vectors consisting entirely of `()`:

> pureV :: IsNat n => a -> Vec n a
> pureV a = fmap (const a) units

or

< pure = (<$ units)

Thanks to Eyal Lotem for [suggesting this rewriting](http://conal.net/blog/posts/doing-more-with-length-typed-vectors/comment-page-1/#comment-73663).

> units :: IsNat n => Vec n ()
> units = unitsN nat

> unitsN :: Nat n -> Vec n ()
> unitsN Zero     = ZVec
> unitsN (Succ n) = () :< unitsN n

Apply functions to arguments:

> applyV :: Vec n (a -> b) -> Vec n a -> Vec n b
> ZVec      `applyV` ZVec      = ZVec
> (f :< fs) `applyV` (x :< xs) = f x :< (fs `applyV` xs)

modulo a compiler oddity.

<div class=toggle>
GHC 6.12.3 gives me a warning (with `-Wall`, which I always use):

    Warning: Pattern match(es) are non-exhaustive
             In the definition of `<*>':
                 Patterns not matched:
                     ZVec (_ :< _)
                     (_ :< _) ZVec

Adding the following cases silences the compiler.

> ZVec `applyV` (_ :< _) = undefined
> (_ :< _) `applyV` ZVec = undefined

I don't know how the two cases could even type-check.

However, benmachine found that GHC 7.0.1 balks at these definitions as ill-typed,
but also warns of non-exhaustive patterns when the lines are removed.

I added [a comment to a ghc ticket](http://hackage.haskell.org/trac/ghc/ticket/3927#comment:14).

</div>

The `pureV` and `applyV` functions are just what we need for an applicative functor instance:

> instance IsNat n => Applicative (Vec n) where
>   pure  = pureV
>   (<*>) = applyV

Finally, a `Monad` instance:

First the easy parts: standard definitions in terms of `pure` and `join`:

> instance IsNat n => Monad (Vec n) where
>   return  = pure
>   v >>= f = join (fmap f v)

The `join` function on `Vec n` is just like `join` for functions and for streams.
(Rightly so, considering the principle of [type class morphism]s.)
It uses diagonalization, and one way to think of vector `join` is that it extracts the diagonal of a square matrix.

> join :: Vec n (Vec n a) -> Vec n a
> join ZVec      = ZVec
> join (v :< vs) = headV v :< join (fmap tailV vs)

Convert between vectors and lists
=================================

> fromList :: IsNat n => [a] -> Vec n a
> fromList = fromListN nat

> fromListN :: Nat n -> [a] -> Vec n a
> fromListN Zero     []     = ZVec
> fromListN (Succ n) (a:as) = a :< fromListN n as
> fromListN _        _      = error "fromListN: length mismatch"

Showing
=======

> instance Show a => Show (Vec n a) where
>   show v = "fromList " ++ show (toList v)
>
> instance ShowF (Vec n) where showF = show

Equality and ordering
=====================

Standard forms:

< instance Eq a => Eq (Vec n a) where
<   ZVec      == ZVec      = True
<   (a :< as) == (b :< bs) = a == b && as == bs
<
< instance Ord a => Ord (Vec n a) where
<   ZVec      `compare` ZVec      = mempty
<   (a :< as) `compare` (b :< bs) = (a `compare` b) `mempty` (as `compare` bs)

This definition makes use of the handy `Monoid` instance for `Ordering`:

< instance Monoid Ordering where
<   mempty     = EQ
<   EQ `mappend` o = o
<   o `mappend` _  = o

More simply:

< instance (IsNat n, Eq a) => Eq (Vec n a) where
<   as == bs = and (liftA2 (==) as bs)
<
< instance (IsNat n, Ord a) => Ord (Vec n a) where
<   as `compare` bs = fold (liftA2 compare as bs)

Or

> instance (IsNat n, Eq a) => Eq (Vec n a) where
>   (==) = (fmap.fmap) and (liftA2 (==))
>
> instance (IsNat n, Ord a) => Ord (Vec n a) where
>   compare = (fmap.fmap) fold (liftA2 compare)


Vectors as tries
================

An $n$-vector associates a value with every number from $0$ to $n-1$, so it's a trie over `BNat n`.

> instance IsNat n => HasTrie (BNat n) where
>   type Trie (BNat n) = Vec n
>   trie = trieB nat
>   untrie (a :< _ ) BZero     = a
>   untrie (_ :< as) (BSucc m) = untrie as m
>   enumerate (a :< as) = (BZero,a) : map (first BSucc) (enumerate as)

> trieB :: Nat n -> (BNat n -> a) -> (BNat n :->: a)
> trieB Zero     _ = ZVec
> trieB (Succ m) f = f BZero :< trieB m (f . BSucc)

Vectors as numbers
==================

We've seen that `Vec` is a trie for bounded numbers.
It's also the case that a vector of digits can be used to *represent* numbers

> type Digits k b = Vec k (BNat b)

Or, more pleasing to my eye,

< type Digits n b = BNat n :->: BNat b

These representations can be given a little-endian or big-endian interpretation:

> littleEndianToZ, bigEndianToZ :: forall k b. IsNat b => Digits k b -> Integer

> littleEndianToZ = foldr' (\ x s -> fromBNat x + b * s) 0
>  where b = natToZ (nat :: Nat b)

> bigEndianToZ    = foldl' (\ s x -> fromBNat x + b * s) 0
>  where b = natToZ (nat :: Nat b)

[The `foldl'` and `foldr'`] are from [`Data.Foldable`](http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-Foldable.html#v:foldl-39-).

Give it a try:

< *Vec> let ds = map zToBNat [3,5,7] :: [BNat TenT]
< *Vec> let v3 = fromList ds :: Vec ThreeT (BNat TenT)
< *Vec> v3
< fromList [3,5,7]
< *Vec> littleEndianToZ v3
< 753
< *Vec> bigEndianToZ v3
< 357

It's a shame here to map to the unconstrained `Integer` type, since (a) the result must be a natural number, and (b) the result is statically bounded by $b^k$.

 <!--[

Another angle on vectors as numbers
===================================

 Generate bogus (error-producing) Enum:

 #define INSTANCE_Enum

 Set up the macro parameters:

 #define CONSTRAINTS IsNat n,
 #define APPLICATIVE (Vec n)

 And generate numeric instances:

 #include "ApplicativeNumeric-inc.hs"

> 

 #include "T1.lhs"

Trying to figure out how to #include code into .lhs files

 ]-->
 
Vector tries
============

Using the analysis above, we can easily define tries over vectors as $n$-ary composition of tries over the vector element type.
Again, there is a right-folded and a left-folded version.
I'll give the right-folded version here.
See the `Left` module for left-folded vectors.

> instance (IsNat n, HasTrie a) => HasTrie (Vec n a) where
>   type Trie (Vec n a) = Trie a :^ n

Conversion from trie to function is, as always, a trie look-up.
Its definition closely follows the definition of `f :^ n`:

>   ZeroC v `untrie` ZVec      = v
>   SuccC t `untrie` (a :< as) = (t `untrie` a) `untrie` as
>   enumerate = error "enumerate: not yet defined on Vec n a"

For `untrie`, we were able to follow the zero/successor structure of the trie.
For `trie`, we don't have such a structure to follow, but we can play the same trick as for defining `units` above: use the `nat` method of the `IsNat` class to synthesize a number of type `Nat n`, and then follow the structure of that number in a new recursive function definition.

>   trie = trieN nat

where

> trieN :: HasTrie a => Nat n -> (Vec n a -> b) -> (Trie a :^ n) b
> trieN Zero     f = ZeroC (f ZVec)
> trieN (Succ _) f = SuccC (trie (\ a -> trie (f . (a :<))))

Some more operations
====================

> transpose :: IsNat n => Vec m (Vec n a) -> Vec n (Vec m a)

< transpose ZVec      = pure ZVec
< transpose (v :< vs) = liftA2 (:<) v (transpose vs)

This simpler definition doesn't check:

< transpose = foldr (liftA2 (:<)) (pure ZVec)

    Occurs check: cannot construct the infinite type: n = S n
      Expected type: Vec n1 (Vec n a)
      Inferred type: Vec n1 (Vec (S n) a)
    In the first argument of `foldr', namely `(liftA2 (:<))'
    In the expression: foldr (liftA2 (:<)) (pure ZVec)

From mux
--------

See [mux's stuff](https://bitbucket.org/mumux/stuff/src/1e9537e03f08/Vector.hs).

> transpose = sequenceA

> instance Traversable (Vec n) where
>   traverse _ ZVec      = pure ZVec
>   traverse f (x :< xs) = (:<) <$> f x <*> traverse f xs

> last :: Vec (S n) a -> a
> last (x :< ZVec)        = x
> last (_ :< xs@(_ :< _)) = last xs

> init :: Vec (S n) a -> Vec n a
> init (_ :< ZVec)        = ZVec
> init (x :< xs@(_ :< _)) = x :< init xs

Mux says

 > ah, from a related bug report: "I wish this was easier to fix. The difficulty is that the type inference engine (which has a sophisticated constraint solver) only sees one equation at a time, and hence can't check exhaustiveness). But the overlap checker (which sees all the equations at once) does not have a sophisticated solver." from spj

vector-space instances
======================

> instance (AdditiveGroup a, IsNat n)
>   => AdditiveGroup (Vec n a) where
>   zeroV = pure zeroV
>   (^+^) = liftA2 (^+^)
>   negateV = fmap negateV
>
> instance (IsNat n, VectorSpace a, s ~ Scalar a)
>   => VectorSpace (Vec n a) where
>   type Scalar (Vec n a) = Scalar a
>   (*^) s = fmap (s *^)
>
> instance (InnerSpace a, s ~ Scalar a,
>   AdditiveGroup (Scalar a), IsNat n)
>   => InnerSpace (Vec n a) where
>   -- (<.>) v = foldr (^+^) zeroV . liftA2 (<.>) v
>   -- (<.>) v = sumV . liftA2 (<.>) v
>   -- (<.>) v = result sumV (liftA2 (<.>) v)
>   (<.>) = (result.result) sumV (liftA2 (<.>))
>
> instance (AffineSpace a, IsNat n) => AffineSpace (Vec n a) where
>   type Diff (Vec n a) = Vec n (Diff a)
>   (.-.) = liftA2 (.-.)
>   (.+^) = liftA2 (.+^)
>
> instance (AdditiveGroup a) => HasCross2 (Vec TwoT a) where
>   cross2 (x :< y :< ZVec) = negateV y :< x :< ZVec
>
> instance (VectorSpace a, a ~ Scalar a) => HasCross3 (Vec ThreeT a) where
>   (ax :< ay :< az :< ZVec) `cross3` (bx :< by :< bz :< ZVec)
>     = cx :< (cy :< (cz :< ZVec))
>     where  cx = ay *^ bz ^-^ az *^ by
>            cy = az *^ bx ^-^ ax *^ bz
>            cz = ax *^ by ^-^ ay *^ bx
>
> instance (HasBasis a, a ~ Scalar a) => HasBasis (Vec OneT a) where
>   type Basis (Vec OneT a) = Basis a
>   basisValue b = (basisValue b) :< ZVec
>   decompose (a :< _) = decompose a
>   decompose' (a :< _) = const a
> 
> instance (HasBasis a, HasBasis (Vec (S n) a), IsNat n)
>   => HasBasis (Vec (S (S n)) a) where
>   type Basis (Vec (S (S n)) a) = Basis a `Either` Basis (Vec (S n) a)
>   basisValue (Left a) = basisValue a :< zeroV
>   basisValue (Right b) = zeroV :< basisValue b
>   decompose (a :< v) = decomp2 Left a ++ decomp2 Right v
>   decompose' (a :< v) = decompose' a `either` decompose' v
> 
> decomp2 :: HasBasis w => (Basis w -> b) -> w -> [(b, Scalar w)]
> decomp2 inject = fmap (first inject) . decompose

Misc
====

Add post-processing, SEC-style:

> result :: (b -> b') -> ((a -> b) -> (a -> b'))
> result = (.)

Sum over several vectors.
To do: move into AdditiveGroup:

> sumV :: (Foldable f, AdditiveGroup v) => f v -> v
> sumV = foldr (^+^) zeroV

