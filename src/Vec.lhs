 <!-- -*- markdown -*-

> {-# LANGUAGE GADTs, KindSignatures, EmptyDataDecls, ScopedTypeVariables #-}
> {-# OPTIONS_GHC -Wall #-}

< {-# LANGUAGE FlexibleInstances, FlexibleContexts #-}  -- For Maxime's version

|
Module      :  Vec
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

Simple module for length-typed vectors

> module Vec (Vec(..),headV,tailV,fromList,littleEndianToZ,bigEndianToZ) where

> import Prelude hiding (foldr,foldl)
> import Control.Applicative (Applicative(..))
> import Data.Foldable (Foldable(..),foldl',foldr')

< import Control.Monad (join) -- with Maxime's version

> import TNat
> import Nat
> import BNat

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
>   (:<) :: a -> Vec n a -> Vec (S n) a


The `headV` and `tailV` functions are like `head` and `tail` but understand lengths:

> headV :: Vec (S n) a -> a
> headV (a :< _) = a
> headV _        = error "bogus case pending compiler fix"

> tailV :: Vec (S n) a -> Vec n a
> tailV (_ :< as) = as
> tailV _         = error "bogus case pending compiler fix"

Unlike their list counterparts, `headV` and `tailV` are *safe*, in that the precondition of non-emptiness is verified statically.


Instances
=========

> instance Functor (Vec n) where
>   fmap _ ZVec     = ZVec
>   fmap f (a :< u) = f a :< fmap f u

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

< instance IsNat n => Monad (Vec n) where
<   return  = pure
<   v >>= f = join (fmap f v)

The `join` function on `Vec n` is just like `join` for functions and for streams.
(Rightly so, considering the principle of [type class morphism]s.)
It uses diagonalization, and one way to think of vector `join` is that it extracts the diagonal of a square matrix.

< join :: Vec n (Vec n a) -> Vec n a
< join ZVec      = ZVec
< join (v :< vs) = headV v :< join (fmap tailV vs)


Convert between vectors and lists
=================================

> fromList :: IsNat n => [a] -> Vec n a
> fromList = fromListN nat

> fromListN :: Nat n -> [a] -> Vec n a
> fromListN Zero     []     = ZVec
> fromListN (Succ n) (a:as) = a :< fromListN n as
> fromListN _        _      = error "fromListN: length mismatch"

> toList :: Vec n a -> [a]
> toList = foldr (:) []

Showing
=======

> instance Show a => Show (Vec n a) where
>   show v = "fromList " ++ show (toList v)


Vectors as numbers
==================

We've seen that `Vec` is a trie for bounded numbers.
It's also the case that a vector of digits can be used to *represent* numbers

> type Digits k b = Vec k (BNat b)

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

[Maxime Henrion suggested](http://conal.net/blog/posts/fixing-lists/comment-page-1/#comment-71660) an alternative to my `Applicative` instance above:

< instance Applicative (Vec Z) where
<   pure _ = ZVec
<   ZVec <*> ZVec = ZVec
<
< instance Applicative (Vec n) => Applicative (Vec (S n)) where
<   pure a = a :< pure a
<   (f :< fs) <*> (a :< as) = f a :< (fs <*> as)

A small drawback of this version is that it requires the GHC language extensions `FlexibleInstances` and `FlexibleContexts`.
I suspect the constraint `Applicative (Vec n)` would be cumbersome in practice.

Continuing on to `Monad`:

< instance Monad (Vec Z) where
<   return  = pure
<   v >>= f = joinZ (fmap f v)
<
< instance Monad (Vec n) => Monad (Vec (S n)) where
<   return  = pure
<   v >>= f = joinS (fmap f v)

< joinZ :: Vec Z (Vec Z a) -> Vec Z a
< joinZ ZVec = ZVec
<
< joinS :: Monad (Vec n) => Vec (S n) (Vec (S n) a) -> Vec (S n) a
< joinS (v :< vs) = headV v :< join (fmap tailV vs)

In this case, I'm using the general `join` function on monads.
The `Monad` instances would be more elegant and perhaps more efficient if `join` were a method on `Monad` as has been proposed.

 -->
