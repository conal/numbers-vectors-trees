 <!-- -*- markdown -*-

> {-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators, Rank2Types #-}

> {-# OPTIONS_GHC -Wall #-}
> {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-} -- temporary, pending ghc/ghci fix
> {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

|
Module      :  TreeScan
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

> module TreeScan where

> import Prelude hiding (sum,zip,unzip)

> import FunctorCombo.StrictMemo

> import Nat
> import Left
> import LeftNum ()
> import Pair
> import SEC

> import Extremes hiding (T)
> import qualified Vec            as R
> import qualified ComposeFunctor as R

> import NavigateTree

 -->

 <!-- references -->

[*From tries to trees*]: http://conal.net/blog/posts/from-tries-to-trees/ "blog post"

[*Programming parallel algorithms*]: http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.53.5739 "Paper by Guy Blelloch, 1990"

[*Type-bounded numbers*]: http://conal.net/blog/posts/type-bounded-numbers/ "blog post"

 <!-- -->


Introduction
============

Guy Blelloch's paper [*Programming parallel algorithms*] includes a parallel algorithm for prefix sum.
It applies not just numeric addition but to all monoids.
Associativity and indentity allow a divide-and-conquer approach.

In the section called "Three Other Algorithms", Guy writes

 > The algorithm works by elementwise adding the odd and even elements and recursively solving the problem on these sums.
   The result of the recursive call is then used to generate all the prefix sums.

This algorithm assumes the array size is a power of two, so that each uninterleaving yields the same number of even as odd elements.
I want to capture this power-of-two assumption statically.
As mentioned in [*From tries to trees*], perfect binary trees (with values at leaves) of depth $n$
have $2^n$ elements and can be statically depth-typed.
Moreover, as shown in [*A trie for length-typed vectors*], such trees naturally arise as the trie functors for size-typed vectors of bits.
A bit can represented as the type of natural numbers less than two, as in [*Type-bounded numbers*], but for notational convenience I'll use a specialized `Bit` type and `Pair` functor.

> type Bits  n = Vec n Bit
>
> type T n = Trie (Bits n)

Equivalently,

< type T n = Trie (Bits n)
<          = Trie (Vec n Bit)
<          = Trie Bit :^ n
<          = Pair :^ n

where `f :^ n` is the $n$-ary composition of the functor `f` with itself.

For now, this module is light on commentary.
To do: extract prose from the other module I started (without size-typing).
Or update that module and refer to it here, focusing remarks on changes.

If the generality of `Vec` leads to inconvenient notation, then maybe use a specialized definitions.
I'd like the general form to work, so I'm trying it first.

Start with a functional algorithm exclusive scan based on Guy Blelloch's.
Use a *left-folded* binary tree to make it easy to access consecutive pairs (even/odd).

Scan
====

< scan1 :: Num a => Unop (T n a)
< scan1 (ZeroC _ ) = ZeroC 0
< scan1 (SuccC as) = SuccC (invert (ss :# ss + es))
<  where
<    (es :# os) = invert as
<    ss         = scan1 (es + os)

Factor out the pair/tree containment inversions:

< scan1 :: Num a => Unop (T n a)
< scan1 (ZeroC _ ) = ZeroC 0
< scan1 (SuccC as) = SuccC (inInvert h as)
<  where
<    h (es :# os) = (ss :# ss + es)
<     where ss = scan1 (es + os)

And then use `inC` for the tree transformation pattern:

> scan1 :: Num a => Unop (T n a)
> scan1 = inC (const 0) (inInvert h)
>  where
>    h (es :# os) = (ss :# ss + es)
>     where ss = scan1 (es + os)


Testing
=======

> mkT :: IsNat n => [a] -> T n a
> mkT = mk' nat
>  where
>    mk' :: Nat m -> [a] -> T m a
>    mk' _ []        = error "mk': empty list"
>    mk' Zero [a]    = ZeroC a
>    mk' (Succ m) xs = SuccC (mk' m (pairs xs))

The utility function `pairs` coalesces adjacent list elements into explicit pairs.

> pairs :: [a] -> [Pair a]
> pairs []       = []
> pairs (a:b:cs) = (a :# b) : pairs cs
> pairs ([_])    = error "pairs: odd-length list."

Use `printT` to try out the following examples.
I haven't yet worked out a good `Show` instance for `(f :^ n) a`.

> showT :: Show a => T n a -> String
> showT (ZeroC a ) = show  a
> showT (SuccC as) = showT (fmap unpair as)

> printT :: Show a => T n a -> IO ()
> printT = putStrLn . showT

> t0 :: T Z Int
> t0 = mkT [3]
>
> t1 :: T OneT Int
> t1 = mkT [3,4]
>
> t4 :: T FourT Int
> t4 = mkT [1..16]
>
> t4' :: T FourT Int
> t4' = scan1 t4


Understanding in-place algorithms
=================================

How can we shift from a functional algorithm toward one that updates its argument in place?
Look again at the functional version:

< scan1 :: Num a => Unop (T n a)
< scan1 = inC (const 0) (inInvert h)
<  where
<    h (es :# os) = (ss :# ss + es)
<     where ss = scan1 (es + os)

To derive an in-place algorithm, let's look carefully at what storage can be recycled when.
Assume that somehow the container inversions are conceptual only, with no data actually being moved.
After adding `es` and `os` (evens & odds), we'll still `es` (for later `ss+es`), but we won't need `os`.
Also, `ss` and `os` have the same size.
Together, these properties mean that `ss` can overwrite `os`.

Similarly, `ss+es` has the same length as `es`, and that sum is the last use of `es`, so `ss+es` can overwrite `es`.

To leave the evens in place and update the odds, we can simply replace each consecutive `(e,o)` pair with `(e,e+o)`.
Then perform the recursive scan on just the seconds of these pairs, leaving the `evens` untouched.
The result corresponds to `invert (es :# ss)`, so we'll want to replace each consecutive `(e :# s)` pair with `(s :# s+e)`.

The modified `SuccC` case:

> scan2 :: Num a => Unop (T n a)

< scan2 = inC (const 0) (fmap after . seconds scan2 . fmap before)

More succinctly:

> scan2 = inC (const 0) (around (seconds scan2))

> before, after :: Num a => Unop (Pair a)
> before (e :# o) = (e :# e+o)
> after  (e :# s) = (s :# s+e)

> around :: (Functor f, Num a) => f (Pair a) :-+> f (Pair a)
> around = before ~>* after

For a more formal derivation, see my notes from 2011-02-08.

This example illustrates an approach to synthesizing in-place algorithms.
Express the algorithms in terms of `Unop` pipelines.
For parallelism, use `fmap`.

Next I want to eliminate `seconds`, with its implied structural inversions.

Trees within trees
------------------

Another whack: place right-folded trees inside of left-folded trees.

> type RBits m = R.Vec m Bit
>
> type RT m = Trie (RBits m)

We'll want to wrap and unwrap the inner right-folded trees:

> inRZeroCs :: Functor g => g (RT Z a) :-+> g a
> inRZeroCs = R.ZeroC ~>* R.unZeroC

> inRSuccCs :: (Functor g, IsNat n) =>
>              g ((f R.:^ (S n)) a) :-+> g (f ((f R.:^ n) a))
> inRSuccCs = R.SuccC ~>* R.unSuccC


> scan3 :: Num a => Unop (T n a)
> scan3 = inRZeroCs scan3'

> scan3' :: (IsNat m, Num a) => Unop (T n (RT m a))
> scan3' = inC (rightmost (const 0)) (around3 (middle3))

> before3, after3 :: (IsNat m, Num a) => Unop (Pair (RT m a))
> before3 = twoRights before
> after3  = twoRights after

> around3 :: (Functor f, IsNat m, Num a) => f (Pair (RT m a)) :-+> f (Pair (RT m a))
> around3 = before3 ~>* after3

> middle3 :: (IsNat m, Num a) => Unop (T n (Pair (RT m a)))
> middle3 = inRSuccCs scan3'

Test it:

< *TreeScan> printT t4
< ((((1,2),(3,4)),((5,6),(7,8))),(((9,10),(11,12)),((13,14),(15,16))))
< *TreeScan> printT (scan1 t4)
< ((((0,1),(3,6)),((10,15),(21,28))),(((36,45),(55,66)),((78,91),(105,120))))
< *TreeScan> printT (scan2 t4)
< ((((0,1),(3,6)),((10,15),(21,28))),(((36,45),(55,66)),((78,91),(105,120))))
< *TreeScan> printT (scan3 t4)
< ((((0,1),(3,6)),((10,15),(21,28))),(((36,45),(55,66)),((78,91),(105,120))))

Let's take another whack, use `up` and `down` from `NavigateTree`.
Drop `inC`, and work always at the level of these left/right hybrid trees.
Instead of `inC`, make `n` explicit as a typed number.

> scan4 :: (IsNat n, Num a) => Unop (T n a)
> scan4 = inRZeroCs (scan4' nat)

> scan4' :: (IsNat m, Num a) => Nat n -> Unop (T n (RT m a))
> scan4' Zero      = inZeroC (rightmost (const 0))
> scan4' (Succ n') = (inSuccC . around4) (middle4 n')

> before4, after4 :: (IsNat m, Num a) => Unop (Pair (RT m a))
> before4 = twoRights before
> after4  = twoRights after

> around4 :: (Functor f, IsNat m, Num a) => f (Pair (RT m a)) :-+> f (Pair (RT m a))
> around4 = before4 ~>* after4

> middle4 :: (IsNat m, Num a) => Nat n -> Unop (T n (Pair (RT m a)))
> middle4 n = inRSuccCs (scan4' n)

Next, shift the formulation to use `up` and `down`, hiding the trees of pairs.

> scan5 :: (IsNat n, Num a) => Unop (T n a)
> scan5 = inRZeroCs (scan5' nat)

> scan5' :: (IsNat m, Num a) => Nat n -> Unop (T n (RT m a))
> scan5' Zero      = inZeroC (rightmost (const 0))
> scan5' (Succ n') = (inUp . around5) (scan5' n')

> before5, after5 :: (IsNat m, Num a) => Unop (RT (S m) a)
> before5 = R.inSuccC before4
> after5  = R.inSuccC after4

> around5 :: (Functor f, IsNat m, Num a) => f (RT (S m) a) :-+> f (RT (S m) a)
> around5 = before5 ~>* after5

