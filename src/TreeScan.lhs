 <!-- -*- markdown -*-

> {-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators, Rank2Types #-}

> {-# OPTIONS_GHC -Wall #-}
> {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-} -- temporary, pending ghc/ghci fix


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
As mentioned in [*From tries to trees*], perfect binary trees (with values at leaves) of depth $n$ have $2^n$ elements and can be statically depth-typed.
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
> scan2 = inC (const 0) (after . seconds scan2 . before)

> before, after :: (Functor f, Num a) => Unop (f (Pair a))
> before = fmap (\ (e :# o) -> (e :# e+o))
> after  = fmap (\ (e :# s) -> (s :# s+e))

For a more formal derivation, see my notes from 2011-02-08.

This example illustrates an approach to synthesizing in-place algorithms.
Express the algorithms in terms of `Unop` pipelines.
For parallelism, use `fmap`.

Next I want to eliminate `seconds`, with its implied structural inversions.

Flattening the recursion
========================

Expand `scan2` once in the context of its own definition:

< seconds (inC (const 0) (after . seconds scan2 . before))

< seconds = inInvert . second

<   (seconds scan) t
< == inInvert (second scan) t
< == (invert . second scan . invert) t
< == invert (second scan (invert t))

Consider the two cases of `inC`

< inC l _ (ZeroC a ) = (ZeroC . l) a
< inC _ b (SuccC as) = (SuccC . b) as

First case: `t = Zero (a,b)` for some `a` and `b`:

< seconds scan t
< seconds scan (Zero (a,b))
< seconds (inC (const 0) (...)) (ZeroC (a,b))
< (inInvert . second) (inC (const 0) (...)) (ZeroC (a,b))
< inInvert (second (inC (const 0) (...))) (ZeroC (a,b))
< invert (second (inC (const 0) (...)) (invert (ZeroC (a,b))))
< invert (second (inC (const 0) (...)) (ZeroC a,ZeroC b))
< invert (ZeroC a,(inC (const 0) (...))(ZeroC b))
< invert (ZeroC a,Zero 0)
< ZeroC (a,0)
< fmap (second (const 0)) (ZeroC (a,b))

Second case, `t = Succ t'` for some `t'`.

< seconds scan t
< seconds scan (SuccC t')
< (inInvert . second) scan (SuccC t')
< inInvert (second scan) (SuccC t')
< (invert . second scan . invert) (SuccC t')
< invert (second scan (invert (SuccC t')))

Note that

< invert (SuccC t') = fmap SuccC . invert . fmap invert $ t'

i.e.,

< invert . SuccC = fmap SuccC . invert . fmap invert

So

< invert . second scan . invert . SuccC
< invert . second scan . fmap SuccC . invert . fmap invert


< Succ t' :: T m (Pair a)
< t' :: T m (Pair (Pair a))
< fmap invert $ t' :: T m (Pair (Pair a))
< invert . fmap invert $ t' :: Pair (T m (Pair a))
< fmap SuccC . invert . fmap invert $ t' :: Pair (T (S m) a)
< second scan . fmap SuccC . invert . fmap invert $ t' :: Pair (T (S m) a)
< invert . second scan . fmap SuccC . invert . fmap invert $ t' :: T (S m) (Pair a)

Where to go from here?

Trees within trees
------------------

I know where I'm trying to get to, as in `NavigateTree` and `Extremes`.
Put the pieces together here, and maybe then I'll see how to derive it.

> atDepth :: IsNat n => Nat m -> T n a :-+> T (m :+: n) a
> atDepth Zero      h t = h t
> atDepth (Succ m') h (SuccC t') = SuccC (atDepth m' (seconds h) t')
