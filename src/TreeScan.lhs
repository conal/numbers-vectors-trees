 <!-- -*- markdown -*-

> {-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators, Rank2Types #-}

> {-# OPTIONS_GHC -Wall #-}
> {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
> {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-} -- temporary, pending ghc/ghci fix


|
Module      :  TreeScan
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

> module TreeScan where

> import Prelude hiding (sum,zip,unzip)
> import Data.Foldable (sum,toList)
> import Data.Traversable (Traversable(..))
> import Control.Applicative (Applicative(..),liftA2)
> import Control.Arrow (first,second,(&&&))

> import FunctorCombo.StrictMemo

> import Nat

> import Left
> import LeftNum
> import Pair

 -->

 <!-- references -->

[*From tries to trees*]: http://conal.net/blog/posts/from-tries-to-trees/ "blog post"

[*Programming parallel algorithms*]: http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.53.5739 "Paper by Guy Blelloch, 1990"

[*Semantic editor combinators*]: http://conal.net/blog/posts/semantic-editor-combinators/ "blog post"

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

This algorithm assumes the array size is a power of two, so that each "uninterleaving" yields the same number of even as odd elements.
I want to capture this power-of-two assumption statically.
As mentioned in [*From tries to trees*], perfect binary trees (with values at leaves) of depth $n$ have $2^n$ elements and can be statically depth-typed.
Moreover, as shown in [*A trie for length-typed vectors*], such trees naturally arise as the trie functors for size-typed vectors of bits.
A bit can represented as the type of natural numbers less than two, as in [*Type-bounded numbers*], but for notational convenience I'll use a specialized `Bit` type and `Pair` functor.

> type Bits  n = Vec n Bit
>
> type BTree n = Trie (Bits n)

Equivalently,

< type BTree n = Trie (Bits n)
<              = Trie (Vec n Bit)
<              = Trie Bit :^ n
<              = Pair :^ n

where `f :^ n` is the $n$-ary composition of the functor `f` with itself.

For now, this module is light on commentary.
To do: extract prose from the other module I started (without size-typing).
Or update that module and refer to it here, focusing remarks on changes.

If the generality of `Vec` leads to inconvenient notation, then maybe use a specialized definitions.
I'd like the general form to work, so I'm trying it first.

Start with a functional algorithm exclusive scan based on Guy Blelloch's.
Use a *left-folded* binary tree to make it easy to access consecutive pairs (even/odd).

Abstract out the general recursion pattern on `BTree`:

> btree :: (a -> c) -> (forall n. IsNat n => BTree n (Pair a) -> c)
>       -> (forall n. BTree n a -> c)
> btree l _ (ZeroC a ) = l a
> btree _ b (SuccC as) = b as

Specialize to type-preserving tree transformations (tree endomorphisms):

> inT :: Unop a -> (forall n. IsNat n => Unop (BTree n (Pair a)))
>     -> (forall n. Unop (BTree n a))
> inT l _ (ZeroC a ) = (ZeroC . l) a
> inT _ b (SuccC as) = (SuccC . b) as

I'd rather write

< inT l b = btree (ZeroC . l) (SuccC . b)

but GHC 6.12.3 gives me this error message:

    Couldn't match expected type `Z' against inferred type `S n'
      Expected type: (:^) Pair Z a
      Inferred type: (:^) Pair (S n) a
    In the second argument of `btree', namely `(SuccC . b)'
    In the expression: btree (ZeroC . l) (SuccC . b)

I think the conflict here is that `c` must match `Z` in the first argument of `btree` but `S n` in the second.

Pairing and unpairing
=====================

Type-preserving editor:

> type Unop a = a -> a

A type-preserving [*Semantic editor combinator*]:

> type p :-+> q = Unop p -> Unop q

Question: is `(:-+>)` an `Arrow` (assuming it were `newtype`-wrapped)?

Start with some convenience for converting between standard pairs and 2-vectors:

> type Pair' a = (a,a)

> pair :: Pair' a -> Pair a
> pair (a,b) = (a :# b)

> unpair :: Pair a -> Pair' a
> unpair (a :# b) = (a , b)

> inPair' :: Pair' a :-+> Pair a
> inPair' = unpair ~> pair

> infixr 1 ~>
> (~>) :: (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
> (f ~> h) g = h . g . f

More generally,

< (~>) :: Category (-->) =>
<         (a' --> a) -> (b --> b') -> ((a --> b) -> (a' --> b'))

> inSequenceA :: (Traversable g, Applicative f, Traversable f, Applicative g) =>
>                f (g a) :-+> g (f a)
> inSequenceA = sequenceA ~> sequenceA

And another, on collections:

> inPairs' :: Functor f => f (Pair' a) :-+> f (Pair a)
> inPairs' = fmap unpair ~> fmap pair


To separate out and later recombine the evens and odds:

> uninterleave :: BTree n (Pair a) -> Pair' (BTree n a)
> uninterleave = unpair . sequenceA

> interleave :: IsNat n => Pair' (BTree n a) -> BTree n (Pair a)
> interleave = sequenceA . pair

< inUninterleave :: IsNat n => Pair' (BTree n a) :-+> BTree n (Pair a)
< inUninterleave = uninterleave ~> interleave

Better:

> inUninterleave :: IsNat n => Pair' (BTree n a) :-+> BTree n (Pair a)
> inUninterleave = inSequenceA . inPair'

And counterparts to `first` and `second`:

> firstP, secondP :: a :-+> Pair a
> firstP  = inPair' . first
> secondP = inPair' . second

Also handy:

> zip :: Applicative f => (f a, f b) -> f (a,b)
> zip = uncurry (liftA2 (,))

> unzip :: Functor f => f (a,b) -> (f a, f b)
> unzip = fmap fst &&& fmap snd

> inZip :: Applicative f => f (a,b) :-+> (f a, f b)
> inZip = zip ~> unzip

> inUnzip :: Applicative f => (f a, f b) :-+> f (a,b)
> inUnzip = unzip ~> zip

> seconds :: Applicative f => f b :-+> f (a,b)
> seconds = inUnzip . second

In particular,

< inUnzip :: BTree n (Pair' a) :-+> Pair' (BTree n a)

< inUnzipT :: Pair' (BTree n a) :-+> BTree n (Pair a)
< inUnzipT h t = 

Scan
====

< scan1 :: Num a => Unop (BTree n a)
< scan1 (ZeroC _ ) = ZeroC 0
< scan1 (SuccC as) = SuccC (interleave (ss,ss + es))
<  where
<    (es,os) = uninterleave as
<    ss      = scan1 (es + os)

Factor out the uninterleaving & interleaving:

< scan1 :: Num a => Unop (BTree n a)
< scan1 (ZeroC _ ) = ZeroC 0
< scan1 (SuccC as) = SuccC (inUninterleave h as)
<  where
<    h (es,os) = (ss,ss + es)
<     where ss = scan1 (es + os)

And then use `inT` for the tree transformation pattern:

> scan1 :: Num a => Unop (BTree n a)
> scan1 = inT (const 0) (inUninterleave h)
>  where
>    h (es,os) = (ss,ss + es)
>     where ss = scan1 (es + os)



Testing
=======

> mkBTree :: IsNat n => [a] -> BTree n a
> mkBTree = mk' nat
>  where
>    mk' :: Nat m -> [a] -> BTree m a
>    mk' _ []        = error "mk': empty list"
>    mk' Zero [a]    = ZeroC a
>    mk' (Succ m) xs = SuccC (mk' m (pairs xs))

The utility function `pairs` coalesces adjacent list elements into explicit pairs.

> pairs :: [a] -> [Pair a]
> pairs []       = []
> pairs (a:b:cs) = pair (a,b) : pairs cs
> pairs ([_])    = error "pairs: odd-length list."

Use `printT` to try out the following examples.
I haven't yet worked out a good `Show` instance for `(f :^ n) a`.

> showT :: Show a => BTree n a -> String
> showT (ZeroC a ) = show  a
> showT (SuccC as) = showT (fmap unpair as)

> printT :: Show a => BTree n a -> IO ()
> printT = putStrLn . showT

> t0 :: BTree Z Int
> t0 = mkBTree [3]

> t1 :: BTree OneT Int
> t1 = mkBTree [3,4]

> t4 :: BTree FourT Int
> t4 = mkBTree [1..16]

> t4' :: BTree FourT Int
> t4' = scan1 t4


Understanding in-place algorithms
=================================

How can we shift from a functional algorithm toward one that updates its argument in place?
Look again at the functional version:

< scan1 :: Num a => Unop (BTree n a)
< scan1 = inT (const 0) (inUninterleave h)
<  where
<    h (es,os) = (ss,ss + es)
<     where ss = scan1 (es + os)

To derive an in-place algorithm, let's look carefully at what storage can be recycled when.
Assume that somehow the uninterleaving and interleaving is conceptual only, with no data actually being moved.
After adding `es` and `os` (evens & odds), we'll still `es` (for later `ss+es`), but we won't need `os`.
Also, `ss` and `os` have the same size.
Together, these properties mean that `ss` can overwrite `os`.

Similarly, `ss+es` has the same length as `es`, and that sum is the last use of `es`, so `ss+es` can overwrite `es`.

To leave the evens in place and update the odds, we can simply replace each consecutive `(e,o)` pair with `(e,e+o)`.
Then perform the recursive scan on just the seconds of these pairs, leaving the `evens` untouched.
The result corresponds to `interleave (es,ss)`, so we'll want to replace each consecutive `(e,s)` pair with `(s,s+e)`.

The modified `SuccC` case:

> scan2 :: Num a => Unop (BTree n a)
> scan2 = inT (const 0) (inPairs' (after . seconds scan2 . before))

> before, after :: (Functor f, Num a) => Unop (f (Pair' a))
> before = fmap (\ (e,o) -> (e,e+o))
> after  = fmap (\ (e,s) -> (s,s+e))

Define a slightly more specialized variant of `inT`:

> inT' :: Unop a -> (forall n. IsNat n => Unop (BTree n (Pair' a)))
>      -> (forall n. Unop (BTree n a))
> inT' l b = inT l (inPairs' b)

We're left with a simple definition:

< scan2 = inT' (const 0) (after . seconds scan2 . before)

This example illustrates an approach to synthesizing in-place algorithms.
Express the algorithms in terms of `Unop` pipelines.
For parallelism, use `fmap`.

Next I want to eliminate `seconds`, with its implied unzipping & zipping.

Flattening the recursion
========================

Expand `scan2` once in the context of its own definition:

< seconds (inT' (const 0) (after . seconds scan2 . before))


< seconds (inT (const 0) (inPairs' (after . seconds scan2 . before)))

Consider the two cases of `inT`

< inT l _ (ZeroC a ) = (ZeroC . l) a
< inT _ b (SuccC as) = (SuccC . b) as

< seconds = inUnzip . second

<   seconds (inT (const 0) (...)) (ZeroC (a,b) )

< == inUnzip (second scan) (inT (const 0) (...)) (ZeroC (a,b) )

< == (zip . second scan . unzip) (inT (const 0) (...)) (ZeroC (a,b) )

< == zip (second scan (unzip (inT (const 0) (...)) (ZeroC (a,b) )



< inT (seconds . const 0) (seconds . inPairs' (after . seconds scan2 . before))


Hm.
Back up to the definition of seconds:

< seconds :: Applicative f => f b :-+> f (a,b)
< seconds = inUnzip . second

< inUnzip :: Applicative f => (f a, f b) :-+> f (a,b)
< inUnzip = unzip ~> zip

I suspect there's a nice law to rewrite `seconds (fmap f)`

< seconds . fmap == fmap . second

< secondsFmap :: Applicative f => b :-+> f (a,b)
< secondsFmap = fmap . second

<   seconds . seconds . fmap
< == seconds . fmap . second
< == fmap . second . second

Maybe think about trees of trees instead of trees of pairs.

< unB :: T (S n) (T m a) -> T n (T (S m)) a
< unB (SuccB t) = ...

Hm. I think I want $1+m$, but I have $m+1$.
This operation would be much easier with right-folded composition.

< SuccC :: T (S n) (T m a) -> T n (Pair (T m a))

< bubble :: (f :^ m) (f a) -> (f :^ S m) a
< bubble (ZeroC fa ) = SuccC (ZeroC fa)

fa :: f a
ZeroC fa :: T Z (f a)
SuccC (ZeroC fa) :: T (S Z) a

fas :: T (S m) (f (f a))

Oh! Use two different tree types.
