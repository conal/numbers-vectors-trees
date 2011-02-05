 <!-- -*- markdown -*-

> {-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators #-}

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

> import Prelude hiding (sum)
> import Data.Foldable (sum,toList)
> import Data.Traversable (sequenceA)

> import FunctorCombo.StrictMemo

> import TNat
> import Nat

> import Left
> import LeftNum

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

This algorithm assumes the array size is a power of two, so that each "uninterleaving" yields the same number of even as odd elements.
I want to capture this power-of-two assumption statically.
As mentioned in [*From tries to trees*], perfect binary trees (with values at leaves) of depth $n$ have $2^n$ elements and can be statically depth-typed.
Moreover, as shown in [*A trie for length-typed vectors*], such trees naturally arise as the trie functors for size-typed vectors of bits.
A bit can represented as the type of natural numbers less than two, as in [*Type-bounded numbers*].

> type Bit     = BNat TwoT
> type Bits  n = Vec n Bit

> type Pair = Vec TwoT -- == Trie Bit

< type BTree n = Trie (Bits n)
<              = Trie (Vec n Bit)
<              = Trie Bit :^ n
<              = Trie (BNat TwoT) :^ n
<              = Vec TwoT :^ n

where `f :^ n` is the $n$-ary composition of the functor `f` with itself, and `n` is a type-encoded natural unber.
Because of what I think is a bug in ghc 6.12.3, I'll use this last form.

> type BTree n = Pair :^ n

For now, this module is light on commentary.
To do: extract from the other module I started (without size-typing).

If the generality of `Vec` leads to inconvenient notation, then maybe use a specialized definitions.
I'd like the general form to work, so I'm trying it first.

Start with a functional algorithm exclusive scan based on Guy Blelloch's.
Use a *left-folded* binary tree to make it easy to access consecutive pairs (even/odd).

> type Unop a = a -> a

> type Pair' a = (a,a)

> pair :: Pair' a -> Pair a
> pair (a,b) = ZVec :> a :> b

> unpair :: Pair a -> Pair' a
> unpair (ZVec :> a :> b) = (a,b)

> uninterleave :: BTree n (Pair a) -> Pair' (BTree n a)
> uninterleave = unpair . sequenceA

> interleave :: IsNat n => Pair' (BTree n a) -> BTree n (Pair a)
> interleave = sequenceA . pair



> scan :: Num a => Unop (BTree n a)
> scan (ZeroC _ ) = ZeroC 0
> scan (SuccC as) = SuccC (interleave (s,s + e))
>  where
>    (e,o) = uninterleave as
>    s     = scan (e + o)

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
> showT (ZeroC a ) = show a
> showT (SuccC as) = showT as

> printT :: Show a => BTree n a -> IO ()
> printT = putStrLn . showT

> t0 :: BTree Z Int
> t0 = mkBTree [3]

> t1 :: BTree OneT Int
> t1 = mkBTree [3,4]

> t4 :: BTree FourT Int
> t4 = mkBTree [1..16]

> t4' :: BTree FourT Int
> t4' = scan t4

