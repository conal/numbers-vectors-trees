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
 <!-- -->


Introduction
============

We'll be using perfect binary trees indexed by binary numbers (bit sequences).

> type Bit     = BNat TwoT
> type Bits  n = Vec n Bit

< type BTree n = Trie (Bits n)
<              = Trie (Vec n Bit)
<              = Trie Bit :^ n
<              = Trie (BNat TwoT) :^ n
<              = Vec TwoT :^ n

> type BTree n = Pair :^ n

> showT :: Show a => BTree n a -> String
> showT (ZeroC a ) = show a
> showT (SuccC as) = showT as

> printT :: Show a => BTree n a -> IO ()
> printT = putStrLn . showT

For now, this module is light on commentary.
To do: extract from the other module I started (without size-typing).

If the generality of `Vec` leads to inconvenient notation, then maybe use a specialized definitions.
I'd like the general form to work, so I'm trying it first.

Start with a functional algorithm exclusive scan based on Guy Blelloch's.
Use a *left-folded* binary tree to make it easy to access consecutive pairs (even/odd).

> type Unop a = a -> a

> type Pair = Vec TwoT

> sumPairs :: Num a => BTree n (Pair a) -> BTree n a
> sumPairs = fmap sum

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
>    s = scan (e + o)

> mkBTree :: IsNat n => [a] -> BTree n a
> mkBTree = mk' nat

> mk' :: Nat n -> [a] -> BTree n a
> mk' _ []        = error "mk': empty list"
> mk' Zero [a]    = ZeroC a
> mk' (Succ m) xs = SuccC (mk' m (pairs xs))

The utility function `pairs` coalesces adjacent list elements into explicit pairs.

> pairs :: [a] -> [Pair a]
> pairs []       = []
> pairs (a:b:cs) = pair (a,b) : pairs cs
> pairs ([_])    = error "pairs: odd-length list."

Use `printT` to try out the following examples.
I don't yet have a good `Show` for `(f :^ n) a`.

> t0 :: BTree Z Int
> t0 = mkBTree [3]

> t1 :: BTree OneT Int
> t1 = mkBTree [3,4]

> t4 :: BTree FourT Int
> t4 = mkBTree [1..16]

> t4' :: BTree FourT Int
> t4' = scan t4

