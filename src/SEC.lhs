 <!-- -*- markdown -*-

> {-# LANGUAGE TypeOperators #-}
> {-# OPTIONS_GHC -Wall #-}

|
Module      :  SEC
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

Semantic editor combinators

> module SEC ((~>),(~>*), Unop, (:-+>), dist, inDist) where

> import Prelude hiding ((.))
> import Control.Applicative (Applicative(..))
> import Data.Traversable
> import Control.Category (Category(..))

 -->

 <!-- references -->

[*Semantic editor combinators*]: http://conal.net/blog/posts/semantic-editor-combinators/ "blog post"

 <!-- -->


Some semantic editor combinators
================================

Type-preserving editor:

> type Unop a = a -> a

A type-preserving [*Semantic editor combinator*] (SEC):

> type p :-+> q = Unop p -> Unop q

Handy for SEC definitions:

> infixr 1 ~>
> (~>) :: Category (-->) =>
>         (a' --> a) -> (b --> b') -> ((a --> b) -> (a' --> b'))
> (f ~> h) g = h . g . f

 <!--[
Like `second` but on function types:

< result :: (b -> b') -> ((a -> b) -> (a -> b'))
< result = (.)

 ]-->

Another version under a functor.
Look for a more systematic approach.

> infixr 1 ~>*
> (~>*) :: Functor f => (a -> b) -> (c -> d) -> (f b -> f c) -> (f a -> f d)
> f ~>* g = fmap f ~> fmap g


A synonym 

> dist :: (Traversable f, Applicative g) => f (g a) -> g (f a)
> dist = sequenceA

> inDist :: (Traversable g, Applicative f, Traversable f, Applicative g) =>
>           f (g a) :-+> g (f a)
> inDist = dist ~> dist

