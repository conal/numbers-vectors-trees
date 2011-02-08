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

> module SEC ((~>), Unop, (:-+>), first, second, result) where

> import Prelude () -- or hiding ((.))
> import Control.Category (Category(..))
> import Control.Arrow (first,second)

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

Like `second` but on function types:

> result :: (b -> b') -> ((a -> b) -> (a -> b'))
> result = (.)

