 <!-- -*- markdown -*-

|
Module      :  ShowF
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

Showable functors

> module ShowF where

> class ShowF f where showF :: Show a => f a -> String


