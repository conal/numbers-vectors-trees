 <!-- -*- markdown -*-

> {-# LANGUAGE TypeOperators #-}

> {-# OPTIONS_GHC -Wall #-}

< {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

|
Module      :  CanScan
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

A class for scans

> module CanScan where

> import Prelude hiding (zip,unzip)

> import Data.Monoid (Monoid(..))
> import Control.Applicative (Applicative,liftA2,(<$>))
> import Control.Arrow ((&&&),first,second)

> import Control.Compose ((:.)(..),unO)

> import Pair (Pair(..))

 -->

 <!-- references -->
 <!-- -->


> class Scan f where
>   scanL :: Monoid m => f m -> (f m, m)
>   scanR :: Monoid m => f m -> (m, f m)

> instance Scan Pair where
>   scanL (a :# b) = ((mempty :# a), a `mappend` b)
>   scanR (a :# b) = (a `mappend` b, (b :# mempty))

> instance (Scan g, Scan f, Functor f, Applicative g) => Scan (g :. f) where
>   scanL = first (O . fmap adjust . zip)  -- or O . uncurry (liftA2 (curry adjust))
>         . assocL
>         . second scanL
>         . unzip
>         . fmap scanL
>         . unO

> unzip :: Functor g => g (a,b) -> (g a, g b)
> unzip = fmap fst &&& fmap snd
>
> zip :: Applicative g => (g a, g b) -> g (a,b)
> zip = uncurry (liftA2 (,))
>
> assocL :: (a,(b,c)) -> ((a,b),c)
> assocL    (a,(b,c)) =  ((a,b),c)

> adjust :: (Functor f, Monoid m) => (f m, m) -> (f m)
> adjust (ms,m) = mappend m <$> ms

Type derivation:

< gofm                   :: (g :. f) m
< unO                 '' :: g (f m)
< fmap scanL          '' :: g (f m, m)
< unzip               '' :: (g (f m), g m)
< second scanL        '' :: (g (f m), (g m, m))
< assocL              '' :: ((g (f m), g m), m)
< first zip           '' :: (g (f m, m), m)
< first (fmap adjust) '' :: (g (f m), m)
< first O             '' :: ((g :. f) m, m)

