 <!-- -*- markdown -*-

> {-# LANGUAGE TypeOperators #-}

> {-# OPTIONS_GHC -Wall #-}

< {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

|
Module      :  Scan
Copyright   :  (c) Conal Elliott 2011
License     :  BSD3
Maintainer  :  conal@conal.net
Stability   :  experimental

A class for scans

> module Scan where

> import Prelude hiding (zip,unzip)

> import Data.Monoid (Monoid(..))
> import Control.Applicative (Applicative,liftA2,(<$>))
> import Control.Arrow ((&&&),first,second)

> import FunctorCombo.Functor

 -->

 <!-- references -->
 <!-- -->

> class Scan f where
>   scanL :: Monoid m => f m -> (f m, m)
>   scanR :: Monoid m => f m -> (m, f m)

> instance Scan Id where
>   scanL (Id m) = (Id mempty, m)
>   scanR (Id m) = (m, Id mempty)

> instance (Scan f, Scan g) => Scan (f :+: g) where
>   scanL (InL fa) = first  InL (scanL fa)
>   scanL (InR ga) = first  InR (scanL ga)
>   scanR (InL fa) = second InL (scanR fa)
>   scanR (InR ga) = second InR (scanR ga)

> instance (Scan f, Scan g, Functor f, Functor g) => Scan (f :*: g) where
>   scanL (fa :*: ga) = (fa' :*: ((af `mappend`) <$> ga'), af `mappend` ag)
>    where (fa',af) = scanL fa
>          (ga',ag) = scanL ga
>   scanR (fa :*: ga) = (af `mappend` ag, ((`mappend` ag) <$> fa') :*: ga')
>    where (af,fa') = scanR fa
>          (ag,ga') = scanR ga

> instance (Scan g, Scan f, Functor f, Applicative g) => Scan (g :. f) where
>   scanL = first (O . fmap adjustL . zip)  -- or O . uncurry (liftA2 (curry adjustL))
>         . assocL
>         . second scanL
>         . unzip
>         . fmap scanL
>         . unO
>   scanR = second (O . fmap adjustR . zip)  -- or O . uncurry (liftA2 (curry adjustL))
>         . assocR
>         . first scanR
>         . unzip
>         . fmap scanR
>         . unO

> unzip :: Functor g => g (a,b) -> (g a, g b)
> unzip = fmap fst &&& fmap snd
>
> zip :: Applicative g => (g a, g b) -> g (a,b)
> zip = uncurry (liftA2 (,))

> assocL :: (a,(b,c)) -> ((a,b),c)
> assocL    (a,(b,c)) =  ((a,b),c)
>
> assocR :: ((a,b),c) -> (a,(b,c))
> assocR    ((a,b),c) =  (a,(b,c))

> adjustL :: (Functor f, Monoid m) => (f m, m) -> f m
> adjustL (ms,m) = (m `mappend`) <$> ms
>
> adjustR :: (Functor f, Monoid m) => (m, f m) -> f m
> adjustR (m,ms) = (`mappend` m) <$> ms

Type-directed derivations:

< gofm                    :: (g :. f) m
< unO                  '' :: g (f m)
< fmap scanL           '' :: g (f m, m)
< unzip                '' :: (g (f m), g m)
< second scanL         '' :: (g (f m), (g m, m))
< assocL               '' :: ((g (f m), g m), m)
< first zip            '' :: (g (f m, m), m)
< first (fmap adjustL) '' :: (g (f m), m)
< first O              '' :: ((g :. f) m, m)
< 
< gofm                     :: (g :. f) m
< unO                   '' :: g (f m)
< fmap scanR            '' :: g (m, f m)
< unzip                 '' :: (g m, g (f m))
< first scanR           '' :: ((m, g m), g (f m))
< assocR                '' :: (m, (g m, g (f m)))
< second zip            '' :: (m, (g (m, f m)))
< second (fmap adjustR) '' :: (m, (g (f m)))
< second O              '' :: (m, ((g :. f) m))

