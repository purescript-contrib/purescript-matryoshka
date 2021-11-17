{-
Copyright 2016 SlamData, Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-}

module Matryoshka.DistributiveLaw where

import Prelude

import Control.Comonad (class Comonad, extract)
import Control.Comonad.Cofree (Cofree, unfoldCofree, tail)
import Control.Comonad.Env.Trans (EnvT(..), runEnvT)
import Control.Comonad.Trans.Class (lower)
import Control.Monad.Except (ExceptT(..), runExceptT)
import Control.Monad.Free (Free, liftF, resume)

import Data.Distributive (class Distributive, distribute)
import Data.Either (Either(..), either)
import Data.Identity (Identity)
import Data.Newtype (unwrap, wrap)
import Data.Traversable (class Traversable, sequence)
import Data.Tuple (Tuple(..), fst, snd)

import Matryoshka.Algebra (Algebra)
import Matryoshka.Class.Corecursive (class Corecursive, embed)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Coalgebra (Coalgebra)

type DistributiveLaw f g = forall a. f (g a) -> g (f a)

distApplicative :: forall f g. Traversable f => Applicative g => DistributiveLaw f g
distApplicative = sequence

distDistributive :: forall f g. Traversable f => Distributive g => DistributiveLaw f g
distDistributive = distribute

distCata :: forall f. Functor f => DistributiveLaw f Identity
distCata = wrap <<< map unwrap

distPara :: forall t f. Corecursive t f => DistributiveLaw f (Tuple t)
distPara = distZygo embed

distParaT
  :: forall t f w
   . Corecursive t f
  => Comonad w
  => DistributiveLaw f w
  -> DistributiveLaw f (EnvT t w)
distParaT = distZygoT embed

distZygo :: forall f a. Functor f => Algebra f a -> DistributiveLaw f (Tuple a)
distZygo g m = Tuple (g (map fst m)) (map snd m)

distZygoT
  :: forall f w a
   . Functor f
  => Comonad w
  => Algebra f a
  -> DistributiveLaw f w
  -> DistributiveLaw f (EnvT a w)
distZygoT g k fe =
  EnvT $ Tuple (g (fst <<< runEnvT <$> fe)) (k (lower <$> fe))

distHisto :: forall f. Functor f => DistributiveLaw f (Cofree f)
distHisto = distGHisto identity

distGHisto
  :: forall f h
   . Functor f
  => Functor h
  => DistributiveLaw f h
  -> DistributiveLaw f (Cofree h)
distGHisto k = unfoldCofree (map extract) (k <<< map tail)

distAna :: forall f. Functor f => DistributiveLaw Identity f
distAna = map wrap <<< unwrap

distApo :: forall t f. Recursive t f => DistributiveLaw (Either t) f
distApo = distGApo project

distGApo :: forall f a. Functor f => Coalgebra f a -> DistributiveLaw (Either a) f
distGApo f = either (map Left <<< f) (map Right)

distGApoT
  :: forall f m a
   . Functor f
  => Functor m
  => Coalgebra f a
  -> DistributiveLaw m f
  -> DistributiveLaw (ExceptT a m) f
distGApoT g k = map ExceptT <<< k <<< map (distGApo g) <<< runExceptT

distFutu :: forall f. Functor f => DistributiveLaw (Free f) f
distFutu = distGFutu identity

distGFutu
  :: forall f h
   . Functor f
  => Functor h
  => DistributiveLaw h f
  -> DistributiveLaw (Free h) f
distGFutu k f = case resume f of
  Left as -> join <<< liftF <$> k (distGFutu k <$> as)
  Right b -> pure <$> b
