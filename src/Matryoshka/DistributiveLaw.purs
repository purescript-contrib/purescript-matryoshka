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
import Control.Comonad.Trans.Class (lower)
import Control.Comonad.Env.Trans (EnvT(..), runEnvT)
import Control.Comonad.Cofree (Cofree, unfoldCofree, tail)
import Control.Monad.Free (Free, liftF, resume)

import Data.Either (Either(..))
import Data.Identity (Identity)
import Data.Newtype (unwrap, wrap)
import Data.Tuple (Tuple(..), fst, snd)

import Matryoshka.Algebra (Algebra)

type DistributiveLaw f g = ∀ a. f (g a) → g (f a)

distAna ∷ ∀ f. Functor f => DistributiveLaw Identity f
distAna = map wrap <<< unwrap

distCata ∷ ∀ f. Functor f => DistributiveLaw f Identity
distCata = wrap <<< map unwrap

distFutu ∷ ∀ f. Functor f ⇒ DistributiveLaw (Free f) f
distFutu = distGFutu id

distGFutu
  ∷ ∀ f h
  . (Functor f, Functor h)
  ⇒ DistributiveLaw h f
  → DistributiveLaw (Free h) f
distGFutu k f = case resume f of
  Left as → join <<< liftF <$> k (distGFutu k <$> as)
  Right b → pure <$> b

distHisto ∷ ∀ f. Functor f ⇒ DistributiveLaw f (Cofree f)
distHisto = distGHisto id

distGHisto
  ∷ ∀ f h
  . (Functor f, Functor h)
  ⇒ DistributiveLaw f h
  → DistributiveLaw f (Cofree h)
distGHisto k x = unfoldCofree x (map extract) (k <<< map tail)

distZygo ∷ ∀ f a. Functor f ⇒ Algebra f a → DistributiveLaw f (Tuple a)
distZygo g m = Tuple (g (map fst m)) (map snd m)

distZygoT
  ∷ ∀ f w a
  . (Functor f, Comonad w)
  ⇒ Algebra f a
  → DistributiveLaw f w
  → DistributiveLaw f (EnvT a w)
distZygoT g k fe =
  EnvT $ Tuple (g (fst <<< runEnvT <$> fe)) (k (lower <$> fe))
