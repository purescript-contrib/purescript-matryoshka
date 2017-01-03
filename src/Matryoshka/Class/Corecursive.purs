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

module Matryoshka.Class.Corecursive where

import Prelude

import Control.Comonad.Cofree (Cofree, mkCofree)
import Control.Comonad.Env (EnvT(..))
import Control.Monad.Free (Free, liftF)

import Data.Either (either)
import Data.Functor.Mu (Mu, roll)
import Data.Functor.Nu (Nu, unfold, observe)
import Data.Tuple (Tuple(..))

import Matryoshka.Pattern.CoEnvT (CoEnvT(..))

class Functor f ⇐ Corecursive t f | t → f where
  embed ∷ f t → t

instance corecursiveMu ∷ Functor f ⇒ Corecursive (Mu f) f where
  embed = roll

instance corecursiveNu ∷ Functor f ⇒ Corecursive (Nu f) f where
  embed = flip unfold (map observe)

instance corecursiveFree ∷ Functor f ⇒ Corecursive (Free f a) (CoEnvT a f) where
  embed (CoEnvT e) = either pure (join <<< liftF) e

instance corecursiveCofree ∷ Functor f ⇒ Corecursive (Cofree f a) (EnvT a f) where
  embed et = mkCofree (ask et) (lower et)
    where
    ask (EnvT (Tuple e _)) = e
    lower (EnvT (Tuple _ x)) = x
