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

module Matryoshka.Class.Recursive where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail)
import Control.Comonad.Env.Trans (EnvT(..))
import Control.Monad.Free (Free, resume)

import Data.Either (Either(..), either)
import Data.Functor.Mu (Mu, unroll)
import Data.Functor.Nu (Nu, observe)
import Data.Tuple (Tuple(..))

import Matryoshka.Pattern.CoEnvT (CoEnvT(..))

class Functor f ⇐ Recursive t f | t → f where
  project ∷ t → f t

instance recursiveMu ∷ Functor f ⇒ Recursive (Mu f) f where
  project = unroll

instance recursiveNu ∷ Functor f ⇒ Recursive (Nu f) f where
  project = observe

instance recursiveFree ∷ Functor f ⇒ Recursive (Free f a) (CoEnvT a f) where
  project = CoEnvT <<< either Right Left <<< resume

instance recursiveCofree ∷ Functor f ⇒ Recursive (Cofree f a) (EnvT a f) where
  project cf = EnvT $ Tuple (head cf) (tail cf)
