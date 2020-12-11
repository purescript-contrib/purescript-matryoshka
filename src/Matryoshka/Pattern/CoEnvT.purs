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

-- | The pattern functor for `Free`. This is not `Reader`, it's the dual of
-- | `EnvT` in the sense that it uses a coproduct (`Either`) rather than a
-- | product (`Tuple`).
module Matryoshka.Pattern.CoEnvT where

import Prelude

import Data.Either (Either)
import Data.Newtype (class Newtype)
import Data.Bifunctor (lmap)

newtype CoEnvT :: Type -> (Type -> Type) -> Type -> Type
newtype CoEnvT e m a = CoEnvT (Either e (m a))

runEnvT ∷ ∀ e m a. CoEnvT e m a → Either e (m a)
runEnvT (CoEnvT x) = x

withEnvT ∷ ∀ e1 e2 m a. (e1 → e2) → CoEnvT e1 m a → CoEnvT e2 m a
withEnvT f (CoEnvT e) = CoEnvT (lmap f e)

mapEnvT ∷ ∀ e m1 m2 a b. (m1 a → m2 b) → CoEnvT e m1 a → CoEnvT e m2 b
mapEnvT f (CoEnvT e) = CoEnvT (map f e)

derive instance newtypeEnvT ∷ Newtype (CoEnvT e m a) _

instance functorEnvT ∷ Functor m ⇒ Functor (CoEnvT e m) where
  map f (CoEnvT e) = CoEnvT (map (map f) e)
