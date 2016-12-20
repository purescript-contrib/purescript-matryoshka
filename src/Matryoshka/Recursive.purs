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

module Matryoshka.Recursive where

import Prelude

import Control.Comonad (class Comonad, duplicate, extract)
import Control.Comonad.Cofree (Cofree)
import Control.Comonad.Env.Trans (EnvT)

import Data.Functor.Mu (Mu, unroll)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..))
import Matryoshka.Algebra (Algebra, AlgebraM, ElgotAlgebra, GAlgebra, GAlgebraM)
import Matryoshka.DistributiveLaw (DistributiveLaw, distGHisto, distHisto, distZygo, distZygoT)

class Functor f ⇐ Recursive t f | t → f where
  project ∷ t → f t

instance recursiveMu ∷ Functor f ⇒ Recursive (Mu f) f where
  project = unroll

cata ∷ ∀ f t a. Recursive t f ⇒ Algebra f a → t → a
cata f = go
  where
  go t = f $ map go $ project t

cataM
  ∷ ∀ f t m a
  . (Recursive t f, Monad m, Traversable f)
  ⇒ AlgebraM m f a
  → t
  → m a
cataM f = go
  where
  go t = f =<< traverse go (project t)

gcata
  ∷ ∀ f t w a
  . (Recursive t f, Comonad w)
  ⇒ DistributiveLaw f w
  → GAlgebra w f a
  → t
  → a
gcata k g = g <<< extract <<< go
  where
  go t = k $ map (duplicate <<< map g <<< go) (project t)

elgotCata
  ∷ ∀ f t w a
  . (Recursive t f, Comonad w)
  ⇒ DistributiveLaw f w
  → ElgotAlgebra w f a
  → t
  → a
elgotCata k g = g <<< go
  where
  go t = k $ map (map g <<< duplicate <<< go) (project t)

para ∷ ∀ f t a. Recursive t f ⇒ GAlgebra (Tuple t) f a → t → a
para f = go
  where
  go ∷ t → a
  go t = f (g <$> project t)
  g ∷ t → Tuple t a
  g t = Tuple t (go t)

elgotPara ∷ ∀ f t a. Recursive t f ⇒ ElgotAlgebra (Tuple t) f a → t → a
elgotPara f = go
  where
  go t = f (Tuple t (go <$> project t))

paraM
  ∷ ∀ f t m a
  . (Recursive t f, Monad m, Traversable f)
  ⇒ GAlgebraM (Tuple t) m f a
  → t
  → m a
paraM f = go
  where
  go t = f =<< traverse (map (Tuple t) <<< go) (project t)

zygo
  ∷ ∀ f t a b
  . Recursive t f
  ⇒ Algebra f b
  → GAlgebra (Tuple b) f a
  → t
  → a
zygo = gcata <<< distZygo

elgotZygo
  ∷ ∀ f t a b
  . Recursive t f
  ⇒ Algebra f b
  → ElgotAlgebra (Tuple b) f a
  → t
  → a
elgotZygo = elgotCata <<< distZygo

gzygo
  ∷ ∀ f t w a b
  . (Recursive t f, Comonad w)
  ⇒ Algebra f b
  → DistributiveLaw f w
  → GAlgebra (EnvT b w) f a
  → t
  → a
gzygo f w = gcata (distZygoT f w)

gElgotZygo
  ∷ ∀ f t w a b
  . (Recursive t f, Comonad w)
  ⇒ Algebra f b
  → DistributiveLaw f w
  → ElgotAlgebra (EnvT b w) f a
  → t
  → a
gElgotZygo f w = elgotCata (distZygoT f w)

mutu
  ∷ ∀ f t a b
  . Recursive t f
  ⇒ GAlgebra (Tuple a) f b
  → GAlgebra (Tuple b) f a
  → t
  → a
mutu f g = g <<< map go <<< project
  where
  go x = Tuple (mutu g f x) (mutu f g x)

histo
  ∷ ∀ f t a
  . Recursive t f
  ⇒ GAlgebra (Cofree f) f a
  → t
  → a
histo = gcata distHisto

elgotHisto
  ∷ ∀ f t a
  . Recursive t f
  ⇒ ElgotAlgebra (Cofree f) f a
  → t
  → a
elgotHisto = elgotCata distHisto

ghisto
  ∷ ∀ f t h a
  . (Recursive t f, Functor h)
  ⇒ DistributiveLaw f h
  → GAlgebra (Cofree h) f a
  → t
  → a
ghisto g = gcata (distGHisto g)
