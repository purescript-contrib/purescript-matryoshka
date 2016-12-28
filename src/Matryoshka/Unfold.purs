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

module Matryoshka.Unfold where

import Prelude

import Control.Monad.Free (Free, resume)

import Data.Either (Either, either)
import Data.Traversable (class Traversable, traverse)

import Matryoshka.Coalgebra (Coalgebra, CoalgebraM, ElgotCoalgebra, GCoalgebra, GCoalgebraM)
import Matryoshka.Class.Corecursive (class Corecursive, embed)
import Matryoshka.DistributiveLaw (DistributiveLaw, distFutu)

ana ∷ ∀ f t a. Corecursive t f ⇒ Coalgebra f a → a → t
ana f = go
  where
  go a = embed (go <$> f a)

anaM
  ∷ ∀ f t m a
  . (Corecursive t f, Monad m, Traversable f)
  ⇒ CoalgebraM m f a
  → a
  → m t
anaM f = go
  where
  go a = f a >>= (\x -> embed `map` traverse go x)

gana
  ∷ ∀ f t n a
  . (Corecursive t f, Monad n)
  ⇒ DistributiveLaw n f
  → GCoalgebra n f a
  → a
  → t
gana k f = go <<< pure <<< f
  where
  go a = embed $ map (go <<< map f <<< join) (k a)

ganaM
  ∷ ∀ f t m n a
  . (Corecursive t f, Monad m, Monad n, Traversable f, Traversable n)
  ⇒ DistributiveLaw n f
  → GCoalgebraM n m f a
  → a
  → m t
ganaM k f = go <=< map pure <<< f
  where
  go a = embed <$> traverse (go <=< traverse f <<< join) (k a)

elgotAna
  ∷ ∀ f t n a
  . (Corecursive t f, Monad n)
  ⇒ DistributiveLaw n f
  → ElgotCoalgebra n f a
  → a
  → t
elgotAna k f = go <<< f
  where
  go :: n (f a) -> t
  go a = embed $ (go <<< (f =<< _)) <$> k a

apo ∷ ∀ f t a. Corecursive t f ⇒ GCoalgebra (Either t) f a → a → t
apo f = go
  where
  go a = embed $ either id go <$> f a

elgotApo ∷ ∀ f t a. Corecursive t f ⇒ ElgotCoalgebra (Either t) f a → a → t
elgotApo f = go
  where
  go a = either id (embed <<< map go) $ f a

gapo
  ∷ ∀ f t a b
  . Corecursive t f
  ⇒ Coalgebra f b
  → GCoalgebra (Either b) f a
  → a
  → t
gapo f g = go
  where
  go a = embed $ either anaf go <$> g a
  anaf = ana f

apoM
  ∷ ∀ f t m a
  . (Corecursive t f, Monad m, Traversable f)
  ⇒ GCoalgebraM (Either t) m f a
  → a
  → m t
apoM f = go
  where
  go a = embed <$> (traverse (either pure go) =<< f a)

futu ∷ ∀ f t a. Corecursive t f ⇒ GCoalgebra (Free f) f a → a → t
futu = gana distFutu

elgotFutu ∷ ∀ f t a. Corecursive t f ⇒ ElgotCoalgebra (Free f) f a → a → t
elgotFutu = elgotAna distFutu

futuM
  ∷ ∀ f t m a
  . (Corecursive t f, Monad m, Traversable f)
  ⇒ GCoalgebraM (Free f) m f a
  → a
  → m t
futuM f = go
  where
  go a = map embed <<< traverse loop =<< f a
  loop x = either (map embed <<< traverse loop) go (resume x)
