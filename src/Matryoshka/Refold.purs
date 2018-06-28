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

module Matryoshka.Refold where

import Prelude

import Control.Comonad (class Comonad, duplicate, extract)
import Control.Comonad.Cofree (Cofree)
import Control.Monad.Free (Free)

import Data.Identity (Identity(..))
import Data.Newtype (unwrap)
import Data.Profunctor (lcmap)
import Data.Traversable (class Traversable, traverse)

import Matryoshka.Algebra (Algebra, AlgebraM, GAlgebra, GAlgebraM)
import Matryoshka.Class.Corecursive (class Corecursive, embed)
import Matryoshka.Class.Recursive (class Recursive)
import Matryoshka.Coalgebra (Coalgebra, CoalgebraM, GCoalgebra, GCoalgebraM)
import Matryoshka.DistributiveLaw (DistributiveLaw, distAna, distCata, distFutu, distHisto)
import Matryoshka.Fold (cata)
import Matryoshka.Transform (Transform)
import Matryoshka.Util (mapR)

hylo
  ∷ ∀ f a b
  . Functor f
  ⇒ Algebra f b
  → Coalgebra f a
  → a
  → b
hylo f g = go
  where
  go a = f $ go <$> g a

hyloM
  ∷ ∀ f m a b
  . Monad m
  ⇒ Traversable f
  ⇒ AlgebraM m f b
  → CoalgebraM m f a
  → a
  → m b
hyloM f g = go
  where
  go a = f =<< traverse go =<< g a

ghylo
  ∷ ∀ f w n a b
  . Monad n
  ⇒ Comonad w
  ⇒ Functor f
  ⇒ DistributiveLaw f w
  → DistributiveLaw n f
  → GAlgebra w f b
  → GCoalgebra n f a
  → a
  → b
ghylo w n f g = extract <<< go <<< pure
  where
  go na = f <$> w ((duplicate <<< go <<< join) <$> n (g <$> na))

ghyloM
  ∷ ∀ f w n m a b
  . Monad m
  ⇒ Monad n
  ⇒ Comonad w
  ⇒ Traversable f
  ⇒ Traversable w
  ⇒ Traversable n
  ⇒ DistributiveLaw f w
  → DistributiveLaw n f
  → GAlgebraM w m f b
  → GCoalgebraM n m f a
  → a
  → m b
ghyloM w m f g = map extract <<< h <<< pure
  where
  h x = traverse f =<< w <$> (traverse (map duplicate <<< h <<< join) <<< m =<< traverse g x)

transHylo
  ∷ ∀ t f g h u
  . Recursive t f
  ⇒ Corecursive u h
  ⇒ Functor g
  ⇒ Transform u g h
  → Transform t f g
  → t
  → u
transHylo f g = go
  where
  go t = mapR (f <<< map go <<< g) t

dyna
  ∷ ∀ f a b
  . Functor f
  ⇒ GAlgebra (Cofree f) f b
  → Coalgebra f a
  → a
  → b
dyna f g = ghylo distHisto distAna f (map Identity <<< g)

codyna
  ∷ ∀ f a b
  . Functor f
  ⇒ Algebra f b
  → GCoalgebra (Free f) f a
  → a
  → b
codyna f = ghylo distCata distFutu (lcmap (map unwrap) f)

codynaM
  ∷ ∀ f m a b
  . Monad m
  ⇒ Traversable f
  ⇒ AlgebraM m f b
  → GCoalgebraM (Free f) m f a
  → a
  → m b
codynaM f = ghyloM distCata distFutu (lcmap (map unwrap) f)

chrono
  ∷ ∀ f a b
  . Functor f
  ⇒ GAlgebra (Cofree f) f b
  → GCoalgebra (Free f) f a
  → a
  → b
chrono = ghylo distHisto distFutu

convertTo ∷ ∀ t f r. Recursive t f ⇒ Corecursive r f ⇒ t → r
convertTo = cata embed
