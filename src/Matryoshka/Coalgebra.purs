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

module Matryoshka.Coalgebra where

type GCoalgebra n f a = a -> f (n a)

type GCoalgebraM n m f a = a -> m (f (n a))

type Coalgebra f a = a -> f a

type CoalgebraM m f a = a -> m (f a)

type ElgotCoalgebra e f a = a -> e (f a)

type ElgotCoalgebraM e m f a = a -> m (e (f a))
