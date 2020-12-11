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

module Matryoshka.Transform where

type Transform :: Type -> (Type -> Type) -> (Type -> Type) -> Type
type Transform t f g = f t → g t

type TransformM :: (Type -> Type) -> Type -> (Type -> Type) -> (Type -> Type) -> Type
type TransformM m t f g = f t → m (g t)

type AlgebraicGTransform :: (Type -> Type) -> Type -> (Type -> Type) -> (Type -> Type) -> Type
type AlgebraicGTransform w t f g = f (w t) → g t

type CoalgebraicGTransform :: (Type -> Type) -> Type -> (Type -> Type) -> (Type -> Type) -> Type
type CoalgebraicGTransform n t f g = f t → g (n t)
