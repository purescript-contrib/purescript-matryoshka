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

module Matryoshka
  ( module Matryoshka.Algebra
  , module Matryoshka.Class.Corecursive
  , module Matryoshka.Class.Recursive
  , module Matryoshka.Coalgebra
  , module Matryoshka.DistributiveLaw
  , module Matryoshka.Fold
  , module Matryoshka.Refold
  , module Matryoshka.Transform
  , module Matryoshka.Unfold
  , module Matryoshka.Util
  ) where

import Matryoshka.Algebra (Algebra, AlgebraM, ElgotAlgebra, GAlgebra, GAlgebraM)
import Matryoshka.Class.Corecursive (class Corecursive, embed)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Coalgebra (Coalgebra, CoalgebraM, ElgotCoalgebra, GCoalgebra, GCoalgebraM)
import Matryoshka.DistributiveLaw (DistributiveLaw, distAna, distApo, distApplicative, distCata, distDistributive, distFutu, distGApo, distGApoT, distGFutu, distGHisto, distHisto, distPara, distParaT, distZygo, distZygoT)
import Matryoshka.Fold (annotateTopDown, annotateTopDownM, cata, cataM, children, elgotCata, elgotHisto, elgotPara, elgotZygo, gElgotZygo, gcata, gcataM, ghisto, gpara, gprepro, gzygo, histo, isLeaf, lambek, mutu, para, paraM, prepro, topDownCata, topDownCataM, transCata, transCataM, transCataT, transCataTM, transPara, transParaT, transPrepro, universe, zygo)
import Matryoshka.Refold (chrono, codyna, codynaM, convertTo, dyna, ghylo, ghyloM, hylo, hyloM, transHylo)
import Matryoshka.Transform (AlgebraicGTransform, CoalgebraicGTransform, Transform, TransformM)
import Matryoshka.Unfold (ana, anaM, apo, apoM, colambek, elgotAna, elgotApo, elgotFutu, futu, futuM, gana, ganaM, gapo, gpostpro, postpro, transAna, transAnaM, transAnaT, transAnaTM, transApo, transApoT, transPostpro)
import Matryoshka.Util (mapR, traverseR)
