module Test.Main where

import Prelude
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE)
import Test.Example.Expr (exprExample)
import Test.Example.List (listExample)

main :: forall t. Eff ( console :: CONSOLE | t) Unit
main = do
  exprExample
  listExample
