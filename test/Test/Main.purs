module Test.Main where

import Prelude
import Effect (Effect)
import Test.Example.Expr (exprExample)
import Test.Example.List (listExample)

main :: Effect Unit
main = do
  exprExample
  listExample
