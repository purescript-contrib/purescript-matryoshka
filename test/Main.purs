module Test.Main where

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, logShow)
import Data.Functor.Mu (Mu)
import Matryoshka (class Corecursive, class Recursive, Algebra, cata, embed)
import Prelude (class Functor, Unit, ($), (*))

data ExprF a = Num Int | Mul a a

derive instance functorExprF :: Functor ExprF

eval :: Algebra ExprF Int
eval (Num i) = i
eval (Mul i j) = i * j

evalExpr :: forall t. (Recursive t ExprF) => t -> Int
evalExpr = cata eval

num :: forall t. Corecursive t ExprF => Int -> t
num i = embed (Num i)

mul :: forall t. Corecursive t ExprF => t -> t -> t
mul i j = embed (Mul i j)

someExpr :: forall t. Corecursive t ExprF => t
someExpr = mul (num 2) (mul (num 3) (num 4))

type Expr = Mu ExprF

main :: forall t. Eff (console :: CONSOLE | t) Unit
main = do
  logShow $ evalExpr (someExpr :: Expr)
