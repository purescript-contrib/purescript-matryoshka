module Test.Example.List where

import Prelude

import Effect (Effect)
import Effect.Console (log, logShow)

import Data.Functor.Mu (Mu)
import Data.TacitString (TacitString)
import Matryoshka (class Corecursive, Algebra, Coalgebra, ana, cata, embed, hylo)

data ListF a t = Nil | Cons a t

derive instance functorListF :: Functor (ListF a)

instance showListF :: Show a => Show (ListF a TacitString) where
  show Nil = "Nil"
  show (Cons h t) = show h <> " : " <> show t

nil :: forall a t. Corecursive t (ListF a) => t
nil = embed Nil

cons :: forall a t. Corecursive t (ListF a) => a -> t -> t
cons h t = embed (Cons h t)

prod :: Algebra (ListF Int) Int
prod Nil = 1
prod (Cons h t) = h * t

count :: Coalgebra (ListF Int) Int
count n
  | n <= 0 = Nil
  | otherwise = Cons n (n - 1)

fac :: Int -> Int
fac = hylo prod count

type List a = Mu (ListF a)

listExample :: Effect Unit
listExample = do
  log "list example"
  let someList = cons 1 (cons 2 (cons 3 (cons 4 nil)))
  logShow $ cata prod (someList :: List Int)
  logShow (ana count 4 :: List Int)
  logShow (fac 6)
