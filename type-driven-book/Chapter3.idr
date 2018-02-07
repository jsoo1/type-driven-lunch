module Chapter3


import Data.Vect

%default total


infixl 2 |>
(|>) : a -> (a -> b) -> b
x |> f = f x


transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = replicate _ []
transposeMat (x :: xs) = zipWith (::) x (transposeMat xs)


multMat : Num num => Vect n (Vect m num) -> Vect m (Vect p num) -> Vect n (Vect p num)
multMat [] mb = []
multMat (row :: rows) mb with (transposeMat mb)
  multMat (row :: rows) mb | [] = replicate _ []
  multMat (row :: rows) mb | (col :: cols) =
    zipWith (*) row col
      |> ?h
