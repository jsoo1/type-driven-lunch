module Chapter3


import Data.Vect

%default total


infixl 0 |>
(|>) : a -> (a -> b) -> b
x |> f = f x


transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = replicate _ []
transposeMat (x :: xs) = zipWith (::) x (transposeMat xs)


multMat : Num num => Vect n (Vect m num) -> Vect m (Vect p num) -> Vect n (Vect p num)
multMat [] mb = []
multMat ma mb with (transposeMat mb)
  multMat ma mb | [] = replicate _ []
  multMat ma mb {m} | mb_trans = ?help
    -- map zipRows ma
    -- where
    --   zipRows : Num num => Vect n num -> Vect n num -> Vect m num
    --   zipRows row col = ?help
