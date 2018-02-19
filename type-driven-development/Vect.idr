module Vect


import Data.Fin


%default total


data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : (x : a) -> (xs : Vect k a) -> Vect (S k) a


%name Vect xs, ys, zs


append : Vect n elem -> Vect m elem -> Vect (n + m) elem
append [] ys = ys
append (x :: xs) ys = x :: append xs ys


zip : Vect n a -> Vect n b -> Vect n (a, b)
zip [] [] = []
zip [] (y :: ys) impossible
zip (x :: xs) [] impossible
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys


index : Fin n -> Vect n a -> a
index _ [] impossible
index FZ (x :: xs) = x
index (FS i) (x :: xs) = index i xs


tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} i xs =
  case integerToFin i n of
    Nothing => Nothing
    Just idx => Just $ index idx xs
