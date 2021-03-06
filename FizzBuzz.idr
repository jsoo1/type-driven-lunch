module InterviewQuestion


{-
for the fizzbuzz numbers:

let X, Y, Z := Fizz, Buzz, FizzBuzz respectively
0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
X   Y X     X  Y     X        Z
-}
fizzbuzz : Nat -> Nat
fizzbuzz n = case toIntegerNat (modNatNZ n 15 SIsNotZ) of
      14 => (Nat.pred . Nat.pred) n
      13 => Nat.pred n
      12 => (Nat.pred . Nat.pred) n
      11 => Nat.pred n
      10 => Nat.pred n
      9 => (Nat.pred . Nat.pred . Nat.pred) n
      8 => (Nat.pred . Nat.pred) n
      7 => Nat.pred n
      6 => Nat.pred n
      5 => (Nat.pred . Nat.pred) n
      4 => Nat.pred n
      3 => (Nat.pred . Nat.pred . Nat.pred) n
      2 => (Nat.pred . Nat.pred) n
      1 => Nat.pred n
      0 => (Nat.pred . Nat.pred . Nat.pred) n


{-
for the fizzbuzz numbers:

let X, Y, Z := Fizz, Buzz, FizzBuzz respectively
0 1 2 3 4 5 6 7 8 9 10 11 12 13 14
Z     X   Y X     X  Y     X
Z - - X - Y X - - X - Y - - X - -
-}
cofizzbuzz : Nat -> Nat
cofizzbuzz n with (toIntegerNat (modNatNZ n 15 SIsNotZ))
           | 14 = 2 + n
           | 13 = 3 + n
           | 12 = 1 + n
           | 11 = 2 + n
           | 10 = 3 + n
           | 9 = 1 + n
           | 8 = 1 + n
           | 7 = 2 + n
           | 6 = 3 + n
           | 5 = 1 + n
           | 4 = 1 + n
           | 3 = 2 + n
           | 2 = 1 + n
           | 11 = 2 + n
           | 0 = 3 + n



data FB : Nat -> Type where
     Nil : n = 0 -> FB n
     Fizz : (m :  Nat) -> 3 = m * n -> FB (fizzbuzz n) -> FB n
     Buzz : (m : Nat) -> 5 = m * n -> FB (fizzbuzz n) -> FB n
     FizzBuzz : (m : Nat) -> 15 = m * n -> FB (fizzbuzz n) -> FB n



halp : fizzbuzz 3 = 0
halp = Refl

help : fizzbuzz 3 = fromInteger 0
help = halp


fb : FB 3
fb = Fizz 1 Refl (Nil help)

