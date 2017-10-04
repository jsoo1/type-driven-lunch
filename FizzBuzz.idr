module FizzBuzz


total fizzbuzz : Nat -> Nat
fizzbuzz Z = Z
fizzbuzz n = case modNat n 15 of
      Z =>
        (Nat.pred . Nat.pred . Nat.pred) n
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))) =>
         (Nat.pred . Nat.pred) n
      (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))) =>
         Nat.pred n
      (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))) =>
         (Nat.pred . Nat.pred) n
      (S (S (S (S (S (S (S (S (S (S (S Z))))))))))) =>
         Nat.pred n
      (S (S (S (S (S (S (S (S (S (S Z)))))))))) =>
         Nat.pred n
      (S (S (S (S (S (S (S (S (S Z))))))))) =>
         (Nat.pred . Nat.pred . Nat.pred) n
      (S (S (S (S (S (S (S (S Z)))))))) =>
         (Nat.pred . Nat.pred) n
      (S (S (S (S (S (S (S Z))))))) =>
         Nat.pred n
      (S (S (S (S (S (S Z)))))) =>
         Nat.pred n
      (S (S (S (S (S Z))))) =>
         (Nat.pred . Nat.pred) n
      (S (S (S (S Z)))) =>
         Nat.pred n
      (S (S (S Z))) =>
         (Nat.pred . Nat.pred . Nat.pred) n
      (S (S Z)) =>
         (Nat.pred . Nat.pred) n
      (S Z) =>
         Nat.pred n


data FB : Nat -> Type where
     Nil : FB Z
     Fizz : FB (fizzbuzz n) -> FB n
     Buzz : FB (fizzbuzz n) -> FB n
     FizzBuzz : FB (fizzbuzz n) -> FB n


-- fizz : FB 2
-- fizz = Fizz (Fizz [])


{-
let X, Y, Z := Fizz, Buzz, FizzBuzz respectively
0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
      X   Y X     X  Y     X        Z
-}
