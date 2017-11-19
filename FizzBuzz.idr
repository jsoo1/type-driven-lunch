module InterviewQuestion
%default total


data FBNum : Type -> Type where
     FizzNum : (n:Nat) -> {auto k_non_zero: (Not (m = Z))} -> FBNum (n = 3 * m)



-- fizzbuzz : Nat -> 


-- data FB : Nat -> Type where
--      Nil : Z = n -> FB n
--      Fizz : l = 3 * k -> FB (fizzbuzz l) -> FB l
--      Buzz : (n:Nat) -> Z = modNatNZ n 5 SIsNotZ -> FB (fizzbuzz n) -> FB n
--      FizzBuzz : (n:Nat) -> Z = modNatNZ n 15 SIsNotZ -> FB (fizzbuzz n) -> FB n


