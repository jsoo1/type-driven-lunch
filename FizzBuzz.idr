module InterviewQuestion
-- IRC help
-- natMod15Succ : NatMod15 n -> NatMod15 (S n)

fizzbuzz : Nat -> Nat
fizzbuzz k with (modNatNZ k 15 SIsNotZ)
  fizzbuzz k | Z = Nat.minus k 3
  fizzbuzz k | (S Z) = Nat.minus k 1
  fizzbuzz k | (S (S Z)) = Nat.minus k 2
  fizzbuzz k | (S (S (S Z))) = Nat.minus k 3
  fizzbuzz k | (S (S (S (S Z)))) = Nat.minus k 1
  fizzbuzz k | (S (S (S (S (S Z))))) = Nat.minus k 2
  fizzbuzz k | (S (S (S (S (S (S Z)))))) = Nat.minus k 1
  fizzbuzz k | (S (S (S (S (S (S (S Z))))))) = Nat.minus k 1
  fizzbuzz k | (S (S (S (S (S (S (S (S Z)))))))) = Nat.minus k 2
  fizzbuzz k | (S (S (S (S (S (S (S (S (S Z))))))))) = Nat.minus k 3
  fizzbuzz k | (S (S (S (S (S (S (S (S (S (S Z)))))))))) = Nat.minus k 1
  fizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S Z))))))))))) = Nat.minus k 1
  fizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))) = Nat.minus k 2
  fizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))) = Nat.minus k 1
  fizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S (S (S (S j)))))))))))))) = Nat.minus k 2


data FB : Nat -> Type where
      Nil : (n:Nat) -> Z = n -> FB Z
      Fizz : (n:Nat) -> Z = modNatNZ n 3 SIsNotZ -> FB (fizzbuzz n) -> FB n
      Buzz : (n:Nat) -> Z = modNatNZ n 5 SIsNotZ -> FB (fizzbuzz n) -> FB n
      FizzBuzz : (n:Nat) -> Z = modNatNZ n 15 SIsNotZ -> FB (fizzbuzz n) -> FB n


mkFizzBuzz : (n:Nat) -> FB n
mkFizzBuzz Z = Nil Z Refl
mkFizzBuzz n with (modNatNZ n 15 SIsNotZ) proof prf
  mkFizzBuzz n | Z = FizzBuzz n ?help (mkFizzBuzz (fizzbuzz n))
  -- mkFizzBuzz n | (S Z) = ?help_rhs_3
  -- mkFizzBuzz n | (S (S Z)) = ?help_rhs_2
  -- mkFizzBuzz n | (S (S (S Z))) = ?help_rhs_4
  -- mkFizzBuzz n | (S (S (S (S Z)))) = ?help_rhs_5
  -- mkFizzBuzz n | (S (S (S (S (S Z))))) = ?help_rhs_6
  -- mkFizzBuzz n | (S (S (S (S (S (S Z)))))) = ?help_rhs_7
  -- mkFizzBuzz n | (S (S (S (S (S (S (S Z))))))) = ?help_rhs_8
  -- mkFizzBuzz n | (S (S (S (S (S (S (S (S Z)))))))) = ?help_rhs_9
  -- mkFizzBuzz n | (S (S (S (S (S (S (S (S (S Z))))))))) = ?help_rhs_10
  -- mkFizzBuzz n | (S (S (S (S (S (S (S (S (S (S Z)))))))))) = ?help_rhs_11
  -- mkFizzBuzz n | (S (S (S (S (S (S (S (S (S (S (S Z))))))))))) = ?help_rhs_12
  -- mkFizzBuzz n | (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))) = ?help_rhs_13
  -- mkFizzBuzz n | (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))) = ?help_rhs_15
