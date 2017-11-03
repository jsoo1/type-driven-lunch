module InterviewQuestion
-- IRC help
-- natMod15Succ : NatMod15 n -> NatMod15 (S n)

fizzbuzz : Nat -> Nat
fizzbuzz Z = 0
fizzbuzz (S Z) = 0
fizzbuzz (S (S Z)) = 0
fizzbuzz (S (S (S Z))) = 0
fizzbuzz (S (S (S (S Z)))) = 3
fizzbuzz (S (S (S (S (S Z))))) = 3
fizzbuzz (S (S (S (S (S (S Z)))))) = 5
fizzbuzz (S (S (S (S (S (S (S Z))))))) = 6
fizzbuzz (S (S (S (S (S (S (S (S Z)))))))) = 6
fizzbuzz (S (S (S (S (S (S (S (S (S Z))))))))) = 6
fizzbuzz (S (S (S (S (S (S (S (S (S (S Z)))))))))) = 9
fizzbuzz (S (S (S (S (S (S (S (S (S (S (S Z))))))))))) = 10
fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))) = 10
fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))) = 12
fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))) = 12
fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) with (modNatNZ k 15 SIsNotZ)
  fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) | Z = Nat.minus k 3
  fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) | (S Z) = Nat.minus k 1
  fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) | (S (S Z)) = Nat.minus k 2
  fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) | (S (S (S Z))) = Nat.minus k 3
  fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) | (S (S (S (S Z)))) = Nat.minus k 1
  fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) | (S (S (S (S (S Z))))) = Nat.minus k 2
  fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) | (S (S (S (S (S (S Z)))))) = Nat.minus k 1
  fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) | (S (S (S (S (S (S (S Z))))))) = Nat.minus k 1
  fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) | (S (S (S (S (S (S (S (S Z)))))))) = Nat.minus k 2
  fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) | (S (S (S (S (S (S (S (S (S Z))))))))) = Nat.minus k 3
  fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) | (S (S (S (S (S (S (S (S (S (S Z)))))))))) = Nat.minus k 1
  fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) | (S (S (S (S (S (S (S (S (S (S (S Z))))))))))) = Nat.minus k 1
  fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) | (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))) = Nat.minus k 2
  fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) | (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))) = Nat.minus k 1
  fizzbuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) | (S (S (S (S (S (S (S (S (S (S (S (S (S (S j)))))))))))))) = Nat.minus k 2


data FB : Nat -> Type where
      Nil : (n:Nat) -> Z = n -> FB Z
      Fizz : (n:Nat) -> Z = modNatNZ n 3 SIsNotZ -> FB (fizzbuzz n) -> FB n
      Buzz : (n:Nat) -> Z = modNatNZ n 5 SIsNotZ -> FB (fizzbuzz n) -> FB n
      FizzBuzz : (n:Nat) -> Z = modNatNZ n 15 SIsNotZ -> FB (fizzbuzz n) -> FB n


mkFizzBuzz : (n:Nat) -> FB (fizzbuzz n)
mkFizzBuzz Z = Nil 0 Refl
mkFizzBuzz (S k) with (mkFizzBuzz (fizzbuzz k))
  mkFizzBuzz (S k) | with_pat = ?k_rhs


