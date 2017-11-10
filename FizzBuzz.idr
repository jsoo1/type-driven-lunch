module InterviewQuestion
%default total


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
     Fizz : (n:Nat) -> Z = modNatNZ  n 3 SIsNotZ -> FB (fizzbuzz n) -> FB n
     Buzz : (n:Nat) -> Z = modNatNZ n 5 SIsNotZ -> FB (fizzbuzz n) -> FB n
     FizzBuzz : (n:Nat) -> Z = modNatNZ n 15 SIsNotZ -> FB (fizzbuzz n) -> FB n


firstFizzbuzz : Nat -> Nat
firstFizzbuzz k with (modNatNZ k 15 SIsNotZ)
  firstFizzbuzz k | Z = k
  firstFizzbuzz k | (S Z) = Nat.minus k 1
  firstFizzbuzz k | (S (S Z)) = Nat.minus k 2
  firstFizzbuzz k | (S (S (S Z))) = k
  firstFizzbuzz k | (S (S (S (S Z)))) = Nat.minus k 1
  firstFizzbuzz k | (S (S (S (S (S Z))))) = k
  firstFizzbuzz k | (S (S (S (S (S (S Z)))))) = k
  firstFizzbuzz k | (S (S (S (S (S (S (S Z))))))) = Nat.minus k 1
  firstFizzbuzz k | (S (S (S (S (S (S (S (S Z)))))))) = Nat.minus k 2
  firstFizzbuzz k | (S (S (S (S (S (S (S (S (S Z))))))))) = k
  firstFizzbuzz k | (S (S (S (S (S (S (S (S (S (S Z)))))))))) = k
  firstFizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S Z))))))))))) = Nat.minus k 1
  firstFizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))) = k
  firstFizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))) = Nat.minus k 1
  firstFizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S (S (S (S j)))))))))))))) = Nat.minus k 2


firstFB : Nat -> Type
firstFB k = FB (firstFizzbuzz k)


mkFizzBuzz : (n:Nat) -> firstFB n
mkFizzBuzz Z = Nil Z Refl
mkFizzBuzz (S Z) = Nil Z Refl
mkFizzBuzz (S (S Z)) = Nil Z Refl
mkFizzBuzz (S (S (S Z))) = Fizz 3 Refl (mkFizzBuzz (fizzbuzz 3))
mkFizzBuzz (S (S (S (S Z)))) = Fizz 3 Refl (mkFizzBuzz (fizzbuzz 3))
mkFizzBuzz (S (S (S (S (S Z))))) = Buzz 5 Refl (mkFizzBuzz (fizzbuzz 5))
mkFizzBuzz (S (S (S (S (S (S Z)))))) = Fizz 6 Refl (mkFizzBuzz (fizzbuzz 6))
mkFizzBuzz (S (S (S (S (S (S (S Z))))))) = Fizz 6 Refl (mkFizzBuzz (fizzbuzz 6))
mkFizzBuzz (S (S (S (S (S (S (S (S Z)))))))) = Fizz 6 Refl (mkFizzBuzz (fizzbuzz 6))
mkFizzBuzz (S (S (S (S (S (S (S (S (S Z))))))))) = Fizz 9 Refl (mkFizzBuzz (fizzbuzz 9))
mkFizzBuzz (S (S (S (S (S (S (S (S (S (S Z)))))))))) = Buzz 10 Refl (mkFizzBuzz (fizzbuzz 10))
mkFizzBuzz (S (S (S (S (S (S (S (S (S (S (S Z))))))))))) = Buzz 10 Refl (mkFizzBuzz (fizzbuzz 10))
mkFizzBuzz (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))) = Fizz 12 Refl (mkFizzBuzz (fizzbuzz 12))
mkFizzBuzz (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))) = Fizz 12 Refl (mkFizzBuzz (fizzbuzz 12))
mkFizzBuzz (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))) = Fizz 12 Refl (mkFizzBuzz (fizzbuzz 12))
mkFizzBuzz n with (modNatNZ (firstFizzbuzz n) 15 SIsNotZ) proof p
  mkFizzBuzz n | Z = FizzBuzz (firstFizzbuzz n) p ?help_next_0
  -- mkFizzBuzz n | (S (S (S Z))) = Fizz (firstFizzbuzz n) p ?help_next_1
  -- mkFizzBuzz n | (S (S (S (S (S Z))))) = Buzz (firstFizzbuzz n) p ?help_next_2
  -- mkFizzBuzz n | (S (S (S (S (S (S Z)))))) = Fizz (firstFizzbuzz n) p ?help_next_3
  -- mkFizzBuzz n | (S (S (S (S (S (S (S (S (S Z))))))))) = Fizz (firstFizzbuzz n) p ?help_next_4
  -- mkFizzBuzz n | (S (S (S (S (S (S (S (S (S (S Z)))))))))) = ?helpt_1
  -- mkFizzBuzz n | (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))) = ?helpt_3
