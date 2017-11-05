module InterviewQuestion
%default total


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


firstFizzbuzz : Nat -> Type
firstFizzbuzz k with (modNatNZ k 15 SIsNotZ)
  firstFizzbuzz k | Z = FB k
  firstFizzbuzz k | (S Z) = FB (Nat.minus k 1)
  firstFizzbuzz k | (S (S Z)) = FB (Nat.minus k 2)
  firstFizzbuzz k | (S (S (S Z))) = FB k
  firstFizzbuzz k | (S (S (S (S Z)))) = FB (Nat.minus k 1)
  firstFizzbuzz k | (S (S (S (S (S Z))))) = FB k
  firstFizzbuzz k | (S (S (S (S (S (S Z)))))) = FB k
  firstFizzbuzz k | (S (S (S (S (S (S (S Z))))))) = FB (Nat.minus k 1)
  firstFizzbuzz k | (S (S (S (S (S (S (S (S Z)))))))) = FB (Nat.minus k 2)
  firstFizzbuzz k | (S (S (S (S (S (S (S (S (S Z))))))))) = FB k
  firstFizzbuzz k | (S (S (S (S (S (S (S (S (S (S Z)))))))))) = FB k
  firstFizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S Z))))))))))) = FB (Nat.minus k 1)
  firstFizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))) = FB k
  firstFizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))) = FB (Nat.minus k 1)
  firstFizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S (S (S (S j)))))))))))))) = FB (Nat.minus k 2)


mkFizzBuzz : (n:Nat) -> firstFizzbuzz n
mkFizzBuzz Z = Nil Z Refl
mkFizzBuzz n with (_)
  mkFizzBuzz n | with_pat = ?n_rhs
