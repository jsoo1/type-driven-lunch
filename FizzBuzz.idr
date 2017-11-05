module InterviewQuestion
%default total


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
  firstFizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S (S (S (S j)))))))))))))) =
                Nat.minus k 2


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
     Nil       : (n:Nat) ->
                 Z = (firstFizzbuzz n) ->
                 FB Z
     Fizz      : (n:Nat) ->
                 Z = modNatNZ (firstFizzbuzz n) 3 SIsNotZ ->
                 FB (fizzbuzz (firstFizzbuzz n)) ->
                 FB (firstFizzbuzz n)
     Buzz      : (n:Nat) ->
                 Z = modNatNZ (firstFizzbuzz n) 5 SIsNotZ ->
                 FB (fizzbuzz (firstFizzbuzz n)) ->
                 FB (firstFizzbuzz n)
     FizzBuzz  : (n:Nat) ->
                 Z = modNatNZ (firstFizzbuzz n) 15 SIsNotZ ->
                 FB (fizzbuzz (firstFizzbuzz n)) ->
                 FB (firstFizzbuzz n)



mkFizzBuzz : (n:Nat) -> FB n
mkFizzBuzz Z = Nil Z Refl
mkFizzBuzz n with (firstFizzbuzz n) proof prf
  mkFizzBuzz n | Z = FizzBuzz n ?help_prf (mkFizzBuzz (fizzbuzz n))
  -- mkFizzBuzz n | (S (S (S Z))) = Fizz n prf (mkFizzBuzz (fizzbuzz n))
  -- mkFizzBuzz n | (S (S (S (S (S Z))))) = ?five
  -- mkFizzBuzz n | (S (S (S (S (S (S Z)))))) = ?six
  -- mkFizzBuzz n | (S (S (S (S (S (S (S (S (S Z))))))))) = ?nine
  -- mkFizzBuzz n | (S (S (S (S (S (S (S (S (S (S Z)))))))))) = ?ten
  -- mkFizzBuzz n | (S (S (S (S (S (S (S (S (S (S (S (S k)))))))))))) = ?twelve
