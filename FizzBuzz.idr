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


divide : prod = l * k -> {k_non_zero: (Not (k = Z))} -> Nat
divide {l} mult_l_k_nat = l


divides_mult_inverse : (mult_j_k: (prod = j * k)) -> {auto k_non_zero: (Not (k = Z))} -> j = divide mult_j_k
divides_mult_inverse mult_j_k = Refl


divides_mod_zero : prod = j * k -> {auto k_non_zero: (Not (k = Z))} -> Z = modNatNZ prod k k_non_zero
divides_mod_zero {prod = Z} {j = j} {k = Z} {k_non_zero} mult_j_k = void (k_non_zero Refl)
divides_mod_zero {prod = Z} {j = j} {k = (S n)} mult_j_k = Refl
divides_mod_zero {prod = (S m)} {j = j} {k = n} mult_j_k = rewrite mult_j_k in ?help


-- nextFizzBuzz : (j : Nat) -> FB (fizzbuzz j)
-- nextFizzBuzz j with (fizzbuzz j) proof fizzbuzz_j_equals

--   nextFizzBuzz j | fizzbuzz_j with (modNatNZ (fizzbuzz j) 15 SIsNotZ) proof mod_15_fizzbuzz_j_equals

--     nextFizzBuzz Z | fizzbuzz_j | mod_15_fizzbuzz_j =
--       rewrite fizzbuzz_j_equals in
--         Nil Z Refl

--     nextFizzBuzz j | fizzbuzz_j | Z =
--       FizzBuzz
--         fizzbuzz_j
--         (rewrite fizzbuzz_j_equals in rewrite mod_15_fizzbuzz_j_equals in Refl)
--         (nextFizzBuzz fizzbuzz_j)

--     nextFizzBuzz j | fizzbuzz_j | (S (S (S Z))) =
--       Fizz
--         fizzbuzz_j
--         ?prf
--         (nextFizzBuzz fizzbuzz_j)


-- mkFizzBuzz : (j:Nat) -> FB (firstFizzbuzz j)
-- mkFizzBuzz Z = Nil Z Refl
-- mkFizzBuzz j with (firstFizzbuzz j) proof firstFizzbuzz_j
--   mkFizzBuzz j | k with (modNatNZ k 15 SIsNotZ) proof mod_15_k
--     mkFizzBuzz j | k | Z = FizzBuzz k mod_15_k ?help_next
    -- mkFizzBuzz j | k | (S (S (S Z))) = ?help_3
    -- mkFizzBuzz j | k | (S (S (S (S (S Z))))) = ?help_2
    -- mkFizzBuzz j | k | (S (S (S (S (S (S Z)))))) = ?help_4
    -- mkFizzBuzz j | k | (S (S (S (S (S (S (S (S (S Z))))))))) = ?help_5
    -- mkFizzBuzz j | k | (S (S (S (S (S (S (S (S (S (S Z)))))))))) = ?help_6
    -- mkFizzBuzz j | k | (S (S (S (S (S (S (S (S (S (S (S (S i)))))))))))) = ?help_9
