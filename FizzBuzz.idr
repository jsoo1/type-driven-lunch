module FizzBuzz


%default total


succ_lemma : (left:Nat) -> (right:Nat) -> left = right -> S left = S right
succ_lemma Z Z prf = Refl
succ_lemma Z (S _) Refl impossible
succ_lemma (S _) Z Refl impossible
succ_lemma (S k) (S j) prf = rewrite succInjective k j prf in Refl


using (n:Nat, m:Nat, o:Nat)
  minus_succ_lemma :
    {m_lte_n: LTE m n} ->
    {m_lte_sn: LTE m (S n)} ->
    (S n) - m = S o ->
    n - m = o
  minus_succ_lemma sn_minus_m_eq_so {n} {m} {o} =
    let rule_1 = plusOneSucc n in
    ?help





using (n:Nat, m:Nat, o:Nat)
  minus_inverse_plus : LTE n o -> o = n + m -> o - n = m
  minus_inverse_plus x n_plus_m {o} {n} {m} with (minus o n) proof o_minus_n
    minus_inverse_plus x n_plus_m {o = o} {n = n} {m = Z} | o_minus =
      rewrite o_minus_n in
      rewrite n_plus_m in
      rewrite plusZeroRightNeutral n in
      rewrite minusZeroN n in
      Refl
    minus_inverse_plus x n_plus_m {o = o} {n = n} {m = (S k)} | o_minus =
      rewrite o_minus_n in
      rewrite n_plus_m in
      -- rewrite succInjective in
      rewrite sym (plusSuccRightSucc n k) in
      ?hlp



-- ||| Get the next fizzbuzz number
-- ||| ```
-- |||
-- ||| X - Fizz
-- ||| Y - Buzz
-- ||| Z - Fizzbuzz
-- ||| 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14
-- ||| Z - - X - Y X - - X  Y  - X  -  -
-- ||| ```
-- fizzbuzz : Nat -> Nat
-- fizzbuzz k with (modNatNZ k 15 SIsNotZ) proof k_mod_15
--   fizzbuzz k | Z = minus k 3
--   fizzbuzz k | (S Z) = minus k 1
--   fizzbuzz k | (S (S Z)) = minus k 2
--   fizzbuzz k | (S (S (S Z))) = minus k 3
--   fizzbuzz k | (S (S (S (S Z)))) = minus k 1
--   fizzbuzz k | (S (S (S (S (S Z))))) = minus k 2
--   fizzbuzz k | (S (S (S (S (S (S Z)))))) = minus k 1
--   fizzbuzz k | (S (S (S (S (S (S (S Z))))))) = minus k 1
--   fizzbuzz k | (S (S (S (S (S (S (S (S Z)))))))) = minus k 2
--   fizzbuzz k | (S (S (S (S (S (S (S (S (S Z))))))))) = minus k 3
--   fizzbuzz k | (S (S (S (S (S (S (S (S (S (S Z)))))))))) = minus k 1
--   fizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S Z))))))))))) = minus k 1
--   fizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))) = minus k 2
--   fizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))) = minus k 1
--   fizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))) = minus k 2
--   fizzbuzz k | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S j))))))))))))))) = ?help



-- data FB : Nat -> Type where
--      Nil : FB Z
--      Fizz : (n:Nat) -> (n = 3 * _) -> FB (fizzbuzz n) -> FB n
--      Buzz : (n:Nat) -> (n = 5 * _) -> FB (fizzbuzz n) -> FB n
--      FizzBuzz : (n:Nat) -> (n = 15 * _) -> FB (fizzbuzz n) -> FB n
