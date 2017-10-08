module InterviewQuestion


data NatMod15 : Nat -> Type where
     Zero     : (n: Nat) -> NatMod15 (Nat.mult 15 n)
     One      : (n: Nat) -> NatMod15 (Nat.plus 1 (Nat.mult 15 n))
     Two      : (n: Nat) -> NatMod15 (Nat.plus 2 (Nat.mult 15 n))
     Three    : (n: Nat) -> NatMod15 (Nat.plus 3 (Nat.mult 15 n))
     Four     : (n: Nat) -> NatMod15 (Nat.plus 4 (Nat.mult 15 n))
     Five     : (n: Nat) -> NatMod15 (Nat.plus 5 (Nat.mult 15 n))
     Six      : (n: Nat) -> NatMod15 (Nat.plus 6 (Nat.mult 15 n))
     Seven    : (n: Nat) -> NatMod15 (Nat.plus 7 (Nat.mult 15 n))
     Eight    : (n: Nat) -> NatMod15 (Nat.plus 8 (Nat.mult 15 n))
     Nine     : (n: Nat) -> NatMod15 (Nat.plus 9 (Nat.mult 15 n))
     Ten      : (n: Nat) -> NatMod15 (Nat.plus 10 (Nat.mult 15 n))
     Eleven   : (n: Nat) -> NatMod15 (Nat.plus 11 (Nat.mult 15 n))
     Twelve   : (n: Nat) -> NatMod15 (Nat.plus 12 (Nat.mult 15 n))
     Thirteen : (n: Nat) -> NatMod15 (Nat.plus 13 (Nat.mult 15 n))
     Fourteen : (n: Nat) -> NatMod15 (Nat.plus 14 (Nat.mult 15 n))


helpZero : (j : Nat) -> (result : NatMod15 (mult (fromInteger 15) (S j))) -> NatMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus j (plus j (plus j (plus j (plus j (plus j (plus j (plus j (plus j (plus j (plus j (plus j (plus j (plus j (plus j 0))))))))))))))))))))))))))))))
helpZero j result = ?helpZero_rhs

nMod15 : (n : Nat) -> NatMod15 n
-- Base
nMod15 Z = Zero {n=Z}
nMod15 (S Z) = One {n=Z}
nMod15 (S (S Z)) = Two{n=Z}
nMod15 (S (S (S Z))) = Three {n=Z}
nMod15 (S (S (S (S Z)))) = Four {n=Z}
nMod15 (S (S (S (S (S Z))))) = Five {n=Z}
nMod15 (S (S (S (S (S (S Z)))))) = Six {n=Z}
nMod15 (S (S (S (S (S (S (S Z))))))) = Seven {n=Z}
nMod15 (S (S (S (S (S (S (S (S Z)))))))) = Eight {n=Z}
nMod15 (S (S (S (S (S (S (S (S (S Z))))))))) = Nine {n=Z}
nMod15 (S (S (S (S (S (S (S (S (S (S Z)))))))))) = Ten {n=Z}
nMod15 (S (S (S (S (S (S (S (S (S (S (S Z))))))))))) = Eleven {n=Z}
nMod15 (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))) = Twelve {n=Z}
nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))) = Thirteen {n=Z}
nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))) = Fourteen {n=Z}
-- Recursive
nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) with (nMod15 k)
  jMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) j)))))))))))))))) | (Zero j) = let result = Zero {n=S j} in (helpZero j result)
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (S Z) (mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) n))))))))))))))))) | (One n) = ?help15_rhs_2
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (S (S Z)) (mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) n))))))))))))))))) | (Two n) = ?help15_rhs_3
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (S (S (S Z))) (mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) n))))))))))))))))) | (Three n) = ?help15_rhs_4
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (S (S (S (S Z)))) (mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) n))))))))))))))))) | (Four n) = ?help15_rhs_5
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (S (S (S (S (S Z))))) (mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) n))))))))))))))))) | (Five n) = ?help15_rhs_6
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (S (S (S (S (S (S Z)))))) (mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) n))))))))))))))))) | (Six n) = ?help15_rhs_7
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (S (S (S (S (S (S (S Z))))))) (mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) n))))))))))))))))) | (Seven n) = ?help15_rhs_8
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (S (S (S (S (S (S (S (S Z)))))))) (mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) n))))))))))))))))) | (Eight n) = ?help15_rhs_9
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (S (S (S (S (S (S (S (S (S Z))))))))) (mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) n))))))))))))))))) | (Nine n) = ?help15_rhs_10
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (S (S (S (S (S (S (S (S (S (S Z)))))))))) (mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) n))))))))))))))))) | (Ten n) = ?help15_rhs_11
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (S (S (S (S (S (S (S (S (S (S (S Z))))))))))) (mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) n))))))))))))))))) | (Eleven n) = ?help15_rhs_12
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))) (mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) n))))))))))))))))) | (Twelve n) = ?help15_rhs_13
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))) (mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) n))))))))))))))))) | (Thirteen n) = ?help15_rhs_14
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))) (mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) n))))))))))))))))) | (Fourteen n) = ?help15_rhs_15


{-
for the fizzbuzz numbers:

-- let X, Y, Z := Fizz, Buzz, FizzBuzz respectively
-- 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
-- X   Y X     X  Y     X        Z
-- -}
-- fizzbuzz : Nat -> Nat
-- fizzbuzz n = case toIntegerNat (modNatNZ n 15 SIsNotZ) of
--       14 => (Nat.pred . Nat.pred) n
--       13 => Nat.pred n
--       12 => (Nat.pred . Nat.pred) n
--       11 => Nat.pred n
--       10 => Nat.pred n
--       9 => (Nat.pred . Nat.pred . Nat.pred) n
--       8 => (Nat.pred . Nat.pred) n
--       7 => Nat.pred n
--       6 => Nat.pred n
--       5 => (Nat.pred . Nat.pred) n
--       4 => Nat.pred n
--       3 => (Nat.pred . Nat.pred . Nat.pred) n
--       2 => (Nat.pred . Nat.pred) n
--       1 => Nat.pred n
--       0 => (Nat.pred . Nat.pred . Nat.pred) n


{-
for the fizzbuzz numbers:

-- let X, Y, Z := Fizz, Buzz, FizzBuzz respectively
-- 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14
-- Z     X   Y X     X  Y     X
-- Z - - X - Y X - - X - Y - - X - -
-- -}
-- cofizzbuzz : Nat -> Nat
-- cofizzbuzz n with (toIntegerNat (modNatNZ n 15 SIsNotZ))
--            | 14 = 2 + n
--            | 13 = 3 + n
--            | 12 = 1 + n
--            | 11 = 2 + n
--            | 10 = 3 + n
--            | 9 = 1 + n
--            | 8 = 1 + n
--            | 7 = 2 + n
--            | 6 = 3 + n
--            | 5 = 1 + n
--            | 4 = 1 + n
--            | 3 = 2 + n
--            | 2 = 1 + n
--            | 11 = 2 + n
--            | 0 = 3 + n



-- data FB : Nat -> Type where
--      Nil : n = 0 -> FB n
--      Fizz : (m :  Nat) -> 3 = m * n -> FB (fizzbuzz n) -> FB n
--      Buzz : (m : Nat) -> 5 = m * n -> FB (fizzbuzz n) -> FB n
--      FizzBuzz : (m : Nat) -> 15 = m * n -> FB (fizzbuzz n) -> FB n



-- halp : fizzbuzz 3 = 0
-- halp = Refl

-- help : fizzbuzz 3 = fromInteger 0
-- help = halp


-- fb : FB 3
-- fb = Fizz 1 Refl (Nil help)
