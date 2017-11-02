module InterviewQuestion

{--
X - Fizz
Y - Buzz
Z - Fizzbuzz
0 1 2 3 4 5 6 7 8 9 10 11 12 13 14
Z - - X - Y X - - X  Y  - X  -  -
--}

data NatMod15 : Nat -> Type where
     Zero     : (n : Nat) -> NatMod15 (15 * n)
     One      : (n : Nat) -> NatMod15 (1 + (15 * n))
     Two      : (n : Nat) -> NatMod15 (2 + (15 * n))
     Three    : (n : Nat) -> NatMod15 (3 + (15 * n))
     Four     : (n : Nat) -> NatMod15 (4 + (15 * n))
     Five     : (n : Nat) -> NatMod15 (5 + (15 * n))
     Six      : (n : Nat) -> NatMod15 (6 + (15 * n))
     Seven    : (n : Nat) -> NatMod15 (7 + (15 * n))
     Eight    : (n : Nat) -> NatMod15 (8 + (15 * n))
     Nine     : (n : Nat) -> NatMod15 (9 + (15 * n))
     Ten      : (n : Nat) -> NatMod15 (10 + (15 * n))
     Eleven   : (n : Nat) -> NatMod15 (11 + (15 * n))
     Twelve   : (n : Nat) -> NatMod15 (12 + (15 * n))
     Thirteen : (n : Nat) -> NatMod15 (13 + (15 * n))
     Fourteen : (n : Nat) -> NatMod15 (14 + (15 * n))


nMod15 : (n : Nat) -> NatMod15 n
-- Base
nMod15 Z = Zero {n=Z}
nMod15 (S Z) = One {n=Z}
nMod15 (S (S Z)) = Two {n=Z}
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
  nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ((fromInteger 15) * n)))))))))))))))) | (Zero n) =
         rewrite sym (multRightSuccPlus 15 n) in Zero (S n)
  nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ((fromInteger 1) + ((fromInteger 15) * n))))))))))))))))) | (One n) =
         rewrite sym (multRightSuccPlus 15 n) in One (S n)
  nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ((fromInteger 2) + ((fromInteger 15) * n))))))))))))))))) | (Two n) =
         rewrite sym (multRightSuccPlus 15 n) in Two (S n)
  nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ((fromInteger 3) + ((fromInteger 15) * n))))))))))))))))) | (Three n) =
         rewrite sym (multRightSuccPlus 15 n) in Three (S n)
  nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ((fromInteger 4) + ((fromInteger 15) * n))))))))))))))))) | (Four n) =
         rewrite sym (multRightSuccPlus 15 n) in Four (S n)
  nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ((fromInteger 5) + ((fromInteger 15) * n))))))))))))))))) | (Five n) =
         rewrite sym (multRightSuccPlus 15 n) in Five (S n)
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ((fromInteger 6) + ((fromInteger 15) * n))))))))))))))))) | (Six n) =
  --        rewrite sym (multRightSuccPlus 15 n) in Six (S n)
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ((fromInteger 7) + ((fromInteger 15) * n))))))))))))))))) | (Seven n) =
  --        rewrite sym (multRightSuccPlus 15 n) in Seven (S n)
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ((fromInteger 8) + ((fromInteger 15) * n))))))))))))))))) | (Eight n) =
  --        rewrite sym (multRightSuccPlus 15 n) in Eight (S n)
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ((fromInteger 9) + ((fromInteger 15) * n))))))))))))))))) | (Nine n) =
  --        rewrite sym (multRightSuccPlus 15 n) in Nine (S n)
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ((fromInteger 10) + ((fromInteger 15) * n))))))))))))))))) | (Ten n) =
  --        rewrite sym (multRightSuccPlus 15 n) in Ten (S n)
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ((fromInteger 11) + ((fromInteger 15) * n))))))))))))))))) | (Eleven n) =
  --        rewrite sym (multRightSuccPlus 15 n) in Eleven (S n)
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ((fromInteger 12) + ((fromInteger 15) * n))))))))))))))))) | (Twelve n) =
  --        rewrite sym (multRightSuccPlus 15 n) in Twelve (S n)
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ((fromInteger 13) + ((fromInteger 15) * n))))))))))))))))) | (Thirteen n) =
  --        rewrite sym (multRightSuccPlus 15 n) in Thirteen (S n)
  -- nMod15 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ((fromInteger 14) + ((fromInteger 15) * n))))))))))))))))) | (Fourteen n) =
  --        rewrite sym (multRightSuccPlus 15 n) in Fourteen (S n)



-- for the fizzbuzz numbers:

-- let X, Y, Z := Fizz, Buzz, FizzBuzz respectively
-- 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
-- X   Y X     X  Y     X        Z
--
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
