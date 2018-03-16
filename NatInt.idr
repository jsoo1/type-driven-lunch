module NatInt

import Even

%default total


data Injective : (a:Type) -> (b:Type) -> (a -> b) -> Type where
     mkInjection : (f: (a -> b)) -> ({x:a} -> {y:a} -> f x = f y -> x = y) -> Injective a b f


embed : Nat -> Integer
embed k with (even k)
  embed k | False = negate (toIntegerNat k)
  embed k | True = toIntegerNat k


int_plus_one_equals_succ : n = fromIntegerNat x -> S n = 1 + (fromIntegerNat x)
int_plus_one_equals_succ prf {x = x} {n = z} =
  rewrite prf in
  Refl
int_plus_one_equals_succ prf {x = x} {n = (S k)} =
  rewrite prf in
  Refl


succ_equals_plus_one : x = toIntegerNat n -> 1 + x = toIntegerNat (S n)
succ_equals_plus_one prf = rewrite prf in Refl


integer_eq_refl : {x:Integer} -> {y:Integer} -> True = x == y -> x = y
integer_eq_refl prf {x} {y} with (x == y) proof x_eq_y
  integer_eq_refl prf {x = x} {y = y} | False with (uninhabited prf)
    integer_eq_refl prf {x = x} {y = y} | False | x_neq_y impossible

  integer_eq_refl prf {x = x} {y = y} | True with (intToBool (prim__eqBigInt x y)) proof next
    integer_eq_refl prf {x = x} {y = y} | True | False = ?int_eq_refl_rhs_rhs_3_rhs_1
    integer_eq_refl prf {x = x} {y = y} | True | True = ?int_eq_refl_rhs_rhs_3_rhs_2




Uninhabited (LT = EQ) where
  uninhabited Refl impossible

Uninhabited (GT = EQ) where
  uninhabited Refl impossible


eq_equal : {x:Integer} -> {y:Integer} -> EQ = compare x y -> x = y
eq_equal prf {x} {y} with (compare x y) proof compare_x_y
  eq_equal prf {x = x} {y = y} | LT with (uninhabited (sym prf))
    eq_equal prf {x = x} {y = y} | _ | lt_is_eq impossible

  eq_equal prf {x = x} {y = y} | EQ with (intToBool (prim__eqBigInt x y))
    eq_equal prf {x = x} {y = y} | _ | False with (intToBool (prim__sltBigInt x y)) proof x_eq_y'

      eq_equal prf {x = x} {y = y} | _ | _ | False with (ifThenElse False (Delay Interfaces.LT) (Delay Interfaces.GT)) proof gt_prf
        eq_equal prf {x = x} {y = y} | _ | _ | _ | gt with (trans compare_x_y gt_prf)
          eq_equal prf {x = x} {y = y} | _ | _ | _ | gt | gt_is_lt with (uninhabited (sym gt_is_lt))
            eq_equal prf {x = x} {y = y} | _ | _ | _ | gt | gt_is_lt | void impossible

      eq_equal prf {x = x} {y = y} | _ | _ | True with (ifThenElse True (Delay Interfaces.LT) (Delay Interfaces.GT)) proof lt
        eq_equal prf {x = x} {y = y} | _ | _ | _ | ite_true with (trans compare_x_y lt)
          eq_equal prf {x = x} {y = y} | _ | _ | _ | ite_true | lt_is_eq with (uninhabited (sym lt_is_eq))
            eq_equal prf {x = x} {y = y} | _ | _ | _ | ite_true | lt_is_eq | void impossible

    eq_equal prf {x = x} {y = y} | _ | True = ?help_rhs_2

  eq_equal prf {x = x} {y = y} | GT with (uninhabited (sym prf))
    eq_equal prf {x = x} {y = y} | _ | gt_is_eq impossible




negate_inj : {x:Integer} -> {y:Integer} -> negate x = negate y -> x = y
negate_inj prf {x} {y} with (compare x y) proof comp_x_y
  negate_inj prf {x} {y} | with_pat = ?heop_rhs


embed_injective : embed x = embed y -> x = y
embed_injective prf {x} {y} with (even x) proof x_even
  embed_injective prf {x} {y} | even_x with (even y) proof y_even

    embed_injective prf {x = Z} {y = Z} | _ | _ = Refl

    embed_injective prf {x = Z} {y = (S k)} | False | False with (uninhabited x_even)
      embed_injective prf {y = (S k)} | _ | _ | x_even_not_even impossible

    embed_injective prf {x = (S k)} {y = Z} | False | False with (uninhabited y_even)
      embed_injective prf {x = (S k)} | _ | _ | y_even_not_even impossible

    embed_injective prf {x = (S k)} {y = (S j)} | False | False with (embed k) proof k_embedded
      embed_injective prf {x = (S k)} {y = (S j)} | _ | _ | embedded_k with (embed j) proof j_embedded
        embed_injective prf {x = (S k)} {y = (S j)} | _ | _ | embedded_k | embedded_j with (toIntegerNat j) proof x_int
          embed_injective prf {x = (S k)} {y = (S j)} | _ | _ | embedded_k | embedded_j | x with (toIntegerNat k) proof y_int
            embed_injective prf {x = (S k)} {y = (S j)} | _ | _ | embedded_k | embedded_j | x | y =
              let thing = succ_equals_plus_one {n = j} x_int in
              ?help

    embed_injective prf {x = x} {y = y} | False | True = ?help_rhs_rhs_4
    embed_injective prf {x = x} {y = y} | True | False = ?help_rhs_rhs_1
    embed_injective prf {x = x} {y = y} | True | True = ?help_rhs_rhs_5




-- natToInt : Injective Nat Integer NatInt.embed
-- natToInt = mkInjection embed ?natToInt
