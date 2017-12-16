module DivMult



||| ```
||| Proof that if False = cond and z = ifThenElse a x y then z = y
||| ```
ite_false_x_y_y : False = a ->  z = ifThenElse a x y ->  z = y
ite_false_x_y_y a_false ite_a_x_y {a} {x} {y} with (ifThenElse a x y) proof  ite_2_prf
  ite_false_x_y_y a_false ite_a_x_y {a} {x} {y} | ite_2 =
    rewrite ite_a_x_y in
    rewrite ite_2_prf in
    rewrite sym a_false in
    Refl


res_gte_succ_mult_succ_left : z = (S k) * (S j) -> LTE (S k) z
res_gte_succ_mult_succ_left z_eq_succ_mult_succ {z = Z} {k = Z} {j = j} with (uninhabited z_eq_succ_mult_succ)
  res_gte_succ_mult_succ_left z_eq_succ_mult_succ {z = Z} {k = Z} {j = j} | z_zero impossible

res_gte_succ_mult_succ_left z_eq_succ_mult_succ {z = (S k)} {k = Z} {j = Z} =
  rewrite z_eq_succ_mult_succ in
  LTESucc (LTEZero {right = Z})

res_gte_succ_mult_succ_left z_eq_succ_mult_succ {z = (S k)} {k = Z} {j = (S j)} =
  rewrite z_eq_succ_mult_succ in
  rewrite plusZeroRightNeutral j in
  LTESucc (LTEZero {right = (S j)})

res_gte_succ_mult_succ_left z_eq_succ_mult_succ {z = z} {k = (S k)} {j = j} =
  rewrite z_eq_succ_mult_succ in
  rewrite sym (plusSuccRightSucc j (plus j (mult k (S j)))) in
  LTESucc (LTESucc ?help)


res_gte_succ_mult_succ_right : z = (S k) * (S j) -> LTE (S k) z


using (x:Nat, y:Nat, z:Nat)
  mult_div_inverse_necessity :
    {y_non_zero: Not (y = Z)} ->
    z = x * y ->
    divNatNZ z y y_non_zero = x

  -- y is non-zero
  mult_div_inverse_necessity _ {y_non_zero} {y = Z} with (y_non_zero Refl)
    mult_div_inverse_necessity _ {y_non_zero} {y = Z} | y_eq_zero impossible

  -- non-trivial case
  mult_div_inverse_necessity z_eq_x_mult_y {y_non_zero} {x = x} {y = (S k)} {z = z} with (divNatNZ z (S k) y_non_zero) proof z_div_sk_prf
    -- x is zero is trivial case
    mult_div_inverse_necessity z_eq_x_mult_y {y_non_zero} {x = Z} {y = (S k)} {z = z} | Z = Refl

    -- succ * succ is non-zero
    mult_div_inverse_necessity z_eq_x_mult_y {y_non_zero} {x = (S j)} {y = (S k)} {z = Z} | Z with (uninhabited z_eq_x_mult_y)
      mult_div_inverse_necessity z_eq_x_mult_y {y_non_zero} {x = (S j)} {y = (S k)} {z = Z} | Z | zero_eq_succ_mult_succ impossible


    mult_div_inverse_necessity z_eq_x_mult_y {y_non_zero} {x = (S j)} {y = (S k)} {z = (S i)} | Z =
      rewrite z_div_sk_prf in
      -- rewrite z_eq_x_mult_y in
      ?succ_times_succ_non_zero_2

    -- induction step
    mult_div_inverse_necessity z_eq_x_mult_y {y_non_zero} {x = x} {y = (S k)} {z = z} | (S j) = ?mult_div_inverse_necessity_inductive


  -- -- y is non-zero
  -- mult_div_inverse_necessity z_equals {y_non_zero} {y = Z} with (y_non_zero Refl)
  --   mult_div_inverse_necessity {y_non_zero} {y = Z} | y_zero impossible

  -- -- non-trivial case
  -- mult_div_inverse_necessity z_equals {y_non_zero} {x} {y = (S k)} {z} with (divNatNZ z (S k) y_non_zero) proof z_div_sk_prf
  --   mult_div_inverse_necessity {x = Z} {y = (S k)} {z = Z} | Z =
  --     Refl

  --   mult_div_inverse_necessity z_equals {z_equals} {x = (S j)} {y = (S k)} {z = Z} | Z with (uninhabited z_equals)
  --     mult_div_inverse_necessity z_equals {z_equals} {x = (S j)} {y = (S k)} {z = Z} | Z | with_pat = ?hlee_rhs


  --   mult_div_inverse_necessity z_equals {y = (S k)} {z = (S j)} | Z = ?mult_div_inverse_necessity_2

  --   mult_div_inverse_necessity z_equals {y = (S k)} {z} | (S j) = ?mult_div_inverse_necessity_3
