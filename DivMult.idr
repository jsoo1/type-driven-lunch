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


mult_x_eq_plus_one_k : (j:Nat) -> (k:Nat) -> (j + (k * (S j))) = (S k) * (S j) - 1
mult_x_eq_plus_one_k j k =
  rewrite minusZeroRight (plus j (mult k (S j))) in
  Refl


||| ```
||| Proof that S k <= z when z = S k * S j
||| ```
res_gte_succ_mult_succ_left : z = (S k) * (S j) -> LTE (S k) z

-- Always have a successor
res_gte_succ_mult_succ_left z_eq_succ_mult_succ {z = Z} {k = Z} {j = j} with (uninhabited z_eq_succ_mult_succ)
  res_gte_succ_mult_succ_left z_eq_succ_mult_succ {z = Z} {k = Z} {j = j} | z_zero impossible

-- 1 * 1 >= 1
res_gte_succ_mult_succ_left z_eq_succ_mult_succ {z = (S k)} {k = Z} {j = Z} =
  rewrite z_eq_succ_mult_succ in
  LTESucc (LTEZero {right = Z})

-- 1 * (S j) >= S j
res_gte_succ_mult_succ_left z_eq_succ_mult_succ {z = (S k)} {k = Z} {j = (S j)} =
  rewrite z_eq_succ_mult_succ in
  rewrite plusZeroRightNeutral j in
  LTESucc (LTEZero {right = (S j)})

res_gte_succ_mult_succ_left z_eq_succ_mult_succ {z = z} {k = (S k)} {j = j} with ((S k) * (S j)) proof sk_mult_sj
  -- Always have a successor
  res_gte_succ_mult_succ_left z_eq_succ_mult_succ {z = z} {k = (S k)} {j = j} | Z with (uninhabited sk_mult_sj)
    res_gte_succ_mult_succ_left z_eq_succ_mult_succ {z = z} {k = (S k)} {j = j} | Z | zero impossible

  -- (S k) * (S j) /= Z
  res_gte_succ_mult_succ_left z_eq_succ_mult_succ {z = Z} {k = (S k)} {j = j} | (S i) with (uninhabited z_eq_succ_mult_succ)
    res_gte_succ_mult_succ_left z_eq_succ_mult_succ {z = Z} {k = (S k)} {j = j} | (S i) | zero impossible

  -- res_gte_succ_mult_succ_left Refl {z = (S (plus j (S i)))} {k = (S k)} {j = j} | (S i) =
  --   rewrite sk_mult_sj in
  --   rewrite sym (plusSuccRightSucc j (plus j (mult k (S j)))) in
  --   rewrite mult_x_eq_plus_one_k j k in
  --   rewrite minusZeroRight (plus j (mult k (S j))) in
  --   LTESucc (LTESucc )


-- ||| ```
-- ||| Proof that S j <= z when z = S k * S j
-- ||| ```
-- res_gte_succ_mult_succ_right : z = (S k) * (S j) -> LTE (S k) z


||| ```
||| Proof that True = lte (S k) (S j) -> True = lte k j
||| ```
lte_true_pred : True = lte (S k) (S j) -> True = lte k j
lte_true_pred k_lte_j {k = Z} {j = i} = Refl
lte_true_pred Refl {k = (S _)} {j = Z} impossible
lte_true_pred k_lte_j {k = (S l)} {j = (S i)} with (lte l i)
  lte_true_pred k_lte_j {k = (S l)} {j = (S i)} | lte_l_i = k_lte_j


lte_transitive : x = lte (S k) (S j) -> x = lte k j
lte_transitive prf {k} {j} = prf


lte_false_not_LTE : False = lte x y -> Not (LTE x y)
lte_false_not_LTE prf {x = Z} {y = y} = \lte => uninhabited prf
lte_false_not_LTE prf {x = (S k)} {y = Z} = \lte => uninhabited lte
lte_false_not_LTE prf {x = (S k)} {y = (S j)} = lte_false_not_LTE (lte_transitive prf)


-- lte_false_not_LTE false_eq_lte_x_y {x = Z} {y = y} = \lte => uninhabited false_eq_lte_x_y
-- lte_false_not_LTE false_eq_lte_x_y {x = (S k)} {y = Z} = \lte => uninhabited lte
-- lte_false_not_LTE false_eq_lte_x_y {x = (S k)} {y = (S j)} =
--   let rec = lte_false_not_LTE {x = k} {y = j} in
--   \lte =>
--     let nextLte = fromLteSucc lte in
--     ?next


||| ```
||| Get an LTE after proving True = lte n m
||| ```
lte_true_LTE : True = lte n m -> LTE n m
lte_true_LTE n_lte_m {n = Z} {m = _} = LTEZero
lte_true_LTE Refl {n = (S _)} {m = Z} impossible
lte_true_LTE n_lte_m {n = (S k)} {m = (S j)} with (lte_true_pred n_lte_m)
  lte_true_LTE n_lte_m {n = (S k)} {m = (S j)} | k_lte_j = LTESucc (lte_true_LTE k_lte_j)


lteMultRight :  (n:Nat) -> LTE n (n * S m)
lteMultRight Z = LTEZero

lteMultRight (S k) {m = Z} =
  rewrite multOneRightNeutral k in
  LTESucc lteRefl

lteMultRight (S k) {m = (S j)} with ((S (plus j (mult k (S (S j)))))) proof mess
  lteMultRight (S k) {m = (S j)} | Z with (uninhabited mess)
    lteMultRight (S k) {m = (S j)} | Z | zero impossible

  lteMultRight (S k) {m = (S j)} | (S i) with (lte k (S i)) proof k_lte_si
    lteMultRight (S k) {m = (S j)} | (S i) | False = LTESucc ?next3_1
    lteMultRight (S k) {m = (S j)} | (S i) | True = LTESucc ?next3_2


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


    mult_div_inverse_necessity z_eq_x_mult_y {y_non_zero = y_non_zero} {x = (S j)} {y = (S k)} {z = (S i)} | Z with (lte (S i) k)
      mult_div_inverse_necessity z_eq_x_mult_y {x = (S j)} {y = (S k)} {z = (S i)} | Z | False =
        -- let something = lteAddRight (mult)
        ?next

      mult_div_inverse_necessity z_eq_x_mult_y {x = (S j)} {y = (S k)} {z = (S i)} | Z | True = ?next

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
