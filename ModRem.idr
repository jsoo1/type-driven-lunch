module ModRem



||| ```
||| Proof that 0 = mod 0 x for non-zero Nats
||| ```
mod_z_z : (y_non_zero: Not (y = 0)) -> (x_zero: x = 0) -> 0 = modNatNZ x y y_non_zero
mod_z_z y_non_zero x_zero {x = x} {y = Z} with (y_non_zero Refl)
  mod_z_z y_non_zero x_zero {x = x} {y = Z} | y_zero impossible
mod_z_z y_non_zero x_zero {x = x} {y = (S k)} = rewrite x_zero in Refl


||| ```
||| Proof that True = lte (S k) (S j) -> True = lte k j
||| ```
lte_true_pred : True = lte (S k) (S j) -> True = lte k j
lte_true_pred k_lte_j {k = Z} {j = i} = Refl
lte_true_pred Refl {k = (S _)} {j = Z} impossible
lte_true_pred k_lte_j {k = (S l)} {j = (S i)} with (lte l i)
  lte_true_pred k_lte_j {k = (S l)} {j = (S i)} | lte_l_i = k_lte_j


||| ```
||| Get an LTE after proving True = lte n m
||| ```
lte_true_LTE : True = lte n m -> LTE n m
lte_true_LTE n_lte_m {n = Z} {m = _} = LTEZero
lte_true_LTE Refl {n = (S _)} {m = Z} impossible
lte_true_LTE n_lte_m {n = (S k)} {m = (S j)} with (lte_true_pred n_lte_m)
  lte_true_LTE n_lte_m {n = (S k)} {m = (S j)} | k_lte_j = LTESucc (lte_true_LTE k_lte_j)


using (x:Nat, y:Nat, z:Nat, r:Nat)
  mod_equals_rem :
    {y_non_zero: Not (y = 0)} ->
    {z_equals: z = (x * y) + r} ->
    r = modNatNZ z y y_non_zero

  mod_equals_rem
    {y_non_zero}
    {z = Z} {x = x} {y = y} {r = Z} =
      mod_z_z y_non_zero Refl {x = Z} {y = y}

  mod_equals_rem
    {y_non_zero}
    {z = (S k)} {x = x} {y = Z} {r = Z}
    with (y_non_zero Refl)

    mod_equals_rem
      {y_non_zero}
      {z = (S k)} {x = x} {y = Z} {r = Z}
      | y_zero impossible

  mod_equals_rem
    {z_equals}
    {z = (S k)} {x = x} {y = (S j)} {r = Z}
    with (lte (S k) j) proof sk_lte_j

    mod_equals_rem
      {z_equals}
      {z = (S k)} {x = x} {y = (S j)} {r = Z}
      | False =
        rewrite z_equals in
        rewrite plusZeroRightNeutral (mult x (S j)) in
        -- rewrite multCommutative x (S j) in
        -- rewrite multLeftSuccPlus (S j) x in
        ?help

    mod_equals_rem
      {z_equals}
      {z = (S k)} {x = Z} {y = (S j)} {r = Z}
      | True =
        rewrite z_equals in
        Refl

    mod_equals_rem
      {z = (S k)} {x = (S i)} {y = (S j)} {r = Z}
      | True =
        ?hele
        -- rewrite z_equals in
        -- rewrite plusZeroRightNeutral (mult (S i) (S j)) in ?helhe


  mod_equals_rem
    {z_equals}
    {z = z} {x = x} {y = y} {r = (S k)} =
      rewrite z_equals in
      ?help_2
