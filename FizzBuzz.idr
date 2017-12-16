module InterviewQuestion
%default total


-- Numbers
data FBNum : Type where
     FizzNum : (n:Nat) -> (m:Nat) -> (m_non_zero: Not (m = Z)) -> (mult_of_three: n = 3 * m)  -> FBNum
     BuzzNum : (n:Nat) -> (m:Nat) -> (m_non_zero: Not (m = Z)) -> (mult_of_five: n = 5 * m)  -> FBNum
     FizzBuzzNum : (n:Nat) -> (m:Nat) -> (m_non_zero: Not (m = Z)) -> (mult_of_fifteen: n = 15 * m) -> FBNum


||| ```
||| Get the next fizzbuzz number
||| X - Fizz
||| Y - Buzz
||| Z - Fizzbuzz
||| 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14
||| Z - - X - Y X - - X  Y  - X  -  -
||| ```
nextFBNum : FBNum -> FBNum
nextFBNum fb = FizzNum 9 3 SIsNotZ Refl


-- data FB : Nat -> Type where
--      Nil : Z = n -> FB n
--      Fizz : l = 3 * k -> FB (fizzbuzz l) -> FB l
--      Buzz : (n:Nat) -> Z = modNatNZ n 5 SIsNotZ -> FB (fizzbuzz n) -> FB n
--      FizzBuzz : (n:Nat) -> Z = modNatNZ n 15 SIsNotZ -> FB (fizzbuzz n) -> FB n

-- fizzbuzz : (n:Nat) -> IO ()
-- fizzbuzz n =


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


using (x:Nat, y:Nat, z:Nat)
  mult_div_inverse :
    {y_non_zero: Not (y = Z)} ->
    {z_equals: z = x * y} ->
    divNatNZ x y y_non_zero = x

  mult_div_inverse
    {y_non_zero}
    {x = Z} {y = y} {z = z}
    with (divNatNZ 0 y y_non_zero) proof z_zero

    mult_div_inverse
      {y_non_zero}
      {x = Z} {y = Z} {z = z}
      | z_div_y
      with (y_non_zero Refl)

      mult_div_inverse
        {x = Z} {y = Z} {z = z}
        | z_div_y
        | y_zero impossible

    mult_div_inverse
      {y_non_zero}
      {x = Z} {y = (S k)} {z = z}
      | z_div_y
      with (divNatNZ Z (S k) y_non_zero)

      mult_div_inverse
        {y_non_zero}
        {x = Z} {y = (S k)} {z = z}
        | z_div_y
        | Z =
          rewrite z_zero in
          Refl

      mult_div_inverse
        {y_non_zero}
        {x = Z} {y = (S k)} {z = z}
        | z_div_y
        | (S j) =
          rewrite z_zero in
          Refl

  mult_div_inverse
    {y_non_zero}
    {x = (S k)} {y = Z} {z = z}
    with (y_non_zero Refl)

    mult_div_inverse
      {y_non_zero}
      {x = (S k)} {y = Z} {z = z}
      | y_zero impossible

  mult_div_inverse
    {y_non_zero}
    {x = (S k)} {y = (S j)} {z = z}
    with (lte (S k) j) proof sk_lte_j

    mult_div_inverse
      {y_non_zero}
      {x = (S k)} {y = (S j)} {z = z}
      | False
      with (divNatNZ (S k) (S j) y_non_zero) proof sk_divnat_sj

      mult_div_inverse
        {y_non_zero}
        {x = (S k)} {y = (S j)} {z = z}
        | False
        | Z
        with (ite_false_x_y_y sk_lte_j sk_divnat_sj) proof something_p

        mult_div_inverse
          {y_non_zero = _}
          {x = (S _)} {y = (S _)} {z = _}
          | False
          | Z
          | Refl impossible

      mult_div_inverse
        {y_non_zero}
        {x = (S k)} {y = (S j)} {z = z}
        | False
        | (S i)
        with (ite_false_x_y_y sk_lte_j sk_divnat_sj) proof sk_div'_sj_prf

        mult_div_inverse
          {y_non_zero}
          {x = (S k)} {y = (S j)} {z = z}
          | False
          | (S i)
          | sk_div'_sj =
            ?heell
            -- rewrite sym sk_div'_sj in
            -- ?heeellll

    mult_div_inverse
      {y_non_zero}
      {x = (S k)} {y = (S j)} {z = z}
      | True =
        ?hldhder
