module Even
%default total


public export
even : Nat -> Bool
even Z = True
even (S Z) = False
even (S (S k)) = even k


public export
even_succ_x_equals_not_even_x : y = even (S x) -> not y = even x
even_succ_x_equals_not_even_x prf {x = Z} {y = False} =
  Refl

even_succ_x_equals_not_even_x prf {x = Z} {y = True} with (uninhabited prf)
  even_succ_x_equals_not_even_x prf | z_odd impossible

even_succ_x_equals_not_even_x prf {x = (S Z)} {y = False} with (uninhabited prf)
  even_succ_x_equals_not_even_x prf {x = (S Z)} {y = False} | two_odd impossible

even_succ_x_equals_not_even_x prf {x = (S Z)} {y = True} =
  Refl

even_succ_x_equals_not_even_x prf {x = (S (S k))} {y = y} with (even k) proof k_even
  even_succ_x_equals_not_even_x prf {x = (S (S k))} {y = y} | False =
    let thing = even_succ_x_equals_not_even_x {x = k} {y = y} in
    let new_thing = thing prf in
    rewrite new_thing in
    rewrite k_even in
    Refl

  even_succ_x_equals_not_even_x prf {x = (S (S k))} {y = y} | True =
    let thing = even_succ_x_equals_not_even_x {x = k} {y = y} in
    let new_thing = thing prf in
    rewrite new_thing in
    rewrite k_even in
    Refl
