module Plus

%default total


minusXPlusYYX : (x:Nat) -> (y:Nat) -> x = minus (x + y) y
minusXPlusYYX x Z =
  rewrite minusZeroRight (plus x Z) in
  rewrite plusZeroRightNeutral x in
  Refl
minusXPlusYYX x (S k) =
  rewrite sym (plusSuccRightSucc x k) in
  minusXPlusYYX x k


minusPlusInverse :
  (x:Nat) ->
  (y:Nat) ->
  (z:Nat) ->
  LTE x z ->
  z = x + y ->
  z - x = y
minusPlusInverse x y (x + y) lte_x_z Refl =
  rewrite plusCommutative x y in
  rewrite minusXPlusYYX y x in
  Refl
