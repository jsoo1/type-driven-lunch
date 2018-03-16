module Playground


-- succInjective : (left : Nat) -> (right : Nat) -> (p : S left = S right) -> (left = right)
-- succInjective Z Z _ = Refl
-- succInjective Z (S _) Refl impossible
-- succInjective (S k) Z p = ?succInjective_rhs_1
-- succInjective (S k) (S j) p = ?succInjective_rhs_5

succInjective : (left : Nat) -> (right : Nat) -> (p : S left = S right) -> (left = right)
succInjective _ _ Refl = Refl
