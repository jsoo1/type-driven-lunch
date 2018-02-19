module Plus


data Vector : Nat -> Type -> Type where
     Nil : Vector Z a
     (::) : x -> Vector n x -> Vector (S n) x


concatVect : Vector n x -> Vector m x -> Vector (n + m) x
concatVect [] y = y
concatVect (x :: xs) y = x :: concatVect xs y


lengthVect : Vector n x -> Nat
lengthVect {n} x = n


takeVect : (n:Nat) -> Vector m x -> LTE n m -> Vector n x
takeVect Z [] LTEZero = []
takeVect Z (x :: xs) LTEZero = []
takeVect (S n) (x :: xs) (LTESucc j) = x :: takeVect n xs j
