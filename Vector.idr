
true : 5 = 5
true = Refl


data Vector : Nat -> Type -> Type where
Nil : Vector Z a
(::) : a -> Vector n a -> Vector (S n) a


total zipWith : (a -> a -> b) -> Vector n a -> Vector n a -> Vector n b
zipWith f [] [] = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys


data InRange : Nat -> Nat -> Nat -> Type where
betweenLowHigh :
(x:Nat) ->
(low:Nat) ->
(hi:Nat) ->
LTE x hi ->
GTE x low ->
InRange x low hi


gte3lte5 : InRange 4 3 5
gte3lte5 = let res = betweenLowHigh 4 3 5 ?lte ?gte in ?help


-- Haskell version of a list declaration
-- data List a = Nil | Cons a (List a)
--       ^^  ^    ^    ^^^
--      type var term term
--
-- example: Cons 5 (Cons 4 (Cons 3 (Cons 2 (Cons 1 (Cons 0 (Nil)))))) : List Int
-- sugar: [5, 4, 3, 2, 1]
