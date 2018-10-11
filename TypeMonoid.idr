module TypeMonoid


data Decl : Type where
     (\\) : (left : Type) -> (right : Type) -> Decl


infixr 5 =|=
data Match : Type -> Type where
     (=|=) : Decl -> Match


record MonoidTypeDisj where
  constructor MonoidDisj
  empty : Type
  operator : Type -> Type -> Type
  empty_l : (operator a empty) = a
  empty_r : (operator empty a) = a
  associativity : operator a (operator b c) = operator (operator a b) c


-- types_are_monoids : MonoidTypeDisj
-- types_are_monoids =
--   MonoidDisj ?empty Plus ?empty_l ?empty_r ?associativity


impossible_f : (x : Type) -> (y : Type) -> (a : x) -> (b : y) ->
impossible_f x y = ?eh_1
