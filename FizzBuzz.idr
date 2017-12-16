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

