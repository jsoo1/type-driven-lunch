module Ch3


import Data.Vect


%default total


transMat : Vect n (Vect m a) -> Vect m (Vect n a)
transMat [] = replicate _ []
transMat (row :: rows) = zipWith (::) row $ transMat rows


addMat : Num num => Vect n (Vect m num) -> Vect n (Vect m num) -> Vect n (Vect m num)
addMat = zipWith (zipWith (+))


multMat : Num num => Vect n (Vect m num) -> Vect m (Vect p num) -> Vect n (Vect p num)
multMat ma mb with (transMat mb)
  multMat ma mb | mb_trans =
    map (\ row => map (foldl (+) 0 . zipWith (*) row) mb_trans) ma
