module Set


import Data.Fin


%default total


||| The `on` combinator
on : (a -> a -> b) -> (c -> a) -> c -> c -> b
on f g x y = f (g x) (g y)


infixl 0 |>
||| The pipeline operator (flip $).
(|>) : a -> (a -> b) -> b
x |> f = f x


infixr 9 ..
||| The blackbird combinator
(..) : (c -> d) -> (a -> b -> c) -> a -> b -> d
(..) = (.).(.)


||| Bifunctors
interface Bifunctor (f : Type -> Type -> Type) where
  ||| Lift two functions into a bifunctor
  bimap : (m : a -> b) -> (n : c -> d) -> f a c -> f b d


Bifunctor Pair where
  bimap f g (x, y) = (f x, g y)


||| Represents a set. Implemented as a binary search tree.
data Set : Fin n -> Type -> Type where
  ||| The empty set.
  Empty : Set FZ setType
  ||| An element of a set.
  Node :
    Ord setType =>
    (val : setType) ->
    (maxDepth : Fin n) ->
    (lessers : Set maxDepth setType) ->
    (greaters : Set maxDepth setType) ->
    Set (FS maxDepth) setType


%name Set set, set1, set2


||| Show a Set with maximum depth of twelve
Show a => Show (Set d a) where
  show Empty =
    "{}"

  show set =
    show' set 12 ""
      where
        show' :
          Show a =>
          Set d a ->
          (depth : Nat) ->
          (padding : String) ->
          String

        show' Empty _ _ =
          "{ }"

        show' (Node val depth lessers greaters) Z padding =
          "{ ... Truncated. Maximum show depth reached. }"

        show' (Node val depth lessers greaters) (S k) padding =
          "\n" ++ padding ++ "{ val = " ++ show val
          ++ "\n" ++ padding ++ ", lessers = " ++ show' lessers k (padding ++ "  ")
          ++ "\n" ++ padding ++ ", greaters = " ++ show' greaters k (padding ++ "  ")
          ++ "\n" ++ padding ++ "}"


||| The singleton set.
singleton : Ord a => a -> Set (FS FZ) a
singleton x =
  Node x FZ Empty Empty


||| Foldl for sets
Foldable (Set _) where
  foldr func init Empty =
    init

  foldr func init (Node val depth lessers greaters) =
    func val (foldr func (foldr func init lessers) greaters)

  foldl func init Empty =
    init

  foldl func init (Node val depth lessers greaters) =
    foldl func (foldl func (func init val) lessers) greaters


||| Value of a node
valOf : Set (FS d) a -> a
valOf (Node val d lessers greaters) = val


||| Children of a node
childrenOf : Set (FS d) a -> (Set d a, Set d a)
childrenOf (Node val d lessers greaters) = (lessers, greaters)


||| Set membership in a set.
member : Ord a => a -> Set depth a -> Bool
member x = foldl (\acc, elem => compare x elem |> (EQ ==) |> (acc ||)) False


-- help :
--   Ord a =>
--   (x : a) ->
--   (set : Set _ a) ->
--   (x_not_member : False = x `member` set) ->
--   Not (EQ = compare x val)
-- help x set x_not_member = ?help_rhs


||| If an element is not in a set, then it is not in any of its children
not_member_transitive :
  Ord a =>
  (x : a) ->
  (set : Set _ a) ->
  (x_not_in_set : False = member x set) ->
  (False, False) = bimap `on` (member x) (childrenOf set)
not_member_transitive x set x_not_in_set with (bimap `on` (member x) (childrenOf set)) proof mem_children
  not_member_transitive x set x_not_in_set | (mem_lessers, mem_greaters) = ?help


||| Insert an element into a set.
insert :
  Ord a =>
  (x : a) ->
  (set : Set d a)->
  if x `member` set
  then Set d a
  else Set (FS d) a
insert x set {d} with (x `member` set) proof x_in_set
  insert x set {d = d} | True =
    set

  insert x Empty {d = FZ} | False =
    singleton x

  insert x (Node val depth lessers greaters) {d = (FS {k} depth)} | False with (x `compare` val) proof x_comp_val
    insert x (Node val depth lessers greaters) {d = (FS {k} depth)} | False | LT =
      let thing = insert x lessers in
      Node val (FS depth) ?huh ?help

    insert x (Node val depth lessers greaters) {d = (FS {k} depth)} | False | GT =
      ?insert_rhs_rhs_3_rhs_3

    insert x (Node val depth lessers greaters) {d = (FS {k} depth)} | False | EQ =
      ?ehhh


-- ||| Create a set from a list of elements.
-- fromList : Ord a => Foldable f => f a -> Set a
-- fromList = foldl (flip insert) Empty


-- [Conjuctive] Ord a => Semigroup (Set a) where
--   (<+>) = intersect


-- [Disjunctive] Ord a => Semigroup (Set a) where
--   (<+>) = union

-- ||| Rotate two branches of a (non empty) binary search tree to the left
-- rotateLeft : Ord a => Set a -> Set a
-- rotateLeft Empty = Empty
-- rotateLeft (Node val lessers right) with (right)

--   rotateLeft (Node val lessers right) | Empty =
--     Node val lessers right

--   rotateLeft (Node val lessers right) | (Node subVal betweens greaters) =
--     Node subVal (Node val lessers betweens) greaters


-- -- ||| Rotate two branches of a (non empty) binary search tree to the right
-- rotateRight : Ord a => Set a -> Set a
-- rotateRight Empty = Empty
-- rotateRight (Node val left greaters) with (left)

--   rotateRight (Node val left greaters) | Empty =
--     Node val left greaters

--   rotateRight (Node val left greaters) | (Node subVal lessers betweens) =
--     Node subVal lessers (Node val betweens greaters)


{- Proofs about Sets -}


-- ||| Get the value at a node of a binary search tree
-- valOf : Ord a => (set : Set a ) -> Not (Empty = set) -> a
-- valOf Empty set_non_empty {a} with (set_non_empty Refl)
--   valOf Empty set_non_empty | set_empty impossible

-- valOf (Node val _ _) _ = val


-- ||| Get the left child of a set
-- leftChild : Ord a => (set : Set a) -> Not (Empty = set) -> Set a
-- leftChild (Node val left right) _ = left
-- leftChild Empty set_non_empty {a} with (set_non_empty Refl)
--   leftChild Empty set_non_empty | set_empty impossible


-- ||| Get the right child of a set
-- rightChild : Ord a => (set : Set a) -> Not (Empty = set) -> Set a
-- rightChild (Node val _ right) _ = right
-- rightChild Empty set_non_empty {a} with (set_non_empty Refl)
--   rightChild Empty set_non_empty | set_empty impossible


-- ||| Get the left child value of a node in a binary search tree
-- leftChildVal :
--   Ord a => (set : Set a) ->
--   (parent_non_empty : Not (Empty = set)) ->
--   (child_non_empty : Not (Empty = (leftChild set parent_non_empty))) ->
--   a
-- leftChildVal Empty parent_non_empty _ {a} with (parent_non_empty Refl)
--   leftChildVal Empty parent_non_empty _ | parent_empty impossible

-- leftChildVal (Node val left right) _ child_non_empty = valOf left child_non_empty


-- ||| Get the right child value of a node in a binary search tree
-- rightChildVal :
--   Ord a => (set : Set a) ->
--   (parent_non_empty : Not (Empty = set)) ->
--   (child_non_empty : Not (Empty = (rightChild set parent_non_empty))) ->
--   a
-- rightChildVal Empty parent_non_empty _ {a} with (parent_non_empty Refl)
--   rightChildVal Empty parent_non_empty _ | parent_empty impossible

-- rightChildVal (Node val left right) _ child_non_empty = valOf right child_non_empty


-- ||| Left rotation of non-empty set results in non-empty set
-- rotate_left_non_empty :
--   Ord a => (set : Set a) ->
--   (set_non_empty : Not (Empty = set)) ->
--   (Node _ _ _) = rotateLeft set set_non_empty
-- rotate_left_non_empty Empty set_non_empty {a} with (set_non_empty Refl)
--   rotate_left_non_empty Empty set_non_empty {a} | set_empty impossible

-- rotate_left_non_empty (Node val left right) set_non_empty  = ?absurd_2



-- ||| Proof that all elements of a left branch of a binary search tree node are less than the node value
-- binary_search_left_lt : Ord a => (set : Set a) ->
--   (parent_non_empty : Not (Empty = set)) ->
--   (child_non_empty : Not (Empty = (leftChild set parent_non_empty))) ->
--   LT = compare (leftChildVal set parent_non_empty child_non_empty) (valOf set parent_non_empty)
-- binary_search_left_lt set parent_non_empty child_non_empty = ?binary_search_left_lt_rhs


-- ||| Left rotation preserves ordering
-- rotation_preserves_order : Ord a => (set : Set a) ->
--   (parent_non_empty : Not (Empty = set)) ->
--   (child_non_empty : Not (Empty = rightChild set parent_non_empty)) ->
--   LT = compare (valOf set parent_non_empty) (rightChildVal set parent_non_empty child_non_empty) ->
--   LT = compare (valOf (rotateLeft set)) (rightChildVal (rotateLeft set) parent_non_empty child_non_empty)
