data Tree = Empty | Branch Tree Tree


total mirror : Tree -> Tree -> Bool
mirror t t' = case (t, t') of
       (Empty, Empty) => True
       (Branch l r, Branch l' r') => (mirror l r') && (mirror r l')
       (_, _)  => False

total symmetric : Tree -> Bool
symmetric t = case t of
          Empty => True
          (Branch l r) => mirror l r


t : Tree
t = (Branch
      (Branch
        (Branch Empty
          (Branch Empty Empty))
        (Branch Empty Empty))
      (Branch
        (Branch Empty Empty)
        (Branch
          (Branch Empty Empty)
          Empty)))
