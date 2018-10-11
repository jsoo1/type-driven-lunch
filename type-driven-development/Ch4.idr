module Ch4


%default total


data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double


%name Shape shape, shape1, shape2


area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle base height) = base * height
area (Circle radius) = pi * radius * radius


data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture


%name Picture pic, pic1, pic2


rectangle : Picture
rectangle = Primitive (Rectangle 20 10)

circle : Picture
circle = Primitive (Circle 5)

triangle : Picture
triangle = Primitive (Triangle 10 10)

testPicture : Picture
testPicture =
  Combine (Translate 5 5 rectangle)
    (Combine (Translate 35 5 circle)
    (Translate 15 25 triangle))


pictureArea : Picture -> Double
pictureArea (Primitive shape) = area shape
pictureArea (Combine pic1 pic2) = pictureArea pic1 + pictureArea pic2
pictureArea (Rotate _ pic) = pictureArea pic
pictureArea (Translate _ _ pic) = pictureArea pic

{--
data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)


%name Tree tree, tree1


insert : Ord elem => elem -> Tree elem -> Tree elem
insert x Empty = Node Empty x Empty
insert x (Node left val right) with (compare x val)
  insert x (Node left val right) | LT = Node (insert x left) val right
  insert x (Node left val right) | EQ = Node left val right
  insert x (Node left val right) | GT = Node left val (insert x right)
--}


data BSTree : Type -> Type where
     Empty : Ord elem => BSTree elem
     Node : Ord elem =>
            (left : BSTree elem)
            -> (val : elem)
            -> (right : BSTree elem) -> BSTree elem


%name BSTree tree, tree1, tree2


insert : Ord a => a -> BSTree a -> BSTree a
insert x Empty = Node Empty x Empty
insert x (Node left val right) with (compare x val)
  insert x (Node left val right) | LT = Node (insert x left) val right
  insert x (Node left val right) | EQ = Node left val right
  insert x (Node left val right) | GT = Node left val (insert x right)


listToTree : Ord a => List a -> BSTree a
listToTree xs = listToTree' xs Empty
  where
  listToTree' : Ord a => List a -> BSTree a -> BSTree a
  listToTree' [] tree = tree
  listToTree' (x :: xs) tree = listToTree' xs (insert x tree)


treeToList : BSTree a -> List a
treeToList Empty = []
treeToList (Node left val right) = treeToList left ++ [val] ++ treeToList right


data Expr : Type where
     Prim : Int -> Expr
     Add : Expr -> Expr -> Expr
     Sub : Expr -> Expr -> Expr
     Mult : Expr -> Expr -> Expr


%name Expr expr, expr1, expr2


evaluate : Expr -> Int
evaluate (Prim x) = x
evaluate (Add expr expr1) = evaluate expr + evaluate expr1
evaluate (Sub expr expr1) = evaluate expr - evaluate expr1
evaluate (Mult expr expr1) = evaluate expr * evaluate expr1


maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing Nothing = Nothing
maxMaybe Nothing (Just x) = Just x
maxMaybe (Just x) Nothing = Just x
maxMaybe (Just x) (Just y) with (compare x y)
  maxMaybe (Just x) (Just y) | LT = Just y
  maxMaybe (Just x) (Just y) | EQ = Just x
  maxMaybe (Just x) (Just y) | GT = Just x


biggestTriangle : Picture -> Maybe Double
biggestTriangle pic = biggestTriangle' pic Nothing
  where
  biggestTriangle' : Picture -> Maybe Double -> Maybe Double
  biggestTriangle' (Primitive triangle@(Triangle _ _)) x = maxMaybe x (Just (area triangle))
  biggestTriangle' (Primitive (Rectangle y z)) x = x
  biggestTriangle' (Primitive (Circle y)) x = x
  biggestTriangle' (Combine pic pic1) x = maxMaybe (biggestTriangle' pic x) (biggestTriangle' pic1 x)
  biggestTriangle' (Rotate y pic) x = maxMaybe (biggestTriangle' pic x) x
  biggestTriangle' (Translate y z pic) x = maxMaybe (biggestTriangle' pic x) x


prf1 :
  biggestTriangle
    (Combine
      (Primitive (Triangle 2 3))
      (Primitive (Triangle 2 4)))
  = Just 4.0
prf1 = Refl


prf2 :
  biggestTriangle
    (Combine
      (Primitive (Rectangle 1 3))
      (Primitive (Circle 4)))
  = Nothing
prf2 = Refl


data ExternalPower = Electric | Petrol


%name ExternalPower externalPower, externalPower1, externalPower2


data PowerSource : Type where
     Pedal : PowerSource
     External: ExternalPower -> PowerSource


%name PowerSource powerSource, powerSource1, powerSource2


data Vehicle : PowerSource -> Type where
     Unicycle : Vehicle Pedal
     Bicycle : Vehicle Pedal
     Motorcycle : (fuel : Nat) -> (power : ExternalPower) -> Vehicle $ External power
     Car : (fuel : Nat) -> (power : ExternalPower) -> Vehicle $ External power
     Bus : (fuel : Nat) -> (power : ExternalPower) -> Vehicle $ External power
     Tram : (fuel : Nat) -> Vehicle $ External Electric


%name Vehicle vehicle, vehicle1, vehicle2


wheels : Vehicle power -> Nat
wheels Bicycle = 2
wheels Unicycle = 1
wheels (Motorcycle _ _) = 2
wheels (Car _ _) = 4
wheels (Bus _ _) = 4
wheels (Tram fuel) = 12


refuel : Vehicle (External power) -> Vehicle (External power)
refuel Bicycle impossible
refuel Unicycle impossible
refuel (Motorcycle _ Electric) = Motorcycle 45 Electric
refuel (Motorcycle _ Petrol) = Motorcycle 50 Petrol
refuel (Car _ Electric) = Car 75 Electric
refuel (Car _ Petrol) = Car 100 Petrol
refuel (Bus _ Electric) = Bus 140 Electric
refuel (Bus _ Petrol) = Bus 200 Petrol
refuel (Tram _) = Tram 1000
