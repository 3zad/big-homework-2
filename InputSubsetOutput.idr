total
splitList : List a -> (List a, List a)
splitList [] = ([],[])
splitList [x] = ([x], [])
splitList (x::y::zs) =
    let (xs, ys) = splitList zs in
    (x::xs, y::ys)
 
total
merge : Ord a => List a -> List a -> List a
merge [] xs = xs
merge xs [] = xs
merge (x::xs) (y::ys) = if compare x y /= GT then x :: merge xs (y::ys) else y :: merge (x::xs) ys
 
total
sort : Ord a => List a -> List a
sort [] = []
sort [x] = [x]
sort (x::y::zs) =
    let (xs, ys) = splitList zs in
    merge (assert_total (sort (x::xs))) (assert_total (sort (y::ys)))
 
total
sorted : Ord a => List a -> Bool
sorted [] = True
sorted [_] = True
sorted (x::y::xs) = compare x y /= GT  && sorted (y::xs)
 
data In : {0 T:Type} -> (x:T) -> (xs: List T) -> Type where
    InHere: {0 T:Type} -> {x:T} -> {xs: List T} -> In x (x::xs)
    InThere: {0 T:Type} -> {x:T} -> {y:T} -> {xs: List T} -> In x xs -> In x (y::xs)

total
lemma1 : (y : Nat) -> (x : Nat) -> not (compareNat x y == GT)  = True -> (xs : List Nat) -> sorted (x :: xs) = True -> (ys : List Nat) -> sorted (y :: ys) = True -> sorted (x :: merge xs (y :: ys)) = True
lemma1 y x p xs q ys r  = ?lemma1_rhs
 
total
lemma2 :(y : Nat) -> (x : Nat) -> not (compareNat x y == LT) = True -> (xs : List Nat) -> sorted (x :: xs) = True -> (ys : List Nat) -> sorted (y :: ys) = True -> sorted (y :: merge (x :: xs) ys) = True
lemma2 y x p xs q ys w = ?lemma2_rhs

total
sortedProp : (xs: List Nat) -> sorted (sort xs) = True
sortedProp xs = ?sortedProp_rhs

total
in_sorted: Ord a => (x:a) -> (xs:List a) -> In x xs -> In x (sort xs)
in_sorted x xs p = ?in_sorted_rhs