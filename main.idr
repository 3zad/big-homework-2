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
 
total
sortedProp : (xs: List Nat) -> sorted (sort xs) = True
sortedProp xs = ?sortedProp_rhs
 
data In : {0 T:Type} -> (x:T) -> (xs: List T) -> Type where
    InHere: {0 T:Type} -> {x:T} -> {xs: List T} -> In x (x::xs)
    InThere: {0 T:Type} -> {x:T} -> {y:T} -> {xs: List T} -> In x xs -> In x (y::xs)
 
sorted_in_rhs_5 : Ord a => (z : a) -> (v : List a) -> In x (merge (sort (y :: w)) (sort (z :: v))) -> (zs : List a) -> (Either (In x w))
sorted_in_rhs_5 z v o p w InHere t = InHere
sorted_in_rhs_5 z v o p w (InThere s) t = InThere ( InThere (w (Left s)) )

total
sorted_in: Ord a => (x:a) -> (xs:List a) -> In x (sort xs) -> In x xs
sorted_in x [] p = ?impossible
sorted_in x (y :: []) p = p
sorted_in x (y :: ( z :: zs )) p with (splitListIn x zs) | (splitList zs)
    _ | q | (w, v) with (merge_in x _ _ p)
        _ | (Left s) with (sorted_in x _ s)
            _ | l = sorted_in_rhs_5 z v p zs q l s
        _ | (Right s) with (sorted_in x _ s)
            _ | l = sorted_in_rhs_6 y w p zs q l s

total
in_sorted: Ord a => (x:a) -> (xs:List a) -> In x xs -> In x (sort xs)
in_sorted x [] p = ?impossible
in_sorted x (y :: []) p = p
in_sorted x (y :: ( z :: zs )) p = ?www

total
lemma1 : (y : Nat) -> (x : Nat) -> not (compareNat x y == GT)  = True -> (xs : List Nat) -> sorted (x :: xs) = True -> (ys : List Nat) -> sorted (y :: ys) = True -> sorted (x :: merge xs (y :: ys)) = True
lemma1 y x p xs q ys r  = ?lemma1_rhs
 
total
lemma2 :(y : Nat) -> (x : Nat) -> not (compareNat x y == LT) = True -> (xs : List Nat) -> sorted (x :: xs) = True -> (ys : List Nat) -> sorted (y :: ys) = True -> sorted (y :: merge (x :: xs) ys) = True
lemma2 y x p xs q ys w = ?lemma2_rhs