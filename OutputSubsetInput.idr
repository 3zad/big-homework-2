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
splitListIn_rhs_6 : Ord a => (s : List a) -> (w : a) -> (zs : List a) -> (Either (In x v) (In x s) -> In x zs) -> In x (z :: v) -> In x (z :: (w :: zs))
splitListIn_rhs_6 s w za p InHere = InHere
splitListIn_rhs_6 s w za p (InThere y) = InThere (InThere (p (Left y)))

total
splitListIn_rhs_7 : Ord a => (v : List a) -> (z : a) -> (zs : List a) -> (Either (In x v) (In x s) -> In x zs) -> In x (w :: s) -> In x (z :: (w :: zs))
splitListIn_rhs_7 v z xs p InHere = InThere InHere
splitListIn_rhs_7 v z xs p (InThere y) = InThere (InThere (p (Right y)))

total
splitListIn : Ord a => (x:a) -> (xs:List a) ->
        Either (In x (fst (splitList xs))) (In x (snd (splitList xs))) -> In x xs
splitListIn x [] (Left y) = y
splitListIn x (z :: []) (Left y) = y
splitListIn x (z:: ( w :: zs) ) (Left y) with (splitListIn x zs) | (splitList zs)
    _ | q | (v, s) = splitListIn_rhs_6 s w zs q y 
splitListIn x [] (Right y) = y
splitListIn x (z :: []) (Right y) = InThere y
splitListIn x (z:: ( w :: zs) ) (Right y) with (splitListIn x zs) | (splitList zs)
    _ | q | (v, s) = splitListIn_rhs_7 v z zs q y

total
invInCons : (x:a) -> (y:a) -> (xs:List a) -> In x (y :: xs) -> Either (x = y) (In x xs)
invInCons x x xs InHere = Left Refl
invInCons x y xs (InThere z) = Right z

total
merge_in_rhs_7 : Ord a => (x:a) -> (y:a) -> (xs: List a) -> (ys: List a) -> (z:a) -> In x (merge (y :: xs) ys) -> Either (In x (y :: xs)) (In x ys) -> Either (In x (y :: xs)) (In x (z :: ys))
merge_in_rhs_7 x y xs ys z p (Left w) = Left w
merge_in_rhs_7 x y xs ys z p (Right w) = Right (InThere w)

total
merge_in_rhs_8 : Ord a => (x:a) -> (y:a) -> (xs: List a) -> (ys: List a) -> (z : a) -> In x (merge xs (z :: ys)) -> Either (In x xs) (In x (z :: ys)) -> Either (In x (y :: xs)) (In x (z :: ys))
merge_in_rhs_8 x y xs ys z p (Left w) = Left (InThere w)
merge_in_rhs_8 x y xs ys z p (Right w) = Right w

total
merge_in : Ord a => (x:a) -> (xs:List a) -> (ys:List a) -> In x (merge xs ys) -> Either (In x xs) (In x ys)
merge_in x [] ys p = Right p
merge_in x (y :: xs) [] p = Left p
merge_in x (y :: xs) (z :: ys) p with (not (compare y z == GT))
    _ | False with (invInCons x _ _ p)
        _ | (Left w) = rewrite w in Right InHere
        _ | (Right w) = 
            let r = assert_total (merge_in x _ _ w) in
            merge_in_rhs_7 x y xs ys z w r
    _ | True with (invInCons x _ _ p)
        _ | (Left w) = rewrite w in Left InHere
        _ | (Right w) = 
            let r = assert_total (merge_in x _ _ w) in
            merge_in_rhs_8 x y xs ys z w r

total
sorted_in_rhs_5 : Ord a => (z : a) -> (v : List a) -> In x (merge (sort (y :: w)) (sort (z :: v))) -> (zs : List a) -> (Either (In x w) (In x v) -> In x zs) -> In x (y :: w) -> In x (sort (y :: w)) -> In x (y :: (z :: zs))
sorted_in_rhs_5 z v o p w InHere t = InHere
sorted_in_rhs_5 z v o p w (InThere s) t = InThere (InThere (w (Left s)))

total
sorted_in_rhs_6 : Ord a => (y : a) -> (w : List a) -> In x (merge (sort (y :: w)) (sort (z :: v))) -> (zs : List a) -> (Either (In x w) (In x v) -> In x zs) -> In x (z :: v) -> In x (sort (z :: v)) -> In x (y :: (z :: zs))
sorted_in_rhs_6 y w p o e InHere t = InThere InHere
sorted_in_rhs_6 y w p o e (InThere s) t = InThere (InThere (e (Right s)))

total
sorted_in: Ord a => (x:a) -> (xs:List a) -> In x (sort xs) -> In x xs
sorted_in x [] p = p
sorted_in x (y :: []) p = p
sorted_in x (y :: (z :: zs)) p with (splitListIn x zs) | (splitList zs)
    _ | q | (w, v) with (merge_in x _ _ p)
        _ | (Left s) with ( assert_total (sorted_in x (y :: w) s))
            _ | l = sorted_in_rhs_5 z v p zs q l s
        _ | (Right s) with ( assert_total (sorted_in x (z :: v) s))
            _ | l = sorted_in_rhs_6 y w p zs q l s