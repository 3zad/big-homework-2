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
lemma1 y x p xs q ys r = ?lemma1_rhs
 
total
lemma2 :(y : Nat) -> (x : Nat) -> not (compareNat x y == LT) = True -> (xs : List Nat) -> sorted (x :: xs) = True -> (ys : List Nat) -> sorted (y :: ys) = True -> sorted (y :: merge (x :: xs) ys) = True
lemma2 y x p xs q ys w = ?lemma2_rhs

total
sortedProp : (xs: List Nat) -> sorted (sort xs) = True
sortedProp xs = ?sortedProp_rhs

total
invInCons : (x:a) -> (y:a) -> (xs:List a) -> In x (y :: xs) -> Either (x = y) (In x xs)
invInCons x x xs InHere = Left Refl
invInCons x y xs (InThere z) = Right z

inSplitList : Ord a => (x:a) -> (xs:List a) ->
        In x xs -> Either (In x (fst (splitList xs))) (In x (snd (splitList xs)))
inSplitList x [] p = Left p
inSplitList x (z :: []) p = Left p
inSplitList x (z :: (w :: zs)) p with (splitList zs) proof prf
    _ | (v, s) = case invInCons x z (w :: zs) p of
        Left t => rewrite t in Left InHere
        Right t => case invInCons x w zs t of
            Left eq => rewrite eq in Right InHere
            Right inZs => case assert_total (inSplitList x zs inZs) of
                Left inV => rewrite sym (cong fst prf) in Left (InThere inV)
                Right inS => rewrite sym (cong snd prf) in Right (InThere inS)

--splitListIn x [] (Left y) = y
--splitListIn x (z :: []) (Left y) = y
-- splitListIn x (z:: ( w :: zs) ) (Left y) with (splitListIn x zs) | (splitList zs)
--     _ | q | (v, s) = splitListIn_rhs_6 s w zs q y 


in_sorted: Ord a => (x:a) -> (xs:List a) -> In x xs -> In x (sort xs)
in_sorted x [] p = p
in_sorted x [y] p = p
in_sorted x (y :: z :: zs) p with (splitList zs)
    _ | (v, s) with (inSplitList x (y :: z :: zs) p)
        _ | (Left inLeft) = ?in_sorted_left
        _ | (Right inRight) = ?in_sorted_right