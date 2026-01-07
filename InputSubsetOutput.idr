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
mergeSorted_rhs_3 : (x : Nat) -> (y : Nat) -> compare x y /= GT = True -> not (compareNat x y == GT) = True
mergeSorted_rhs_3 x y prf with (compare x y) proof cmp
    _ | LT = Refl
    _ | EQ = Refl  

total  
extractTailSorted : (x : Nat) -> (xs : List Nat) -> sorted (x :: xs) = True -> sorted xs = True
extractTailSorted x [] prf = Refl
extractTailSorted x (y :: ys) prf with (compare x y /= GT) proof p | (sorted (y :: ys)) proof q
    _ | True | True = Refl
    _ | True | False = absurd prf
    _ | False | _ = absurd prf

total
mergeSorted_rhs_4 : (x : Nat) -> (y : Nat) -> compare x y /= GT = False -> not (compareNat x y == LT) = True
mergeSorted_rhs_4 x y prf with (compare x y) proof cmp
    _ | GT = Refl
    

total
mergeSorted : (xs : List Nat) -> sorted xs = True -> (ys : List Nat) -> sorted ys = True -> sorted (merge xs ys) = True
mergeSorted [] p ys q = q
mergeSorted xs p [] q with (xs)
    _ | [] = p
    _ | (x :: xs') = p
mergeSorted (x :: xs) p (y :: ys) q with (compare x y /= GT) proof prf
    _ | True = lemma1 y x (mergeSorted_rhs_3 x y prf) xs p ys q
    _ | False = lemma2 y x (mergeSorted_rhs_4 x y prf) xs p ys q

total
sortedProp : (xs: List Nat) -> sorted (sort xs) = True
sortedProp [] = Refl
sortedProp [x] = Refl
sortedProp (x :: y :: zs) with (splitList zs) proof prf
    _ | (v, s) = 
        let sortedLeft = assert_total (sortedProp (x :: v))
            sortedRight = assert_total (sortedProp (y :: s))
        in mergeSorted (sort (x :: v)) sortedLeft (sort (y :: s)) sortedRight

total
invInCons : (x:a) -> (y:a) -> (xs:List a) -> In x (y :: xs) -> Either (x = y) (In x xs)
invInCons x x xs InHere = Left Refl
invInCons x y xs (InThere z) = Right z

total
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

total
in_merge : Ord a => (x:a) -> (xs:List a) -> (ys:List a) -> Either (In x xs) (In x ys) -> In x (merge xs ys)
in_merge x [] ys (Left p) impossible
in_merge x [] ys (Right p) = p
in_merge x (y :: xs) [] (Left p) = p
in_merge x (y :: xs) [] (Right p) impossible
in_merge x (y :: xs) (z :: ys) e with (compare y z /= GT)
    _ | True = case e of
        Left InHere => InHere
        Left (InThere rest) => InThere (assert_total (in_merge x xs (z :: ys) (Left rest)))
        Right p => InThere (assert_total (in_merge x xs (z :: ys) (Right p)))
    _ | False = case e of
        Left p => InThere (assert_total (in_merge x (y :: xs) ys (Left p)))
        Right InHere => InHere
        Right (InThere rest) => InThere (assert_total (in_merge x (y :: xs) ys (Right rest)))

total
splitListConsCons : (y : a) -> (z : a) -> (zs : List a) -> (v : List a) -> (s : List a) -> splitList zs = (v, s) -> splitList (y :: z :: zs) = (y :: v, z :: s)
splitListConsCons y z zs v s prf = rewrite prf in Refl

total
in_sorted: Ord a => (x:a) -> (xs:List a) -> In x xs -> In x (sort xs)
in_sorted x [] p = p
in_sorted x [y] p = p
in_sorted x (y :: z :: zs) p with (splitList zs) proof prf
    _ | (v, s) =
        let splitEq = splitListConsCons y z zs v s prf in
        case inSplitList x (y :: z :: zs) p of
            Left inLeft => 
                let inLeft' = rewrite sym (cong fst splitEq) in inLeft in
                let inSorted = assert_total (in_sorted x (y :: v) inLeft')
                in in_merge x (sort (y :: v)) (sort (z :: s)) (Left inSorted)
            Right inRight =>
                let inRight' = rewrite sym (cong snd splitEq) in inRight in
                let inSorted = assert_total (in_sorted x (z :: s) inRight')
                in in_merge x (sort (y :: v)) (sort (z :: s)) (Right inSorted)
