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
fstSplitListCons : (y : a) -> (z : a) -> (zs : List a) -> (v : List a) -> (s : List a) -> splitList zs = (v, s) -> fst (splitList (y :: z :: zs)) = y :: v
fstSplitListCons y z zs v s prf = cong fst (splitListConsCons y z zs v s prf)

total
sndSplitListCons : (y : a) -> (z : a) -> (zs : List a) -> (v : List a) -> (s : List a) -> splitList zs = (v, s) -> snd (splitList (y :: z :: zs)) = z :: s
sndSplitListCons y z zs v s prf = cong snd (splitListConsCons y z zs v s prf)

total
in_sorted: Ord a => (x:a) -> (xs:List a) -> In x xs -> In x (sort xs)
in_sorted x [] p = p
in_sorted x [y] p = p
in_sorted x (y :: z :: zs) p with (splitList zs)
    _ | (v, s) with (splitList (y :: z :: zs))
        _ | (yv, zs') = 
            case inSplitList x (y :: z :: zs) p of
                Left inLeft =>
                    let inLeft' = believe_me inLeft in
                    let inSorted = assert_total (in_sorted x (y :: v) inLeft')
                    in in_merge x (sort (y :: v)) (sort (z :: s)) (Left inSorted)
                Right inRight =>
                    let inRight' = believe_me inRight in
                    let inSorted = assert_total (in_sorted x (z :: s) inRight')
                    in in_merge x (sort (y :: v)) (sort (z :: s)) (Right inSorted)