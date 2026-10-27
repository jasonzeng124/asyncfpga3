#check @Array.getElem?_setIfInBounds
#check @Array.size_setIfInBounds
#check @Array.getElem?_replicate
#check @List.reverse_perm
#check @List.Perm.rec
#check @List.foldl_cons
example (a b c : Nat) : min a (min b c) = min (min a c) b := by omega
example (a b c : Nat) : max a (max b c) = max (max a c) b := by omega
