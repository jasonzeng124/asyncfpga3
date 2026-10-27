#check @List.Nodup
#check @List.nodup_cons
#check @List.getD
#check @List.mapIdx
#check @List.getElem?_mapIdx
#check @List.getD_eq_getElem?_getD
#check @List.sum
#check @Nat.and_one_is_mod
#check @List.lookup
#check @List.flatten
#check @Nat.testBit
example : (decide ([1,2,3].Nodup)) = true := by decide +kernel
