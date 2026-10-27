set_option profiler true
set_option maxRecDepth 100000
theorem t1 : ((List.range 100).all (fun s => [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20].contains (s+100) == false)) = true := by decide +kernel
theorem t2 : ((List.range 400).all (fun s => [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20].contains (s+100) == false)) = true := by decide +kernel
def l20 : List Nat := [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]
theorem t3 : ((List.range 400).all (fun s => l20.contains (s+100) == false)) = true := by decide +kernel
def chk : Nat → Bool | 0 => true | n+1 => !(l20.contains (n+100)) && chk n
theorem t4 : chk 400 = true := by decide +kernel
