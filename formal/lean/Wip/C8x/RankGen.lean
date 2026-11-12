import Formal.Net.CapstoneNetChk
/-! Generator (proves nothing): combinational rank of every channel of the gcd_hw network.
rank c = 0 if c's producer is a link, source or sink; else 1 + max rank of the producer's inputs.
Printed list is pasted into Formal/Net/CapstonePhysRefine.lean as `rkL` and re-checked there by
kernel `decide` (`comb_rank_ok`), so this generator is not trusted. -/
open Formal.Net.CapNet Formal.Net.CapNet.Gcd
def isComb : K NC → Bool
  | .link _ _ => false | .src _ _ _ => false | .sink _ => false | _ => true
def step (r : List Nat) : List Nat :=
  (List.range NC).map fun c =>
    let k := ops.getD (prodT.getD c 0).val (K.sink 0)
    if isComb k then 1 + (k.insC.map (fun i => r.getD i.val 0)).foldl max 0 else 0
def iter : Nat → List Nat → List Nat
  | 0, r => r
  | n + 1, r => iter n (step r)
#eval let r := iter 100 (List.replicate NC 0); (r == step r, r.foldl max 0, r)
