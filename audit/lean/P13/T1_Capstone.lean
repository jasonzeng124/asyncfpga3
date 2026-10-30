import Formal.Net.CapstoneWitness3
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
  Formal.Net.CapNet.Wit Formal.Net.CapSafe Formal.Net.GcdHw Formal.Net.GcdHw.Gcd

#check @gcd_hw_joint_witness3
#check @gcd_hw_witness3_consistent
#check @gcd_hw_walk
#check @gcd_hw_circuit_safe3
#print axioms gcd_hw_witness3_consistent

-- WalkOK is not vacuous for the witness: the walk reaches an arbiter (amerge) stage.
def arbHits (σ : Fin NC → Nat → Nat) (n : Nat) : Nat :=
  ((List.range n).filter fun p =>
    match (walk σ p).cur with
    | some d => match opAt (consOf d) with
                | .amerge .. => true
                | _ => false
    | none => false).length

theorem walk_hits_arbiter : 0 < arbHits (σY 12 18 yW) 80 := by decide +kernel

-- H_START_ONCE is not met by "start never offered": start rises exactly once by the close.
theorem start_rises_once : cnt (riseB (chW start).req) 474 = 1 := by decide +kernel
