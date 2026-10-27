import Formal.Net.Capstone
import Formal.Cells.ArbOverlapRace
import Formal.Net.OpsLive
import Formal.Timing.RtFbGcd

/-! Audit P4 (claude/formal eecc6f7): checks on the c5c6d8b..HEAD headline theorems. -/

namespace AuditP4
open Formal.Net Formal.Net.Ops Formal.Net.Handshake

/-! ## 1. `gcd_hw_conditional` carries no gcd content

It is quantified over an ARBITRARY network `N`, channels and equations; `a b` occur only
inside the premise `O_SOLUTION`. Instantiating `a := g, b := 0` turns it into the
generic "a solution with constant out-stream g forces every latched value to be g", for
ANY constant g, i.e. `latched_const`.1. -/
theorem cond_any_const {C O : Type} (g : Nat) (N : Net C O) (ch : C → Chan)
    (E : O → (C → Nat → Nat) → Prop)
    (H_CELLS : ∀ o, OpProto ch (N.ins o) (N.outs o) ∧ OpData ch (N.ins o) (N.outs o) (E o))
    (H_BUNDLE : ∀ c, Held (ch c)) (out0 : C)
    (O_SOLUTION : ∃ ref : C → Nat → Nat, (∀ o, E o ref) ∧ ∀ k, ref out0 k = g) :
    ∀ k e, TokAt (ch out0) k e → (ch out0).dat e = g := by
  have := Formal.Net.Capstone.gcd_hw_conditional g 0 N ch E H_CELLS H_BUNDLE out0
    (by simpa [Nat.gcd_zero_right] using O_SOLUTION)
  simpa [Nat.gcd_zero_right] using this

/-- ... and the "gcd" one is literally `latched_const` with g := Nat.gcd a b. -/
example {C O : Type} (a b : Nat) (N : Net C O) (ch : C → Chan)
    (E : O → (C → Nat → Nat) → Prop)
    (H_CELLS : ∀ o, OpProto ch (N.ins o) (N.outs o) ∧ OpData ch (N.ins o) (N.outs o) (E o))
    (H_BUNDLE : ∀ c, Held (ch c)) (out0 : C)
    (O_SOLUTION : ∃ ref : C → Nat → Nat, (∀ o, E o ref) ∧ ∀ k, ref out0 k = Nat.gcd a b) :
    Formal.Net.Capstone.gcd_hw_conditional a b N ch E H_CELLS H_BUNDLE out0 O_SOLUTION =
    (Formal.Net.Capstone.latched_const N ch E (fun o => (H_CELLS o).1) H_BUNDLE
      (fun o => (H_CELLS o).2) out0 _ O_SOLUTION).1 := rfl

/-! ## 4. ArbOverlapRace: the 305 ps witness depends on q entering ugrant on A5

Same rig, same routes, same detector pins, but q on ugrant pin A3 (SLICEL slow-max site
pin 344 ps, O5(A3) 150, O6 124): b5 = 295+344+150 = 789, b6 = 295+344+124 = 763.
`handover12` gives raw high exactly on [f+s1+e2+b6, min(f+e1+a1, f+s1+e1+b5)) =
[1935, 2008): 73 ps, which does NOT pass a 203 ps filter. -/
open Formal.Cells.ArbOverlapRace Formal.Cells.ArbBinary in
def a3D : Dl := { slowD with b5 := 789, b6 := 763 }

open Formal.Cells.ArbOverlapRace Formal.Cells.ArbBinary in
theorem a3_overlap (r1 r2 q g1 g2 raw : Sig) (hR : Rig a3D r1 r2 q g1 g2 raw)
    (hr1 : ∀ t, r1 t = decide (t < 0)) (hr2 : ∀ t, r2 t = true)
    (hq0 : ∀ t, t < 0 + a3D.s1 → q t = true) (t : Int) :
    raw t = true ↔ 1935 ≤ t ∧ t < 2008 := by
  have := (handover12 hR 0 hr1 hr2 hq0).2 t
  simp only [a3D, slowD] at this
  rw [this]; omega

open Formal.Cells.ArbOverlapRace Formal.Cells.ArbBinary in
/-- With q on A3 the same handover does not pass the 203 ps filter. -/
theorem a3_no_pass (r1 r2 q g1 g2 raw : Sig) (hR : Rig a3D r1 r2 q g1 g2 raw)
    (hr1 : ∀ t, r1 t = decide (t < 0)) (hr2 : ∀ t, r2 t = true)
    (hq0 : ∀ t, t < 0 + a3D.s1 → q t = true) (c0 : Int) :
    ¬ ∃ t, (raw (t - c0) && raw (t - c0 - 203)) = true := by
  rw [filter_iff raw 1935 2008 c0 203 (a3_overlap r1 r2 q g1 g2 raw hR hr1 hr2 hq0) (by decide)]
  omega

/-- The witness's overlap is entirely detector-side: at the GRANT LUT g1 and g2 are
never high together in the slowD trace (g1 falls at 1068, g2 rises at 1167). -/

theorem slow_trace_grants_disjoint (t : Int) :
    (Formal.Cells.ArbOverlapRace.sG1 t && Formal.Cells.ArbOverlapRace.sG2 t) = false := by
  simp only [Formal.Cells.ArbOverlapRace.sG1, Formal.Cells.ArbOverlapRace.sG2, Formal.Cells.ArbOverlapRace.sR1, Formal.Cells.ArbOverlapRace.sR2, Formal.Cells.ArbOverlapRace.sQ, Formal.Cells.ArbBinary.gr1_eq, Formal.Cells.ArbBinary.gr2_eq]
  by_cases h1 : t - 1068 < 0 <;> by_cases h2 : t - 525 < 636 <;> by_cases h3 : t - 531 < 636 <;>
    simp [h1, h2, h3] <;> omega

end AuditP4

#print axioms AuditP4.cond_any_const
#print axioms AuditP4.a3_no_pass
#print axioms AuditP4.slow_trace_grants_disjoint
#print axioms Formal.Net.Capstone.gcd_hw_conditional
#print axioms Formal.Net.Capstone.latched_const
#print axioms Formal.Net.GcdHw.Gcd.gcdhw_ring_ge3
#print axioms Formal.Net.GcdHw.Gcd.gcdhw_has_cycle
#print axioms Formal.Net.Capstone.gcdhw_not_ge8
#print axioms Formal.Net.Capstone.ring_weights_are_links
#print axioms Formal.Net.Ops.Live.gcd_stuck
#print axioms Formal.Cells.ArbOverlapRace.grant_cap
#print axioms Formal.Cells.ArbOverlapRace.cell_cap_consistent
#print axioms Formal.Cells.ArbOverlapRace.cell_never_203
#print axioms Formal.Cells.ArbOverlapRace.rig_cap_fastMin
#print axioms Formal.Cells.ArbOverlapRace.slow_trace_raw
#print axioms Formal.Cells.ArbOverlapRace.slow_trace_passes_203
#print axioms Formal.Timing.RtFb.gcd4_slowE_safe
#print axioms Formal.Timing.RtFb.gcd4_pass
#check @Formal.Net.GcdHw.Gcd.gcdhw_ring_ge3
#check @Formal.Net.Ops.Live.gcd_stuck
