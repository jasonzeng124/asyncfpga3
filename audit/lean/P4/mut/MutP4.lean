import Formal.Net.Capstone
import Formal.Cells.ArbOverlapRace
/-! Mutants: every theorem below is a deliberately WRONG variant of a headline and must FAIL. -/
open Formal.Net Formal.Net.Ops Formal.Net.Handshake
open Formal.Cells.ArbOverlapRace Formal.Cells.ArbBinary

-- M1: cell_cap_consistent tightened 33 -> 32 at SLOW_MAX
theorem M1 (o5q : Int) : (116 ≤ o5q ∧ o5q ≤ 157) → adist o5q 124 ≤ 32 := by
  unfold adist; intro h; split <;> omega

-- M2: cell_cap_box 112 -> 111
theorem M2 (o5q o6q : Int) (h5 : 42 ≤ o5q ∧ o5q ≤ 157) (h6 : 45 ≤ o6q ∧ o6q ≤ 124) :
    adist o5q o6q ≤ 111 := by unfold adist; split <;> omega

-- M3: slow trace overlap one ps longer
theorem M3 (t : Int) : sRaw t = true ↔ 1703 ≤ t ∧ t < 2009 := by
  have := (handover12 slow_trace_rig 0 (fun _ => rfl) (fun _ => rfl)
    (fun t ht => by simp [sQ, slowD] at ht ⊢; omega)).2 t
  rw [this]; simp only [slowD]; omega

-- M4: grant_cap with the cap reduced by one
theorem M4 {D : Dl} {r1 r2 q g1 g2 raw : Sig} (hD : Dec D r1 r2 q g1 g2 raw)
    (T ℓ : Int) (h : HighOn (fun t => g1 t && g2 t) T ℓ) : ℓ ≤ adist D.b5 D.b6 - 1 := by
  have := grant_cap hD T ℓ h; omega

-- M5: rig_cap_fastMin 184 -> 183
theorem M5 {D : Dl} {r1 r2 q g1 g2 raw : Sig} (hD : Dec D r1 r2 q g1 g2 raw)
    (P : Decomp D) (hw : P.w1 = P.w2) (hx : P.xo5 = 0)
    (hp1 : 2 ≤ P.p1 ∧ P.p1 ≤ 180) (hp2 : 2 ≤ P.p2 ∧ P.p2 ≤ 180)
    (h5 : 42 ≤ P.o5q ∧ P.o5q ≤ 51) (h6 : P.o6q = 45)
    (T ℓ : Int) (h : HighOn raw T ℓ) : ℓ ≤ 183 := by
  have h1 := raw_cap hD T ℓ h
  have h2 := sb_eq P
  unfold adist at h1; split at h1 <;> omega

-- M6: gcd_hw_conditional with a different value in the conclusion than in the premise
theorem M6 {C O : Type} (a b : Nat) (N : Net C O) (ch : C → Chan)
    (E : O → (C → Nat → Nat) → Prop)
    (H_CELLS : ∀ o, OpProto ch (N.ins o) (N.outs o) ∧ OpData ch (N.ins o) (N.outs o) (E o))
    (H_BUNDLE : ∀ c, Held (ch c)) (out0 : C)
    (O_SOLUTION : ∃ ref : C → Nat → Nat, (∀ o, E o ref) ∧ ∀ k, ref out0 k = Nat.gcd a b) :
    ∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a (b + 1) := by
  intro k e h
  have := Formal.Net.Capstone.gcd_hw_conditional a b N ch E H_CELLS H_BUNDLE out0 O_SOLUTION k e h
  omega
