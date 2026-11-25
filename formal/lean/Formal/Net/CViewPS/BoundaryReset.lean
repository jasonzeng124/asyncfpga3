import Formal.Net.CViewPS.BoundaryResetData

/-!
# THE target's boundary starts idle: reset drives the acknowledges and out0's request low (shard C)

**Problem, plainly.** Correct requires the circuit's handshake outputs to follow the four-phase
protocol from the end of reset, so they must start low. Does the reset alone guarantee that?
**Proved** (`boundary_reset`): in every behaviour of THE theorem's circuit (sane p), at its
corner, if reset is high on `[0, R)`: `a.ack` and `start.ack` (storage nodes in `resetList`) are
low on their reset windows (`reset_state`), and `b.ack` and `out0.req` (combinational, over a
30-node cone whose storage roots are 5 reset-forced nodes) are low on `[A + 8·M, B]` and `[A + 19·M, B]` for any
`A` past the cone's and roots' start/reset-arrival times, `B ≤ R - 1` within every root's reset
window, and `M` bounding the cone's composite pin delays (global ranks 7 and 18, kernel-checked). Each
fact about the data (cone values = INIT at their sources, sources in the cone with smaller rank or
roots, roots forced by reset to the listed values) is a `decide`.
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop

/-- The values: cone, then roots. -/
def vB (w : Nat) : Bool := ((coneList ++ rootList).lookup w).getD false

def inCone (w : Nat) : Bool := coneList.any fun e => e.1 == w
def inRoot (w : Nat) : Bool := rootList.any fun e => e.1 == w

def coneOK (e : Nat × Bool) : Bool :=
  logicB e.1 && isComb keepPS (gAt cs 2500 e.1) (pvAt vss 2500 e.1) &&
  (vB e.1 == (gAt cs 2500 e.1).init.testBit (addr (gAt cs 2500 e.1).k fun i => vB (srcPS e.1 i))) &&
  (List.range (gAt cs 2500 e.1).k).all fun i =>
    inRoot (srcPS e.1 i) || (inCone (srcPS e.1 i) && decide ((rkPS (srcPS e.1 i)).getD 0 < (rkPS e.1).getD 0))

def rootOK (e : Nat × Bool) : Bool :=
  resetList.any fun r => r.1 == e.1 && r.2.2 == e.2 && vB e.1 == e.2

set_option maxRecDepth 100000 in
theorem cone_ok : coneList.all coneOK = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem root_ok : rootList.all rootOK = true := by decide +kernel

theorem combPS_of {w : Nat} (h1 : logicB w = true) (h2 : isComb keepPS (gAt cs 2500 w) (pvAt vss 2500 w) = true) :
    combPS w := by
  obtain ⟨a, b, -, -⟩ := logicPS_of_B h1
  exact ⟨a, b, h2⟩

theorem ranks_out : (rkPS 104695).getD 0 = 7 ∧ (rkPS 160957).getD 0 = 18 ∧
    inCone 104695 = true ∧ inCone 160957 = true ∧ vB 104695 = false ∧ vB 160957 = false := by
  decide +kernel

/-- **The boundary's handshake outputs start low.** -/
theorem boundary_reset {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ (R M A B : Nat), (∀ t, t < R → x rstPS t = true) → 0 < R → B ≤ R - 1 →
      (∀ w, inCone w = true → ∀ i, i < (gAt cs 2500 w).k → sumMax p (arcsPS w i) ≤ M) →
      (∀ w, inCone w = true → startPS p w ≤ A) →
      (∀ e ∈ resetList, inRoot e.1 = true →
        startPS p e.1 ≤ A ∧ sumMax p (arcsPS e.1 e.2.1) ≤ A) →
      (∀ t, A + 8 * M ≤ t → t ≤ B → x 104695 t = false) ∧
      (∀ t, A + 19 * M ≤ t → t ≤ B → x 160957 t = false) := by
  obtain ⟨c, hc0, hc1, hall⟩ := collapsed hp hb
  refine ⟨c, hc0, hc1, fun R M A B hR hR0 hB hM hS hroots => ?_⟩
  have key := settle_value hp hc0 hc1 (fun w => inCone w = true) (fun r => inRoot r = true)
    (fun w => (rkPS w).getD 0) (gAt cs 2500) srcPS arcsPS (startPS p) M A B vB
    (by
      intro w hw
      obtain ⟨e, he, hew⟩ := List.any_eq_true.mp hw
      have hok := List.all_eq_true.mp cone_ok e he
      simp only [coneOK, Bool.and_eq_true, beq_iff_eq] at hok
      have hcw := combPS_of hok.1.1.1 hok.1.1.2
      simp only [beq_iff_eq] at hew; subst hew
      exact ⟨gAt_out hcw, hall _ (mem_view hcw)⟩)
    (by
      intro w hw
      obtain ⟨e, he, hew⟩ := List.any_eq_true.mp hw
      have hok := List.all_eq_true.mp cone_ok e he
      simp only [coneOK, Bool.and_eq_true, beq_iff_eq] at hok
      simp only [beq_iff_eq] at hew; subst hew
      exact ord_logic (logicPS_of_B hok.1.1.1))
    (by
      intro w hw i hi
      obtain ⟨e, he, hew⟩ := List.any_eq_true.mp hw
      have hok := List.all_eq_true.mp cone_ok e he
      simp only [coneOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
        Bool.or_eq_true, decide_eq_true_eq] at hok
      simp only [beq_iff_eq] at hew; subst hew
      rcases hok.2 i hi with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2⟩)
    hM hS
    (by
      intro w hw
      obtain ⟨e, he, hew⟩ := List.any_eq_true.mp hw
      have hok := List.all_eq_true.mp cone_ok e he
      simp only [coneOK, Bool.and_eq_true, beq_iff_eq] at hok
      simp only [beq_iff_eq] at hew; subst hew
      exact hok.1.2)
    (by
      intro r hr t ht1 ht2
      obtain ⟨e, he, her⟩ := List.any_eq_true.mp hr
      have hok := List.all_eq_true.mp root_ok e he
      simp only [rootOK, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨r', hr', ⟨h1, h2⟩, h3⟩ := hok
      simp only [beq_iff_eq] at her; subst her
      obtain ⟨s1, s2⟩ := hroots r' hr' (by rw [h1]; exact hr)
      simp only [startPS, pcsPS, arcsPS] at s1 s2
      -- reset_state, at `collapsed`'s corner: re-run its proof with this corner
      have hok2 := List.all_eq_true.mp resetList_ok r' hr'
      simp only [resetOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok2
      obtain ⟨⟨⟨hl, hj⟩, hs⟩, hF⟩ := hok2
      have hw := logicPS_of_B hl
      have k := cgate_force_pin hp hc0 hc1 (ord_logic hw) (hall _ (mem_view_logic hw)) hj true r'.2.2 hF 0 (R - 1)
        (fun t' _ b => by
          show x (srcPS r'.1 r'.2.1) t' = true
          rw [hs]; exact hR t' (by omega)) t (by dsimp only; omega) (by simp only [arcsPS, pcsPS] at s2 ⊢; omega) (by omega)
      rw [gAt_out_logic hw] at k
      rw [h3, ← h2, ← h1]; exact k)
  obtain ⟨r1, r2, i1, i2, v1, v2⟩ := ranks_out
  refine ⟨fun t a b => ?_, fun t a b => ?_⟩
  · have := key 104695 i1 t (by rw [r1]; omega) b; rw [this, v1]
  · have := key 160957 i2 t (by rw [r2]; omega) b; rw [this, v2]

end Formal.Net.CViewPS
