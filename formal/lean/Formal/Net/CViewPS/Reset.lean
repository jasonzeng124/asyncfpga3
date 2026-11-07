import Formal.Net.CViewPS.ResetData

/-!
# Reset puts THE target's control storage nodes in their reset state (shard C)

**Problem, plainly.** Any proof about THE target starts from a known state. Spec's `Env` holds the
reset node high on `[0, R)`. Which storage nodes does that alone determine, and from when?
**Proved** (`reset_state`): in every behaviour of THE theorem's circuit (sane p), at its corner,
if the reset node is high on `[0, R)`, then each of the 403 storage nodes in `resetList` (link
controllers, mux joins and selects, forks, arbiter C-elements: every storage node whose reset pin
alone forces its output) equals its listed reset value at every time `t` with
`startPS p w ≤ t`, `Σdmax(reset pin) ≤ t` and `t ≤ R - 1 + Σdmin(reset pin)`. Per entry the kernel
checks: a logic node of the circuit, the pin's source is the reset node, and the INIT is forced
(`Forces`). The other 4,194 storage nodes (4,185 data latches without reset, 9 arbiter states) are
not covered.
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop

/-- Bool form of `logicPS`. -/
def logicB (w : Nat) : Bool :=
  decide (w / 2500 < cs.length) && decide (w % 2500 < (cs.getD (w / 2500) []).length) &&
    keepPS (gAt cs 2500 w) && (cpIn (gAt cs 2500 w)).isNone

def resetOK (e : Nat × Nat × Bool) : Bool :=
  logicB e.1 && decide (e.2.1 < (gAt cs 2500 e.1).k) && (srcPS e.1 e.2.1 == rstPS) &&
    Forces (gAt cs 2500 e.1).k (gAt cs 2500 e.1).init e.2.1 true e.2.2

set_option maxRecDepth 100000 in
theorem resetList_ok : resetList.all resetOK = true := by decide +kernel

theorem logicPS_of_B {w : Nat} (h : logicB w = true) : logicPS w := by
  simp only [logicB, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- **Reset state of THE target's control storage nodes.** -/
theorem reset_state {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ R : Nat, (∀ t, t < R → x rstPS t = true) →
      ∀ e ∈ resetList, ∀ t, startPS p e.1 ≤ t → sumMax p (arcsPS e.1 e.2.1) ≤ t →
        t ≤ R - 1 + sumMin p (arcsPS e.1 e.2.1) → 0 < R → x e.1 t = e.2.2 := by
  obtain ⟨c, hc0, hc1, hall⟩ := collapsed hp hb
  refine ⟨c, hc0, hc1, fun R hR e he t h1 h2 h3 hR0 => ?_⟩
  have hok := List.all_eq_true.mp resetList_ok e he
  simp only [resetOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨hl, hj⟩, hs⟩, hF⟩ := hok
  have hw := logicPS_of_B hl
  have key := cgate_force_pin hp hc0 hc1 (ord_logic hw) (hall _ (mem_view_logic hw)) hj true e.2.2 hF 0 (R - 1)
    (fun t' _ b => by
      show x (srcPS e.1 e.2.1) t' = true
      rw [hs]; exact hR t' (by omega)) t h1 (by simpa using h2) h3
  rw [gAt_out_logic hw] at key
  exact key

end Formal.Net.CViewPS
