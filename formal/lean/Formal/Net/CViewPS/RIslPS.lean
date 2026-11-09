import Formal.Net.CViewPS.RIslChk

/-!
# THE target starts quiet: every exact control node is known during reset (shard C)

**Problem, plainly.** The timed theorem needs a quiet start: during reset, every control node
whose value reset alone determines must hold that value, whatever the 4,185 unreset data latches
hold and whatever the delays (in Adm). **Proved** (`reset_quiet_PS`): in every behaviour of THE
theorem's circuit (sane `p`), at its corner: if the reset node `rstPS` (186905) is high on
`[0, R)` with `0 < R`, every member's start is at most `A`, and every pin of every member has
composite delay at most `M`, then every one of the 3,224 members `w` of `rIsl` equals its listed
value `valR w` at every `t` with `A + (ρ w + 1)·M ≤ t ≤ R - 1`; since `ρ ≤ 14`, on
`[A + 15·M, R - 1]` (`reset_quiet_PS15`). Members: 402 storage nodes forced by their reset pin,
9 arbiter states (forced by rst = 1 and a constant pin), about 2,800 combinational nodes, and 11
constant (k = 0) gates. Kernel-checked per member (`rEntryOK`, RIslChk*.lean): a logic node of the
circuit (so `collapsed` gives its `CGateOK`, storage included), not `rstPS`, `ρ ≤ 14`; its forcing
pins are pins of the gate whose sources are `rstPS` (value 1) or members of strictly smaller
`ρ`; and those pins at those values force its INIT to the listed value (`ForcesP`), whatever its
other pins read. Then `Island.settle_partial` with the single root `rstPS` on `[A, R - 1]`.

**Not shown.** The delay hypotheses (`A`, `M`) for a concrete `p`; which nodes outside the list
are known (none are claimed); anything after `R - 1`.
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop
  Formal.Timing.Island

theorem rentry_facts {w : Nat} (h : memR w = true) :
    logicPS w ∧ rhoR w ≤ 14 ∧
    (∀ j ∈ psR w, j < (gAt cs 2500 w).k ∧
      (srcPS w j = rstPS ∨ (memR (srcPS w j) = true ∧ rhoR (srcPS w j) < rhoR w))) ∧
    ForcesP (gAt cs 2500 w).k (gAt cs 2500 w).init (asgOf srcPS valR w (psR w)) (valR w) = true := by
  unfold memR at h
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨rfl, hok⟩ := RTree.find_all rIsl w e he rIsl_ok
  have hps : psR e.1 = e.2.2.1 := by unfold psR; rw [he]; rfl
  have hrho : rhoR e.1 = e.2.2.2 := by unfold rhoR; rw [he]; rfl
  simp only [rEntryOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨hl, hne⟩, hr⟩, hall⟩, hF⟩ := hok
  have hval : valR e.1 = e.2.1 := by
    unfold valR; rw [he]; simp [hne]
  rw [hps, hrho, hval]
  refine ⟨logicPS_of_BR hl, hr, fun j hj => ?_, hF⟩
  have := List.all_eq_true.mp hall j hj
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at this
  exact this

/-- **Quiet start of THE target.** -/
theorem reset_quiet_PS {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ (R M A : Nat),
      (∀ t, t < R → x rstPS t = true) → 0 < R →
      (∀ w, memR w = true → startPS p w ≤ A) →
      (∀ w, memR w = true → ∀ i, i < (gAt cs 2500 w).k → sumMax p (arcsPS w i) ≤ M) →
      ∀ w, memR w = true → ∀ t, A + (rhoR w + 1) * M ≤ t → t ≤ R - 1 → x w t = valR w := by
  obtain ⟨c, hc0, hc1, hall⟩ := collapsed hp hb
  refine ⟨c, hc0, hc1, fun R M A hR hR0 hS hM => ?_⟩
  exact settle_partial hp hc0 hc1 (fun w => memR w = true) (fun r => r = rstPS) rhoR (gAt cs 2500)
    srcPS arcsPS (startPS p) M A (R - 1) valR psR
    (fun w hw => ⟨gAt_out_logic (rentry_facts hw).1, hall _ (mem_view_logic (rentry_facts hw).1)⟩)
    (fun w hw => ord_logic (rentry_facts hw).1)
    (fun w hw => (rentry_facts hw).2.2.2)
    (fun w hw j hj => (rentry_facts hw).2.2.1 j hj)
    hM hS
    (by
      rintro r rfl t - h2
      simp only [valR, beq_self_eq_true, ite_true]
      exact hR t (by omega))

/-- The same, on one window for all members (`ρ ≤ 14`). -/
theorem reset_quiet_PS15 {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ (R M A : Nat),
      (∀ t, t < R → x rstPS t = true) → 0 < R →
      (∀ w, memR w = true → startPS p w ≤ A) →
      (∀ w, memR w = true → ∀ i, i < (gAt cs 2500 w).k → sumMax p (arcsPS w i) ≤ M) →
      ∀ w, memR w = true → ∀ t, A + 15 * M ≤ t → t ≤ R - 1 → x w t = valR w := by
  obtain ⟨c, hc0, hc1, h⟩ := reset_quiet_PS hp hb
  refine ⟨c, hc0, hc1, fun R M A hR hR0 hS hM w hw t h1 h2 => h R M A hR hR0 hS hM w hw t ?_ h2⟩
  have : (rhoR w + 1) * M ≤ 15 * M := Nat.mul_le_mul_right M (by have := (rentry_facts hw).2.1; omega)
  omega

end Formal.Net.CViewPS
