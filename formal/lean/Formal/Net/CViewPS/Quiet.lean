import Formal.Net.CViewPS.Settle

/-!
# THE target never starts moving by itself (shard C)

**Problem, plainly.** THE theorem's conclusion ends with the circuit idle for ever after the last
pair. Can the circuit, once quiet, start moving with no input (a late glitch, an oscillation)?
**Proved** (`quiet_PS`): in every behaviour of THE theorem's circuit (sane p), at its corner, for
any `M` bounding every logic pin's composite delay, with every pin's delay ≥ 1 ps unless its source is outside the logic or a constant (k = 0) gate, and `T ≥ M` past every logic gate's
start (+ M): if the environment and undriven nodes that feed logic are constant from `T - M` on,
and every logic node (combinational and storage, 19,878) is constant on `[T - M, T]`, then every
logic node is constant for ever from `T - M`. From `collapsed` and `SpecLoop.quiet_forever`.

**Not shown.** That the circuit reaches such a quiet state after the last pair (liveness), and
the delay hypotheses for a concrete `p` (on the data, the only zero-fmin composite pins are 368
CARRY4 pins reading the CONST0 gate, k = 0, which the hypothesis allows).
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop

/-- A logic node of THE target's circuit (combinational or storage). -/
def logicPS (w : Nat) : Prop :=
  w / 2500 < cs.length ∧ w % 2500 < (cs.getD (w / 2500) []).length ∧
    keepPS (gAt cs 2500 w) = true ∧ cpIn (gAt cs 2500 w) = none

theorem mem_view_logic {w : Nat} (h : logicPS w) :
    (gAt cs 2500 w, pvAt vss 2500 w) ∈ logicView cs keepPS vss := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hc : (cs.getD (w / 2500) [], vss.getD (w / 2500) []) ∈ cs.zip vss :=
    mem_zip_getD _ _ _ _ _ h1 (by have : cs.length = vss.length := rfl; omega)
  have hv := views_ok _ hc
  simp only [chunkViewOK, Bool.and_eq_true, beq_iff_eq] at hv
  have hl2 : w % 2500 < (vss.getD (w / 2500) []).length := by rw [← hv.1]; exact h2
  simp only [logicView, List.mem_flatMap, List.mem_filter]
  exact ⟨_, hc, mem_zip_getD _ _ _ _ _ h2 hl2, by simp [h3, h4]⟩

theorem gAt_out_logic {w : Nat} (h : logicPS w) : (gAt cs 2500 w).out = w := by
  obtain ⟨h1, h2, -⟩ := h
  obtain ⟨-, -, ho, -⟩ := facts _ h1
  rw [gAt, out_of_outsOK _ _ _ ho h2]; exact Nat.div_add_mod w 2500

theorem ord_logic {w : Nat} (hw : logicPS w) : ∀ i, i < (gAt cs 2500 w).k → ArcsOrd (arcsPS w i) := by
  have hwf := circuit_wf (N := net) (B := boundary) net_wf
  intro i hi e he
  obtain ⟨q, hq, he', hk, hn⟩ := mem_logicView (mem_view_logic hw)
  have hmem : gAt cs 2500 w ∈ (circuit net boundary).gates := by
    rw [circuit_eq, List.mem_filter, List.mem_flatten]
    exact ⟨⟨q.1, (List.of_mem_zip hq).1, (List.of_mem_zip he').1⟩, hk⟩
  simp only [arcsPS, pinArcs, List.mem_cons, List.mem_map] at he
  rcases he with rfl | ⟨g', hg', rfl⟩
  · exact arcsOK_of_wf hwf hmem i
  · have hv := views_ok q hq
    simp only [chunkViewOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at hv
    have hpm : pinsOKm cmPS (gAt cs 2500 w) (pvAt vss 2500 w) = true := by
      rcases hv.2 _ he' with (h | h) | h
      · simp [hk] at h
      · simp [Option.isNone_iff_eq_none] at hn; simp [hn] at h
      · exact h
    have hch := (pinsOK_of_m (cmSound_of_chunks (by decide) (by decide) circuit_eq tl_len facts) hpm).2 i hi g' hg'
    exact arcsOK_of_wf hwf hch 0

/-- **Quiet is forever, on THE target.** -/
theorem quiet_PS {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ (M T : Nat), M ≤ T →
      (∀ w, logicPS w → ∀ i, i < (gAt cs 2500 w).k →
        (1 ≤ sumMin p (arcsPS w i) ∨ ¬ logicPS (srcPS w i) ∨ (gAt cs 2500 (srcPS w i)).k = 0) ∧
        sumMax p (arcsPS w i) ≤ M) →
      (∀ w, logicPS w → startPS p w ≤ T - M) →
      (∀ r, ¬ logicPS r → (∃ w i, logicPS w ∧ i < (gAt cs 2500 w).k ∧ srcPS w i = r) →
        ∀ t, T - M ≤ t → x r t = x r (T - M)) →
      (∀ w, logicPS w → ∀ t, T - M ≤ t → t ≤ T → x w t = x w (T - M)) →
      ∀ w, logicPS w → ∀ t, T - M ≤ t → x w t = x w (T - M) := by
  obtain ⟨c, hc0, hc1, hall⟩ := collapsed hp hb
  refine ⟨c, hc0, hc1, fun M T hMT hM hS hroot hq => ?_⟩
  apply quiet_forever hp hc0 hc1 logicPS
    (fun r => ¬ logicPS r ∧ ∃ w i, logicPS w ∧ i < (gAt cs 2500 w).k ∧ srcPS w i = r)
    (gAt cs 2500) srcPS arcsPS (startPS p) M T hMT
  · intro w hw; exact ⟨gAt_out_logic hw, hall _ (mem_view_logic hw)⟩
  · intro w hw; exact ord_logic hw
  · intro w hw i hi
    by_cases hs : logicPS (srcPS w i)
    · exact Or.inr hs
    · exact Or.inl ⟨hs, w, i, hw, hi, rfl⟩
  · intro w hw i hi
    obtain ⟨h1, h2⟩ := hM w hw i hi
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨h1, w, i, hw, hi, rfl⟩)
    · exact Or.inr (Or.inr h1)
  · exact hS
  · intro r ⟨h1, h2⟩; exact hroot r h1 h2
  · exact hq

end Formal.Net.CViewPS
