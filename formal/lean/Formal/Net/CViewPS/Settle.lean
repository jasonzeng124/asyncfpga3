import Formal.Net.CViewPS.HuffmanPS
import Formal.Timing.SpecLoop

/-!
# THE target settles in fundamental mode (shard C)

**Problem, plainly.** Between storage-node switches, does the rest of THE target's circuit
settle, and how fast? **Proved** (`settle_PS`): in every behaviour of THE theorem's circuit
(sane parameters), at its corner, for any bound `M` on every combinational pin's composite delay
(`sumMax`) and any `A` past every combinational gate's start: if every node that feeds a
combinational gate and is not itself combinational (a storage node, an environment node, an
undriven node) is constant on `[A, B]`, then every combinational node `w` is constant on
`[A + (ρ w + 1)·M, B]`, where `ρ` is the kernel-checked rank (≤ 96 by the generator; the bound
is not itself stated in Lean). From `collapsed` (CViewPS), `comb_ranked` (HuffmanPS) and
`SpecLoop.settle_ranked`.

**Not shown.** That storage nodes and the environment are ever quiet (dynamics); the value of `M`
for a concrete `p` (a computation over 96k pins).
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop

/-- A combinational node of THE target's circuit. -/
def combPS (w : Nat) : Prop :=
  w / 2500 < cs.length ∧ w % 2500 < (cs.getD (w / 2500) []).length ∧
    isComb keepPS (gAt cs 2500 w) (pvAt vss 2500 w) = true

def pcsPS (w : Nat) : List PinChain := toPCs cmPS (gaOf cs 2500) (gAt cs 2500 w) (pvAt vss 2500 w)
def srcPS (w i : Nat) : Nat := ((pcsPS w).getD i ⟨0, []⟩).src
def arcsPS (w : Nat) : Nat → List Arc := pinArcs (gAt cs 2500 w) (pcsPS w)
def startPS (p : DelayPar) (w : Nat) : Nat := cStart p (gAt cs 2500 w) (pcsPS w)

theorem mem_zip_getD {α β : Type} (l1 : List α) (l2 : List β) (o : Nat) (d1 : α) (d2 : β)
    (h1 : o < l1.length) (h2 : o < l2.length) : (l1.getD o d1, l2.getD o d2) ∈ l1.zip l2 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some, List.mem_iff_getElem]
  exact ⟨o, by simp; omega, by simp⟩

theorem mem_view {w : Nat} (h : combPS w) : (gAt cs 2500 w, pvAt vss 2500 w) ∈ logicView cs keepPS vss := by
  obtain ⟨h1, h2, h3⟩ := h
  have hlen : cs.length = vss.length := rfl
  have hc : (cs.getD (w / 2500) [], vss.getD (w / 2500) []) ∈ cs.zip vss :=
    mem_zip_getD _ _ _ _ _ h1 (by omega)
  have hv := views_ok _ hc
  simp only [chunkViewOK, Bool.and_eq_true, beq_iff_eq] at hv
  have hl2 : w % 2500 < (vss.getD (w / 2500) []).length := by rw [← hv.1]; exact h2
  simp only [logicView, List.mem_flatMap, List.mem_filter]
  refine ⟨_, hc, ?_, ?_⟩
  · exact mem_zip_getD _ _ _ _ _ h2 hl2
  · simp only [isComb, Bool.and_eq_true] at h3
    simp [h3.1.1, h3.1.2]

theorem gAt_out {w : Nat} (h : combPS w) : (gAt cs 2500 w).out = w := by
  obtain ⟨h1, h2, -⟩ := h
  obtain ⟨-, -, ho, -⟩ := facts _ h1
  rw [gAt, out_of_outsOK _ _ _ ho h2]; exact Nat.div_add_mod w 2500

theorem srcPS_eq {w i : Nat} (hi : i < (gAt cs 2500 w).k) : srcPS w i = ((pvAt vss 2500 w).getD i (0, 0)).1 := by
  unfold srcPS pcsPS; rw [toPCs_getD _ _ _ _ hi]

/-- **THE target settles in fundamental mode.** -/
theorem settle_PS {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ (M A B : Nat),
      (∀ w, combPS w → ∀ i, i < (gAt cs 2500 w).k → sumMax p (arcsPS w i) ≤ M) →
      (∀ w, combPS w → startPS p w ≤ A) →
      (∀ r, ¬ combPS r → (∃ w i, combPS w ∧ i < (gAt cs 2500 w).k ∧ srcPS w i = r) → Quiet (x r) A B) →
      ∀ w, combPS w → Quiet (x w) (A + ((rkPS w).getD 0 + 1) * M) B := by
  obtain ⟨c, hc0, hc1, hall⟩ := collapsed hp hb
  refine ⟨c, hc0, hc1, fun M A B hM hS hroot => ?_⟩
  have hwf := circuit_wf (N := net) (B := boundary) net_wf
  have hordg : ∀ w, combPS w → ∀ i, i < (gAt cs 2500 w).k → ArcsOrd (arcsPS w i) := by
    intro w hw i hi e he
    have hmem : gAt cs 2500 w ∈ (circuit net boundary).gates := by
      rw [circuit_eq, List.mem_filter, List.mem_flatten]
      obtain ⟨q, hq, he', hk, -⟩ := mem_logicView (mem_view hw)
      exact ⟨⟨q.1, (List.of_mem_zip hq).1, (List.of_mem_zip he').1⟩, hk⟩
    simp only [arcsPS, pinArcs, List.mem_cons, List.mem_map] at he
    rcases he with rfl | ⟨g', hg', rfl⟩
    · exact arcsOK_of_wf hwf hmem i
    · -- a chain gate of the circuit
      have hch := (pinsOK_of_m (cmSound_of_chunks (by decide) (by decide) circuit_eq tl_len facts)
        (by
          obtain ⟨q, hq, he', -, hn⟩ := mem_logicView (mem_view hw)
          have hv := views_ok q hq
          simp only [chunkViewOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at hv
          rcases hv.2 _ he' with (h | h) | h
          · obtain ⟨-, -, h3⟩ := hw; simp only [isComb, Bool.and_eq_true] at h3; simp [h3.1.1] at h
          · obtain ⟨-, -, h3⟩ := hw; simp only [isComb, Bool.and_eq_true] at h3
            simp [Option.isNone_iff_eq_none] at h3; simp [h3.1.2] at h
          · exact h)).2 i hi g' hg'
      exact arcsOK_of_wf hwf hch 0
  apply settle_ranked hp hc0 hc1 combPS
    (fun r => ¬ combPS r ∧ ∃ w i, combPS w ∧ i < (gAt cs 2500 w).k ∧ srcPS w i = r)
    (fun w => (rkPS w).getD 0) (gAt cs 2500) srcPS arcsPS (startPS p) M A B
  · intro w hw; exact ⟨gAt_out hw, hall _ (mem_view hw)⟩
  · exact hordg
  · intro w hw i hi
    by_cases hs : combPS (srcPS w i)
    · right; refine ⟨hs, ?_⟩
      obtain ⟨h1, h2, h3⟩ := hw
      obtain ⟨s1, s2, s3⟩ := hs
      exact comb_ranked w h1 h2 h3 i hi _ (srcPS_eq hi) s1 s2 s3
    · left; exact ⟨hs, w, i, hw, hi, rfl⟩
  · exact hM
  · exact hS
  · intro r ⟨h1, h2⟩; exact hroot r h1 h2

end Formal.Net.CViewPS
