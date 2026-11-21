import Formal.Cells.StartBoundPS.Chunks
import Formal.Net.CViewPS.Quiet

/-!
# Formal.Cells.StartBoundPS.Main — every logic gate of THE target starts within `⌈(1+κ)g⌉ · 33,002 ps`
(shard B, 2026-11-10)

**Problem, plainly.** The theorems on THE target's collapsed view hold from each gate's collapsed start time
`startPS p w` (the gate's and its pins' routing chains' slowest delays); several carry the premise that every such
start is at most some `H` (C's `quiet_PS`, B's `target_reads_slice`). What is `H`?

**Proved.** `startPS_le`: for every sane `p` and every logic node `w` of THE target (`logicPS`, 19,878 nodes),
`startPS p w ≤ ⌈(1+κ)·g⌉ · 33,002` ps. Kernel-checked: per-node values `stN + smax(arc0)` stored in 75 chunk trees
(`ffacts`) and, per chunk, every logic gate's start at g = 1, κ = 0 summed along its pins' copy chains (`start_ok`).
With `SliceNet.sumHiC_le_cStart`, every kept pin's route bound on a slice net (c2 ≤ 1) is within it too.

**Not shown here:** anything about behaviours; the bound is not claimed tight (the generator's max is 33,002 ps at
SLICE_X20Y93.BLUT.O6; median 6.4 ns).
-/

namespace Formal.Cells.StartBoundPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Timing.SpecChainM
  Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Net.CViewPS Formal.Cells.StartBound

theorem boundN_le {w : Nat} (h : logicPS w) : boundN cmPS fPS (gAt cs 2500 w) (pvAt vss 2500 w) ≤ HB := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hc : (cs.getD (w / 2500) [], vss.getD (w / 2500) []) ∈ cs.zip vss :=
    mem_zip_getD _ _ _ _ _ h1 (by have : cs.length = vss.length := rfl; omega)
  have hv := views_ok _ hc
  simp only [chunkViewOK, Bool.and_eq_true, beq_iff_eq] at hv
  have hl2 : w % 2500 < (vss.getD (w / 2500) []).length := by rw [← hv.1]; exact h2
  have hs := start_ok _ hc
  simp only [chunkStartOK, List.all_eq_true] at hs
  have hm : (gAt cs 2500 w, pvAt vss 2500 w) ∈ (cs.getD (w / 2500) []).zip (vss.getD (w / 2500) []) :=
    mem_zip_getD _ _ _ _ _ h2 hl2
  have := hs _ hm
  simp only [h3, h4, Option.isSome_none, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
  exact this

/-- **Every logic gate's collapsed start is at most `⌈(1+κ)g⌉ · HB`.** -/
theorem startPS_le {p : DelayPar} (hp : Sane p) {w : Nat} (hw : logicPS w) : startPS p w ≤ mOf p * HB := by
  have h1 := cStart_le_m hp (gAt cs 2500 w) (pcsPS w)
  have h2 : cStartN' (gAt cs 2500 w) (pcsPS w) = boundN cmPS fPS (gAt cs 2500 w) (pvAt vss 2500 w) := by
    unfold pcsPS
    rw [cStartN'_eq]
    congr 1
    funext u
    exact (fPS_eq u).symm
  have h3 := boundN_le hw
  unfold startPS
  rw [h2] at h1
  exact le_trans h1 (Nat.mul_le_mul_left _ h3)

end Formal.Cells.StartBoundPS
