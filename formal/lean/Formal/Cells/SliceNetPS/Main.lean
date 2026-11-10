import Formal.Cells.SliceNetPS.Sound
import Formal.Net.CViewPS.Collapsed

/-!
# Formal.Cells.SliceNetPS.Main — THE target's timed net for a slice of corners, and its read hypotheses
(shard B, 2026-11-10)

**Problem, plainly.** C's AO certificate theorems (`Net/AO`, B's `CovUpMain`) are about behaviours of a timed net
(`TBehX`); THE statement is about `Spec.Behaves` of the decoded circuit, each behaviour at its own corner. Is there a
concrete timed net for THE target whose read hypotheses every behaviour meets, for a whole slice of corners?

**Proved.** `tnPS p c1 c2` is THE target's slice net: its gates are the 19,878 logic nodes (`logicPS`), its pins the
collapsed sources of each gate's kept pins (pins neither dead in the INIT nor tied to one of the 1,925 constant
nodes), its function the INIT with the constant pins filled in, `lo`/`hi` the routes' corner sums at `c1`/`c2`.
`target_reads_slice`: for every sane `p` and every behaviour of THE theorem's circuit there is a corner `c ∈ [0,1]`
such that for every slice `[c1, c2] ∋ c` with `c2 ≤ 1`, every `H` bounding every logic gate's collapsed start time
`startPS p w`, and every `t0 ≥ startPS p w + H` (all w), there are read times meeting `TBehX`'s `rd`, `mono` and
`geq` on `tnPS p c1 c2`. Kernel-checked data: kept sources distinct on every logic gate (`sel_ok`, 75 chunks), every
listed constant is a k = 0 logic gate with that value (`constF_sound`, per chunk).

**Not shown here:** the other `TBehX` fields (quiet start, environment rule, `lo ≥ 1` on kept pins); a concrete `H`
(a bound on `startPS` over all logic gates, a netlist computation, left as the premise C's `quiet_PS` also has); any
certificate on `tnPS`.
-/

namespace Formal.Cells.SliceNetPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Timing.SpecChainM
  Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop Formal.Net.CViewPS Formal.Net.OccNet
  Formal.Net.OccNet.Timed Formal.Net.OccNet.Bridge Formal.Cells.CornerSlice Formal.Cells.SliceReads Formal.Cells.SliceNet

def keepPSN (v : Nat) : List Nat := keepL constF (gAt cs 2500 v) (pvAt vss 2500 v)
def cstPSN (v : Nat) : Nat → Option Bool := cstL constF (gAt cs 2500 v) (pvAt vss 2500 v)

/-- **THE target's timed net for the corner slice `[c1, c2]`.** -/
def tnPS (p : DelayPar) (c1 c2 : ℚ) : TNet Nat := selNet p c1 c2 logicB (gAt cs 2500) pcsPS keepPSN cstPSN

theorem keep_lt {v i : Nat} (h : i ∈ keepPSN v) : i < (gAt cs 2500 v).k := by
  unfold keepPSN keepL at h
  exact List.mem_range.1 (List.mem_filter.1 h).1

theorem keep_src {v : Nat} : (keepPSN v).map (srcOf (pcsPS v)) = (keepPSN v).map (srcD (pvAt vss 2500 v)) := by
  apply List.map_congr_left
  intro i hi
  exact srcPS_eq (keep_lt hi)

theorem nodup_logic {w : Nat} (h : logicPS w) : ((keepPSN w).map (srcOf (pcsPS w))).Nodup := by
  rw [keep_src]
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hc : (cs.getD (w / 2500) [], vss.getD (w / 2500) []) ∈ cs.zip vss :=
    mem_zip_getD _ _ _ _ _ h1 (by have : cs.length = vss.length := rfl; omega)
  have hv := views_ok _ hc
  simp only [chunkViewOK, Bool.and_eq_true, beq_iff_eq] at hv
  have hl2 : w % 2500 < (vss.getD (w / 2500) []).length := by rw [← hv.1]; exact h2
  have hs := sel_ok _ hc
  simp only [chunkSelOK, List.all_eq_true] at hs
  have hm : (gAt cs 2500 w, pvAt vss 2500 w) ∈ (cs.getD (w / 2500) []).zip (vss.getD (w / 2500) []) :=
    mem_zip_getD _ _ _ _ _ h2 hl2
  have := hs _ hm
  simp only [h3, h4, Option.isSome_none, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at this
  exact this.1

theorem fmin_logic {w : Nat} (h : logicPS w) : ∀ i ∈ keepPSN w, 1 ≤ ((gAt cs 2500 w).arcs.getD i default).fmin := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hc : (cs.getD (w / 2500) [], vss.getD (w / 2500) []) ∈ cs.zip vss :=
    mem_zip_getD _ _ _ _ _ h1 (by have : cs.length = vss.length := rfl; omega)
  have hv := views_ok _ hc
  simp only [chunkViewOK, Bool.and_eq_true, beq_iff_eq] at hv
  have hl2 : w % 2500 < (vss.getD (w / 2500) []).length := by rw [← hv.1]; exact h2
  have hs := sel_ok _ hc
  simp only [chunkSelOK, List.all_eq_true] at hs
  have hm : (gAt cs 2500 w, pvAt vss 2500 w) ∈ (cs.getD (w / 2500) []).zip (vss.getD (w / 2500) []) :=
    mem_zip_getD _ _ _ _ _ h2 hl2
  have := hs _ hm
  simp only [h3, h4, Option.isSome_none, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at this
  exact this.2

/-- **`TBehX.lo1` on the slice net**: every kept pin's lower bound is at least 1 ps (κ < 1, `0 ≤ c1`). -/
theorem tnPS_lo1 {p : DelayPar} (hp : Sane p) (hk : p.κ < 1) {c1 c2 : ℚ} (hc1 : 0 ≤ c1) :
    ∀ v w, (tnPS p c1 c2).gate v = true → w ∈ (tnPS p c1 c2).pins v → 1 ≤ (tnPS p c1 c2).lo v w := by
  intro v w hv hw
  have hl := logicB_iff.1 hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
  show 1 ≤ sumLoC p c1 (pinArcs (gAt cs 2500 v) (pcsPS v) (pinOf (keepPSN v) (srcOf (pcsPS v)) (srcOf (pcsPS v) i)))
  rw [pinOf_src (nodup_logic hl) hi]
  have hf := fmin_logic hl i hi
  have hord := ord_logic hl i (keep_lt hi) _ (List.mem_cons_self ..)
  simp only [pinArcs, sumLoC, List.map_cons, List.sum_cons]
  suffices 1 ≤ loC p c1 ((gAt cs 2500 v).arcs.getD i default) by omega
  unfold loC
  obtain ⟨_, _, hg⟩ := hp
  have hl1 : (1 : ℚ) ≤ lerp ((gAt cs 2500 v).arcs.getD i default).fmin ((gAt cs 2500 v).arcs.getD i default).smin c1 := by
    have := lerp_mono hord.1 hc1
    have h0 : lerp ((gAt cs 2500 v).arcs.getD i default).fmin ((gAt cs 2500 v).arcs.getD i default).smin 0 =
        ((gAt cs 2500 v).arcs.getD i default).fmin := by simp [lerp]
    have hf' : (1 : ℚ) ≤ ((gAt cs 2500 v).arcs.getD i default).fmin := by exact_mod_cast hf
    linarith
  have hpos : 0 < (1 - p.κ) * lerp ((gAt cs 2500 v).arcs.getD i default).fmin
      ((gAt cs 2500 v).arcs.getD i default).smin c1 / p.g := by
    apply div_pos _ hg; apply mul_pos (by linarith); linarith
  have := Int.ceil_pos.2 hpos
  omega

/-- **Every behaviour of THE target meets the read hypotheses of the timed model on the slice net of any slice
containing its corner.** -/
theorem target_reads_slice {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ (c1 c2 : ℚ) (t0 H : Nat), c1 ≤ c → c ≤ c2 → c2 ≤ 1 →
      (∀ w, logicPS w → startPS p w ≤ H) → (∀ w, logicPS w → startPS p w + H ≤ t0) →
      ∃ r : Nat → Nat → Nat → Nat,
        (∀ v w t, (tnPS p c1 c2).gate v = true → w ∈ (tnPS p c1 c2).pins v → t0 < t →
          (tnPS p c1 c2).lo v w ≤ t - r v w t ∧ t - r v w t ≤ (tnPS p c1 c2).hi v w ∧ r v w t ≤ t ∧
          t0 ≤ r v w t + H) ∧
        (∀ v w t t', (tnPS p c1 c2).gate v = true → w ∈ (tnPS p c1 c2).pins v → t0 < t → t ≤ t' →
          r v w t ≤ r v w t') ∧
        (∀ v t, (tnPS p c1 c2).gate v = true → t0 < t →
          x v t = (tnPS p c1 c2).F v (((tnPS p c1 c2).pins v).map fun w => x w (r v w t))) := by
  obtain ⟨c, hc0, hc1, hC⟩ := collapsed hp hb
  have hCv : ∀ v, logicPS v → CGateOK p c (gAt cs 2500 v) (srcOf (pcsPS v)) (arcsPS v) (startPS p v) x :=
    fun v hv => hC _ (mem_view_logic hv)
  refine ⟨c, hc0, hc1, fun c1 c2 t0 H h1 h2 hc2 hSH hSt => ?_⟩
  apply selNet_reads hp h1 h2 (startPS p)
  · intro v hv; exact gAt_out_logic (logicB_iff.1 hv)
  · intro v hv; exact hCv v (logicB_iff.1 hv)
  · intro v hv; have := hSt v (logicB_iff.1 hv); omega
  · intro v hv; exact nodup_logic (logicB_iff.1 hv)
  · intro v _ i hi; exact keep_lt hi
  · intro v hv i hi a ha; exact ord_logic (logicB_iff.1 hv) i hi a ha
  · intro v _ i hi hni
    have hn : ¬ (!deadB (gAt cs 2500 v) i && (constF (srcD (pvAt vss 2500 v) i)).isNone) = true := by
      intro hh; exact hni (List.mem_filter.2 ⟨List.mem_range.2 hi, hh⟩)
    by_cases hd : deadB (gAt cs 2500 v) i = true
    · right; exact ⟨by simp [cstPSN, cstL, hd], dead_of_deadB hd hi⟩
    · left
      simp only [hd, Bool.not_false, Bool.true_and, Bool.not_eq_true, Option.isNone_eq_false_iff] at hn
      simpa [cstPSN, cstL, hd] using hn
  · intro v hv i b hi _ hcb s hs
    have hd : deadB (gAt cs 2500 v) i = false := by
      by_contra hd; simp [cstPSN, cstL, hd] at hcb
    have hf : constF (srcD (pvAt vss 2500 v) i) = some b := by simpa [cstPSN, cstL, hd] using hcb
    obtain ⟨hlog', hk0, hbit⟩ := constF_sound hf
    have hsrc : srcOf (pcsPS v) i = srcD (pvAt vss 2500 v) i := srcPS_eq hi
    rw [hsrc]
    obtain ⟨F, _, hok⟩ := hCv _ hlog'
    have hst := hSt _ hlog'
    obtain ⟨_, hx⟩ := hok s (by omega)
    rw [gAt_out_logic hlog'] at hx
    rw [hx, hk0]
    simpa [addr] using hbit
  · intro v hv i hi
    exact le_trans (sumHiC_le_cStart hp hc2 hi (fun a ha => ord_logic (logicB_iff.1 hv) i hi a ha))
      (hSH v (logicB_iff.1 hv))

end Formal.Cells.SliceNetPS
