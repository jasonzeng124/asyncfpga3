import Formal.Cells.SliceReads
import Formal.Timing.SpecChainM

/-!
# Formal.Cells.SliceNet — a timed net built from a list of collapsed gates (shard B, 2026-11-10)

**Problem, plainly.** To instantiate the timed model (`TBehX`) on THE target, one needs a concrete timed net:
which nodes are gates, their pins, their functions and their integer delay bounds. This file builds it, node-indexed, from
a gate predicate `isG` and per node its collapsed gate (`gOf`), pin chains (`pcsOf`), the pins to keep (`keepOf`)
and the constants of the others (`cstOf`), for a corner slice `[c1, c2]` (THE target: C's `logicPS`, `gAt`,
`pcsPS`):
* the gates are the `isG` nodes; their pins are the kept pins' sources;
* its function is the INIT with the kept pins read and the others filled in (`SliceReads.fill`);
* `lo`/`hi` of a kept pin are its route's corner sums at `c1`/`c2` (`sumLoC`, `sumHiC`; Nat forms in `CornerSlice`).

**Proved.** `selNet_reads`: if every gate node has its `CGateOK` fact at a corner `c ∈ [c1, c2]` (from `t0 + 1` on),
its kept sources are distinct, its routes' arcs are corner-ordered, every non-kept pin is constant (and its source
shows that constant from `t0 - H` on) or dead, and every route's slow-end sum is at most `H`, then the read
hypotheses of `TBehX` (`rd`, `mono`, `geq`) hold on `selNet` for that behaviour. `sumHiC_le_cStart`: every
route's slow-end sum (`c2 ≤ 1`) is at most the gate's collapsed start time `cStart`, so `H` can be any bound on the
start times.

**Not shown here:** the instance (`Formal/Cells/SliceNetPS.lean`); the other `TBehX` fields.
-/

namespace Formal.Cells.SliceNet
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Timing.SpecChainM Formal.Net.OccNet
  Formal.Net.OccNet.Timed Formal.Net.OccNet.Bridge Formal.Cells.CornerSlice Formal.Cells.SliceReads

/-- The source of pin `i`. -/
def srcOf (pcs : List PinChain) (i : Nat) : Nat := (pcs.getD i ⟨0, []⟩).src

section
variable (p : DelayPar) (c1 c2 : ℚ)

/-- **The slice net, node-indexed**: `isG v` says node `v` is driven by a collapsed gate `gOf v` with pin chains
`pcsOf v`, kept pins `keepOf v` and constants `cstOf v`. -/
def selNet (isG : Nat → Bool) (gOf : Nat → Gate) (pcsOf : Nat → List PinChain) (keepOf : Nat → List Nat)
    (cstOf : Nat → Nat → Option Bool) : TNet Nat where
  gate := isG
  pins v := (keepOf v).map (srcOf (pcsOf v))
  F v l := (gOf v).init.testBit (addr (gOf v).k (fill (keepOf v) (cstOf v) l))
  lo v w := sumLoC p c1 (pinArcs (gOf v) (pcsOf v) (pinOf (keepOf v) (srcOf (pcsOf v)) w))
  hi v w := sumHiC p c2 (pinArcs (gOf v) (pcsOf v) (pinOf (keepOf v) (srcOf (pcsOf v)) w))
end

/-- **The read hypotheses of `TBehX` on the slice net.** -/
theorem selNet_reads {p : DelayPar} (hp : Sane p) {c1 c2 c : ℚ} (h1 : c1 ≤ c) (h2 : c ≤ c2)
    {isG : Nat → Bool} {gOf : Nat → Gate} {pcsOf : Nat → List PinChain} {keepOf : Nat → List Nat}
    {cstOf : Nat → Nat → Option Bool} {x : Beh} {t0 H : Nat} (S : Nat → Nat)
    (hout : ∀ v, isG v = true → (gOf v).out = v)
    (hC : ∀ v, isG v = true → CGateOK p c (gOf v) (srcOf (pcsOf v)) (pinArcs (gOf v) (pcsOf v)) (S v) x)
    (hS : ∀ v, isG v = true → S v ≤ t0 + 1)
    (hnd : ∀ v, isG v = true → ((keepOf v).map (srcOf (pcsOf v))).Nodup)
    (hklt : ∀ v, isG v = true → ∀ i ∈ keepOf v, i < (gOf v).k)
    (hord : ∀ v, isG v = true → ∀ i, i < (gOf v).k → ∀ a ∈ pinArcs (gOf v) (pcsOf v) i, ArcOrd a)
    (hrest : ∀ v, isG v = true → ∀ i, i < (gOf v).k → i ∉ keepOf v →
      (cstOf v i).isSome ∨ (cstOf v i = none ∧ Dead (gOf v) i))
    (hcst : ∀ v, isG v = true → ∀ i b, i < (gOf v).k → i ∉ keepOf v → cstOf v i = some b →
      ∀ s, t0 ≤ s + H → x (srcOf (pcsOf v) i) s = b)
    (hH : ∀ v, isG v = true → ∀ i, i < (gOf v).k → sumHiC p c2 (pinArcs (gOf v) (pcsOf v) i) ≤ H) :
    ∃ r : Nat → Nat → Nat → Nat,
      (∀ v w t, (selNet p c1 c2 isG gOf pcsOf keepOf cstOf).gate v = true →
        w ∈ (selNet p c1 c2 isG gOf pcsOf keepOf cstOf).pins v → t0 < t →
        (selNet p c1 c2 isG gOf pcsOf keepOf cstOf).lo v w ≤ t - r v w t ∧
        t - r v w t ≤ (selNet p c1 c2 isG gOf pcsOf keepOf cstOf).hi v w ∧ r v w t ≤ t ∧ t0 ≤ r v w t + H) ∧
      (∀ v w t t', (selNet p c1 c2 isG gOf pcsOf keepOf cstOf).gate v = true →
        w ∈ (selNet p c1 c2 isG gOf pcsOf keepOf cstOf).pins v → t0 < t → t ≤ t' → r v w t ≤ r v w t') ∧
      (∀ v t, (selNet p c1 c2 isG gOf pcsOf keepOf cstOf).gate v = true → t0 < t →
        x v t = (selNet p c1 c2 isG gOf pcsOf keepOf cstOf).F v
          (((selNet p c1 c2 isG gOf pcsOf keepOf cstOf).pins v).map fun w => x w (r v w t))) := by
  apply reads_of_sel hp h1 h2
  · intro v hv
    refine ⟨gOf v, srcOf (pcsOf v), pinArcs (gOf v) (pcsOf v), S v, keepOf v, cstOf v,
      ⟨rfl, hnd v hv, hout v hv, hklt v hv, fun l => rfl, hord v hv, ?_, ?_, ?_⟩, hC v hv, hS v hv, hcst v hv⟩
    · intro i hi; show sumLoC p c1 (pinArcs (gOf v) (pcsOf v) (pinOf (keepOf v) (srcOf (pcsOf v)) (srcOf (pcsOf v) i))) ≤ _
      rw [pinOf_src (hnd v hv) hi]
    · intro i hi; show _ ≤ sumHiC p c2 (pinArcs (gOf v) (pcsOf v) (pinOf (keepOf v) (srcOf (pcsOf v)) (srcOf (pcsOf v) i)))
      rw [pinOf_src (hnd v hv) hi]
    · intro i hi hni
      rcases hrest v hv i hi hni with h | h
      · exact Or.inl ⟨h, hH v hv i hi⟩
      · exact Or.inr h
  · intro v w hv hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
    show sumHiC p c2 (pinArcs (gOf v) (pcsOf v) (pinOf (keepOf v) (srcOf (pcsOf v)) (srcOf (pcsOf v) i))) ≤ H
    rw [pinOf_src (hnd v hv) hi]
    exact hH v hv i (hklt v hv i hi)

/-- A route's slow-end sum is bounded by the gate's collapsed start time (any corner `c ≤ 1`). -/
theorem hiC_le_dmax {p : DelayPar} (hp : Sane p) {c : ℚ} (hc : c ≤ 1) {e : Arc} (he : ArcOrd e) :
    hiC p c e ≤ dmax p e := by
  unfold hiC dmax
  obtain ⟨hk0, _, hg⟩ := hp
  have hl : lerp e.fmax e.smax c ≤ e.smax := by
    unfold lerp
    have : (e.fmax : ℚ) ≤ e.smax := by exact_mod_cast he.2
    nlinarith
  have h1 : (1 + p.κ) * lerp e.fmax e.smax c * p.g ≤ (1 + p.κ) * (e.smax : ℚ) * p.g := by
    apply mul_le_mul_of_nonneg_right _ hg.le
    exact mul_le_mul_of_nonneg_left hl (by linarith)
  exact Int.toNat_le_toNat (le_trans (Int.floor_le_floor h1) (Int.floor_le_ceil _))

theorem le_sum_of_mem' : ∀ {l : List Nat} {a : Nat}, a ∈ l → a ≤ l.sum
  | b :: l, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := le_sum_of_mem' h; simp only [List.sum_cons]; omega

theorem sumHiC_le_cStart {p : DelayPar} (hp : Sane p) {c : ℚ} (hc : c ≤ 1) {g : Gate} {pcs : List PinChain}
    {i : Nat} (hi : i < g.k) (hord : ∀ a ∈ pinArcs g pcs i, ArcOrd a) : sumHiC p c (pinArcs g pcs i) ≤ cStart p g pcs := by
  have hsum : ∀ (cs : List Gate), (∀ a ∈ cs.map arc0, ArcOrd a) → sumHiC p c (cs.map arc0) ≤ chainStart p cs := by
    intro cs
    induction cs with
    | nil => intro _; simp [sumHiC, chainStart]
    | cons d ds ih =>
      intro h
      have h0 := hiC_le_dmax hp hc (h (arc0 d) (by simp))
      have := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      simp only [sumHiC, List.map_cons, List.sum_cons, chainStart] at this ⊢
      omega
  have hpin := hiC_le_dmax hp hc (hord _ (List.mem_cons_self ..))
  have hch := hsum _ (fun a ha => hord a (List.mem_cons_of_mem _ ha))
  have hterm : chainStart p (pcs.getD i ⟨0, []⟩).chain + dmax p (g.arcs.getD i default) ≤
      ((List.range g.k).map fun i => chainStart p (pcs.getD i ⟨0, []⟩).chain + dmax p (g.arcs.getD i default)).sum :=
    le_sum_of_mem' (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
  have e1 : sumHiC p c (pinArcs g pcs i) =
      hiC p c (g.arcs.getD i default) + sumHiC p c ((pcs.getD i ⟨0, []⟩).chain.map arc0) := by
    simp [pinArcs, sumHiC]
  rw [e1]; unfold cStart; omega

end Formal.Cells.SliceNet
