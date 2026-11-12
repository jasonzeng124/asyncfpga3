import Formal.Cells.SliceNetPS.Final

/-!
# Formal.Cells.SliceNetPS.TBeh — `TBehX` on THE target's slice nets, and dispatch over a finite slice cover
(shard B, 2026-11-10)

**Problem, plainly.** C's certificate theorems (`Net/AO`, `timedA_follows*`, `timedA_live*`) conclude safety and
liveness for every run of a timed net satisfying `TBehX`. To use them on THE statement, (1) every Spec behaviour must
be such a run, and (2) since a certificate is built for one integer net, finitely many slice certificates must cover
every corner.

**Proved.**
* `target_tbehX`: for every sane `p` with `κ < 1` and every behaviour of THE theorem's circuit there is a corner
  `c ∈ [0,1]` such that for every slice `[c1, c2] ∋ c` (`0 ≤ c1`, `c2 ≤ 1`), every `t0 ≥ 2H`
  (`H = ⌈(1+κ)g⌉·33,002`), every data marking `dat` and environment rule `envEn`: IF the exact nodes are quiet on
  `[t0 - H, t0]` and every exact non-gate node's change is allowed by `envEn` (TBehX's `quiet` and `env` fields,
  kept as hypotheses), THEN there are read times `r` with `TBehX (tnPS p c1 c2) dat envEn x r t0 H`.
* `target_by_slices`: given slice points `a, b, s…` in `[0,1]`, first 0 and last 1, a property `P` of behaviours
  holds for EVERY behaviour as soon as, for each consecutive pair `[lo, hi]`, it holds for every behaviour that has
  read times on `tnPS p lo hi` from every `t0 ≥ 2H` (the `rd/mono/geq/lo1` part of `TBehX`).

* `tnPS_lo_nat`, `tnPS_hi_nat`: for `p = ⟨gn/gd, kn/kd⟩` and rational slice ends, every bound is a Nat sum
  (`loN`/`hiN`), so certificate checks on `tnPS` need no ℚ in the kernel.

**Not shown here:** the `quiet` and `env` fields for THE target (reset island, `AO/EnvHS`); any certificate.
-/

namespace Formal.Cells.SliceNetPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Net.CViewPS Formal.Net.OccNet
  Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Cells.CornerSlice Formal.Cells.StartBound
  Formal.Cells.StartBoundPS

/-- The read part of `TBehX` on a slice net, from `t0`. -/
def ReadsOn (p : DelayPar) (c1 c2 : ℚ) (x : Beh) (t0 : Nat) : Prop :=
  ∃ r : Nat → Nat → Nat → Nat,
    (∀ v w t, (tnPS p c1 c2).gate v = true → w ∈ (tnPS p c1 c2).pins v → t0 < t →
      (tnPS p c1 c2).lo v w ≤ t - r v w t ∧ t - r v w t ≤ (tnPS p c1 c2).hi v w ∧ r v w t ≤ t ∧
      t0 ≤ r v w t + mOf p * HB) ∧
    (∀ v w t t', (tnPS p c1 c2).gate v = true → w ∈ (tnPS p c1 c2).pins v → t0 < t → t ≤ t' →
      r v w t ≤ r v w t') ∧
    (∀ v t, (tnPS p c1 c2).gate v = true → t0 < t →
      x v t = (tnPS p c1 c2).F v (((tnPS p c1 c2).pins v).map fun w => x w (r v w t)))

theorem target_tbehX {p : DelayPar} (hp : Sane p) (hk : p.κ < 1) {x : Beh}
    (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ (c1 c2 : ℚ) (t0 : Nat) (dat : Nat → Bool) (envEn : Nat → (Nat → Bool) → Bool),
      c1 ≤ c → c ≤ c2 → 0 ≤ c1 → c2 ≤ 1 → 2 * (mOf p * HB) ≤ t0 →
      (∀ u s, dat u = false → t0 ≤ s + mOf p * HB → s ≤ t0 → x u s = x u t0) →
      (∀ u t, (tnPS p c1 c2).gate u = false → dat u = false → t0 < t → x u t ≠ x u (t - 1) →
        envEn u (fun w => x w (t - 1)) = true) →
      ∃ r, TBehX (tnPS p c1 c2) dat envEn x r t0 (mOf p * HB) := by
  obtain ⟨c, hc0, hc1, h⟩ := target_reads_slice_H hp hb
  refine ⟨c, hc0, hc1, fun c1 c2 t0 dat envEn h1 h2 h0 hc2 ht0 hq he => ?_⟩
  obtain ⟨r, hrd, hmono, hgeq⟩ := h c1 c2 t0 h1 h2 hc2 ht0
  exact ⟨r, ⟨hq, hrd, tnPS_lo1 hp hk h0, hmono, hgeq, he⟩⟩

/-- **Certificates on finitely many slices cover every behaviour.** -/
theorem target_by_slices {p : DelayPar} (hp : Sane p) (P : Beh → Prop) (a b : ℚ) (s : List ℚ)
    (ha : a = 0) (hlast : (b :: s).getLast (List.cons_ne_nil _ _) = 1)
    (hin : ∀ q ∈ a :: b :: s, 0 ≤ q ∧ q ≤ 1)
    (hslice : ∀ i lo hi, (a :: b :: s)[i]? = some lo → (a :: b :: s)[i + 1]? = some hi →
      ∀ x, Behaves p (circuit net boundary) x → (∀ t0, 2 * (mOf p * HB) ≤ t0 → ReadsOn p lo hi x t0) → P x)
    {x : Beh} (hb : Behaves p (circuit net boundary) x) : P x := by
  obtain ⟨c, hc0, hc1, h⟩ := target_reads_slice_H hp hb
  obtain ⟨i, lo, hi, e1, e2, l1, l2⟩ := slice_cover s a b c (by rw [ha]; exact hc0) (by rw [hlast]; exact hc1)
  have hhi : hi ≤ 1 := (hin hi (List.mem_of_getElem? e2)).2
  exact hslice i lo hi e1 e2 x hb (fun t0 ht0 => h lo hi t0 l1 l2 hhi ht0)

end Formal.Cells.SliceNetPS

namespace Formal.Cells.SliceNetPS
open Formal.Target Formal.Timing.SpecChain Formal.Net.OccNet Formal.Net.OccNet.Bridge Formal.Cells.CornerSlice
  Formal.Timing.Huffman Formal.Target.DecodedPS Formal.Net.CViewPS Formal.Cells.SliceReads
  Formal.Cells.SliceNet

/-- **Nat forms of the slice net's bounds** (for `decide`): with `p = ⟨gn/gd, kn/kd⟩` and slice ends `cn1/cd`,
`cn2/cd`, every `lo`/`hi` is a sum of Nat ceilings/floors (`CornerSlice.loN`/`hiN`) along the pin's route. -/
theorem tnPS_lo_nat {kn kd gn gd cn1 cn2 cd : Nat} (hk : kn ≤ kd) (hc : cn1 ≤ cd) (hkd : 0 < kd) (hgn : 0 < gn)
    (hgd : 0 < gd) (hcd : 0 < cd) (cx : ℚ) (v w : Nat) :
    (tnPS ⟨(gn : ℚ) / gd, (kn : ℚ) / kd⟩ ((cn1 : ℚ) / cd) cx).lo v w =
      ((pinArcs (gAt cs 2500 v) (pcsPS v) (pinOf (keepPSN v) (srcOf (pcsPS v)) w)).map
        (loN kn kd gn gd cn1 cd)).sum := by
  show sumLoC _ _ _ = _
  exact sumLoC_eq hk hc hkd hgn hgd hcd _

theorem tnPS_hi_nat {kn kd gn gd cn2 cd : Nat} (hc : cn2 ≤ cd) (hkd : 0 < kd)
    (hgd : 0 < gd) (hcd : 0 < cd) (cx : ℚ) (v w : Nat) :
    (tnPS ⟨(gn : ℚ) / gd, (kn : ℚ) / kd⟩ cx ((cn2 : ℚ) / cd)).hi v w =
      ((pinArcs (gAt cs 2500 v) (pcsPS v) (pinOf (keepPSN v) (srcOf (pcsPS v)) w)).map
        (hiN kn kd gn gd cn2 cd)).sum := by
  show sumHiC _ _ _ = _
  exact sumHiC_eq hc hkd hgd hcd _

end Formal.Cells.SliceNetPS
