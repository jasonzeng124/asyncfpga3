import Formal.Cells.ViewPS
import Formal.Cells.CElemPS.Defs
import Formal.Cells.SpecCElem

/-!
# Formal.Cells.CElemView — THE target's C-elements switch only when forced, in every behaviour of its circuit

Shard B, THE goal, S3.

## Problem, plainly
Put together, for gates of THE target's own Lean netlist: in every behaviour of THE theorem's circuit (`Behaves p
(circuit net boundary) x`, any `0 ≤ κ ≤ 1`, `g > 0`), does a listed C-element switch only when forced, given only its
environment (`hA`), the timing premises, the reset held low, and a quiet start? Here the collapsed relation comes
from `Behaves` (`ViewPS.view_collapse`, through the row's own checked copy chains), the INIT facts from `cfact`, the
held pins from the constant gates' own relation (`ViewPS.const_hold`) or the reset hypothesis, and the bands from the
summed integer window ends (`SpecFbChain.cbands_of_sums`).

## Results
* `CRow`, `crowOK` (Bool row check), `target_celem_forced` (for every list of rows passing the check).
The generated instance (`CElemViewPS`) supplies THE target's rows.

## Not covered
`hA` and the timing premises (the network's and C's); `Δ`, `M`, `H`, `S0` are free parameters of the conclusion.
-/

namespace Formal.Cells.CElemView
open Formal.Target Formal.Target.DecodedPS Formal.Cells.RaceLinkPS Formal.Timing.SpecSettle
  Formal.Timing.SpecChain Formal.Net.CViewPS Formal.Cells.ViewPS Formal.Cells.SpecCElemFact
  Formal.Cells.SpecCElem Formal.Cells.SpecFbChain

structure CRow where
  q : Nat
  j : Nat
  ci : List Bool
  pol : List Bool
  ov : List Bool
  pins : Pins

def CRow.g (r : CRow) : Gate := gateAt r.q
def CRow.src (r : CRow) (i : Nat) : Nat := ((pcsOf r.pins).getD i ⟨0, []⟩).src
def CRow.arcs (r : CRow) : Nat → List Arc := pinArcs r.g (pcsOf r.pins)
def CRow.S (p : DelayPar) (r : CRow) : Nat := cStart p r.g (pcsOf r.pins)
def CRow.lo (p : DelayPar) (c : ℚ) (r : CRow) (i : Nat) : Nat :=
  ((r.arcs i).map (Formal.Cells.Ua1Static.lo p.g p.κ c)).sum.toNat
def CRow.hi (p : DelayPar) (c : ℚ) (r : CRow) (i : Nat) : Nat :=
  ((r.arcs i).map (Formal.Cells.Ua1Static.hi p.g p.κ c)).sum.toNat

/-- A held pin's source is either the reset node (value false) or a constant gate of the circuit with the value. -/
def heldOK (r : CRow) (i : Nat) : Bool :=
  let s := (r.pins.getD i ([], 0)).2
  (s == CElemPS.rstNode && !(fl r.ov i)) ||
    (decide (s < 186873) && keepPS (gateAt s) && (gateAt s).k == 0 && (gateAt s).out == s &&
      (gateAt s).init.testBit 0 == fl r.ov i)

def crowOK (r : CRow) : Bool :=
  r.g.k == r.pins.length && decide (r.j < r.g.k) && cfact r.g.k r.g.init r.j (fl r.ci) (fl r.pol) (fl r.ov) &&
  viewOK r.q r.pins && (r.pins.getD r.j ([], 0)).2 == r.q && (gateAt r.q).out == r.q &&
  (List.range r.g.k).all fun i => i == r.j || fl r.ci i || heldOK r i

theorem src_eq (r : CRow) {i : Nat} (hi : i < r.pins.length) : r.src i = (r.pins.getD i ([], 0)).2 := by
  simp only [CRow.src, pcsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some]

/-- **THE target's listed C-elements switch only when forced, in every behaviour of the circuit.** -/
theorem target_celem_forced (L : List CRow) (hL : L.all crowOK = true) {p : DelayPar} (hp : Sane p) {x : Beh}
    (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ r ∈ L, ∀ (Δ : Nat → Nat) (H M S0 i0 : Nat), r.S p ≤ S0 →
      (∀ i, i < r.g.k → r.hi p c i ≤ H) → M ≤ H → 1 ≤ r.lo p c r.j →
      (∀ i, i < r.g.k → i ≠ r.j → fl r.ci i = true → r.hi p c i ≤ M) →
      (∀ i, i < r.g.k → i ≠ r.j → fl r.ci i = true → r.hi p c r.j ≤ Δ i + r.lo p c i) →
      i0 < r.g.k → i0 ≠ r.j → fl r.ci i0 = true → M ≤ Δ i0 + r.lo p c i0 →
      (∀ t, S0 ≤ t + H → x CElemPS.rstNode t = false) →
      (∀ i, i < r.g.k → i ≠ r.j → fl r.ci i = true → ∀ τ, S0 ≤ τ + H →
        (x (r.src i) (τ - 1) ^^ fl r.pol i) ≠ (x (r.src i) τ ^^ fl r.pol i) →
        ∀ s, τ - Δ i ≤ s → s ≤ τ → x r.q s = (x (r.src i) (τ - 1) ^^ fl r.pol i)) →
      (∀ u, S0 < u + H → u ≤ S0 → ¬ Tog (x r.q) u) →
      ∀ t, S0 ≤ t → Tog (x r.q) t →
        (∀ i, i < r.g.k → i ≠ r.j → fl r.ci i = true →
          ∃ s, s + r.lo p c i ≤ t ∧ t ≤ s + r.hi p c i ∧ (x (r.src i) s ^^ fl r.pol i) = x r.q t) ∧
        (∀ u, u < t → t < u + M → ¬ Tog (x r.q) u) := by
  obtain ⟨c, hc0, hc1, hcol⟩ := view_collapse hp hb (L.map fun r => (r.q, r.pins)) (by
    simp only [List.all_map, List.all_eq_true] at hL ⊢
    intro r hr
    have := hL r hr
    simp only [crowOK, Bool.and_eq_true] at this
    exact this.1.1.1.2)
  refine ⟨c, hc0, hc1, fun r hr Δ H M S0 i0 hS hH hMH hloj hM hloop hi0k hi0j hi0c hi0 hrst hA hq0 => ?_⟩
  have hok : crowOK r = true := by simp only [List.all_eq_true] at hL; exact hL r hr
  simp only [crowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨hk, hj⟩, hf⟩, -⟩, hfb⟩, hout⟩, hheld⟩ := hok
  have hg : CGateOK p c r.g r.src r.arcs (r.S p) x := hcol _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hout' : r.g.out = r.q := hout
  have hfb' : r.src r.j = r.g.out := by rw [src_eq r (by omega), hfb, hout']
  have key := celem_forced' hg (cbands_of_sums r.arcs) hj hfb' hloj (fl r.ci) (fl r.pol) (fl r.ov) Δ H M S0 hS
    hH hMH hM hloop i0 hi0k hi0j hi0c hi0 (hall_of_cfact hf) (hhold_of_cfact hf hj)
    (fun i hi' hij hci t ht => by
      have h := hheld i hi'
      simp only [Bool.or_eq_true, beq_iff_eq, hij, false_or, hci, Bool.false_eq_true] at h
      rw [src_eq r (by omega)]
      simp only [heldOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
      rcases h with ⟨hs, hov⟩ | ⟨⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩, hs5⟩
      · rw [hs, hov]; exact hrst t ht
      · rw [const_hold hb hs1 hs2 hs3 hs4 t, hs5])
    (by rw [hout']; exact hA) (by rw [hout']; exact hq0)
  rw [hout'] at key
  exact key

end Formal.Cells.CElemView
