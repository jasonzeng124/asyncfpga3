import Formal.Cells.CElemView
import Formal.Cells.SpecLatchFact

/-!
# Formal.Cells.LatchView — THE target's latches close cleanly, in every behaviour of its circuit

Shard B, THE goal, S3. The latch counterpart of `CElemView`: for every row list passing `lrowOK` (the netlist gate's
INIT is a latch, `lfact`; every pin's copy chain checked, `viewOK`; feedback source = own output; held pins' sources
= the reset node at false or constant gates of the stated value), in every behaviour of THE circuit, at its corner,
every listed latch whose enable source is open on `[τ - We, τ - 1]` and closed on `[τ, E]`, whose data source shows
`v` on `[τ - Wd, τ + hi e]`, with `τ + hi e ≤ A + We`, `τ + hi d ≤ A + Wd`, `A + hi j ≤ τ + lo e` (its own summed
integer window ends) and the reset low from `A - H` on, holds `v` on `[A, E + lo e]` (`target_latch_close`).

Not covered: that the network supplies the enable and data windows (the bundling obligations).
-/

namespace Formal.Cells.LatchView
open Formal.Target Formal.Target.DecodedPS Formal.Cells.RaceLinkPS Formal.Timing.SpecSettle
  Formal.Timing.SpecChain Formal.Net.CViewPS Formal.Cells.ViewPS Formal.Cells.SpecCElemFact
  Formal.Cells.SpecLatchFact Formal.Cells.SpecLatch Formal.Cells.SpecFbChain

structure LRow where
  q : Nat
  e : Nat
  d : Nat
  j : Nat
  pe : Bool
  pd : Bool
  held : List Bool
  ov : List Bool
  pins : Pins

def LRow.g (r : LRow) : Gate := gateAt r.q
def LRow.src (r : LRow) (i : Nat) : Nat := ((pcsOf r.pins).getD i ⟨0, []⟩).src
def LRow.arcs (r : LRow) : Nat → List Arc := pinArcs r.g (pcsOf r.pins)
def LRow.S (p : DelayPar) (r : LRow) : Nat := cStart p r.g (pcsOf r.pins)
def LRow.lo (p : DelayPar) (c : ℚ) (r : LRow) (i : Nat) : Nat :=
  ((r.arcs i).map (Formal.Cells.Ua1Static.lo p.g p.κ c)).sum.toNat
def LRow.hi (p : DelayPar) (c : ℚ) (r : LRow) (i : Nat) : Nat :=
  ((r.arcs i).map (Formal.Cells.Ua1Static.hi p.g p.κ c)).sum.toNat

def lheldOK (r : LRow) (i : Nat) : Bool :=
  let s := (r.pins.getD i ([], 0)).2
  (s == CElemPS.rstNode && !(fl r.ov i)) ||
    (decide (s < 186873) && keepPS (gateAt s) && (gateAt s).k == 0 && (gateAt s).out == s &&
      (gateAt s).init.testBit 0 == fl r.ov i)

def lrowOK (r : LRow) : Bool :=
  r.g.k == r.pins.length && decide (r.e < r.g.k) && decide (r.d < r.g.k) && decide (r.j < r.g.k) &&
  r.e != r.d && r.e != r.j && r.d != r.j && !(fl r.held r.e) && !(fl r.held r.j) &&
  lfact r.g.k r.g.init r.e r.d r.j r.pe r.pd (fl r.held) (fl r.ov) &&
  viewOK r.q r.pins && (r.pins.getD r.j ([], 0)).2 == r.q && (gateAt r.q).out == r.q &&
  (List.range r.g.k).all fun i => !(fl r.held i) || lheldOK r i

theorem src_eq (r : LRow) {i : Nat} (hi : i < r.pins.length) : r.src i = (r.pins.getD i ([], 0)).2 := by
  simp only [LRow.src, pcsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some]

/-- **THE target's listed latches close cleanly and hold, in every behaviour of the circuit.** -/
theorem target_latch_close (L : List LRow) (hL : L.all lrowOK = true) {p : DelayPar} (hp : Sane p) {x : Beh}
    (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ r ∈ L, ∀ (τ E We Wd A H : Nat) (v : Bool), r.S p ≤ A →
      (∀ i, i < r.g.k → r.hi p c i ≤ H) → 1 ≤ r.lo p c r.j →
      (∀ t, A ≤ t + H → x CElemPS.rstNode t = false) →
      (∀ t, τ ≤ t + We → t < τ → (x (r.src r.e) t ^^ r.pe) = true) →
      (∀ t, τ ≤ t → t ≤ E → (x (r.src r.e) t ^^ r.pe) = false) →
      (∀ t, τ ≤ t + Wd → t ≤ τ + r.hi p c r.e → (x (r.src r.d) t ^^ r.pd) = v) →
      τ + r.hi p c r.e ≤ A + We → τ + r.hi p c r.d ≤ A + Wd → A + r.hi p c r.j ≤ τ + r.lo p c r.e →
      ∀ s, A ≤ s → s ≤ E + r.lo p c r.e → x r.q s = v := by
  obtain ⟨c, hc0, hc1, hcol⟩ := view_collapse hp hb (L.map fun r => (r.q, r.pins)) (by
    simp only [List.all_map, List.all_eq_true] at hL ⊢
    intro r hr
    have := hL r hr
    simp only [lrowOK, Bool.and_eq_true] at this
    exact this.1.1.1.2)
  refine ⟨c, hc0, hc1, fun r hr τ E We Wd A H v hS hH hloj hrst hop hcl hdat hAe hAd hloop => ?_⟩
  have hok : lrowOK r = true := by simp only [List.all_eq_true] at hL; exact hL r hr
  simp only [lrowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    bne_iff_ne, ne_eq, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, he⟩, hd⟩, hj⟩, hed⟩, hej⟩, hdj⟩, -⟩, -⟩, hf⟩, -⟩, hfb⟩, hout⟩, hheld⟩ := hok
  have hg : CGateOK p c r.g r.src r.arcs (r.S p) x := hcol _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hout' : r.g.out = r.q := hout
  have hfb' : r.src r.j = r.g.out := by rw [src_eq r (by omega), hfb, hout']
  have key := latch_close hg (cbands_of_sums r.arcs) he hd hj hed hej hdj hfb' hloj r.pe r.pd (fl r.held) (fl r.ov)
    (hopen_of_lfact hf he hd) (hclosed_of_lfact hf he hj) τ E We Wd A H v hH
    (fun i hi' hh t ht => by
      have h := hheld i hi'
      simp only [hh, Bool.not_true, Bool.false_or] at h
      rw [src_eq r (by omega)]
      simp only [lheldOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
      rcases h with ⟨hs, hov⟩ | ⟨⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩, hs5⟩
      · rw [hs, hov]; exact hrst t ht
      · rw [const_hold hb hs1 hs2 hs3 hs4 t, hs5])
    hop hcl hdat hS hAe hAd hloop
  rw [hout'] at key
  exact key

end Formal.Cells.LatchView
