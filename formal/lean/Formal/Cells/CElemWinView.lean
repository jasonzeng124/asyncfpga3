import Formal.Cells.ViewPS
import Formal.Cells.CElemPS.Defs
import Formal.Cells.SpecCElemWin

/-!
# Formal.Cells.CElemWinView — THE target's mux joins switch only when forced while their select is held

Shard B, THE goal, S3. The windowed counterpart of `CElemView` for gates that are C-elements only while one pin (the
select `sp`) is held at a value `sv` (THE target's mux joins `j0 = C(x_req, ctl_req·¬s)`, `j1 = C(y_req, ctl_req·s)`):
`target_celemw_forced`: in every behaviour of THE circuit, at its corner, for every listed join, on any window
`[S0, E]` on which the select's source shows `sv` (from `S0 - H`), given hA (up to `E`), the timing premises, the
reset low and a quiet start, every toggle in `[S0, E]` is forced and toggles are `M` apart. The select's stability is
the mux's control-channel contract (bdc: s is held from ctl_req rise to ctl_ack fall), an explicit premise here.
-/

namespace Formal.Cells.CElemWinView
open Formal.Target Formal.Target.DecodedPS Formal.Cells.RaceLinkPS Formal.Timing.SpecSettle
  Formal.Timing.SpecChain Formal.Net.CViewPS Formal.Cells.ViewPS Formal.Cells.SpecCElemFact
  Formal.Cells.SpecCElem Formal.Cells.SpecFbChain Formal.Cells.SpecCElemWin

structure CRow where
  q : Nat
  j : Nat
  sp : Nat
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
  decide (r.sp < r.g.k) && r.sp != r.j && !(fl r.ci r.sp) &&
  (List.range r.g.k).all fun i => i == r.j || fl r.ci i || i == r.sp || heldOK r i

theorem src_eq (r : CRow) {i : Nat} (hi : i < r.pins.length) : r.src i = (r.pins.getD i ([], 0)).2 := by
  simp only [CRow.src, pcsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some]

/-- **THE target's listed C-elements switch only when forced, in every behaviour of the circuit.** -/
theorem target_celemw_forced (L : List CRow) (hL : L.all crowOK = true) {p : DelayPar} (hp : Sane p) {x : Beh}
    (hb' : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ r ∈ L, ∀ (Δ : Nat → Nat) (H M S0 E i0 : Nat), r.S p ≤ S0 →
      (∀ i, i < r.g.k → r.hi p c i ≤ H) → M ≤ H → 1 ≤ r.lo p c r.j →
      (∀ i, i < r.g.k → i ≠ r.j → fl r.ci i = true → r.hi p c i ≤ M) →
      (∀ i, i < r.g.k → i ≠ r.j → fl r.ci i = true → r.hi p c r.j ≤ Δ i + r.lo p c i) →
      i0 < r.g.k → i0 ≠ r.j → fl r.ci i0 = true → M ≤ Δ i0 + r.lo p c i0 →
      (∀ t, S0 ≤ t + H → x CElemPS.rstNode t = false) →
      (∀ t, S0 ≤ t + H → t ≤ E → x (r.src r.sp) t = fl r.ov r.sp) →
      (∀ i, i < r.g.k → i ≠ r.j → fl r.ci i = true → ∀ τ, S0 ≤ τ + H → τ ≤ E →
        (x (r.src i) (τ - 1) ^^ fl r.pol i) ≠ (x (r.src i) τ ^^ fl r.pol i) →
        ∀ s, τ - Δ i ≤ s → s ≤ τ → x r.q s = (x (r.src i) (τ - 1) ^^ fl r.pol i)) →
      (∀ u, S0 < u + H → u ≤ S0 → ¬ Tog (x r.q) u) →
      ∀ t, S0 ≤ t → t ≤ E → Tog (x r.q) t →
        (∀ i, i < r.g.k → i ≠ r.j → fl r.ci i = true →
          ∃ s, s + r.lo p c i ≤ t ∧ t ≤ s + r.hi p c i ∧ (x (r.src i) s ^^ fl r.pol i) = x r.q t) ∧
        (∀ u, u < t → t < u + M → ¬ Tog (x r.q) u) := by
  obtain ⟨c, hc0, hc1, hcol⟩ := view_collapse hp hb' (L.map fun r => (r.q, r.pins)) (by
    simp only [List.all_map, List.all_eq_true] at hL ⊢
    intro r hr
    have := hL r hr
    simp only [crowOK, Bool.and_eq_true] at this
    exact this.1.1.1.1.1.1.2)
  refine ⟨c, hc0, hc1, fun r hr Δ H M S0 E i0 hS hH hMH hloj hM hloop hi0k hi0j hi0c hi0 hrst hsel hA hq0 => ?_⟩
  have hok : crowOK r = true := by simp only [List.all_eq_true] at hL; exact hL r hr
  simp only [crowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    bne_iff_ne, ne_eq, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, hj⟩, hf⟩, -⟩, hfb⟩, hout⟩, hsp⟩, hspj⟩, hspc⟩, hheld⟩ := hok
  have hg : CGateOK p c r.g r.src r.arcs (r.S p) x := hcol _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hout' : r.g.out = r.q := hout
  have hfb' : r.src r.j = r.g.out := by rw [src_eq r (by omega), hfb, hout']
  obtain ⟨F, hFm, hF⟩ := hg
  have hb := cbands_of_sums (p := p) (c := c) (k := r.g.k) r.arcs
  have key := celem_forced_win hb F hFm hF hj hfb' hloj (fl r.ci) (fl r.pol) (fl r.ov) Δ H M S0 E hS
    hH hMH hM hloop i0 hi0k hi0j hi0c hi0 (hall_of_cfact hf) (hhold_of_cfact hf hj)
    (fun i hi' hij hci t ht htE => by
      by_cases hisp : i = r.sp
      · subst hisp; exact hsel t ht htE
      have h := hheld i hi'
      simp only [Bool.or_eq_true, beq_iff_eq, hij, false_or, hci, Bool.false_eq_true, hisp] at h
      rw [src_eq r (by omega)]
      simp only [heldOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
      rcases h with ⟨hs, hov⟩ | ⟨⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩, hs5⟩
      · rw [hs, hov]; exact hrst t ht
      · rw [const_hold hb' hs1 hs2 hs3 hs4 t, hs5])
    (by rw [hout']; exact hA) (by rw [hout']; exact hq0)
  intro t ht htE htog
  rw [← hout'] at htog ⊢
  obtain ⟨h1, h2⟩ := key t ht htE htog
  refine ⟨fun i hik hij hci => ?_, fun u a b => by rw [← hout'] at *; exact h2 u a b⟩
  obtain ⟨hr, -⟩ := hF t (by omega)
  have hd := hb i hik _ (hr i hik).2
  dsimp only at hd
  have := (hr i hik).1
  refine ⟨F i t, ?_, ?_, h1 i hik hij hci⟩ <;> simp only [CRow.lo, CRow.hi] <;> omega

end Formal.Cells.CElemWinView
