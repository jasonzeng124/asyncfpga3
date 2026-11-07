import Formal.Cells.CertMarginPS

/-!
# Formal.Cells.CertRaceAll — a race obligation from a chain certificate, generically (every behaviour)

Shard B, 2026-11-07.

## Problem, plainly
For a storage node `n` of THE target (a C-element whose acknowledge comes back through a path of LUTs), show in
every behaviour, at g = 1 and κ ≤ 83/200: after `n` flips (at `e + 1`), the source of `n`'s acknowledge pin keeps its
old value long enough that every read of that pin within `n`'s own feedback-loop upper delay sees the old value.
This is the switch obligation of `SpecFbChain.cfb_switch` (B's RaceTablePS rows, until now checked only on simulated
paths).

## Proved (standard axioms)
* `chainShape`, `psum_chain`: in a chain-shaped certificate (row 0 reads the cause, row i reads row i-1), `psum`
  of the last row is the sum of the rows' path-pin lower bands.
* `race_holds`: from `certOK`, `singlePath`, `chainShape` and the two integer arc-sum facts on
  (path pins' arcs ++ the node's acknowledge-pin arcs) vs (the node's feedback-pin arcs), with the certificate's
  value premises: the acknowledge source shows its old value at every `u ≥` the last row's window start with
  `u + lo(ack pin) ≤ e + hi(feedback pin)`.
-/

namespace Formal.Cells.CertRaceAll
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecChain Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS
  Formal.Cells.RaceCornersPS

def chainShape (rows : List CRow) : Bool :=
  (List.range rows.length).all fun i =>
    let r := rows.getD i default
    let l := r.lab (pathPin r)
    if i = 0 then l.kind == 0 else (l.kind == 2 && l.k == i - 1)

/-- The path pins' arcs, row by row, concatenated. -/
def pathArcs (rows : List CRow) : List Arc :=
  ((List.range rows.length).map fun i => (rows.getD i default).r.arcs (pathPin (rows.getD i default))).flatten

def loSum (p : DelayPar) (c : ℚ) (rows : List CRow) (n : Nat) : Nat :=
  ((List.range n).map fun i => (rows.getD i default).r.lo p c (pathPin (rows.getD i default))).sum

theorem psum_chain {p : DelayPar} {c : ℚ} (rows : List CRow) (hch : chainShape rows = true) :
    ∀ n, 1 ≤ n → n ≤ rows.length → psum p c rows (n - 1) = loSum p c rows n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro _ hn
    simp only [chainShape, List.all_eq_true, List.mem_range] at hch
    have h := hch n (by omega)
    rw [Nat.add_sub_cancel, psum]
    simp only [loSum, List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    by_cases hn0 : n = 0
    · subst hn0
      simp only [if_true, beq_iff_eq] at h
      simp [h]
    · simp only [hn0, if_false, Bool.and_eq_true, beq_iff_eq] at h
      have hy : ((rows.getD n default).lab (pathPin (rows.getD n default))).kind = 2 ∧
          ((rows.getD n default).lab (pathPin (rows.getD n default))).k < n := ⟨h.1, by omega⟩
      rw [dif_pos hy, h.2, ih (by omega) (by omega)]
      simp only [loSum]; omega

theorem sum_nonneg' : ∀ l : List ℤ, (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum
  | [], _ => le_refl _
  | x :: l, h => by
    simp only [List.sum_cons]
    have := sum_nonneg' l fun y hy => h y (List.mem_cons_of_mem _ hy)
    have := h x List.mem_cons_self
    omega

theorem toNat_sum_le (f : Nat → List Arc) (g : Arc → ℤ) (hg : ∀ e, 0 ≤ g e) :
    ∀ n, (((List.range n).map f).flatten.map g).sum.toNat ≤ ((List.range n).map fun i => ((f i).map g).sum.toNat).sum
  | 0 => by simp
  | n + 1 => by
    have ih := toNat_sum_le f g hg n
    simp only [List.range_succ, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    have h1 : 0 ≤ (((List.range n).map f).flatten.map g).sum := sum_nonneg' _ (fun y hy => by obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy; exact hg a)
    have h2 : 0 ≤ ((f n).map g).sum := sum_nonneg' _ (fun y hy => by obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy; exact hg a)
    omega

theorem lo_nonneg {κ c : ℚ} (hk1 : κ ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (e : Arc) :
    0 ≤ Formal.Cells.Ua1Static.lo 1 κ c e := by
  unfold Formal.Cells.Ua1Static.lo
  have h0 : (0 : ℚ) ≤ (1 - κ) * lerp e.fmin e.smin c / 1 := by
    unfold lerp
    have : (0 : ℚ) ≤ 1 - c := by linarith
    have : (0 : ℚ) ≤ 1 - κ := by linarith
    positivity
  have hc := Rat.le_ceil (x := (1 - κ) * lerp e.fmin e.smin c / 1)
  have : (0 : ℚ) ≤ (((1 - κ) * lerp e.fmin e.smin c / 1).ceil : ℚ) := h0.trans hc
  exact_mod_cast this

/-- **The race obligation from a chain certificate** (every behaviour, g = 1, κ ≤ 83/200, at the corner `c` of the
collapsed relations `G`). With the certificate's premises (the cause = the storage node showing its old value on
`[a, e]`, static nodes, memory rows), the acknowledge source (the last row's node) shows its old value at every
`u` from the last row's window start with `u + lo(ack pin) ≤ e + hi(feedback pin)`: every read of the node's
acknowledge pin within the node's feedback-loop upper delay after its flip sees the old value. -/
theorem race_holds {κ : ℚ} (hk0 : 0 ≤ κ) (hk : κ ≤ 83 / 200) {x : Beh}
    (hb : Behaves ⟨1, κ⟩ (circuit net boundary) x) (P : Prem) (rows : List CRow) (node : KRow) (ja jf : Nat)
    (hok : certOK P rows = true) (hsp : singlePath rows = true) (hch : chainShape rows = true)
    (hn : 1 ≤ rows.length)
    (h1 : 283 * sFmax (node.arcs jf) ≤ 117 * sFmin (pathArcs rows ++ node.arcs ja))
    (h2 : 283 * sSmax (node.arcs jf) ≤ 117 * sSmin (pathArcs rows ++ node.arcs ja))
    {c : ℚ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (G : ∀ i, i < rows.length → CGateOK ⟨1, κ⟩ c (rows.getD i default).r.g (rows.getD i default).r.src
      (rows.getD i default).r.arcs ((rows.getD i default).r.S ⟨1, κ⟩) x)
    (a e : Nat) (E : Nat → Nat) (PS : Nat)
    (hcause : ∀ t, a ≤ t → t ≤ e → x P.cn t = P.cv)
    (hstat : ∀ k, k < P.sn.length → ∀ t, a ≤ t → t ≤ E k → x (P.sn.getD k 0) t = P.sv.getD k false)
    (hmem : ∀ i, i < rows.length → (rows.getD i default).r.mem = true →
      1 ≤ (rows.getD i default).r.lo ⟨1, κ⟩ c (rows.getD i default).r.fb ∧
      ∀ t, (win ⟨1, κ⟩ c a e E rows i).1 ≤ t + (rows.getD i default).r.hi ⟨1, κ⟩ c (rows.getD i default).r.fb →
        t < (win ⟨1, κ⟩ c a e E rows i).1 → x (rows.getD i default).r.q t = (rows.getD i default).r.w)
    (hPS : ∀ i, i < rows.length → psum ⟨1, κ⟩ c rows i ≤ PS) (hE : ∀ k, e + PS ≤ E k) (hB : e + PS ≤ BIG) :
    ∀ u, (win ⟨1, κ⟩ c a e E rows (rows.length - 1)).1 ≤ u →
      u + node.lo ⟨1, κ⟩ c ja ≤ e + node.hi ⟨1, κ⟩ c jf →
      x (rows.getD (rows.length - 1) default).r.q u = (rows.getD (rows.length - 1) default).r.w := by
  intro u hu1 hu2
  have hw := win_end_ge (p := ⟨1, κ⟩) (c := c) P rows hok hsp a e E PS hPS hE hB (rows.length - 1) (by omega)
  have hpc := psum_chain (p := ⟨1, κ⟩) (c := c) rows hch rows.length hn le_rfl
  have hm := margin_of_sums hk0 hk hc0 hc1 h1 h2
  have hsplit : (((pathArcs rows ++ node.arcs ja).map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat) ≤
      ((pathArcs rows).map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat +
        ((node.arcs ja).map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat := by
    rw [List.map_append, List.sum_append]
    have := sum_nonneg' ((pathArcs rows).map (Formal.Cells.Ua1Static.lo 1 κ c))
      (fun y hy => by obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy; exact lo_nonneg (by linarith) hc0 hc1 a)
    have := sum_nonneg' ((node.arcs ja).map (Formal.Cells.Ua1Static.lo 1 κ c))
      (fun y hy => by obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy; exact lo_nonneg (by linarith) hc0 hc1 a)
    omega
  have hpath := toNat_sum_le (fun i => (rows.getD i default).r.arcs (pathPin (rows.getD i default)))
    (Formal.Cells.Ua1Static.lo 1 κ c) (lo_nonneg (by linarith) hc0 hc1) rows.length
  have hm' : node.hi ⟨1, κ⟩ c jf ≤ ((pathArcs rows ++ node.arcs ja).map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat := by
    exact_mod_cast hm
  have hlo : ((pathArcs rows).map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat ≤ loSum ⟨1, κ⟩ c rows rows.length :=
    hpath
  have hja : ((node.arcs ja).map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat = node.lo ⟨1, κ⟩ c ja := rfl
  exact cert_sound hb P rows hok G a e E hcause hstat hmem (rows.length - 1) (by omega) u hu1 (by omega)

/-- A race row: a certificate, the storage node's row (its pins; the other fields unused), the node's acknowledge
pin `ja` and feedback pin `jf`. -/
structure RaceRow where
  pc : Prem × List CRow
  node : KRow
  ja : Nat
  jf : Nat

/-- The checks of a race row besides `certOK`: path shape, the node's wiring (its `ja` reads the last row's node, its
`jf` reads itself, it is the cause), and the two integer arc-sum facts. -/
def raceOK (r : RaceRow) : Bool :=
  singlePath r.pc.2 && chainShape r.pc.2 && decide (1 ≤ r.pc.2.length) &&
  Formal.Cells.ViewPS.viewOK r.node.q r.node.pins && r.node.q == r.pc.1.cn &&
  (r.node.pins.getD r.ja ([], 0)).2 == (r.pc.2.getD (r.pc.2.length - 1) default).r.q &&
  (r.node.pins.getD r.jf ([], 0)).2 == r.node.q &&
  decide (283 * sFmax (r.node.arcs r.jf) ≤ 117 * sFmin (pathArcs r.pc.2 ++ r.node.arcs r.ja)) &&
  decide (283 * sSmax (r.node.arcs r.jf) ≤ 117 * sSmin (pathArcs r.pc.2 ++ r.node.arcs r.ja))

/-- **A checked race row gives the race obligation** (`race_holds` with the row's facts). -/
theorem race_row {r : RaceRow} (hc : certOK r.pc.1 r.pc.2 = true) (hr : raceOK r = true) {κ : ℚ} (hk0 : 0 ≤ κ)
    (hk : κ ≤ 83 / 200) {x : Beh} (hb : Behaves ⟨1, κ⟩ (circuit net boundary) x) {c : ℚ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (G : ∀ i, i < r.pc.2.length → CGateOK ⟨1, κ⟩ c (r.pc.2.getD i default).r.g (r.pc.2.getD i default).r.src
      (r.pc.2.getD i default).r.arcs ((r.pc.2.getD i default).r.S ⟨1, κ⟩) x)
    (a e : Nat) (E : Nat → Nat) (PS : Nat)
    (hcause : ∀ t, a ≤ t → t ≤ e → x r.pc.1.cn t = r.pc.1.cv)
    (hstat : ∀ k, k < r.pc.1.sn.length → ∀ t, a ≤ t → t ≤ E k → x (r.pc.1.sn.getD k 0) t = r.pc.1.sv.getD k false)
    (hmem : ∀ i, i < r.pc.2.length → (r.pc.2.getD i default).r.mem = true →
      1 ≤ (r.pc.2.getD i default).r.lo ⟨1, κ⟩ c (r.pc.2.getD i default).r.fb ∧
      ∀ t, (win ⟨1, κ⟩ c a e E r.pc.2 i).1 ≤ t + (r.pc.2.getD i default).r.hi ⟨1, κ⟩ c (r.pc.2.getD i default).r.fb →
        t < (win ⟨1, κ⟩ c a e E r.pc.2 i).1 → x (r.pc.2.getD i default).r.q t = (r.pc.2.getD i default).r.w)
    (hPS : ∀ i, i < r.pc.2.length → psum ⟨1, κ⟩ c r.pc.2 i ≤ PS) (hE : ∀ k, e + PS ≤ E k) (hB : e + PS ≤ BIG) :
    (r.node.pins.getD r.ja ([], 0)).2 = (r.pc.2.getD (r.pc.2.length - 1) default).r.q ∧
    (r.node.pins.getD r.jf ([], 0)).2 = r.node.q ∧ r.node.q = r.pc.1.cn ∧
    ∀ u, (win ⟨1, κ⟩ c a e E r.pc.2 (r.pc.2.length - 1)).1 ≤ u →
      u + r.node.lo ⟨1, κ⟩ c r.ja ≤ e + r.node.hi ⟨1, κ⟩ c r.jf →
      x (r.pc.2.getD (r.pc.2.length - 1) default).r.q u = (r.pc.2.getD (r.pc.2.length - 1) default).r.w := by
  simp only [raceOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsp, hch⟩, hn⟩, -⟩, hq⟩, hja⟩, hjf⟩, h1⟩, h2⟩ := hr
  exact ⟨hja, hjf, hq, race_holds hk0 hk hb r.pc.1 r.pc.2 r.node r.ja r.jf hc hsp hch hn h1 h2 hc0 hc1 G a e E PS
    hcause hstat hmem hPS hE hB⟩

end Formal.Cells.CertRaceAll
