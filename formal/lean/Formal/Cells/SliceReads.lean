import Formal.Cells.CornerSlice

/-!
# Formal.Cells.SliceReads — the timed net's read hypotheses with constant pins folded and dead pins dropped
(shard B, 2026-11-10)

**Problem, plainly.** C's bridge (`TimedBridge.reads_of_cgate`) turns the collapsed view's `CGateOK` facts into the
read hypotheses (`rd`, `mono`, `geq`) of the timed model `TBehX`, but only for gates whose pin sources are all
distinct. On THE target many LUTs tie several pins to one constant node (VCC/GND), 57 read one live source on two
pins, and many pins are dead (the INIT ignores them). The certificate builders already treat constant pins as known
and dead pins as irrelevant, with no Lean justification ("constant pins have no emitted cover", "dead pins set to 0",
JOURNAL-C 2026-11-09 18:52). And the bridge works at one corner; a certificate should cover a slice of corners.

**Proved.** `reads_of_sel`: let each gate `v` of a timed net `N` come with a pin selection `keep` (the pins the net
keeps, in order) and a constant map `cst`, such that (`SelGate`)
* the net's pins are the kept pins' sources, distinct; the net's function is the INIT with the kept pins read from
  the list and every other pin filled from `cst` (`fill`);
* every non-kept pin either has a constant value `b = cst i` whose route is at most `H` long at the slice's slow end,
  or is DEAD: flipping it never changes the INIT's output (`Dead`; Boolean form `deadB` over the 2^k addresses,
  sound by `dead_of_deadB`);
* the net's bounds are the kept routes' sums at the slice ends (`lo` at `c1`, `hi` at `c2`).
Then for every behaviour whose corner `c ∈ [c1, c2]` and whose `CGateOK` facts hold, and in which each constant-pin
source shows its value `b` from `t0 - H` on, there are read times meeting `TBehX`'s `rd` (given `hi ≤ H`), `mono`
and `geq` on `N`.

**Not shown here:** any instance (THE target's net: generator + chunked checks, next); the other `TBehX` fields
(quiet start, environment rule, `lo ≥ 1`); that a constant node of THE target holds its value (its `CGateOK` with
k = 0 gives it after its start time).
-/

namespace Formal.Cells.SliceReads
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Net.OccNet
  Formal.Net.OccNet.Timed Formal.Net.OccNet.Bridge Formal.Cells.CornerSlice

/-- The full pin vector from the kept pins' values `l` and the constants. -/
def fill (keep : List Nat) (cst : Nat → Option Bool) (l : List Bool) (i : Nat) : Bool :=
  if i ∈ keep then l.getD (keep.idxOf i) false else (cst i).getD false

/-- Pin `i` of gate `g` is dead: flipping it never changes the output. -/
def Dead (g : Gate) (i : Nat) : Prop :=
  ∀ (w : Nat → Bool) (b : Bool), g.init.testBit (addr g.k w) = g.init.testBit (addr g.k fun j => if j = i then b else w j)

/-- Agreement outside a list of dead pins gives the same output. -/
theorem testBit_dead (g : Gate) : ∀ (D : List Nat), (∀ i ∈ D, Dead g i) → ∀ (w1 w2 : Nat → Bool),
    (∀ i, i < g.k → i ∉ D → w1 i = w2 i) → g.init.testBit (addr g.k w1) = g.init.testBit (addr g.k w2)
  | [], _, w1, w2, h => by rw [addr_congr g.k w1 w2 (fun i hi => h i hi (List.not_mem_nil))]
  | d :: D, hD, w1, w2, h => by
    rw [hD d (List.mem_cons_self ..) w1 (w2 d)]
    apply testBit_dead g D (fun i hi => hD i (List.mem_cons_of_mem _ hi))
    intro i hi hni
    by_cases hid : i = d
    · simp [hid]
    · simp only [hid, ite_false]
      exact h i hi (by simp [hid, hni])

/-- What a timed net must satisfy at one gate (behaviour-independent): the slice form with pin selection. -/
structure SelGate (p : DelayPar) (c1 c2 : ℚ) (H : Nat) (N : TNet Nat) (v : Nat) (g : Gate) (src : Nat → Nat)
    (arcs : Nat → List Arc) (keep : List Nat) (cst : Nat → Option Bool) : Prop where
  pins : N.pins v = keep.map src
  nodup : (keep.map src).Nodup
  out : g.out = v
  klt : ∀ i ∈ keep, i < g.k
  fn : ∀ l, N.F v l = g.init.testBit (addr g.k (fill keep cst l))
  ord : ∀ i, i < g.k → ∀ e ∈ arcs i, ArcOrd e
  lo : ∀ i ∈ keep, N.lo v (src i) ≤ sumLoC p c1 (arcs i)
  hi : ∀ i ∈ keep, sumHiC p c2 (arcs i) ≤ N.hi v (src i)
  rest : ∀ i, i < g.k → i ∉ keep → (cst i).isSome ∧ sumHiC p c2 (arcs i) ≤ H ∨ (cst i = none ∧ Dead g i)

theorem keep_nodup {keep : List Nat} {src : Nat → Nat} (h : (keep.map src).Nodup) : keep.Nodup :=
  List.Nodup.of_map src h

/-- The pin index of a kept source. -/
def pinOf (keep : List Nat) (src : Nat → Nat) (w : Nat) : Nat := keep.getD ((keep.map src).idxOf w) 0

theorem pinOf_src {keep : List Nat} {src : Nat → Nat} (h : (keep.map src).Nodup) {i : Nat} (hi : i ∈ keep) :
    pinOf keep src (src i) = i := by
  unfold pinOf
  have hm : src i ∈ keep.map src := List.mem_map.2 ⟨i, hi, rfl⟩
  have hlt : (keep.map src).idxOf (src i) < (keep.map src).length := List.idxOf_lt_length_iff.2 hm
  have hget := List.getElem_idxOf hlt
  have hlt' : (keep.map src).idxOf (src i) < keep.length := by simpa using hlt
  have hj : keep.idxOf i < keep.length := List.idxOf_lt_length_iff.2 hi
  have hgj := List.getElem_idxOf hj
  have hj' : keep.idxOf i < (keep.map src).length := by simpa using hj
  have heq : (keep.map src)[(keep.map src).idxOf (src i)] = (keep.map src)[keep.idxOf i] := by
    rw [hget, List.getElem_map, hgj]
  have hmj : (keep.map src).idxOf (src i) = keep.idxOf i := (h.getElem_inj_iff).1 heq
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt', Option.getD_some]
  simp only [hmj, hgj]

theorem fill_kept {keep : List Nat} {cst : Nat → Option Bool} (hk : keep.Nodup) (f : Nat → Bool) {i : Nat}
    (hi : i ∈ keep) : fill keep cst (keep.map f) i = f i := by
  unfold fill
  have hj : keep.idxOf i < keep.length := List.idxOf_lt_length_iff.2 hi
  have hj' : keep.idxOf i < (keep.map f).length := by simpa using hj
  rw [if_pos hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some, List.getElem_map,
    List.getElem_idxOf hj]

/-- **The read hypotheses of `TBehX` on a slice net with pin selection.** -/
theorem reads_of_sel {p : DelayPar} (hp : Sane p) {c1 c2 c : ℚ} (h1 : c1 ≤ c) (h2 : c ≤ c2)
    {N : TNet Nat} {x : Beh} {t0 H : Nat}
    (hF : ∀ v, N.gate v = true → ∃ (g : Gate) (src : Nat → Nat) (arcs : Nat → List Arc) (S : Nat)
      (keep : List Nat) (cst : Nat → Option Bool),
      SelGate p c1 c2 H N v g src arcs keep cst ∧ CGateOK p c g src arcs S x ∧ S ≤ t0 + 1 ∧
      (∀ i b, i < g.k → i ∉ keep → cst i = some b → ∀ s, t0 ≤ s + H → x (src i) s = b))
    (hH : ∀ v w, N.gate v = true → w ∈ N.pins v → N.hi v w ≤ H) :
    ∃ r : Nat → Nat → Nat → Nat,
      (∀ v w t, N.gate v = true → w ∈ N.pins v → t0 < t →
        N.lo v w ≤ t - r v w t ∧ t - r v w t ≤ N.hi v w ∧ r v w t ≤ t ∧ t0 ≤ r v w t + H) ∧
      (∀ v w t t', N.gate v = true → w ∈ N.pins v → t0 < t → t ≤ t' → r v w t ≤ r v w t') ∧
      (∀ v t, N.gate v = true → t0 < t → x v t = N.F v ((N.pins v).map fun w => x w (r v w t))) := by
  classical
  have hc : ∀ v, ∃ R : Nat → Nat → Nat, N.gate v = true →
      (∀ w t, w ∈ N.pins v → t0 < t →
        N.lo v w ≤ t - R w t ∧ t - R w t ≤ N.hi v w ∧ R w t ≤ t ∧ t0 ≤ R w t + H) ∧
      (∀ w t t', w ∈ N.pins v → t0 < t → t ≤ t' → R w t ≤ R w t') ∧
      (∀ t, t0 < t → x v t = N.F v ((N.pins v).map fun w => x w (R w t))) := by
    intro v
    by_cases hg : N.gate v = true
    · obtain ⟨g, src, arcs, S, keep, cst, hs, ⟨Fr, hmono, hok⟩, hS, hcst⟩ := hF v hg
      have hkn := keep_nodup hs.nodup
      have hmem : ∀ w, w ∈ N.pins v → ∃ i ∈ keep, src i = w := by
        intro w hw; rw [hs.pins] at hw; exact List.mem_map.1 hw
      refine ⟨fun w t => Fr (pinOf keep src w) t, fun _ => ⟨?_, ?_, ?_⟩⟩
      · intro w t hw ht
        obtain ⟨i, hi, rfl⟩ := hmem w hw
        simp only [pinOf_src hs.nodup hi]
        have hik := hs.klt i hi
        obtain ⟨hr, _⟩ := hok t (by omega)
        obtain ⟨r1, r2⟩ := hr i hik
        obtain ⟨b1, b2⟩ := sumAdm_corner _ _ r2
        have l1 := le_trans (hs.lo i hi) (sumLoC_mono hp h1 _ (hs.ord i hik))
        have l2 := le_trans (sumHiC_mono hp h2 _ (hs.ord i hik)) (hs.hi i hi)
        have := hH v (src i) hg (by rw [hs.pins]; exact List.mem_map.2 ⟨i, hi, rfl⟩)
        omega
      · intro w t t' hw ht htt
        obtain ⟨i, hi, rfl⟩ := hmem w hw
        simp only [pinOf_src hs.nodup hi]
        exact hmono i (hs.klt i hi) htt
      · intro t ht
        obtain ⟨hr, ho⟩ := hok t (by omega)
        rw [← hs.out, ho, hs.out, hs.fn, hs.pins, List.map_map]
        have hl : (keep.map ((fun w => x w (Fr (pinOf keep src w) t)) ∘ src)) =
            keep.map (fun i => x (src i) (Fr i t)) := by
          apply List.map_congr_left
          intro i hi
          simp [pinOf_src hs.nodup hi]
        rw [hl]
        -- the two pin vectors agree except on dead pins
        let D := (List.range g.k).filter fun i => decide (i ∉ keep) && (cst i).isNone
        apply testBit_dead g D
        · intro i hi
          simp only [D, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
            Option.isNone_iff_eq_none] at hi
          rcases hs.rest i hi.1 hi.2.1 with ⟨hsome, _⟩ | ⟨_, hd⟩
          · rw [hi.2.2] at hsome; exact absurd hsome (by simp)
          · exact hd
        · intro i hik hnD
          by_cases hki : i ∈ keep
          · rw [fill_kept hkn _ hki]
          · have hsome : (cst i).isSome := by
              by_contra hn
              apply hnD
              simp only [D, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨hik, hki, by simpa using hn⟩
            obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
            rcases hs.rest i hik hki with ⟨_, hH'⟩ | ⟨hn, _⟩
            · have r1 := (hr i hik).1
              obtain ⟨_, b2⟩ := sumAdm_corner _ _ (hr i hik).2
              have hm := sumHiC_mono hp h2 _ (hs.ord i hik)
              rw [hcst i b hik hki hb (Fr i t) (by omega)]
              simp [fill, hki, hb]
            · rw [hn] at hb; exact absurd hb (by simp)
    · exact ⟨fun _ _ => 0, fun h => absurd h hg⟩
  choose R hR using hc
  refine ⟨fun v w t => R v w t, ?_, ?_, ?_⟩
  · intro v w t hg hw ht; exact (hR v hg).1 w t hw ht
  · intro v w t t' hg hw ht htt; exact (hR v hg).2.1 w t t' hw ht htt
  · intro v t hg ht; exact (hR v hg).2.2 t ht

/-- A Boolean form of `Dead`: flipping pin `i` never changes the INIT bit, over all `2^k` addresses. -/
def deadB (g : Gate) (i : Nat) : Bool :=
  (List.range (2 ^ g.k)).all fun a => g.init.testBit a == g.init.testBit (a ^^^ 2 ^ i)

theorem addr_lt : ∀ (k : Nat) (w : Nat → Bool), addr k w < 2 ^ k
  | 0, _ => by simp [addr]
  | k + 1, w => by
    have := addr_lt k w
    simp only [addr, Nat.pow_succ]
    split <;> omega

theorem testBit_addr : ∀ (k : Nat) (w : Nat → Bool) (j : Nat), (addr k w).testBit j = (decide (j < k) && w j)
  | 0, w, j => by simp [addr]
  | k + 1, w, j => by
    have hl := addr_lt k w
    simp only [addr]
    by_cases hw : w k
    · simp only [hw, if_true]
      rw [Nat.add_comm]
      rcases Nat.lt_trichotomy j k with h | h | h
      · rw [Nat.testBit_two_pow_add_gt h, testBit_addr k w j]; simp [h, show j < k + 1 by omega]
      · subst h; rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hl]; simp [hw]
      · rw [Nat.testBit_lt_two_pow (by
            have : 2 ^ (k + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) h
            rw [Nat.pow_succ] at this; omega)]
        simp; omega
    · simp only [hw, if_false, Nat.add_zero, Bool.false_eq_true]
      rw [testBit_addr k w j]
      by_cases hj : j = k
      · subst hj; simp [hw]
      · by_cases h : j < k
        · simp [h, show j < k + 1 by omega]
        · simp [h, show ¬ j < k + 1 by omega]

/-- **`deadB` is sound.** -/
theorem dead_of_deadB {g : Gate} {i : Nat} (h : deadB g i = true) (hi : i < g.k) : Dead g i := by
  intro w b
  by_cases hb : w i = b
  · congr 1; apply addr_congr; intro j _; by_cases hj : j = i <;> simp [hj, hb]
  · have hx : addr g.k (fun j => if j = i then b else w j) = addr g.k w ^^^ 2 ^ i := by
      apply Nat.eq_of_testBit_eq; intro j
      rw [Nat.testBit_xor, testBit_addr, testBit_addr, Nat.testBit_two_pow]
      by_cases hj : j = i
      · subst hj; cases hw : w j <;> cases b <;> simp_all
      · simp [hj, Ne.symm hj]
    rw [hx]
    unfold deadB at h
    have := List.all_eq_true.1 h (addr g.k w) (List.mem_range.2 (addr_lt g.k w))
    simpa using this

end Formal.Cells.SliceReads
