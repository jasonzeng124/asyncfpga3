import Formal.Net.CexRg16.KBase
import Formal.Target.SpecRunt

/-!
# Witness behaviours under H_RUNT(w): a finite check for `SpecRunt.GateOKRunt` (shard A, 2026-11-07;
# shard C copy at g = 8/5, κ = 0 with per-arc slow lists, for the C3 counterexample)

**Problem.** Shard C's refutations of THE statement (`CexPS`, `CexPS72`) use transport reads, and their runs read
1 ps pulses on LUT pins, so they say nothing about the owner's headline statement `NetCorrectSeqRunt 20`
(H_RUNT(20 ps): a LUT input pin never reads inside a pulse narrower than 20 ps). A run that obeys H_RUNT must
show, for every LUT pin, a read map that skips such pulses while staying inside the pin's delay window.

**The read maps.** A non-LUT pin `i` of gate `g` reads at `t - dR g i` (transport). A LUT pin reads at
`jr ch (t - dR g i)`: if `t - dR` lies in one of the listed *chains* `[S, E)` of its input node (maximal runs of
narrow pulses, data), it reads at `S - 1` instead, i.e. it keeps the value from before the chain. `dR` is C's
`dK` (slow end for the listed slow arcs `8·out + pin`, fast end otherwise, at g = 8/5, κ = 0) raised to at least `w` on LUT pins.

**Proved.** `gateOKRunt_of_gateWR`: if `gateWR w enc chs sl g = true`, then
`SpecRunt.GateOKRunt w pK 0 g (fun n => sigL (enc n))`. The finite check `gateWR` asks: every delay inside
`Adm pK 0` (as integers) and below the check's start; the gate equation at its start and at every breakpoint
(output transitions; every input transition shifted by that pin's delay); and for every LUT pin, with
`r0 = startK g - d` (the earliest read position that matters): the input's transition list is strictly increasing;
the chains are ordered and disjoint (`chSorted`) with both ends at transitions; every pair of transitions closer
than `w` that ends after `r0` lies inside one chain; no transition below `w` ends after `r0` (the power-up interval);
and every chain ending after `r0` starts at least `w` after the previous transition (so its jump target `S - 1` is
in no narrow pulse) and keeps the read lag `d + E - S` inside the window.

**Not shown here.** That any particular run passes (data, per chunk), nor the environment clauses.
-/

namespace Formal.Net.CexRg16
open Formal.Target

/-- Trees with chain-list leaves (a leaf stands for every index below it: sparse data). -/
inductive BTC
  | lf (v : List (Nat × Nat))
  | nd (l r : BTC)

def BTC.get : BTC → Nat → Nat → List (Nat × Nat)
  | .lf v, _, _ => v
  | .nd _ _, 0, _ => []
  | .nd l r, d + 1, i => if i < 2 ^ d then l.get d i else r.get d (i - 2 ^ d)

/-- Pin `i`'s base read delay: C's `dK`, raised to at least `w` on LUT pins. -/
def dR (w : Nat) (sl : List Nat) (g : Gate) (i : Nat) : Nat :=
  if lutGate g then max (dK sl g i) w else dK sl g i

/-- Jump read: inside a listed chain `[S, E)` read at `S - 1`, else at `r`. -/
def jr : List (Nat × Nat) → Nat → Nat
  | [], r => r
  | c :: ch, r => if c.1 ≤ r ∧ r < c.2 then c.1 - 1 else jr ch r

/-- The read map of pin `i` of `g`. -/
def rd (w : Nat) (chs : Nat → List (Nat × Nat)) (sl : List Nat) (g : Gate) (i t : Nat) : Nat :=
  if lutGate g then jr (chs (g.ins.getD i 0)) (t - dR w sl g i) else t - dR w sl g i

/-- Chains: each starts at ≥ 1, is nonempty, and ends strictly before every later chain starts. -/
def chSorted : List (Nat × Nat) → Bool
  | [] => true
  | c :: ch => decide (1 ≤ c.1) && decide (c.1 < c.2) && ch.all (fun c' => decide (c.2 < c'.1)) && chSorted ch

/-- The per-LUT-pin conditions (see the module doc). `d` = the pin's delay, `r0 = startK g - d`, `hi25 = 40·fmax` (25·lag ≤ 40·fmax is lag ≤ g·fmax). -/
def pinOK (w : Nat) (e : Option (Bool × List Nat)) (ch : List (Nat × Nat)) (d r0 hi25 : Nat) : Bool :=
  decide ((thrL e).Pairwise (· < ·)) && chSorted ch &&
    ch.all (fun c => (thrL e).contains c.1 && (thrL e).contains c.2) &&
    (thrL e).all (fun a => (thrL e).all fun b =>
      !(decide (a < b) && decide (b - a < w) && decide (r0 < b)) || ch.any fun c => decide (c.1 ≤ a) && decide (b ≤ c.2)) &&
    (thrL e).all (fun b => !(decide (b < w) && decide (r0 < b))) &&
    ch.all (fun c => !decide (r0 < c.2) ||
      (decide (w ≤ c.1) && (thrL e).all (fun p => !decide (p < c.1) || decide (p + w ≤ c.1)) &&
        decide (25 * (d + c.2 - c.1) ≤ hi25)))

def bpsR (w : Nat) (enc : Nat → Option (Bool × List Nat)) (sl : List Nat) (g : Gate) : List Nat :=
  thrL (enc g.out) ++ (List.range g.k).flatMap fun i => (thrL (enc (g.ins.getD i 0))).map (· + dR w sl g i)

def eqAtR (w : Nat) (enc : Nat → Option (Bool × List Nat)) (chs : Nat → List (Nat × Nat)) (sl : List Nat)
    (g : Gate) (τ : Nat) : Bool :=
  sigL (enc g.out) τ == g.init.testBit (addr g.k fun i => sigL (enc (g.ins.getD i 0)) (rd w chs sl g i τ))

def arcsOKR (w : Nat) (sl : List Nat) (g : Gate) : Bool :=
  (List.range g.k).all fun i =>
    decide (5 * (g.arcs.getD i default).fmin ≤ 8 * dR w sl g i) &&
      decide (25 * dR w sl g i ≤ 40 * (g.arcs.getD i default).fmax) && decide (dR w sl g i ≤ startK g)

/-- The finite check of one gate under H_RUNT(w). -/
def gateWR (w : Nat) (enc : Nat → Option (Bool × List Nat)) (chs : Nat → List (Nat × Nat)) (sl : List Nat)
    (g : Gate) : Bool :=
  arcsOKR w sl g &&
    (!lutGate g || (List.range g.k).all fun i =>
      pinOK w (enc (g.ins.getD i 0)) (chs (g.ins.getD i 0)) (dR w sl g i) (startK g - dR w sl g i)
        (40 * (g.arcs.getD i default).fmax)) &&
    (startK g :: bpsR w enc sl g).all fun τ => decide (τ < startK g) || eqAtR w enc chs sl g τ

/-! ## The jump read -/

theorem jr_le : ∀ (ch : List (Nat × Nat)) (r : Nat), jr ch r ≤ r
  | [], r => le_refl r
  | c :: ch, r => by
    simp only [jr]; split
    · omega
    · exact jr_le ch r

/-- `jr` either reads in place (no chain contains `r`) or jumps to `S - 1` for a chain `(S, E)` containing `r`. -/
theorem jr_cases : ∀ (ch : List (Nat × Nat)) (r : Nat),
    (jr ch r = r ∧ ∀ c ∈ ch, ¬ (c.1 ≤ r ∧ r < c.2)) ∨ (∃ c ∈ ch, c.1 ≤ r ∧ r < c.2 ∧ jr ch r = c.1 - 1)
  | [], r => Or.inl ⟨rfl, by simp⟩
  | c :: ch, r => by
    simp only [jr]; split
    · rename_i h; exact Or.inr ⟨c, List.mem_cons_self, h.1, h.2, rfl⟩
    · rename_i h
      rcases jr_cases ch r with ⟨h1, h2⟩ | ⟨c', hc', h1, h2, h3⟩
      · refine Or.inl ⟨h1, fun c'' hc'' => ?_⟩
        rcases List.mem_cons.mp hc'' with rfl | hm
        · exact h
        · exact h2 c'' hm
      · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', h1, h2, h3⟩

/-- `jr` depends only on which chains contain the position. -/
theorem jr_congr : ∀ (ch : List (Nat × Nat)) (r r' : Nat),
    (∀ c ∈ ch, (c.1 ≤ r ∧ r < c.2) ↔ (c.1 ≤ r' ∧ r' < c.2)) →
      (jr ch r = jr ch r' ∨ (jr ch r = r ∧ jr ch r' = r'))
  | [], r, r', _ => Or.inr ⟨rfl, rfl⟩
  | c :: ch, r, r', h => by
    have hc := h c List.mem_cons_self
    have ht := jr_congr ch r r' (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    simp only [jr]
    by_cases h1 : c.1 ≤ r ∧ r < c.2
    · rw [if_pos h1, if_pos (hc.mp h1)]; exact Or.inl rfl
    · have h2 : ¬ (c.1 ≤ r' ∧ r' < c.2) := fun h' => h1 (hc.mpr h')
      rw [if_neg h1, if_neg h2]; exact ht

/-- Every value of `jr ch r` is `r` or some chain start minus one, with that chain start `≤ r`. -/
theorem jr_ge (ch : List (Nat × Nat)) (r m : Nat) (hm : m ≤ r) (hc : ∀ c ∈ ch, m ≤ c.1 - 1) : m ≤ jr ch r := by
  rcases jr_cases ch r with ⟨h1, _⟩ | ⟨c, hc', _, _, h3⟩
  · rw [h1]; exact hm
  · rw [h3]; exact hc c hc'

theorem jr_mono : ∀ (ch : List (Nat × Nat)), chSorted ch = true → ∀ r r', r ≤ r' → jr ch r ≤ jr ch r'
  | [], _, r, r', h => h
  | c :: ch, hs, r, r', hrr => by
    simp only [chSorted, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hs
    simp only [jr]
    by_cases hr : c.1 ≤ r ∧ r < c.2
    · rw [if_pos hr]
      by_cases hr' : c.1 ≤ r' ∧ r' < c.2
      · rw [if_pos hr']
      · rw [if_neg hr']
        exact jr_ge ch r' _ (by omega) (fun c' hc' => by have := h3 c' hc'; omega)
    · rw [if_neg hr]
      by_cases hr' : c.1 ≤ r' ∧ r' < c.2
      · rw [if_pos hr']
        have : r < c.1 := by omega
        have := jr_le ch r
        omega
      · rw [if_neg hr']; exact jr_mono ch h4 r r' hrr

/-! ## Transitions of a coded signal -/

-- `countP_le_split`, `sigL_toggles`: copied from shard C's `CexPS72/Refute.lean` (which imports the whole run).
theorem countP_le_split (θ : Nat) (hθ : 1 ≤ θ) : ∀ ts : List Nat,
    ts.countP (fun x => decide (x ≤ θ)) = ts.countP (fun x => decide (x ≤ θ - 1)) + ts.count θ
  | [] => rfl
  | x :: ts => by
    rw [List.countP_cons, List.countP_cons, List.count_cons, countP_le_split θ hθ ts]
    by_cases h1 : x = θ
    · subst h1
      have : ¬ (x ≤ x - 1) := by omega
      simp [this]; omega
    · by_cases h2 : x ≤ θ - 1
      · have : x ≤ θ := by omega
        simp [h2, this, h1]; try omega
      · have : ¬ x ≤ θ := by omega
        simp [h2, this, h1]; try omega

theorem sigL_toggles (b : Bool) (ts : List Nat) (hs : ts.Pairwise (· < ·)) (θ : Nat) (hθ : θ ∈ ts) (h1 : 1 ≤ θ) :
    sigL (some (b, ts)) (θ - 1) ≠ sigL (some (b, ts)) θ := by
  simp only [sigL]
  rw [countP_le_split θ h1 ts]
  have hc : ts.count θ = 1 := List.Nodup.count_of_mem (hs.imp (fun h => Nat.ne_of_lt h)) hθ
  rw [hc]
  cases b <;> cases h : (ts.countP fun x => decide (x ≤ θ - 1)) % 2 == 1 <;> simp_all <;> omega


theorem sigL_no_toggle (b : Bool) (ts : List Nat) (x : Nat) (hx : 1 ≤ x) (hn : x ∉ ts) :
    sigL (some (b, ts)) (x - 1) = sigL (some (b, ts)) x := by
  simp only [sigL]
  rw [countP_le_split x hx ts, List.count_eq_zero.mpr hn, Nat.add_zero]

/-- A pulse of a coded signal with strictly increasing transitions: its end is a transition, its start is `0` or a
transition, and no transition lies strictly inside. -/
theorem pulse_shape (b : Bool) (ts : List Nat) (hs : ts.Pairwise (· < ·)) (a e : Nat)
    (hp : Pulse (sigL (some (b, ts))) a e) :
    e ∈ ts ∧ (a = 0 ∨ a ∈ ts) ∧ ∀ x ∈ ts, ¬ (a < x ∧ x < e) := by
  obtain ⟨hae, hc, hpre, hend⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  · by_contra hn
    have := sigL_no_toggle b ts e (by omega) hn
    rw [hc (e - 1) (by omega) (by omega)] at this
    exact hend this.symm
  · by_cases h0 : a = 0
    · exact Or.inl h0
    · right; by_contra hn
      exact hpre (by omega) (sigL_no_toggle b ts a (by omega) hn)
  · intro x hx ⟨h1, h2⟩
    have tog := sigL_toggles b ts hs x hx (by omega)
    rw [hc (x - 1) (by omega) (by omega), hc x (by omega) (by omega)] at tog
    exact tog rfl

/-! ## The per-pin conditions give H_RUNT and the delay window -/

theorem contains_mem {l : List Nat} {x : Nat} (h : l.contains x = true) : x ∈ l := by
  simpa using h

/-- The read of a LUT pin never lands in a pulse narrower than `w`, at positions `r ≥ r0`. -/
theorem noRunt_of_pinOK (w : Nat) (hw : 1 ≤ w) (e : Option (Bool × List Nat)) (ch : List (Nat × Nat))
    (d r0 hi25 : Nat) (hp : pinOK w e ch d r0 hi25 = true) (r : Nat) (hr : r0 ≤ r) :
    NoRuntRead w (sigL e) (jr ch r) := by
  intro a b hpl hab ⟨hu1, hu2⟩
  simp only [pinOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hp
  obtain ⟨⟨⟨⟨⟨hinc, _⟩, hends⟩, hcov⟩, hinit⟩, hjump⟩ := hp
  cases e with
  | none =>
    obtain ⟨_, _, _, hend⟩ := hpl
    exact hend rfl
  | some pr =>
    obtain ⟨b0, ts⟩ := pr
    simp only [thrL] at hinc hends hcov hinit hjump
    obtain ⟨hb, ha, hbet⟩ := pulse_shape b0 ts hinc a b hpl
    rcases jr_cases ch r with ⟨h1, h2⟩ | ⟨c, hc, h1, h2, h3⟩
    · rw [h1] at hu1 hu2
      rcases ha with ha | ha
      · rcases hinit b hb with h | h
        · omega
        · omega
      · rcases hcov a ha b hb with h | ⟨c, hc, hc1, hc2⟩
        · rcases h with (h | h) | h <;> omega
        · exact h2 c hc ⟨by omega, by omega⟩
    · rw [h3] at hu1 hu2
      rcases hjump c hc with h | ⟨⟨hwS, hprev⟩, _⟩
      · omega
      · have hS : c.1 ∈ ts := contains_mem (hends c hc).1
        have hSb : b ≤ c.1 := by
          by_contra hlt
          exact hbet c.1 hS ⟨by omega, by omega⟩
        rcases ha with ha | ha
        · omega
        · rcases hprev a ha with h | h <;> omega

/-- The read lag of a LUT pin stays inside the window: `t - jr ch (t - d) ≤ d + E - S` for the chain it jumps in. -/
theorem lag_of_pinOK (w : Nat) (e : Option (Bool × List Nat)) (ch : List (Nat × Nat)) (d r0 hi25 : Nat)
    (hp : pinOK w e ch d r0 hi25 = true) (t : Nat) (hdt : d ≤ t) (hr : r0 ≤ t - d) (hd : 25 * d ≤ hi25) :
    25 * (t - jr ch (t - d)) ≤ hi25 := by
  simp only [pinOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at hp
  obtain ⟨_, hjump⟩ := hp
  rcases jr_cases ch (t - d) with ⟨h1, _⟩ | ⟨c, hc, h1, h2, h3⟩
  · rw [h1]; omega
  · rw [h3]
    rcases hjump c hc with h | ⟨_, h⟩
    · omega
    · omega

/-! ## Soundness of the per-gate check -/

theorem adm_of_int (e : Arc) (δ : Nat) (h1 : 5 * e.fmin ≤ 8 * δ) (h2 : 25 * δ ≤ 40 * e.fmax) : Adm pK 0 e δ := by
  simp only [Adm, pK, lerp, sub_zero, one_mul, zero_mul, add_zero, mul_one]
  constructor
  · have : ((5 * e.fmin : Nat) : ℚ) ≤ ((8 * δ : Nat) : ℚ) := by exact_mod_cast h1
    push_cast at this
    rw [div_le_iff₀ (by norm_num)]; linarith
  · have : ((25 * δ : Nat) : ℚ) ≤ ((40 * e.fmax : Nat) : ℚ) := by exact_mod_cast h2
    push_cast at this; linarith

theorem gateOKRunt_of_gateWR (w : Nat) (hw : 1 ≤ w) (enc : Nat → Option (Bool × List Nat))
    (chs : Nat → List (Nat × Nat)) (sl : List Nat) (g : Gate) (hc : gateWR w enc chs sl g = true) :
    GateOKRunt w pK 0 g (fun n => sigL (enc n)) := by
  simp only [gateWR, Bool.and_eq_true] at hc
  obtain ⟨⟨harc, hpin⟩, hc⟩ := hc
  have hA : ∀ i, i < g.k → 5 * (g.arcs.getD i default).fmin ≤ 8 * dR w sl g i ∧
      25 * dR w sl g i ≤ 40 * (g.arcs.getD i default).fmax ∧ dR w sl g i ≤ startK g := by
    intro i hi
    have := List.all_eq_true.mp harc i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hP : lutGate g = true → ∀ i, i < g.k →
      pinOK w (enc (g.ins.getD i 0)) (chs (g.ins.getD i 0)) (dR w sl g i) (startK g - dR w sl g i)
        (40 * (g.arcs.getD i default).fmax) = true := by
    intro hl i hi
    simp only [hl, Bool.not_true, Bool.false_or] at hpin
    exact List.all_eq_true.mp hpin i (List.mem_range.mpr hi)
  refine ⟨fun i t => rd w chs sl g i t, fun i hi a b hab => ?_, fun t ht => ?_⟩
  · -- monotone read maps
    simp only [rd]
    split
    · rename_i hl
      have hs := hP hl i hi
      simp only [pinOK, Bool.and_eq_true] at hs
      exact jr_mono _ hs.1.1.1.1.2 _ _ (by omega)
    · omega
  have ht' : startK g ≤ t := le_trans (startK_le g) ht
  refine ⟨fun i hi => ⟨?_, ?_, fun hl => ?_⟩, ?_⟩
  · simp only [rd]; split
    · exact le_trans (jr_le _ _) (by omega)
    · omega
  · obtain ⟨h1, h2, h3⟩ := hA i hi
    simp only [rd]; split
    · rename_i hl
      have hlag := lag_of_pinOK w _ _ _ _ _ (hP hl i hi) t (by omega) (by omega) h2
      have hle := jr_le (chs (g.ins.getD i 0)) (t - dR w sl g i)
      exact adm_of_int _ _ (by omega) hlag
    · rw [show t - (t - dR w sl g i) = dR w sl g i by omega]
      exact adm_of_int _ _ h1 h2
  · simp only [rd, hl, if_true]
    exact noRunt_of_pinOK w hw _ _ _ _ _ (hP hl i hi) _ (by have := (hA i hi).2.2; omega)
  · -- the gate equation, from the last breakpoint
    obtain ⟨a, b, c, d⟩ := lastBp_spec (startK g) t ht' (bpsR w enc sl g)
    set τ := lastBp (startK g) t (bpsR w enc sl g)
    have hτ : eqAtR w enc chs sl g τ = true := by
      have hm : τ ∈ startK g :: bpsR w enc sl g := by
        rcases c with c | c
        · rw [c]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ c
      have := List.all_eq_true.mp hc τ hm
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with h | h
      · omega
      · exact h
    simp only [eqAtR, beq_iff_eq] at hτ
    have hout : sigL (enc g.out) t = sigL (enc g.out) τ := by
      apply sigL_eq; intro θ hθ
      exact d θ (by simp only [bpsR, List.mem_append]; exact Or.inl hθ)
    show sigL (enc g.out) t = g.init.testBit (addr g.k fun i => sigL (enc (g.ins.getD i 0)) (rd w chs sl g i t))
    rw [hout, hτ]
    congr 1
    apply Formal.Timing.SpecSettle.addr_congr
    intro i hi
    have hdi := (hA i hi).2.2
    -- no input transition θ with τ - d < θ ≤ t - d
    have hno : ∀ θ ∈ thrL (enc (g.ins.getD i 0)), (θ ≤ t - dR w sl g i ↔ θ ≤ τ - dR w sl g i) := by
      intro θ hθ
      have := d (θ + dR w sl g i) (by
        simp only [bpsR, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map]
        exact Or.inr ⟨i, hi, θ, hθ, rfl⟩)
      constructor
      · intro h; have := this.mp (by omega); omega
      · intro h; have := this.mpr (by omega); omega
    simp only [rd]
    split
    · rename_i hl
      have hs := hP hl i hi
      simp only [pinOK, Bool.and_eq_true, List.all_eq_true] at hs
      have hends := hs.1.1.1.2
      have hcg : ∀ c ∈ chs (g.ins.getD i 0), (c.1 ≤ τ - dR w sl g i ∧ τ - dR w sl g i < c.2) ↔
          (c.1 ≤ t - dR w sl g i ∧ t - dR w sl g i < c.2) := by
        intro c hc
        have he := hends c hc
        have h1 := hno c.1 (contains_mem he.1)
        have h2 := hno c.2 (contains_mem he.2)
        constructor
        · intro ⟨x, y⟩; exact ⟨h1.mpr x, by by_contra hh; exact absurd (h2.mp (by omega)) (by omega)⟩
        · intro ⟨x, y⟩; exact ⟨h1.mp x, by by_contra hh; exact absurd (h2.mpr (by omega)) (by omega)⟩
      rcases jr_congr _ _ _ hcg with h | ⟨h1, h2⟩
      · rw [h]
      · rw [h1, h2]; exact sigL_eq _ _ _ (fun θ hθ => (hno θ hθ).symm)
    · exact sigL_eq _ _ _ (fun θ hθ => (hno θ hθ).symm)

end Formal.Net.CexRg16
