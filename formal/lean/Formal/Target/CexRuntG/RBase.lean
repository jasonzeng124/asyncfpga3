import Formal.Net.CexPS72.KBase
import Formal.Target.SpecRunt

/-!
# Witness behaviours under H_RUNT(w) along the guard axis: g = N/D, κ = 0, per-arc slow lists (shard A, 2026-11-07)

The finite check of `Formal.Target.CexRuntP.RBase` (see `CexRunt72.RBase` for the read maps and per-pin
conditions) for the delay parameters `pG N D = ⟨N/D, 0⟩` (guard g = N/D ≥ ... any N, D > 0; corner 0): a slow arc
(listed by code `8·out + pin`) reads at `⌊N·FAST_MAX/D⌋`, every other at `⌈D·FAST_MIN/N⌉` (raised to at least `w` on
LUT pins), the window being `Adm ⟨g, 0⟩ 0 = [FAST_MIN/g, FAST_MAX·g]`, i.e. `D·fmin ≤ N·d` and `D·d ≤ N·fmax`.

**Proved.** `gateOKRunt_of_gateWR`: `gateWR N D w enc chs sl g = true → GateOKRunt w (pG N D) 0 g (fun n => sigL (enc n))`
for `0 < N`, `0 < D`.
-/

namespace Formal.Target.CexRuntG
open Formal.Target Formal.Net.CexPS72

/-- The delay parameters: guard `N/D`, no scatter. -/
def pG (N D : Nat) : DelayPar := ⟨(N : ℚ) / D, 0⟩

/-- Per-arc base delay: slow end for listed arcs (code `8·out + pin`), fast end otherwise. -/
def dKG (N D : Nat) (sl : List Nat) (g : Gate) (i : Nat) : Nat :=
  if sl.contains (8 * g.out + i) then N * (g.arcs.getD i default).fmax / D
  else (D * (g.arcs.getD i default).fmin + N - 1) / N

/-- A lower bound of `Gate.start (pG N D) g`. -/
def startKG (N D : Nat) (g : Gate) : Nat := (g.arcs.map fun e => N * e.smax / D).foldr max 0

theorem div_le_ceilG (N D s : Nat) (hD : 0 < D) : N * s / D ≤ (Rat.ceil ((1 + 0) * (s : ℚ) * ((N : ℚ) / D))).toNat := by
  rw [rat_ceil_eq']
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  have h1 : ((N * s / D : Nat) : ℚ) ≤ (1 + 0) * (s : ℚ) * ((N : ℚ) / D) := by
    have : N * s / D * D ≤ N * s := Nat.div_mul_le_self _ _
    have h' : ((N * s / D : Nat) : ℚ) * D ≤ (N : ℚ) * (s : ℚ) := by exact_mod_cast this
    rw [show (1 + 0) * (s : ℚ) * ((N : ℚ) / D) = (N : ℚ) * s / D by ring, le_div_iff₀ hD']
    linarith
  have h3 : ((N * s / D : Nat) : ℤ) ≤ ⌈(1 + 0) * (s : ℚ) * ((N : ℚ) / D)⌉ := by
    have := Int.ceil_mono h1
    rwa [Int.ceil_natCast] at this
  omega

theorem startKG_le (N D : Nat) (hD : 0 < D) (g : Gate) : startKG N D g ≤ g.start (pG N D) := by
  unfold startKG Gate.start
  apply foldr_max_mono
  intro e _
  simp only [pG]
  exact div_le_ceilG N D e.smax hD

/-- Trees with chain-list leaves (a leaf stands for every index below it: sparse data). -/
inductive BTC
  | lf (v : List (Nat × Nat))
  | nd (l r : BTC)

def BTC.get : BTC → Nat → Nat → List (Nat × Nat)
  | .lf v, _, _ => v
  | .nd _ _, 0, _ => []
  | .nd l r, d + 1, i => if i < 2 ^ d then l.get d i else r.get d (i - 2 ^ d)

/-- Pin `i`'s base read delay: C's `dK`, raised to at least `w` on LUT pins. -/
def dR (N D w : Nat) (sl : List Nat) (g : Gate) (i : Nat) : Nat :=
  if lutGate g then max (dKG N D sl g i) w else dKG N D sl g i

/-- Jump read: inside a listed chain `[S, E)` read at `S - 1`, else at `r`. -/
def jr : List (Nat × Nat) → Nat → Nat
  | [], r => r
  | c :: ch, r => if c.1 ≤ r ∧ r < c.2 then c.1 - 1 else jr ch r

/-- The read map of pin `i` of `g`. -/
def rd (N D w : Nat) (chs : Nat → List (Nat × Nat)) (sl : List Nat) (g : Gate) (i t : Nat) : Nat :=
  if lutGate g then jr (chs (g.ins.getD i 0)) (t - dR N D w sl g i) else t - dR N D w sl g i

/-- Chains: each starts at ≥ 1, is nonempty, and ends strictly before every later chain starts. -/
def chSorted : List (Nat × Nat) → Bool
  | [] => true
  | c :: ch => decide (1 ≤ c.1) && decide (c.1 < c.2) && ch.all (fun c' => decide (c.2 < c'.1)) && chSorted ch

/-- The per-LUT-pin conditions (see the module doc). `d` = the pin's delay, `r0 = startKG N D g - d`, `hi25 = (25+P)·fmax`. -/
def pinOK (M w : Nat) (e : Option (Bool × List Nat)) (ch : List (Nat × Nat)) (d r0 hi25 : Nat) : Bool :=
  decide ((thrL e).Pairwise (· < ·)) && chSorted ch &&
    ch.all (fun c => (thrL e).contains c.1 && (thrL e).contains c.2) &&
    (thrL e).all (fun a => (thrL e).all fun b =>
      !(decide (a < b) && decide (b - a < w) && decide (r0 < b)) || ch.any fun c => decide (c.1 ≤ a) && decide (b ≤ c.2)) &&
    (thrL e).all (fun b => !(decide (b < w) && decide (r0 < b))) &&
    ch.all (fun c => !decide (r0 < c.2) ||
      (decide (w ≤ c.1) && (thrL e).all (fun p => !decide (p < c.1) || decide (p + w ≤ c.1)) &&
        decide (M * (d + c.2 - c.1) ≤ hi25)))

def bpsR (N D w : Nat) (enc : Nat → Option (Bool × List Nat)) (sl : List Nat) (g : Gate) : List Nat :=
  thrL (enc g.out) ++ (List.range g.k).flatMap fun i => (thrL (enc (g.ins.getD i 0))).map (· + dR N D w sl g i)

def eqAtR (N D w : Nat) (enc : Nat → Option (Bool × List Nat)) (chs : Nat → List (Nat × Nat)) (sl : List Nat)
    (g : Gate) (τ : Nat) : Bool :=
  sigL (enc g.out) τ == g.init.testBit (addr g.k fun i => sigL (enc (g.ins.getD i 0)) (rd N D w chs sl g i τ))

def arcsOKR (N D w : Nat) (sl : List Nat) (g : Gate) : Bool :=
  (List.range g.k).all fun i =>
    decide (D * (g.arcs.getD i default).fmin ≤ N * dR N D w sl g i) &&
      decide (D * dR N D w sl g i ≤ N * (g.arcs.getD i default).fmax) && decide (dR N D w sl g i ≤ startKG N D g)

/-- The finite check of one gate under H_RUNT(w). -/
def gateWR (N D w : Nat) (enc : Nat → Option (Bool × List Nat)) (chs : Nat → List (Nat × Nat)) (sl : List Nat)
    (g : Gate) : Bool :=
  arcsOKR N D w sl g &&
    (!lutGate g || (List.range g.k).all fun i =>
      pinOK D w (enc (g.ins.getD i 0)) (chs (g.ins.getD i 0)) (dR N D w sl g i) (startKG N D g - dR N D w sl g i)
        (N * (g.arcs.getD i default).fmax)) &&
    (startKG N D g :: bpsR N D w enc sl g).all fun τ => decide (τ < startKG N D g) || eqAtR N D w enc chs sl g τ

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
theorem noRunt_of_pinOK (M w : Nat) (hw : 1 ≤ w) (e : Option (Bool × List Nat)) (ch : List (Nat × Nat))
    (d r0 hi25 : Nat) (hp : pinOK M w e ch d r0 hi25 = true) (r : Nat) (hr : r0 ≤ r) :
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
theorem lag_of_pinOK (M w : Nat) (e : Option (Bool × List Nat)) (ch : List (Nat × Nat)) (d r0 hi25 : Nat)
    (hp : pinOK M w e ch d r0 hi25 = true) (t : Nat) (hdt : d ≤ t) (hr : r0 ≤ t - d) (hd : M * d ≤ hi25) :
    M * (t - jr ch (t - d)) ≤ hi25 := by
  simp only [pinOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at hp
  obtain ⟨_, hjump⟩ := hp
  rcases jr_cases ch (t - d) with ⟨h1, _⟩ | ⟨c, hc, h1, h2, h3⟩
  · rw [h1, show t - (t - d) = d by omega]; exact hd
  · rw [h3]
    rcases hjump c hc with h | ⟨_, h⟩
    · omega
    · exact le_trans (Nat.mul_le_mul_left M (by omega)) h

/-! ## Soundness of the per-gate check -/

theorem adm_of_int (N D : Nat) (hN : 0 < N) (hD : 0 < D) (e : Arc) (δ : Nat) (h1 : D * e.fmin ≤ N * δ)
    (h2 : D * δ ≤ N * e.fmax) : Adm (pG N D) 0 e δ := by
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  simp only [Adm, pG, lerp, sub_zero, one_mul, zero_mul, add_zero, mul_one]
  constructor
  · have : ((D * e.fmin : Nat) : ℚ) ≤ ((N * δ : Nat) : ℚ) := by exact_mod_cast h1
    push_cast at this
    rw [div_div_eq_mul_div, div_le_iff₀ hN']; linarith
  · have : ((D * δ : Nat) : ℚ) ≤ ((N * e.fmax : Nat) : ℚ) := by exact_mod_cast h2
    push_cast at this
    rw [mul_div_assoc', le_div_iff₀ hD']; linarith

theorem gateOKRunt_of_gateWR (N D : Nat) (hN0 : 0 < N) (hD0 : 0 < D) (w : Nat) (hw : 1 ≤ w) (enc : Nat → Option (Bool × List Nat))
    (chs : Nat → List (Nat × Nat)) (sl : List Nat) (g : Gate) (hc : gateWR N D w enc chs sl g = true) :
    GateOKRunt w (pG N D) 0 g (fun n => sigL (enc n)) := by
  simp only [gateWR, Bool.and_eq_true] at hc
  obtain ⟨⟨harc, hpin⟩, hc⟩ := hc
  have hA : ∀ i, i < g.k → D * (g.arcs.getD i default).fmin ≤ N * dR N D w sl g i ∧
      D * dR N D w sl g i ≤ N * (g.arcs.getD i default).fmax ∧ dR N D w sl g i ≤ startKG N D g := by
    intro i hi
    have := List.all_eq_true.mp harc i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hP : lutGate g = true → ∀ i, i < g.k →
      pinOK D w (enc (g.ins.getD i 0)) (chs (g.ins.getD i 0)) (dR N D w sl g i) (startKG N D g - dR N D w sl g i)
        (N * (g.arcs.getD i default).fmax) = true := by
    intro hl i hi
    simp only [hl, Bool.not_true, Bool.false_or] at hpin
    exact List.all_eq_true.mp hpin i (List.mem_range.mpr hi)
  refine ⟨fun i t => rd N D w chs sl g i t, fun i hi a b hab => ?_, fun t ht => ?_⟩
  · -- monotone read maps
    simp only [rd]
    split
    · rename_i hl
      have hs := hP hl i hi
      simp only [pinOK, Bool.and_eq_true] at hs
      exact jr_mono _ hs.1.1.1.1.2 _ _ (by omega)
    · omega
  have ht' : startKG N D g ≤ t := le_trans (startKG_le N D hD0 g) ht
  refine ⟨fun i hi => ⟨?_, ?_, fun hl => ?_⟩, ?_⟩
  · simp only [rd]; split
    · exact le_trans (jr_le _ _) (by omega)
    · omega
  · obtain ⟨h1, h2, h3⟩ := hA i hi
    simp only [rd]; split
    · rename_i hl
      have hlag := lag_of_pinOK D w _ _ _ _ _ (hP hl i hi) t (by omega) (by omega) h2
      have hle := jr_le (chs (g.ins.getD i 0)) (t - dR N D w sl g i)
      exact adm_of_int N D hN0 hD0 _ _ (le_trans h1 (Nat.mul_le_mul_left N (by omega))) hlag
    · rw [show t - (t - dR N D w sl g i) = dR N D w sl g i by omega]
      exact adm_of_int N D hN0 hD0 _ _ h1 h2
  · simp only [rd, hl, if_true]
    exact noRunt_of_pinOK D w hw _ _ _ _ _ (hP hl i hi) _ (by have := (hA i hi).2.2; omega)
  · -- the gate equation, from the last breakpoint
    obtain ⟨a, b, c, d⟩ := lastBp_spec (startKG N D g) t ht' (bpsR N D w enc sl g)
    set τ := lastBp (startKG N D g) t (bpsR N D w enc sl g)
    have hτ : eqAtR N D w enc chs sl g τ = true := by
      have hm : τ ∈ startKG N D g :: bpsR N D w enc sl g := by
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
    show sigL (enc g.out) t = g.init.testBit (addr g.k fun i => sigL (enc (g.ins.getD i 0)) (rd N D w chs sl g i t))
    rw [hout, hτ]
    congr 1
    apply Formal.Timing.SpecSettle.addr_congr
    intro i hi
    have hdi := (hA i hi).2.2
    -- no input transition θ with τ - d < θ ≤ t - d
    have hno : ∀ θ ∈ thrL (enc (g.ins.getD i 0)), (θ ≤ t - dR N D w sl g i ↔ θ ≤ τ - dR N D w sl g i) := by
      intro θ hθ
      have := d (θ + dR N D w sl g i) (by
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
      have hcg : ∀ c ∈ chs (g.ins.getD i 0), (c.1 ≤ τ - dR N D w sl g i ∧ τ - dR N D w sl g i < c.2) ↔
          (c.1 ≤ t - dR N D w sl g i ∧ t - dR N D w sl g i < c.2) := by
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

end Formal.Target.CexRuntG
