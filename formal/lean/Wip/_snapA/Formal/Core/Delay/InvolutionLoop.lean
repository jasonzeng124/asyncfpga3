import Formal.Core.Delay.Involution
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The involution OR loop: pulse-width orbit, critical runt, unbounded resolution

Probe InvLoop (shard A).  The loop is shard B's OR storage loop
(`Formal.Cells.CElemInvolution`, `ArbInvolution.stF_runt`): a zero-time OR of a runt
`b = [0, s)` and the loop output `q`, followed by ONE involution channel `P`
(LUT + feedback wire lumped), whose output is `q`.  Its output transition times are
B's `orb P s`; the recurrence is copied here as `lo` (same equations, so
`lo P s = orb P s` is `rfl`; the bridge is not stated here because B's module needs
Mathlib's topology, which was not built when this file was written).

`lo s 0 = δ∞↑` (first rise of `q`), `lo s 1 = s + δ↓(s - δ∞↑)` (the fall caused by
the end of the runt), `lo s (n+2) = lo s n + δ_n(lo s n - lo s (n+1))` (the loop
input copies `q`; `δ_n = δ↑` for even `n`).  The run is cancellation-free up to `n`
while every width `wd s j = lo s (j+1) - lo s j`, `j < n`, is positive (B's `chainS`);
the first index `m` with `wd s m ≤ 0` is B's first cancellation, and B's `loop_orb`
says that then `q` is constant after `lo s (m-1)`: equal to 1 if `m` is odd
(LATCHED), 0 if `m` is even (LOST).

## Results (every hypothesis is a named field or argument)
* `wd_succ`: `wd (n+1) = δ_n(-wd n) - wd n`.  Each half-lap map `w ↦ δ(-w) - w` is
  strictly decreasing and EXPANDING: `fu_exp`, `fd_exp` (from strict monotonicity
  alone).  The lap map `F = fd ∘ fu` satisfies `F b - F a > b - a` (`F_exp`).
* `Stat h l`: a stationary pulse train, high `h`, low `l`, period `h + l`:
  `δ↑(-h) = h + l = δ↓(-l)`.  `stat_exists` (IVT, proved by `sSup`, no topology
  library) and `stat_unique`.
* `crit l = δ∞↑ - l` is the critical runt: `wd_crit` (the orbit IS the stationary
  train, forever).  `latch`: wider runts latch, with high widths growing by at least
  a fixed `c > 0` per lap (`latch_grow`); `lost`: narrower runts die, high widths
  shrinking by at least `c > 0` per lap (`lost_shrink`).  So the critical width is
  unique (`crit_unique`).
* `laps_unbounded_above/below`, `resolution_unbounded`: for every `N` (every time
  bound `B`) there are runts on either side of `s*`, as close as wanted, whose orbit
  makes more than `N` cancellation-free transitions (resolves after `B`).
* Symmetric channel (`Sym`): `sym_stat`: `h = l = w*` with `2 w* = δ(-w*)`;
  `sym_crit_gt_half`: `s* = δ∞ - w* > δ∞/2`; `sym_crit_lt`: `s* < δ∞ - δmin/2`;
  `exp_crit_lt` for A's exp-channel: `s* < τ ln 2 + T_p/2` (i.e. `δ∞ - T_p/2`).
* Asymmetric: `asym_up_le_down`: `δ↑ ≤ δ↓` on `(-δ↓(0), 0)` gives `h ≤ l`, hence
  `s* ≤ δ∞↑ - (h+l)/2`; `asym_down_le_up` the reverse.  `crit_bounds`:
  `δ∞↑ - (h+l) < s* < δ∞↑` and `h + l < min(δ↑(0), δ↓(0))` in general.
-/

namespace Formal.Core.InvolutionLoop
open Formal.Core.DelayInvolution

variable (P : InvolutionPair)

/-! ## 0. Parity helpers for A's `delayAt` / `infAt` -/

theorem delayAt_even {n : ℕ} (h : n % 2 = 0) : P.delayAt n = P.up := by
  unfold InvolutionPair.delayAt; rw [ite_eq_left h]
theorem delayAt_odd {n : ℕ} (h : n % 2 = 1) : P.delayAt n = P.down := by
  unfold InvolutionPair.delayAt; rw [ite_eq_right (by omega)]

/-! ## 1. The orbit and the width recurrence -/

/-- Output transition times of the OR loop for a runt `[0, s)` (B's `orb`). -/
noncomputable def lo (s : ℝ) : ℕ → ℝ
  | 0 => P.infUp
  | 1 => s + P.down (s - P.infUp)
  | n + 2 => lo s n + P.delayAt n (lo s n - lo s (n + 1))

theorem lo_ss (s : ℝ) (n : ℕ) :
    lo P s (n + 2) = lo P s n + P.delayAt n (lo P s n - lo P s (n + 1)) := rfl

/-- Width of the `n`-th pulse of `q` (high for even `n`, low for odd `n`). -/
noncomputable def wd (s : ℝ) (n : ℕ) : ℝ := lo P s (n + 1) - lo P s n

theorem wd_zero (s : ℝ) : wd P s 0 = (s - P.infUp) + P.down (s - P.infUp) := by
  unfold wd; show s + P.down (s - P.infUp) - P.infUp = _; ring

theorem wd_succ (s : ℝ) (n : ℕ) : wd P s (n + 1) = P.delayAt n (-wd P s n) - wd P s n := by
  unfold wd
  rw [show n + 1 + 1 = n + 2 from rfl, lo_ss, neg_sub]
  ring

/-- Half-lap maps: the low width following a high pulse of width `w`, and the high
width following a low gap of width `w`. -/
noncomputable def fu (w : ℝ) : ℝ := P.up (-w) - w
noncomputable def fd (w : ℝ) : ℝ := P.down (-w) - w
/-- One lap (high width to next high width). -/
noncomputable def F (w : ℝ) : ℝ := fd P (fu P w)

theorem wd_odd (s : ℝ) (k : ℕ) : wd P s (2 * k + 1) = fu P (wd P s (2 * k)) := by
  rw [wd_succ, delayAt_even P (by omega)]; rfl

theorem wd_even (s : ℝ) (k : ℕ) : wd P s (2 * k + 2) = fd P (wd P s (2 * k + 1)) := by
  rw [wd_succ, delayAt_odd P (by omega)]; rfl

theorem wd_lap (s : ℝ) (k : ℕ) : wd P s (2 * (k + 1)) = F P (wd P s (2 * k)) := by
  rw [show 2 * (k + 1) = 2 * k + 2 by ring, wd_even, wd_odd]; rfl

/-! ## 2. Expansion -/

/-- `fu` is strictly decreasing and expanding. -/
theorem fu_exp {a b : ℝ} (hab : a < b) (hb : b < P.infDown) : fu P b + (b - a) < fu P a := by
  have := P.up_strictMono (-b) (-a) (by linarith) (by linarith)
  unfold fu; linarith

theorem fd_exp {a b : ℝ} (hab : a < b) (hb : b < P.infUp) : fd P b + (b - a) < fd P a := by
  have := P.down_strictMono (-b) (-a) (by linarith) (by linarith)
  unfold fd; linarith

theorem fu_lt {a : ℝ} (h0 : 0 ≤ a) (ha : a < P.infDown) : fu P a < P.infUp := by
  have := P.up_lt (-a) (by linarith); unfold fu; linarith

theorem fd_lt {a : ℝ} (h0 : 0 ≤ a) (ha : a < P.infUp) : fd P a < P.infDown := by
  have := P.down_lt (-a) (by linarith); unfold fd; linarith

/-- The lap map is expanding: `F b - F a > b - a`. -/
theorem F_exp {a b : ℝ} (h0 : 0 ≤ a) (hab : a < b) (hb : b < P.infDown) :
    F P a + (b - a) < F P b := by
  have h1 := fu_exp P hab hb
  have h2 := fu_lt P h0 (by linarith)
  have h3 := fd_exp P (a := fu P b) (b := fu P a) (by linarith) h2
  unfold F; linarith

/-! ## 3. Stationary trains and the critical runt -/

/-- A stationary pulse train of the loop: high `h`, low `l`, period `h + l`. -/
structure Stat (h l : ℝ) : Prop where
  h_pos : 0 < h
  l_pos : 0 < l
  h_lt : h < P.infDown
  l_lt : l < P.infUp
  up_eq : P.up (-h) = h + l
  down_eq : P.down (-l) = h + l

variable {P}

theorem Stat.fu_h {h l : ℝ} (S : Stat P h l) : fu P h = l := by
  unfold fu; rw [S.up_eq]; ring
theorem Stat.fd_l {h l : ℝ} (S : Stat P h l) : fd P l = h := by
  unfold fd; rw [S.down_eq]; ring
theorem Stat.F_h {h l : ℝ} (S : Stat P h l) : F P h = h := by
  unfold F; rw [S.fu_h, S.fd_l]

/-- The stationary train is unique. -/
theorem stat_unique {h l h' l' : ℝ} (S : Stat P h l) (S' : Stat P h' l') : h = h' ∧ l = l' := by
  have hh : h = h' := by
    rcases lt_trichotomy h h' with c | c | c
    · have := F_exp P (le_of_lt S.h_pos) c S'.h_lt
      rw [S.F_h, S'.F_h] at this; linarith
    · exact c
    · have := F_exp P (le_of_lt S'.h_pos) c S.h_lt
      rw [S.F_h, S'.F_h] at this; linarith
  refine ⟨hh, ?_⟩
  rw [← S.fu_h, ← S'.fu_h, hh]

variable (P)

/-- The critical runt width belonging to a stationary train with low width `l`. -/
noncomputable def crit (l : ℝ) : ℝ := P.infUp - l

variable {P}

/-- At the critical runt the orbit IS the stationary train: forever high `h`, low `l`. -/
theorem wd_crit {h l : ℝ} (S : Stat P h l) :
    ∀ k : ℕ, wd P (crit P l) (2 * k) = h ∧ wd P (crit P l) (2 * k + 1) = l := by
  intro k
  induction k with
  | zero =>
    have e0 : wd P (crit P l) 0 = h := by
      rw [wd_zero]; unfold crit
      rw [show P.infUp - l - P.infUp = -l by ring, S.down_eq]; ring
    refine ⟨e0, ?_⟩
    rw [wd_odd, Nat.mul_zero, e0, S.fu_h]
  | succ k ih =>
    have e : wd P (crit P l) (2 * (k + 1)) = h := by rw [wd_lap, ih.1, S.F_h]
    refine ⟨e, ?_⟩
    rw [wd_odd, e, S.fu_h]

theorem wd_crit_pos {h l : ℝ} (S : Stat P h l) (n : ℕ) : 0 < wd P (crit P l) n := by
  obtain ⟨k, hk | hk⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
  · rw [hk, (wd_crit S k).1]; exact S.h_pos
  · rw [hk, (wd_crit S k).2]; exact S.l_pos

theorem crit_pos {h l : ℝ} (S : Stat P h l) : 0 < crit P l := by
  unfold crit; linarith [S.l_lt]

theorem crit_lt {h l : ℝ} (S : Stat P h l) : crit P l < P.infUp := by
  unfold crit; linarith [S.l_pos]

/-- The first high width is strictly increasing in the runt width, equal to `h` at `s*`. -/
theorem wd0_lt {a b : ℝ} (ha : 0 < a) (hab : a < b) : wd P a 0 < wd P b 0 := by
  rw [wd_zero, wd_zero]
  have := P.gapDown_strictMono (a := a - P.infUp) (b := b - P.infUp) (by linarith) (by linarith)
  unfold InvolutionPair.gapDown at this; exact this

theorem wd0_crit {h l : ℝ} (S : Stat P h l) : wd P (crit P l) 0 = h := (wd_crit S 0).1

theorem wd0_lt_infDown {s : ℝ} (h0 : 0 < s) (h1 : s < P.infUp) : wd P s 0 < P.infDown := by
  rw [wd_zero]; have := P.down_lt (s - P.infUp) (by linarith); linarith

/-! ## 4. First nonpositive width -/

theorem first_of_exists (p : ℕ → Prop) : ∀ n, (∃ j, j ≤ n ∧ p j) → ∃ j, p j ∧ ∀ i < j, ¬ p i := by
  intro n
  induction n with
  | zero =>
    rintro ⟨j, hj, hp⟩
    have : j = 0 := by omega
    subst this
    exact ⟨0, hp, fun i hi => absurd hi (by omega)⟩
  | succ n ih =>
    rintro ⟨j, hj, hp⟩
    by_cases h : ∃ j', j' ≤ n ∧ p j'
    · exact ih h
    · have hj' : j = n + 1 := by
        by_contra hne
        exact h ⟨j, by omega, hp⟩
      subst hj'
      refine ⟨n + 1, hp, fun i hi hpi => h ⟨i, by omega, hpi⟩⟩

variable (P) in
/-- `s` runs cancellation-free for its first `n` widths (B's `chainS`). -/
def Chain (s : ℝ) (n : ℕ) : Prop := ∀ j < n, 0 < wd P s j

/-! ## 5. Wider than critical: LATCH -/

section latch
variable {h l s : ℝ}

/-- Growth invariant above the critical runt. -/
theorem grow_inv (S : Stat P h l) (hx0 : h < wd P s 0) (hx0' : wd P s 0 < P.infDown) :
    ∀ k : ℕ, Chain P s (2 * k) →
      h < wd P s (2 * k) ∧
      wd P s 0 + k * (F P (wd P s 0) - wd P s 0) ≤ wd P s (2 * k) ∧
      wd P s (2 * k) < P.infDown := by
  intro k
  induction k with
  | zero => intro _; simp only [Nat.mul_zero, Nat.cast_zero, zero_mul, add_zero]; exact ⟨hx0, le_refl _, hx0'⟩
  | succ k ih =>
    intro hc
    obtain ⟨i1, i2, i3⟩ := ih (fun j hj => hc j (by omega))
    set x := wd P s (2 * k) with hx
    set x0 := wd P s 0 with hx0d
    have hy : 0 < wd P s (2 * k + 1) := hc _ (by omega)
    rw [wd_odd] at hy
    rw [wd_lap]
    have hxpos : 0 ≤ x := by linarith [S.h_pos]
    have g1 : F P h + (x - h) < F P x := F_exp P (le_of_lt S.h_pos) i1 i3
    rw [S.F_h] at g1
    have g2 : F P x0 - x0 ≤ F P x - x := by
      rcases eq_or_lt_of_le (show x0 ≤ x by
        have : 0 ≤ (k : ℝ) * (F P x0 - x0) := by
          have := F_exp P (le_of_lt S.h_pos) hx0 hx0'
          rw [S.F_h] at this
          exact mul_nonneg (Nat.cast_nonneg k) (by linarith)
        linarith) with e | e
      · rw [e]
      · have := F_exp P (by linarith [S.h_pos]) e i3; linarith
    have g3 : F P x < P.infDown := by
      unfold F
      exact fd_lt P (le_of_lt hy) (fu_lt P hxpos i3)
    refine ⟨by linarith, ?_, g3⟩
    push_cast
    linarith

/-- **Latch.** A runt wider than the critical one (and below `δ∞↑`) latches: the first
nonpositive width has an ODD index `2k+1` (a low gap cancels; `q` stays 1). -/
theorem latch (S : Stat P h l) (hs : crit P l < s) (hsI : s < P.infUp) :
    ∃ k : ℕ, Chain P s (2 * k + 1) ∧ wd P s (2 * k + 1) ≤ 0 := by
  have hs0 : 0 < s := lt_trans (crit_pos S) hs
  have hx0 : h < wd P s 0 := by rw [← wd0_crit S]; exact wd0_lt (crit_pos S) hs
  have hx0' := wd0_lt_infDown (P := P) hs0 hsI
  set c := F P (wd P s 0) - wd P s 0 with hc
  have hcpos : 0 < c := by
    have := F_exp P (le_of_lt S.h_pos) hx0 hx0'
    rw [S.F_h] at this; linarith
  obtain ⟨K, hK⟩ := exists_nat_gt ((P.infDown - wd P s 0) / c)
  have hnot : ¬ Chain P s (2 * K) := by
    intro hch
    have := (grow_inv S hx0 hx0' K hch).2
    have e : (P.infDown - wd P s 0) / c * c = P.infDown - wd P s 0 := by
      exact div_mul_cancel₀ _ (ne_of_gt hcpos)
    have : P.infDown - wd P s 0 < K * c := by
      have := mul_lt_mul_of_pos_right hK hcpos; linarith
    linarith [this, (grow_inv S hx0 hx0' K hch).2.1, (grow_inv S hx0 hx0' K hch).2.2]
  have hex : ∃ j, j ≤ 2 * K ∧ wd P s j ≤ 0 := by
    by_contra hno
    apply hnot
    intro j hj
    by_contra hp
    exact hno ⟨j, by omega, le_of_not_gt hp⟩
  obtain ⟨j, hj, hmin⟩ := first_of_exists (fun j => wd P s j ≤ 0) _ hex
  have hch : Chain P s j := fun i hi => lt_of_not_ge (hmin i hi)
  obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · subst hk
    have := (grow_inv S hx0 hx0' k hch).1
    linarith [S.h_pos]
  · subst hk
    exact ⟨k, hch, hj⟩

/-- Above the critical runt the high pulses grow by at least `c > 0` per lap and the
low gaps shrink, for as long as the run is cancellation-free. -/
theorem latch_grow (S : Stat P h l) (hs : crit P l < s) (hsI : s < P.infUp) :
    ∃ c > 0, ∀ k : ℕ, Chain P s (2 * k + 2) →
      wd P s (2 * k) + c ≤ wd P s (2 * (k + 1)) ∧ wd P s (2 * (k + 1) + 1) < wd P s (2 * k + 1) := by
  have hs0 : 0 < s := lt_trans (crit_pos S) hs
  have hx0 : h < wd P s 0 := by rw [← wd0_crit S]; exact wd0_lt (crit_pos S) hs
  have hx0' := wd0_lt_infDown (P := P) hs0 hsI
  refine ⟨F P (wd P s 0) - wd P s 0, ?_, ?_⟩
  · have := F_exp P (le_of_lt S.h_pos) hx0 hx0'
    rw [S.F_h] at this; linarith
  · intro k hc
    obtain ⟨i1, i2, i3⟩ := grow_inv S hx0 hx0' k (fun j hj => hc j (by omega))
    obtain ⟨j1, j2, j3⟩ := grow_inv S hx0 hx0' (k + 1) (fun j hj => hc j (by omega))
    have hmono : wd P s 0 ≤ wd P s (2 * k) := by
      have := F_exp P (le_of_lt S.h_pos) hx0 hx0'
      rw [S.F_h] at this
      have : 0 ≤ (k : ℝ) * (F P (wd P s 0) - wd P s 0) :=
        mul_nonneg (Nat.cast_nonneg k) (by linarith)
      linarith
    refine ⟨?_, ?_⟩
    · rw [wd_lap]
      rcases eq_or_lt_of_le hmono with e | e
      · rw [← e]; linarith
      · have := F_exp P (by linarith [S.h_pos]) e i3; linarith
    · rw [wd_odd, wd_odd]
      have hlt : wd P s (2 * k) < wd P s (2 * (k + 1)) := by
        rw [wd_lap]
        have := F_exp P (le_of_lt S.h_pos) i1 i3
        rw [S.F_h] at this; linarith
      have := fu_exp P hlt j3; linarith

end latch

/-! ## 6. Narrower than critical: LOST -/

section lost
variable {h l s : ℝ}

theorem shrink_inv (S : Stat P h l) (hx0 : wd P s 0 < h) (hx0p : 0 < wd P s 0) :
    ∀ k : ℕ, Chain P s (2 * k) →
      wd P s (2 * k) < h ∧
      wd P s (2 * k) ≤ wd P s 0 - k * (wd P s 0 - F P (wd P s 0)) := by
  intro k
  induction k with
  | zero => intro _; simp only [Nat.mul_zero, Nat.cast_zero, zero_mul, sub_zero]; exact ⟨hx0, le_refl _⟩
  | succ k ih =>
    intro hc
    obtain ⟨i1, i2⟩ := ih (fun j hj => hc j (by omega))
    set x := wd P s (2 * k) with hx
    set x0 := wd P s 0 with hx0d
    have hxpos : 0 < x := hc _ (by omega)
    rw [wd_lap]
    have g1 : F P x + (h - x) < F P h := F_exp P (le_of_lt hxpos) i1 S.h_lt
    rw [S.F_h] at g1
    have g2 : F P x - x ≤ F P x0 - x0 := by
      have hxx0 : x ≤ x0 := by
        have := F_exp P (le_of_lt hx0p) hx0 S.h_lt
        rw [S.F_h] at this
        have : 0 ≤ (k : ℝ) * (x0 - F P x0) := mul_nonneg (Nat.cast_nonneg k) (by linarith)
        linarith
      rcases eq_or_lt_of_le hxx0 with e | e
      · rw [e]
      · have := F_exp P (le_of_lt hxpos) e (by linarith [S.h_lt]); linarith
    refine ⟨by linarith, ?_⟩
    push_cast
    linarith

/-- **Lost.** A runt narrower than the critical one (`0 < s < s*`) dies: the first
nonpositive width has an EVEN index `2k` (a high pulse cancels; `q` returns to 0). -/
theorem lost (S : Stat P h l) (hs0 : 0 < s) (hs : s < crit P l) :
    ∃ k : ℕ, Chain P s (2 * k) ∧ wd P s (2 * k) ≤ 0 := by
  by_cases hp : wd P s 0 ≤ 0
  · exact ⟨0, fun j hj => absurd hj (by omega), hp⟩
  push Not at hp
  have hx0 : wd P s 0 < h := by rw [← wd0_crit S]; exact wd0_lt hs0 hs
  set c := wd P s 0 - F P (wd P s 0) with hc
  have hcpos : 0 < c := by
    have := F_exp P (le_of_lt hp) hx0 S.h_lt
    rw [S.F_h] at this; linarith
  obtain ⟨K, hK⟩ := exists_nat_gt (wd P s 0 / c)
  have hnot : ¬ Chain P s (2 * K + 1) := by
    intro hch
    have h1 := (shrink_inv S hx0 hp K (fun j hj => hch j (by omega))).2
    have h2 : 0 < wd P s (2 * K) := hch _ (by omega)
    have e : wd P s 0 / c * c = wd P s 0 := div_mul_cancel₀ _ (ne_of_gt hcpos)
    have : wd P s 0 < K * c := by
      have := mul_lt_mul_of_pos_right hK hcpos; linarith
    linarith
  have hex : ∃ j, j ≤ 2 * K + 1 ∧ wd P s j ≤ 0 := by
    by_contra hno
    apply hnot
    intro j hj
    by_contra hq
    exact hno ⟨j, by omega, le_of_not_gt hq⟩
  obtain ⟨j, hj, hmin⟩ := first_of_exists (fun j => wd P s j ≤ 0) _ hex
  have hch : Chain P s j := fun i hi => lt_of_not_ge (hmin i hi)
  obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · subst hk; exact ⟨k, hch, hj⟩
  · subst hk
    have i1 := (shrink_inv S hx0 hp k (fun i hi => hch i (by omega))).1
    have hxpos : 0 < wd P s (2 * k) := hch _ (by omega)
    have := fu_exp P i1 S.h_lt
    rw [S.fu_h, ← wd_odd] at this
    linarith [S.l_pos]

/-- Below the critical runt the high pulses shrink by at least `c > 0` per lap. -/
theorem lost_shrink (S : Stat P h l) (hs0 : 0 < s) (hs : s < crit P l) (hp : 0 < wd P s 0) :
    ∃ c > 0, ∀ k : ℕ, Chain P s (2 * k + 1) → wd P s (2 * (k + 1)) + c ≤ wd P s (2 * k) := by
  have hx0 : wd P s 0 < h := by rw [← wd0_crit S]; exact wd0_lt hs0 hs
  refine ⟨wd P s 0 - F P (wd P s 0), ?_, ?_⟩
  · have := F_exp P (le_of_lt hp) hx0 S.h_lt
    rw [S.F_h] at this; linarith
  · intro k hc
    obtain ⟨i1, i2⟩ := shrink_inv S hx0 hp k (fun j hj => hc j (by omega))
    have hxpos : 0 < wd P s (2 * k) := hc _ (by omega)
    have hle : wd P s (2 * k) ≤ wd P s 0 := by
      have := F_exp P (le_of_lt hp) hx0 S.h_lt
      rw [S.F_h] at this
      have : 0 ≤ (k : ℝ) * (wd P s 0 - F P (wd P s 0)) :=
        mul_nonneg (Nat.cast_nonneg k) (by linarith)
      linarith
    rw [wd_lap]
    rcases eq_or_lt_of_le hle with e | e
    · rw [e]; linarith
    · have := F_exp P (le_of_lt hxpos) e (by linarith [S.h_lt]); linarith

end lost

/-- The critical runt is the ONLY width in `(0, δ∞↑)` whose orbit never cancels. -/
theorem crit_unique {h l s : ℝ} (S : Stat P h l) (hs0 : 0 < s) (hsI : s < P.infUp)
    (hosc : ∀ n, 0 < wd P s n) : s = crit P l := by
  rcases lt_trichotomy s (crit P l) with c | c | c
  · obtain ⟨k, _, hk⟩ := lost S hs0 c; linarith [hosc (2 * k)]
  · exact c
  · obtain ⟨k, _, hk⟩ := latch S c hsI; linarith [hosc (2 * k + 1)]

/-! ## 7. Elementary continuity (from strict monotonicity and surjectivity only) -/

/-- A strictly increasing function on `(L, ∞)` that attains every value below `I` is
continuous there (stated in ε-η form). -/
theorem loc_cont {g : ℝ → ℝ} {L I : ℝ}
    (hmono : ∀ a b, L < a → a < b → g a < g b)
    (hlt : ∀ T, L < T → g T < I)
    (hsurj : ∀ v, v < I → ∃ T, L < T ∧ g T = v)
    {T0 : ℝ} (h0 : L < T0) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ T, |T - T0| < η → L < T ∧ |g T - g T0| < ε := by
  have hI := hlt T0 h0
  obtain ⟨T1, hT1, e1⟩ := hsurj (g T0 - ε) (by linarith)
  have hm1 : min ε ((I - g T0) / 2) ≤ ε := min_le_left _ _
  have hm2 : min ε ((I - g T0) / 2) ≤ (I - g T0) / 2 := min_le_right _ _
  have hmpos : 0 < min ε ((I - g T0) / 2) := lt_min hε (by linarith)
  obtain ⟨T2, hT2, e2⟩ := hsurj (g T0 + min ε ((I - g T0) / 2)) (by linarith)
  have l1 : T1 < T0 := by
    by_contra hc; push Not at hc
    rcases eq_or_lt_of_le hc with e | e
    · rw [e] at e1; linarith
    · have := hmono T0 T1 h0 e; linarith
  have l2 : T0 < T2 := by
    by_contra hc; push Not at hc
    rcases eq_or_lt_of_le hc with e | e
    · rw [← e] at e2; linarith
    · have := hmono T2 T0 hT2 e; linarith
  refine ⟨min (T0 - T1) (T2 - T0), lt_min (by linarith) (by linarith), fun T hT => ?_⟩
  have q1 : min (T0 - T1) (T2 - T0) ≤ T0 - T1 := min_le_left _ _
  have q2 : min (T0 - T1) (T2 - T0) ≤ T2 - T0 := min_le_right _ _
  obtain ⟨a1, a2⟩ := abs_lt.mp hT
  have b1 := hmono T1 T hT1 (by linarith)
  have b2 := hmono T T2 (by linarith) (by linarith)
  exact ⟨by linarith, abs_lt.mpr ⟨by linarith, by linarith⟩⟩

theorem up_loc {T0 : ℝ} (h0 : -P.infDown < T0) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ T, |T - T0| < η → -P.infDown < T ∧ |P.up T - P.up T0| < ε :=
  loc_cont P.up_strictMono P.up_lt
    (fun _ hv => ⟨_, (P.up_surj hv).1, (P.up_surj hv).2⟩) h0 hε

theorem down_loc {T0 : ℝ} (h0 : -P.infUp < T0) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ T, |T - T0| < η → -P.infUp < T ∧ |P.down T - P.down T0| < ε :=
  loc_cont P.down_strictMono P.down_lt
    (fun _ hv => ⟨_, (P.down_surj hv).1, (P.down_surj hv).2⟩) h0 hε

/-! ## 8. Near the critical runt: unboundedly many laps -/

section near
variable {h l : ℝ}

theorem dA_loc (S : Stat P h l) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ T, |T - (-wd P (crit P l) n)| < η →
      |P.delayAt n T - P.delayAt n (-wd P (crit P l) n)| < ε := by
  obtain ⟨k, hk | hk⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
  · subst hk
    rw [delayAt_even P (by omega), (wd_crit S k).1]
    obtain ⟨η, hη, hf⟩ := up_loc (P := P) (T0 := -h) (by linarith [S.h_lt]) hε
    exact ⟨η, hη, fun T hT => (hf T hT).2⟩
  · subst hk
    rw [delayAt_odd P (by omega), (wd_crit S k).2]
    obtain ⟨η, hη, hf⟩ := down_loc (P := P) (T0 := -l) (by linarith [S.l_lt]) hε
    exact ⟨η, hη, fun T hT => (hf T hT).2⟩

/-- Each width is a continuous function of the runt width at `s*`. -/
theorem wd_cont (S : Stat P h l) : ∀ n : ℕ, ∀ ε > 0, ∃ η > 0, ∀ s,
    |s - crit P l| < η → |wd P s n - wd P (crit P l) n| < ε := by
  intro n
  induction n with
  | zero =>
    intro ε hε
    obtain ⟨η1, hη1, hf⟩ := down_loc (P := P) (T0 := crit P l - P.infUp)
      (by linarith [crit_pos S]) (half_pos hε)
    refine ⟨min η1 (ε / 2), lt_min hη1 (half_pos hε), fun s hs => ?_⟩
    have m1 : min η1 (ε / 2) ≤ η1 := min_le_left _ _
    have m2 : min η1 (ε / 2) ≤ ε / 2 := min_le_right _ _
    obtain ⟨a1, a2⟩ := abs_lt.mp hs
    have := (hf (s - P.infUp) (abs_lt.mpr ⟨by linarith, by linarith⟩)).2
    obtain ⟨c1, c2⟩ := abs_lt.mp this
    rw [wd_zero, wd_zero]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  | succ n ih =>
    intro ε hε
    obtain ⟨η1, hη1, hf⟩ := dA_loc S n (half_pos hε)
    obtain ⟨η, hη, hg⟩ := ih (min η1 (ε / 2)) (lt_min hη1 (half_pos hε))
    refine ⟨η, hη, fun s hs => ?_⟩
    have m1 : min η1 (ε / 2) ≤ η1 := min_le_left _ _
    have m2 : min η1 (ε / 2) ≤ ε / 2 := min_le_right _ _
    obtain ⟨a1, a2⟩ := abs_lt.mp (hg s hs)
    have := hf (-wd P s n) (abs_lt.mpr ⟨by linarith, by linarith⟩)
    obtain ⟨c1, c2⟩ := abs_lt.mp this
    rw [wd_succ, wd_succ]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem wd_crit_ge (S : Stat P h l) (n : ℕ) : min h l ≤ wd P (crit P l) n := by
  obtain ⟨k, hk | hk⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
  · rw [hk, (wd_crit S k).1]; exact min_le_left _ _
  · rw [hk, (wd_crit S k).2]; exact min_le_right _ _

/-- Close enough to `s*`, the first `N + 1` widths all exceed `min(h, l)/2`. -/
theorem near_chain (S : Stat P h l) (N : ℕ) : ∃ η > 0, ∀ s, |s - crit P l| < η →
    ∀ n ≤ N, min h l / 2 < wd P s n := by
  have hm : 0 < min h l := lt_min S.h_pos S.l_pos
  induction N with
  | zero =>
    obtain ⟨η, hη, hf⟩ := wd_cont S 0 (min h l / 2) (half_pos hm)
    refine ⟨η, hη, fun s hs n hn => ?_⟩
    have : n = 0 := by omega
    subst this
    obtain ⟨a1, _⟩ := abs_lt.mp (hf s hs)
    linarith [wd_crit_ge S 0]
  | succ N ih =>
    obtain ⟨η0, hη0, h0⟩ := ih
    obtain ⟨η1, hη1, h1⟩ := wd_cont S (N + 1) (min h l / 2) (half_pos hm)
    refine ⟨min η0 η1, lt_min hη0 hη1, fun s hs n hn => ?_⟩
    have m0 : min η0 η1 ≤ η0 := min_le_left _ _
    have m1 : min η0 η1 ≤ η1 := min_le_right _ _
    obtain ⟨b1, b2⟩ := abs_lt.mp hs
    rcases Nat.lt_or_ge n (N + 1) with c | c
    · exact h0 s (abs_lt.mpr ⟨by linarith, by linarith⟩) n (by omega)
    · have : n = N + 1 := by omega
      subst this
      obtain ⟨a1, _⟩ := abs_lt.mp (h1 s (abs_lt.mpr ⟨by linarith, by linarith⟩))
      linarith [wd_crit_ge S (N + 1)]

/-- **Unboundedly many laps, from above.** For every `N` and every `ε > 0` there is a
runt in `(s*, s* + ε)` whose orbit runs cancellation-free for more than `N` widths
and then LATCHES (first cancellation at an odd index `2k+1 > N`). -/
theorem laps_unbounded_above (S : Stat P h l) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ s, crit P l < s ∧ s < crit P l + ε ∧ s < P.infUp ∧ Chain P s (N + 1) ∧
      ∃ k, N < 2 * k + 1 ∧ Chain P s (2 * k + 1) ∧ wd P s (2 * k + 1) ≤ 0 := by
  obtain ⟨η, hη, hf⟩ := near_chain S N
  have hm : 0 < min h l := lt_min S.h_pos S.l_pos
  have hgap : 0 < P.infUp - crit P l := by linarith [crit_lt S]
  set r := min η (min ε (P.infUp - crit P l)) with hr
  have r1 : r ≤ η := min_le_left _ _
  have r2 : r ≤ ε := le_trans (min_le_right _ _) (min_le_left _ _)
  have r3 : r ≤ P.infUp - crit P l := le_trans (min_le_right _ _) (min_le_right _ _)
  have rpos : 0 < r := lt_min hη (lt_min hε hgap)
  set s := crit P l + r / 2 with hs
  have hsI : s < P.infUp := by linarith
  have hch : Chain P s (N + 1) := fun j hj =>
    lt_trans (half_pos hm) (hf s (abs_lt.mpr ⟨by linarith, by linarith⟩) j (by omega))
  obtain ⟨k, hk1, hk2⟩ := latch S (show crit P l < s by linarith) hsI
  refine ⟨s, by linarith, by linarith, hsI, hch, k, ?_, hk1, hk2⟩
  by_contra hc
  have := hch (2 * k + 1) (by omega)
  linarith

/-- **Unboundedly many laps, from below.** For every `N` and `ε > 0` there is a runt in
`(s* - ε, s*)` whose orbit runs cancellation-free for more than `N` widths and then is
LOST (first cancellation at an even index `2k > N`). -/
theorem laps_unbounded_below (S : Stat P h l) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ s, crit P l - ε < s ∧ s < crit P l ∧ 0 < s ∧ Chain P s (N + 1) ∧
      ∃ k, N < 2 * k ∧ Chain P s (2 * k) ∧ wd P s (2 * k) ≤ 0 := by
  obtain ⟨η, hη, hf⟩ := near_chain S N
  have hm : 0 < min h l := lt_min S.h_pos S.l_pos
  have hgap : 0 < crit P l := crit_pos S
  set r := min η (min ε (crit P l)) with hr
  have r1 : r ≤ η := min_le_left _ _
  have r2 : r ≤ ε := le_trans (min_le_right _ _) (min_le_left _ _)
  have r3 : r ≤ crit P l := le_trans (min_le_right _ _) (min_le_right _ _)
  have rpos : 0 < r := lt_min hη (lt_min hε hgap)
  set s := crit P l - r / 2 with hs
  have hs0 : 0 < s := by linarith
  have hch : Chain P s (N + 1) := fun j hj =>
    lt_trans (half_pos hm) (hf s (abs_lt.mpr ⟨by linarith, by linarith⟩) j (by omega))
  obtain ⟨k, hk1, hk2⟩ := lost S hs0 (show s < crit P l by linarith)
  refine ⟨s, by linarith, by linarith, hs0, hch, k, ?_, hk1, hk2⟩
  by_contra hc
  have := hch (2 * k) (by omega)
  linarith

theorem lo_succ (s : ℝ) (n : ℕ) : lo P s (n + 1) = lo P s n + wd P s n := by
  unfold wd; ring

theorem lo_mono {s : ℝ} {n : ℕ} (hc : Chain P s n) : ∀ i ≤ n, lo P s i ≤ lo P s n := by
  induction n with
  | zero => intro i hi; have : i = 0 := by omega
            subst this; exact le_refl _
  | succ n ih =>
    intro i hi
    have hpos := hc n (by omega)
    rw [lo_succ]
    rcases Nat.lt_or_ge i (n + 1) with c | c
    · have := ih (fun j hj => hc j (by omega)) i (by omega); linarith
    · have : i = n + 1 := by omega
      subst this; rw [lo_succ]

theorem lo_lin {s m : ℝ} {N : ℕ} (hm : ∀ n < N, m ≤ wd P s n) :
    P.infUp + N * m ≤ lo P s N := by
  induction N with
  | zero => show P.infUp + ((0 : ℕ) : ℝ) * m ≤ P.infUp; simp
  | succ N ih =>
    have := ih (fun n hn => hm n (by omega))
    have h2 := hm N (by omega)
    rw [lo_succ]; push_cast; linarith

/-- **Unbounded resolution time (latching side).** For every time bound `B` there is a
runt in `(s*, δ∞↑)` that latches, and whose last transition of `q` (the final rise at
`lo s (2k)`, after which the low gap cancels) is later than `B`. -/
theorem resolution_unbounded (S : Stat P h l) (B : ℝ) :
    ∃ s, crit P l < s ∧ s < P.infUp ∧
      ∃ k, Chain P s (2 * k + 1) ∧ wd P s (2 * k + 1) ≤ 0 ∧ B < lo P s (2 * k) := by
  have hm : 0 < min h l := lt_min S.h_pos S.l_pos
  obtain ⟨N, hN⟩ := exists_nat_gt ((B - P.infUp) / (min h l / 2))
  obtain ⟨η, hη, hf⟩ := near_chain S N
  have hgap : 0 < P.infUp - crit P l := by linarith [crit_lt S]
  set r := min η (P.infUp - crit P l) with hr
  have r1 : r ≤ η := min_le_left _ _
  have r3 : r ≤ P.infUp - crit P l := min_le_right _ _
  have rpos : 0 < r := lt_min hη hgap
  set s := crit P l + r / 2 with hs
  have hsI : s < P.infUp := by linarith
  have hwide : ∀ n ≤ N, min h l / 2 < wd P s n :=
    hf s (abs_lt.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨k, hk1, hk2⟩ := latch S (show crit P l < s by linarith) hsI
  have hNk : N ≤ 2 * k := by
    by_contra hc
    have := hwide (2 * k + 1) (by omega)
    linarith
  have hlin := lo_lin (P := P) (s := s) (m := min h l / 2) (N := N)
    (fun n hn => le_of_lt (hwide n (by omega)))
  have hmono := lo_mono (P := P) (fun j hj => hk1 j (by omega)) N hNk
  have hB : B - P.infUp < N * (min h l / 2) := by
    have e : (B - P.infUp) / (min h l / 2) * (min h l / 2) = B - P.infUp :=
      div_mul_cancel₀ _ (ne_of_gt (half_pos hm))
    have := mul_lt_mul_of_pos_right hN (half_pos hm); linarith
  exact ⟨s, by linarith, hsI, k, hk1, hk2, by linarith⟩

end near

/-! ## 9. Existence of the stationary train (IVT via `sSup`) -/

/-- Intermediate value theorem for a function continuous (ε-η form) on `[a, b]`. -/
theorem ivt {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ∀ x, a ≤ x → x ≤ b → ∀ ε > 0, ∃ η > 0, ∀ y, |y - x| < η → |G y - G x| < ε)
    (ha : G a < 0) (hb : 0 < G b) : ∃ c, a < c ∧ c < b ∧ G c = 0 := by
  set S : Set ℝ := {x | a ≤ x ∧ x ≤ b ∧ G x < 0} with hS
  have hne : S.Nonempty := ⟨a, le_refl a, hab, ha⟩
  have hbdd : BddAbove S := ⟨b, fun x hx => hx.2.1⟩
  have hac : a ≤ sSup S := le_csSup hbdd ⟨le_refl a, hab, ha⟩
  have hcb : sSup S ≤ b := csSup_le hne (fun x hx => hx.2.1)
  have key : G (sSup S) = 0 := by
    rcases lt_trichotomy (G (sSup S)) 0 with c | c | c
    · exfalso
      have hcb' : sSup S < b := by
        rcases eq_or_lt_of_le hcb with e | e
        · rw [e] at c; linarith
        · exact e
      obtain ⟨η, hη, hf⟩ := hcont _ hac hcb (-G (sSup S)) (by linarith)
      have m1 : min η (b - sSup S) ≤ η := min_le_left _ _
      have m2 : min η (b - sSup S) ≤ b - sSup S := min_le_right _ _
      have mp : 0 < min η (b - sSup S) := lt_min hη (by linarith)
      set y := sSup S + min η (b - sSup S) / 2 with hy
      have hyc := hf y (abs_lt.mpr ⟨by linarith, by linarith⟩)
      obtain ⟨_, d2⟩ := abs_lt.mp hyc
      have hyS : y ∈ S := ⟨by linarith, by linarith, by linarith⟩
      have := le_csSup hbdd hyS
      linarith
    · exact c
    · exfalso
      obtain ⟨η, hη, hf⟩ := hcont _ hac hcb (G (sSup S)) c
      obtain ⟨x, hxS, hx⟩ := exists_lt_of_lt_csSup hne (show sSup S - η < sSup S by linarith)
      have hxle := le_csSup hbdd hxS
      have := hf x (abs_lt.mpr ⟨by linarith, by linarith⟩)
      obtain ⟨d1, _⟩ := abs_lt.mp this
      linarith [hxS.2.2]
  refine ⟨sSup S, ?_, ?_, key⟩
  · rcases eq_or_lt_of_le hac with e | e
    · rw [← e] at key; linarith
    · exact e
  · rcases eq_or_lt_of_le hcb with e | e
    · rw [e] at key; linarith
    · exact e

theorem F_loc {x : ℝ} (h0 : 0 ≤ x) (hx : x < P.infDown) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ y, |y - x| < η → |F P y - F P x| < ε := by
  have hfu := fu_lt P h0 hx
  obtain ⟨η2, hη2, hf2⟩ := down_loc (P := P) (T0 := -fu P x) (by linarith) (show 0 < ε / 3 by linarith)
  set ρ := min η2 (ε / 3) with hρ
  have ρ1 : ρ ≤ η2 := min_le_left _ _
  have ρ2 : ρ ≤ ε / 3 := min_le_right _ _
  have ρpos : 0 < ρ := lt_min hη2 (by linarith)
  obtain ⟨η1, hη1, hf1⟩ := up_loc (P := P) (T0 := -x) (by linarith) (half_pos ρpos)
  refine ⟨min η1 (ρ / 2), lt_min hη1 (half_pos ρpos), fun y hy => ?_⟩
  have m1 : min η1 (ρ / 2) ≤ η1 := min_le_left _ _
  have m2 : min η1 (ρ / 2) ≤ ρ / 2 := min_le_right _ _
  obtain ⟨a1, a2⟩ := abs_lt.mp hy
  obtain ⟨b1, b2⟩ := abs_lt.mp (hf1 (-y) (abs_lt.mpr ⟨by linarith, by linarith⟩)).2
  have efu : ∀ z, fu P z = P.up (-z) - z := fun _ => rfl
  have c := (hf2 (-fu P y) (abs_lt.mpr ⟨by rw [efu, efu]; linarith, by rw [efu, efu]; linarith⟩)).2
  obtain ⟨c1, c2⟩ := abs_lt.mp c
  have eF : ∀ z, F P z = P.down (-fu P z) - fu P z := fun _ => rfl
  rw [eF, eF]
  rw [efu y, efu x] at c1 c2 ⊢
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- **Existence of the stationary train** (every involution pair): there are `h, l`
with `δ↑(-h) = h + l = δ↓(-l)`, and `h < δ↓(0)`. -/
theorem stat_exists : ∃ h l, Stat P h l ∧ h < P.down 0 := by
  have hd0 := P.down_causal
  have hd0I : P.down 0 < P.infDown := P.down_lt 0 (by linarith [P.infUp_pos])
  have hcont : ∀ x, 0 ≤ x → x ≤ P.down 0 → ∀ ε > 0, ∃ η > 0, ∀ y, |y - x| < η →
      |(F P y - y) - (F P x - x)| < ε := by
    intro x h0 hx ε hε
    obtain ⟨η, hη, hf⟩ := F_loc (P := P) h0 (by linarith) (half_pos hε)
    refine ⟨min η (ε / 2), lt_min hη (half_pos hε), fun y hy => ?_⟩
    have m1 : min η (ε / 2) ≤ η := min_le_left _ _
    have m2 : min η (ε / 2) ≤ ε / 2 := min_le_right _ _
    obtain ⟨a1, a2⟩ := abs_lt.mp hy
    obtain ⟨b1, b2⟩ := abs_lt.mp (hf y (abs_lt.mpr ⟨by linarith, by linarith⟩))
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have G0 : F P 0 - 0 < 0 := by
    have e1 : fu P 0 = P.up 0 := by unfold fu; rw [neg_zero, sub_zero]
    have e2 : P.down (-P.up 0) = 0 := by
      have := P.down_neg_up (T := 0) (by linarith [P.infDown_pos]); rw [this, neg_zero]
    have : F P 0 = -P.up 0 := by unfold F fd; rw [e1, e2]; ring
    rw [this]; linarith [P.up_causal]
  have G1 : 0 < F P (P.down 0) - P.down 0 := by
    have e1 : fu P (P.down 0) = -P.down 0 := by
      unfold fu
      have := P.up_neg_down (T := 0) (by linarith [P.infUp_pos]); rw [this]; ring
    have : F P (P.down 0) = P.down (P.down 0) + P.down 0 := by
      unfold F fd; rw [e1, neg_neg]; ring
    rw [this]
    have := P.down_strictMono 0 (P.down 0) (by linarith [P.infUp_pos]) hd0
    linarith
  obtain ⟨c, hc0, hc1, hc⟩ := ivt (G := fun x => F P x - x) (le_of_lt hd0) hcont G0 G1
  have hFc : F P c = c := by simp only at hc; linarith
  have hlI := fu_lt P (le_of_lt hc0) (by linarith)
  have hl : 0 < fu P c := by
    by_contra hn; push Not at hn
    have e : F P c = P.down (-fu P c) - fu P c := rfl
    have : P.down 0 ≤ P.down (-fu P c) := by
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ -fu P c by linarith) with q | q
      · rw [← q]
      · exact le_of_lt (P.down_strictMono 0 _ (by linarith [P.infUp_pos]) q)
    linarith
  refine ⟨c, fu P c, ⟨hc0, hl, by linarith, hlI, ?_, ?_⟩, hc1⟩
  · unfold fu; ring
  · have e : F P c = P.down (-fu P c) - fu P c := rfl
    linarith

/-! ## 10. Symmetric channel: 50% duty, `s* = δ∞ - w*` -/

/-- Symmetric involution pair: `δ↑ = δ↓`. -/
structure Sym : Prop where
  up_eq_down : ∀ T, P.up T = P.down T
  inf_eq : P.infUp = P.infDown

section sym
variable {P} {h l w : ℝ}

theorem Sym.swap (Y : Sym P) (S : Stat P h l) : Stat P l h :=
  ⟨S.l_pos, S.h_pos, by rw [← Y.inf_eq]; exact S.l_lt, by rw [Y.inf_eq]; exact S.h_lt,
    by rw [Y.up_eq_down, S.down_eq]; ring, by rw [← Y.up_eq_down, S.up_eq]; ring⟩

/-- Under symmetry the stationary train has 50% duty: `h = l`. -/
theorem Sym.duty (Y : Sym P) (S : Stat P h l) : h = l := (stat_unique S (Y.swap S)).1

/-- **(1) Symmetric fixed point.** There is exactly one `w* > 0` with `δ(-w*) = 2 w*`;
the stationary train is high `w*`, low `w*`, period `δ(-w*) = 2 w*`, and the critical
runt is `s* = δ∞ - w*`. -/
theorem Sym.fixed (Y : Sym P) : ∃ w, 0 < w ∧ P.up (-w) = 2 * w ∧ Stat P w w ∧
    (∀ h' l', Stat P h' l' → h' = w ∧ l' = w) ∧ crit P w = P.infUp - w := by
  obtain ⟨h, l, S, _⟩ := stat_exists (P := P)
  have hl := Y.duty S
  subst hl
  refine ⟨h, S.h_pos, by rw [S.up_eq]; ring, S, fun h' l' S' => ?_, rfl⟩
  obtain ⟨a, b⟩ := stat_unique S' S
  exact ⟨a, b⟩

/-- **(1') Where `s*` sits (symmetric).** `s* - δ∞/2 = (δ∞ - δ(-w*))/2 > 0`: the critical
runt is strictly MORE than half the long-quiet loop delay, by half the loop delay the
pulse train itself loses (`δ∞ - δ(-w*)`), and `s* > δ∞ - δ(0)/2`. -/
theorem Sym.crit_gt_half (S : Stat P w w) :
    crit P w - P.infUp / 2 = (P.infUp - P.up (-w)) / 2 ∧ P.infUp / 2 < crit P w ∧
      P.infUp - P.up 0 / 2 < crit P w := by
  have h1 : P.up (-w) = 2 * w := by rw [S.up_eq]; ring
  have h2 := P.up_lt (-w) (by linarith [S.h_lt])
  have h3 := P.up_strictMono (-w) 0 (by linarith [S.h_lt]) (by linarith [S.h_pos])
  unfold crit
  refine ⟨by rw [h1]; ring, by linarith, by linarith⟩

/-- **(1'') Upper bound (symmetric).** With `δmin = d`: `d/2 < w* < d`, so
`δ∞ - d < s* < δ∞ - d/2`. -/
theorem Sym.crit_lt (S : Stat P w w) {d : ℝ} (hd : P.IsDMin d) :
    d / 2 < w ∧ w < d ∧ P.infUp - d < crit P w ∧ crit P w < P.infUp - d / 2 := by
  have h1 : P.up (-w) = 2 * w := by rw [S.up_eq]; ring
  have hwd : w < d := by
    by_contra hc; push Not at hc
    have : P.up (-w) ≤ P.up (-d) := by
      rcases eq_or_lt_of_le hc with e | e
      · rw [e]
      · exact le_of_lt (P.up_strictMono (-w) (-d) (by linarith [S.h_lt]) (by linarith))
    rw [hd.up_fix, h1] at this
    linarith [S.h_pos]
  have h2 := P.up_strictMono (-d) (-w) hd.mem_up (by linarith)
  rw [hd.up_fix, h1] at h2
  unfold crit
  exact ⟨by linarith, hwd, by linarith, by linarith⟩

end sym

/-- **Exp-channel corollary.** For A's exp-channel (`δ∞ = T_p + τ ln 2`, `δmin = T_p`)
the critical runt satisfies `δ∞/2 < s* < δ∞ - T_p/2 = τ ln 2 + T_p/2`. -/
theorem exp_crit (X : ExpLog) (Tp : ℝ) (hTp : 0 < Tp) :
    ∃ w, Stat (X.expPair Tp hTp) w w ∧
      X.expInf Tp / 2 < crit (X.expPair Tp hTp) w ∧
      crit (X.expPair Tp hTp) w < X.expInf Tp - Tp / 2 := by
  have Y : Sym (X.expPair Tp hTp) := ⟨fun _ => rfl, rfl⟩
  obtain ⟨w, _, _, S, _, _⟩ := Y.fixed
  exact ⟨w, S, (Sym.crit_gt_half S).2.1, (Sym.crit_lt S (X.exp_dmin Tp hTp)).2.2.2⟩

/-! ## 11. Asymmetric channel: where `s*` moves -/

section asym
variable {P} {h l : ℝ}

/-- General bounds: `s* = δ∞↑ - l` with `δ∞↑ - (h + l) < s* < δ∞↑`, and the train period
`h + l` is below both zero-gap delays. -/
theorem crit_bounds (S : Stat P h l) :
    P.infUp - (h + l) < crit P l ∧ crit P l < P.infUp ∧
      h + l < P.up 0 ∧ h + l < P.down 0 := by
  have h1 := P.up_strictMono (-h) 0 (by linarith [S.h_lt]) (by linarith [S.h_pos])
  have h2 := P.down_strictMono (-l) 0 (by linarith [S.l_lt]) (by linarith [S.l_pos])
  rw [S.up_eq] at h1; rw [S.down_eq] at h2
  unfold crit
  exact ⟨by linarith [S.h_pos], by linarith [S.l_pos], h1, h2⟩

/-- **(4a)** If rising is no slower than falling on `(-δ↓(0), 0)`, the train has at
least as much low time as high time, and `s* ≤ δ∞↑ - (h + l)/2`. -/
theorem asym_up_le_down (S : Stat P h l)
    (hle : ∀ T, -P.down 0 < T → T < 0 → P.up T ≤ P.down T) :
    h ≤ l ∧ crit P l ≤ P.infUp - (h + l) / 2 := by
  obtain ⟨_, _, hu, hd⟩ := crit_bounds S
  have hupI := P.up_lt (-h) (by linarith [S.h_lt])
  have e := hle (-h) (by linarith [S.l_pos]) (by linarith [S.h_pos])
  rw [S.up_eq] at e hupI
  have hhl : h ≤ l := by
    by_contra hc; push Not at hc
    have := P.down_strictMono (-h) (-l) (by linarith) (by linarith)
    rw [S.down_eq] at this
    linarith
  unfold crit
  exact ⟨hhl, by linarith⟩

/-- **(4b)** If falling is no slower than rising on `(-δ↑(0), 0)`, the train has at
least as much high time, and `s* ≥ δ∞↑ - (h + l)/2`. -/
theorem asym_down_le_up (S : Stat P h l)
    (hle : ∀ T, -P.up 0 < T → T < 0 → P.down T ≤ P.up T) :
    l ≤ h ∧ P.infUp - (h + l) / 2 ≤ crit P l := by
  obtain ⟨_, _, hu, hd⟩ := crit_bounds S
  have hdnI := P.down_lt (-l) (by linarith [S.l_lt])
  have e := hle (-l) (by linarith [S.h_pos]) (by linarith [S.l_pos])
  rw [S.down_eq] at e hdnI
  have hlh : l ≤ h := by
    by_contra hc; push Not at hc
    have := P.up_strictMono (-l) (-h) (by linarith) (by linarith)
    rw [S.up_eq] at this
    linarith
  unfold crit
  exact ⟨hlh, by linarith⟩

end asym

end Formal.Core.InvolutionLoop
