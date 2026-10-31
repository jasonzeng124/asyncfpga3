import Formal.Cells.CElemTiming
import Formal.Core.Delay.Involution
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Track 5, probe 5e: the `bd_c2` loop under shard A's involution channel

The cell is `bd_c2` (`cells/rtl/bd_ce.v`, INIT `0x00E800E800E800E8`, pins
`I0=a I1=b I2=q I3=rst`), evaluated through `Prelim.lutB` via
`CElemTiming.exc`. The gate model is the one of Fuegger, Najvirt, Nowak and
Schmid: a ZERO-TIME Boolean function (here: the real INIT through `lutB`)
followed by ONE involution channel (LUT and feedback wire lumped), whose
output is fed back to pin `I2`. The channel is shard A's
`Formal.Core.DelayInvolution.InvolutionPair` with A's transition semantics
`InvolutionPair.tent` (tentative output of input transition `n`; out-of-order
tentative outputs annihilate, `cancel_iff`).

Contents.
0. Facts about A's channel: the delay functions are CONTINUOUS on their
   domains (derived from A's fields: strictly monotone with an interval as
   image), and they can NOT be continuous on all of `ℝ` (`up_not_continuous`).
   So 5d's `InvCh` (global continuity and a global involution law) is not an
   abstraction of A's channel and 5d's `inv_eternal` cannot be applied by
   instantiation; it is re-proved here, tracking domains.
1. Orbit level: `orb` is exactly 5d's recurrence, now with A's delay
   functions. All arguments stay in the domains along a chain
   (`dom_chain`). Lost/latched sets are open, disjoint, cover the
   non-oscillating widths. `crit_exists`: there is a critical width `c`
   that oscillates forever, and LOST widths accumulate at `c` from below.
   `osc_unbounded`: on an oscillating orbit the transitions go to `∞`.
2. Signal level. `InvChanF P x y`: a signal-level relation built on A's
   `tent` (fragment: at most one cancellation, of the last two tentative
   transitions; see the notes). `CLoop`: the `bd_c2` loop with `a = 1`,
   `rst = 0`, `b` a runt `[0, Δ0)`, `x = lutB INIT (a,b,qp,rst)` (zero time),
   `InvChanF P x qp`.
   * `loop_orb` (DERIVATION): every solution's `qp` is the alternating signal
     whose transition times are `orb P Δ0`, either forever (`Osc`) or up to
     the first cancellation index `m` (`qp = den (orb) (· < m)`).
   * `loop_exists`: for every `Δ0 ∈ (0, δ∞↑)` there is a solution.
   * `c2_eternal`: some runt width makes every solution switch after every
     time bound.
   * `c2_slow_resolution`: arbitrarily close to that width there are widths
     whose every solution is LOST (eventually constant 0) but still switches
     after any given time `B`: resolution time is unbounded near the
     critical width.
3. Quantitative (`window_lower`): under a Lipschitz bound `K` and a margin
   `g` on the critical orbit (named hypotheses, `QuantHyp`), widths within
   `g / (2 (1+K) (1+2K)^N)` of it still switch at time `δ∞↑ + (N - 1/2) g`:
   the unresolved window shrinks at most like `e^{-T/τ}`, `τ = g / ln(1+2K)`.
   `sym_const_gap`: for a symmetric channel an orbit with constant gap `w`
   (`δ(-w) = 2w`) meets the margin hypotheses.
-/

namespace Formal.Cells.CElemInvolution
open Formal.Cells
open Formal.Cells.CElemTiming (exc INIT_c2 c2_eq)
open Formal.Core.DelayInvolution
open Filter Topology Set

abbrev Sig := ℝ → Bool

/-- With `a = 1`, `rst = 0`, `bd_c2`'s INIT computes `b ∨ q` (OR storage loop). -/
theorem exc_or (b q : Bool) : exc INIT_c2 true b q false = (b || q) := by
  rw [c2_eq]; cases b <;> cases q <;> rfl

/-! ## 0. Facts about A's channel -/

section chan
variable (P : InvolutionPair)

/-- A's `δ↑` is continuous at every point of its domain: it is strictly
monotone there and its image is the whole interval `(-∞, δ∞↑)` (A's
`up_surj`). No continuity hypothesis is needed. -/
theorem up_contAt {T : ℝ} (hT : -P.infDown < T) : ContinuousAt P.up T := by
  have hmono : StrictMonoOn P.up (Ioi (-P.infDown)) :=
    fun a ha b _ hab => P.up_strictMono a b ha hab
  refine hmono.continuousAt_of_image_mem_nhds (Ioi_mem_nhds hT) ?_
  refine mem_of_superset (Iio_mem_nhds (P.up_lt T hT)) ?_
  intro v hv
  obtain ⟨h1, h2⟩ := P.up_surj hv
  exact ⟨_, h1, h2⟩

theorem down_contAt {T : ℝ} (hT : -P.infUp < T) : ContinuousAt P.down T := by
  have hmono : StrictMonoOn P.down (Ioi (-P.infUp)) :=
    fun a ha b _ hab => P.down_strictMono a b ha hab
  refine hmono.continuousAt_of_image_mem_nhds (Ioi_mem_nhds hT) ?_
  refine mem_of_superset (Iio_mem_nhds (P.down_lt T hT)) ?_
  intro v hv
  obtain ⟨h1, h2⟩ := P.down_surj hv
  exact ⟨_, h1, h2⟩

/-- **Discrepancy with 5d.** No involution pair in A's sense has a `δ↑` that
is continuous on all of `ℝ`: `δ↑` takes every value below `δ↑(0)` on
`(-δ∞↓, 0)`, so it is unbounded below on the compact `[-δ∞↓, 0]`. 5d's
`InvCh` assumes `Continuous dU` and the involution law for all `T`, so it is
a different channel class; its `inv_eternal` does not transfer by
instantiation. -/
theorem up_not_continuous : ¬ Continuous P.up := by
  intro hc
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -P.infDown) (b := 0)).bddBelow_image hc.continuousOn
  have hv : B - 1 < P.infUp := by
    by_contra hcon
    push Not at hcon
    have h0 : (0 : ℝ) ∈ Icc (-P.infDown) 0 := ⟨by linarith [P.infDown_pos], le_refl _⟩
    have := hB ⟨0, h0, rfl⟩
    have := P.up_lt 0 (by linarith [P.infDown_pos])
    linarith
  rcases lt_or_ge (B - 1) (P.up 0) with hlt | hge
  · obtain ⟨h1, h2⟩ := P.up_surj hv
    have hT0 : -P.down (-(B - 1)) < 0 := by
      by_contra hcon
      push Not at hcon
      rcases eq_or_lt_of_le hcon with he | he
      · rw [← he] at h2; linarith
      · have := P.up_strictMono _ _ (by linarith [P.infDown_pos]) he
        rw [h2] at this; linarith
    have := hB ⟨_, ⟨le_of_lt h1, le_of_lt hT0⟩, h2⟩
    linarith
  · have h0 : (0 : ℝ) ∈ Icc (-P.infDown) 0 := ⟨by linarith [P.infDown_pos], le_refl _⟩
    have := hB ⟨0, h0, rfl⟩
    -- B ≤ up 0 ≤ B - 1 is absurd
    linarith

theorem delayAt_even {n : ℕ} (h : n % 2 = 0) : P.delayAt n = P.up := by
  unfold InvolutionPair.delayAt; rw [ite_eq_left h]
theorem delayAt_odd {n : ℕ} (h : n % 2 = 1) : P.delayAt n = P.down := by
  unfold InvolutionPair.delayAt; rw [ite_eq_right (by omega)]
theorem infAt_even {n : ℕ} (h : n % 2 = 0) : P.infAt n = P.infUp := by
  unfold InvolutionPair.infAt; rw [ite_eq_left h]
theorem infAt_odd {n : ℕ} (h : n % 2 = 1) : P.infAt n = P.infDown := by
  unfold InvolutionPair.infAt; rw [ite_eq_right (by omega)]

theorem delayAt_add_two (n : ℕ) : P.delayAt (n + 2) = P.delayAt n := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [delayAt_even P h, delayAt_even P (by omega)]
  · rw [delayAt_odd P h, delayAt_odd P (by omega)]

theorem infAt_add_two (n : ℕ) : P.infAt (n + 2) = P.infAt n := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [infAt_even P h, infAt_even P (by omega)]
  · rw [infAt_odd P h, infAt_odd P (by omega)]

theorem infAt_pos (n : ℕ) : 0 < P.infAt n := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [infAt_even P h]; exact P.infUp_pos
  · rw [infAt_odd P h]; exact P.infDown_pos

/-- The domain of `delayAt n` is `(-infAt (n+1), ∞)`. -/
theorem dA_lt (n : ℕ) {T : ℝ} (hT : -P.infAt (n + 1) < T) : P.delayAt n T < P.infAt n := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [delayAt_even P h, infAt_even P h]
    rw [infAt_odd P (by omega)] at hT; exact P.up_lt T hT
  · rw [delayAt_odd P h, infAt_odd P h]
    rw [infAt_even P (by omega)] at hT; exact P.down_lt T hT

theorem dA_strictMono (n : ℕ) {a b : ℝ} (ha : -P.infAt (n + 1) < a) (hab : a < b) :
    P.delayAt n a < P.delayAt n b := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [delayAt_even P h]
    rw [infAt_odd P (by omega)] at ha; exact P.up_strictMono a b ha hab
  · rw [delayAt_odd P h]
    rw [infAt_even P (by omega)] at ha; exact P.down_strictMono a b ha hab

theorem dA_mono (n : ℕ) {a b : ℝ} (ha : -P.infAt (n + 1) < a) (hab : a ≤ b) :
    P.delayAt n a ≤ P.delayAt n b := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · exact le_of_lt (dA_strictMono P n ha h)

theorem dA_contAt (n : ℕ) {T : ℝ} (hT : -P.infAt (n + 1) < T) :
    ContinuousAt (P.delayAt n) T := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [delayAt_even P h]
    rw [infAt_odd P (by omega)] at hT; exact up_contAt P hT
  · rw [delayAt_odd P h]
    rw [infAt_even P (by omega)] at hT; exact down_contAt P hT

theorem dA_pos (n : ℕ) : 0 < P.delayAt n 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [delayAt_even P h]; exact P.up_causal
  · rw [delayAt_odd P h]; exact P.down_causal

/-- The involution law at `T = 0`: a transition fed back exactly when the
previous one was emitted is undone by the next one at the same instant. -/
theorem dA_inv (n : ℕ) : P.delayAt (n + 1) (-(P.delayAt n 0)) = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [delayAt_even P h, delayAt_odd P (by omega)]
    have := P.down_neg_up (T := 0) (by linarith [P.infDown_pos]); linarith
  · rw [delayAt_odd P h, delayAt_even P (by omega)]
    have := P.up_neg_down (T := 0) (by linarith [P.infUp_pos]); linarith

end chan

/-! ## 1. The orbit of the OR loop -/

/-- Output transition times of the OR loop for a runt `[0, Δ0)`: 5d's `orb`
with A's delay functions (`dly n = δ↑` for even `n`). Derived from the
signal-level loop in `loop_orb`. -/
noncomputable def orb (P : InvolutionPair) (Δ0 : ℝ) : ℕ → ℝ
  | 0 => P.infUp
  | 1 => Δ0 + P.down (Δ0 - P.infUp)
  | n + 2 => orb P Δ0 n + P.delayAt n (orb P Δ0 n - orb P Δ0 (n + 1))

section orbit
variable (P : InvolutionPair)

theorem orb_ss (Δ0 : ℝ) (n : ℕ) :
    orb P Δ0 (n + 2) = orb P Δ0 n + P.delayAt n (orb P Δ0 n - orb P Δ0 (n + 1)) := rfl

/-- The argument of `delayAt n` is in its domain. -/
def Dom (Δ0 : ℝ) (n : ℕ) : Prop := -P.infAt (n + 1) < orb P Δ0 n - orb P Δ0 (n + 1)

/-- Runt widths of interest: `0 < Δ0 < δ∞↑`. -/
def G : Set ℝ := Ioo 0 P.infUp

def chainS (n : ℕ) : Set ℝ := {x | ∀ j < n, orb P x j < orb P x (j + 1)}

/-- The loop never cancels: it oscillates forever. -/
def Osc (x : ℝ) : Prop := ∀ n, orb P x n < orb P x (n + 1)

theorem chainS_succ {n : ℕ} {x : ℝ} :
    x ∈ chainS P (n + 1) ↔ x ∈ chainS P n ∧ orb P x n < orb P x (n + 1) := by
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega), h n (by omega)⟩
  · rintro ⟨h1, h2⟩ j hj
    by_cases hjn : j < n
    · exact h1 j hjn
    · have : j = n := by omega
      subst this; exact h2

theorem dom0 {x : ℝ} (hx : x ∈ G P) : Dom P x 0 := by
  obtain ⟨h0, h1⟩ := hx
  have := P.down_lt (x - P.infUp) (by linarith)
  show -P.infAt 1 < P.infUp - (x + P.down (x - P.infUp))
  rw [infAt_odd P (by rfl)]
  linarith

theorem dom_succ {x : ℝ} {n : ℕ} (hd : Dom P x n) (hle : orb P x n ≤ orb P x (n + 1)) :
    Dom P x (n + 1) := by
  have h := dA_lt P n hd
  show -P.infAt (n + 2) < orb P x (n + 1) - orb P x (n + 2)
  rw [orb_ss, infAt_add_two]
  linarith

theorem dom_chain {x : ℝ} (hx : x ∈ G P) : ∀ n, x ∈ chainS P n → Dom P x n := by
  intro n
  induction n with
  | zero => intro _; exact dom0 P hx
  | succ n ih =>
    intro h
    obtain ⟨h1, h2⟩ := (chainS_succ P).mp h
    exact dom_succ P (ih h1) (le_of_lt h2)

theorem cont0 (x : ℝ) : ContinuousAt (fun y => orb P y 0) x := continuousAt_const

theorem cont1 {x : ℝ} (hx : -P.infUp < x - P.infUp) : ContinuousAt (fun y => orb P y 1) x := by
  show ContinuousAt (fun y => y + P.down (y - P.infUp)) x
  have hg : ContinuousAt P.down ((fun y => y - P.infUp) x) := down_contAt P hx
  have hf : ContinuousAt (fun y => y - P.infUp) x := continuousAt_id.sub continuousAt_const
  have hc : ContinuousAt (fun y => P.down (y - P.infUp)) x :=
    ContinuousAt.comp (g := P.down) (f := fun y => y - P.infUp) hg hf
  exact continuousAt_id.add hc

theorem cont_ss {x : ℝ} {n : ℕ} (h0 : ContinuousAt (fun y => orb P y n) x)
    (h1 : ContinuousAt (fun y => orb P y (n + 1)) x) (hd : Dom P x n) :
    ContinuousAt (fun y => orb P y (n + 2)) x := by
  show ContinuousAt (fun y => orb P y n + P.delayAt n (orb P y n - orb P y (n + 1))) x
  have hg : ContinuousAt (P.delayAt n)
      ((fun y => orb P y n - orb P y (n + 1)) x) := dA_contAt P n hd
  have hf : ContinuousAt (fun y => orb P y n - orb P y (n + 1)) x := h0.sub h1
  have hc : ContinuousAt (fun y => P.delayAt n (orb P y n - orb P y (n + 1))) x :=
    ContinuousAt.comp (g := P.delayAt n) (f := fun y => orb P y n - orb P y (n + 1)) hg hf
  exact h0.add hc

theorem cont_chain {x : ℝ} (hx : x ∈ G P) : ∀ n, x ∈ chainS P n →
    ContinuousAt (fun y => orb P y n) x ∧ ContinuousAt (fun y => orb P y (n + 1)) x ∧
      ContinuousAt (fun y => orb P y (n + 2)) x := by
  have hx1 : -P.infUp < x - P.infUp := by linarith [hx.1]
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨cont0 P x, cont1 P hx1, cont_ss P (cont0 P x) (cont1 P hx1) (dom0 P hx)⟩
  | succ n ih =>
    intro h
    obtain ⟨h1, _⟩ := (chainS_succ P).mp h
    obtain ⟨_, c1, c2⟩ := ih h1
    exact ⟨c1, c2, cont_ss P c1 c2 (dom_chain P hx (n + 1) h)⟩

theorem ev_chain {x : ℝ} (hx : x ∈ G P) : ∀ n, x ∈ chainS P n →
    ∀ᶠ y in 𝓝 x, y ∈ G P ∧ y ∈ chainS P n := by
  intro n
  induction n with
  | zero =>
    intro _
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact ⟨hy, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    intro h
    obtain ⟨h1, h2⟩ := (chainS_succ P).mp h
    obtain ⟨c0, c1, _⟩ := cont_chain P hx n h1
    filter_upwards [ih h1, c0.eventually_lt c1 h2] with y hy hlt
    exact ⟨hy.1, (chainS_succ P).mpr ⟨hy.2, hlt⟩⟩

/-- First cancellation at `n`, strictly. -/
def U (n : ℕ) : Set ℝ := {x | x ∈ G P ∧ x ∈ chainS P n ∧ orb P x (n + 1) < orb P x n}
/-- Around a tie at `n`: cancellation at `n` or at `n + 2`. -/
def W (n : ℕ) : Set ℝ := {x | x ∈ G P ∧ x ∈ chainS P n ∧ Dom P x (n + 1) ∧
  orb P x (n + 1) < orb P x (n + 2) ∧ orb P x (n + 3) < orb P x (n + 2)}
/-- LOST widths: first cancellation at an even index (output ends at 0). -/
def Lset : Set ℝ := ⋃ k : ℕ, (U P (2 * k) ∪ W P (2 * k))
/-- LATCHED widths: first cancellation at an odd index (output ends at 1). -/
def Hset : Set ℝ := ⋃ k : ℕ, (U P (2 * k + 1) ∪ W P (2 * k + 1))

theorem isOpen_U (n : ℕ) : IsOpen (U P n) := by
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro x ⟨hG, hc, hlt⟩
  obtain ⟨c0, c1, _⟩ := cont_chain P hG n hc
  filter_upwards [ev_chain P hG n hc, c1.eventually_lt c0 hlt] with y hy h
  exact ⟨hy.1, hy.2, h⟩

theorem isOpen_W (n : ℕ) : IsOpen (W P n) := by
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro x ⟨hG, hc, hd, h1, h2⟩
  obtain ⟨_, c1, c2⟩ := cont_chain P hG n hc
  have c3 := cont_ss P c1 c2 hd
  have hdev : ∀ᶠ y in 𝓝 x, Dom P y (n + 1) :=
    continuousAt_const.eventually_lt (c1.sub c2) hd
  filter_upwards [ev_chain P hG n hc, hdev, c1.eventually_lt c2 h1, c3.eventually_lt c2 h2]
    with y hy hd' h1' h2'
  exact ⟨hy.1, hy.2, hd', h1', h2'⟩

theorem isOpen_L : IsOpen (Lset P) :=
  isOpen_iUnion fun _ => (isOpen_U P _).union (isOpen_W P _)

theorem isOpen_H : IsOpen (Hset P) :=
  isOpen_iUnion fun _ => (isOpen_U P _).union (isOpen_W P _)

theorem first_of_UW {x : ℝ} {n : ℕ} (h : x ∈ U P n ∪ W P n) :
    ∃ m, m % 2 = n % 2 ∧ x ∈ chainS P m ∧ orb P x (m + 1) ≤ orb P x m := by
  rcases h with ⟨_, hc, hl⟩ | ⟨_, hc, _, h1, h2⟩
  · exact ⟨n, rfl, hc, le_of_lt hl⟩
  · by_cases hn : orb P x (n + 1) ≤ orb P x n
    · exact ⟨n, rfl, hc, hn⟩
    · refine ⟨n + 2, by omega, ?_, le_of_lt h2⟩
      intro j hj
      by_cases ha : j < n
      · exact hc j ha
      · by_cases hb : j = n
        · subst hb; exact not_le.mp hn
        · have : j = n + 1 := by omega
          subst this; exact h1

theorem first_unique {x : ℝ} {m m' : ℕ} (h1 : x ∈ chainS P m)
    (f1 : orb P x (m + 1) ≤ orb P x m) (h2 : x ∈ chainS P m')
    (f2 : orb P x (m' + 1) ≤ orb P x m') : m = m' := by
  rcases lt_trichotomy m m' with h | h | h
  · exact absurd (h2 m h) (not_lt.mpr f1)
  · exact h
  · exact absurd (h1 m' h) (not_lt.mpr f2)

theorem L_first {x : ℝ} (h : x ∈ Lset P) :
    ∃ m, m % 2 = 0 ∧ x ∈ chainS P m ∧ orb P x (m + 1) ≤ orb P x m := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
  obtain ⟨m, pm, cm, fm⟩ := first_of_UW P hk
  exact ⟨m, by omega, cm, fm⟩

theorem H_first {x : ℝ} (h : x ∈ Hset P) :
    ∃ m, m % 2 = 1 ∧ x ∈ chainS P m ∧ orb P x (m + 1) ≤ orb P x m := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
  obtain ⟨m, pm, cm, fm⟩ := first_of_UW P hk
  exact ⟨m, by omega, cm, fm⟩

theorem LH_disjoint {x : ℝ} (hL : x ∈ Lset P) (hH : x ∈ Hset P) : False := by
  obtain ⟨m, pm, cm, fm⟩ := L_first P hL
  obtain ⟨m', pm', cm', fm'⟩ := H_first P hH
  have := first_unique P cm fm cm' fm'
  omega

theorem not_osc_of_first {x : ℝ} {m : ℕ} (f : orb P x (m + 1) ≤ orb P x m) : ¬ Osc P x :=
  fun h => absurd (h m) (not_lt.mpr f)

/-- Every non-oscillating width in `G` is lost or latched. A tie
`o (m+1) = o m` is resolved two transitions later by the involution law
at `T = 0` (`dA_inv`). -/
theorem cover {x : ℝ} (hx : x ∈ G P) (h : ¬ Osc P x) : x ∈ Lset P ∪ Hset P := by
  classical
  have hex : ∃ m, orb P x (m + 1) ≤ orb P x m := by
    unfold Osc at h; push Not at h; exact h
  obtain ⟨m, hfail, hmin⟩ : ∃ m, orb P x (m + 1) ≤ orb P x m ∧
      ∀ j < m, ¬ orb P x (j + 1) ≤ orb P x j :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hch : x ∈ chainS P m := fun j hj => not_le.mp (hmin j hj)
  have hUW : x ∈ U P m ∪ W P m := by
    rcases lt_or_eq_of_le hfail with hlt | heq
    · exact Or.inl ⟨hx, hch, hlt⟩
    · right
      have h2 : orb P x (m + 2) = orb P x m + P.delayAt m 0 := by
        rw [orb_ss, heq, sub_self]
      have h3 : orb P x (m + 3) =
          orb P x (m + 1) + P.delayAt (m + 1) (orb P x (m + 1) - orb P x (m + 2)) :=
        orb_ss P x (m + 1)
      have hpos := dA_pos P m
      have e : orb P x (m + 1) - orb P x (m + 2) = -(P.delayAt m 0) := by
        rw [h2, heq]; ring
      refine ⟨hx, hch, dom_succ P (dom_chain P hx m hch) (le_of_eq heq.symm), ?_, ?_⟩
      · show orb P x (m + 1) < orb P x (m + 2)
        rw [h2, heq]; linarith
      · show orb P x (m + 3) < orb P x (m + 2)
        rw [h3, e, dA_inv]
        linarith [h2, heq, hpos]
  rcases Nat.mod_two_eq_zero_or_one m with hp | hp
  · left
    obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
    exact Set.mem_iUnion.mpr ⟨k, hUW⟩
  · right
    obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
    exact Set.mem_iUnion.mpr ⟨k, hUW⟩

/-- The left end of the bracket: `l = δ∞↑ - δ↑(0)`. -/
noncomputable def lft : ℝ := P.infUp - P.up 0

theorem lft_pos : 0 < lft P := by
  have := P.up_lt 0 (by linarith [P.infDown_pos]); unfold lft; linarith

theorem lft_lt : lft P < P.infUp := by unfold lft; linarith [P.up_causal]

/-- The left end is LOST: the falling transition of the runt cancels the
first rise (`o 1 = l < o 0`). -/
theorem lft_in_L : lft P ∈ Lset P := by
  refine Set.mem_iUnion.mpr ⟨0, Or.inl ⟨⟨lft_pos P, lft_lt P⟩, fun j hj => by omega, ?_⟩⟩
  show lft P + P.down (lft P - P.infUp) < P.infUp
  have e : lft P - P.infUp = -P.up 0 := by unfold lft; ring
  rw [e, P.down_neg_up (by linarith [P.infDown_pos])]
  have := lft_lt P
  linarith

/-- Just below `δ∞↑` the runt LATCHES (`o 0 < o 1`, `o 2 < o 1`): there is
such a width `r` in `(l, δ∞↑)`. -/
theorem right_in_H : ∃ r, lft P < r ∧ r < P.infUp ∧ r ∈ Hset P := by
  set a := P.infUp with ha
  have hd0 : -P.infUp < a - P.infUp := by rw [ha, sub_self]; linarith [P.infUp_pos]
  have e1 : orb P a 1 = P.infUp + P.down 0 := by
    show a + P.down (a - P.infUp) = _
    rw [ha, sub_self]
  have hdom : Dom P a 0 := by
    show -P.infAt 1 < orb P a 0 - orb P a 1
    rw [e1, infAt_odd P (by rfl)]
    show -P.infDown < P.infUp - (P.infUp + P.down 0)
    have := P.down_lt 0 (by linarith [P.infUp_pos]); linarith
  have e2 : orb P a 2 = P.infUp := by
    rw [show (2 : ℕ) = 0 + 2 from rfl, orb_ss, e1, delayAt_even P (by rfl)]
    show P.infUp + P.up (P.infUp - (P.infUp + P.down 0)) = P.infUp
    rw [show P.infUp - (P.infUp + P.down 0) = -P.down 0 by ring,
      P.up_neg_down (by linarith [P.infUp_pos])]
    ring
  have c1 := cont1 P hd0
  have c2 := cont_ss P (cont0 P a) c1 hdom
  have hD := P.down_causal
  have ev : ∀ᶠ y in 𝓝 a, orb P y 0 < orb P y 1 ∧ orb P y 2 < orb P y 1 := by
    have h01 : orb P a 0 < orb P a 1 := by
      rw [e1]; show P.infUp < _; linarith
    have h21 : orb P a 2 < orb P a 1 := by rw [e1, e2]; linarith
    exact ((cont0 P a).eventually_lt c1 h01).and (c2.eventually_lt c1 h21)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ev
  have hu := P.up_causal
  set η := min (ε / 2) (P.up 0 / 2) with hη
  have hη1 : η ≤ ε / 2 := min_le_left _ _
  have hη2 : η ≤ P.up 0 / 2 := min_le_right _ _
  have hηpos : 0 < η := lt_min (by linarith) (by linarith)
  have hr := hball (y := a - η) (by
    rw [Real.dist_eq, show a - η - a = -η by ring, abs_neg, abs_of_pos hηpos]; linarith)
  refine ⟨a - η, ?_, ?_, ?_⟩
  · unfold lft; rw [ha]; linarith
  · rw [ha]; linarith
  · refine Set.mem_iUnion.mpr ⟨0, Or.inl ⟨⟨?_, ?_⟩, ?_, hr.2⟩⟩
    · have := lft_pos P; unfold lft at this; rw [ha]; linarith
    · rw [ha]; linarith
    · intro j hj
      have : j = 0 := by omega
      subst this; exact hr.1

/-- **Critical width.** There is `c ∈ (l, δ∞↑)` for which the loop oscillates
forever, and LOST widths accumulate at `c` from the left. (`c` is the
supremum of the lost interval starting at `l`; the involution model's
binary form of metastability.) -/
theorem crit_exists : ∃ c, lft P < c ∧ c < P.infUp ∧ Osc P c ∧
    ∀ ε > 0, ∃ y, c - ε < y ∧ y < c ∧ lft P ≤ y ∧ y ∈ Lset P := by
  obtain ⟨r, hlr, hrI, hrH⟩ := right_in_H P
  set l := lft P with hl
  set S : Set ℝ := {x | x ≤ r ∧ ∀ y, l ≤ y → y ≤ x → y ∈ Lset P} with hS
  have hlS : l ∈ S := ⟨le_of_lt hlr, fun y h1 h2 => by
    have : y = l := le_antisymm h2 h1
    rw [this]; exact lft_in_L P⟩
  have hbdd : BddAbove S := ⟨r, fun x hx => hx.1⟩
  set c := sSup S with hc
  have hlc : l ≤ c := le_csSup hbdd hlS
  have hcr : c ≤ r := csSup_le ⟨l, hlS⟩ (fun x hx => hx.1)
  have below : ∀ y, l ≤ y → y < c → y ∈ Lset P := by
    intro y hly hyc
    obtain ⟨x, hxS, hyx⟩ := exists_lt_of_lt_csSup ⟨l, hlS⟩ hyc
    exact hxS.2 y hly (le_of_lt hyx)
  have hcG : c ∈ G P := ⟨by linarith [lft_pos P], by linarith⟩
  have hrL : r ∉ Lset P := fun h => LH_disjoint P h hrH
  have hlH : l ∉ Hset P := fun h => LH_disjoint P (lft_in_L P) h
  have hcL : c ∉ Lset P := by
    intro hcL
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp (isOpen_L P) c hcL
    have hcr' : c < r := by
      rcases eq_or_lt_of_le hcr with h | h
      · exact absurd (h ▸ hcL) hrL
      · exact h
    set x := c + min (ε / 2) ((r - c) / 2) with hx
    have hm1 : min (ε / 2) ((r - c) / 2) ≤ ε / 2 := min_le_left _ _
    have hm2 : min (ε / 2) ((r - c) / 2) ≤ (r - c) / 2 := min_le_right _ _
    have hmpos : 0 < min (ε / 2) ((r - c) / 2) := lt_min (by linarith) (by linarith)
    have hxS : x ∈ S := by
      refine ⟨by linarith, fun y hly hyx => ?_⟩
      rcases lt_or_ge y c with hyc | hyc
      · exact below y hly hyc
      · apply hb
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
        linarith
    have := le_csSup hbdd hxS
    linarith
  have hcH : c ∉ Hset P := by
    intro hcH
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp (isOpen_H P) c hcH
    have hlc' : l < c := by
      rcases eq_or_lt_of_le hlc with h | h
      · exact absurd (h ▸ hcH) hlH
      · exact h
    set y := c - min (ε / 2) ((c - l) / 2) with hy
    have hm1 : min (ε / 2) ((c - l) / 2) ≤ ε / 2 := min_le_left _ _
    have hm2 : min (ε / 2) ((c - l) / 2) ≤ (c - l) / 2 := min_le_right _ _
    have hmpos : 0 < min (ε / 2) ((c - l) / 2) := lt_min (by linarith) (by linarith)
    have hyH : y ∈ Hset P := by
      apply hb
      rw [Metric.mem_ball, Real.dist_eq, show y - c = -min (ε / 2) ((c - l) / 2) by rw [hy]; ring,
        abs_neg, abs_of_pos hmpos]
      linarith
    exact LH_disjoint P (below y (by linarith) (by linarith)) hyH
  have hosc : Osc P c := by
    by_contra hno
    rcases cover P hcG hno with h | h
    · exact hcL h
    · exact hcH h
  have hlc' : l < c := by
    rcases eq_or_lt_of_le hlc with h | h
    · exact absurd (h ▸ lft_in_L P) hcL
    · exact h
  refine ⟨c, hlc', by linarith, hosc, ?_⟩
  intro ε hε
  set y := c - min (ε / 2) ((c - l) / 2) with hy
  have hm1 : min (ε / 2) ((c - l) / 2) ≤ ε / 2 := min_le_left _ _
  have hm2 : min (ε / 2) ((c - l) / 2) ≤ (c - l) / 2 := min_le_right _ _
  have hmpos : 0 < min (ε / 2) ((c - l) / 2) := lt_min (by linarith) (by linarith)
  exact ⟨y, by linarith, by linarith, by linarith, below y (by linarith) (by linarith)⟩

/-- 5d's `inv_eternal`, on A's channel. -/
theorem inv_eternal : ∃ Δ0, lft P < Δ0 ∧ Δ0 < P.infUp ∧ Osc P Δ0 := by
  obtain ⟨c, h1, h2, h3, _⟩ := crit_exists P
  exact ⟨c, h1, h2, h3⟩

theorem exists_mul_gt {D : ℝ} (hD : 0 < D) (x : ℝ) : ∃ n : ℕ, x < n * D := by
  obtain ⟨n, hn⟩ := Archimedean.arch x hD
  refine ⟨n + 1, ?_⟩
  rw [nsmul_eq_mul] at hn
  push_cast
  linarith

/-- A uniform positive delay just left of `T = 0`. -/
theorem exists_c : ∃ c > 0, c < P.infUp ∧ c < P.infDown ∧ 0 < P.up (-c) ∧ 0 < P.down (-c) := by
  have ev : ∀ᶠ y in 𝓝 (0 : ℝ), 0 < P.up y ∧ 0 < P.down y :=
    (continuousAt_const.eventually_lt (up_contAt P (by linarith [P.infDown_pos])) P.up_causal).and
      (continuousAt_const.eventually_lt (down_contAt P (by linarith [P.infUp_pos])) P.down_causal)
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp ev
  have hU := P.infUp_pos
  have hD := P.infDown_pos
  set c := min (ε / 2) (min (P.infUp / 2) (P.infDown / 2)) with hc
  have h1 : c ≤ ε / 2 := min_le_left _ _
  have h2 : c ≤ P.infUp / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have h3 : c ≤ P.infDown / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hcpos : 0 < c := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have := hb (y := -c) (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hcpos]; linarith)
  exact ⟨c, hcpos, by linarith, by linarith, this.1, this.2⟩

/-- **No Zeno.** On an oscillating orbit the even transitions go to `∞`
at a uniform rate: `o (2k) ≥ o 0 + k·p` for a fixed `p > 0`. -/
theorem osc_unbounded {x : ℝ} (h : Osc P x) : ∀ B : ℝ, ∃ k : ℕ, B < orb P x (2 * k) := by
  obtain ⟨c, hc, hcU, hcD, hU, hD⟩ := exists_c P
  set p := min c (min (P.up (-c)) (P.down (-c))) with hp
  have hp0 : 0 < p := lt_min hc (lt_min hU hD)
  have step2 : ∀ n, orb P x n + p ≤ orb P x (n + 2) := by
    intro n
    have e := orb_ss P x n
    have h1 := h n
    have h2 := h (n + 1)
    by_cases hw : orb P x (n + 1) - orb P x n ≤ c
    · have hdom : -P.infAt (n + 1) < -c := by
        rcases Nat.mod_two_eq_zero_or_one n with hq | hq
        · rw [infAt_odd P (by omega)]; linarith
        · rw [infAt_even P (by omega)]; linarith
      have hmono : P.delayAt n (-c) ≤ P.delayAt n (orb P x n - orb P x (n + 1)) :=
        dA_mono P n hdom (by linarith)
      have hlow : p ≤ P.delayAt n (-c) := by
        rcases Nat.mod_two_eq_zero_or_one n with hq | hq
        · rw [delayAt_even P hq]; exact le_trans (min_le_right _ _) (min_le_left _ _)
        · rw [delayAt_odd P hq]; exact le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
    · have : p ≤ c := min_le_left _ _
      push Not at hw
      linarith
  have lin : ∀ k : ℕ, orb P x 0 + k * p ≤ orb P x (2 * k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := step2 (2 * k)
      rw [show 2 * (k + 1) = 2 * k + 2 by ring]
      push_cast
      linarith
  intro B
  obtain ⟨k, hk⟩ := exists_mul_gt hp0 (B - orb P x 0)
  exact ⟨k, by linarith [lin k]⟩

end orbit

/-! ## 2. Signal level

A transition sequence `s` with a downward-closed activity predicate `ok`
denotes the signal that starts at 0 (value at `-∞`) and toggles at each
active `s n`: it is 1 on `[s n, s (n+1))` for even active `n` (to `∞` if
`n + 1` is not active). -/

def Hi (s : ℕ → ℝ) (ok : ℕ → Prop) (u : ℝ) : Prop :=
  ∃ n, n % 2 = 0 ∧ ok n ∧ s n ≤ u ∧ (ok (n + 1) → u < s (n + 1))

open Classical in
/-- The signal denoted by a transition sequence. -/
noncomputable def den (s : ℕ → ℝ) (ok : ℕ → Prop) : Sig := fun u => decide (Hi s ok u)

open Classical in
theorem den_true {s : ℕ → ℝ} {ok : ℕ → Prop} {u : ℝ} : den s ok u = true ↔ Hi s ok u := by
  unfold den; exact decide_eq_true_iff

def DownC (ok : ℕ → Prop) : Prop := ∀ n, ok (n + 1) → ok n
def Incr (s : ℕ → ℝ) (ok : ℕ → Prop) : Prop := ∀ n, ok (n + 1) → s n < s (n + 1)

section sig
variable {s s' : ℕ → ℝ} {ok ok' : ℕ → Prop}

theorem ok_le (hd : DownC ok) {i j : ℕ} (hj : ok j) (hij : i ≤ j) : ok i := by
  induction j with
  | zero => have : i = 0 := by omega
            rw [this]; exact hj
  | succ j ih =>
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]; exact hj
    · exact ih (hd j hj) (by omega)

theorem s_lt (hd : DownC ok) (hi : Incr s ok) {i j : ℕ} (hj : ok j) (hij : i < j) :
    s i < s j := by
  induction j with
  | zero => omega
  | succ j ih =>
    have h1 := hi j hj
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hij) with h | h
    · rw [h]; exact h1
    · exact lt_trans (ih (hd j hj) h) h1

theorem s_le (hd : DownC ok) (hi : Incr s ok) {i j : ℕ} (hj : ok j) (hij : i ≤ j) :
    s i ≤ s j := by
  rcases eq_or_lt_of_le hij with h | h
  · rw [h]
  · exact le_of_lt (s_lt hd hi hj h)

/-- Value of the denoted signal between two consecutive transitions. -/
theorem hi_iff (hd : DownC ok) (hi : Incr s ok) {n : ℕ} {u : ℝ} (hn : ok n) (h1 : s n ≤ u)
    (h2 : ok (n + 1) → u < s (n + 1)) : Hi s ok u ↔ n % 2 = 0 := by
  constructor
  · rintro ⟨m, pm, okm, hm1, hm2⟩
    rcases lt_trichotomy m n with h | h | h
    · have hok : ok (m + 1) := ok_le hd hn h
      have := hm2 hok
      have := s_le hd hi hn (show m + 1 ≤ n by omega)
      linarith
    · rw [← h]; exact pm
    · have hok : ok (n + 1) := ok_le hd okm h
      have := h2 hok
      have := s_le hd hi okm (show n + 1 ≤ m by omega)
      linarith
  · intro p; exact ⟨n, p, hn, h1, h2⟩

/-- Before the first transition the denoted signal is 0. -/
theorem hi_before (hd : DownC ok) (hi : Incr s ok) {u : ℝ} (h : ok 0 → u < s 0) :
    ¬ Hi s ok u := by
  rintro ⟨m, _, okm, hm, _⟩
  have := h (ok_le hd okm (Nat.zero_le m))
  have := s_le hd hi okm (Nat.zero_le m)
  linarith

theorem hi_congr (hok : ∀ n, ok n ↔ ok' n) (hs : ∀ n, ok n → s n = s' n) (u : ℝ) :
    Hi s ok u ↔ Hi s' ok' u := by
  constructor
  · rintro ⟨n, p, o, h1, h2⟩
    refine ⟨n, p, (hok n).mp o, (hs n o) ▸ h1, fun o' => ?_⟩
    have o1 := (hok (n + 1)).mpr o'
    rw [← hs (n + 1) o1]; exact h2 o1
  · rintro ⟨n, p, o, h1, h2⟩
    have o0 := (hok n).mpr o
    refine ⟨n, p, o0, (hs n o0).symm ▸ h1, fun o1 => ?_⟩
    rw [hs (n + 1) o1]; exact h2 ((hok (n + 1)).mp o1)

theorem den_congr (hok : ∀ n, ok n ↔ ok' n) (hs : ∀ n, ok n → s n = s' n) :
    den s ok = den s' ok' := by
  funext u
  rw [Bool.eq_iff_iff, den_true, den_true]
  exact hi_congr hok hs u

theorem side_zero (hd : DownC ok) (hi : Incr s ok) (hd' : DownC ok') (hi' : Incr s' ok')
    (he : ∀ u, Hi s ok u ↔ Hi s' ok' u) (h0 : ok 0) : ok' 0 ∧ s' 0 ≤ s 0 := by
  have hs : Hi s ok (s 0) := (hi_iff hd hi h0 (le_refl _) (fun o => hi (0) o)).mpr rfl
  have hs' := (he (s 0)).mp hs
  by_cases h' : ok' 0
  · refine ⟨h', ?_⟩
    by_contra hlt
    push Not at hlt
    exact hi_before hd' hi' (fun _ => hlt) hs'
  · exact absurd hs' (hi_before hd' hi' (fun o => absurd o h'))

theorem side_succ (hd : DownC ok) (hi : Incr s ok) (hd' : DownC ok') (hi' : Incr s' ok')
    (he : ∀ u, Hi s ok u ↔ Hi s' ok' u) {j : ℕ} (hj' : ok' j) (hsj : s' j = s j)
    (h1 : ok (j + 1)) : ok' (j + 1) ∧ s' (j + 1) ≤ s (j + 1) := by
  have hpar : Hi s ok (s (j + 1)) ↔ (j + 1) % 2 = 0 :=
    hi_iff hd hi h1 (le_refl _) (fun o => hi (j + 1) o)
  have hlt : s j < s (j + 1) := hi j h1
  by_cases h' : ok' (j + 1)
  · refine ⟨h', ?_⟩
    by_contra hc
    push Not at hc
    have hpar' : Hi s' ok' (s (j + 1)) ↔ j % 2 = 0 :=
      hi_iff hd' hi' hj' (by rw [hsj]; exact le_of_lt hlt) (fun _ => hc)
    have := (he (s (j + 1))).trans hpar'
    rw [hpar] at this
    omega
  · have hpar' : Hi s' ok' (s (j + 1)) ↔ j % 2 = 0 :=
      hi_iff hd' hi' hj' (by rw [hsj]; exact le_of_lt hlt) (fun o => absurd o h')
    have := (he (s (j + 1))).trans hpar'
    rw [hpar] at this
    omega

/-- **Transition times are determined by the signal**: two increasing
transition sequences that denote the same signal have the same active
indices and the same times. -/
theorem den_inj (hd : DownC ok) (hi : Incr s ok) (hd' : DownC ok') (hi' : Incr s' ok')
    (h : den s ok = den s' ok') : ∀ n, (ok n ↔ ok' n) ∧ (ok n → s n = s' n) := by
  have he : ∀ u, Hi s ok u ↔ Hi s' ok' u := by
    intro u
    have := congrFun h u
    rw [Bool.eq_iff_iff, den_true, den_true] at this
    exact this
  have he' : ∀ u, Hi s' ok' u ↔ Hi s ok u := fun u => (he u).symm
  intro n
  induction n with
  | zero =>
    by_cases h0 : ok 0
    · obtain ⟨h0', a1⟩ := side_zero hd hi hd' hi' he h0
      obtain ⟨_, a2⟩ := side_zero hd' hi' hd hi he' h0'
      exact ⟨⟨fun _ => h0', fun _ => h0⟩, fun _ => le_antisymm a2 a1⟩
    · refine ⟨⟨fun o => absurd o h0, fun o' => ?_⟩, fun o => absurd o h0⟩
      exact (side_zero hd' hi' hd hi he' o').1
  | succ n ih =>
    by_cases h1 : ok (n + 1)
    · have on : ok n := hd n h1
      have on' : ok' n := ih.1.mp on
      have es : s n = s' n := ih.2 on
      obtain ⟨h1', a1⟩ := side_succ hd hi hd' hi' he on' es.symm h1
      obtain ⟨_, a2⟩ := side_succ hd' hi' hd hi he' on es h1'
      exact ⟨⟨fun _ => h1', fun _ => h1⟩, fun _ => le_antisymm a2 a1⟩
    · refine ⟨⟨fun o => absurd o h1, fun o' => ?_⟩, fun o => absurd o h1⟩
      have on' : ok' n := hd' n o'
      have on : ok n := ih.1.mpr on'
      exact (side_succ hd' hi' hd hi he' on (ih.2 on) o').1

end sig

/-! ### The channel relation (signal level, on A's `tent`) -/

/-- How A's channel acts on an input transition sequence `t` (active indices
`ok`), with surviving output indices `okO`. Three shapes are
allowed (fragment: at most one cancellation, of the LAST two tentative
transitions; see the notes):
* infinitely many inputs, no tentative output ever cancelled;
* inputs `0 .. m+1`, outputs `0 .. m-1` real, tentative outputs `m` and
  `m+1` annihilate (A's `cancel_iff`: `tent (m+1) ≤ tent m`);
* inputs `0 .. N-1`, all `N` outputs real. -/
structure InvRun (P : InvolutionPair) (t : ℕ → ℝ) (ok okO : ℕ → Prop) : Prop where
  down : DownC ok
  incr : Incr t ok
  out :
    ((∀ n, ok n) ∧ (∀ n, okO n) ∧ ∀ n, P.tent t n < P.tent t (n + 1)) ∨
    (∃ m, (∀ n, ok n ↔ n < m + 2) ∧ (∀ n, okO n ↔ n < m) ∧
        (∀ n < m, P.tent t n < P.tent t (n + 1)) ∧ P.tent t (m + 1) ≤ P.tent t m) ∨
    (∃ N, (∀ n, ok n ↔ n < N) ∧ (∀ n, okO n ↔ n < N) ∧
        ∀ n, n + 1 < N → P.tent t n < P.tent t (n + 1))

/-- **Signal-level involution channel relation** (fragment): `y` is the
output of A's channel `P` for input `x`. -/
def InvChanF (P : InvolutionPair) (x y : Sig) : Prop :=
  ∃ t ok okO, InvRun P t ok okO ∧ x = den t ok ∧ y = den (P.tent t) okO

theorem run_out {P : InvolutionPair} {t : ℕ → ℝ} {ok okO : ℕ → Prop} (R : InvRun P t ok okO) :
    DownC okO ∧ Incr (P.tent t) okO := by
  rcases R.out with ⟨_, h2, h3⟩ | ⟨m, _, h2, h3, _⟩ | ⟨N, _, h2, h3⟩
  · exact ⟨fun n _ => h2 n, fun n _ => h3 n⟩
  · refine ⟨fun n o => (h2 n).mpr (by have := (h2 (n + 1)).mp o; omega), fun n o => ?_⟩
    exact h3 n (by have := (h2 (n + 1)).mp o; omega)
  · refine ⟨fun n o => (h2 n).mpr (by have := (h2 (n + 1)).mp o; omega), fun n o => ?_⟩
    exact h3 n ((h2 (n + 1)).mp o)

/-! ### The loop -/

/-- Prepend the runt's two input transitions `0` (rise) and `Δ0` (fall). -/
def cons2 (a b : ℝ) (o : ℕ → ℝ) : ℕ → ℝ
  | 0 => a
  | 1 => b
  | n + 2 => o n

def ok2 (okO : ℕ → Prop) : ℕ → Prop
  | 0 => True
  | 1 => True
  | n + 2 => okO n

theorem den_cons2 (Δ0 : ℝ) (o : ℕ → ℝ) (okO : ℕ → Prop) (u : ℝ) :
    (decide (0 ≤ u ∧ u < Δ0) || den o okO u) = den (cons2 0 Δ0 o) (ok2 okO) u := by
  rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_iff, den_true, den_true]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨k, pk, okk, h1, h2⟩)
    · exact ⟨0, rfl, trivial, h1, fun _ => h2⟩
    · exact ⟨k + 2, by omega, okk, h1, h2⟩
  · rintro ⟨n, pn, okn, h1, h2⟩
    match n, pn, okn, h1, h2 with
    | 0, _, _, h1, h2 => exact Or.inl ⟨h1, h2 trivial⟩
    | 1, pn, _, _, _ => exact absurd pn (by decide)
    | k + 2, pn, okn, h1, h2 => exact Or.inr ⟨k, by omega, okn, h1, h2⟩

theorem incr_cons2 {Δ0 : ℝ} {o : ℕ → ℝ} {okO : ℕ → Prop} (h0 : 0 < Δ0) (h1 : Δ0 < o 0)
    (hi : Incr o okO) : Incr (cons2 0 Δ0 o) (ok2 okO) := by
  intro n hn
  match n, hn with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | k + 2, hn => exact hi k hn

theorem down_ok2 {okO : ℕ → Prop} (hd : DownC okO) : DownC (ok2 okO) := by
  intro n hn
  match n, hn with
  | 0, _ => trivial
  | 1, _ => trivial
  | k + 2, hn => exact hd k hn

/-- **The `bd_c2` feedback loop, Fuegger gate model.** Every field is a
named hypothesis.
* `H_A`, `H_RST`: pin `I0 = a` held at 1, `I3 = rst` held at 0 (the
  C-element waits for `b`).
* `H_RUNT`: pin `I1 = b` carries a runt `[0, Δ0)` (as seen at the pin).
* `H_LUT`: the LUT's Boolean function is applied in ZERO time: `x` is
  `lutB INIT_c2` of the current pin values (Fuegger's gate = zero-time
  Boolean function + channel). Faithfulness: the real LUT is a mux tree;
  its delay and pulse shaping are all moved into the channel.
* `H_CH`: the LUT output, routed back to pin `I2 = q`, is the output of ONE
  involution channel (LUT + feedback wire lumped) fed by `x`: A's
  `InvolutionPair` and `tent`, as the signal-level relation `InvChanF`.
  Test: fit `δ↑`, `δ↓` from pulse-shrink measurements of LUT + route
  (A's notes). -/
structure CLoop (P : InvolutionPair) (Δ0 : ℝ) (a b rst x qp : Sig) : Prop where
  H_A : ∀ u, a u = true
  H_RST : ∀ u, rst u = false
  H_RUNT : ∀ u, b u = decide (0 ≤ u ∧ u < Δ0)
  H_LUT : ∀ u, x u = exc INIT_c2 (a u) (b u) (qp u) (rst u)
  H_CH : InvChanF P x qp

section loop
variable (P : InvolutionPair)

/-- If the channel's input transitions are `0, Δ0, o 0, o 1, ...` (the
feedback closes the loop), its tentative outputs are exactly `orb`. -/
theorem tent_eq_orb {Δ0 : ℝ} {t : ℕ → ℝ} {ok : ℕ → Prop} (hd : DownC ok)
    (h0 : t 0 = 0) (h1 : ok 1 → t 1 = Δ0) (h2 : ∀ n, ok (n + 2) → t (n + 2) = P.tent t n) :
    ∀ n, ok (n + 1) → P.tent t n = orb P Δ0 n ∧ P.tent t (n + 1) = orb P Δ0 (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro o1
    have e0 : P.tent t 0 = orb P Δ0 0 := by
      show t 0 + P.infUp = P.infUp; rw [h0]; ring
    refine ⟨e0, ?_⟩
    show t 1 + P.delayAt 1 (t 1 - P.tent t 0) = Δ0 + P.down (Δ0 - P.infUp)
    rw [h1 o1, delayAt_odd P (by rfl), e0]; rfl
  | succ n ih =>
    intro o2
    obtain ⟨e0, e1⟩ := ih (hd (n + 1) o2)
    refine ⟨e1, ?_⟩
    show t (n + 2) + P.delayAt (n + 2) (t (n + 2) - P.tent t (n + 1)) = orb P Δ0 (n + 2)
    rw [h2 n o2, delayAt_add_two, e0, e1]; rfl

/-- **Derivation of 5d's recurrence from the signal-level loop.** For a runt
`0 < Δ0 < δ∞↑`, in EVERY solution of the loop the C-element output `qp` is
the alternating signal with transition times `orb P Δ0`: either forever (the
loop oscillates forever) or up to the first cancellation index `m`, after
which it is constant (`0` if `m` is even: LOST; `1` if odd: LATCHED). -/
theorem loop_orb {Δ0 : ℝ} (hΔ0 : 0 < Δ0) (hΔ1 : Δ0 < P.infUp) {a b rst x qp : Sig}
    (L : CLoop P Δ0 a b rst x qp) :
    (Osc P Δ0 ∧ qp = den (orb P Δ0) (fun _ => True)) ∨
    (∃ m, Δ0 ∈ chainS P m ∧ orb P Δ0 (m + 1) ≤ orb P Δ0 m ∧
      qp = den (orb P Δ0) (fun n => n < m)) := by
  obtain ⟨t, ok, okO, R, hx, hqp⟩ := L.H_CH
  obtain ⟨hdO, hiO⟩ := run_out R
  have hxq : ∀ u, x u = (decide (0 ≤ u ∧ u < Δ0) || den (P.tent t) okO u) := by
    intro u; rw [L.H_LUT, L.H_A, L.H_RST, exc_or, L.H_RUNT, hqp]
  have hxd : ∀ u, x u = den t ok u := fun u => congrFun hx u
  -- the first input transition is the runt's rise at 0
  have hok0 : ok 0 := by
    by_contra h
    have e := (hxq 0).symm.trans (hxd 0)
    have hb : decide ((0 : ℝ) ≤ 0 ∧ (0 : ℝ) < Δ0) = true := by
      rw [decide_eq_true_iff]; exact ⟨le_refl _, hΔ0⟩
    rw [hb, Bool.true_or] at e
    exact hi_before R.down R.incr (fun o => absurd o h) (den_true.mp e.symm)
  have ht0 : t 0 = 0 := by
    rcases lt_trichotomy (t 0) 0 with h | h | h
    · exfalso
      have hhi : Hi t ok (t 0) := (hi_iff R.down R.incr hok0 (le_refl _)
        (fun o => R.incr 0 o)).mpr rfl
      have e := (hxd (t 0)).symm.trans (hxq (t 0))
      rw [den_true.mpr hhi] at e
      have hb : decide (0 ≤ t 0 ∧ t 0 < Δ0) = false := by
        rw [decide_eq_false_iff_not]; intro hh; linarith [hh.1]
      have hq : den (P.tent t) okO (t 0) = false := by
        rw [Bool.eq_false_iff]; intro hh
        refine hi_before hdO hiO (fun _ => ?_) (den_true.mp hh)
        show t 0 < t 0 + P.infUp
        linarith [P.infUp_pos]
      rw [hb, hq] at e
      exact Bool.noConfusion e
    · exact h
    · exfalso
      have e := (hxq 0).symm.trans (hxd 0)
      have hb : decide ((0 : ℝ) ≤ 0 ∧ (0 : ℝ) < Δ0) = true := by
        rw [decide_eq_true_iff]; exact ⟨le_refl _, hΔ0⟩
      rw [hb, Bool.true_or] at e
      exact hi_before R.down R.incr (fun _ => h) (den_true.mp e.symm)
  have htent0 : P.tent t 0 = P.infUp := by
    show t 0 + P.infUp = P.infUp; rw [ht0]; ring
  -- the input is the runt OR the fed-back output: cons2 0 Δ0 (tent t)
  have hx2 : den t ok = den (cons2 0 Δ0 (P.tent t)) (ok2 okO) := by
    funext u; rw [← hxd u, hxq u, den_cons2]
  have hinj := den_inj R.down R.incr (down_ok2 hdO)
    (incr_cons2 hΔ0 (by rw [htent0]; exact hΔ1) hiO) hx2
  have h1 : ok 1 → t 1 = Δ0 := fun o => (hinj 1).2 o
  have h2 : ∀ n, ok (n + 2) → t (n + 2) = P.tent t n := fun n o => (hinj (n + 2)).2 o
  have hT := tent_eq_orb P R.down ht0 h1 h2
  have hok2 : ∀ n, ok (n + 2) ↔ okO n := fun n => (hinj (n + 2)).1
  rcases R.out with ⟨hall, hallO, hinc⟩ | ⟨m, hm1, hm2, hm3, hm4⟩ | ⟨N, hN1, hN2, _⟩
  · left
    refine ⟨fun n => ?_, ?_⟩
    · obtain ⟨e0, e1⟩ := hT n (hall _)
      rw [← e0, ← e1]; exact hinc n
    · rw [hqp]
      exact den_congr (fun n => ⟨fun _ => trivial, fun _ => hallO n⟩)
        (fun n _ => (hT n (hall _)).1)
  · right
    refine ⟨m, fun j hj => ?_, ?_, ?_⟩
    · obtain ⟨e0, e1⟩ := hT j ((hm1 _).mpr (by omega))
      rw [← e0, ← e1]; exact hm3 j hj
    · obtain ⟨e0, e1⟩ := hT m ((hm1 _).mpr (by omega))
      rw [← e0, ← e1]; exact hm4
    · rw [hqp]
      exact den_congr (fun n => hm2 n) (fun n o => (hT n ((hm1 _).mpr (by
        have := (hm2 n).mp o; omega))).1)
  · exfalso
    have hN : 0 < N := (hN1 0).mp hok0
    obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
    have : ok (K + 2) := (hok2 K).mpr ((hN2 K).mpr (by omega))
    have := (hN1 _).mp this
    omega

/-- The input pins of the runt experiment. -/
def aR : Sig := fun _ => true
def rstR : Sig := fun _ => false
noncomputable def bR (Δ0 : ℝ) : Sig := fun u => decide (0 ≤ u ∧ u < Δ0)

theorem tent_cons2 (Δ0 : ℝ) :
    ∀ n, P.tent (cons2 0 Δ0 (orb P Δ0)) n = orb P Δ0 n ∧
      P.tent (cons2 0 Δ0 (orb P Δ0)) (n + 1) = orb P Δ0 (n + 1) := by
  intro n
  induction n with
  | zero =>
    have e0 : P.tent (cons2 0 Δ0 (orb P Δ0)) 0 = orb P Δ0 0 := by
      show (0 : ℝ) + P.infUp = P.infUp; ring
    refine ⟨e0, ?_⟩
    show Δ0 + P.delayAt 1 (Δ0 - P.tent (cons2 0 Δ0 (orb P Δ0)) 0) = Δ0 + P.down (Δ0 - P.infUp)
    rw [delayAt_odd P (by rfl), e0]; rfl
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    show orb P Δ0 n + P.delayAt (n + 2) (orb P Δ0 n - P.tent (cons2 0 Δ0 (orb P Δ0)) (n + 1))
      = orb P Δ0 (n + 2)
    rw [delayAt_add_two, ih.2]; rfl

/-- **Existence.** For every runt `0 < Δ0 < δ∞↑` the loop has a solution
(the one whose output transitions are `orb P Δ0`). -/
theorem loop_exists {Δ0 : ℝ} (hΔ0 : 0 < Δ0) (hΔ1 : Δ0 < P.infUp) :
    ∃ x qp : Sig, CLoop P Δ0 aR (bR Δ0) rstR x qp := by
  classical
  set t := cons2 0 Δ0 (orb P Δ0) with ht
  have hT : ∀ n, P.tent t n = orb P Δ0 n := fun n => (tent_cons2 P Δ0 n).1
  by_cases hosc : Osc P Δ0
  · refine ⟨den t (fun _ => True), den (orb P Δ0) (fun _ => True), ?_⟩
    have hR : InvRun P t (fun _ => True) (fun _ => True) := by
      refine ⟨fun _ _ => trivial, fun n _ => ?_, Or.inl ⟨fun _ => trivial, fun _ => trivial,
        fun n => by rw [hT, hT]; exact hosc n⟩⟩
      exact incr_cons2 (okO := fun _ => True) hΔ0 hΔ1 (fun k _ => hosc k) n
        (by match n with
            | 0 => trivial
            | 1 => trivial
            | _ + 2 => trivial)
    refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun u => ?_, ⟨t, _, _, hR, rfl, ?_⟩⟩
    · show den t (fun _ => True) u = exc INIT_c2 true (bR Δ0 u) _ false
      rw [exc_or, bR, den_cons2]
      exact congrFun (den_congr (fun n => by
        match n with
        | 0 => exact Iff.rfl
        | 1 => exact Iff.rfl
        | _ + 2 => exact Iff.rfl) (fun _ _ => rfl)) u
    · exact den_congr (fun _ => Iff.rfl) (fun n _ => (hT n).symm)
  · have hex : ∃ m, orb P Δ0 (m + 1) ≤ orb P Δ0 m := by
      unfold Osc at hosc; push Not at hosc; exact hosc
    set m := Nat.find hex with hm
    have hfail : orb P Δ0 (m + 1) ≤ orb P Δ0 m := Nat.find_spec hex
    have hmin : ∀ j < m, orb P Δ0 j < orb P Δ0 (j + 1) :=
      fun j hj => not_le.mp (Nat.find_min hex hj)
    refine ⟨den t (fun n => n < m + 2), den (orb P Δ0) (fun n => n < m), ?_⟩
    have hR : InvRun P t (fun n => n < m + 2) (fun n => n < m) := by
      refine ⟨fun n h => by omega, fun n hn => ?_, Or.inr (Or.inl ⟨m, fun _ => Iff.rfl,
        fun _ => Iff.rfl, fun n hn => by rw [hT, hT]; exact hmin n hn,
        by rw [hT, hT]; exact hfail⟩)⟩
      match n, hn with
      | 0, _ => exact hΔ0
      | 1, _ => exact hΔ1
      | k + 2, hn => exact hmin k (by omega)
    refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun u => ?_, ⟨t, _, _, hR, rfl, ?_⟩⟩
    · show den t (fun n => n < m + 2) u = exc INIT_c2 true (bR Δ0 u) _ false
      rw [exc_or, bR, den_cons2]
      exact congrFun (den_congr (fun n => by
        match n with
        | 0 => exact ⟨fun _ => trivial, fun _ => by omega⟩
        | 1 => exact ⟨fun _ => trivial, fun _ => by omega⟩
        | k + 2 => exact ⟨fun h => (by omega : k < m), fun h => (by
            have : k < m := h
            omega)⟩) (fun _ _ => rfl)) u
    · exact den_congr (fun _ => Iff.rfl) (fun n _ => (hT n).symm)

/-! ### Main results at signal level -/

/-- **Eternal oscillation (5d's `inv_eternal`, on A's channel, signal
level).** There is a runt width `Δ0 ∈ (δ∞↑ - δ↑(0), δ∞↑)` for which the
`bd_c2` loop has a solution, and in EVERY solution the output `qp` takes
both values after every time bound `B`: the C-element never resolves. -/
theorem c2_eternal : ∃ Δ0, lft P < Δ0 ∧ Δ0 < P.infUp ∧
    (∃ x qp : Sig, CLoop P Δ0 aR (bR Δ0) rstR x qp) ∧
    ∀ a b rst x qp : Sig, CLoop P Δ0 a b rst x qp →
      ∀ B : ℝ, (∃ u, B < u ∧ qp u = true) ∧ (∃ u, B < u ∧ qp u = false) := by
  obtain ⟨c, hlc, hcI, hosc, _⟩ := crit_exists P
  have hc0 : 0 < c := lt_trans (lft_pos P) hlc
  refine ⟨c, hlc, hcI, loop_exists P hc0 hcI, ?_⟩
  intro a b rst x qp L B
  rcases loop_orb P hc0 hcI L with ⟨_, hq⟩ | ⟨m, _, hf, _⟩
  · obtain ⟨k, hk⟩ := osc_unbounded P hosc B
    have hd : DownC (fun _ : ℕ => True) := fun _ _ => trivial
    have hi : Incr (orb P c) (fun _ => True) := fun n _ => hosc n
    refine ⟨⟨orb P c (2 * k), hk, ?_⟩, ⟨orb P c (2 * k + 1), by linarith [hosc (2 * k)], ?_⟩⟩
    · rw [hq, den_true]
      exact (hi_iff hd hi trivial (le_refl _) (fun _ => hosc _)).mpr (by omega)
    · rw [hq, Bool.eq_false_iff]; intro hh
      have := (hi_iff hd hi trivial (le_refl _) (fun _ => hosc _)).mp (den_true.mp hh)
      omega
  · exact absurd (hosc m) (not_lt.mpr hf)

/-- **Unbounded resolution time near the critical width.** Let `c` be the
critical width of `crit_exists` (it oscillates forever). For every `ε > 0`
and every time `B` there is a runt width `Δ0 ∈ (c - ε, c)` such that the loop
has a solution, and EVERY solution is LOST (`qp` is eventually constant 0)
yet `qp` is still 1 at some time after `B`. So the resolution time is not
bounded on any neighbourhood of `c`. -/
theorem c2_slow_resolution : ∃ c, lft P < c ∧ c < P.infUp ∧ Osc P c ∧
    ∀ ε > 0, ∀ B : ℝ, ∃ Δ0, c - ε < Δ0 ∧ Δ0 < c ∧
      (∃ x qp : Sig, CLoop P Δ0 aR (bR Δ0) rstR x qp) ∧
      ∀ a b rst x qp : Sig, CLoop P Δ0 a b rst x qp →
        (∃ u, B < u ∧ qp u = true) ∧ (∃ T, ∀ u, T ≤ u → qp u = false) := by
  obtain ⟨c, hlc, hcI, hosc, happ⟩ := crit_exists P
  have hc0 : 0 < c := lt_trans (lft_pos P) hlc
  have hcG : c ∈ G P := ⟨hc0, hcI⟩
  refine ⟨c, hlc, hcI, hosc, ?_⟩
  intro ε hε B
  obtain ⟨k, hk⟩ := osc_unbounded P hosc B
  set n := 2 * k with hn
  have hch : c ∈ chainS P (n + 1) := fun j _ => hosc j
  obtain ⟨c0, _, _⟩ := cont_chain P hcG n (fun j _ => hosc j)
  have ev : ∀ᶠ y in 𝓝 c, (y ∈ G P ∧ y ∈ chainS P (n + 1)) ∧ B < orb P y n :=
    (ev_chain P hcG (n + 1) hch).and (continuousAt_const.eventually_lt c0 hk)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp ev
  obtain ⟨y, hy1, hy2, hly, hyL⟩ := happ (min ε δ) (lt_min hε hδ)
  have hm1 : min ε δ ≤ ε := min_le_left _ _
  have hm2 : min ε δ ≤ δ := min_le_right _ _
  obtain ⟨⟨hyG, hych⟩, hyB⟩ := hball (y := y) (by
    rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith)
  obtain ⟨m, pm, cm, fm⟩ := L_first P hyL
  have hnm : n < m := by
    by_contra hc
    push Not at hc
    exact absurd (hych m (by omega)) (not_lt.mpr fm)
  refine ⟨y, by linarith, hy2, loop_exists P hyG.1 hyG.2, ?_⟩
  intro a b rst x qp L
  rcases loop_orb P hyG.1 hyG.2 L with ⟨hosc', _⟩ | ⟨m', cm', fm', hq⟩
  · exact absurd (hosc' m) (not_lt.mpr fm)
  · have hmm : m' = m := first_unique P cm' fm' cm fm
    subst hmm
    have hd : DownC (fun j : ℕ => j < m') := fun j h => by omega
    have hi : Incr (orb P y) (fun j => j < m') := fun j h => cm' j (by omega)
    refine ⟨⟨orb P y n, hyB, ?_⟩, ?_⟩
    · rw [hq, den_true]
      exact (hi_iff hd hi hnm (le_refl _) (fun _ => cm' n (by omega))).mpr (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
      refine ⟨orb P y j, fun u hu => ?_⟩
      rw [hq, Bool.eq_false_iff]; intro hh
      have := (hi_iff hd hi (show j < j + 1 by omega) hu (fun h => absurd h (by omega))).mp
        (den_true.mp hh)
      omega

end loop

/-! ## 3. Quantitative: the unresolved window is at least exponential

Under a Lipschitz bound on the delay functions away from the domain edge
and a margin on the critical orbit, widths within `≈ λ^{-N}` of the
critical one still have `N + 1` uncancelled transitions, the `N`-th after
time `δ∞↑ + (N - 1/2)·g`. With `τ = g / ln λ` this is a window of half-width
`≥ const · e^{-T/τ}` of runt widths unresolved at time `T`: the same shape as
probe 7d's `e^{-T/τ_r}` law, here as a LOWER bound. -/

section quant
variable (P : InvolutionPair)

/-- Hypotheses of the quantitative bound. All are named; see the notes for
their physical reading and how to test them. -/
structure QuantHyp (c K M g : ℝ) : Prop where
  /-- **H_LIP**: the delay functions have slope at most `K` on `[-M, ∞)`
  (away from the domain edge, where `δ → -∞`). Test: slope of the measured
  pulse-shrink curve `Δ ↦ Δ'` of LUT + route. -/
  H_LIP : ∀ n a b, -M ≤ a → -M ≤ b → |P.delayAt n a - P.delayAt n b| ≤ K * |a - b|
  H_K : 0 ≤ K
  H_g : 0 < g
  /-- **H_MARGIN**: along the critical orbit every output pulse/gap is at
  least `g` (the critical orbit does not degenerate). -/
  H_MARGIN : ∀ n, g ≤ orb P c (n + 1) - orb P c n
  /-- **H_GAPMAX**: and at most `M - g`, so its delay arguments stay
  `g` inside the Lipschitz region. -/
  H_GAPMAX : ∀ n, orb P c (n + 1) - orb P c n ≤ M - g
  /-- **H_FIRST**: the first delay argument `c - δ∞↑` is in the region. -/
  H_FIRST : -M ≤ c - P.infUp

theorem orb_lin {c g : ℝ} (hm : ∀ n, g ≤ orb P c (n + 1) - orb P c n) :
    ∀ N : ℕ, orb P c 0 + N * g ≤ orb P c N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih => have := hm N; push_cast; linarith

/-- **Exponential window of slow resolution.** If `c` satisfies `QuantHyp`
and `2 (1+2K)^N (1+K) |Δ0 - c| < g` (with `Δ0 - δ∞↑ ≥ -M`), then the loop
for `Δ0` has no cancellation among its first `N + 2` output transitions and
the `N`-th comes after `δ∞↑ + N·g - g/2`. -/
theorem window_lower {c K M g Δ0 : ℝ} (H : QuantHyp P c K M g) (hΔ : -M ≤ Δ0 - P.infUp)
    (N : ℕ) (hN : 2 * ((1 + 2 * K) ^ N * ((1 + K) * |Δ0 - c|)) < g) :
    Δ0 ∈ chainS P (N + 1) ∧ P.infUp + N * g - g / 2 < orb P Δ0 N := by
  have hK := H.H_K
  set lam := 1 + 2 * K with hlam
  set A := (1 + K) * |Δ0 - c| with hA
  have hA0 : 0 ≤ A := mul_nonneg (by linarith) (abs_nonneg _)
  have hlam1 : 1 ≤ lam := by linarith
  have hpow : ∀ n, n ≤ N → lam ^ n * A ≤ lam ^ N * A := fun n hn =>
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlam1 hn) hA0
  set e : ℕ → ℝ := fun n => |orb P Δ0 n - orb P c n| with he
  have key : ∀ n, n ≤ N → e n ≤ lam ^ n * A ∧ e (n + 1) ≤ lam ^ n * A := by
    intro n
    induction n with
    | zero =>
      intro _
      simp only [pow_zero, one_mul]
      refine ⟨by simp [he, orb, hA0], ?_⟩
      show |(Δ0 + P.down (Δ0 - P.infUp)) - (c + P.down (c - P.infUp))| ≤ A
      have hl := H.H_LIP 1 (Δ0 - P.infUp) (c - P.infUp) hΔ H.H_FIRST
      rw [delayAt_odd P (by rfl), show Δ0 - P.infUp - (c - P.infUp) = Δ0 - c by ring] at hl
      calc |(Δ0 + P.down (Δ0 - P.infUp)) - (c + P.down (c - P.infUp))|
          = |(Δ0 - c) + (P.down (Δ0 - P.infUp) - P.down (c - P.infUp))| := by ring_nf
        _ ≤ |Δ0 - c| + |P.down (Δ0 - P.infUp) - P.down (c - P.infUp)| := abs_add_le _ _
        _ ≤ |Δ0 - c| + K * |Δ0 - c| := by linarith
        _ = A := by rw [hA]; ring
    | succ n ih =>
      intro hn
      obtain ⟨i0, i1⟩ := ih (by omega)
      have hb := hpow n (by omega)
      have hp : 0 ≤ lam ^ n * A := mul_nonneg (pow_nonneg (by linarith) n) hA0
      have hp2 := mul_le_mul_of_nonneg_left hlam1 hp
      refine ⟨le_trans i1 (by rw [pow_succ]; linarith), ?_⟩
      -- arguments of delayAt n
      set Ta := orb P Δ0 n - orb P Δ0 (n + 1) with hTa
      set Tc := orb P c n - orb P c (n + 1) with hTc
      have hgap := H.H_GAPMAX n
      have hdiff : |Ta - Tc| ≤ e n + e (n + 1) := by
        have : Ta - Tc = (orb P Δ0 n - orb P c n) - (orb P Δ0 (n + 1) - orb P c (n + 1)) := by
          rw [hTa, hTc]; ring
        rw [this]; exact abs_sub _ _
      have hTc' : -M + g ≤ Tc := by rw [hTc]; linarith
      have hTa' : -M ≤ Ta := by
        have := (abs_le.mp (le_trans hdiff (show e n + e (n+1) ≤ 2 * (lam ^ N * A) by
          linarith))).1
        linarith
      have hl := H.H_LIP n Ta Tc hTa' (by linarith [H.H_g])
      show |orb P Δ0 (n + 2) - orb P c (n + 2)| ≤ lam ^ (n + 1) * A
      rw [orb_ss, orb_ss, ← hTa, ← hTc]
      calc |orb P Δ0 n + P.delayAt n Ta - (orb P c n + P.delayAt n Tc)|
          = |(orb P Δ0 n - orb P c n) + (P.delayAt n Ta - P.delayAt n Tc)| := by ring_nf
        _ ≤ e n + |P.delayAt n Ta - P.delayAt n Tc| := abs_add_le _ _
        _ ≤ e n + K * (e n + e (n + 1)) := by
            have := mul_le_mul_of_nonneg_left hdiff hK; linarith
        _ ≤ lam ^ n * A + K * (lam ^ n * A + lam ^ n * A) := by
            have := mul_le_mul_of_nonneg_left (add_le_add i0 i1) hK; linarith
        _ = lam ^ (n + 1) * A := by rw [pow_succ, hlam]; ring
  refine ⟨fun j hj => ?_, ?_⟩
  · obtain ⟨i0, i1⟩ := key j (by omega)
    have hb := hpow j (by omega)
    have h1 := (abs_le.mp i0).2
    have h1' := (abs_le.mp i0).1
    have h2 := (abs_le.mp i1).1
    have hm := H.H_MARGIN j
    linarith
  · obtain ⟨i0, _⟩ := key N le_rfl
    have h1 := (abs_le.mp i0).1
    have hl := orb_lin P H.H_MARGIN N
    have e0 : orb P c 0 = P.infUp := rfl
    linarith

/-- Consistency of `H_MARGIN`/`H_GAPMAX`: for a SYMMETRIC channel
(`δ↑ = δ↓ = δ`) the gaps obey the one-dimensional map
`w ↦ -w + δ(-w)`, so if the first gap is a fixed point `w` (`δ(-w) = 2w`),
every gap is `w`: that width oscillates forever with pulses and gaps exactly
`w`, and satisfies the margin hypotheses with `g = w`, `M = 2w`. -/
theorem sym_const_gap (hsym : P.up = P.down) {Δ0 w : ℝ} (hw : P.up (-w) = 2 * w)
    (h1 : orb P Δ0 1 - orb P Δ0 0 = w) : ∀ n, orb P Δ0 (n + 1) - orb P Δ0 n = w := by
  have hdA : ∀ n, P.delayAt n = P.up := by
    intro n
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · exact delayAt_even P h
    · rw [delayAt_odd P h, hsym]
  intro n
  induction n with
  | zero => exact h1
  | succ n ih =>
    rw [orb_ss, hdA, show orb P Δ0 n - orb P Δ0 (n + 1) = -w by linarith, hw]
    linarith

end quant

end Formal.Cells.CElemInvolution
