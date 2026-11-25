import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Involution delay channels (Függer, Najvirt, Nowak, Schmid)

Track 3, delay channel (c).  Reference: M. Függer, R. Najvirt, T. Nowak,
U. Schmid, "Towards binary circuit models that faithfully capture physical
solvability", DATE 2015, and "A faithful binary circuit model", IEEE TCAD 2020
(arXiv 1406.2544 is the earlier "Faithful glitch propagation in binary circuit
models").

## The model

A channel has two delay functions `δ↑ = up`, `δ↓ = down`.  `T` is the time from
the *previous output* transition to the *current input* transition (so it may
be negative).  An input transition at time `t` whose previous tentative output
was at `o` schedules a tentative output at `t + δ(t - o)`.  If that is not after
`o`, both tentative transitions annihilate (the pulse is cancelled).  The first
transition sees `T = ∞` and gets the limit delay `δ∞`.

Every property used is a named field of `InvolutionPair` (nothing is assumed silently):
* `up : (-δ∞↓, ∞) → (-∞, δ∞↑)`, `down : (-δ∞↑, ∞) → (-∞, δ∞↓)`
  (fields `up_lt`, `down_lt`), strictly increasing (`*_strictMono`);
* the involution property `-δ↑(-δ↓ T) = T` and its mirror (`inv_up`, `inv_down`);
* strict causality `δ↑(0) > 0`, `δ↓(0) > 0`.
The paper also requires continuity, concavity and `lim_{T→∞} δ = δ∞`; none of the
results in this file needs them.  The paper derives the existence of the
fixed point `δmin` from continuity (IVT); here `IsDMin d` is a hypothesis
(everything else about `δmin` is proved: it is unique, positive, shared by both
directions, and it is the exact cancellation threshold).

## Main results
* `IsDMin.up_fix`, `IsDMin.unique`, `IsDMin.pos`: δ↑(-δmin) = δmin = δ↓(-δmin).
* `tent_le`, `dom_ok`: the channel semantics is well defined on any strictly
  increasing input sequence (every `T` lies in the delay function's domain).
* `cancel_iff`: transition `n+1` cancels against `n` iff `t(n+1) - o(n) ≤ -δmin`.
* `pulse_cancel_iff`: a single isolated input pulse of width `Δ` is cancelled iff
  `Δ ≤ δ∞↑ - δmin`.
* `pulseWidth_strictMono`, `pulseWidth_small`: the output pulse width is strictly
  increasing in `Δ` and tends to `0` as `Δ ↓ δ∞↑ - δmin`: there are arbitrarily
  short output pulses.  This is the property that makes the model faithful
  (bounded short-pulse filtration is unsolvable), contrasted with
  `inertial_gap`: an inertial channel has no output pulse narrower than its delay.
* `pulseWidth_lt`: long pulses change width by less than `δ∞↓ - δ∞↑`.
* `up_bounds`, `down_bounds`: under an input-separation hypothesis an involution
  channel is a bounded pure delay `[δ(T0), δ∞)`.
* `ExpLog`, `expPair`, `exp_dmin`, `exp_pulse_cancel_iff`: the exp-channel
  `δ(T) = T_p + τ·ln(2 - e^{-(T+T_p)/τ})` (first-order RC + pure delay `T_p`,
  threshold 1/2; derived here from the RC trajectory, the papers were not
  reachable from this sandbox to compare symbols) is an involution pair with
  `δmin = T_p`; it cancels a pulse iff
  `Δ ≤ τ ln 2`.  `exp`/`log` are abstracted as `ExpLog` (scaled by `τ`), because
  `Mathlib.Analysis.SpecialFunctions.Log.Basic` is not built here; the real
  instance is in `Wip/DelayInvolution.lean`.
-/

namespace Formal.Core.DelayInvolution

/-- A pair of involution delay functions, every property a named hypothesis. -/
structure InvolutionPair where
  up : ℝ → ℝ
  down : ℝ → ℝ
  /-- `δ∞↑`, the rising delay after a long quiet period. -/
  infUp : ℝ
  /-- `δ∞↓`. -/
  infDown : ℝ
  infUp_pos : 0 < infUp
  infDown_pos : 0 < infDown
  up_lt : ∀ T, -infDown < T → up T < infUp
  down_lt : ∀ T, -infUp < T → down T < infDown
  up_strictMono : ∀ a b, -infDown < a → a < b → up a < up b
  down_strictMono : ∀ a b, -infUp < a → a < b → down a < down b
  inv_up : ∀ T, -infUp < T → -up (-down T) = T
  inv_down : ∀ T, -infDown < T → -down (-up T) = T
  up_causal : 0 < up 0
  down_causal : 0 < down 0

namespace InvolutionPair

variable (P : InvolutionPair)

theorem up_neg_down {T : ℝ} (hT : -P.infUp < T) : P.up (-P.down T) = -T := by
  have := P.inv_up T hT; linarith

theorem down_neg_up {T : ℝ} (hT : -P.infDown < T) : P.down (-P.up T) = -T := by
  have := P.inv_down T hT; linarith

theorem neg_down_mem {T : ℝ} (hT : -P.infUp < T) : -P.infDown < -P.down T := by
  have := P.down_lt T hT; linarith

theorem neg_up_mem {T : ℝ} (hT : -P.infDown < T) : -P.infUp < -P.up T := by
  have := P.up_lt T hT; linarith

/-- `δ↓` attains every value below `δ∞↓`, at an explicit point (from the involution). -/
theorem down_surj {v : ℝ} (hv : v < P.infDown) :
    -P.infUp < -P.up (-v) ∧ P.down (-P.up (-v)) = v := by
  have h : -P.infDown < -v := by linarith
  refine ⟨P.neg_up_mem h, ?_⟩
  have := P.down_neg_up h; linarith

/-- `δ↑` attains every value below `δ∞↑`. -/
theorem up_surj {v : ℝ} (hv : v < P.infUp) :
    -P.infDown < -P.down (-v) ∧ P.up (-P.down (-v)) = v := by
  have h : -P.infUp < -v := by linarith
  refine ⟨P.neg_down_mem h, ?_⟩
  have := P.up_neg_down h; linarith

theorem down_lt_iff {a b : ℝ} (ha : -P.infUp < a) (hb : -P.infUp < b) :
    P.down a < P.down b ↔ a < b := by
  constructor
  · intro h
    rcases lt_or_ge a b with hab | hab
    · exact hab
    · exfalso
      rcases lt_or_eq_of_le hab with hab | hab
      · have := P.down_strictMono b a hb hab; linarith
      · rw [hab] at h; exact lt_irrefl _ h
  · intro h; exact P.down_strictMono a b ha h

theorem up_lt_iff {a b : ℝ} (ha : -P.infDown < a) (hb : -P.infDown < b) :
    P.up a < P.up b ↔ a < b := by
  constructor
  · intro h
    rcases lt_or_ge a b with hab | hab
    · exact hab
    · exfalso
      rcases lt_or_eq_of_le hab with hab | hab
      · have := P.up_strictMono b a hb hab; linarith
      · rw [hab] at h; exact lt_irrefl _ h
  · intro h; exact P.up_strictMono a b ha h

/-- The composed map `T ↦ -δ↑(-δ↓ T)` is the identity, hence strictly increasing;
and `T ↦ -δ↓ T` is strictly *decreasing* from the `δ↓` domain into the `δ↑` domain. -/
theorem neg_down_strictAnti {a b : ℝ} (ha : -P.infUp < a) (hab : a < b) :
    -P.down b < -P.down a := by
  have := P.down_strictMono a b ha hab; linarith

/-! ### δmin -/

/-- `d` is δmin: the fixed point `δ↓(-d) = d`.  Existence is a hypothesis (IVT in
the paper, from continuity). -/
structure IsDMin (d : ℝ) : Prop where
  mem : -P.infUp < -d
  fix : P.down (-d) = d

variable {P}

theorem IsDMin.up_fix {d : ℝ} (h : P.IsDMin d) : P.up (-d) = d := by
  have := P.up_neg_down h.mem
  rw [h.fix] at this; linarith

theorem IsDMin.lt_infDown {d : ℝ} (h : P.IsDMin d) : d < P.infDown := by
  have := P.down_lt _ h.mem; rw [h.fix] at this; exact this

theorem IsDMin.mem_up {d : ℝ} (h : P.IsDMin d) : -P.infDown < -d := by
  have := h.lt_infDown; linarith

theorem IsDMin.lt_infUp {d : ℝ} (h : P.IsDMin d) : d < P.infUp := by
  have := h.mem; linarith

theorem IsDMin.pos {d : ℝ} (h : P.IsDMin d) : 0 < d := by
  rcases lt_or_ge 0 d with hd | hd
  · exact hd
  · exfalso
    rcases lt_or_eq_of_le hd with hd | hd
    · have h0 : -P.infUp < (0 : ℝ) := by linarith [P.infUp_pos]
      have := P.down_strictMono 0 (-d) h0 (by linarith)
      rw [h.fix] at this; linarith [P.down_causal]
    · have := h.fix
      subst hd
      rw [neg_zero] at this; linarith [P.down_causal]

theorem IsDMin.unique {d e : ℝ} (hd : P.IsDMin d) (he : P.IsDMin e) : d = e := by
  rcases lt_trichotomy d e with h | h | h
  · have := P.down_strictMono (-e) (-d) he.mem (by linarith)
    rw [hd.fix, he.fix] at this; linarith
  · exact h
  · have := P.down_strictMono (-d) (-e) hd.mem (by linarith)
    rw [hd.fix, he.fix] at this; linarith

/-- δmin lies strictly below both zero-gap delays: `δmin < δ↓(0)`, `δmin < δ↑(0)`. -/
theorem IsDMin.lt_down_zero {d : ℝ} (h : P.IsDMin d) : d < P.down 0 := by
  have := P.down_strictMono (-d) 0 h.mem (by linarith [h.pos])
  rw [h.fix] at this; exact this

theorem IsDMin.lt_up_zero {d : ℝ} (h : P.IsDMin d) : d < P.up 0 := by
  have := P.up_strictMono (-d) 0 h.mem_up (by linarith [h.pos])
  rw [h.up_fix] at this; exact this

variable (P)

/-! ### The gap map `T ↦ T + δ(T)` -/

/-- Separation between a new tentative output and the previous one. -/
def gapUp (T : ℝ) : ℝ := T + P.up T
def gapDown (T : ℝ) : ℝ := T + P.down T

theorem gapUp_strictMono {a b : ℝ} (ha : -P.infDown < a) (hab : a < b) :
    P.gapUp a < P.gapUp b := by
  unfold gapUp; have := P.up_strictMono a b ha hab; linarith

theorem gapDown_strictMono {a b : ℝ} (ha : -P.infUp < a) (hab : a < b) :
    P.gapDown a < P.gapDown b := by
  unfold gapDown; have := P.down_strictMono a b ha hab; linarith

variable {P}

theorem gapDown_nonpos_iff {d : ℝ} (h : P.IsDMin d) {T : ℝ} (hT : -P.infUp < T) :
    P.gapDown T ≤ 0 ↔ T ≤ -d := by
  have h0 : P.gapDown (-d) = 0 := by unfold gapDown; rw [h.fix]; ring1
  constructor
  · intro hg
    rcases lt_or_ge (-d) T with hc | hc
    · have := P.gapDown_strictMono h.mem hc; linarith
    · exact hc
  · intro hc
    rcases lt_or_eq_of_le hc with hc | hc
    · have := P.gapDown_strictMono hT hc; linarith
    · rw [hc, h0]

theorem gapUp_nonpos_iff {d : ℝ} (h : P.IsDMin d) {T : ℝ} (hT : -P.infDown < T) :
    P.gapUp T ≤ 0 ↔ T ≤ -d := by
  have h0 : P.gapUp (-d) = 0 := by unfold gapUp; rw [h.up_fix]; ring1
  constructor
  · intro hg
    rcases lt_or_ge (-d) T with hc | hc
    · have := P.gapUp_strictMono h.mem_up hc; linarith
    · exact hc
  · intro hc
    rcases lt_or_eq_of_le hc with hc | hc
    · have := P.gapUp_strictMono hT hc; linarith
    · rw [hc, h0]

variable (P)

/-! ### Channel semantics on an input transition sequence

Input transitions at strictly increasing times `t 0 < t 1 < ...`; the input starts
at 0, so transition `n` is rising iff `n` is even.  `tent t n` is the tentative
output time of transition `n` (the paper computes `T` against the previous
tentative output whether or not it is later cancelled). -/

def delayAt (n : ℕ) : ℝ → ℝ := if n % 2 = 0 then P.up else P.down
def infAt (n : ℕ) : ℝ := if n % 2 = 0 then P.infUp else P.infDown

def tent (t : ℕ → ℝ) : ℕ → ℝ
  | 0 => t 0 + P.infUp
  | n + 1 => t (n + 1) + P.delayAt (n + 1) (t (n + 1) - tent t n)

theorem delayAt_succ_lt (n : ℕ) {T : ℝ} (hT : -P.infAt n < T) :
    P.delayAt (n + 1) T < P.infAt (n + 1) := by
  unfold delayAt infAt at *
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [ite_eq_left h] at hT
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    exact P.down_lt T hT
  · rw [ite_eq_right (by omega)] at hT
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    exact P.up_lt T hT

theorem tent_le (t : ℕ → ℝ) (ht : ∀ n, t n < t (n + 1)) (n : ℕ) :
    P.tent t n ≤ t n + P.infAt n := by
  induction n with
  | zero => simp [tent, infAt]
  | succ n ih =>
    have hT : -P.infAt n < t (n + 1) - P.tent t n := by linarith [ht n]
    have := P.delayAt_succ_lt n hT
    show t (n + 1) + P.delayAt (n + 1) (t (n + 1) - P.tent t n) ≤ t (n + 1) + P.infAt (n + 1)
    linarith

/-- Well-definedness: every `T` fed to a delay function lies in its domain. -/
theorem dom_ok (t : ℕ → ℝ) (ht : ∀ n, t n < t (n + 1)) (n : ℕ) :
    -P.infAt n < t (n + 1) - P.tent t n := by
  linarith [P.tent_le t ht n, ht n]

variable {P}

/-- Local cancellation rule: tentative output `n+1` is not after output `n`
(so both annihilate) iff the input came less than `δmin` before... precisely iff
`t(n+1) - o(n) ≤ -δmin`.  The same threshold serves both directions. -/
theorem cancel_iff {d : ℝ} (h : P.IsDMin d) (t : ℕ → ℝ) (ht : ∀ n, t n < t (n + 1)) (n : ℕ) :
    P.tent t (n + 1) ≤ P.tent t n ↔ t (n + 1) - P.tent t n ≤ -d := by
  have hT := P.dom_ok t ht n
  have e : P.tent t (n + 1) - P.tent t n
      = (t (n + 1) - P.tent t n) + P.delayAt (n + 1) (t (n + 1) - P.tent t n) := by
    show t (n + 1) + P.delayAt (n + 1) (t (n + 1) - P.tent t n) - P.tent t n = _
    ring1
  have key : (t (n + 1) - P.tent t n) + P.delayAt (n + 1) (t (n + 1) - P.tent t n) ≤ 0
      ↔ t (n + 1) - P.tent t n ≤ -d := by
    unfold delayAt infAt at *
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · rw [ite_eq_left hn] at hT
      rw [ite_eq_right (by omega)]
      exact gapDown_nonpos_iff h hT
    · rw [ite_eq_right (by omega)] at hT
      rw [ite_eq_left (by omega)]
      exact gapUp_nonpos_iff h hT
  constructor
  · intro hc; exact key.mp (by linarith)
  · intro hc; have := key.mpr hc; linarith

/-! ### A single isolated pulse -/

variable (P)

/-- Output width for an isolated input pulse `0 ↑ ... Δ ↓`. -/
def pulseWidth (Δ : ℝ) : ℝ := (Δ - P.infUp) + P.down (Δ - P.infUp)

theorem pulseWidth_eq (t : ℕ → ℝ) (Δ : ℝ) (h0 : t 0 = 0) (h1 : t 1 = Δ) :
    P.tent t 1 - P.tent t 0 = P.pulseWidth Δ := by
  have hd : P.delayAt 1 = P.down := by simp [delayAt]
  simp only [tent, hd, h0, h1, pulseWidth, zero_add]
  ring1

variable {P}

/-- A pulse of width `Δ > 0` is cancelled iff `Δ ≤ δ∞↑ - δmin`. -/
theorem pulse_cancel_iff {d : ℝ} (h : P.IsDMin d) {Δ : ℝ} (hΔ : 0 < Δ) :
    P.pulseWidth Δ ≤ 0 ↔ Δ ≤ P.infUp - d := by
  have hT : -P.infUp < Δ - P.infUp := by linarith
  have := gapDown_nonpos_iff h hT
  unfold gapDown at this
  unfold pulseWidth
  rw [this]
  constructor <;> intro hc <;> linarith

theorem pulseWidth_strictMono {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    P.pulseWidth a < P.pulseWidth b := by
  have := P.gapDown_strictMono (a := a - P.infUp) (b := b - P.infUp) (by linarith) (by linarith)
  unfold gapDown at this; unfold pulseWidth; exact this

/-- Output pulses shrink continuously to zero at the cancellation threshold:
for every `ε > 0`, inputs just above `δ∞↑ - δmin` give outputs in `(0, ε)`. -/
theorem pulseWidth_small {d : ℝ} (h : P.IsDMin d) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ Δ, P.infUp - d < Δ → Δ < P.infUp - d + η →
      0 < P.pulseWidth Δ ∧ P.pulseWidth Δ < ε := by
  have hdD := h.lt_infDown
  have hdpos := h.pos
  set m := min (ε / 2) ((P.infDown - d) / 2) with hm
  have hm1 : m ≤ ε / 2 := min_le_left _ _
  have hm2 : m ≤ (P.infDown - d) / 2 := min_le_right _ _
  have hmpos : 0 < m := lt_min (by linarith) (by linarith)
  set v := d + m with hv
  have hvlt : v < P.infDown := by linarith
  obtain ⟨hT1, hdT1⟩ := P.down_surj hvlt
  set T1 := -P.up (-v) with hT1def
  -- T1 > -d because δ↓(T1) = v > d = δ↓(-d)
  have hT1gt : -d < T1 := by
    have : P.down (-d) < P.down T1 := by rw [h.fix, hdT1]; linarith
    exact (P.down_lt_iff h.mem hT1).mp this
  refine ⟨min (ε / 2) (T1 + d), lt_min (by linarith) (by linarith), ?_⟩
  intro Δ hlo hhi
  have hη1 : min (ε / 2) (T1 + d) ≤ ε / 2 := min_le_left _ _
  have hη2 : min (ε / 2) (T1 + d) ≤ T1 + d := min_le_right _ _
  have hΔpos : 0 < Δ := by linarith [h.lt_infUp]
  refine ⟨?_, ?_⟩
  · rcases lt_or_ge 0 (P.pulseWidth Δ) with hp | hp
    · exact hp
    · exfalso; have := (pulse_cancel_iff h hΔpos).mp hp; linarith
  · have hT : -P.infUp < Δ - P.infUp := by linarith
    have hlt : P.down (Δ - P.infUp) < P.down T1 :=
      P.down_strictMono _ _ hT (by linarith)
    rw [hdT1] at hlt
    unfold pulseWidth
    linarith

variable (P)

/-- Long pulses: the output is narrower than `Δ + (δ∞↓ - δ∞↑)`; the asymmetry
`δ∞↓ - δ∞↑` is the per-stage stretch (or shrink) of a long positive pulse. -/
theorem pulseWidth_lt (Δ : ℝ) (hΔ : 0 < Δ) :
    P.pulseWidth Δ < Δ + (P.infDown - P.infUp) := by
  have := P.down_lt (Δ - P.infUp) (by linarith)
  unfold pulseWidth; linarith

/-- Refinement to bounded pure delay: if every input transition comes at least
`T0` after the previous output (an environment separation hypothesis), every
rising delay lies in `[δ↑(T0), δ∞↑)`.  So bounded-delay proofs apply verbatim
to involution channels under a separation hypothesis. -/
theorem up_bounds {T0 T : ℝ} (h0 : -P.infDown < T0) (hT : T0 ≤ T) :
    P.up T0 ≤ P.up T ∧ P.up T < P.infUp := by
  refine ⟨?_, P.up_lt T (by linarith)⟩
  rcases lt_or_eq_of_le hT with h | h
  · exact le_of_lt (P.up_strictMono _ _ h0 h)
  · rw [h]

theorem down_bounds {T0 T : ℝ} (h0 : -P.infUp < T0) (hT : T0 ≤ T) :
    P.down T0 ≤ P.down T ∧ P.down T < P.infDown := by
  refine ⟨?_, P.down_lt T (by linarith)⟩
  rcases lt_or_eq_of_le hT with h | h
  · exact le_of_lt (P.down_strictMono _ _ h0 h)
  · rw [h]

/-! ### Contrast: inertial delay has a width gap -/

/-- Inertial channel of delay `D`: pulses narrower than `D` vanish, others pass. -/
noncomputable def inertialWidth (D Δ : ℝ) : ℝ := if Δ < D then 0 else Δ

/-- An inertial channel never emits a pulse of width in `(0, D)`: this gap is what
lets bounded short-pulse filtration be "solved" in the inertial model, which is
physically impossible (Marino); the involution model has no gap (`pulseWidth_small`). -/
theorem inertial_gap (D Δ : ℝ) : inertialWidth D Δ = 0 ∨ D ≤ inertialWidth D Δ := by
  unfold inertialWidth
  by_cases hΔ : Δ < D
  · left; rw [ite_eq_left hΔ]
  · right; rw [ite_eq_right hΔ]; linarith

end InvolutionPair

/-! ## The exp-channel

`exp` and `log` are taken as abstract functions with the defining properties
(named hypotheses), already scaled by `τ`: intended `E x = e^{x/τ}`,
`L y = τ·ln y`.  Then `δ(T) = T_p + L(2 - E(-(T + T_p)))` is
`T_p + τ ln(2 - e^{-(T+T_p)/τ})`: pure delay `T_p` followed by a first-order RC
stage with threshold 1/2 that starts from the level the previous opposite
transition left it at.  `δ∞ = T_p + τ ln 2`. -/

structure ExpLog where
  E : ℝ → ℝ
  L : ℝ → ℝ
  E_pos : ∀ x, 0 < E x
  E_strictMono : ∀ a b, a < b → E a < E b
  E_zero : E 0 = 1
  L_E : ∀ x, L (E x) = x
  E_L : ∀ y, 0 < y → E (L y) = y

namespace ExpLog

variable (X : ExpLog)

theorem L_one : X.L 1 = 0 := by
  have := X.L_E 0; rwa [X.E_zero] at this

theorem L_strictMono {a b : ℝ} (ha : 0 < a) (hab : a < b) : X.L a < X.L b := by
  rcases lt_or_ge (X.L a) (X.L b) with h | h
  · exact h
  · exfalso
    rcases lt_or_eq_of_le h with h | h
    · have := X.E_strictMono _ _ h
      rw [X.E_L a ha, X.E_L b (by linarith)] at this; linarith
    · have := congrArg X.E h
      rw [X.E_L a ha, X.E_L b (by linarith)] at this; linarith

theorem L_pos {y : ℝ} (hy : 1 < y) : 0 < X.L y := by
  have := X.L_strictMono one_pos hy; rwa [X.L_one] at this

/-- The exp-channel delay function. -/
def expDelay (Tp T : ℝ) : ℝ := Tp + X.L (2 - X.E (-(T + Tp)))

/-- `δ∞ = T_p + τ ln 2`. -/
def expInf (Tp : ℝ) : ℝ := Tp + X.L 2

theorem exp_dom (Tp : ℝ) {T : ℝ} (hT : -X.expInf Tp < T) : 0 < 2 - X.E (-(T + Tp)) := by
  unfold expInf at hT
  have h1 : -(T + Tp) < X.L 2 := by linarith
  have := X.E_strictMono _ _ h1
  rw [X.E_L 2 (by norm_num)] at this
  linarith

theorem exp_lt (Tp : ℝ) {T : ℝ} (hT : -X.expInf Tp < T) : X.expDelay Tp T < X.expInf Tp := by
  have hd := X.exp_dom Tp hT
  unfold expDelay expInf
  have := X.L_strictMono hd
    (show 2 - X.E (-(T + Tp)) < 2 by linarith [X.E_pos (-(T + Tp))])
  linarith

theorem exp_strictMono (Tp : ℝ) {a b : ℝ} (ha : -X.expInf Tp < a) (hab : a < b) :
    X.expDelay Tp a < X.expDelay Tp b := by
  have hd := X.exp_dom Tp ha
  have hE := X.E_strictMono (-(b + Tp)) (-(a + Tp)) (by linarith)
  unfold expDelay
  have := X.L_strictMono hd (show 2 - X.E (-(a + Tp)) < 2 - X.E (-(b + Tp)) by linarith)
  linarith

/-- The involution property of the exp-channel. -/
theorem exp_inv (Tp : ℝ) {T : ℝ} (hT : -X.expInf Tp < T) :
    -X.expDelay Tp (-X.expDelay Tp T) = T := by
  have hpos := X.exp_dom Tp hT
  unfold expDelay
  have h1 : -(-(Tp + X.L (2 - X.E (-(T + Tp)))) + Tp) = X.L (2 - X.E (-(T + Tp))) := by ring1
  rw [h1, X.E_L _ hpos, sub_sub_cancel, X.L_E]
  ring1

theorem exp_causal (Tp : ℝ) (hTp : 0 < Tp) : 0 < X.expDelay Tp 0 := by
  unfold expDelay
  have hE := X.E_strictMono (-(0 + Tp)) 0 (by linarith)
  rw [X.E_zero] at hE
  have := X.L_pos (show 1 < 2 - X.E (-(0 + Tp)) by linarith)
  linarith

theorem expInf_pos (Tp : ℝ) (hTp : 0 < Tp) : 0 < X.expInf Tp := by
  unfold expInf; have := X.L_pos (show (1 : ℝ) < 2 by norm_num); linarith

/-- The symmetric exp-channel as an involution pair (`δ↑ = δ↓`). -/
def expPair (Tp : ℝ) (hTp : 0 < Tp) : InvolutionPair where
  up := X.expDelay Tp
  down := X.expDelay Tp
  infUp := X.expInf Tp
  infDown := X.expInf Tp
  infUp_pos := X.expInf_pos Tp hTp
  infDown_pos := X.expInf_pos Tp hTp
  up_lt := fun _ hT => X.exp_lt Tp hT
  down_lt := fun _ hT => X.exp_lt Tp hT
  up_strictMono := fun _ _ ha hab => X.exp_strictMono Tp ha hab
  down_strictMono := fun _ _ ha hab => X.exp_strictMono Tp ha hab
  inv_up := fun _ hT => X.exp_inv Tp hT
  inv_down := fun _ hT => X.exp_inv Tp hT
  up_causal := X.exp_causal Tp hTp
  down_causal := X.exp_causal Tp hTp

/-- For the exp-channel, `δmin = T_p`. -/
theorem exp_dmin (Tp : ℝ) (hTp : 0 < Tp) : (X.expPair Tp hTp).IsDMin Tp where
  mem := by
    show -(Tp + X.L 2) < -Tp
    have := X.L_pos (show (1 : ℝ) < 2 by norm_num); linarith
  fix := by
    show Tp + X.L (2 - X.E (-(-Tp + Tp))) = Tp
    rw [show -(-Tp + Tp) = (0 : ℝ) by ring1, X.E_zero, show (2 : ℝ) - 1 = 1 by norm_num,
      X.L_one]
    ring1

/-- The exp-channel cancels an isolated pulse iff `Δ ≤ τ ln 2` (here `L 2`). -/
theorem exp_pulse_cancel_iff (Tp : ℝ) (hTp : 0 < Tp) {Δ : ℝ} (hΔ : 0 < Δ) :
    (X.expPair Tp hTp).pulseWidth Δ ≤ 0 ↔ Δ ≤ X.L 2 := by
  rw [InvolutionPair.pulse_cancel_iff (X.exp_dmin Tp hTp) hΔ]
  show Δ ≤ Tp + X.L 2 - Tp ↔ Δ ≤ X.L 2
  constructor <;> intro h <;> linarith

end ExpLog

end Formal.Core.DelayInvolution
