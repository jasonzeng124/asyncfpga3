import Formal.Core.Trace.Discrete

/-!
# The GLS's "sample at fire" (SAF) delay channel, discrete time

`formal/notes/A-gls-compare.md` found that the research branch's GLS LUT
(an iverilog specify path) is neither transport nor inertial. Every change of
the LUT's zero-time function value `x` at step `u` schedules an update at
`u + d`. When the update fires it copies the value `x` has *just before* the
fire instant (`x (u + d - 1)` at 1 ps resolution), and nothing is ever
cancelled.

Time is `ℕ` (one step = 1 ps), signals are `Formal.Core.TraceDiscrete.Sig`
(`ℕ → Bool`), constant before time 0. A change "at step `k+1`" is
`Tr x k` (`x (k+1) ≠ x k`).

Modelling choice (stated once): an update firing at step `F` copies `x (F-1)`,
the value just before `F`, i.e. a same-instant input change loses the race.
This is the reading that reproduces the GLS's measured tie behaviour (a pulse of
width exactly `d` passes, A-gls-compare §2) and the 1000/1120 example of §1.
With the other tie order (`x F`), every statement below holds with `d`
replaced by `d + 1` in the thresholds.

Results (names in the notes `formal/notes/A-delay-saf.md`):
1. `saf_eq_delay_iff`, `saf_eq_delay_of_spaced`: SAF = pure delay `d` exactly
   when every fire copies the value its own change set; in particular when the
   input never changes twice within `d` steps.
2. `saf_pulse_short`, `saf_pulse_long`, `saf_pulse_eq_inertial`: on an
   isolated pulse SAF is the inertial delay (pulses `< d` vanish).
3. `saf_early`, `saf_runt`, `saf_runt_not_inertial`: early propagation with any
   latency `ε ∈ [1, d)`, and output runts of every width `1 .. d-2`.
4. `saf_transport` (SAF ⊆ transport `[1, d]`), `saf_window`, and
   `saf_not_transport` (SAF ⊄ transport `[lo, hi]` for `lo ≥ 2`, `hi ≤ 2d-2`):
   the GLS per-LUT delay is an upper bound only; its lower bound is one step.
5. Settle times: `settle_of_transport`, `saf_settle_le_delay`,
   `chain_settle_le_delay`, `chain_settle_static`, `chain_early`,
   `xor_settle_late`, `chain_eq_delay_of_faithful`.
-/

namespace Formal.Core.DelaySAF

open Formal.Core.TraceDiscrete

/-! ## The channel -/

/-- An update fires entering step `t+1`: the input changed entering step
`t+1-d` (so `d ≤ t`). -/
def fireB (d : Nat) (x : Sig) (t : Nat) : Bool :=
  decide (d ≤ t) && (x (t - d + 1) != x (t - d))

theorem fireB_true {d : Nat} {x : Sig} {t : Nat} :
    fireB d x t = true ↔ d ≤ t ∧ x (t - d + 1) ≠ x (t - d) := by
  simp [fireB]

/-- The sample-at-fire channel with delay `d`: the output starts at `x 0` and
changes only at fire steps, where it copies the input value just before the
fire step. -/
def saf (d : Nat) (x : Sig) : Sig
  | 0 => x 0
  | t + 1 => if fireB d x t then x t else saf d x t

theorem saf_zero (d : Nat) (x : Sig) : saf d x 0 = x 0 := rfl

theorem saf_succ (d : Nat) (x : Sig) (t : Nat) :
    saf d x (t + 1) = if fireB d x t then x t else saf d x t := rfl

/-! ## 1. When SAF is pure delay -/

/-- Every fire copies the value its own change set: for a change entering step
`k+1`, the input still has that value at step `k+d` (just before its fire). -/
def Faithful (d : Nat) (x : Sig) : Prop :=
  ∀ k, x (k + 1) ≠ x k → x (k + d) = x (k + 1)

/-- No two input changes closer than `d` steps. -/
def Spaced (d : Nat) (x : Sig) : Prop :=
  ∀ k k', x (k + 1) ≠ x k → x (k' + 1) ≠ x k' → k < k' → d ≤ k' - k

/-- Exact characterization: SAF is the pure delay `d` iff every fire is
faithful. -/
theorem saf_eq_delay_iff {d : Nat} {x : Sig} : saf d x = delay d x ↔ Faithful d x := by
  constructor
  · intro h k hk
    have e := congrFun h (k + d + 1)
    have hf : fireB d x (k + d) = true :=
      fireB_true.2 ⟨by omega, by rw [show k + d - d = k by omega]; exact hk⟩
    rw [saf_succ] at e
    simp only [hf, ↓reduceIte] at e
    simp only [delay] at e
    rw [e, show k + d + 1 - d = k + 1 by omega]
  · intro h
    funext t
    induction t with
    | zero => simp [saf_zero, delay]
    | succ t ih =>
      rw [saf_succ]
      simp only [delay] at ih ⊢
      split
      · rename_i hf
        obtain ⟨h1, h2⟩ := fireB_true.1 hf
        have e := h (t - d) h2
        rw [show t - d + d = t by omega] at e
        rw [e, show t + 1 - d = t - d + 1 by omega]
      · rename_i hf
        rw [ih]
        by_cases h1 : d ≤ t
        · rw [show t + 1 - d = t - d + 1 by omega]
          by_cases h2 : x (t - d + 1) = x (t - d)
          · exact h2.symm
          · exact absurd (fireB_true.2 ⟨h1, h2⟩) hf
        · rw [show t + 1 - d = 0 by omega, show t - d = 0 by omega]

theorem faithful_of_spaced {d : Nat} {x : Sig} (hd : 1 ≤ d) (h : Spaced d x) :
    Faithful d x := by
  intro k hk
  by_cases e : x (k + d) = x (k + 1)
  · exact e
  · obtain ⟨u, h1, h2, h3⟩ := exists_tr x (k + 1) (k + d) (by omega) (fun e' => e e'.symm)
    have := h k u hk h3 (by omega)
    omega

/-- (1) Bridge: on stimuli whose changes are at least `d` apart the GLS's SAF
LUT is exactly the pure delay `d`. -/
theorem saf_eq_delay_of_spaced {d : Nat} {x : Sig} (hd : 1 ≤ d) (h : Spaced d x) :
    saf d x = delay d x :=
  saf_eq_delay_iff.2 (faithful_of_spaced hd h)


/-! ## 4. SAF is a bounded transport channel with band `[1, d]` -/

/-- The read-time of SAF: the step whose input value the output shows. -/
def gsaf (d : Nat) (x : Sig) : Nat → Nat
  | 0 => 0
  | t + 1 => if fireB d x t then t else max (gsaf d x t) (t + 1 - d)

theorem gsaf_spec {d : Nat} {x : Sig} (hd : 1 ≤ d) :
    ∀ t, t - d ≤ gsaf d x t ∧ gsaf d x t ≤ t - 1 ∧ saf d x t = x (gsaf d x t) := by
  intro t
  induction t with
  | zero => exact ⟨by omega, by simp [gsaf], rfl⟩
  | succ t ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    simp only [gsaf, saf_succ]
    split
    · exact ⟨by omega, by omega, rfl⟩
    · rename_i hf
      refine ⟨by omega, by omega, ?_⟩
      rw [i3]
      by_cases hc : t + 1 - d ≤ gsaf d x t
      · rw [Nat.max_eq_left hc]
      · rw [Nat.max_eq_right (by omega)]
        have hdt : d ≤ t := by omega
        have hg : gsaf d x t = t - d := by omega
        rw [hg, show t + 1 - d = t - d + 1 by omega]
        by_cases h2 : x (t - d + 1) = x (t - d)
        · exact h2.symm
        · exact absurd (fireB_true.2 ⟨hdt, h2⟩) hf

theorem mono_of_step {f : Nat → Nat} (h : ∀ t, f t ≤ f (t + 1)) : Mono f := by
  intro a b hab
  induction b with
  | zero => rw [show a = 0 by omega]; exact Nat.le_refl _
  | succ b ih =>
    by_cases hb : a ≤ b
    · exact Nat.le_trans (ih hb) (h b)
    · rw [show a = b + 1 by omega]; exact Nat.le_refl _

theorem gsaf_mono {d : Nat} {x : Sig} (hd : 1 ≤ d) : Mono (gsaf d x) := by
  apply mono_of_step
  intro t
  have := (gsaf_spec (x := x) hd t).2.1
  simp only [gsaf]
  split
  · omega
  · exact Nat.le_max_left _ _

/-- (4) SAF is contained in the sound bounded transport channel with band
`[1, d]`: lower bound one step (the time quantum), upper bound `d`. -/
theorem saf_transport {d : Nat} (x : Sig) (hd : 1 ≤ d) : Transport 1 d x (saf d x) :=
  ⟨gsaf d x, ⟨gsaf_mono hd, fun t => (gsaf_spec hd t).2.1, fun t => (gsaf_spec hd t).1⟩,
    fun t => (gsaf_spec hd t).2.2⟩

/-- (4) Window form: the output at `t` is the input at some step in
`[t-d, t-1]` (truncated at 0). -/
theorem saf_window {d : Nat} (x : Sig) (hd : 1 ≤ d) (t : Nat) :
    ∃ u, t - d ≤ u ∧ u ≤ t - 1 ∧ saf d x t = x u :=
  ⟨gsaf d x t, gsaf_spec hd t⟩


/-! ## 2. Isolated pulses: SAF is inertial -/

theorem pulse_tr {a : Bool} {p w k : Nat} (h : pulse a p w (k + 1) ≠ pulse a p w k) :
    k + 1 = p ∨ k + 1 = p + w := by
  simp only [pulse] at h
  by_cases c1 : p ≤ k + 1 ∧ k + 1 < p + w <;> by_cases c2 : p ≤ k ∧ k < p + w <;>
    simp only [c1, c2, if_true, if_false] at h <;> first | omega | exact absurd rfl h

theorem pulse_spaced {a : Bool} {p w d : Nat} (hw : d ≤ w) : Spaced d (pulse a p w) := by
  intro k k' hk hk' hlt
  rcases pulse_tr hk with h1 | h1 <;> rcases pulse_tr hk' with h2 | h2 <;> omega

theorem delay_pulse {a : Bool} {p w d : Nat} (hp : 1 ≤ p) :
    delay d (pulse a p w) = pulse a (p + d) w := by
  funext t
  simp only [delay, pulse]
  by_cases c1 : p ≤ t - d ∧ t - d < p + w <;> by_cases c2 : p + d ≤ t ∧ t < p + d + w <;>
    simp only [c1, c2, if_true, if_false] <;> omega

/-- (2) A pulse of width `w ≥ d` passes, delayed by `d`, width unchanged. -/
theorem saf_pulse_long {a : Bool} {p w d : Nat} (hd : 1 ≤ d) (hp : 1 ≤ p) (hw : d ≤ w) :
    saf d (pulse a p w) = pulse a (p + d) w := by
  rw [saf_eq_delay_of_spaced hd (pulse_spaced hw), delay_pulse hp]

/-- (2) A pulse of width `w < d` vanishes: the output never moves. -/
theorem saf_pulse_short {a : Bool} {p w d : Nat} (hp : 1 ≤ p) (hw : w < d) :
    ∀ t, saf d (pulse a p w) t = a := by
  intro t
  induction t with
  | zero => simp only [saf_zero, pulse]; split <;> first | rfl | omega
  | succ t ih =>
    rw [saf_succ]
    split
    · rename_i hf
      obtain ⟨h1, h2⟩ := fireB_true.1 hf
      have := pulse_tr h2
      simp only [pulse]; split <;> first | rfl | omega
    · exact ih

/-- (2) On an isolated pulse SAF `d` is exactly the inertial delay of
`Trace.Discrete` with rejection `d-1` (pulses of width `≤ d-1`, i.e. `< d`,
vanish), followed by one step. In continuous time this is `InertialRD d d`
with ties passing, as measured in A-gls-compare §2. -/
theorem saf_pulse_eq_inertial {a : Bool} {p w d : Nat} (hd : 1 ≤ d) (hp : 1 ≤ p) :
    saf d (pulse a p w) = delay 1 (inertial (d - 1) (pulse a p w)) := by
  funext t
  simp only [delay]
  by_cases hw : w < d
  · rw [saf_pulse_short hp hw, inertial_filters hp (by omega)]
  · rw [saf_pulse_long hd hp (by omega), inertial_passes hp (by omega)]
    simp only [pulse]
    by_cases c1 : p + d ≤ t ∧ t < p + d + w <;>
      by_cases c2 : p + (d - 1) ≤ t - 1 ∧ t - 1 < p + (d - 1) + w <;>
      simp only [c1, c2, if_true, if_false] <;> omega

end Formal.Core.DelaySAF
