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
    simp only [c1, c2, ↓reduceIte] at h <;> first | omega | exact absurd rfl h

theorem pulse_spaced {a : Bool} {p w d : Nat} (hw : d ≤ w) : Spaced d (pulse a p w) := by
  intro k k' hk hk' hlt
  rcases pulse_tr hk with h1 | h1 <;> rcases pulse_tr hk' with h2 | h2 <;> omega

theorem delay_pulse {a : Bool} {p w d : Nat} (hp : 1 ≤ p) :
    delay d (pulse a p w) = pulse a (p + d) w := by
  funext t
  simp only [delay, pulse]
  by_cases c1 : p ≤ t - d ∧ t - d < p + w <;> by_cases c2 : p + d ≤ t ∧ t < p + d + w <;>
    simp only [c1, c2, ↓reduceIte] <;> omega

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
      simp only [c1, c2, ↓reduceIte] <;> omega


/-! ## 3. Early propagation and runts -/

/-- Early-propagation witness: rises at step 1, falls at `d`, rises for good
at `s = 2d - ε`. -/
def early (d ε : Nat) : Sig := fun t => decide ((1 ≤ t ∧ t < d) ∨ 2 * d - ε ≤ t)

/-- The SAF output for `early d ε`: low until `2d`, then high. -/
theorem saf_early_val {d ε : Nat} (h1 : 1 ≤ ε) (h2 : ε < d) :
    ∀ t, saf d (early d ε) t = decide (2 * d ≤ t) := by
  intro t
  induction t with
  | zero => simp only [saf_zero, early]; simp only [decide_eq_decide]; omega
  | succ t ih =>
    rw [saf_succ]
    split
    · rename_i hf
      obtain ⟨hd, hc⟩ := fireB_true.1 hf
      simp only [early, ne_eq, decide_eq_decide] at hc ⊢
      omega
    · rename_i hf
      rw [fireB_true] at hf
      simp only [early, ne_eq, decide_eq_decide] at hf
      rw [ih]; simp only [decide_eq_decide]
      omega

/-- (3) Early propagation. For every `ε ∈ [1, d)`: the input makes its last
change at `s = 2d - ε`; the SAF output makes its last change to the final value
at `s + ε` (and differs from it before), whereas the pure delay `d` still
shows the old value at `s + d - 1`. -/
theorem saf_early {d ε : Nat} (h1 : 1 ≤ ε) (h2 : ε < d) :
    early d ε (2 * d - ε) ≠ early d ε (2 * d - ε - 1) ∧
    (∀ t, 2 * d - ε ≤ t → early d ε t = early d ε (2 * d - ε)) ∧
    (∀ t, 2 * d - ε + ε ≤ t → saf d (early d ε) t = early d ε (2 * d - ε)) ∧
    (∀ t, t < 2 * d - ε + ε → saf d (early d ε) t ≠ early d ε (2 * d - ε)) ∧
    delay d (early d ε) (2 * d - ε + d - 1) ≠ early d ε (2 * d - ε) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [early, ne_eq, decide_eq_decide]; omega
  · intro t ht; simp only [early, decide_eq_decide]; omega
  · intro t ht; rw [saf_early_val h1 h2]; simp only [early, decide_eq_decide]; omega
  · intro t ht; rw [saf_early_val h1 h2]; simp only [early, ne_eq, decide_eq_decide]; omega
  · simp only [delay, early, ne_eq, decide_eq_decide]; omega

/-- Two input pulses of width `w`, at `[1, 1+w)` and `[d, d+w)`; both are
narrower than `d`. -/
def twoPulse (d w : Nat) : Sig := fun t => decide ((1 ≤ t ∧ t < 1 + w) ∨ (d ≤ t ∧ t < d + w))

theorem pulse_false_eq (p w t : Nat) : pulse false p w t = decide (p ≤ t ∧ t < p + w) := by
  simp only [pulse]; split <;> rename_i h <;> simp [h]

/-- (3) Runts: SAF turns two sub-`d` input pulses into one output pulse of
width exactly `w`, for every `1 ≤ w ≤ d - 2`. -/
theorem saf_runt {d w : Nat} (hw1 : 1 ≤ w) (hw : w + 2 ≤ d) :
    saf d (twoPulse d w) = pulse false (1 + d) w := by
  funext t
  rw [pulse_false_eq]
  induction t with
  | zero => simp only [saf_zero, twoPulse, decide_eq_decide]; omega
  | succ t ih =>
    rw [saf_succ]
    split
    · rename_i hf
      obtain ⟨hd, hc⟩ := fireB_true.1 hf
      simp only [twoPulse, ne_eq, decide_eq_decide] at hc ⊢
      omega
    · rename_i hf
      rw [fireB_true] at hf
      simp only [twoPulse, ne_eq, decide_eq_decide] at hf
      rw [ih]; simp only [decide_eq_decide]
      omega

/-- (3) That runt is not an output of any inertial channel of `Trace.Discrete`
with rejection `d - 1` (for any input whatsoever): inertial outputs hold every
new value for `d` steps (`inertial_min_width`). -/
theorem saf_runt_not_inertial {d w : Nat} (hw1 : 1 ≤ w) (hw : w + 2 ≤ d) (i : Sig) :
    delay 1 (inertial (d - 1) i) ≠ saf d (twoPulse d w) := by
  intro h
  rw [saf_runt hw1 hw] at h
  have e1 := congrFun h (1 + d)
  have e0 := congrFun h d
  have e2 := congrFun h (1 + d + w)
  simp only [delay, pulse_false_eq] at e0 e1 e2
  rw [show 1 + d - 1 = d - 1 + 1 by omega] at e1
  rw [show 1 + d + w - 1 = d - 1 + 1 + w by omega] at e2
  have hne : inertial (d - 1) i (d - 1 + 1) ≠ inertial (d - 1) i (d - 1) := by
    have : inertial (d - 1) i (d - 1) = false := by
      simpa [show ¬ (1 + d ≤ d) by omega] using e0
    rw [e1, this]; simp; omega
  have := inertial_min_width hne w (by omega)
  rw [e2, e1] at this
  simp at this; omega

/-! ## 4 (cont.). No positive lower bound beyond one step -/

/-- (4) SAF `d` is not contained in any transport band `[lo, hi]` with
`lo ≥ 2` and `hi ≤ 2d - 2` (in particular not in `[lo, d]` for `lo ≥ 2`):
the early witness with `ε = 1` refutes it. With `saf_transport`, `[1, d]` is
the exact discrete band: the GLS per-LUT delay is an upper bound only. -/
theorem saf_not_transport {d lo hi : Nat} (hd : 2 ≤ d) (hlo : 2 ≤ lo) (hhi : hi ≤ 2 * d - 2) :
    ¬ Transport lo hi (early d 1) (saf d (early d 1)) := by
  intro h
  obtain ⟨f, F, hf⟩ := transport_mono hlo hhi h
  have a := hf (2 * d)
  have b := hf (2 * d - 1)
  have m := F.mono (2 * d - 1) (2 * d) (by omega)
  have l := F.le_late (2 * d)
  have e := F.early_le (2 * d - 1)
  rw [saf_early_val (by omega) (by omega)] at a b
  simp only [early, decide_eq_decide] at a b
  omega

/-! ## 5. Settle times and bundled-data margins -/

/-- `s` holds its final value from step `T` on. -/
def SettledFrom (s : Sig) (T : Nat) : Prop := ∀ t, T ≤ t → s t = s T

theorem settled_mono {s : Sig} {T T' : Nat} (h : SettledFrom s T) (hT : T ≤ T') :
    SettledFrom s T' := by
  intro t ht; rw [h t (by omega), h T' hT]

theorem settled_delay {s : Sig} {T : Nat} (d : Nat) (h : SettledFrom s T) :
    SettledFrom (delay d s) (T + d) := by
  intro t ht; simp only [delay]
  rw [h (t - d) (by omega), h (T + d - d) (by omega)]

/-- Any transport behaviour with upper bound `hi` settles no later than the
pure delay `hi` does. -/
theorem settle_of_transport {lo hi S : Nat} {x y : Sig} (h : Transport lo hi x y)
    (hs : SettledFrom (delay hi x) S) : SettledFrom y S := by
  obtain ⟨f, F, hf⟩ := h
  have key : ∀ u, S - hi ≤ u → x u = x (S - hi) := by
    intro u hu
    have := hs (u + hi) (by omega)
    simp only [delay] at this
    rwa [show u + hi - hi = u by omega] at this
  intro t ht
  rw [hf, hf, key (f t) (by have := F.early_le t; omega),
    key (f S) (by have := F.early_le S; omega)]

/-- (5) One LUT: the settle time the GLS shows is never later than the pure
delay `d` settle time on the same function-value stimulus. (Strictly earlier
is possible: `saf_early`.) -/
theorem saf_settle_le_delay {d S : Nat} {x : Sig} (hd : 1 ≤ d)
    (hs : SettledFrom (delay d x) S) : SettledFrom (saf d x) S :=
  settle_of_transport (saf_transport x hd) hs

/-- Static bound: SAF output settles `d` after its input. -/
theorem saf_settle {d T : Nat} {x : Sig} (hd : 1 ≤ d) (h : SettledFrom x T) :
    SettledFrom (saf d x) (T + d) :=
  saf_settle_le_delay hd (settled_delay d h)

theorem transport_map {lo hi : Nat} {x y : Sig} (g : Bool → Bool) (h : Transport lo hi x y) :
    Transport lo hi (fun t => g (x t)) (fun t => g (y t)) := by
  obtain ⟨f, F, hf⟩ := h
  exact ⟨f, F, fun t => by dsimp only; rw [hf]⟩

/-- (5) Two-LUT chain (LUT 2 computes `g` of LUT 1's output): the GLS (SAF)
settle time is never later than the pure-delay (`[d1,d1]`, `[d2,d2]`) settle
time. The GLS is optimistic, never pessimistic, on a chain. -/
theorem chain_settle_le_delay {d1 d2 S : Nat} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (g : Bool → Bool) (a : Sig)
    (hs : SettledFrom (delay d2 (fun t => g (delay d1 a t))) S) :
    SettledFrom (saf d2 (fun t => g (saf d1 a t))) S := by
  have T1 := transport_map g (saf_transport a hd1)
  have T2 := saf_transport (fun t => g (saf d1 a t)) hd2
  have T := transport_comp T1 T2
  apply settle_of_transport T
  have e : delay (d1 + d2) (fun t => g (a t)) = delay d2 (fun t => g (delay d1 a t)) := by
    funext t; simp only [delay]; rw [show t - d2 - d1 = t - (d1 + d2) by omega]
  rw [e]; exact hs

/-- (5) Static bound for a 2-LUT network where LUT 2 also reads a side input
`b`: the GLS output settles by `max (Ta + d1) Tb + d2`, the same bound static
timing gives for pure delays. -/
theorem net_settle_static {d1 d2 Ta Tb : Nat} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (f : Bool → Bool → Bool) {a b : Sig} (ha : SettledFrom a Ta) (hb : SettledFrom b Tb) :
    SettledFrom (saf d2 (fun t => f (saf d1 a t) (b t))) (max (Ta + d1) Tb + d2) := by
  apply saf_settle hd2
  have h1 := settled_mono (saf_settle hd1 ha) (Nat.le_max_left (Ta + d1) Tb)
  have h2 := settled_mono hb (Nat.le_max_right (Ta + d1) Tb)
  intro t ht; dsimp only; rw [h1 t ht, h2 t ht]

/-- (5) The reverse of `chain_settle_le_delay` fails: on a 2-LUT chain (LUT 2
a buffer) the GLS output has settled at `2d + d2` while the pure-delay chain
has not (it settles only at `3d - 1 + d2`): the GLS reports the data valid
`d - 1` steps early. -/
theorem chain_early {d d2 : Nat} (hd : 2 ≤ d) (hd2 : 1 ≤ d2) :
    SettledFrom (saf d2 (fun t => saf d (early d 1) t)) (2 * d + d2) ∧
    ¬ SettledFrom (delay d2 (fun t => delay d (early d 1) t)) (2 * d + d2) := by
  constructor
  · apply saf_settle hd2
    intro t ht; dsimp only
    rw [saf_early_val (by omega) (by omega), saf_early_val (by omega) (by omega)]
    simp only [decide_eq_decide]; omega
  · intro h
    have := h (3 * d - 1 + d2) (by omega)
    simp only [delay, early, decide_eq_decide] at this
    omega

theorem xor_input {d : Nat} (hd : 2 ≤ d) :
    (fun t => xor (saf d (early d 1) t) (delay d (early d 1) t)) =
      pulse false (1 + d) (2 * d - 2) := by
  funext t
  rw [saf_early_val (by omega) (by omega), pulse_false_eq]
  simp only [delay, early]
  by_cases c1 : 2 * d ≤ t <;>
    by_cases c2 : (1 ≤ t - d ∧ t - d < d) ∨ 2 * d - 1 ≤ t - d <;>
    by_cases c3 : 1 + d ≤ t ∧ t < 1 + d + (2 * d - 2) <;>
    simp only [c1, c2, c3, decide_true, decide_false] <;> first | rfl | omega

/-- (5) In a reconvergent 2-LUT network neither direction holds: with LUT 2 an
XOR whose side input `b` equals the pure-delay image of LUT 1's output, the
pure-delay network output is constant (settled from 0), while the GLS output
still moves at `3d - 1 + d2` (the static bound). So "GLS settle ≤ transport
settle" is a chain property, not a network property. -/
theorem xor_settle_late {d d2 : Nat} (hd : 2 ≤ d) (hd2 : 1 ≤ d2) (hd2' : d2 ≤ 2 * d - 2) :
    SettledFrom (delay d2 (fun t => xor (delay d (early d 1) t) (delay d (early d 1) t))) 0 ∧
    ¬ SettledFrom (saf d2 (fun t => xor (saf d (early d 1) t) (delay d (early d 1) t)))
        (3 * d - 2 + d2) := by
  constructor
  · intro t _; simp [delay]
  · rw [xor_input hd, saf_pulse_long hd2 (by omega) hd2']
    intro h
    have := h (3 * d - 1 + d2) (by omega)
    rw [pulse_false_eq, pulse_false_eq] at this
    simp only [decide_eq_decide] at this
    omega

/-- (5) Trust condition. If, in the GLS run itself, every fire of LUT 1 and of
LUT 2 copies the value its own change set (`Faithful`), the GLS run of the
2-LUT network is exactly the pure-delay run: every observed time, settle time
and margin is the transport one. -/
theorem net_eq_delay_of_faithful {d1 d2 : Nat} (f : Bool → Bool → Bool) (a b : Sig)
    (h1 : Faithful d1 a) (h2 : Faithful d2 (fun t => f (saf d1 a t) (b t))) :
    saf d2 (fun t => f (saf d1 a t) (b t)) = delay d2 (fun t => f (delay d1 a t) (b t)) := by
  rw [saf_eq_delay_iff.2 h2, saf_eq_delay_iff.2 h1]

/-- (5) The same with the stimulus condition: each LUT's function value has no
two changes closer than its delay (evaluated on the pure-delay run, which
then equals the GLS run). -/
theorem net_eq_delay_of_spaced {d1 d2 : Nat} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (f : Bool → Bool → Bool) (a b : Sig)
    (h1 : Spaced d1 a) (h2 : Spaced d2 (fun t => f (delay d1 a t) (b t))) :
    saf d2 (fun t => f (saf d1 a t) (b t)) = delay d2 (fun t => f (delay d1 a t) (b t)) := by
  have e1 := saf_eq_delay_of_spaced hd1 h1
  rw [e1]; exact saf_eq_delay_of_spaced hd2 h2

end Formal.Core.DelaySAF
