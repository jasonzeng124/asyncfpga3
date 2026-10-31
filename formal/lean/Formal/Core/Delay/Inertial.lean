import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Inertial delay channels in continuous time (track 3, channel (b))

Self-contained probe. A signal is any `ℝ → Bool` (the representation probe picks the
final type; nothing here needs finite variability, the theorems are about the
specific signals they name).

Semantics. `Filt ρ x` is the zero-delay *rejection filter* with window `ρ`:
its value at `u` is `x τ` for the latest `τ ≤ u` such that `x` is constant on
`[τ, τ + ρ)`. An inertial channel with rejection window `ρ` and delay `Δ` is that
filter followed by a pure shift by `Δ`; the classic Verilog inertial delay `δ` is
`ρ = Δ = δ`. For a finitely-variable input this is exactly the event-queue rule
"an input change at `t` schedules the new value at `t + δ`; a later input change
before `t + δ` cancels it": the surviving input changes are exactly those followed
by `≥ δ` of stability. (Tie convention: a change at exactly `t + δ` does not cancel.)

Channels are relations (`Filt`, `InertialRD`), not functions; we prove they are
functional (`filt_unique`, `inertialRD_unique`), so every "the output is ..."
theorem below is a uniqueness consequence plus an existence witness.

Main results (all proved, no axioms):
* `inertialRD_pulse_short` / `_exists`: pulses shorter than `ρ` are removed.
* `inertialRD_pulse_long`  / `_exists`: pulses of width `≥ ρ` pass, width
  preserved, shifted by `Δ`.
* `inertial_width_discontinuous`: output pulse width jumps from `0` to `δ` at `δ`.
* `noShort_of_inertialRD`, `inertialRD_output_pulse_width_ge`: an inertial
  channel never outputs a pulse shorter than `ρ`, whatever the input.
* `inertialRD_comp`, `inertialRD_comp_iff`: if `ρ₂ ≤ ρ₁`,
  `InertialRD ρ₁ Δ₁ ; InertialRD ρ₂ Δ₂ = InertialRD ρ₁ (Δ₁ + Δ₂)`;
  in particular `Inertial δ ; Inertial δ = InertialRD δ (2δ)` (idempotence of the filter).
* `inertial_comp_ne_sum`: `Inertial δ₁ ; Inertial δ₂ ≠ Inertial (δ₁ + δ₂)`
  for all `δ₁, δ₂ > 0`.
* `inertial_comp_1_2_not_inertialRD`: `Inertial 1 ; Inertial 2` is not
  `InertialRD ρ Δ` for any `ρ, Δ`; `inertial_order_matters`: the two orders differ.
* Bounded-delay variant `BoundedInertial`: same filtering/passing theorems.
-/

namespace Formal.Core.DelayInertial

/-- A binary signal in continuous time. -/
abbrev Sig := ℝ → Bool

/-- `x` is constant on `[τ, τ + ρ)`. -/
def Stable (x : Sig) (τ ρ : ℝ) : Prop := ∀ u, τ ≤ u → u < τ + ρ → x u = x τ

/-- The filter with rejection window `ρ` outputs `b` at time `u`. -/
def FiltAt (ρ : ℝ) (x : Sig) (b : Bool) (u : ℝ) : Prop :=
  ∃ τ, τ ≤ u ∧ Stable x τ ρ ∧ b = x τ ∧
    ∀ τ', τ < τ' → τ' ≤ u → Stable x τ' ρ → x τ' = x τ

/-- Zero-delay rejection filter relation. -/
def Filt (ρ : ℝ) (x z : Sig) : Prop := ∀ u, FiltAt ρ x (z u) u

/-- Inertial channel with rejection window `ρ` and (fixed) delay `Δ`.
Verilog: a module path delay `Δ` with `PATHPULSE` reject limit `ρ`. -/
def InertialRD (ρ Δ : ℝ) (x y : Sig) : Prop := Filt ρ x (fun u => y (u + Δ))

/-- Classic inertial delay `δ` (Verilog default: reject limit = delay). -/
def Inertial (δ : ℝ) (x y : Sig) : Prop := InertialRD δ δ x y

/-- Bounded inertial channel: rejection window `ρ`, delay fixed but only known to
lie in `[lo, hi]` (one unknown delay per channel instance). -/
def BoundedInertial (ρ lo hi : ℝ) (x y : Sig) : Prop :=
  ∃ Δ, lo ≤ Δ ∧ Δ ≤ hi ∧ InertialRD ρ Δ x y

/-- Pure (transport) shift by `Δ`. -/
def shift (Δ : ℝ) (x : Sig) : Sig := fun s => x (s - Δ)

/-- Every maximal constant run of `x` reaching `u` started at a point `t` from
which `x` stays constant for `ρ`: "`x` has no pulse shorter than `ρ`". -/
def NoShort (ρ : ℝ) (x : Sig) : Prop :=
  ∀ u, ∃ t, t ≤ u ∧ Stable x t ρ ∧ ∀ v, t ≤ v → v ≤ u → x v = x t

/-! ## Functionality -/

theorem filtAt_unique {ρ : ℝ} {x : Sig} {b b' : Bool} {u : ℝ}
    (h : FiltAt ρ x b u) (h' : FiltAt ρ x b' u) : b = b' := by
  obtain ⟨τ, hτu, hs, hb, hmax⟩ := h
  obtain ⟨τ', hτu', hs', hb', hmax'⟩ := h'
  subst hb; subst hb'
  rcases lt_trichotomy τ τ' with hlt | heq | hgt
  · exact (hmax τ' hlt hτu' hs').symm
  · rw [heq]
  · exact hmax' τ hgt hτu hs

theorem filt_unique {ρ : ℝ} {x z z' : Sig} (h : Filt ρ x z) (h' : Filt ρ x z') :
    z = z' := funext fun u => filtAt_unique (h u) (h' u)

theorem inertialRD_unique {ρ Δ : ℝ} {x y y' : Sig} (h : InertialRD ρ Δ x y)
    (h' : InertialRD ρ Δ x y') : y = y' := by
  funext s
  have := filtAt_unique (h (s - Δ)) (h' (s - Δ))
  simpa using this

/-! ## No-short-pulse signals -/

theorem stable_mono {x : Sig} {τ ρ ρ' : ℝ} (h : ρ' ≤ ρ) (hs : Stable x τ ρ) :
    Stable x τ ρ' := fun u h1 h2 => hs u h1 (by linarith)

theorem noShort_mono {x : Sig} {ρ ρ' : ℝ} (h : ρ' ≤ ρ) (hx : NoShort ρ x) :
    NoShort ρ' x := fun u => by
  obtain ⟨t, a, b, c⟩ := hx u
  exact ⟨t, a, stable_mono h b, c⟩

/-- On a signal without pulses shorter than `ρ`, the filter is the identity. -/
theorem filt_self_of_noShort {ρ : ℝ} {x : Sig} (hx : NoShort ρ x) : Filt ρ x x := by
  intro u
  obtain ⟨t, htu, hs, hrun⟩ := hx u
  exact ⟨t, htu, hs, hrun u htu le_rfl, fun τ' h1 h2 _ => hrun τ' h1.le h2⟩

/-- The filter's output never has a pulse shorter than `ρ`. -/
theorem noShort_of_filt {ρ : ℝ} {x z : Sig} (h : Filt ρ x z) : NoShort ρ z := by
  intro u
  obtain ⟨τ, hτu, hs, _hb, hmax⟩ := h u
  have key : ∀ v, τ ≤ v → (v ≤ u ∨ v < τ + ρ) → z v = x τ := by
    intro v hv hvor
    obtain ⟨σ, hσv, hσs, hσb, hσmax⟩ := h v
    rw [hσb]
    rcases lt_trichotomy σ τ with hlt | heq | hgt
    · exact (hσmax τ hlt hv hs).symm
    · rw [heq]
    · rcases hvor with hvu | hvr
      · exact hmax σ hgt (le_trans hσv hvu) hσs
      · exact hs σ hgt.le (lt_of_le_of_lt hσv hvr)
  refine ⟨τ, hτu, ?_, ?_⟩
  · intro v h1 h2
    rw [key v h1 (Or.inr h2), key τ le_rfl (Or.inl hτu)]
  · intro v h1 h2
    rw [key v h1 (Or.inl h2), key τ le_rfl (Or.inl hτu)]

theorem noShort_shift {ρ : ℝ} {x : Sig} (Δ : ℝ) (hx : NoShort ρ x) :
    NoShort ρ (shift Δ x) := by
  intro u
  obtain ⟨t, htu, hs, hrun⟩ := hx (u - Δ)
  refine ⟨t + Δ, by linarith, ?_, ?_⟩
  · intro v h1 h2
    simp only [shift, add_sub_cancel_right]
    exact hs (v - Δ) (by linarith) (by linarith)
  · intro v h1 h2
    simp only [shift, add_sub_cancel_right]
    exact hrun (v - Δ) (by linarith) (by linarith)

theorem shift_shift (Δ₁ Δ₂ : ℝ) (x : Sig) :
    shift Δ₂ (shift Δ₁ x) = shift (Δ₁ + Δ₂) x := by
  funext s
  simp only [shift]
  congr 1
  linarith

/-- A filter relation, shifted, is an inertial channel relation. -/
theorem inertialRD_of_filt {ρ : ℝ} {x z : Sig} (Δ : ℝ) (h : Filt ρ x z) :
    InertialRD ρ Δ x (shift Δ z) := by
  have : (fun u => shift Δ z (u + Δ)) = z := by funext u; simp [shift]
  unfold InertialRD; rw [this]; exact h

theorem filt_of_inertialRD {ρ Δ : ℝ} {x y : Sig} (h : InertialRD ρ Δ x y) :
    Filt ρ x (fun u => y (u + Δ)) := h

/-- On a signal without short pulses an inertial channel is a pure delay. -/
theorem inertialRD_of_noShort {ρ : ℝ} {x : Sig} (Δ : ℝ) (hx : NoShort ρ x) :
    InertialRD ρ Δ x (shift Δ x) := inertialRD_of_filt Δ (filt_self_of_noShort hx)

/-- An inertial channel never outputs a pulse shorter than its rejection window. -/
theorem noShort_of_inertialRD {ρ Δ : ℝ} {x y : Sig} (h : InertialRD ρ Δ x y) :
    NoShort ρ y := by
  have h1 := noShort_shift Δ (noShort_of_filt h)
  have : shift Δ (fun u => y (u + Δ)) = y := by funext s; simp [shift]
  rwa [this] at h1

/-! ## Single pulses -/

/-- `b` everywhere except `!b` on `[a, a + w)`. -/
noncomputable def pulse (b : Bool) (a w : ℝ) : Sig :=
  fun u => if a ≤ u ∧ u < a + w then !b else b

theorem pulse_in {b : Bool} {a w u : ℝ} (h1 : a ≤ u) (h2 : u < a + w) :
    pulse b a w u = !b := by
  unfold pulse; rw [if_pos ⟨h1, h2⟩]

theorem pulse_before {b : Bool} {a w u : ℝ} (h : u < a) : pulse b a w u = b := by
  unfold pulse; rw [if_neg]; rintro ⟨h1, _⟩; linarith

theorem pulse_after {b : Bool} {a w u : ℝ} (h : a + w ≤ u) : pulse b a w u = b := by
  unfold pulse; rw [if_neg]; rintro ⟨_, h2⟩; linarith

theorem pulse_eq_not {b : Bool} {a w u : ℝ} (h : pulse b a w u = !b) :
    a ≤ u ∧ u < a + w := by
  unfold pulse at h
  split_ifs at h with hc
  · exact hc
  · cases b <;> simp at h

theorem shift_pulse (b : Bool) (a w Δ : ℝ) : shift Δ (pulse b a w) = pulse b (a + Δ) w := by
  funext s
  have e : (a ≤ s - Δ ∧ s - Δ < a + w) ↔ (a + Δ ≤ s ∧ s < a + Δ + w) :=
    ⟨fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩, fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩⟩
  simp only [shift, pulse, e]

theorem noShort_pulse {b : Bool} {a w ρ : ℝ} (h0 : 0 ≤ ρ) (hw : ρ ≤ w) :
    NoShort ρ (pulse b a w) := by
  intro u
  rcases lt_or_ge u a with h1 | h1
  · refine ⟨u - ρ, by linarith, ?_, ?_⟩
    · intro v _ h3
      rw [pulse_before (by linarith), pulse_before (by linarith)]
    · intro v _ h3
      rw [pulse_before (by linarith), pulse_before (by linarith)]
  · rcases lt_or_ge u (a + w) with h2 | h2
    · refine ⟨a, h1, ?_, ?_⟩
      · intro v h3 h4
        rw [pulse_in h3 (by linarith), pulse_in le_rfl (by linarith)]
      · intro v h3 h4
        rw [pulse_in h3 (by linarith), pulse_in le_rfl (by linarith)]
    · refine ⟨a + w, h2, ?_, ?_⟩
      · intro v h3 _
        rw [pulse_after h3, pulse_after le_rfl]
      · intro v h3 _
        rw [pulse_after h3, pulse_after le_rfl]

theorem noShort_const {ρ : ℝ} (b : Bool) (h0 : 0 ≤ ρ) : NoShort ρ (fun _ => b) :=
  fun u => ⟨u - ρ, by linarith, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- A pulse shorter than the rejection window is removed by the filter. -/
theorem filt_pulse_short {b : Bool} {a w ρ : ℝ} (hρ : 0 < ρ) (hw : w < ρ) :
    Filt ρ (pulse b a w) (fun _ => b) := by
  intro u
  have hm := min_le_right u (a - ρ)
  refine ⟨min u (a - ρ), min_le_left _ _, ?_, ?_, ?_⟩
  · intro v _ h2
    rw [pulse_before (by linarith), pulse_before (by linarith)]
  · exact (pulse_before (by linarith)).symm
  · intro τ' _ _ hs'
    rw [pulse_before (u := min u (a - ρ)) (by linarith)]
    cases hv : pulse b a w τ' with
    | false =>
      cases b
      · rfl
      · exfalso
        have hn : pulse true a w τ' = !true := hv
        obtain ⟨h1, h2⟩ := pulse_eq_not hn
        have := hs' (a + w) (by linarith) (by linarith)
        rw [pulse_after le_rfl, hv] at this
        exact absurd this (by decide)
    | true =>
      cases b
      · exfalso
        have hn : pulse false a w τ' = !false := hv
        obtain ⟨h1, h2⟩ := pulse_eq_not hn
        have := hs' (a + w) (by linarith) (by linarith)
        rw [pulse_after le_rfl, hv] at this
        exact absurd this (by decide)
      · rfl

/-! ## Pulse theorems for the inertial channel -/

theorem inertialRD_pulse_short_exists {b : Bool} {a w ρ : ℝ} (Δ : ℝ) (hρ : 0 < ρ)
    (hw : w < ρ) : InertialRD ρ Δ (pulse b a w) (fun _ => b) :=
  filt_pulse_short hρ hw

/-- **Short pulses are filtered**: if `w < ρ`, the output is constant `b`. -/
theorem inertialRD_pulse_short {b : Bool} {a w ρ Δ : ℝ} {y : Sig} (hρ : 0 < ρ)
    (hw : w < ρ) (h : InertialRD ρ Δ (pulse b a w) y) : y = fun _ => b :=
  inertialRD_unique h (inertialRD_pulse_short_exists Δ hρ hw)

theorem inertialRD_pulse_long_exists {b : Bool} {a w ρ : ℝ} (Δ : ℝ) (h0 : 0 ≤ ρ)
    (hw : ρ ≤ w) : InertialRD ρ Δ (pulse b a w) (pulse b (a + Δ) w) := by
  rw [← shift_pulse]
  exact inertialRD_of_noShort Δ (noShort_pulse h0 hw)

/-- **Long pulses pass**: if `w ≥ ρ`, the output is the same pulse delayed by `Δ`. -/
theorem inertialRD_pulse_long {b : Bool} {a w ρ Δ : ℝ} {y : Sig} (h0 : 0 ≤ ρ)
    (hw : ρ ≤ w) (h : InertialRD ρ Δ (pulse b a w) y) : y = pulse b (a + Δ) w :=
  inertialRD_unique h (inertialRD_pulse_long_exists Δ h0 hw)

/-- Classic inertial delay `δ`: short pulses vanish. -/
theorem inertial_pulse_short {b : Bool} {a w δ : ℝ} {y : Sig} (hδ : 0 < δ) (hw : w < δ)
    (h : Inertial δ (pulse b a w) y) : y = fun _ => b :=
  inertialRD_pulse_short hδ hw h

/-- Classic inertial delay `δ`: pulses of width `≥ δ` pass, delayed by `δ`. -/
theorem inertial_pulse_long {b : Bool} {a w δ : ℝ} {y : Sig} (hδ : 0 ≤ δ) (hw : δ ≤ w)
    (h : Inertial δ (pulse b a w) y) : y = pulse b (a + δ) w :=
  inertialRD_pulse_long hδ hw h

/-- A constant input gives the same constant output (SPF condition "no input
pulse, no output transition"). -/
theorem inertialRD_const {b : Bool} {ρ Δ : ℝ} {y : Sig} (h0 : 0 ≤ ρ)
    (h : InertialRD ρ Δ (fun _ => b) y) : y = fun _ => b := by
  have h2 := inertialRD_of_noShort Δ (noShort_const b h0)
  rw [inertialRD_unique h h2]
  rfl

/-- **No runts**: whatever the input, if an inertial channel outputs a single pulse of
positive width `w`, then `w ≥ ρ`. -/
theorem inertialRD_output_pulse_width_ge {b : Bool} {a w ρ Δ : ℝ} {x : Sig}
    (h : InertialRD ρ Δ x (pulse b a w)) (hw : 0 < w) : ρ ≤ w := by
  obtain ⟨t, hta, hs, hrun⟩ := noShort_of_inertialRD h a
  have ha : pulse b a w a = !b := pulse_in le_rfl (by linarith)
  have ht : pulse b a w t = !b := (hrun a hta le_rfl).symm.trans ha
  obtain ⟨h1, h2⟩ := pulse_eq_not ht
  by_contra hlt
  have hlt' : w < ρ := lt_of_not_ge hlt
  have := hs (a + w) (by linarith) (by linarith)
  rw [pulse_after le_rfl, ht] at this
  cases b <;> simp at this

/-- **Discontinuity** of the input-width ↦ output-width map at `δ`: arbitrarily close
input widths `w₁ < w₂` give no output pulse and an output pulse of width `w₂ ≥ δ`. -/
theorem inertial_width_discontinuous {b : Bool} {a δ : ℝ} (hδ : 0 < δ) :
    ∀ ε > 0, ∃ w₁ w₂ : ℝ, w₁ < w₂ ∧ w₂ - w₁ < ε ∧ δ ≤ w₂ ∧
      (∀ y, Inertial δ (pulse b a w₁) y → y = fun _ => b) ∧
      (∀ y, Inertial δ (pulse b a w₂) y → y = pulse b (a + δ) w₂) := by
  intro ε hε
  refine ⟨δ - ε / 2, δ, by linarith, by linarith, le_rfl, ?_, ?_⟩
  · intro y hy; exact inertial_pulse_short hδ (by linarith) hy
  · intro y hy; exact inertial_pulse_long hδ.le le_rfl hy

/-- **An inertial channel solves bounded Short-Pulse Filtration** (SPF, Függer et al.),
in the single-pulse form used here: (i) no input pulse, no output transition; (ii) some input
pulse produces an output transition; (iii) no output pulse is shorter than `ρ`, for every
input; (iv) on a pulse input the output is settled `Δ` after the input settles. Physically
bounded SPF is impossible (see notes), so this is a witness that the inertial model is
unfaithful. -/
theorem inertialRD_solves_boundedSPF {ρ Δ : ℝ} (hρ : 0 < ρ) :
    (∀ y, InertialRD ρ Δ (fun _ => false) y → y = fun _ => false) ∧
    (∃ y, InertialRD ρ Δ (pulse false 0 ρ) y ∧ y Δ = true) ∧
    (∀ x y, InertialRD ρ Δ x y → NoShort ρ y) ∧
    (∀ a w y, InertialRD ρ Δ (pulse false a w) y → ∀ s, a + w + Δ ≤ s → y s = false) := by
  refine ⟨fun y h => inertialRD_const hρ.le h, ⟨_, inertialRD_pulse_long_exists Δ hρ.le le_rfl,
    pulse_in (by linarith) (by linarith)⟩, fun _ _ h => noShort_of_inertialRD h, ?_⟩
  intro a w y h s hs
  rcases lt_or_ge w ρ with hw | hw
  · rw [inertialRD_pulse_short hρ hw h]
  · rw [inertialRD_pulse_long hρ.le hw h, pulse_after (by linarith)]

/-! ## Bounded inertial channel -/

theorem boundedInertial_pulse_short {b : Bool} {a w ρ lo hi : ℝ} {y : Sig} (hρ : 0 < ρ)
    (hw : w < ρ) (h : BoundedInertial ρ lo hi (pulse b a w) y) : y = fun _ => b := by
  obtain ⟨Δ, _, _, hΔ⟩ := h
  exact inertialRD_pulse_short hρ hw hΔ

theorem boundedInertial_pulse_long {b : Bool} {a w ρ lo hi : ℝ} {y : Sig} (h0 : 0 ≤ ρ)
    (hw : ρ ≤ w) (h : BoundedInertial ρ lo hi (pulse b a w) y) :
    ∃ Δ, lo ≤ Δ ∧ Δ ≤ hi ∧ y = pulse b (a + Δ) w := by
  obtain ⟨Δ, h1, h2, hΔ⟩ := h
  exact ⟨Δ, h1, h2, inertialRD_pulse_long h0 hw hΔ⟩

/-- Every delay in `[lo, hi]` is realised: the bounded channel is genuinely
nondeterministic on long pulses. -/
theorem boundedInertial_pulse_long_exists {b : Bool} {a w ρ lo hi Δ : ℝ} (h0 : 0 ≤ ρ)
    (hw : ρ ≤ w) (h1 : lo ≤ Δ) (h2 : Δ ≤ hi) :
    BoundedInertial ρ lo hi (pulse b a w) (pulse b (a + Δ) w) :=
  ⟨Δ, h1, h2, inertialRD_pulse_long_exists Δ h0 hw⟩

theorem boundedInertial_no_runt {b : Bool} {a w ρ lo hi : ℝ} {x : Sig}
    (h : BoundedInertial ρ lo hi x (pulse b a w)) (hw : 0 < w) : ρ ≤ w := by
  obtain ⟨Δ, _, _, hΔ⟩ := h
  exact inertialRD_output_pulse_width_ge hΔ hw

/-! ## Composition -/

/-- **Composition, the true relation (one direction)**: if the second rejection window is
no wider than the first, the cascade is the first filter followed by the summed delay. -/
theorem inertialRD_comp {ρ₁ ρ₂ Δ₁ Δ₂ : ℝ} {x y w : Sig} (hρ : ρ₂ ≤ ρ₁)
    (h1 : InertialRD ρ₁ Δ₁ x y) (h2 : InertialRD ρ₂ Δ₂ y w) :
    InertialRD ρ₁ (Δ₁ + Δ₂) x w := by
  have hy : Filt ρ₂ y y := filt_self_of_noShort (noShort_mono hρ (noShort_of_inertialRD h1))
  have hw : (fun u => w (u + Δ₂)) = y := filt_unique h2 hy
  have e : (fun u => w (u + (Δ₁ + Δ₂))) = (fun u => y (u + Δ₁)) := by
    funext u
    have := congrFun hw (u + Δ₁)
    rw [← add_assoc]; exact this
  unfold InertialRD; rw [e]; exact h1

/-- ... and the converse: for `ρ₂ ≤ ρ₁`, `w` is a cascade output iff it is the output of
`InertialRD ρ₁ (Δ₁ + Δ₂)`. -/
theorem inertialRD_comp_iff {ρ₁ ρ₂ Δ₁ Δ₂ : ℝ} {x y w : Sig} (hρ : ρ₂ ≤ ρ₁)
    (h1 : InertialRD ρ₁ Δ₁ x y) :
    InertialRD ρ₂ Δ₂ y w ↔ InertialRD ρ₁ (Δ₁ + Δ₂) x w := by
  constructor
  · exact inertialRD_comp hρ h1
  · intro h
    have hny : NoShort ρ₂ y := noShort_mono hρ (noShort_of_inertialRD h1)
    have hc := inertialRD_comp hρ h1 (inertialRD_of_noShort Δ₂ hny)
    rw [inertialRD_unique h hc]
    exact inertialRD_of_noShort Δ₂ hny

/-- Idempotence of the classic channel: `Inertial δ ; Inertial δ` is the `δ` filter with
delay `2δ` -- *not* `Inertial (2δ)` (see `inertial_comp_ne_sum`). -/
theorem inertial_comp_self {δ : ℝ} {x y w : Sig} (h1 : Inertial δ x y) :
    Inertial δ y w ↔ InertialRD δ (δ + δ) x w :=
  inertialRD_comp_iff le_rfl h1

/-- **Counterexample**: for all `δ₁, δ₂ > 0`, the cascade `Inertial δ₁ ; Inertial δ₂`
is not `Inertial (δ₁ + δ₂)`: a pulse of width `max δ₁ δ₂` passes the cascade but is
filtered by `Inertial (δ₁ + δ₂)`. -/
theorem inertial_comp_ne_sum {δ₁ δ₂ : ℝ} (h1 : 0 < δ₁) (h2 : 0 < δ₂) :
    ¬ ∀ x y w : Sig, Inertial δ₁ x y → Inertial δ₂ y w → Inertial (δ₁ + δ₂) x w := by
  intro h
  let m := max δ₁ δ₂
  let x := pulse false 0 m
  have hx1 : NoShort δ₁ x := noShort_pulse h1.le (le_max_left _ _)
  have hx2 : NoShort δ₂ x := noShort_pulse h2.le (le_max_right _ _)
  have hy : Inertial δ₁ x (shift δ₁ x) := inertialRD_of_noShort δ₁ hx1
  have hw : Inertial δ₂ (shift δ₁ x) (shift δ₂ (shift δ₁ x)) :=
    inertialRD_of_noShort δ₂ (noShort_shift δ₁ hx2)
  have hm : m < δ₁ + δ₂ := max_lt (by linarith) (by linarith)
  have hc := inertial_pulse_short (by linarith) hm (h x _ _ hy hw)
  have := congrFun hc (δ₁ + δ₂)
  rw [shift_shift, shift_pulse] at this
  have hp : pulse false (0 + (δ₁ + δ₂)) m (δ₁ + δ₂) = true :=
    pulse_in (by linarith) (by have : 0 < m := lt_max_of_lt_left h1; linarith)
  rw [hp] at this
  exact absurd this (by decide)

/-! ### Order matters, and `Inertial 1 ; Inertial 2` is not any inertial channel -/

/-- High on `[0, 3/2)` and `[2, 7/2)`: two `3/2` pulses separated by a `1/2` gap. -/
noncomputable def twoPulse : Sig :=
  fun u => if (0 ≤ u ∧ u < 3 / 2) ∨ (2 ≤ u ∧ u < 7 / 2) then true else false

theorem twoPulse_true {u : ℝ} (h : (0 ≤ u ∧ u < 3 / 2) ∨ (2 ≤ u ∧ u < 7 / 2)) :
    twoPulse u = true := by
  unfold twoPulse; rw [if_pos h]

theorem twoPulse_false {u : ℝ} (h : ¬ ((0 ≤ u ∧ u < 3 / 2) ∨ (2 ≤ u ∧ u < 7 / 2))) :
    twoPulse u = false := by
  unfold twoPulse; rw [if_neg h]

theorem twoPulse_cond_of_true {u : ℝ} (h : twoPulse u = true) :
    (0 ≤ u ∧ u < 3 / 2) ∨ (2 ≤ u ∧ u < 7 / 2) := by
  unfold twoPulse at h
  split_ifs at h with hc
  · exact hc

theorem twoPulse_cond_of_false {u : ℝ} (h : twoPulse u = false) :
    ¬ ((0 ≤ u ∧ u < 3 / 2) ∨ (2 ≤ u ∧ u < 7 / 2)) := by
  intro hc; rw [twoPulse_true hc] at h; exact absurd h (by decide)

theorem twoPulse_neg {u : ℝ} (h : u < 0) : twoPulse u = false :=
  twoPulse_false (by rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> linarith)

/-- Any filter wider than `3/2` removes both pulses. -/
theorem filt_twoPulse_wide {ρ : ℝ} (hρ : 3 / 2 < ρ) : Filt ρ twoPulse (fun _ => false) := by
  intro u
  have hm := min_le_right u (-ρ)
  refine ⟨min u (-ρ), min_le_left _ _, ?_, ?_, ?_⟩
  · intro v _ h2
    rw [twoPulse_neg (by linarith), twoPulse_neg (by linarith)]
  · exact (twoPulse_neg (by linarith)).symm
  · intro τ' _ _ hs'
    rw [twoPulse_neg (u := min u (-ρ)) (by linarith)]
    cases hv : twoPulse τ' with
    | false => rfl
    | true =>
      exfalso
      rcases twoPulse_cond_of_true hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := hs' (3 / 2) (by linarith) (by linarith)
        rw [hv, twoPulse_false (by rintro (⟨_, h⟩ | ⟨h, _⟩) <;> linarith)] at this
        exact absurd this (by decide)
      · have := hs' (7 / 2) (by linarith) (by linarith)
        rw [hv, twoPulse_false (by rintro (⟨_, h⟩ | ⟨_, h⟩) <;> linarith)] at this
        exact absurd this (by decide)

/-- The width-1 filter fills the `1/2` gap: output is one pulse on `[0, 7/2)`. -/
theorem filt_twoPulse_one : Filt 1 twoPulse (pulse false 0 (7 / 2)) := by
  intro u
  rcases lt_or_ge u 0 with ha | ha
  · -- before the first pulse
    refine ⟨u - 1, by linarith, ?_, ?_, ?_⟩
    · intro v _ h2; rw [twoPulse_neg (by linarith), twoPulse_neg (by linarith)]
    · rw [pulse_before ha, twoPulse_neg (by linarith)]
    · intro τ' _ h2 _; rw [twoPulse_neg (by linarith), twoPulse_neg (by linarith)]
  rcases le_or_gt u (1 / 2) with hb | hb
  · -- inside the first pulse, a full window ahead
    refine ⟨u, le_rfl, ?_, ?_, ?_⟩
    · intro v h1 h2
      rw [twoPulse_true (Or.inl ⟨by linarith, by linarith⟩),
        twoPulse_true (Or.inl ⟨by linarith, by linarith⟩)]
    · rw [pulse_in ha (by linarith), twoPulse_true (Or.inl ⟨by linarith, by linarith⟩)]; rfl
    · intro τ' h1 h2 _; linarith
  rcases lt_or_ge u 2 with hc | hc
  · -- end of the first pulse and the gap: held by the window starting at 1/2
    refine ⟨1 / 2, by linarith, ?_, ?_, ?_⟩
    · intro v h1 h2
      rw [twoPulse_true (Or.inl ⟨by linarith, by linarith⟩),
        twoPulse_true (Or.inl ⟨by norm_num, by norm_num⟩)]
    · rw [pulse_in ha (by linarith), twoPulse_true (Or.inl ⟨by norm_num, by norm_num⟩)]; rfl
    · intro τ' h1 h2 hs'
      rw [twoPulse_true (u := 1 / 2) (Or.inl ⟨by norm_num, by norm_num⟩)]
      cases hv : twoPulse τ' with
      | true => rfl
      | false =>
        exfalso
        have hn := twoPulse_cond_of_false hv
        have h3 : 3 / 2 ≤ τ' := by
          by_contra hh
          exact hn (Or.inl ⟨by linarith, lt_of_not_ge hh⟩)
        have := hs' 2 (by linarith) (by linarith)
        rw [hv, twoPulse_true (Or.inr ⟨by norm_num, by norm_num⟩)] at this
        exact absurd this (by decide)
  rcases le_or_gt u (5 / 2) with hd | hd
  · -- inside the second pulse, a full window ahead
    refine ⟨u, le_rfl, ?_, ?_, ?_⟩
    · intro v h1 h2
      rw [twoPulse_true (Or.inr ⟨by linarith, by linarith⟩),
        twoPulse_true (Or.inr ⟨by linarith, by linarith⟩)]
    · rw [pulse_in ha (by linarith), twoPulse_true (Or.inr ⟨by linarith, by linarith⟩)]; rfl
    · intro τ' h1 h2 _; linarith
  rcases lt_or_ge u (7 / 2) with he | he
  · -- end of the second pulse: held by the window starting at 5/2
    refine ⟨5 / 2, by linarith, ?_, ?_, ?_⟩
    · intro v h1 h2
      rw [twoPulse_true (Or.inr ⟨by linarith, by linarith⟩),
        twoPulse_true (Or.inr ⟨by norm_num, by norm_num⟩)]
    · rw [pulse_in ha (by linarith), twoPulse_true (Or.inr ⟨by norm_num, by norm_num⟩)]; rfl
    · intro τ' h1 h2 _
      rw [twoPulse_true (Or.inr ⟨by linarith, by linarith⟩),
        twoPulse_true (Or.inr ⟨by norm_num, by norm_num⟩)]
  · -- after the second pulse
    have hf : ∀ v, 7 / 2 ≤ v → twoPulse v = false := fun v hv =>
      twoPulse_false (by rintro (⟨_, h⟩ | ⟨_, h⟩) <;> linarith)
    refine ⟨u, le_rfl, ?_, ?_, ?_⟩
    · intro v h1 _; rw [hf v (by linarith), hf u he]
    · rw [pulse_after (by linarith), hf u he]
    · intro τ' h1 h2 _; linarith

/-- **Order matters**: `Inertial 1 ; Inertial 2` and `Inertial 2 ; Inertial 1` differ on
`twoPulse` (the first merges the two pulses, the second removes them). -/
theorem inertial_order_matters :
    ∃ x y₁ w₁ y₂ w₂ : Sig, Inertial 1 x y₁ ∧ Inertial 2 y₁ w₁ ∧
      Inertial 2 x y₂ ∧ Inertial 1 y₂ w₂ ∧ w₁ ≠ w₂ := by
  let p := pulse false 0 (7 / 2)
  have hp2 : NoShort 2 p := noShort_pulse (by norm_num) (by norm_num)
  refine ⟨twoPulse, shift 1 p, shift 2 (shift 1 p), shift 2 (fun _ => false),
    shift 1 (shift 2 (fun _ => false)), inertialRD_of_filt 1 filt_twoPulse_one,
    inertialRD_of_noShort 2 (noShort_shift 1 hp2),
    inertialRD_of_filt 2 (filt_twoPulse_wide (by norm_num)),
    inertialRD_of_noShort 1 (noShort_shift 2 (noShort_const false (by norm_num))), ?_⟩
  intro heq
  have := congrFun heq 3
  simp only [shift] at this
  rw [show p (3 - 2 - 1) = true from pulse_in (by norm_num) (by norm_num)] at this
  exact absurd this (by decide)

/-- **`Inertial 1 ; Inertial 2` is not an inertial channel** for any rejection window
and delay. -/
theorem inertial_comp_1_2_not_inertialRD :
    ¬ ∃ ρ Δ : ℝ, ∀ x y w : Sig, Inertial 1 x y → Inertial 2 y w → InertialRD ρ Δ x w := by
  rintro ⟨ρ, Δ, h⟩
  rcases le_or_gt ρ (3 / 2) with hρ | hρ
  · -- a 3/2 pulse: the cascade removes it, any ρ ≤ 3/2 channel passes it
    let x := pulse false 0 (3 / 2)
    have hy : Inertial 1 x (shift 1 x) :=
      inertialRD_of_noShort 1 (noShort_pulse (by norm_num) (by norm_num))
    have hw : Inertial 2 (shift 1 x) (fun _ => false) := by
      have e : shift 1 x = pulse false (0 + 1) (3 / 2) := shift_pulse _ _ _ _
      rw [e]; exact inertialRD_pulse_short_exists 2 (by norm_num) (by norm_num)
    have hc := h x _ _ hy hw
    have hx : NoShort ρ x := noShort_mono hρ (noShort_pulse (by norm_num) le_rfl)
    have := congrFun (inertialRD_unique hc (inertialRD_of_noShort Δ hx)) Δ
    simp only [shift, sub_self] at this
    rw [show x 0 = true from pulse_in le_rfl (by norm_num)] at this
    exact absurd this (by decide)
  · -- twoPulse: the cascade passes one long pulse, any ρ > 3/2 channel removes it
    let p := pulse false 0 (7 / 2)
    have hp2 : NoShort 2 p := noShort_pulse (by norm_num) (by norm_num)
    have hc := h twoPulse _ _ (inertialRD_of_filt 1 filt_twoPulse_one)
      (inertialRD_of_noShort 2 (noShort_shift 1 hp2))
    have := congrFun (inertialRD_unique hc (inertialRD_of_filt Δ (filt_twoPulse_wide hρ))) 3
    simp only [shift] at this
    rw [pulse_in (by norm_num) (by norm_num)] at this
    exact absurd this (by decide)

end Formal.Core.DelayInertial
