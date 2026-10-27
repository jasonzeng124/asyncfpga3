import Formal.Core.Trace.Real
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Trace benchmark (a), B4 inertial delay -- staging file

Needs `Real.exists_isGLB` (completeness of ℝ), i.e. the Mathlib module
`Mathlib.Algebra.Order.Archimedean.Real.Basic`. Content checked here is moved
into `Formal/Core/Trace/Real.lean` once that module is built.
-/

namespace Formal.Core.TraceReal

/-- First change: a right-continuous signal that has value `b` at `v₀` and not
`b` at `t > v₀` has a transition at some `s ∈ (v₀, t]` with `y s ≠ b`.
This is the induction-over-time principle for continuous traces; it needs the
completeness of ℝ. -/
theorem first_change {y : Sig} (hy : WF y) {v₀ t : ℝ} {b : Val} (hv : v₀ ≤ t)
    (h0 : y v₀ = b) (ht : y t ≠ b) :
    ∃ s, v₀ < s ∧ s ≤ t ∧ y s ≠ b ∧ Trans y s := by
  let S : Set ℝ := {u | v₀ ≤ u ∧ u ≤ t ∧ y u ≠ b}
  have hne : S.Nonempty := ⟨t, hv, le_refl t, ht⟩
  have hbdd : BddBelow S := ⟨v₀, fun u hu => hu.1⟩
  obtain ⟨g, hg⟩ := Real.exists_isGLB hne hbdd
  have hgt : g ≤ t := hg.1 ⟨hv, le_refl t, ht⟩
  have hv0g : v₀ ≤ g := hg.2 (fun u hu => hu.1)
  -- below g (and from v₀) the signal is b
  have below : ∀ u, v₀ ≤ u → u < g → y u = b := by
    intro u hu1 hu2
    by_contra hne'
    have := hg.1 ⟨hu1, by linarith, hne'⟩
    linarith
  have hgb : y g ≠ b := by
    intro hgb
    obtain ⟨ε, hε, h1, _⟩ := hy g
    have : g + ε ≤ g := by
      apply hg.2
      intro u hu
      by_contra hlt
      push_neg at hlt
      have hgu : g ≤ u := hg.1 hu
      exact hu.2.2 ((h1 u hgu hlt).trans hgb)
    linarith
  have hv0lt : v₀ < g := by
    rcases eq_or_lt_of_le hv0g with h | h
    · exact absurd (h ▸ h0) hgb
    · exact h
  refine ⟨g, hv0lt, hgt, hgb, g - v₀, by linarith, fun u hu1 hu2 => ?_⟩
  rw [below u (by linarith) hu2]
  exact fun h => hgb h.symm

/-- Inertial delay `δ` as a relation. (1) if the input has been constant on
`[t-δ, t]` the output at `t` equals it; (2) the output only has a transition
at `t` when the input has been constant on `[t-δ, t]`. -/
def Inertial (δ : ℝ) (x y : Sig) : Prop :=
  (∀ t, (∀ u, t - δ ≤ u → u ≤ t → x u = x t) → y t = x t) ∧
  (∀ t, Trans y t → ∀ u, t - δ ≤ u → u ≤ t → x u = x t)

/-- B4 (short pulses): a pulse of width `w ≤ δ` produces no output at all. -/
theorem inertial_short {δ a w : ℝ} {y : Sig} (hδ : 0 ≤ δ) (hw : w ≤ δ) (hy : WF y)
    (h : Inertial δ (pulse a w) y) : ∀ t, y t = false := by
  intro t
  by_contra ht
  have v0 : y (min t a - 1) = false := by
    apply (h.1 _ _).trans
    · simp [pulse]; intro; linarith [min_le_right t a]
    · intro u _ hu2
      have : u < a := by linarith [min_le_right t a]
      simp [pulse]
      constructor <;> intro <;> linarith [min_le_right t a]
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ :=
    first_change hy (by linarith [min_le_left t a]) v0 ht
  have stab := h.2 s hs4
  have ys := h.1 s stab
  have xs : pulse a w s = true := by rw [← ys]; simpa using hs3
  have xsd : pulse a w (s - δ) = true := (stab (s - δ) (le_refl _) (by linarith)).trans xs
  simp [pulse] at xs xsd
  linarith [xs.2, xsd.1]

/-- B4 (long pulses): a pulse of width `w > δ` is propagated, delayed by `δ`. -/
theorem inertial_long {δ a w : ℝ} {y : Sig} (hδ : 0 ≤ δ) (hw : δ < w) (hy : WF y)
    (h : Inertial δ (pulse a w) y) : y = pulse (a + δ) w := by
  -- the four regions
  have r2 : ∀ t, a + δ ≤ t → t < a + w → y t = true := by
    intro t h1 h2
    have := h.1 t (fun u hu1 hu2 => by
      simp [pulse]; constructor <;> intro <;> constructor <;> linarith)
    rw [this]; simp [pulse]; constructor <;> linarith
  have r4 : ∀ t, a + w + δ ≤ t → y t = false := by
    intro t h1
    have := h.1 t (fun u hu1 hu2 => by
      simp [pulse]; constructor <;> intro _ <;> intro <;> linarith)
    rw [this]; simp [pulse]; intro; linarith
  have r1 : ∀ t, t < a + δ → y t = false := by
    intro t h1
    by_contra ht
    have v0 : y (min t a - 1) = false := by
      apply (h.1 _ _).trans
      · simp [pulse]; intro; linarith [min_le_right t a]
      · intro u _ hu2
        simp [pulse]
        constructor <;> intro <;> linarith [min_le_right t a]
    obtain ⟨s, hs1, hs2, hs3, hs4⟩ :=
      first_change hy (by linarith [min_le_left t a]) v0 ht
    have stab := h.2 s hs4
    have ys := h.1 s stab
    have xs : pulse a w s = true := by rw [← ys]; simpa using hs3
    have xsd : pulse a w (s - δ) = true :=
      (stab (s - δ) (le_refl _) (by linarith)).trans xs
    simp [pulse] at xsd
    linarith [xsd.1]
  have r3 : ∀ t, a + w ≤ t → t < a + w + δ → y t = true := by
    intro t h1 h2
    by_contra ht
    have v0 : y (a + δ) = true := r2 _ (le_refl _) (by linarith)
    obtain ⟨s, hs1, hs2, hs3, hs4⟩ := first_change hy (by linarith) v0 ht
    have stab := h.2 s hs4
    have ys := h.1 s stab
    have xs : pulse a w s = false := by rw [← ys]; simpa using hs3
    have xsd : pulse a w (s - δ) = false :=
      (stab (s - δ) (le_refl _) (by linarith)).trans xs
    simp [pulse] at xsd
    have := xsd (by linarith)
    linarith
  funext t
  by_cases c1 : t < a + δ
  · rw [r1 t c1]; simp [pulse]; intro; linarith
  by_cases c2 : t < a + w
  · rw [r2 t (by linarith) c2]; simp [pulse]; constructor <;> linarith
  by_cases c3 : t < a + w + δ
  · rw [r3 t (by linarith) c3]; simp [pulse]; constructor <;> linarith
  · rw [r4 t (by linarith)]; simp [pulse]; intro; linarith

end Formal.Core.TraceReal
