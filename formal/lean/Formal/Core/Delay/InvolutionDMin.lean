import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Formal.Core.Delay.Involution
import Formal.Core.Delay.InvolutionTransfer

/-!
# Involution channels: δmin exists, and the exact input-separation threshold

Track 3, channel (c), follow-up to `Involution.lean` / `InvolutionTransfer.lean`,
where the existence of δmin is the hypothesis `IsDMin d` of every headline theorem.

## Results

1. `exists_dmin`: every `InvolutionPair` has a δmin (`δ↓(-d) = d`, hence also
   `δ↑(-d) = d`, `IsDMin.up_fix`).  Proved from the existing fields only
   (strict monotonicity, `down_lt`, the involution property and causality); no
   continuity field is added.  The proof does not go through continuity + IVT:
   it takes `d = sup {x < δ∞↑ | x < δ↓(-x)}` (completeness of `ℝ`) and uses
   `down_surj` (every value below `δ∞↓` is attained, at an explicit point) to
   rule out `δ↓(-d) ≠ d`.  Surjectivity onto an interval is exactly what rules out
   a jump, which is the content of "strictly monotone + surjective ⇒ continuous".
   `dmin P` is the (unique, `IsDMin.unique`) value, `dmin_spec` its property.
2. Hypothesis-free corollaries (`IsDMin` discharged by `dmin_spec`):
   `pulse_cancel_iff'`, `pulseWidth_small'`, `cancel_iff'`, `transfer_gap'`,
   `transfer_sep'`, `sep_threshold_sharp'`, plus `dmin_pos`, `dmin_lt_infUp`,
   `dmin_lt_infDown`.
3. The exact separation threshold, asymmetric pairs included.  Call an input
   `S`-separated if `t n + S ≤ t (n+1)` for all `n`.
   * `sep_no_cancel`: if `δ∞↑ - δmin < S` and `δ∞↓ - δmin ≤ S` then no
     `S`-separated input ever cancels (`tent n < tent (n+1)` for all `n`).
   * `sep_cancel_down`: if `S < δ∞↓ - δmin`, some `S`-separated input cancels
     (a long high phase, then a negative pulse of width `max S ((δ∞↓-δmin)/2)`;
     transitions 1 and 2 annihilate).
   * `sep_threshold_exact`: no `S`-separated input cancels  ⟺
     `δ∞↑ - δmin < S ∧ δ∞↓ - δmin ≤ S`.
   So the threshold is `max (δ∞↑ - δmin) (δ∞↓ - δmin)` = `max δ∞↑ δ∞↓ - δmin`
   (the sufficient bound of `transfer_sep` was the right number), and it is
   attained (closed) on the falling side when `δ∞↓ > δ∞↑`, but not on the rising
   side.  The asymmetry is the first transition: it gets exactly `δ∞↑`, every
   later delay is strictly below its `δ∞` (`delayAt_succ_lt`).
   * `sep_transfer_exact`: at and above the exact threshold the output is a
     `Chan δmin (max δ∞↑ δ∞↓)` behaviour (lower end `δmin`, weaker than the
     `transfer_sep` band, which needs `S` strictly above `max δ∞ - δmin`).

## What is NOT covered
* "Cancels" means a tentative output not after its predecessor
  (`tent (n+1) ≤ tent n`, the `cancel_iff` event).  The full filtered output
  trace with chained cancellations is still not formalized (as in
  `InvolutionTransfer`).
* Continuity, concavity and `lim δ = δ∞` of the paper are not fields and are not
  used; nothing here says that `δ` is continuous (it is, but that is not proved).
-/

open Formal.Core.DelayPure Formal.Core.DelayInvolutionTransfer

namespace Formal.Core.DelayInvolution.InvolutionPair

variable (P : InvolutionPair)

/-- Non-strict monotonicity of `δ↓` on its domain. -/
theorem down_mono {a b : ℝ} (ha : -P.infUp < a) (hab : a ≤ b) : P.down a ≤ P.down b := by
  rcases lt_or_eq_of_le hab with h | h
  · exact le_of_lt (P.down_strictMono a b ha h)
  · rw [h]

/-- The set whose supremum is δmin. -/
def dminSet : Set ℝ := {x | x < P.infUp ∧ x < P.down (-x)}

theorem dminSet_zero_mem : (0 : ℝ) ∈ P.dminSet :=
  ⟨P.infUp_pos, by rw [neg_zero]; exact P.down_causal⟩

/-- Every element of the set is below `δ↑(0)` (where `δ↓(-δ↑ 0) = 0 < δ↑ 0`). -/
theorem dminSet_lt_up_zero {x : ℝ} (hx : x ∈ P.dminSet) : x < P.up 0 := by
  by_contra hc
  push Not at hc
  have h0 : -P.infDown < (0 : ℝ) := by linarith [P.infDown_pos]
  have hf0 : P.down (-P.up 0) = 0 := by have := P.down_neg_up h0; linarith
  have hm := P.down_mono (a := -x) (b := -P.up 0) (by linarith [hx.1]) (by linarith)
  have := hx.2
  linarith [P.up_causal]

theorem dminSet_bdd : BddAbove P.dminSet := ⟨P.up 0, fun _ hx => le_of_lt (P.dminSet_lt_up_zero hx)⟩

/-- **δmin exists**, from the fields of `InvolutionPair` alone. -/
theorem exists_dmin : ∃ d, P.IsDMin d := by
  set d := sSup P.dminSet with hd
  have hne : P.dminSet.Nonempty := ⟨0, P.dminSet_zero_mem⟩
  have hd0 : 0 ≤ d := le_csSup P.dminSet_bdd P.dminSet_zero_mem
  have hdu : d ≤ P.up 0 := csSup_le hne fun _ hx => le_of_lt (P.dminSet_lt_up_zero hx)
  have hupl : P.up 0 < P.infUp := P.up_lt 0 (by linarith [P.infDown_pos])
  have hmem : -P.infUp < -d := by linarith
  refine ⟨d, hmem, ?_⟩
  have hfd := P.down_lt (-d) hmem
  rcases lt_trichotomy (P.down (-d)) d with hlt | heq | hgt
  · -- δ↓(-d) < d: a smaller upper bound exists
    exfalso
    set m := min d P.infDown with hm
    have hm1 : m ≤ d := min_le_left _ _
    have hm2 : m ≤ P.infDown := min_le_right _ _
    have hfm : P.down (-d) < m := lt_min hlt hfd
    set v := (P.down (-d) + m) / 2 with hv
    obtain ⟨hT, hdT⟩ := P.down_surj (v := v) (by linarith)
    set T := -P.up (-v) with hTdef
    -- x1 = -T < d
    have hx1 : -d < T := by
      have : P.down (-d) < P.down T := by rw [hdT]; linarith
      exact (P.down_lt_iff hmem hT).mp this
    have hb : ∀ x ∈ P.dminSet, x ≤ max (-T) v := by
      intro x hx
      by_contra hc
      push Not at hc
      have h1 : -T < x := lt_of_le_of_lt (le_max_left _ _) hc
      have h2 : v < x := lt_of_le_of_lt (le_max_right _ _) hc
      have := P.down_strictMono (-x) T (by linarith [hx.1]) (by linarith)
      rw [hdT] at this
      linarith [hx.2]
    have := csSup_le hne hb
    rw [← hd] at this
    have : max (-T) v < d := max_lt (by linarith) (by linarith)
    linarith
  · exact heq
  · -- δ↓(-d) > d: a larger element of the set exists
    exfalso
    set v := (d + P.down (-d)) / 2 with hv
    obtain ⟨hT, hdT⟩ := P.down_surj (v := v) (by linarith)
    set T := -P.up (-v) with hTdef
    have hx1 : T < -d := by
      have : P.down T < P.down (-d) := by rw [hdT]; linarith
      exact (P.down_lt_iff hT hmem).mp this
    set x := (d + min (-T) v) / 2 with hx
    have hmn1 : min (-T) v ≤ -T := min_le_left _ _
    have hmn2 : min (-T) v ≤ v := min_le_right _ _
    have hmd : d < min (-T) v := lt_min (by linarith) (by linarith)
    have hxA : x ∈ P.dminSet := by
      refine ⟨by linarith, ?_⟩
      have := P.down_strictMono T (-x) hT (by linarith)
      rw [hdT] at this
      linarith
    have := le_csSup P.dminSet_bdd hxA
    rw [← hd] at this
    linarith

/-- The δmin of an involution pair. -/
noncomputable def dmin : ℝ := Classical.choose P.exists_dmin

theorem dmin_spec : P.IsDMin P.dmin := Classical.choose_spec P.exists_dmin

theorem isDMin_iff {d : ℝ} : P.IsDMin d ↔ d = P.dmin :=
  ⟨fun h => h.unique P.dmin_spec, fun h => h ▸ P.dmin_spec⟩

theorem dmin_pos : 0 < P.dmin := P.dmin_spec.pos
theorem dmin_lt_infUp : P.dmin < P.infUp := P.dmin_spec.lt_infUp
theorem dmin_lt_infDown : P.dmin < P.infDown := P.dmin_spec.lt_infDown
theorem down_dmin : P.down (-P.dmin) = P.dmin := P.dmin_spec.fix
theorem up_dmin : P.up (-P.dmin) = P.dmin := P.dmin_spec.up_fix

/-! ### Hypothesis-free headline theorems -/

variable {P}

/-- `cancel_iff` without the `IsDMin` hypothesis. -/
theorem cancel_iff' (t : ℕ → ℝ) (ht : ∀ n, t n < t (n + 1)) (n : ℕ) :
    P.tent t (n + 1) ≤ P.tent t n ↔ t (n + 1) - P.tent t n ≤ -P.dmin :=
  InvolutionPair.cancel_iff P.dmin_spec t ht n

/-- A single pulse of width `Δ > 0` is cancelled iff `Δ ≤ δ∞↑ - δmin`
(no `IsDMin` hypothesis). -/
theorem pulse_cancel_iff' {Δ : ℝ} (hΔ : 0 < Δ) :
    P.pulseWidth Δ ≤ 0 ↔ Δ ≤ P.infUp - P.dmin :=
  InvolutionPair.pulse_cancel_iff P.dmin_spec hΔ

/-- Arbitrarily short output pulses exist, for every involution pair. -/
theorem pulseWidth_small' {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ Δ, P.infUp - P.dmin < Δ → Δ < P.infUp - P.dmin + η →
      0 < P.pulseWidth Δ ∧ P.pulseWidth Δ < ε :=
  InvolutionPair.pulseWidth_small P.dmin_spec hε

/-- For every involution pair there is a pulse width that is cancelled and one that
is not: the cancellation threshold `δ∞↑ - δmin` lies strictly in `(0, δ∞↑)`. -/
theorem pulse_threshold_pos : 0 < P.infUp - P.dmin ∧ P.infUp - P.dmin < P.infUp := by
  have := P.dmin_lt_infUp; have := P.dmin_pos
  constructor <;> linarith

theorem transfer_gap' {T0 : ℝ} (h0 : -P.dmin < T0) (t : ℕ → ℝ)
    (ht : ∀ n, t n < t (n + 1)) (hT : ∀ n, T0 ≤ t (n + 1) - P.tent t n) :
    (∀ n, P.tent t n < P.tent t (n + 1)) ∧
    (∀ n, min (P.up T0) (P.down T0) ≤ P.tent t n - t n ∧
          P.tent t n - t n ≤ max P.infUp P.infDown) ∧
    (∀ N, Chan (min (P.up T0) (P.down T0)) (max P.infUp P.infDown)
            (sigOf N t) (sigOf N (P.tent t))) :=
  transfer_gap P.dmin_spec h0 t ht hT

/-- `transfer_sep` without the `IsDMin` hypothesis. -/
theorem transfer_sep' {S : ℝ} (hS : max P.infUp P.infDown - P.dmin < S)
    (t : ℕ → ℝ) (ht : ∀ n, t n + S ≤ t (n + 1)) :
    (∀ n, P.tent t n < P.tent t (n + 1)) ∧
    (∀ n, min (P.up (S - max P.infUp P.infDown)) (P.down (S - max P.infUp P.infDown))
            ≤ P.tent t n - t n ∧ P.tent t n - t n ≤ max P.infUp P.infDown) ∧
    (∀ N, Chan (min (P.up (S - max P.infUp P.infDown)) (P.down (S - max P.infUp P.infDown)))
            (max P.infUp P.infDown) (sigOf N t) (sigOf N (P.tent t))) :=
  transfer_sep P.dmin_spec hS t ht

theorem sep_threshold_sharp' {S : ℝ} (hS0 : 0 < S) (hS : S ≤ P.infUp - P.dmin) :
    (∀ n, spaced S n + S ≤ spaced S (n + 1)) ∧
    P.tent (spaced S) 1 ≤ P.tent (spaced S) 0 :=
  sep_threshold_sharp P.dmin_spec hS0 hS

/-! ### The exact input-separation threshold -/

/-- Delay of transition `n`: `δ∞↑` for `n = 0`, strictly below `δ∞` of its
direction afterwards. -/
theorem tent_sub_le (t : ℕ → ℝ) (ht : ∀ n, t n < t (n + 1)) (n : ℕ) :
    P.tent t n - t n ≤ P.infAt n := by
  have := P.tent_le t ht n; linarith

theorem tent_sub_lt (t : ℕ → ℝ) (ht : ∀ n, t n < t (n + 1)) (n : ℕ) :
    P.tent (t) (n + 1) - t (n + 1) < P.infAt (n + 1) := by
  rw [tent_succ_sub]
  exact P.delayAt_succ_lt n (P.dom_ok t ht n)

/-- **Sufficiency, exact form.**  If `δ∞↑ - δmin < S` and `δ∞↓ - δmin ≤ S`, an
`S`-separated input never cancels. -/
theorem sep_no_cancel {S : ℝ} (hup : P.infUp - P.dmin < S) (hdn : P.infDown - P.dmin ≤ S)
    (t : ℕ → ℝ) (ht : ∀ n, t n + S ≤ t (n + 1)) :
    ∀ n, -P.dmin < t (n + 1) - P.tent t n := by
  have hSpos : 0 < S := by linarith [P.dmin_lt_infUp]
  have ht' : ∀ n, t n < t (n + 1) := fun n => by linarith [ht n]
  intro n
  cases n with
  | zero =>
    have := ht 0
    rw [tent_zero]
    linarith
  | succ k =>
    have h1 := tent_sub_lt (P := P) t ht' k
    have h2 := ht (k + 1)
    unfold InvolutionPair.infAt at h1
    split_ifs at h1
    · linarith
    · linarith

theorem sep_no_cancel_tent {S : ℝ} (hup : P.infUp - P.dmin < S) (hdn : P.infDown - P.dmin ≤ S)
    (t : ℕ → ℝ) (ht : ∀ n, t n + S ≤ t (n + 1)) :
    ∀ n, P.tent t n < P.tent t (n + 1) := by
  have hSpos : 0 < S := by linarith [P.dmin_lt_infUp]
  have ht' : ∀ n, t n < t (n + 1) := fun n => by linarith [ht n]
  intro n
  by_contra hc
  push Not at hc
  have := (cancel_iff' t ht' n).mp hc
  linarith [sep_no_cancel hup hdn t ht n]

/-- At or above the exact threshold, the output is a `Chan δmin (max δ∞↑ δ∞↓)`
behaviour of the input (every delay is `≥ δmin`). -/
theorem sep_transfer_exact {S : ℝ} (hup : P.infUp - P.dmin < S) (hdn : P.infDown - P.dmin ≤ S)
    (t : ℕ → ℝ) (ht : ∀ n, t n + S ≤ t (n + 1)) (N : ℕ) :
    Chan P.dmin (max P.infUp P.infDown) (sigOf N t) (sigOf N (P.tent t)) := by
  have hSpos : 0 < S := by linarith [P.dmin_lt_infUp]
  have ht' : ∀ n, t n < t (n + 1) := fun n => by linarith [ht n]
  have hnc := sep_no_cancel_tent hup hdn t ht
  have hgap := sep_no_cancel hup hdn t ht
  have hlo : ∀ n, P.dmin ≤ P.tent t n - t n := by
    intro n
    cases n with
    | zero => rw [tent_zero]; linarith [P.dmin_lt_infUp]
    | succ k =>
      rw [tent_succ_sub]
      have hg := hgap k
      unfold InvolutionPair.delayAt
      split_ifs
      · have := P.up_strictMono _ _ P.dmin_spec.mem_up hg
        rw [P.up_dmin] at this; linarith
      · have := P.down_strictMono _ _ P.dmin_spec.mem hg
        rw [P.down_dmin] at this; linarith
  have hhi : ∀ n, P.tent t n - t n ≤ max P.infUp P.infDown := fun n =>
    le_trans (tent_sub_le (P := P) t ht' n) (infAt_le_max (P := P) n)
  exact chan_sigOf (strictMono_nat_of_lt_succ ht')
    (monotone_nat_of_le_succ fun n => le_of_lt (hnc n)) hlo hhi N

/-- The witness for the falling side: high from `0` to `L`, then a negative pulse
of width `s`, then transitions every `s`. -/
noncomputable def negPulse (L s : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else L + ((n : ℝ) - 1) * s

theorem negPulse_sep {L s : ℝ} (hs : 0 < s) (hL : s ≤ L) (n : ℕ) :
    negPulse L s n + s ≤ negPulse L s (n + 1) := by
  unfold negPulse
  rw [if_neg (Nat.succ_ne_zero n)]
  by_cases hn : n = 0
  · subst hn; rw [if_pos rfl]; push_cast; linarith
  · rw [if_neg hn]; push_cast; linarith

/-- **Necessity on the falling side.**  If `S < δ∞↓ - δmin`, some `S`-separated
input cancels (its transitions 1 and 2 annihilate). -/
theorem sep_cancel_down {S : ℝ} (hS : S < P.infDown - P.dmin) :
    ∃ t : ℕ → ℝ, (∀ n, t n + S ≤ t (n + 1)) ∧ (∀ n, t n < t (n + 1)) ∧
      P.tent t 2 ≤ P.tent t 1 := by
  have hdD := P.dmin_lt_infDown
  set s := max S ((P.infDown - P.dmin) / 2) with hsdef
  have hs1 : S ≤ s := le_max_left _ _
  have hs2 : (P.infDown - P.dmin) / 2 ≤ s := le_max_right _ _
  have hspos : 0 < s := by linarith
  have hsD : s < P.infDown - P.dmin := max_lt hS (by linarith)
  obtain ⟨hT1, hdT1⟩ := P.down_surj (v := s + P.dmin) (by linarith)
  set T1 := -P.up (-(s + P.dmin)) with hT1def
  set L := max (T1 + P.infUp) s with hLdef
  have hL1 : T1 + P.infUp ≤ L := le_max_left _ _
  have hL2 : s ≤ L := le_max_right _ _
  have hsep : ∀ n, negPulse L s n + s ≤ negPulse L s (n + 1) := negPulse_sep hspos hL2
  have ht : ∀ n, negPulse L s n < negPulse L s (n + 1) := fun n => by linarith [hsep n]
  refine ⟨negPulse L s, fun n => by linarith [hsep n], ht, ?_⟩
  apply (cancel_iff' (negPulse L s) ht 1).mpr
  have e0 : negPulse L s 0 = 0 := by simp [negPulse]
  have e1 : negPulse L s 1 = L := by simp [negPulse]
  have e2 : negPulse L s 2 = L + s := by
    simp only [negPulse, if_neg (show (2 : ℕ) ≠ 0 by omega)]; push_cast; ring1
  have hd1 : P.delayAt 1 = P.down := by simp [InvolutionPair.delayAt]
  have htent1 : P.tent (negPulse L s) 1 = L + P.down (L - P.infUp) := by
    show negPulse L s 1 + P.delayAt 1 (negPulse L s 1 - P.tent (negPulse L s) 0) = _
    rw [hd1, tent_zero, e0, e1, zero_add]
  rw [htent1, e2]
  have := P.down_mono (a := T1) (b := L - P.infUp) hT1 (by linarith)
  rw [hdT1] at this
  linarith

/-- **The exact threshold.**  No `S`-separated input ever cancels iff
`δ∞↑ - δmin < S` and `δ∞↓ - δmin ≤ S`. -/
theorem sep_threshold_exact (S : ℝ) :
    (∀ t : ℕ → ℝ, (∀ n, t n + S ≤ t (n + 1)) → ∀ n, P.tent t n < P.tent t (n + 1)) ↔
      (P.infUp - P.dmin < S ∧ P.infDown - P.dmin ≤ S) := by
  constructor
  · intro H
    have hdU := P.dmin_lt_infUp
    refine ⟨?_, ?_⟩
    · by_contra hc
      push Not at hc
      set s := max S ((P.infUp - P.dmin) / 2) with hsdef
      have hs1 : S ≤ s := le_max_left _ _
      have hs2 : (P.infUp - P.dmin) / 2 ≤ s := le_max_right _ _
      have hsU : s ≤ P.infUp - P.dmin := max_le hc (by linarith)
      obtain ⟨hsep, hcan⟩ := sep_threshold_sharp' (S := s) (by linarith) hsU
      have := H (spaced s) (fun n => by linarith [hsep n]) 0
      linarith
    · by_contra hc
      push Not at hc
      obtain ⟨t, hsep, _, hcan⟩ := sep_cancel_down hc
      have := H t hsep 1
      linarith
  · rintro ⟨hup, hdn⟩ t ht
    exact sep_no_cancel_tent hup hdn t ht

end Formal.Core.DelayInvolution.InvolutionPair
