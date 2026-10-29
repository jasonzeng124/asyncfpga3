import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Formal.Core.Delay.Involution
import Formal.Core.Delay.InvolutionTransfer
import Formal.Core.Delay.InvolutionDMin

/-!
# Involution channels: full trace semantics (with cancellation)

Track 3, channel (c), follow-up to `Involution.lean`, `InvolutionTransfer.lean` and
`InvolutionDMin.lean`, which only formalize the tentative output times
`InvolutionPair.tent` and the local cancellation event `tent (n+1) ≤ tent n`.
Here the channel maps a whole input trace to a whole output trace.

## Semantics

Input: `N` transitions at times `t 0 < t 1 < ... < t (N-1)` (the hypotheses are stated
on a strictly increasing `t : ℕ → ℝ`; only `t 0 .. t (N-1)` matter, see
`outList_congr`), input initially low, so transition `n` is rising iff `n` is even.
Tentative outputs `tent n` as in `Involution.lean` (Függer/Najvirt/Nowak/Schmid: `T` is
measured from the previous *tentative* output, whether or not that one is later
cancelled).  Transition `n` is **cancelled with its successor** (`CN N t n`) if
`n + 1 < N` and `tent (n+1) ≤ tent n` (the pair would reorder, so both annihilate).
A transition **survives** (`Surv`) if it is cancelled neither with its successor nor
with its predecessor.  The output trace `outList` is the list of `tent n` of the
surviving `n`, in index order; the output signal starts low and toggles at each of
them.

The paper's rule "a transition that would overtake the previous output transition
cancels with it" is ambiguous in general for chains (does a third transition cancel
against a transition already cancelled?).  `cancel_no_chain` shows the question never
arises for involution channels: two consecutive cancellations `(n, n+1)` and
`(n+1, n+2)` are impossible.  So the cancelled transitions form disjoint consecutive
pairs, and every reasonable reading of the rule (pairwise neighbour rule, a stack-based
scheduler) gives this output.  The key fact is the **window lemma**: transition `n`
survives iff `t n + δmin < tent n < t (n+1) + δmin` (`surv_lo`, `surv_hi`,
`surv_of_window`); the windows of different `n` are disjoint and ordered.

## Results
1. Well-formedness: `outList_sorted` (strictly increasing output times) and
   `surv_parity` (the number of surviving transitions before a surviving `n` has the
   parity of `n`, so the output toggles alternate rising/falling exactly as the
   input transitions they come from; the first survivor is rising).
2. Agreement with the existing semantics: `outList_one` (one transition gives
   `[t 0 + δ∞↑]`), `outList_two` (two transitions: `[]` if `tent 1 ≤ tent 0`, else
   `[tent 0, tent 1]`), `outList_of_noCancel` (no cancellation: the output is exactly
   `tent 0, ..., tent (N-1)`), and every output time is a `tent n`.
3. Short pulses: `pulse_out` (an isolated pulse `[a, a+Δ]` gives `[]` iff
   `Δ ≤ δ∞↑ - δmin`, else `[a + δ∞↑, a + δ∞↑ + pulseWidth Δ]`), output width
   strictly increasing in `Δ` (`pulseWidth_strictMono`) and tending to 0
   (`pulseWidth_small'`).
4. Composition with a fixed pure delay: `outList_shift_input` (delay then involution
   = involution then delay: time invariance) and `outList_shiftPair` (involution then
   pure delay `D ≥ 0` is again an involution channel, `shiftPair D P`, with
   `δ'(T) = D + δ(T + D)`, `δ'∞ = δ∞ + D`, `δ'min = δmin + D`: `shiftPair_dmin`).
5. Transfer from the trace semantics: `trace_transfer_sep`: if consecutive input
   transitions are `≥ S` apart, `S > max δ∞↑ δ∞↓ - δmin`, the full output trace
   (with the cancellation rule) is a `DelayPure.Chan` behaviour of the input with
   band `[min (δ↑ T0) (δ↓ T0), max δ∞↑ δ∞↓]`, `T0 = S - max δ∞↑ δ∞↓`.
6. A chained-history example on `ratPair` (`rat_memory`): a cancelled pulse still
   shortens the delay of the next transition.

## What is NOT covered
* The relation to `TraceEvent.Sig` (Core's event-list trace type) is not made; the
  output is related to `DelayPure.Sig` only (through `listSig`).
* Only one channel, no circuit (no feedback, no zero-time gates); the circuit-level
  SPF impossibility theorem of the paper is not attempted.
* Continuity of the output in the input times is not stated.
-/

namespace Formal.Core.DelayInvolution.InvolutionPair

open Formal.Core.DelayInvolution Formal.Core.DelayPure Formal.Core.DelayInvolutionTransfer

noncomputable section

variable (P : InvolutionPair)

/-! ## Definitions -/

/-- Transition `n` (of the first `N`) is cancelled together with transition `n+1`. -/
def CN (N : ℕ) (t : ℕ → ℝ) (n : ℕ) : Prop := n + 1 < N ∧ P.tent t (n + 1) ≤ P.tent t n

/-- Transition `n` survives: it is one of the first `N`, and it is cancelled neither
with its successor nor with its predecessor. -/
def Surv (N : ℕ) (t : ℕ → ℝ) (n : ℕ) : Prop :=
  n < N ∧ ¬ P.CN N t n ∧ ∀ m, n = m + 1 → ¬ P.CN N t m

/-- `Surv` is not decidable (it quantifies over reals and indices); the trace is a
noncomputable function, so we use classical decidability. -/
noncomputable instance survDecidable (N : ℕ) (t : ℕ → ℝ) (n : ℕ) : Decidable (P.Surv N t n) :=
  Classical.propDecidable _

/-- Indices of the surviving transitions, increasing. -/
def survIdx (N : ℕ) (t : ℕ → ℝ) : List ℕ := (List.range N).filter (fun n => decide (P.Surv N t n))

/-- **The output trace**: times of the surviving output transitions, in index order.
The output signal starts low and toggles at each of them. -/
def outList (N : ℕ) (t : ℕ → ℝ) : List ℝ := (P.survIdx N t).map (P.tent t)

/-- Number of surviving transitions among the first `n` indices. -/
def survBelow (N : ℕ) (t : ℕ → ℝ) (n : ℕ) : ℕ :=
  ((List.range n).filter (fun m => decide (P.Surv N t m))).length

/-! ## Basic facts about `tent` -/

theorem tent_zero' (t : ℕ → ℝ) : P.tent t 0 = t 0 + P.infUp := rfl

theorem tent_succ' (t : ℕ → ℝ) (n : ℕ) :
    P.tent t (n + 1) = t (n + 1) + P.delayAt (n + 1) (t (n + 1) - P.tent t n) := rfl

/-- `tent t n` depends only on `t 0, ..., t n`. -/
theorem tent_congr {t u : ℕ → ℝ} {n : ℕ} (h : ∀ m, m ≤ n → t m = u m) :
    P.tent t n = P.tent u n := by
  induction n with
  | zero => simp [InvolutionPair.tent, h 0 (le_refl 0)]
  | succ n ih =>
    rw [tent_succ', tent_succ', ih (fun m hm => h m (by omega)), h (n + 1) (le_refl _)]

variable {P}

/-- `δ(T) ≤ δmin ↔ T ≤ -δmin`, for the delay function of transition `n+1`, on its domain. -/
theorem delayAt_le_dmin_iff (n : ℕ) {T : ℝ} (hT : -P.infAt n < T) :
    P.delayAt (n + 1) T ≤ P.dmin ↔ T ≤ -P.dmin := by
  have hd := P.dmin_spec
  unfold InvolutionPair.delayAt InvolutionPair.infAt at *
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · rw [ite_eq_left hn] at hT
    rw [ite_eq_right (by omega)]
    have := P.down_lt_iff hd.mem hT
    rw [hd.fix] at this
    constructor
    · intro h; by_contra hc; push_neg at hc; linarith [this.mpr hc]
    · intro h; by_contra hc; push_neg at hc; linarith [this.mp hc]
  · rw [ite_eq_right (by omega)] at hT
    rw [ite_eq_left (by omega)]
    have := P.up_lt_iff hd.mem_up hT
    rw [hd.up_fix] at this
    constructor
    · intro h; by_contra hc; push_neg at hc; linarith [this.mpr hc]
    · intro h; by_contra hc; push_neg at hc; linarith [this.mp hc]

variable (t : ℕ → ℝ) (ht : ∀ n, t n < t (n + 1))
include ht

/-- Cancellation, seen from the later transition: `tent (n+1) ≤ tent n` iff the
tentative output of `n+1` is at most `δmin` after its input. -/
theorem cancel_iff_late (n : ℕ) :
    P.tent t (n + 1) ≤ P.tent t n ↔ P.tent t (n + 1) ≤ t (n + 1) + P.dmin := by
  rw [InvolutionPair.cancel_iff' t ht n]
  have hT := P.dom_ok t ht n
  rw [← delayAt_le_dmin_iff n hT, tent_succ']
  constructor <;> intro h <;> linarith

/-- Cancellation, seen from the earlier transition: `tent (n+1) ≤ tent n` iff the
tentative output of `n` is at least `δmin` after the next input. -/
theorem cancel_iff_early (n : ℕ) :
    P.tent t (n + 1) ≤ P.tent t n ↔ t (n + 1) + P.dmin ≤ P.tent t n := by
  rw [InvolutionPair.cancel_iff' t ht n]
  constructor <;> intro h <;> linarith

/-- **No chained cancellation**: transition `n+1` cannot cancel with both `n` and
`n+2`. -/
theorem cancel_no_chain (n : ℕ) (h1 : P.tent t (n + 1) ≤ P.tent t n) :
    P.tent t (n + 1) < P.tent t (n + 2) := by
  have a := (cancel_iff_late t ht n).mp h1
  by_contra hc
  push_neg at hc
  have b := (cancel_iff_early t ht (n + 1)).mp hc
  linarith [ht (n + 1)]

theorem CN_no_chain {N : ℕ} {n : ℕ} (h : P.CN N t n) : ¬ P.CN N t (n + 1) := by
  intro h'
  have := cancel_no_chain t ht n h.2
  linarith [h'.2]

/-! ## The window lemma -/

/-- A survivor's output is more than `δmin` after its input. -/
theorem surv_lo {N n : ℕ} (h : P.Surv N t n) : t n + P.dmin < P.tent t n := by
  cases n with
  | zero => rw [tent_zero']; linarith [P.dmin_lt_infUp]
  | succ k =>
    have hk : ¬ P.CN N t k := h.2.2 k rfl
    have hlt : P.tent t k < P.tent t (k + 1) := by
      by_contra hc; push_neg at hc; exact hk ⟨h.1, hc⟩
    by_contra hc; push_neg at hc
    have := (cancel_iff_late t ht k).mpr hc
    linarith

/-- A survivor's output is less than `δmin` after the next input. -/
theorem surv_hi {N n : ℕ} (h : P.Surv N t n) (hn : n + 1 < N) :
    P.tent t n < t (n + 1) + P.dmin := by
  have hlt : P.tent t n < P.tent t (n + 1) := by
    by_contra hc; push_neg at hc; exact h.2.1 ⟨hn, hc⟩
  by_contra hc; push_neg at hc
  have := (cancel_iff_early t ht n).mpr hc
  linarith

/-- Converse of the window lemma. -/
theorem surv_of_window {N n : ℕ} (hn : n < N) (hlo : n = 0 ∨ t n + P.dmin < P.tent t n)
    (hhi : n + 1 < N → P.tent t n < t (n + 1) + P.dmin) : P.Surv N t n := by
  refine ⟨hn, ?_, ?_⟩
  · intro hc
    have := (cancel_iff_early t ht n).mp hc.2
    linarith [hhi hc.1]
  · intro m hm hc
    subst hm
    have := (cancel_iff_late t ht m).mp hc.2
    rcases hlo with h0 | h0
    · omega
    · linarith

/-- Survivors' output times are strictly increasing in the index. -/
theorem surv_strictMono {N m n : ℕ} (hm : P.Surv N t m) (hn : P.Surv N t n) (hmn : m < n) :
    P.tent t m < P.tent t n := by
  have hmono : StrictMono t := strictMono_nat_of_lt_succ ht
  have h1 := surv_hi t ht hm (by have := hn.1; omega)
  have h2 := surv_lo t ht hn
  have h3 : t (m + 1) ≤ t n := hmono.monotone (by omega)
  linarith

/-! ## 1. Well-formedness -/

theorem survIdx_sorted (N : ℕ) : (P.survIdx N t).Pairwise (· < ·) :=
  List.Pairwise.filter _ (List.pairwise_lt_range)

theorem mem_survIdx {N n : ℕ} : n ∈ P.survIdx N t ↔ P.Surv N t n := by
  unfold survIdx
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- **Well-formedness (order)**: the output transition times are strictly increasing. -/
theorem outList_sorted (N : ℕ) : (P.outList N t).Pairwise (· < ·) := by
  unfold outList
  rw [List.pairwise_map]
  exact (survIdx_sorted t ht N).imp_of_mem (fun ha hb hab =>
    surv_strictMono t ht ((mem_survIdx t ht).mp ha) ((mem_survIdx t ht).mp hb) hab)

/-- Every output time is the tentative output of a surviving input transition. -/
theorem mem_outList {N : ℕ} {s : ℝ} :
    s ∈ P.outList N t ↔ ∃ n, P.Surv N t n ∧ P.tent t n = s := by
  unfold outList
  simp only [List.mem_map]
  constructor
  · rintro ⟨n, hn, e⟩; exact ⟨n, (mem_survIdx t ht).mp hn, e⟩
  · rintro ⟨n, hn, e⟩; exact ⟨n, (mem_survIdx t ht).mpr hn, e⟩

theorem survBelow_succ (N n : ℕ) :
    P.survBelow N t (n + 1) = P.survBelow N t n + (if P.Surv N t n then 1 else 0) := by
  unfold survBelow
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : P.Surv N t n <;> simp [h]

open scoped Classical in
/-- The parity invariant behind alternation. -/
theorem survBelow_parity (N : ℕ) :
    ∀ n, n ≤ N →
      (P.survBelow N t n + (if ∃ m, n = m + 1 ∧ P.CN N t m then 1 else 0)) % 2 = n % 2 := by
  intro n
  induction n with
  | zero => intro _; simp [survBelow]
  | succ n ih =>
    intro hn
    have ih := ih (by omega)
    rw [survBelow_succ t ht]
    have hpc : (∃ m, n + 1 = m + 1 ∧ P.CN N t m) ↔ P.CN N t n :=
      ⟨fun ⟨m, hm, h⟩ => by rw [show n = m by omega]; exact h, fun h => ⟨n, rfl, h⟩⟩
    by_cases hprev : ∃ m, n = m + 1 ∧ P.CN N t m
    · obtain ⟨m, hm, hcm⟩ := hprev
      have hnc : ¬ P.CN N t n := by subst hm; exact CN_no_chain t ht hcm
      have hns : ¬ P.Surv N t n := fun hs => hs.2.2 m hm hcm
      rw [if_pos ⟨m, hm, hcm⟩] at ih
      rw [if_neg hns, if_neg (fun h => hnc (hpc.mp h))]
      omega
    · rw [if_neg hprev] at ih
      by_cases hc : P.CN N t n
      · have hns : ¬ P.Surv N t n := fun hs => hs.2.1 hc
        rw [if_neg hns, if_pos (hpc.mpr hc)]
        omega
      · have hs : P.Surv N t n :=
          ⟨by omega, hc, fun m hm hcm => hprev ⟨m, hm, hcm⟩⟩
        rw [if_pos hs, if_neg (fun h => hc (hpc.mp h))]
        omega

/-- **Well-formedness (alternation)**: before a surviving transition `n`, the number of
surviving output transitions has the parity of `n`.  So the output (which starts low
and toggles at each survivor) makes, at `tent n`, exactly the transition of input
transition `n`: rising for even `n`, falling for odd `n`. -/
theorem surv_parity {N n : ℕ} (h : P.Surv N t n) : P.survBelow N t n % 2 = n % 2 := by
  have := survBelow_parity t ht N n (le_of_lt h.1)
  rw [if_neg (fun ⟨m, hm, hc⟩ => h.2.2 m hm hc)] at this
  simpa using this

/-- Corollary: the first survivor is a rising transition (even index), and between two
consecutive survivors the index changes parity. -/
theorem first_surv_even {N n : ℕ} (h : P.Surv N t n) (hfirst : ∀ m, m < n → ¬ P.Surv N t m) :
    n % 2 = 0 := by
  have hz : P.survBelow N t n = 0 := by
    unfold survBelow
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro m hm
    simp only [List.mem_range] at hm
    simpa using hfirst m hm
  have := surv_parity t ht h
  omega

omit ht in
/-- The output depends only on `t 0, ..., t (N-1)`. -/
theorem outList_congr {N : ℕ} {u : ℕ → ℝ} (h : ∀ m, m < N → t m = u m) :
    P.outList N t = P.outList N u := by
  have ht' : ∀ n, n < N → P.tent t n = P.tent u n := fun n hn =>
    P.tent_congr (fun m hm => h m (by omega))
  have hcn : ∀ n, P.CN N t n ↔ P.CN N u n := by
    intro n; unfold CN
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← ht' _ h1, ← ht' _ (by omega)]; exact h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [ht' _ h1, ht' _ (by omega)]; exact h2⟩
  have hs : ∀ n, P.Surv N t n ↔ P.Surv N u n := by
    intro n; unfold Surv; simp only [hcn]
  unfold outList survIdx
  rw [List.map_inj_left.mpr ?_]
  · congr 1
    apply List.filter_congr
    intro n _
    simp only [hs]
  · intro n hn
    simp only [List.mem_filter, List.mem_range] at hn
    exact ht' n hn.1

/-! ## 2. Agreement with `tent` -/

omit ht in
/-- A single transition: output `[t 0 + δ∞↑]`. -/
theorem outList_one : P.outList 1 t = [t 0 + P.infUp] := by
  have hs : P.Surv 1 t 0 := ⟨by omega, fun h => by have := h.1; omega, fun m hm => by omega⟩
  simp [outList, survIdx, hs, tent_zero']

/-- Two transitions: the pulse is cancelled (output `[]`) if `tent 1 ≤ tent 0`,
otherwise the output is `[tent 0, tent 1]`. -/
theorem outList_two :
    P.outList 2 t = if P.tent t 1 ≤ P.tent t 0 then [] else [P.tent t 0, P.tent t 1] := by
  by_cases hc : P.tent t 1 ≤ P.tent t 0
  · have h0 : ¬ P.Surv 2 t 0 := fun h => h.2.1 ⟨by omega, hc⟩
    have h1 : ¬ P.Surv 2 t 1 := fun h => h.2.2 0 rfl ⟨by omega, hc⟩
    simp [outList, survIdx, List.range_succ, h0, h1, hc]
  · have h0 : P.Surv 2 t 0 := ⟨by omega, fun h => hc h.2, fun m hm => by omega⟩
    have h1 : P.Surv 2 t 1 :=
      ⟨by omega, fun h => by have := h.1; omega, fun m hm h => by
        rw [show m = 0 by omega] at h; exact hc h.2⟩
    simp [outList, survIdx, List.range_succ, h0, h1, hc]

/-- If nothing cancels, the output is exactly `tent 0, ..., tent (N-1)`. -/
theorem outList_of_noCancel {N : ℕ} (h : ∀ n, n + 1 < N → P.tent t n < P.tent t (n + 1)) :
    P.outList N t = (List.range N).map (P.tent t) := by
  have hs : ∀ n, n < N → P.Surv N t n := by
    intro n hn
    refine ⟨hn, fun hc => ?_, fun m hm hc => ?_⟩
    · linarith [h n hc.1, hc.2]
    · linarith [h m hc.1, hc.2]
  unfold outList survIdx
  congr 1
  rw [List.filter_eq_self]
  intro n hn
  simp only [List.mem_range] at hn
  simpa using hs n hn

/-! ## 3. Isolated pulses -/

omit ht in
/-- The output of an isolated input pulse `[a, a + Δ]` (`Δ > 0`, input initially low):
cancelled iff `Δ ≤ δ∞↑ - δmin`; otherwise a pulse starting `δ∞↑` after `a` of width
`pulseWidth Δ` (strictly increasing in `Δ`, `pulseWidth_strictMono`, and tending to 0
at the threshold, `pulseWidth_small'`). -/
theorem pulse_out (a Δ : ℝ) (hΔ : 0 < Δ) (t : ℕ → ℝ) (h0 : t 0 = a) (h1 : t 1 = a + Δ) :
    (Δ ≤ P.infUp - P.dmin → P.outList 2 t = []) ∧
    (P.infUp - P.dmin < Δ →
      P.outList 2 t = [a + P.infUp, a + P.infUp + P.pulseWidth Δ]) := by
  have e0 : P.tent t 0 = a + P.infUp := by rw [tent_zero', h0]
  have hd1 : P.delayAt 1 = P.down := by simp [InvolutionPair.delayAt]
  have e1 : P.tent t 1 = a + P.infUp + P.pulseWidth Δ := by
    rw [tent_succ', e0, hd1, h1, InvolutionPair.pulseWidth,
      show a + Δ - (a + P.infUp) = Δ - P.infUp by ring]
    ring
  have key : P.tent t 1 ≤ P.tent t 0 ↔ Δ ≤ P.infUp - P.dmin := by
    rw [e0, e1, ← InvolutionPair.pulse_cancel_iff' hΔ]
    constructor <;> intro h <;> linarith
  rw [outList_two]
  refine ⟨fun h => by rw [if_pos (key.mpr h)], fun h => ?_⟩
  rw [if_neg (fun hc => by linarith [key.mp hc]), e0, e1]

/-! ## 4. Composition with a fixed pure delay -/

omit ht in
theorem tent_shift_input (D : ℝ) (n : ℕ) :
    P.tent (fun m => t m + D) n = P.tent t n + D := by
  induction n with
  | zero => simp [tent_zero']; ring
  | succ n ih =>
    rw [tent_succ', tent_succ', ih, show t (n + 1) + D - (P.tent t n + D)
      = t (n + 1) - P.tent t n by ring]
    ring

omit ht in
/-- **Time invariance**: delaying the input by `D` delays the output by `D`, so a pure
delay `D` followed by the involution channel equals the involution channel followed by
the pure delay `D`. -/
theorem outList_shift_input (D : ℝ) (N : ℕ) :
    P.outList N (fun m => t m + D) = (P.outList N t).map (· + D) := by
  have hcn : ∀ n, P.CN N (fun m => t m + D) n ↔ P.CN N t n := by
    intro n; unfold CN; rw [tent_shift_input, tent_shift_input]
    constructor <;> rintro ⟨a, b⟩ <;> exact ⟨a, by linarith⟩
  have hs : ∀ n, P.Surv N (fun m => t m + D) n ↔ P.Surv N t n := by
    intro n; unfold Surv; simp only [hcn]
  unfold outList survIdx
  rw [List.map_map]
  have : (List.range N).filter (fun n => decide (P.Surv N (fun m => t m + D) n))
      = (List.range N).filter (fun n => decide (P.Surv N t n)) := by
    apply List.filter_congr; intro n _; simp only [hs]
  rw [this]
  apply List.map_congr_left
  intro n _
  simp [tent_shift_input]

end

noncomputable section

variable (P : InvolutionPair)

/-- The involution channel `P` followed by a pure delay `D ≥ 0`, as an involution pair:
`δ'(T) = D + δ(T + D)`. -/
def shiftPair (D : ℝ) (hD : 0 ≤ D) : InvolutionPair where
  up T := D + P.up (T + D)
  down T := D + P.down (T + D)
  infUp := P.infUp + D
  infDown := P.infDown + D
  infUp_pos := by linarith [P.infUp_pos]
  infDown_pos := by linarith [P.infDown_pos]
  up_lt T hT := by have := P.up_lt (T + D) (by linarith); linarith
  down_lt T hT := by have := P.down_lt (T + D) (by linarith); linarith
  up_strictMono a b ha hab := by
    have := P.up_strictMono (a + D) (b + D) (by linarith) (by linarith); linarith
  down_strictMono a b ha hab := by
    have := P.down_strictMono (a + D) (b + D) (by linarith) (by linarith); linarith
  inv_up T hT := by
    have := P.inv_up (T + D) (by linarith)
    rw [show -(D + P.down (T + D)) + D = -P.down (T + D) by ring]
    linarith
  inv_down T hT := by
    have := P.inv_down (T + D) (by linarith)
    rw [show -(D + P.up (T + D)) + D = -P.up (T + D) by ring]
    linarith
  up_causal := by
    have h0 : -P.infDown < (0 : ℝ) := by linarith [P.infDown_pos]
    rcases lt_or_eq_of_le hD with h | h
    · have := P.up_strictMono 0 D h0 h; linarith [P.up_causal]
    · rw [← h]; simp [P.up_causal]
  down_causal := by
    have h0 : -P.infUp < (0 : ℝ) := by linarith [P.infUp_pos]
    rcases lt_or_eq_of_le hD with h | h
    · have := P.down_strictMono 0 D h0 h; linarith [P.down_causal]
    · rw [← h]; simp [P.down_causal]

variable {P}

theorem shiftPair_delayAt (D : ℝ) (hD : 0 ≤ D) (m : ℕ) (T : ℝ) :
    (P.shiftPair D hD).delayAt m T = D + P.delayAt m (T + D) := by
  unfold InvolutionPair.delayAt
  split_ifs <;> rfl

/-- `δ'min = δmin + D`. -/
theorem shiftPair_dmin (D : ℝ) (hD : 0 ≤ D) : (P.shiftPair D hD).dmin = P.dmin + D := by
  symm
  rw [← InvolutionPair.isDMin_iff]
  exact ⟨by show -(P.infUp + D) < -(P.dmin + D); linarith [P.dmin_lt_infUp],
    by show D + P.down (-(P.dmin + D) + D) = P.dmin + D
       rw [show -(P.dmin + D) + D = -P.dmin by ring, P.down_dmin]; ring⟩

theorem tent_shiftPair (D : ℝ) (hD : 0 ≤ D) (t : ℕ → ℝ) (n : ℕ) :
    (P.shiftPair D hD).tent t n = P.tent t n + D := by
  induction n with
  | zero => show t 0 + (P.infUp + D) = t 0 + P.infUp + D; ring
  | succ n ih =>
    rw [tent_succ', tent_succ', ih, shiftPair_delayAt,
      show t (n + 1) - (P.tent t n + D) + D = t (n + 1) - P.tent t n by ring]
    ring

/-- **Involution channel followed by a pure delay `D ≥ 0`** is the involution channel
`shiftPair D P`, on every input trace (with cancellations). -/
theorem outList_shiftPair (D : ℝ) (hD : 0 ≤ D) (t : ℕ → ℝ) (N : ℕ) :
    (P.shiftPair D hD).outList N t = (P.outList N t).map (· + D) := by
  have hcn : ∀ n, (P.shiftPair D hD).CN N t n ↔ P.CN N t n := by
    intro n; unfold CN; rw [tent_shiftPair, tent_shiftPair]
    constructor <;> rintro ⟨a, b⟩ <;> exact ⟨a, by linarith⟩
  have hs : ∀ n, (P.shiftPair D hD).Surv N t n ↔ P.Surv N t n := by
    intro n; unfold Surv; simp only [hcn]
  unfold outList survIdx
  rw [List.map_map]
  have : (List.range N).filter (fun n => decide ((P.shiftPair D hD).Surv N t n))
      = (List.range N).filter (fun n => decide (P.Surv N t n)) := by
    apply List.filter_congr; intro n _; simp only [hs]
  rw [this]
  apply List.map_congr_left
  intro n _
  simp [tent_shiftPair]

/-! ## 5. The transfer lemma from the trace semantics -/

/-- `cnt` (used by `sigOf`) as a list count. -/
theorem cnt_eq_countP (N : ℕ) (u : ℕ → ℝ) (s : ℝ) :
    cnt N u s = (List.range N).countP (fun n => decide (u n ≤ s)) := by
  induction N with
  | zero => simp [cnt]
  | succ N ih =>
    rw [List.range_succ, List.countP_append, ← ih]
    unfold cnt
    rw [Finset.range_succ, Finset.filter_insert]
    by_cases h : u N ≤ s
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
      simp [h]
    · rw [if_neg h]; simp [h]

/-- Toggle signal of a list of times (start low, toggle at each element). -/
def listSig (l : List ℝ) : Sig := fun s => decide (l.countP (fun e => decide (e ≤ s)) % 2 = 1)

/-- The output signal of the involution channel (full trace semantics). -/
def outSig (N : ℕ) (t : ℕ → ℝ) : Sig := listSig (P.outList N t)

theorem listSig_map_range (N : ℕ) (u : ℕ → ℝ) : listSig ((List.range N).map u) = sigOf N u := by
  funext s
  unfold listSig sigOf
  rw [cnt_eq_countP, List.countP_map]
  rfl

/-- **Transfer from the trace semantics.**  If consecutive input transitions are at
least `S` apart, `S > max δ∞↑ δ∞↓ - δmin`, then nothing is cancelled, the full output
trace of the channel is `tent 0, ..., tent (N-1)`, and the output signal is a
`DelayPure.Chan` behaviour of the input signal, band
`[min (δ↑ T0) (δ↓ T0), max δ∞↑ δ∞↓]` with `T0 = S - max δ∞↑ δ∞↓`. -/
theorem trace_transfer_sep {S : ℝ} (hS : max P.infUp P.infDown - P.dmin < S)
    (t : ℕ → ℝ) (ht : ∀ n, t n + S ≤ t (n + 1)) (N : ℕ) :
    P.outList N t = (List.range N).map (P.tent t) ∧
    Chan (min (P.up (S - max P.infUp P.infDown)) (P.down (S - max P.infUp P.infDown)))
      (max P.infUp P.infDown) (listSig ((List.range N).map t)) (P.outSig N t) := by
  have ht' : ∀ n, t n < t (n + 1) := by
    have := P.dmin_lt_infUp; have := le_max_left P.infUp P.infDown
    intro n; linarith [ht n]
  obtain ⟨hnc, -, hchan⟩ := InvolutionPair.transfer_sep' hS t ht
  have hout := outList_of_noCancel t ht' (N := N) (fun n _ => hnc n)
  refine ⟨hout, ?_⟩
  unfold outSig
  rw [hout, listSig_map_range, listSig_map_range]
  exact hchan N

/-- The same with the exact threshold of `InvolutionDMin.sep_threshold_exact`
(`δ∞↑ - δmin < S`, `δ∞↓ - δmin ≤ S`) and band `[δmin, max δ∞↑ δ∞↓]`. -/
theorem trace_transfer_exact {S : ℝ} (hup : P.infUp - P.dmin < S)
    (hdn : P.infDown - P.dmin ≤ S) (t : ℕ → ℝ) (ht : ∀ n, t n + S ≤ t (n + 1)) (N : ℕ) :
    P.outList N t = (List.range N).map (P.tent t) ∧
    Chan P.dmin (max P.infUp P.infDown) (listSig ((List.range N).map t)) (P.outSig N t) := by
  have ht' : ∀ n, t n < t (n + 1) := by
    have := P.dmin_lt_infUp; intro n; linarith [ht n]
  have hnc := InvolutionPair.sep_no_cancel_tent hup hdn t ht
  have hout := outList_of_noCancel t ht' (N := N) (fun n _ => hnc n)
  refine ⟨hout, ?_⟩
  unfold outSig
  rw [hout, listSig_map_range, listSig_map_range]
  exact InvolutionPair.sep_transfer_exact hup hdn t ht N

/-- Series composition with a bounded pure-delay channel, under separation: the
involution channel followed by `Chan lo2 hi2` is contained in the pure channel with the
summed band. -/
theorem trace_transfer_comp {S lo2 hi2 : ℝ} (hS : max P.infUp P.infDown - P.dmin < S)
    (t : ℕ → ℝ) (ht : ∀ n, t n + S ≤ t (n + 1)) (N : ℕ) {z : Sig}
    (hz : Chan lo2 hi2 (P.outSig N t) z) :
    Chan (min (P.up (S - max P.infUp P.infDown)) (P.down (S - max P.infUp P.infDown)) + lo2)
      (max P.infUp P.infDown + hi2) (listSig ((List.range N).map t)) z :=
  chan_comp (trace_transfer_sep hS t ht N).2 hz

/-! ## 6. A concrete trace on `ratPair`: cancelled pulses leave a memory -/

theorem rat_dmin_eq : ratPair.dmin = 1 := (ratPair.isDMin_iff.mp rat_dmin).symm

/-- The input `0, 1/2, 5` (a pulse of width `1/2 ≤ δ∞ - δmin = 1`, then a rising
transition at 5). -/
def ratIn (n : ℕ) : ℝ := if n = 0 then 0 else if n = 1 then 1 / 2 else (n : ℝ) + 3

theorem ratIn_mono : ∀ n, ratIn n < ratIn (n + 1) := by
  intro n
  unfold ratIn
  rcases n with _ | _ | n
  · norm_num
  · norm_num
  · simp only [show n + 2 ≠ 0 by omega, show n + 2 ≠ 1 by omega, if_false,
      show n + 2 + 1 ≠ 0 by omega, show n + 2 + 1 ≠ 1 by omega]
    push_cast; linarith

/-- **Memory of a cancelled pulse.**  On `ratPair`, the input `0, 1/2, 5` gives the
single output transition `89/13 = 5 + 24/13`: the pulse `[0, 1/2]` is cancelled, and
the rising transition at 5 gets delay `24/13 < δ∞ = 2`, because `T` is measured from
the cancelled tentative output at `1/2`.  (A channel that forgot cancelled pulses
would give `5 + δ∞ = 7`.) -/
theorem rat_memory : ratPair.outList 3 ratIn = [89 / 13] := by
  have e0 : ratPair.tent ratIn 0 = 2 := by
    show ratIn 0 + 2 = 2; norm_num [ratIn]
  have e1 : ratPair.tent ratIn 1 = 1 / 2 := by
    rw [tent_succ', e0]
    show ratIn 1 + ratDelay (ratIn 1 - 2) = 1 / 2
    norm_num [ratIn, ratDelay]
  have e2 : ratPair.tent ratIn 2 = 89 / 13 := by
    rw [tent_succ', e1]
    show ratIn 2 + ratDelay (ratIn 2 - 1 / 2) = 89 / 13
    norm_num [ratIn, ratDelay]
  have c0 : ratPair.CN 3 ratIn 0 := ⟨by omega, by rw [e0, e1]; norm_num⟩
  have s0 : ¬ ratPair.Surv 3 ratIn 0 := fun h => h.2.1 c0
  have s1 : ¬ ratPair.Surv 3 ratIn 1 := fun h => h.2.2 0 rfl c0
  have s2 : ratPair.Surv 3 ratIn 2 :=
    ⟨by omega, fun h => by have := h.1; omega, fun m hm h => by
      rw [show m = 1 by omega] at h; have := h.2; rw [e1, e2] at this; norm_num at this⟩
  simp [InvolutionPair.tent, outList, survIdx, List.range_succ, s0, s1, s2, e2]

end


/-! ## 7. The paper's channel algorithm, and agreement with `outList`

The channel algorithm of Függer/Nowak/Schmid ("non-forgetful" channel; Függer,
Najvirt, Nowak, Schmid, "A faithful binary circuit model", IEEE TCAD 39(10), 2020,
and "Unfaithful glitch propagation in existing binary circuit models", IEEE TC 2016,
Alg. "non-forgetful channel"): process the input transitions in order; transition `n`
at time `t` computes `T = t - t'` against the previous *tentative* output `t'`
(whether or not that one was cancelled), and the candidate output `o = t + δ(T)`.  If
`o > t'` it is appended to the output; otherwise the pending output at `t'` is removed
and `o` is not added.  `step` is that rule, `channel` folds it over an input list. -/

noncomputable section

variable {P : InvolutionPair}

section Step

variable (t : ℕ → ℝ)

theorem CN_succ_iff {N k : ℕ} (hk : k + 1 < N) : P.CN (N + 1) t k ↔ P.CN N t k := by
  constructor
  · rintro ⟨-, h⟩; exact ⟨hk, h⟩
  · rintro ⟨-, h⟩; exact ⟨by omega, h⟩

theorem surv_succ_of_lt {N m : ℕ} (hm : m + 1 < N) : P.Surv (N + 1) t m ↔ P.Surv N t m := by
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨by omega, fun hc => h1 ((CN_succ_iff t hm).mpr hc),
      fun k hk hc => h2 k hk ((CN_succ_iff t (by omega)).mpr hc)⟩
  · rintro ⟨-, h1, h2⟩
    exact ⟨by omega, fun hc => h1 ((CN_succ_iff t hm).mp hc),
      fun k hk hc => h2 k hk ((CN_succ_iff t (by omega)).mp hc)⟩

/-- The previously last transition `n`, once transition `n+1` arrives. -/
theorem surv_last_iff (n : ℕ) :
    P.Surv (n + 1 + 1) t n ↔ P.Surv (n + 1) t n ∧ P.tent t n < P.tent t (n + 1) := by
  constructor
  · rintro ⟨-, h1, h2⟩
    refine ⟨⟨by omega, fun hc => by have := hc.1; omega,
      fun k hk hc => h2 k hk ((CN_succ_iff t (by omega)).mpr hc)⟩, ?_⟩
    by_contra hc; push_neg at hc; exact h1 ⟨by omega, hc⟩
  · rintro ⟨⟨-, -, h2⟩, hlt⟩
    exact ⟨by omega, fun hc => by linarith [hc.2],
      fun k hk hc => h2 k hk ((CN_succ_iff t (by omega)).mp hc)⟩

/-- The new transition `n+1` survives (so far) iff it does not cancel with `n`. -/
theorem surv_new_iff (n : ℕ) :
    P.Surv (n + 1 + 1) t (n + 1) ↔ P.tent t n < P.tent t (n + 1) := by
  constructor
  · rintro ⟨-, -, h2⟩
    by_contra hc; push_neg at hc; exact h2 n rfl ⟨by omega, hc⟩
  · intro hlt
    refine ⟨by omega, fun hc => by have := hc.1; omega, fun k hk hc => ?_⟩
    have hkn : k = n := by omega
    subst hkn
    linarith [hc.2]

variable (ht : ∀ n, t n < t (n + 1))
include ht

/-- When transition `n+1` cancels with `n`, the transition `n` was pending (it was a
survivor of the first `n+1` transitions): "remove the pending output" is well defined.
This is the paper's remark that an output event is deleted in the next iteration or
never; here it is `cancel_no_chain`. -/
theorem surv_of_cancel (n : ℕ) (hc : P.tent t (n + 1) ≤ P.tent t n) : P.Surv (n + 1) t n := by
  refine ⟨by omega, fun h => by have := h.1; omega, fun k hk hck => ?_⟩
  subst hk
  have h1 := cancel_no_chain t ht k hck.2
  have e : P.tent t (k + 2) = P.tent t (k + 1 + 1) := rfl
  linarith

theorem survIdx_step (n : ℕ) :
    P.survIdx (n + 1 + 1) t =
      if P.tent t n < P.tent t (n + 1) then P.survIdx (n + 1) t ++ [n + 1]
      else (P.survIdx (n + 1) t).dropLast := by
  have hpre : ∀ m ∈ List.range n,
      decide (P.Surv (n + 1 + 1) t m) = decide (P.Surv (n + 1) t m) := by
    intro m hm
    simp only [List.mem_range] at hm
    simp only [surv_succ_of_lt t (N := n + 1) (show m + 1 < n + 1 by omega)]
  have hA : P.survIdx (n + 1 + 1) t =
      (List.range n).filter (fun m => decide (P.Surv (n + 1) t m)) ++
        ((if P.Surv (n + 1 + 1) t n then [n] else []) ++
          (if P.Surv (n + 1 + 1) t (n + 1) then [n + 1] else [])) := by
    unfold InvolutionPair.survIdx
    rw [List.range_succ, List.range_succ, List.filter_append, List.filter_append,
      List.filter_congr hpre, List.append_assoc]
    by_cases h1 : P.Surv (n + 1 + 1) t n <;> by_cases h2 : P.Surv (n + 1 + 1) t (n + 1) <;>
      simp [h1, h2]
  have hB : P.survIdx (n + 1) t =
      (List.range n).filter (fun m => decide (P.Surv (n + 1) t m)) ++
        (if P.Surv (n + 1) t n then [n] else []) := by
    unfold InvolutionPair.survIdx
    rw [List.range_succ, List.filter_append]
    by_cases h1 : P.Surv (n + 1) t n <;> simp [h1]
  by_cases hlt : P.tent t n < P.tent t (n + 1)
  · rw [if_pos hlt, hA, hB, if_pos ((surv_new_iff t n).mpr hlt), List.append_assoc]
    by_cases hs : P.Surv (n + 1) t n
    · rw [if_pos ((surv_last_iff t n).mpr ⟨hs, hlt⟩), if_pos hs]
    · rw [if_neg (fun h => hs ((surv_last_iff t n).mp h).1), if_neg hs]
  · rw [if_neg hlt, hA, hB, if_neg (fun h => hlt ((surv_new_iff t n).mp h)),
      if_neg (fun h => hlt ((surv_last_iff t n).mp h).2),
      if_pos (surv_of_cancel t ht n (le_of_not_gt hlt))]
    simp

/-- **One step of the trace semantics**: when transition `n+1` arrives, its output is
appended if it is after the previous tentative output, otherwise the last output
(which is transition `n`'s, `surv_of_cancel`) is removed. -/
theorem outList_step (n : ℕ) :
    P.outList (n + 1 + 1) t =
      if P.tent t n < P.tent t (n + 1) then P.outList (n + 1) t ++ [P.tent t (n + 1)]
      else (P.outList (n + 1) t).dropLast := by
  unfold InvolutionPair.outList
  rw [survIdx_step t ht n]
  split_ifs <;> simp [List.map_dropLast]

end Step

variable (P) in
/-- Output so far (reversed: most recent first) after the first `n` input transitions,
by the paper's algorithm on the tentative times. -/
def accOut (t : ℕ → ℝ) : ℕ → List ℝ
  | 0 => []
  | 1 => [P.tent t 0]
  | n + 2 => if P.tent t n < P.tent t (n + 1) then P.tent t (n + 1) :: accOut t (n + 1)
             else (accOut t (n + 1)).tail

theorem accOut_step (t : ℕ → ℝ) (n : ℕ) :
    P.accOut t (n + 1 + 1) = if P.tent t n < P.tent t (n + 1)
      then P.tent t (n + 1) :: P.accOut t (n + 1) else (P.accOut t (n + 1)).tail := rfl

theorem outList_zero (t : ℕ → ℝ) : P.outList 0 t = [] := by
  simp [InvolutionPair.outList, InvolutionPair.survIdx]

theorem accOut_reverse (t : ℕ → ℝ) (ht : ∀ n, t n < t (n + 1)) (N : ℕ) :
    (P.accOut t N).reverse = P.outList N t := by
  rcases N with _ | N
  · rw [outList_zero]; rfl
  induction N with
  | zero =>
    rw [outList_one]; rfl
  | succ n ih =>
    rw [accOut_step, outList_step t ht n]
    split_ifs
    · rw [List.reverse_cons, ih]
    · rw [← List.dropLast_reverse, ih]

variable (P) in
/-- **The paper's channel algorithm, one step.**  State: number of input transitions
seen, previous tentative output time, output so far (most recent first).  The first
transition gets `δ∞↑` (input initially low, `T = ∞`); transition `k+1` gets
`δ(x - o)` with `δ = δ↑` for even `k+1`, `δ↓` for odd, against the previous tentative
output `o`; its output is added if after `o`, otherwise the pending output is
removed. -/
def step : ℕ × ℝ × List ℝ → ℝ → ℕ × ℝ × List ℝ
  | (0, _, _), x => (1, x + P.infUp, [x + P.infUp])
  | (k + 1, o, out), x =>
      (k + 1 + 1, x + P.delayAt (k + 1) (x - o),
        if o < x + P.delayAt (k + 1) (x - o) then (x + P.delayAt (k + 1) (x - o)) :: out
        else out.tail)

variable (P) in
/-- **The involution channel as a function on transition lists**: input transition
times (input initially low, alternating rising/falling) to output transition times
(output initially low, toggling at each). -/
def channel (l : List ℝ) : List ℝ := (l.foldl P.step (0, 0, [])).2.2.reverse

variable (P) in
/-- Previous tentative output after `n` transitions (`0` is a dummy for `n = 0`). -/
def prevTent (t : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => P.tent t k

theorem foldl_step (t : ℕ → ℝ) (l : List ℝ) (hl : ∀ n (h : n < l.length), t n = l[n]) :
    l.foldl P.step (0, 0, []) = (l.length, P.prevTent t l.length, P.accOut t l.length) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
    have hl' : ∀ n (h : n < l.length), t n = l[n] := fun n h => by
      rw [hl n (by simp; omega)]; exact List.getElem_append_left h
    have hx : t l.length = x := by rw [hl l.length (by simp)]; simp
    rw [List.foldl_append, ih hl', List.length_append, List.length_singleton]
    cases hlen : l.length with
    | zero =>
      rw [hlen] at hx
      show P.step (0, 0, []) x = (0 + 1, P.tent t 0, [P.tent t 0])
      rw [tent_zero', hx]; rfl
    | succ k =>
      rw [hlen] at hx
      show P.step (k + 1, P.tent t k, P.accOut t (k + 1)) x =
        (k + 1 + 1, P.tent t (k + 1), P.accOut t (k + 1 + 1))
      rw [accOut_step, tent_succ', hx]
      rfl

/-- **Agreement of the algorithm with the declarative trace semantics**: on a strictly
increasing input, `channel` is the list of surviving tentative outputs (`outList`),
for any extension `t` of the list to a strictly increasing sequence. -/
theorem channel_eq (l : List ℝ) (t : ℕ → ℝ) (hl : ∀ n (h : n < l.length), t n = l[n])
    (ht : ∀ n, t n < t (n + 1)) : P.channel l = P.outList l.length t := by
  unfold InvolutionPair.channel
  rw [foldl_step t l hl]
  exact accOut_reverse t ht l.length

/-- Extension of a finite list to a sequence (unit steps after the last element). -/
def extend (l : List ℝ) (n : ℕ) : ℝ :=
  if h : n < l.length then l[n] else l.getD (l.length - 1) 0 + ((n : ℝ) - l.length + 1)

theorem extend_agree (l : List ℝ) : ∀ n (h : n < l.length), extend l n = l[n] :=
  fun n h => by simp [extend, h]

theorem extend_mono {l : List ℝ} (hs : l.Pairwise (· < ·)) : ∀ n, extend l n < extend l (n + 1) := by
  intro n
  unfold extend
  by_cases h1 : n + 1 < l.length
  · rw [dif_pos (by omega : n < l.length), dif_pos h1]
    exact List.pairwise_iff_getElem.mp hs n (n + 1) (by omega) h1 (by omega)
  · rw [dif_neg h1]
    by_cases h0 : n < l.length
    · rw [dif_pos h0]
      have e1 : l.length - 1 = n := by omega
      have e2 : (l.length : ℝ) = n + 1 := by exact_mod_cast (show l.length = n + 1 by omega)
      rw [e1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0, Option.getD_some, e2]
      push_cast; linarith
    · rw [dif_neg h0]; push_cast; linarith

/-! ## 8. Properties of `channel` on lists -/

/-- `channel` on a strictly increasing list is `outList` of its extension. -/
theorem channel_eq_extend {l : List ℝ} (hs : l.Pairwise (· < ·)) :
    P.channel l = P.outList l.length (extend l) :=
  channel_eq l (extend l) (extend_agree l) (extend_mono hs)

/-- **(c) Well-formed output, order**: strictly increasing output times. -/
theorem channel_sorted {l : List ℝ} (hs : l.Pairwise (· < ·)) :
    (P.channel l).Pairwise (· < ·) := by
  rw [channel_eq_extend hs]
  exact outList_sorted (extend l) (extend_mono hs) l.length

theorem outList_length_parity (t : ℕ → ℝ) (ht : ∀ n, t n < t (n + 1)) (N : ℕ) :
    (P.outList N t).length % 2 = N % 2 := by
  have h := survBelow_parity t ht N N le_rfl
  rw [if_neg (fun ⟨m, hm, hc⟩ => by have := hc.1; omega)] at h
  simpa [InvolutionPair.survBelow, InvolutionPair.outList, InvolutionPair.survIdx] using h

/-- **(c) Well-formed output, final value**: cancellations remove transitions in pairs,
so the output makes as many transitions as the input modulo 2: after the last output
transition the output equals the input's final value. -/
theorem channel_length_parity {l : List ℝ} (hs : l.Pairwise (· < ·)) :
    (P.channel l).length % 2 = l.length % 2 := by
  rw [channel_eq_extend hs]
  exact outList_length_parity (extend l) (extend_mono hs) l.length

/-- **(c) Causality**: every output transition is the tentative output of some input
transition `n`, more than `δmin` after it, and (if `n` is not last) less than `δmin`
after input transition `n+1`; and the number of earlier output transitions has the
parity of `n`, so it has the direction of input transition `n` (`surv_parity`). -/
theorem channel_mem {l : List ℝ} (hs : l.Pairwise (· < ·)) {s : ℝ} (hsm : s ∈ P.channel l) :
    ∃ n, ∃ h : n < l.length, s = P.tent (extend l) n ∧ l[n] + P.dmin < s ∧
      (∀ h' : n + 1 < l.length, s < l[n + 1] + P.dmin) ∧
      P.survBelow l.length (extend l) n % 2 = n % 2 := by
  rw [channel_eq_extend hs] at hsm
  obtain ⟨n, hsv, e⟩ := (mem_outList (extend l) (extend_mono hs)).mp hsm
  refine ⟨n, hsv.1, e.symm, ?_, fun h' => ?_, surv_parity (extend l) (extend_mono hs) hsv⟩
  · have := surv_lo (extend l) (extend_mono hs) hsv
    rw [extend_agree l n hsv.1] at this; rw [← e]; exact this
  · have := surv_hi (extend l) (extend_mono hs) hsv h'
    rw [extend_agree l (n + 1) h'] at this; rw [← e]; exact this

/-- **(a) Agreement with `InvolutionTransfer`/`InvolutionDMin` under separation**: on an
`S`-separated list with `S` above the exact threshold, nothing is cancelled and the
output is exactly the tentative outputs `tent 0, ..., tent (N-1)`, which those files
show to be a `DelayPure.Chan δmin (max δ∞↑ δ∞↓)` behaviour (`trace_transfer_exact`). -/
theorem channel_of_sep {S : ℝ} (hup : P.infUp - P.dmin < S) (hdn : P.infDown - P.dmin ≤ S)
    (t : ℕ → ℝ) (ht : ∀ n, t n + S ≤ t (n + 1)) (N : ℕ) :
    P.channel ((List.range N).map t) = (List.range N).map (P.tent t) := by
  have ht' : ∀ n, t n < t (n + 1) := by
    have := P.dmin_lt_infUp; intro n; linarith [ht n]
  rw [channel_eq ((List.range N).map t) t (fun n h => by simp) ht', List.length_map,
    List.length_range]
  exact (trace_transfer_exact hup hdn t ht N).1

/-- **(b) A single input pulse** `[a, a + Δ]` (`Δ > 0`, input initially low): the output
is empty iff `Δ ≤ δ∞↑ - δmin`; otherwise it is the pulse
`[a + δ∞↑, a + δ∞↑ + Δ']` with `Δ' = pulseWidth Δ = (Δ - δ∞↑) + δ↓(Δ - δ∞↑)`, which is
strictly increasing in `Δ` (`pulseWidth_strictMono`), positive exactly above the
threshold (`pulse_cancel_iff'`), below `Δ + (δ∞↓ - δ∞↑)` (`pulseWidth_lt`), and tends
to `0` at the threshold (`pulseWidth_small'`). -/
theorem channel_pulse (a Δ : ℝ) (hΔ : 0 < Δ) :
    P.channel [a, a + Δ] = if Δ ≤ P.infUp - P.dmin then []
      else [a + P.infUp, a + P.infUp + P.pulseWidth Δ] := by
  have hs : [a, a + Δ].Pairwise (· < ·) := by simpa using (by linarith : a < a + Δ)
  rw [channel_eq_extend hs]
  have h0 : extend [a, a + Δ] 0 = a := extend_agree _ 0 (by simp)
  have h1 : extend [a, a + Δ] 1 = a + Δ := extend_agree _ 1 (by simp)
  obtain ⟨hc, hp⟩ := pulse_out a Δ hΔ (extend [a, a + Δ]) h0 h1
  show P.outList 2 _ = _
  split_ifs with h
  · exact hc h
  · exact hp (lt_of_not_ge h)

/-- **(b) Monotone relation**: wider input pulses give wider output pulses
(as long as the narrower one survives); every surviving output width is positive. -/
theorem channel_pulse_mono {Δ₁ Δ₂ : ℝ} (h1 : P.infUp - P.dmin < Δ₁) (h12 : Δ₁ < Δ₂) :
    0 < P.pulseWidth Δ₁ ∧ P.pulseWidth Δ₁ < P.pulseWidth Δ₂ := by
  have hpos : 0 < Δ₁ := by linarith [P.dmin_lt_infUp]
  refine ⟨?_, pulseWidth_strictMono hpos h12⟩
  by_contra hc; push_neg at hc
  have := (pulse_cancel_iff' hpos).mp hc
  linarith

end

/-! ## 9. Concrete instance: `ratPair` (δ(T) = 2 - 1/(T+2), δ∞ = 2, δmin = 1)

Expected values are computed by hand from `ratDelay`, not from a run:
* `[0, 1/2]`: tent 0 = 0 + 2 = 2, tent 1 = 1/2 + δ(1/2 - 2) = 1/2 + 2 - 2 = 1/2 ≤ 2:
  the runt (width 1/2 ≤ δ∞ - δmin = 1) is cancelled, output `[]`.
* `[0, 3/2]`: tent 1 = 3/2 + δ(-1/2) = 3/2 + 2 - 2/3 = 17/6 > 2: output `[2, 17/6]`,
  a pulse of width 5/6 < 3/2 (pulse shrinking).
* `[0, 1]` is exactly at the threshold: tent 1 = 1 + δ(-1) = 2 = tent 0, cancelled.
-/

noncomputable section

theorem rat_delayAt (n : ℕ) : ratPair.delayAt n = ratDelay := by
  unfold InvolutionPair.delayAt; split_ifs <;> rfl

/-- **(d) A runt is cancelled** (computed through the algorithm, not through the theorems). -/
theorem rat_runt_cancelled : ratPair.channel [0, 1 / 2] = [] := by
  simp only [InvolutionPair.channel, List.foldl, InvolutionPair.step, rat_delayAt]
  show (if (0 : ℝ) + 2 < 1 / 2 + ratDelay (1 / 2 - (0 + 2)) then _ else _).reverse = []
  rw [if_neg (by norm_num [ratDelay])]
  rfl

/-- A wider pulse passes, shrunk: `[0, 3/2] ↦ [2, 17/6]` (width 3/2 ↦ 5/6). -/
theorem rat_pulse_shrunk : ratPair.channel [0, 3 / 2] = [2, 17 / 6] := by
  simp only [InvolutionPair.channel, List.foldl, InvolutionPair.step, rat_delayAt]
  show (if (0 : ℝ) + 2 < 3 / 2 + ratDelay (3 / 2 - (0 + 2)) then _ else _).reverse = _
  rw [if_pos (by norm_num [ratDelay])]
  norm_num [ratDelay]

/-- At the threshold width `δ∞ - δmin = 1` the pulse is still cancelled. -/
theorem rat_threshold_cancelled : ratPair.channel [0, 1] = [] := by
  simp only [InvolutionPair.channel, List.foldl, InvolutionPair.step, rat_delayAt]
  show (if (0 : ℝ) + 2 < 1 + ratDelay (1 - (0 + 2)) then _ else _).reverse = []
  rw [if_neg (by norm_num [ratDelay])]
  rfl

/-- The same three results from the general theorem `channel_pulse` (consistency of the
algorithm with the threshold `δ∞↑ - δmin`). -/
theorem rat_pulse_general (Δ : ℝ) (hΔ : 0 < Δ) :
    ratPair.channel [0, Δ] = if Δ ≤ 1 then [] else [2, 2 + ratPair.pulseWidth Δ] := by
  have := channel_pulse (P := ratPair) 0 Δ hΔ
  rw [zero_add] at this
  rw [this, InvolutionPair.rat_dmin_eq]
  show (if Δ ≤ 2 - 1 then _ else [0 + 2, 0 + 2 + _]) = _
  norm_num

/-- **Chained history on lists**: `[0, 1/2, 5] ↦ [89/13]` (`rat_memory` via the
algorithm): the cancelled runt still shortens the next delay to `24/13 < δ∞`. -/
theorem rat_memory_channel : ratPair.channel [0, 1 / 2, 5] = [89 / 13] := by
  rw [channel_eq [0, 1 / 2, 5] InvolutionPair.ratIn (fun n h => by
    simp only [List.length_cons, List.length_nil] at h
    rcases n with _ | _ | _ | n
    · simp [InvolutionPair.ratIn]
    · simp [InvolutionPair.ratIn]
    · norm_num [InvolutionPair.ratIn]
    · omega) InvolutionPair.ratIn_mono]
  exact InvolutionPair.rat_memory

end

/-! ## 10. The exp-channel (first-order RC + pure delay `T_p`), on traces

`ExpLog` abstracts `exp`/`log` by named hypotheses (`Involution.lean`); the real instance
`E x = e^{x/τ}`, `L y = τ ln y` needs `Mathlib.Analysis.SpecialFunctions.Log.Basic`
(Wip/InvTrace/ExpReal.lean). -/

noncomputable section

theorem exp_dmin_eq (X : ExpLog) (Tp : ℝ) (hTp : 0 < Tp) : (X.expPair Tp hTp).dmin = Tp :=
  ((X.expPair Tp hTp).isDMin_iff.mp (X.exp_dmin Tp hTp)).symm

/-- **(d) exp-channel**: an isolated pulse `[a, a + Δ]` is cancelled iff `Δ ≤ τ ln 2`
(here `X.L 2`); otherwise it comes out `T_p + τ ln 2` later with width `pulseWidth Δ`. -/
theorem exp_channel_pulse (X : ExpLog) (Tp : ℝ) (hTp : 0 < Tp) (a Δ : ℝ) (hΔ : 0 < Δ) :
    (X.expPair Tp hTp).channel [a, a + Δ] = if Δ ≤ X.L 2 then []
      else [a + (Tp + X.L 2), a + (Tp + X.L 2) + (X.expPair Tp hTp).pulseWidth Δ] := by
  rw [channel_pulse a Δ hΔ, exp_dmin_eq]
  show (if Δ ≤ Tp + X.L 2 - Tp then _ else _) = _
  rw [show Tp + X.L 2 - Tp = X.L 2 by ring]
  rfl

end

end Formal.Core.DelayInvolution.InvolutionPair
