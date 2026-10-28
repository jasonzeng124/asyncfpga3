import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Formal.Core.Delay.Involution
import Formal.Core.Delay.Pure

/-!
# Involution channels: a concrete instance and the transfer to bounded pure delay

Track 3, channel (c), follow-up to `Formal.Core.Delay.Involution` (the audit marked
the "transfer lemma" claim OVERSTATED: only monotonicity of `δ` was proved).

## Results

1. `ratPair`, `rat_dmin`: a concrete `InvolutionPair`, `δ↑ = δ↓ = δ(T) = 2 - 1/(T+2)`,
   `δ∞ = 2`, `δmin = 1`.  Every field, the involution property included, is proved
   exactly (`rat_inv`), so the class is non-vacuous in the claimed build.
2. `chan_sigOf`: a generic bridge to `DelayPure.Chan`.  If two finite event
   sequences `t` (input) and `o` (output) are each monotone (`t` strictly), and
   `lo ≤ o n - t n ≤ hi` for every `n`, then the signal with transitions `o` is a
   `Chan lo hi` behaviour of the signal with transitions `t`.
3. `transfer_gap` (separation measured from the previous OUTPUT, the paper's
   variable `T`): if every input transition comes at least `T0 > -δmin` after the
   previous output, then no output is cancelled, every delay is in
   `[min (δ↑ T0) (δ↓ T0), max δ∞↑ δ∞↓]`, and the output trace is a `Chan` behaviour
   of the input trace with that band.
4. `transfer_sep` (separation measured between consecutive INPUT transitions,
   which an environment spec can state without knowing the channel): if
   consecutive input transitions are `≥ S` apart with `S > max δ∞↑ δ∞↓ - δmin`,
   then (3) holds with `T0 = S - max δ∞↑ δ∞↓`.  `band_lo_gt_dmin`: the lower end of
   the band is `> δmin > 0`.
5. `sep_threshold_sharp`: for EVERY involution pair and every `0 < S ≤ δ∞↑ - δmin`
   there is an `S`-separated input (`t n = n·S`) whose first two outputs cancel.  So
   for symmetric channels (`δ∞↑ = δ∞↓`) the threshold `S > δ∞ - δmin` of (4) is
   exact.  Concrete negative controls on `ratPair`: `rat_cancel_at_threshold`
   (S = 1 = δ∞ - δmin) and `rat_cancel_half` (S = 1/2); positive example
   `rat_transfer_example` (S = 3/2 gives `Chan (4/3) 2`).

## Conventions and what is NOT covered

* The channel semantics is `InvolutionPair.tent` from `Involution.lean`: the first
  input transition gets `δ∞↑` (input initially low, `T = ∞`), transition `n+1` gets
  `δ(t(n+1) - tent n)`.  A cancellation is `tent (n+1) ≤ tent n` (`cancel_iff`).
  When no cancellation occurs the output transitions are exactly `tent 0, tent 1, ...`
  (one per input transition), which is what `transfer_*` prove; the general filtered
  output trace (with chained cancellations) is NOT formalized.
* Signals are `sigOf N u`: initially `false`, toggling at `u 0, ..., u (N-1)`
  (right-continuous).  The theorems hold for every `N`; the hypotheses are stated
  on the whole sequence `t : ℕ → ℝ`, and a finite trace of `N` transitions is
  covered by extending it (e.g. by `S`-spaced dummy transitions after `t (N-1)`,
  which do not affect `tent 0 .. tent (N-1)`).
* The upper end of the band is CLOSED: the first transition gets exactly `δ∞↑`.
  Every later delay is strictly below `δ∞` (`Involution.up_lt/down_lt`).
-/

namespace Formal.Core.DelayInvolutionTransfer

open Formal.Core.DelayInvolution Formal.Core.DelayPure

/-! ## 1. A concrete involution pair -/

/-- `δ(T) = 2 - 1/(T+2)` on `T > -2`. -/
noncomputable def ratDelay (T : ℝ) : ℝ := 2 - 1 / (T + 2)

theorem ratDelay_lt {T : ℝ} (hT : -2 < T) : ratDelay T < 2 := by
  have : 0 < 1 / (T + 2) := one_div_pos.mpr (by linarith)
  unfold ratDelay; linarith

theorem ratDelay_strictMono {a b : ℝ} (ha : -2 < a) (hab : a < b) :
    ratDelay a < ratDelay b := by
  have h := one_div_lt_one_div_of_lt (show 0 < a + 2 by linarith) (show a + 2 < b + 2 by linarith)
  unfold ratDelay; linarith

/-- The involution property, exactly: `-δ(-δ T) = T`. -/
theorem rat_inv {T : ℝ} (_hT : -2 < T) : -ratDelay (-ratDelay T) = T := by
  unfold ratDelay
  rw [show -(2 - 1 / (T + 2)) + 2 = 1 / (T + 2) by ring1, one_div_one_div]
  ring1

theorem ratDelay_zero : ratDelay 0 = 3 / 2 := by norm_num [ratDelay]

/-- The concrete symmetric involution pair. -/
noncomputable def ratPair : InvolutionPair where
  up := ratDelay
  down := ratDelay
  infUp := 2
  infDown := 2
  infUp_pos := by norm_num
  infDown_pos := by norm_num
  up_lt := fun _ hT => ratDelay_lt hT
  down_lt := fun _ hT => ratDelay_lt hT
  up_strictMono := fun _ _ ha hab => ratDelay_strictMono ha hab
  down_strictMono := fun _ _ ha hab => ratDelay_strictMono ha hab
  inv_up := fun _ hT => rat_inv hT
  inv_down := fun _ hT => rat_inv hT
  up_causal := by show 0 < ratDelay 0; rw [ratDelay_zero]; norm_num
  down_causal := by show 0 < ratDelay 0; rw [ratDelay_zero]; norm_num

/-- `δmin = 1` for `ratPair`. -/
theorem rat_dmin : ratPair.IsDMin 1 where
  mem := by show (-2 : ℝ) < -1; norm_num
  fix := by show ratDelay (-1) = 1; norm_num [ratDelay]

/-! ## 2. Event sequences as signals, and the bridge to `Chan` -/

/-- Number of the first `N` events of `u` at or before `s`. -/
noncomputable def cnt (N : ℕ) (u : ℕ → ℝ) (s : ℝ) : ℕ :=
  ((Finset.range N).filter (fun n => u n ≤ s)).card

/-- The signal that starts `false` and toggles at `u 0, ..., u (N-1)`. -/
noncomputable def sigOf (N : ℕ) (u : ℕ → ℝ) : Sig :=
  fun s => decide (cnt N u s % 2 = 1)

theorem cnt_mono (N : ℕ) (u : ℕ → ℝ) {a b : ℝ} (hab : a ≤ b) : cnt N u a ≤ cnt N u b := by
  unfold cnt
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, le_trans hi.2 hab⟩

/-- For monotone `u`, the events at or before `s` are a prefix: `i < cnt ↔ u i ≤ s`
(the `←` direction needs `i < N`). -/
theorem lt_cnt_of_le {N : ℕ} {u : ℕ → ℝ} (hu : Monotone u) {s : ℝ} {i : ℕ} (hi : i < N)
    (h : u i ≤ s) : i < cnt N u s := by
  have hsub : Finset.range (i + 1) ⊆ (Finset.range N).filter (fun n => u n ≤ s) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, le_trans (hu (by omega)) h⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  unfold cnt; omega

theorem le_of_lt_cnt {N : ℕ} {u : ℕ → ℝ} (hu : Monotone u) {s : ℝ} {i : ℕ}
    (h : i < cnt N u s) : u i ≤ s := by
  by_contra hc
  push Not at hc
  have hsub : (Finset.range N).filter (fun n => u n ≤ s) ⊆ Finset.range i := by
    intro j hj
    simp only [Finset.mem_filter] at hj
    simp only [Finset.mem_range]
    by_contra hji
    push Not at hji
    have := hu hji
    linarith [hj.2]
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  unfold cnt at h; omega

/-- The read-time map used for the bridge: `σ s = max (s - hi) (t (k-1))` where
`k` output events have happened by `s` (`σ s = s - hi` if none). -/
noncomputable def readMap (N : ℕ) (t o : ℕ → ℝ) (hi s : ℝ) : ℝ :=
  if cnt N o s = 0 then s - hi else max (s - hi) (t (cnt N o s - 1))

theorem readMap_ge (N : ℕ) (t o : ℕ → ℝ) (hi s : ℝ) : s - hi ≤ readMap N t o hi s := by
  unfold readMap
  split_ifs
  · exact le_refl _
  · exact le_max_left _ _

/-- **Bridge.**  Monotone output events, each within `[lo, hi]` after its input
event, give a `Chan lo hi` behaviour (for any number `N` of events). -/
theorem chan_sigOf {lo hi : ℝ} {t o : ℕ → ℝ} (ht : StrictMono t) (ho : Monotone o)
    (hlo : ∀ n, lo ≤ o n - t n) (hhi : ∀ n, o n - t n ≤ hi) (N : ℕ) :
    Chan lo hi (sigOf N t) (sigOf N o) := by
  have hlh : lo ≤ hi := le_trans (hlo 0) (hhi 0)
  let r : Retime lo hi :=
    { σ := readMap N t o hi
      mono := by
        intro a b hab
        have hk := cnt_mono N o hab
        unfold readMap
        by_cases ha : cnt N o a = 0
        · rw [ite_eq_left ha]
          have := readMap_ge N t o hi b
          unfold readMap at this
          linarith
        · have hb : cnt N o b ≠ 0 := by omega
          rw [ite_eq_right ha, ite_eq_right hb]
          exact max_le_max (by linarith) (ht.monotone (by omega))
      ge := readMap_ge N t o hi
      le := by
        intro s
        unfold readMap
        split_ifs with hk
        · linarith
        · apply max_le (by linarith)
          have h1 := le_of_lt_cnt ho (show cnt N o s - 1 < cnt N o s by omega)
          have h2 := hlo (cnt N o s - 1)
          linarith }
  refine ⟨r, fun s => ?_⟩
  show sigOf N o s = sigOf N t (readMap N t o hi s)
  have key : cnt N t (readMap N t o hi s) = cnt N o s := by
    unfold cnt
    congr 1
    apply Finset.filter_congr
    intro n hn
    rw [Finset.mem_range] at hn
    constructor
    · intro h
      by_contra hc
      push Not at hc
      -- `s < o n`, so at most `n` output events by `s`, and `σ s < t n`
      have hkn : ¬ n < cnt N o s := fun hlt => by
        have := le_of_lt_cnt ho hlt; linarith
      have hon := hhi n
      have : readMap N t o hi s < t n := by
        unfold readMap
        split_ifs with hk
        · linarith
        · apply max_lt (by linarith)
          exact ht (by omega)
      linarith
    · intro h
      have hlt := lt_cnt_of_le ho hn h
      have hk : cnt N o s ≠ 0 := by omega
      unfold readMap
      rw [ite_eq_right hk]
      exact le_trans (ht.monotone (by omega)) (le_max_right _ _)
  unfold sigOf
  rw [key]

/-! ## 3. The transfer theorems -/

variable {P : InvolutionPair}

theorem tent_zero (t : ℕ → ℝ) : P.tent t 0 = t 0 + P.infUp := rfl

theorem tent_succ_sub (t : ℕ → ℝ) (n : ℕ) :
    P.tent t (n + 1) - t (n + 1) = P.delayAt (n + 1) (t (n + 1) - P.tent t n) := by
  show t (n + 1) + P.delayAt (n + 1) (t (n + 1) - P.tent t n) - t (n + 1) = _
  ring1

/-- Every delay function value at `T ≥ T0 > -δmin` lies in the band. -/
theorem delayAt_band {d T0 T : ℝ} (h : P.IsDMin d) (h0 : -d < T0) (hT : T0 ≤ T) (m : ℕ) :
    min (P.up T0) (P.down T0) ≤ P.delayAt m T ∧ P.delayAt m T < max P.infUp P.infDown := by
  unfold InvolutionPair.delayAt
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · rw [ite_eq_left hm]
    obtain ⟨a, b⟩ := P.up_bounds (lt_trans h.mem_up h0) hT
    exact ⟨le_trans (min_le_left _ _) a, lt_of_lt_of_le b (le_max_left _ _)⟩
  · rw [ite_eq_right (show ¬ m % 2 = 0 by omega)]
    obtain ⟨a, b⟩ := P.down_bounds (lt_trans h.mem h0) hT
    exact ⟨le_trans (min_le_right _ _) a, lt_of_lt_of_le b (le_max_right _ _)⟩

/-- The band's lower end exceeds `δmin` (so it is positive). -/
theorem band_lo_gt_dmin {d T0 : ℝ} (h : P.IsDMin d) (h0 : -d < T0) :
    d < min (P.up T0) (P.down T0) := by
  have hu := P.up_strictMono _ _ h.mem_up h0
  have hd := P.down_strictMono _ _ h.mem h0
  rw [h.up_fix] at hu
  rw [h.fix] at hd
  exact lt_min hu hd

/-- **Transfer, output-relative form.**  If every input transition comes at least
`T0` after the previous (tentative) output, with `T0 > -δmin`, then:
(i) no cancellation: the tentative outputs are strictly increasing, so each input
transition produces exactly one output transition, at `tent n`;
(ii) every delay `tent n - t n` lies in `[min (δ↑ T0) (δ↓ T0), max δ∞↑ δ∞↓]`;
(iii) for every `N`, the output trace is a `Chan` behaviour of the input trace with
that band. -/
theorem transfer_gap {d T0 : ℝ} (h : P.IsDMin d) (h0 : -d < T0) (t : ℕ → ℝ)
    (ht : ∀ n, t n < t (n + 1)) (hT : ∀ n, T0 ≤ t (n + 1) - P.tent t n) :
    (∀ n, P.tent t n < P.tent t (n + 1)) ∧
    (∀ n, min (P.up T0) (P.down T0) ≤ P.tent t n - t n ∧
          P.tent t n - t n ≤ max P.infUp P.infDown) ∧
    (∀ N, Chan (min (P.up T0) (P.down T0)) (max P.infUp P.infDown)
            (sigOf N t) (sigOf N (P.tent t))) := by
  have hnc : ∀ n, P.tent t n < P.tent t (n + 1) := by
    intro n
    by_contra hc
    push Not at hc
    have := (InvolutionPair.cancel_iff h t ht n).mp hc
    linarith [hT n]
  have hband : ∀ n, min (P.up T0) (P.down T0) ≤ P.tent t n - t n ∧
      P.tent t n - t n ≤ max P.infUp P.infDown := by
    intro n
    cases n with
    | zero =>
      rw [tent_zero]
      have hu := P.up_lt T0 (lt_trans h.mem_up h0)
      refine ⟨?_, ?_⟩
      · have := min_le_left (P.up T0) (P.down T0); linarith
      · have := le_max_left P.infUp P.infDown; linarith
    | succ n =>
      rw [tent_succ_sub]
      obtain ⟨a, b⟩ := delayAt_band h h0 (hT n) (n + 1)
      exact ⟨a, le_of_lt b⟩
  refine ⟨hnc, hband, fun N => ?_⟩
  exact chan_sigOf (strictMono_nat_of_lt_succ ht)
    (monotone_nat_of_le_succ fun n => le_of_lt (hnc n))
    (fun n => (hband n).1) (fun n => (hband n).2) N

theorem infAt_le_max (n : ℕ) : P.infAt n ≤ max P.infUp P.infDown := by
  unfold InvolutionPair.infAt
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- **Transfer, input-separation form.**  If consecutive input transitions are at
least `S` apart, with `S > max δ∞↑ δ∞↓ - δmin`, then the conclusions of
`transfer_gap` hold with `T0 = S - max δ∞↑ δ∞↓`: no cancellation, delays in
`[min (δ↑ T0) (δ↓ T0), max δ∞↑ δ∞↓]` (lower end `> δmin`, `band_lo_gt_dmin`), and
the output trace is a `Chan` behaviour of the input trace. -/
theorem transfer_sep {d S : ℝ} (h : P.IsDMin d) (hS : max P.infUp P.infDown - d < S)
    (t : ℕ → ℝ) (ht : ∀ n, t n + S ≤ t (n + 1)) :
    (∀ n, P.tent t n < P.tent t (n + 1)) ∧
    (∀ n, min (P.up (S - max P.infUp P.infDown)) (P.down (S - max P.infUp P.infDown))
            ≤ P.tent t n - t n ∧ P.tent t n - t n ≤ max P.infUp P.infDown) ∧
    (∀ N, Chan (min (P.up (S - max P.infUp P.infDown)) (P.down (S - max P.infUp P.infDown)))
            (max P.infUp P.infDown) (sigOf N t) (sigOf N (P.tent t))) := by
  have hSpos : 0 < S := by
    have := h.lt_infUp; have := le_max_left P.infUp P.infDown; linarith
  have ht' : ∀ n, t n < t (n + 1) := fun n => by linarith [ht n]
  have hT : ∀ n, S - max P.infUp P.infDown ≤ t (n + 1) - P.tent t n := by
    intro n
    have h1 := P.tent_le t ht' n
    have h2 := infAt_le_max (P := P) n
    linarith [ht n]
  exact transfer_gap (T0 := S - max P.infUp P.infDown) h (by linarith) t ht' hT

/-! ## 4. Sharpness and negative controls -/

/-- The evenly spaced input `t n = n·S`. -/
def spaced (S : ℝ) (n : ℕ) : ℝ := (n : ℝ) * S

theorem spaced_sep (S : ℝ) (n : ℕ) : spaced S n + S ≤ spaced S (n + 1) := by
  unfold spaced; push_cast; linarith [show ((n : ℝ) + 1) * S = (n : ℝ) * S + S by ring1]

/-- **Necessity.**  For every involution pair, an input-separation guarantee
`S ≤ δ∞↑ - δmin` does NOT prevent cancellation: the `S`-spaced input cancels its
first pulse.  With `transfer_sep` this makes `S > δ∞ - δmin` the exact threshold
for symmetric pairs (`δ∞↑ = δ∞↓`); for asymmetric pairs the gap between
`δ∞↑ - δmin` and `max δ∞↑ δ∞↓ - δmin` is not resolved here. -/
theorem sep_threshold_sharp {d S : ℝ} (h : P.IsDMin d) (hS0 : 0 < S)
    (hS : S ≤ P.infUp - d) :
    (∀ n, spaced S n + S ≤ spaced S (n + 1)) ∧
    P.tent (spaced S) 1 ≤ P.tent (spaced S) 0 := by
  have ht : ∀ n, spaced S n < spaced S (n + 1) := fun n => by
    linarith [spaced_sep S n]
  refine ⟨spaced_sep S, (InvolutionPair.cancel_iff h (spaced S) ht 0).mpr ?_⟩
  rw [tent_zero]
  simp only [spaced, Nat.cast_zero, zero_mul, zero_add, Nat.cast_one, one_mul]
  linarith

/-- Negative control at the threshold: `ratPair`, input spaced by exactly
`S = 1 = δ∞ - δmin`, cancels. -/
theorem rat_cancel_at_threshold :
    ratPair.tent (spaced 1) 1 ≤ ratPair.tent (spaced 1) 0 :=
  (sep_threshold_sharp rat_dmin (by norm_num) (by show (1 : ℝ) ≤ 2 - 1; norm_num)).2

/-- Negative control below the threshold (`S = 1/2`). -/
theorem rat_cancel_half :
    ratPair.tent (spaced (1 / 2)) 1 ≤ ratPair.tent (spaced (1 / 2)) 0 :=
  (sep_threshold_sharp rat_dmin (by norm_num) (by show (1 / 2 : ℝ) ≤ 2 - 1; norm_num)).2

/-- The concrete values at the threshold: both tentative outputs are at time 2
(`tent 1 = 1 + δ(1 - 2) = 1 + δ(-1) = 2`), so the pulse is annihilated. -/
theorem rat_threshold_values :
    ratPair.tent (spaced 1) 0 = 2 ∧ ratPair.tent (spaced 1) 1 = 2 := by
  constructor
  · show (((0 : ℕ) : ℝ)) * 1 + 2 = 2; norm_num
  · show (((1 : ℕ) : ℝ)) * 1 + ratDelay ((((1 : ℕ) : ℝ)) * 1 - ((((0 : ℕ) : ℝ)) * 1 + 2)) = 2
    norm_num [ratDelay]

/-- Positive example: with input separation `S = 3/2 > 1`, the `ratPair` channel is
a bounded pure delay in `[4/3, 2]`. -/
theorem rat_transfer_example (t : ℕ → ℝ) (ht : ∀ n, t n + 3 / 2 ≤ t (n + 1)) (N : ℕ) :
    Chan (3 / 2) 2 (sigOf N t) (sigOf N (ratPair.tent t)) := by
  have H := (transfer_sep rat_dmin (S := 3 / 2)
    (by show max (2 : ℝ) 2 - 1 < 3 / 2; norm_num) t ht).2.2 N
  have e1 : min (ratPair.up (3 / 2 - max ratPair.infUp ratPair.infDown))
      (ratPair.down (3 / 2 - max ratPair.infUp ratPair.infDown)) = 4 / 3 := by
    show min (ratDelay (3 / 2 - max 2 2)) (ratDelay (3 / 2 - max 2 2)) = 4 / 3
    norm_num [ratDelay]
  have e2 : max ratPair.infUp ratPair.infDown = 2 := by
    show max (2 : ℝ) 2 = 2; norm_num
  rw [e1, e2] at H
  exact H

end Formal.Core.DelayInvolutionTransfer
