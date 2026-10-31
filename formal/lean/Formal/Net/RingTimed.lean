import Formal.Net.BridgeRing

/-!
# Probe C-9d: the ring rule on bounded-delay timed traces, with a period bound

Probe 9a (`Ring.lean`) proves "a ring of `bd_link_ctl` controllers is dead for `N ≤ 2` and,
with one four-phase token, live iff `N ≥ 3`" in the interleaving (SI) semantics. Probe 8d
(`Bridge`, `BridgeRing`) turned the SI facts into facts about timed traces in which every
stage is an inertial (or no-overtaking) delay channel. This file adds what was missing:

* `timed_ring_three`: the rule as ONE timed statement, both directions. For `0 < K < N`,
  "every inertial timed trace from reset, with any per-stage bounds, toggles some stage
  within its upper bound after every instant" holds iff `N ≥ 3`. The `→` direction is not
  vacuous: the unit-delay trace exists for every network (`Bridge.unit_timed`), and for
  `N ≤ 2` it is frozen (`timed_ring_dead`).
* Max-plus causality on timed traces. `nc x i u` counts the changes of stage `i` before
  `u`. The timed balance law `balance_t` is 9a's `balance` read through 8d's bridge. With
  the inertial cause condition we get the per-stage recurrences
  `nc j u ≤ nc (j-1) (u - lo j) + δ_j` (`fwd`) and
  `nc j u + δ_(j+1) ≤ nc (j+1) (u - lo j) + 1` (`bwd`), where `δ_i` is the wavefront at `i`
  at time 0. Iterated round the ring (`iter_fwd`, `iter_bwd`), with `d ≤ lo i` for every
  stage and `D` wavefronts at time 0:
  - `window_fwd`: at most `D` changes of any stage in any window of `N·d`;
  - `window_bwd`: at most `N - D` changes of any stage in any window of `N·d`;
  - `window_loc`: at most 1 change in any window of `2·d`.
* Period lower bounds from reset (one token, `D = 2`), as event statements:
  - `gap_two`: two changes of one stage are at least `2·d` apart;
  - `gap_three`: three changes of one stage span at least `N·d` (so a full four-phase
    cycle of a stage, rise to rise, takes at least `N·d`);
  - `gap_two_n3`: for `N = 3`, two changes are at least `3·d` apart (rise to rise ≥ `6·d`).
  So the per-token period of a stage is at least `max(N, 4)·dmin` for `N ≥ 4` and
  `6·dmin` for `N = 3`. The upper side is 8o's `OpsRingLive.ring_every_window_reset`:
  every stage changes in every window of `N·H` (`H ≥ hi i`), so rise to rise is at most
  `2·N·H`. Not proved: the exact max-plus cycle time (see the note).
* `ring_no_runt`: in every no-overtaking timed trace of the ring (any bounds), once a stage
  is excited its LUT output stays at the excited value until the stage changes. So the
  LUT output never carries a pulse that the stage does not follow: an inertial channel's
  pulse filter never has anything to swallow, whatever its width, and cannot kill a live
  ring. (Runts need a non-persistent network, e.g. a slow feedback wire:
  `BridgeWire.fb3_timed_token_lost`.)

Hypotheses (all named in the statements): the ring network of `BridgeRing` (real
`bd_c2n`/`bd_c2n_set` LUT in run mode, H_ISO forks, H_FB_SETTLED feedback inside the gate);
`Timed` (H_INERTIAL with per-stage `[lo i, hi i]`, `lo i ≥ 1`) or `TimedF`
(H_NO_OVERTAKE); H_RESET_CLEAN as `x 0 = resetState K` where it is used.
Discrete time (`Nat` ticks); nothing depends on the tick size.
-/

namespace Formal.Net.RingTimed
open Formal.Net Formal.Net.Bridge Formal.Net.Bridge.RingT

/-! ## The rule as one timed statement -/

/-- Liveness after every instant: some stage toggles within its own upper bound. -/
def LiveAfter (n : Nat) (hi : Nat → Nat) (x : Nat → Ring.State) : Prop :=
  ∀ t, ∃ i u, i < n ∧ t ≤ u ∧ u < t + hi i ∧ x (u + 1) i ≠ x u i

/-- **The ring rule, timed, both directions.** For a clean reset with `0 < K < N`: every
inertial timed trace (any per-stage bounds) is live after every instant iff `N ≥ 3`. -/
theorem timed_ring_three (n K : Nat) (hK0 : 0 < K) (hKn : K < n) :
    (∀ (lo hi : Nat → Nat) (x : Nat → Ring.State), Timed (ringNet n K) lo hi x →
        x 0 = Ring.resetState K → LiveAfter n hi x) ↔ 3 ≤ n := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have hx := unit_timed (ringNet n K) (Ring.resetState K)
    obtain ⟨i, u, _, _, _, hc⟩ := h _ _ _ hx rfl 0
    apply hc
    rw [timed_ring_dead (by omega) hx (u + 1), timed_ring_dead (by omega) hx u]
  · intro hn lo hi x hx h0 t
    exact timed_ring_live hn hK0 hKn hx.toF h0 t

/-- The dead direction holds for every trace, not just for one witness: for `N ≤ 2` no
inertial timed trace ever toggles a stage. -/
theorem timed_ring_never (n K : Nat) (hn : n ≤ 2) {lo hi : Nat → Nat} {x : Nat → Ring.State}
    (hx : Timed (ringNet n K) lo hi x) (i u : Nat) : x (u + 1) i = x u i := by
  rw [timed_ring_dead hn hx (u + 1), timed_ring_dead hn hx u]

/-! ## Change counts -/

theorem nf_append (i : Nat) : ∀ a b : List Nat, Ring.nf i (a ++ b) = Ring.nf i a + Ring.nf i b := by
  intro a b
  induction a with
  | nil => simp [Ring.nf]
  | cons j a ih => simp only [List.cons_append, Ring.nf, ih]; omega

theorem nf_nodup (i : Nat) : ∀ {L : List Nat}, L.Nodup → Ring.nf i L = if i ∈ L then 1 else 0 := by
  intro L
  induction L with
  | nil => intro _; simp [Ring.nf]
  | cons j L ih =>
    intro h
    have h' := List.nodup_cons.1 h
    simp only [Ring.nf, ih h'.2, List.mem_cons]
    by_cases e : j = i
    · subst e; simp [h'.1]
    · have : ¬ i = j := fun h => e h.symm
      simp [e, this]

variable {n K : Nat}

/-- Number of changes of node `i` at the steps `0 … u-1`. -/
def nc (n K : Nat) (x : Nat → Ring.State) (i u : Nat) : Nat :=
  Ring.nf i (obs (ringNet n K) x 0 u)

theorem nc_zero (x : Nat → Ring.State) (i : Nat) : nc n K x i 0 = 0 := rfl

theorem nc_succ (x : Nat → Ring.State) (i u : Nat) :
    nc n K x i (u + 1) = nc n K x i u + (if i ∈ chg (ringNet n K) x u then 1 else 0) := by
  unfold nc
  show Ring.nf i (obs (ringNet n K) x 0 u ++ chg (ringNet n K) x (0 + u)) = _
  rw [nf_append, Nat.zero_add, nf_nodup i (chg_nodup x u)]

theorem nc_mono (x : Nat → Ring.State) (i : Nat) {u v : Nat} (h : u ≤ v) :
    nc n K x i u ≤ nc n K x i v := by
  induction v with
  | zero => have : u = 0 := by omega
            subst this; omega
  | succ v ih =>
    by_cases e : u = v + 1
    · subst e; omega
    · have := ih (by omega); rw [nc_succ]; omega

theorem nc_const (x : Nat → Ring.State) (i a : Nat) :
    ∀ m, (∀ w, a ≤ w → w < a + m → x (w + 1) i = x w i) → nc n K x i (a + m) = nc n K x i a := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [← Nat.add_assoc, nc_succ, ih (fun w h1 h2 => h w h1 (by omega))]
    have : i ∉ chg (ringNet n K) x (a + m) := fun hm =>
      (mem_chg.1 hm).2 (h (a + m) (by omega) (by omega)).symm
    simp [this]

theorem nc_step_chg {x : Nat → Ring.State} {i t : Nat} (hi : i < n) (hc : x (t + 1) i ≠ x t i) :
    nc n K x i (t + 1) = nc n K x i t + 1 := by
  rw [nc_succ]
  have : i ∈ chg (ringNet n K) x t := mem_chg.2 ⟨hi, fun h => hc h.symm⟩
  simp [this]

/-- Wavefront at stage `i` at time 0, as a number. -/
def δ (n : Nat) (x : Nat → Ring.State) (i : Nat) : Nat := Ring.b2n (Ring.tok n (x 0) i)

theorem final_eq : ∀ (L : List Nat) (s : Ring.State), Ring.final s L = Bridge.final s L := by
  intro L
  induction L with
  | nil => intro s; rfl
  | cons i L ih => intro s; exact ih _

theorem b2n_le (b : Bool) : Ring.b2n b ≤ 1 := by unfold Ring.b2n; split <;> omega

/-- **Timed balance law** (9a's `balance` through 8d's bridge): a wavefront enters stage
`j` only when stage `j-1` changes and leaves only when `j` changes. -/
theorem balance_t (hn : 3 ≤ n) {hi : Nat → Nat} {x : Nat → Ring.State}
    (hx : TimedF (ringNet n K) hi x) {j : Nat} (hj : j < n) (u : Nat) :
    nc n K x j u + Ring.b2n (Ring.tok n (x u) j) = nc n K x (Ring.prv n j) u + δ n x j := by
  obtain ⟨hr, hf⟩ := timed_runF (ring_persistent n K (x 0)) hx rfl 0 u
  have := Ring.balance hn hj _ _ (run_ring hr)
  rw [final_eq, hf, Nat.zero_add] at this
  exact this

/-! ## Inertial causality -/

section Cause
variable {lo hi : Nat → Nat} {x : Nat → Ring.State}

/-- If stage `j` changes at step `t`, then on the whole window `[t+1-lo j, t]` it held its
old value and was excited (the inertial channel needs the excitation for `lo j` ticks). -/
theorem cause_window (hx : Timed (ringNet n K) lo hi x) {j t : Nat} (hj : j < n)
    (hc : x (t + 1) j ≠ x t j) :
    lo j ≤ t + 1 ∧ ∀ k, k < lo j → x (t - k) j = x t j ∧ Ring.excited n (x (t - k)) j := by
  have g := hx.gate j hj
  obtain ⟨hlo, hw⟩ := g.cause t (fun h => hc h.symm)
  refine ⟨hlo, ?_⟩
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨rfl, ?_⟩
    apply excited_ring.1
    refine ⟨hj, ?_⟩
    have e : (ringNet n K).f j (x t) = x (t + 1) j := hw t (by omega) (Nat.le_refl _)
    rw [Nat.sub_zero, e]; exact hc
  | succ k ih =>
    intro hk
    obtain ⟨ih1, _⟩ := ih (by omega)
    have hv : x (t - (k + 1)) j = x t j := by
      apply Classical.byContradiction
      intro hne
      have e1 : t - (k + 1) + 1 = t - k := by omega
      have hcv : x (t - (k + 1)) j ≠ x (t - (k + 1) + 1) j := by rw [e1, ih1]; exact hne
      obtain ⟨_, hw2⟩ := g.cause (t - (k + 1)) hcv
      have a1 : (ringNet n K).f j (x (t - (k + 1))) = x (t - (k + 1) + 1) j :=
        hw2 (t - (k + 1)) (by omega) (Nat.le_refl _)
      have a2 : (ringNet n K).f j (x (t - (k + 1))) = x (t + 1) j :=
        hw (t - (k + 1)) (by omega) (by omega)
      rw [e1, ih1] at a1
      exact hc (a2.symm.trans a1)
    refine ⟨hv, ?_⟩
    apply excited_ring.1
    refine ⟨hj, ?_⟩
    have e : (ringNet n K).f j (x (t - (k + 1))) = x (t + 1) j := hw _ (by omega) (by omega)
    rw [e, hv]; exact hc

/-- One step of the recurrences: at a change of `j` at step `t`, with `u0 = t+1-lo j`. -/
theorem cause_counts (hn : 3 ≤ n) (hx : Timed (ringNet n K) lo hi x) {j t : Nat} (hj : j < n)
    (hc : x (t + 1) j ≠ x t j) :
    nc n K x j (t + 1) = nc n K x (Ring.prv n j) (t + 1 - lo j) + δ n x j ∧
    nc n K x j (t + 1) + δ n x (Ring.nxt n j) = nc n K x (Ring.nxt n j) (t + 1 - lo j) + 1 := by
  obtain ⟨hlo, hw⟩ := cause_window hx hj hc
  have hlo1 := (hx.gate j hj).lo_pos
  have u0e : t + 1 - lo j = t - (lo j - 1) := by omega
  obtain ⟨_, hex⟩ := hw (lo j - 1) (by omega)
  rw [← u0e] at hex
  -- the count of `j` is flat on [u0, t]
  have flat : nc n K x j t = nc n K x j (t + 1 - lo j) := by
    have := nc_const (n := n) (K := K) x j (t + 1 - lo j) (lo j - 1) (fun w h1 h2 => by
      have a := (hw (t - w) (by omega)).1
      have b := (hw (t - (w + 1)) (by omega)).1
      rw [show t - (t - w) = w by omega] at a
      rw [show t - (t - (w + 1)) = w + 1 by omega] at b
      rw [a, b])
    rwa [show t + 1 - lo j + (lo j - 1) = t by omega] at this
  have step := nc_step_chg (K := K) hj hc
  have tk := (Ring.excited_tok hn _ hj).1 hex
  have hxF := hx.toF
  have b1 := balance_t hn hxF hj (t + 1 - lo j)
  have b2 := balance_t hn hxF (Ring.nxt_lt hj) (t + 1 - lo j)
  rw [Ring.prv_nxt hj] at b2
  rw [tk.1] at b1; rw [tk.2] at b2
  simp only [Ring.b2n] at b1 b2
  simp only [ite_true, ite_false, Bool.false_eq_true] at b1 b2
  constructor <;> omega

/-- **Forward recurrence** at every time: `nc j u ≤ nc (j-1) (u - lo j) + δ_j`. -/
theorem fwd (hn : 3 ≤ n) (hx : Timed (ringNet n K) lo hi x) {j : Nat} (hj : j < n) :
    ∀ u, nc n K x j u ≤ nc n K x (Ring.prv n j) (u - lo j) + δ n x j := by
  intro u
  induction u with
  | zero => rw [nc_zero]; omega
  | succ u ih =>
    by_cases hc : x (u + 1) j = x u j
    · have : nc n K x j (u + 1) = nc n K x j u := by
        rw [nc_succ]
        have : j ∉ chg (ringNet n K) x u := fun hm => (mem_chg.1 hm).2 hc.symm
        simp [this]
      have := nc_mono (n := n) (K := K) x (Ring.prv n j) (show u - lo j ≤ u + 1 - lo j by omega)
      omega
    · exact Nat.le_of_eq (cause_counts hn hx hj hc).1

/-- **Backward recurrence** at every time: `nc j u + δ_(j+1) ≤ nc (j+1) (u - lo j) + 1`. -/
theorem bwd (hn : 3 ≤ n) (hx : Timed (ringNet n K) lo hi x) {j : Nat} (hj : j < n) :
    ∀ u, nc n K x j u + δ n x (Ring.nxt n j) ≤ nc n K x (Ring.nxt n j) (u - lo j) + 1 := by
  intro u
  induction u with
  | zero => rw [nc_zero]; have := b2n_le (Ring.tok n (x 0) (Ring.nxt n j)); unfold δ; omega
  | succ u ih =>
    by_cases hc : x (u + 1) j = x u j
    · have : nc n K x j (u + 1) = nc n K x j u := by
        rw [nc_succ]
        have : j ∉ chg (ringNet n K) x u := fun hm => (mem_chg.1 hm).2 hc.symm
        simp [this]
      have := nc_mono (n := n) (K := K) x (Ring.nxt n j) (show u - lo j ≤ u + 1 - lo j by omega)
      omega
    · exact Nat.le_of_eq (cause_counts hn hx hj hc).2

end Cause

/-! ## Walking round the ring -/

/-- `m` steps backward from `j` (for `m ≤ n`). -/
def bk (n j m : Nat) : Nat := if m ≤ j then j - m else j + n - m
/-- `m` steps forward from `j` (for `m ≤ n`). -/
def fk (n j m : Nat) : Nat := if j + m < n then j + m else j + m - n

theorem bk_lt {j m : Nat} (hj : j < n) (hm : m < n) : bk n j m < n := by
  unfold bk; split <;> omega

theorem bk_succ {j m : Nat} (hj : j < n) (hm : m < n) : bk n j (m + 1) = Ring.prv n (bk n j m) := by
  rw [Ring.prv_eq (bk_lt hj hm)]
  unfold bk
  by_cases h1 : m + 1 ≤ j
  · have h2 : m ≤ j := by omega
    simp only [h1, h2, ite_true]
    have : j - m ≠ 0 := by omega
    simp only [this, ite_false]; omega
  · by_cases h2 : m ≤ j
    · simp only [h1, h2, ite_true, ite_false]
      have : j - m = 0 := by omega
      simp only [this, ite_true]; omega
    · simp only [h1, h2, ite_false]
      have : j + n - m ≠ 0 := by omega
      simp only [this, ite_false]; omega

theorem bk_zero (j : Nat) : bk n j 0 = j := by unfold bk; simp

theorem bk_n {j : Nat} (hj : j < n) : bk n j n = j := by
  unfold bk; have : ¬ n ≤ j := by omega
  simp only [this, ite_false]; omega

theorem fk_lt {j m : Nat} (hj : j < n) (hm : m < n) : fk n j m < n := by
  unfold fk; split <;> omega

theorem fk_succ {j m : Nat} (hj : j < n) (hm : m < n) : fk n j (m + 1) = Ring.nxt n (fk n j m) := by
  rw [Ring.nxt_eq (fk_lt hj hm)]
  unfold fk
  by_cases h1 : j + m < n
  · simp only [h1, ite_true]
    by_cases h2 : j + m + 1 < n
    · have : j + (m + 1) < n := by omega
      simp only [this, h2, ite_true]; omega
    · have : ¬ j + (m + 1) < n := by omega
      simp only [this, h2, ite_false]; omega
  · have : ¬ j + (m + 1) < n := by omega
    simp only [h1, this, ite_false]
    have : j + m - n + 1 < n := by omega
    simp only [this, ite_true]; omega

theorem fk_zero {j : Nat} (hj : j < n) : fk n j 0 = j := by
  unfold fk; simp [hj]

theorem fk_n {j : Nat} (_hj : j < n) : fk n j n = j := by
  unfold fk; have : ¬ j + n < n := by omega
  simp only [this, ite_false]; omega

/-! ### Sums -/

theorem sumTo_congr {g h : Nat → Nat} : ∀ {a : Nat}, (∀ k, k < a → g k = h k) →
    Ring.sumTo g a = Ring.sumTo h a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro hk
    simp only [Ring.sumTo]
    rw [ih (fun k h' => hk k (by omega)), hk a (by omega)]

theorem sumTo_add (g : Nat → Nat) (a : Nat) : ∀ b,
    Ring.sumTo g (a + b) = Ring.sumTo g a + Ring.sumTo (fun k => g (a + k)) b := by
  intro b
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [← Nat.add_assoc]; simp only [Ring.sumTo]; rw [ih]; omega

theorem sumTo_front (g : Nat → Nat) : ∀ a,
    Ring.sumTo g (a + 1) = g 0 + Ring.sumTo (fun k => g (k + 1)) a := by
  intro a
  induction a with
  | zero => simp [Ring.sumTo]
  | succ a ih =>
    show Ring.sumTo g (a + 1) + g (a + 1) = g 0 + (Ring.sumTo (fun k => g (k + 1)) a + g (a + 1))
    rw [ih]; omega

theorem sumTo_rev (g : Nat → Nat) : ∀ a,
    Ring.sumTo (fun k => g (a - 1 - k)) a = Ring.sumTo g a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [sumTo_front]
    have : Ring.sumTo (fun k => g (a + 1 - 1 - (k + 1))) a = Ring.sumTo (fun k => g (a - 1 - k)) a :=
      sumTo_congr (fun k _ => by rw [show a + 1 - 1 - (k + 1) = a - 1 - k by omega])
    rw [this, ih]
    show g (a + 1 - 1 - 0) + Ring.sumTo g a = Ring.sumTo g a + g a
    rw [show a + 1 - 1 - 0 = a by omega]; omega

theorem cnt_eq_sum (f : Nat → Bool) : ∀ m, Ring.cnt f m = Ring.sumTo (fun i => Ring.b2n (f i)) m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => simp only [Ring.cnt, Ring.sumTo, ih, Ring.b2n]

theorem bk_sum (g : Nat → Nat) {j : Nat} (hj : j < n) :
    Ring.sumTo (fun k => g (bk n j k)) n = Ring.sumTo g n := by
  have hn : n = (j + 1) + (n - j - 1) := by omega
  rw [hn, sumTo_add, sumTo_add g]
  congr 1
  · rw [← sumTo_rev g (j + 1)]
    exact sumTo_congr (fun k hk => by
      unfold bk; have : k ≤ j := by omega
      simp only [this, ite_true]; rw [show j + 1 - 1 - k = j - k by omega])
  · rw [← sumTo_rev (fun k => g (j + 1 + k)) (n - j - 1)]
    exact sumTo_congr (fun k hk => by
      unfold bk
      have : ¬ j + 1 + k ≤ j := by omega
      simp only [this, ite_false]
      have e1 : j + 1 + (n - j - 1 - 1 - k) = j + ((j + 1) + (n - j - 1)) - (j + 1 + k) := by omega
      rw [e1])

theorem fk_sum (g : Nat → Nat) {j : Nat} (hj : j < n) :
    Ring.sumTo (fun k => g (fk n j (k + 1))) n = Ring.sumTo g n := by
  have e1 := sumTo_add (fun k => g (fk n j (k + 1))) (n - j - 1) (j + 1)
  have e2 := sumTo_add g (j + 1) (n - j - 1)
  rw [show n - j - 1 + (j + 1) = n by omega] at e1
  rw [show j + 1 + (n - j - 1) = n by omega] at e2
  rw [e1, e2, Nat.add_comm]
  congr 1
  · exact sumTo_congr (fun k hk => by
      unfold fk
      have : ¬ j + (n - j - 1 + k + 1) < n := by omega
      simp only [this, ite_false]
      rw [show j + (n - j - 1 + k + 1) - n = k by omega])
  · exact sumTo_congr (fun k hk => by
      unfold fk
      have : j + (k + 1) < n := by omega
      simp only [this, ite_true]
      rw [show j + (k + 1) = j + 1 + k by omega])

theorem sum_bk_D {j : Nat} (hj : j < n) (x : Nat → Ring.State) :
    Ring.sumTo (fun k => δ n x (bk n j k)) n = Ring.D n (x 0) := by
  rw [bk_sum (δ n x) hj]; unfold Ring.D δ; rw [cnt_eq_sum]

theorem sum_fk_D {j : Nat} (hj : j < n) (x : Nat → Ring.State) :
    Ring.sumTo (fun k => δ n x (fk n j (k + 1))) n = Ring.D n (x 0) := by
  rw [fk_sum (δ n x) hj]; unfold Ring.D δ; rw [cnt_eq_sum]

/-! ## Window bounds -/

section Windows
variable {lo hi : Nat → Nat} {x : Nat → Ring.State} {d : Nat}

theorem iter_fwd (hn : 3 ≤ n) (hx : Timed (ringNet n K) lo hi x) (hd : ∀ i, i < n → d ≤ lo i)
    {j : Nat} (hj : j < n) (u : Nat) : ∀ m, m ≤ n →
    nc n K x j u ≤ nc n K x (bk n j m) (u - m * d) + Ring.sumTo (fun k => δ n x (bk n j k)) m := by
  intro m
  induction m with
  | zero => intro _; rw [bk_zero]; simp [Ring.sumTo]
  | succ m ih =>
    intro hm
    have ih := ih (by omega)
    have hbl := bk_lt hj (show m < n by omega)
    have f := fwd hn hx hbl (u - m * d)
    have mo := nc_mono (n := n) (K := K) x (Ring.prv n (bk n j m))
      (show u - m * d - lo (bk n j m) ≤ u - (m + 1) * d by
        have := hd _ hbl; rw [Nat.succ_mul]; omega)
    rw [bk_succ hj (by omega)]
    simp only [Ring.sumTo]
    omega

theorem iter_bwd (hn : 3 ≤ n) (hx : Timed (ringNet n K) lo hi x) (hd : ∀ i, i < n → d ≤ lo i)
    {j : Nat} (hj : j < n) (u : Nat) : ∀ m, m ≤ n →
    nc n K x j u + Ring.sumTo (fun k => δ n x (fk n j (k + 1))) m ≤
      nc n K x (fk n j m) (u - m * d) + m := by
  intro m
  induction m with
  | zero => intro _; rw [fk_zero hj]; simp [Ring.sumTo]
  | succ m ih =>
    intro hm
    have ih := ih (by omega)
    have hfl := fk_lt hj (show m < n by omega)
    have b := bwd hn hx hfl (u - m * d)
    have mo := nc_mono (n := n) (K := K) x (Ring.nxt n (fk n j m))
      (show u - m * d - lo (fk n j m) ≤ u - (m + 1) * d by
        have := hd _ hfl; rw [Nat.succ_mul]; omega)
    rw [← fk_succ hj (by omega)] at b mo
    simp only [Ring.sumTo]
    omega

/-- **At most `D` changes of a stage in any window of `N·d`.** -/
theorem window_fwd (hn : 3 ≤ n) (hx : Timed (ringNet n K) lo hi x) (hd : ∀ i, i < n → d ≤ lo i)
    {j : Nat} (hj : j < n) (u : Nat) :
    nc n K x j (u + n * d) ≤ nc n K x j u + Ring.D n (x 0) := by
  have := iter_fwd hn hx hd hj (u + n * d) n (Nat.le_refl _)
  rwa [bk_n hj, sum_bk_D hj, Nat.add_sub_cancel] at this

/-- **At most `N - D` changes of a stage in any window of `N·d`.** -/
theorem window_bwd (hn : 3 ≤ n) (hx : Timed (ringNet n K) lo hi x) (hd : ∀ i, i < n → d ≤ lo i)
    {j : Nat} (hj : j < n) (u : Nat) :
    nc n K x j (u + n * d) + Ring.D n (x 0) ≤ nc n K x j u + n := by
  have := iter_bwd hn hx hd hj (u + n * d) n (Nat.le_refl _)
  rwa [fk_n hj, sum_fk_D hj, Nat.add_sub_cancel] at this

/-- **At most one change of a stage in any window of `2·d`** (the local cycle through a
neighbour). -/
theorem window_loc (hn : 3 ≤ n) (hx : Timed (ringNet n K) lo hi x) (hd : ∀ i, i < n → d ≤ lo i)
    {j : Nat} (hj : j < n) (u : Nat) :
    nc n K x j (u + 2 * d) ≤ nc n K x j u + 1 := by
  have hp := Ring.prv_lt hj
  have f := fwd hn hx hj (u + 2 * d)
  have b := bwd hn hx hp (u + 2 * d - lo j)
  rw [Ring.nxt_prv hj] at b
  have m1 := nc_mono (n := n) (K := K) x (Ring.prv n j)
    (show u + 2 * d - lo j ≤ u + 2 * d - d by have := hd j hj; omega)
  have m2 := nc_mono (n := n) (K := K) x j
    (show u + 2 * d - lo j - lo (Ring.prv n j) ≤ u by
      have := hd j hj; have := hd _ hp; omega)
  have hbd := bwd hn hx hp (u + 2 * d - lo j)
  rw [Ring.nxt_prv hj] at hbd
  omega

/-! ### Event form: gaps between changes of one stage -/

theorem two_changes {j t1 t2 : Nat} (hj : j < n) (h12 : t1 < t2)
    (c1 : x (t1 + 1) j ≠ x t1 j) (c2 : x (t2 + 1) j ≠ x t2 j) :
    nc n K x j t1 + 2 ≤ nc n K x j (t2 + 1) := by
  have a := nc_step_chg (K := K) hj c1
  have b := nc_step_chg (K := K) hj c2
  have m := nc_mono (n := n) (K := K) x j (show t1 + 1 ≤ t2 by omega)
  omega

/-- **Two changes of one stage are at least `2·d` apart.** -/
theorem gap_two (hn : 3 ≤ n) (hx : Timed (ringNet n K) lo hi x) (hd : ∀ i, i < n → d ≤ lo i)
    {j t1 t2 : Nat} (hj : j < n) (h12 : t1 < t2)
    (c1 : x (t1 + 1) j ≠ x t1 j) (c2 : x (t2 + 1) j ≠ x t2 j) : t1 + 2 * d ≤ t2 := by
  apply Classical.byContradiction
  intro h
  have w := window_loc hn hx hd hj t1
  have m := nc_mono (n := n) (K := K) x j (show t2 + 1 ≤ t1 + 2 * d by omega)
  have := two_changes (K := K) hj h12 c1 c2
  omega

/-- **Three changes of one stage span at least `N·d`** when the ring holds one token
(`D = 2` at time 0, e.g. from a clean reset: `Ring.D_reset`). So rise to rise of any
stage takes at least `N·dmin`. -/
theorem gap_three (hn : 3 ≤ n) (hx : Timed (ringNet n K) lo hi x) (hd : ∀ i, i < n → d ≤ lo i)
    (hD : Ring.D n (x 0) = 2) {j t1 t2 t3 : Nat} (hj : j < n) (h12 : t1 < t2) (h23 : t2 < t3)
    (c1 : x (t1 + 1) j ≠ x t1 j) (c2 : x (t2 + 1) j ≠ x t2 j) (c3 : x (t3 + 1) j ≠ x t3 j) :
    t1 + n * d ≤ t3 := by
  apply Classical.byContradiction
  intro h
  have w := window_fwd hn hx hd hj t1
  rw [hD] at w
  have m := nc_mono (n := n) (K := K) x j (show t3 + 1 ≤ t1 + n * d by omega)
  have a := two_changes (K := K) hj h12 c1 c2
  have b := nc_step_chg (K := K) hj c3
  have m2 := nc_mono (n := n) (K := K) x j (show t2 + 1 ≤ t3 by omega)
  omega

/-- **`N = 3`: two changes of one stage are at least `3·d` apart**, so rise to rise is at
least `6·dmin` (the backward ring carries `N - D = 1` bubble). -/
theorem gap_two_n3 (hx : Timed (ringNet 3 K) lo hi x) (hd : ∀ i, i < 3 → d ≤ lo i)
    (hD : Ring.D 3 (x 0) = 2) {j t1 t2 : Nat} (hj : j < 3) (h12 : t1 < t2)
    (c1 : x (t1 + 1) j ≠ x t1 j) (c2 : x (t2 + 1) j ≠ x t2 j) : t1 + 3 * d ≤ t2 := by
  apply Classical.byContradiction
  intro h
  have w := window_bwd (Nat.le_refl 3) hx hd hj t1
  rw [hD] at w
  have m := nc_mono (n := 3) (K := K) x j (show t2 + 1 ≤ t1 + 3 * d by omega)
  have := two_changes (K := K) hj h12 c1 c2
  omega

/-- The same bounds from a clean reset (`0 < K < N`): the reset state carries `D = 2`. -/
theorem gap_three_reset (hn : 3 ≤ n) (hK0 : 0 < K) (hKn : K < n)
    (hx : Timed (ringNet n K) lo hi x) (h0 : x 0 = Ring.resetState K)
    (hd : ∀ i, i < n → d ≤ lo i) {j t1 t2 t3 : Nat} (hj : j < n) (h12 : t1 < t2) (h23 : t2 < t3)
    (c1 : x (t1 + 1) j ≠ x t1 j) (c2 : x (t2 + 1) j ≠ x t2 j) (c3 : x (t3 + 1) j ≠ x t3 j) :
    t1 + n * d ≤ t3 :=
  gap_three hn hx hd (by rw [h0]; exact Ring.D_reset hK0 hKn) hj h12 h23 c1 c2 c3

end Windows

/-! ## No runts -/

/-- **No runt on a ring LUT.** In every no-overtaking timed trace of the ring from a
reachable start (any per-stage bounds), once stage `j` is excited, its LUT output keeps the
excited value until the stage changes. So the LUT output never shows a pulse that the stage
does not follow, and a pulse filter of any width never swallows one. -/
theorem ring_no_runt {hi : Nat → Nat} {x : Nat → Ring.State} (hx : TimedF (ringNet n K) hi x)
    {t u j : Nat} (htu : t ≤ u) (he : Ring.excited n (x t) j)
    (hstill : ∀ w, t ≤ w → w < u → x (w + 1) j = x w j) :
    Ring.excited n (x u) j ∧ Ring.gate n K false (x u) j = Ring.gate n K false (x t) j := by
  have hp := ring_persistent n K (x 0)
  obtain ⟨hr, hf⟩ := timed_runF hp hx rfl t (u - t)
  have hni : j ∉ obs (ringNet n K) x t (u - t) := not_mem_obs (fun w h1 h2 => hstill w h1 (by omega))
  have := persist_run hp (timed_reachF hp hx rfl t) (excited_ring.2 he) hr hni
  rw [hf, show t + (u - t) = u by omega] at this
  have he' := excited_ring.1 this
  refine ⟨he', ?_⟩
  have xs : x u j = x t j := by
    have key : ∀ m, m ≤ u - t → x (t + m) j = x t j := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ m ih => intro hm; rw [← Nat.add_assoc, hstill (t + m) (by omega) (by omega), ih (by omega)]
    have := key (u - t) (Nat.le_refl _); rwa [show t + (u - t) = u by omega] at this
  have a := ((Ring.excited_gate n K _ j).1 he').2
  have b := ((Ring.excited_gate n K _ j).1 he).2
  rw [xs] at a
  revert a b; cases Ring.gate n K false (x u) j <;> cases Ring.gate n K false (x t) j <;>
    cases x t j <;> simp

/-! ## The lower bounds are attained (unit delay, `d = 1`)

`unitTrace` is an inertial trace with `lo = hi = 1` (`Bridge.unit_timed`). On it the bounds
of `gap_two_n3`, `gap_two` and `gap_three` are met with equality, so none of them can be
improved in general. -/

/-- `N = 3`: stage 0 changes at steps 1 and 4: gap `3 = 3·d`. -/
theorem tight_n3 :
    unitTrace (ringNet 3 1) (Ring.resetState 1) 2 0 ≠ unitTrace (ringNet 3 1) (Ring.resetState 1) 1 0 ∧
    unitTrace (ringNet 3 1) (Ring.resetState 1) 5 0 ≠ unitTrace (ringNet 3 1) (Ring.resetState 1) 4 0 := by
  decide +kernel

/-- `N = 4`: stage 0 changes at steps 1 and 3: gap `2 = 2·d`; and 1, 3, 5: span `4 = N·d`. -/
theorem tight_n4 :
    unitTrace (ringNet 4 1) (Ring.resetState 1) 2 0 ≠ unitTrace (ringNet 4 1) (Ring.resetState 1) 1 0 ∧
    unitTrace (ringNet 4 1) (Ring.resetState 1) 4 0 ≠ unitTrace (ringNet 4 1) (Ring.resetState 1) 3 0 ∧
    unitTrace (ringNet 4 1) (Ring.resetState 1) 6 0 ≠ unitTrace (ringNet 4 1) (Ring.resetState 1) 5 0 := by
  decide +kernel

/-- `N = 5`: stage 0 changes at steps 1, 4, 6: span `5 = N·d`. -/
theorem tight_n5 :
    unitTrace (ringNet 5 1) (Ring.resetState 1) 2 0 ≠ unitTrace (ringNet 5 1) (Ring.resetState 1) 1 0 ∧
    unitTrace (ringNet 5 1) (Ring.resetState 1) 5 0 ≠ unitTrace (ringNet 5 1) (Ring.resetState 1) 4 0 ∧
    unitTrace (ringNet 5 1) (Ring.resetState 1) 7 0 ≠ unitTrace (ringNet 5 1) (Ring.resetState 1) 6 0 := by
  decide +kernel

/-- Non-vacuity of the window theorems' hypotheses: the unit-delay trace from reset is an
inertial trace with `d = 1 ≤ lo i`. -/
theorem unit_hyps (n K : Nat) :
    Timed (ringNet n K) (fun _ => 1) (fun _ => 1) (unitTrace (ringNet n K) (Ring.resetState K)) ∧
    (∀ i, i < n → 1 ≤ (fun _ => 1) i) :=
  ⟨unit_timed _ _, fun _ _ => Nat.le_refl _⟩

end Formal.Net.RingTimed
