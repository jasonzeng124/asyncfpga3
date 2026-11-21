import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Formal.Core.Trace.Discrete
import Formal.Core.Delay.Pure
import Formal.Net.Prelim
import Formal.Cells.CElemTiming
/-!
# Discretisation soundness: from continuous (`ℝ`) to discrete (`ℕ`) time

Shards B and C prove cells and networks in discrete time (`ℕ → Bool`, one
step = one quantum `q`, e.g. 1 ps). This file proves when such proofs say
something about continuous time.

Continuous model: `Formal.Core.DelayPure.Chan lo hi x y` (FIFO transport
channel, read-time map `σ`). Discrete model:
`Formal.Core.TraceDiscrete.Transport L H xd yd` (monotone warp `f`).
Sampling: `sample q x k = x (k * q)`.

## Results

* `chan_sample` (**discretisation soundness, one channel**): if `x` is
  `Sep q` (no two transitions within one quantum, `Sep`) and at rest before
  time 0 (`AtRest`), then the samples of every continuous `[lo, hi]`
  behaviour are a discrete `[L, H]` behaviour for any naturals with
  `L * q ≤ lo` and `hi ≤ H * q`; the tightest choice is
  `L = ⌊lo/q⌋`, `H = ⌈hi/q⌉`. **Only the channel input needs `Sep`**,
  the output does not.
* `gate_sample`, `gate2_sample`: a zero-delay Boolean function followed by a
  channel. The separation hypothesis is on the gate's **excitation**, which
  follows from JOINT separation of its inputs (`sep_map`), not from
  separation of each input alone (`tie_counterexample`).
* `circuit_sample`: a circuit (a conjunction of gate relations over a net
  type `N`) — every continuous behaviour sampled is a discrete behaviour of
  the widened circuit. `transfer`, `transfer_invariant`: any property proved
  for all discrete behaviours of the widened circuit holds of the samples of
  every continuous behaviour.
* Between grid points: `stable_between` (a `Sep q` signal that is `v` at the
  grid points `K1..K2` is `v` on the whole real interval `[K1 q, K2 q]`, so
  real-time stability on `[a, b]` follows from discrete stability on the grid
  interval `[⌊a/q⌋, ⌈b/q⌉]`, at most one quantum longer at each end);
  `invariant_everywhere` (a state invariant over a JOINTLY separated tuple of
  nets holds at every real time if it holds at every grid point).
* Counterexamples when separation fails (`runt_*`, `tie_*`, `mutex_*`): a
  sub-quantum runt between two grid points is invisible to sampling at the
  channel input but, shifted by the channel delay, visible at the output, so
  NO discrete `[L, H]` channel relates the samples, for any `L, H`. The runt
  is the excitation of an AND whose inputs (each perfectly clean) cross within
  one quantum: this is the arbiter's sub-quantum tie / runt case. Likewise a
  mutual-exclusion invariant can hold at all grid points and fail between.
* Bridges to the other shards' channel relations:
  `transport_boundedDelay` (into shard C's `Formal.Net.BoundedDelay`),
  `chan_sample_win` (into shard B's `Formal.Cells.CElemTiming.WinDelay`, no `AtRest`
  needed), and `loop_of_continuous`: the samples of every continuous
  feedback-LUT behaviour (with `Sep` on the excitation and on `O`) form a
  `Formal.Cells.CElemTiming.Loop`, so `c2_follow_hold`, `c2_reset`, ... apply to them.

`Archimedean ℝ` is not built in this Mathlib checkout, so no `⌊·⌋`: the
grid cell of a time `s` is found by a least-element search
(`TraceDiscrete.exists_least`) whose existence witness comes from the channel
bound `σ (k q) ≤ k q`.
-/

namespace Formal.Core.Discretize

open Formal.Core

/-! ## Separation, rest, sampling -/

/-- **H-SEP** (no two transitions within one quantum): in any window of
length `≤ q`, the value at an interior point equals the value at one of the
ends. For `Bool` this says a value can not be left and re-entered within `q`
(`sep_bool`): every pulse is at least `q` wide. For a tuple of nets it says
the tuple changes at most once per window (joint separation). -/
def Sep {α : Type*} (q : ℝ) (x : ℝ → α) : Prop :=
  ∀ a b c : ℝ, a ≤ b → b ≤ c → c - a ≤ q → x b = x a ∨ x b = x c

/-- **H-REST**: the signal is constant up to time 0 (the discrete model's
convention that a signal is constant before step 0). -/
def AtRest {α : Type*} (x : ℝ → α) : Prop := ∀ t : ℝ, t ≤ 0 → x t = x 0

/-- Sampling on the grid `k * q`. -/
def sample {α : Type*} (q : ℝ) (x : ℝ → α) : ℕ → α := fun k => x ((k : ℝ) * q)

theorem sep_map {α β : Type*} {q : ℝ} {x : ℝ → α} (g : α → β) (h : Sep q x) :
    Sep q (fun t => g (x t)) := by
  intro a b c h1 h2 h3
  rcases h a b c h1 h2 h3 with e | e
  · left; simp only [e]
  · right; simp only [e]

theorem atRest_map {α β : Type*} {x : ℝ → α} (g : α → β) (h : AtRest x) :
    AtRest (fun t => g (x t)) := by
  intro t ht; simp only [h t ht]

theorem sep_anti {α : Type*} {q q' : ℝ} {x : ℝ → α} (hq : q' ≤ q) (h : Sep q x) :
    Sep q' x := fun a b c h1 h2 h3 => h a b c h1 h2 (le_trans h3 hq)

theorem sep_bool {q : ℝ} {x : ℝ → Bool} (h : Sep q x) {a b c : ℝ}
    (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c - a ≤ q) (he : x a = x c) : x b = x a := by
  rcases h a b c h1 h2 h3 with e | e
  · exact e
  · rw [e, he]

/-- For `Bool`, `Sep` is exactly "no excursion shorter than `q`". -/
theorem sep_bool_iff {q : ℝ} {x : ℝ → Bool} :
    Sep q x ↔ ∀ a b c : ℝ, a ≤ b → b ≤ c → c - a ≤ q → x a = x c → x b = x a := by
  constructor
  · intro h a b c h1 h2 h3 he; exact sep_bool h h1 h2 h3 he
  · intro h a b c h1 h2 h3
    by_cases he : x a = x c
    · exact Or.inl (h a b c h1 h2 h3 he)
    · cases hb : x b <;> cases ha : x a <;> cases hc : x c <;> simp_all

/-- A monotone (single-step) Boolean signal is separated for every `q`. -/
theorem sep_of_monotone {q : ℝ} {x : ℝ → Bool}
    (h : ∀ a b, a ≤ b → x a = true → x b = true) : Sep q x := by
  intro a b c h1 h2 _
  cases hb : x b
  · left; cases ha : x a
    · rfl
    · rw [h a b h1 ha] at hb; exact absurd hb (by decide)
  · right; exact (h b c h2 hb).symm

theorem sep_of_antitone {q : ℝ} {x : ℝ → Bool}
    (h : ∀ a b, a ≤ b → x b = true → x a = true) : Sep q x := by
  intro a b c h1 h2 _
  cases hb : x b
  · right; cases hc : x c
    · rfl
    · rw [h b c h2 hc] at hb; exact absurd hb (by decide)
  · left; exact (h a b h1 hb).symm

/-- **Separation through a channel.** A channel can narrow a pulse by
`hi - lo`, so separation `q + (hi - lo)` at the input gives separation `q` at
the output (the FIFO read map `σ` stretches a window by at most `hi - lo`). -/
theorem sep_out {q lo hi : ℝ} {x y : ℝ → Bool} (hc : DelayPure.Chan lo hi x y)
    (hsep : Sep (q + (hi - lo)) x) : Sep q y := by
  obtain ⟨r, e⟩ := hc
  rw [sep_bool_iff]
  intro a b c h1 h2 h3 he
  rw [e, e] at he ⊢
  have := r.le c; have := r.ge a
  exact sep_bool hsep (r.mono _ _ h1) (r.mono _ _ h2) (by linarith) he

/-! ## Grid cells without `Archimedean`

`Below q s n` says `s < (n+1) q`. `cell q s` is the least such `n`, which is
`⌊s/q⌋` for `s ≥ 0` and `0` for `s < 0`. Existence is passed in as a
hypothesis (a witness always exists by the Archimedean property, which this
Mathlib checkout has not built; here the witness comes from the channel). -/

def Below (q s : ℝ) (n : ℕ) : Prop := s < ((n : ℝ) + 1) * q

open Classical in
/-- The grid cell of time `s` (least `n` with `s < (n+1) q`). -/
noncomputable def cell (q s : ℝ) : ℕ :=
  if h : ∃ n, Below q s n then Classical.choose (TraceDiscrete.exists_least _ h) else 0

theorem cell_spec {q s : ℝ} (h : ∃ n, Below q s n) :
    Below q s (cell q s) ∧ ∀ m, m < cell q s → ¬ Below q s m := by
  unfold cell; rw [dif_pos h]; exact Classical.choose_spec (TraceDiscrete.exists_least _ h)

theorem cell_lt {q s : ℝ} (h : ∃ n, Below q s n) : s < ((cell q s : ℝ) + 1) * q :=
  (cell_spec h).1

theorem cell_low {q s : ℝ} (h : ∃ n, Below q s n) :
    cell q s = 0 ∨ (cell q s : ℝ) * q ≤ s := by
  rcases hc : cell q s with _ | n
  · left; rfl
  · right
    have := (cell_spec h).2 n (by omega)
    unfold Below at this
    push_cast
    exact not_lt.mp this

theorem cell_mono {q s s' : ℝ} (hss : s ≤ s') (h' : ∃ n, Below q s' n) :
    cell q s ≤ cell q s' := by
  have h : ∃ n, Below q s n := by
    obtain ⟨n, hn⟩ := h'; exact ⟨n, lt_of_le_of_lt hss hn⟩
  by_contra hlt
  exact (cell_spec h).2 (cell q s') (by omega) (lt_of_le_of_lt hss (cell_lt h'))

/-- Natural-number comparison from a real one scaled by `q > 0`. -/
theorem nat_lt_of_mul {q : ℝ} (hq : 0 < q) {a b : ℕ} (h : (a : ℝ) * q < (b : ℝ) * q) :
    a < b := by
  by_contra hc
  have h1 : (b : ℝ) ≤ a := by exact_mod_cast Nat.le_of_not_lt hc
  have := mul_le_mul_of_nonneg_right h1 hq.le
  linarith

/-! ## Picking a grid point that shows the same value -/

/-- The grid index read for time `s`: the left end of its cell if it shows
the same value, else the right end. -/
noncomputable def pick (q : ℝ) (x : ℝ → Bool) (s : ℝ) : ℕ :=
  if x s = x ((cell q s : ℝ) * q) then cell q s else cell q s + 1

/-- If the left end of the cell disagrees with `x s`, then `s` is strictly
inside the cell (needs the rest hypothesis for `s < 0`). -/
theorem cell_strict {q s : ℝ} {x : ℝ → Bool} (h : ∃ n, Below q s n)
    (hneg : s < 0 → x s = x 0) (hne : x s ≠ x ((cell q s : ℝ) * q)) :
    (cell q s : ℝ) * q < s := by
  rcases cell_low h with h0 | hle
  · rw [h0] at hne ⊢
    simp only [Nat.cast_zero, zero_mul] at hne ⊢
    rcases lt_trichotomy s 0 with hs | hs | hs
    · exact absurd (hneg hs) hne
    · rw [hs] at hne; exact absurd rfl hne
    · exact hs
  · rcases lt_or_eq_of_le hle with hl | he
    · exact hl
    · rw [he] at hne; exact absurd rfl hne

theorem pick_val {q s : ℝ} {x : ℝ → Bool} (hsep : Sep q x)
    (h : ∃ n, Below q s n) (hneg : s < 0 → x s = x 0) :
    x ((pick q x s : ℝ) * q) = x s := by
  unfold pick
  split
  · rename_i he; exact he.symm
  · rename_i hne
    have hl := cell_strict h hneg hne
    have hr := cell_lt h
    push_cast
    rcases hsep ((cell q s : ℝ) * q) s (((cell q s : ℝ) + 1) * q) hl.le hr.le
      (by linarith) with e | e
    · exact absurd e hne
    · exact e.symm

theorem pick_ge {q s : ℝ} {x : ℝ → Bool} : cell q s ≤ pick q x s := by
  unfold pick; split <;> omega

theorem pick_cases {q s : ℝ} {x : ℝ → Bool} (h : ∃ n, Below q s n)
    (hneg : s < 0 → x s = x 0) :
    (pick q x s = cell q s) ∨ ((cell q s : ℝ) * q < s ∧ pick q x s = cell q s + 1) := by
  unfold pick
  split
  · left; rfl
  · rename_i hne; right; exact ⟨cell_strict h hneg hne, rfl⟩

theorem pick_eq_cell {q s : ℝ} {x : ℝ → Bool} (h : pick q x s = cell q s) :
    x s = x ((cell q s : ℝ) * q) := by
  unfold pick at h; split at h
  · assumption
  · omega

theorem pick_ne_cell {q s : ℝ} {x : ℝ → Bool} (h : pick q x s = cell q s + 1) :
    x s ≠ x ((cell q s : ℝ) * q) := by
  unfold pick at h; split at h
  · omega
  · assumption

theorem pick_mono {q s s' : ℝ} {x : ℝ → Bool} (hsep : Sep q x)
    (hss : s ≤ s') (h' : ∃ n, Below q s' n) (hneg : s < 0 → x s = x 0) :
    pick q x s ≤ pick q x s' := by
  have h : ∃ n, Below q s n := by
    obtain ⟨n, hn⟩ := h'; exact ⟨n, lt_of_le_of_lt hss hn⟩
  have hc := cell_mono hss h'
  have g' : cell q s' ≤ pick q x s' := pick_ge
  rcases pick_cases h hneg with e | ⟨hl, e⟩
  · omega
  · by_contra hlt
    -- then `s, s'` share a cell and `pick s' = cell`: Sep is violated
    have heq : cell q s = cell q s' := by omega
    have e' : pick q x s' = cell q s' := by
      have : pick q x s' ≤ cell q s' + 1 := by unfold pick; split <;> omega
      omega
    have he' := pick_eq_cell e'
    have hne := pick_ne_cell e
    have hr := cell_lt h'
    rw [← heq] at he' hr
    exact hne (sep_bool hsep hl.le hss (by linarith) he'.symm)

/-! ## Discretisation soundness for one channel -/

/-- Bounds on the picked index, for a read time `s` of output step `k`. -/
theorem pick_bounds {q lo hi s : ℝ} {L H k : ℕ} {x : ℝ → Bool} (hq : 0 < q)
    (hL : (L : ℝ) * q ≤ lo) (hH : hi ≤ (H : ℝ) * q)
    (hs1 : (k : ℝ) * q - hi ≤ s) (hs2 : s ≤ (k : ℝ) * q - lo)
    (hneg : s < 0 → x s = x 0) :
    (∃ n, Below q s n) ∧ pick q x s ≤ k - L ∧ k - H ≤ pick q x s := by
  have hlo : 0 ≤ lo := le_trans (mul_nonneg (Nat.cast_nonneg L) hq.le) hL
  have hex : ∃ n, Below q s n := ⟨k, by unfold Below; linarith⟩
  refine ⟨hex, ?_, ?_⟩
  · rcases pick_cases hex hneg with e | ⟨hl, e⟩
    · rw [e]
      rcases cell_low hex with h0 | hle
      · omega
      · rcases Nat.eq_zero_or_pos (cell q s) with h0 | _
        · omega
        have : cell q s + L ≤ k := by
          by_contra hc
          have : k < cell q s + L := by omega
          have h2 : (k : ℝ) * q < ((cell q s + L : ℕ) : ℝ) * q := by
            have h3 : ((k + 1 : ℕ) : ℝ) ≤ ((cell q s + L : ℕ) : ℝ) := by
              exact_mod_cast this
            push_cast at h3 ⊢
            nlinarith
          push_cast at h2
          linarith
        omega
    · rw [e]
      have : cell q s + L < k := nat_lt_of_mul hq (by push_cast; linarith)
      omega
  · have g := (pick_ge : cell q s ≤ pick q x s)
    have hr := cell_lt hex
    have : k < cell q s + 1 + H := nat_lt_of_mul hq (by push_cast; linarith)
    omega

/-- **Discretisation soundness (one channel).** Sampling a continuous
`[lo, hi]` transport behaviour on the grid `k q` gives a discrete `[L, H]`
transport behaviour, for any `L q ≤ lo`, `hi ≤ H q` (best:
`L = ⌊lo/q⌋`, `H = ⌈hi/q⌉`), provided the input is separated by one quantum
(`Sep q x`) and at rest before 0. Nothing is assumed of the output. -/
theorem chan_sample {q lo hi : ℝ} {L H : ℕ} (hq : 0 < q)
    (hL : (L : ℝ) * q ≤ lo) (hH : hi ≤ (H : ℝ) * q)
    {x y : ℝ → Bool} (hc : DelayPure.Chan lo hi x y) (hsep : Sep q x) (hrest : AtRest x) :
    TraceDiscrete.Transport L H (sample q x) (sample q y) := by
  obtain ⟨r, e⟩ := hc
  have hneg : ∀ s : ℝ, s < 0 → x s = x 0 := fun s hs => hrest s hs.le
  have B : ∀ k : ℕ, (∃ n, Below q (r.σ ((k : ℝ) * q)) n) ∧
      pick q x (r.σ ((k : ℝ) * q)) ≤ k - L ∧ k - H ≤ pick q x (r.σ ((k : ℝ) * q)) :=
    fun k => pick_bounds hq hL hH (by have := r.ge ((k : ℝ) * q); linarith)
      (r.le _) (hneg _)
  refine ⟨fun k => pick q x (r.σ ((k : ℝ) * q)), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a b hab
    have hab' : (a : ℝ) * q ≤ (b : ℝ) * q :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hq.le
    exact pick_mono hsep (r.mono _ _ hab') (B b).1 (hneg _)
  · intro k; exact (B k).2.1
  · intro k; exact (B k).2.2
  · intro k
    show y ((k : ℝ) * q) = x ((pick q x (r.σ ((k : ℝ) * q)) : ℝ) * q)
    rw [e, pick_val hsep (B k).1 (hneg _)]

/-- **Sound discretisation WITHOUT separation (cell hull).** Every continuous
`[lo, hi]` behaviour is matched by a discrete warp `f` with bounds `[L, H]`
such that output sample `k` equals the input's value at SOME time in the
grid cell `[f k q, (f k + 1) q]`. So the discrete abstraction is sound for
all signals if a sample stands for the set of values a signal takes in its
cell (`X` when it moves inside the cell): this is the bridge to the ternary
(Kleene) discrete model, in which the arbiter's sub-quantum runt appears as
`X` instead of disappearing. -/
theorem chan_sample_hull {q lo hi : ℝ} {L H : ℕ} (hq : 0 < q)
    (hL : (L : ℝ) * q ≤ lo) (hH : hi ≤ (H : ℝ) * q)
    {x y : ℝ → Bool} (hc : DelayPure.Chan lo hi x y) (hrest : AtRest x) :
    ∃ f : ℕ → ℕ, TraceDiscrete.Warp L H f ∧
      ∀ k : ℕ, ∃ t : ℝ, (f k : ℝ) * q ≤ t ∧ t ≤ ((f k : ℝ) + 1) * q ∧
        sample q y k = x t := by
  obtain ⟨r, e⟩ := hc
  have hlo : 0 ≤ lo := le_trans (mul_nonneg (Nat.cast_nonneg L) hq.le) hL
  have hex : ∀ k : ℕ, ∃ n, Below q (r.σ ((k : ℝ) * q)) n := fun k =>
    ⟨k, by unfold Below; have := r.le ((k : ℝ) * q); linarith⟩
  refine ⟨fun k => cell q (r.σ ((k : ℝ) * q)), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a b hab
    have hab' : (a : ℝ) * q ≤ (b : ℝ) * q :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hq.le
    exact cell_mono (r.mono _ _ hab') (hex b)
  · intro k
    show cell q (r.σ ((k : ℝ) * q)) ≤ k - L
    rcases cell_low (hex k) with h0 | hle
    · omega
    · have := r.le ((k : ℝ) * q)
      have : cell q (r.σ ((k : ℝ) * q)) + L < k + 1 :=
        nat_lt_of_mul hq (by push_cast; linarith)
      omega
  · intro k
    show k - H ≤ cell q (r.σ ((k : ℝ) * q))
    have hr := cell_lt (hex k)
    have := r.ge ((k : ℝ) * q)
    have : k < cell q (r.σ ((k : ℝ) * q)) + 1 + H := nat_lt_of_mul hq (by push_cast; linarith)
    omega
  · intro k
    dsimp only
    have hr := cell_lt (hex k)
    rcases lt_or_ge (r.σ ((k : ℝ) * q)) 0 with hn | hp
    · have h0 : cell q (r.σ ((k : ℝ) * q)) = 0 := by
        rcases cell_low (hex k) with h0 | hle
        · exact h0
        · exfalso
          have : (0 : ℝ) ≤ (cell q (r.σ ((k : ℝ) * q)) : ℝ) * q :=
            mul_nonneg (Nat.cast_nonneg _) hq.le
          linarith
      refine ⟨0, by rw [h0]; simp, by rw [h0]; simp [hq.le], ?_⟩
      show y ((k : ℝ) * q) = x 0
      rw [e, hrest _ hn.le]
    · refine ⟨r.σ ((k : ℝ) * q), ?_, hr.le, e _⟩
      rcases cell_low (hex k) with h0 | hle
      · rw [h0]; simpa using hp
      · exact hle

/-! ## Gates and circuits -/

/-- **Gate (n inputs).** A zero-delay Boolean function `g` of the inputs,
then a `[lo, hi]` channel. Separation is needed JOINTLY on the input tuple
(equivalently: on the excitation; see `tie_counterexample` for why per-input
separation is not enough). -/
theorem gate_sample {n : ℕ} {q lo hi : ℝ} {L H : ℕ} (hq : 0 < q)
    (hL : (L : ℝ) * q ≤ lo) (hH : hi ≤ (H : ℝ) * q)
    (g : (Fin n → Bool) → Bool) {xs : Fin n → ℝ → Bool} {y : ℝ → Bool}
    (hc : DelayPure.Chan lo hi (fun t => g (fun i => xs i t)) y)
    (hsep : Sep q (fun t i => xs i t)) (hrest : AtRest (fun t i => xs i t)) :
    TraceDiscrete.Transport L H (fun k => g (fun i => sample q (xs i) k)) (sample q y) :=
  chan_sample hq hL hH hc (sep_map g hsep) (atRest_map g hrest)

/-- **Gate (2 inputs)**: `y = Chan lo hi (g ∘ (x1, x2))`. -/
theorem gate2_sample {q lo hi : ℝ} {L H : ℕ} (hq : 0 < q)
    (hL : (L : ℝ) * q ≤ lo) (hH : hi ≤ (H : ℝ) * q)
    (g : Bool → Bool → Bool) {x1 x2 y : ℝ → Bool}
    (hc : DelayPure.Chan lo hi (fun t => g (x1 t) (x2 t)) y)
    (hsep : Sep q (fun t => (x1 t, x2 t))) (hrest : AtRest (fun t => (x1 t, x2 t))) :
    TraceDiscrete.Transport L H (fun k => g (sample q x1 k) (sample q x2 k)) (sample q y) :=
  chan_sample hq hL hH hc (sep_map (fun p => g p.1 p.2) hsep)
    (atRest_map (fun p => g p.1 p.2) hrest)

/-- A continuous-time circuit over nets `N`: each driven net `n` (`drv n`)
is the output of a gate computing `f n` from the current net values,
through a `[lo n, hi n]` channel. Undriven nets are primary inputs. -/
structure CCircuit (N : Type*) where
  drv : N → Prop
  f : N → (N → Bool) → Bool
  lo : N → ℝ
  hi : N → ℝ

/-- The same circuit in discrete time, bounds in steps. -/
structure DCircuit (N : Type*) where
  drv : N → Prop
  f : N → (N → Bool) → Bool
  L : N → ℕ
  H : N → ℕ

/-- Excitation of net `n`: the gate function applied to the current values. -/
def CCircuit.exc {N : Type*} (C : CCircuit N) (v : N → ℝ → Bool) (n : N) : ℝ → Bool :=
  fun t => C.f n (fun m => v m t)

/-- A continuous behaviour: the conjunction of the gate relations. -/
def CCircuit.Beh {N : Type*} (C : CCircuit N) (v : N → ℝ → Bool) : Prop :=
  ∀ n, C.drv n → DelayPure.Chan (C.lo n) (C.hi n) (C.exc v n) (v n)

def DCircuit.Beh {N : Type*} (D : DCircuit N) (v : N → ℕ → Bool) : Prop :=
  ∀ n, D.drv n → TraceDiscrete.Transport (D.L n) (D.H n) (fun k => D.f n (fun m => v m k)) (v n)

/-- The discrete circuit with bounds widened to the grid. -/
def CCircuit.widen {N : Type*} (C : CCircuit N) (L H : N → ℕ) : DCircuit N :=
  ⟨C.drv, C.f, L, H⟩

/-- Sample every net. -/
def sampleAll {N : Type*} (q : ℝ) (v : N → ℝ → Bool) : N → ℕ → Bool :=
  fun n => sample q (v n)

/-- Hypotheses of the transfer, per driven net: grid bounds enclose the real
bounds, the excitation is separated and at rest. -/
structure Discretizes {N : Type*} (q : ℝ) (C : CCircuit N) (L H : N → ℕ)
    (v : N → ℝ → Bool) : Prop where
  q_pos : 0 < q
  lo_grid : ∀ n, C.drv n → (L n : ℝ) * q ≤ C.lo n
  hi_grid : ∀ n, C.drv n → C.hi n ≤ (H n : ℝ) * q
  /-- **H-SEP** on every excitation (e.g. from joint separation of each
  gate's fan-in, `sep_map`). -/
  sep : ∀ n, C.drv n → Sep q (C.exc v n)
  /-- **H-REST**: every excitation is constant up to time 0. -/
  rest : ∀ n, C.drv n → AtRest (C.exc v n)

/-- **Discretisation soundness (circuit).** Every continuous behaviour,
sampled, is a behaviour of the widened discrete circuit. -/
theorem circuit_sample {N : Type*} {q : ℝ} {C : CCircuit N} {L H : N → ℕ}
    {v : N → ℝ → Bool} (hb : C.Beh v) (hd : Discretizes q C L H v) :
    (C.widen L H).Beh (sampleAll q v) := by
  intro n hn
  exact chan_sample hd.q_pos (hd.lo_grid n hn) (hd.hi_grid n hn) (hb n hn)
    (hd.sep n hn) (hd.rest n hn)

/-- **Transfer.** A property proved for all discrete behaviours of the
widened circuit holds of the samples of every continuous behaviour. -/
theorem transfer {N : Type*} {q : ℝ} {C : CCircuit N} {L H : N → ℕ}
    (P : (N → ℕ → Bool) → Prop) (hP : ∀ vd, (C.widen L H).Beh vd → P vd)
    {v : N → ℝ → Bool} (hb : C.Beh v) (hd : Discretizes q C L H v) :
    P (sampleAll q v) :=
  hP _ (circuit_sample hb hd)

/-- **Transfer of a safety invariant** at grid points. -/
theorem transfer_invariant {N : Type*} {q : ℝ} {C : CCircuit N} {L H : N → ℕ}
    (Inv : (N → Bool) → Prop) (hP : ∀ vd, (C.widen L H).Beh vd → ∀ k, Inv (fun n => vd n k))
    {v : N → ℝ → Bool} (hb : C.Beh v) (hd : Discretizes q C L H v) :
    ∀ k : ℕ, Inv (fun n => v n ((k : ℝ) * q)) :=
  hP _ (circuit_sample hb hd)

/-! ## Between grid points -/

/-- A `Sep q` signal that equals `v` at the grid points `K1 .. K2` equals
`v` on the whole real interval `[K1 q, K2 q]`. -/
theorem stable_between {α : Type*} {q : ℝ} (hq : 0 < q) {z : ℝ → α} (hsep : Sep q z)
    {v : α} {K1 : ℕ} : ∀ K2 : ℕ, (∀ k : ℕ, K1 ≤ k → k ≤ K2 → z ((k : ℝ) * q) = v) →
    ∀ t : ℝ, (K1 : ℝ) * q ≤ t → t ≤ (K2 : ℝ) * q → z t = v := by
  intro K2
  induction K2 with
  | zero =>
    intro hv t h1 h2
    have hK : K1 = 0 := by
      by_contra hc
      have : (1 : ℝ) ≤ K1 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
      have := mul_le_mul_of_nonneg_right this hq.le
      push_cast at h2; linarith
    subst hK
    push_cast at h1 h2
    have ht : t = ((0 : ℕ) : ℝ) * q := by push_cast; linarith
    rw [ht]; exact hv 0 le_rfl le_rfl
  | succ K ih =>
    intro hv t h1 h2
    by_cases hle : t ≤ (K : ℝ) * q
    · exact ih (fun k hk1 hk2 => hv k hk1 (by omega)) t h1 hle
    · by_cases hK : K1 ≤ K
      · have a := hv K hK (by omega)
        have c := hv (K + 1) (by omega) le_rfl
        push_cast at c h2
        rcases hsep ((K : ℝ) * q) t (((K : ℝ) + 1) * q) (not_le.mp hle).le h2 (by linarith)
          with e | e
        · rw [e, a]
        · rw [e, c]
      · have h3 : ((K + 1 : ℕ) : ℝ) ≤ K1 := by
          have : K + 1 ≤ K1 := by omega
          exact_mod_cast this
        have h4 := mul_le_mul_of_nonneg_right h3 hq.le
        have hK2 : K1 < K + 2 := nat_lt_of_mul hq (by push_cast at h2 ⊢; linarith)
        push_cast at h2 h4
        have ht : t = ((K + 1 : ℕ) : ℝ) * q := by push_cast; linarith
        rw [ht]; exact hv (K + 1) (by omega) le_rfl

/-- Real-interval form: stability on `[a, b]` follows from stability at the
grid points of any grid interval `[K1, K2]` covering it (best:
`K1 = ⌊a/q⌋`, `K2 = ⌈b/q⌉`, i.e. less than one quantum longer at each end). -/
theorem stable_interval {α : Type*} {q a b : ℝ} (hq : 0 < q) {z : ℝ → α} (hsep : Sep q z)
    {v : α} {K1 K2 : ℕ} (ha : (K1 : ℝ) * q ≤ a) (hb : b ≤ (K2 : ℝ) * q)
    (hv : ∀ k : ℕ, K1 ≤ k → k ≤ K2 → z ((k : ℝ) * q) = v) :
    ∀ t, a ≤ t → t ≤ b → z t = v :=
  fun t h1 h2 => stable_between hq hsep K2 hv t (le_trans ha h1) (le_trans h2 hb)

/-- A state invariant over a JOINTLY separated, at-rest tuple of nets that
holds at every grid point holds at every real time `t` (the hypothesis
`∃ T, t ≤ T q` is the Archimedean property, true for every real `t`, stated
because `Archimedean ℝ` is not built in this checkout). -/
theorem invariant_everywhere {α : Type*} {q : ℝ} (hq : 0 < q) {z : ℝ → α}
    (hsep : Sep q z) (hrest : AtRest z) (Inv : α → Prop)
    (hinv : ∀ k : ℕ, Inv (z ((k : ℝ) * q))) (t : ℝ) (ht : ∃ T : ℕ, t ≤ (T : ℝ) * q) :
    Inv (z t) := by
  rcases lt_or_ge t 0 with hneg | hpos
  · rw [hrest t hneg.le]; have := hinv 0; simpa using this
  · obtain ⟨T, hT⟩ := ht
    have hex : ∃ n, Below q t n := ⟨T, by unfold Below; linarith⟩
    have hr := cell_lt hex
    have hl : (cell q t : ℝ) * q ≤ t := by
      rcases cell_low hex with h0 | h
      · rw [h0]; simpa using hpos
      · exact h
    rcases hsep ((cell q t : ℝ) * q) t (((cell q t : ℝ) + 1) * q) hl hr.le (by linarith)
      with e | e
    · rw [e]; exact hinv _
    · rw [e]; have := hinv (cell q t + 1); push_cast at this; exact this

/-! ## Counterexamples: separation cannot be dropped

Quantum `q = 1`. `up` rises at `1/4`, `dn` falls at `1/2`; each is a single
clean edge (separated for every `q`). Their AND, `runt`, is a pulse on
`[1/4, 1/2)`, narrower than one quantum and strictly between grid points 0
and 1, so it is invisible in the samples. A channel with delay `3/4` moves
it onto `[1, 5/4)`, which contains grid point 1. -/

noncomputable def up : ℝ → Bool := fun t => if 1/4 ≤ t then true else false
noncomputable def dn : ℝ → Bool := fun t => if t < 1/2 then true else false
noncomputable def runt : ℝ → Bool := fun t => up t && dn t

theorem up_sep (q : ℝ) : Sep q up :=
  sep_of_monotone fun a b hab ha => by
    simp only [up] at ha ⊢; split_ifs at ha ⊢ with h1 h2 <;> first | rfl | (exfalso; linarith)

theorem dn_sep (q : ℝ) : Sep q dn :=
  sep_of_antitone fun a b hab hb => by
    simp only [dn] at hb ⊢; split_ifs at hb ⊢ with h1 h2 <;> first | rfl | (exfalso; linarith)

theorem pair_atRest : AtRest (fun t => (up t, dn t)) := by
  intro t ht
  simp only [up, dn]
  split_ifs <;> first | rfl | (exfalso; linarith)

theorem runt_sample (k : ℕ) : sample 1 runt k = false := by
  simp only [sample, runt, up, dn, mul_one]
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; norm_num
  · have : (1 : ℝ) ≤ k := by exact_mod_cast h
    split_ifs with h1 h2 <;> first | rfl | (exfalso; linarith)

/-- The delayed runt (fixed delay `3/4`, a behaviour of every `[lo, hi]`
channel with `lo ≤ 3/4 ≤ hi`, by `DelayPure.chan_shift`). -/
noncomputable def runtOut : ℝ → Bool := fun s => runt (s - 3/4)

theorem runtOut_one : sample 1 runtOut 1 = true := by
  simp only [sample, runtOut, runt, up, dn]; norm_num

theorem runt_chan {lo hi : ℝ} (h1 : lo ≤ 3/4) (h2 : 3/4 ≤ hi) :
    DelayPure.Chan lo hi runt runtOut :=
  DelayPure.chan_shift h1 h2 runt

/-- **The sampled runt has no discrete channel explanation, for any bounds.**
The input samples are constantly `false`; the output samples are not. -/
theorem runt_no_transport (L H : ℕ) :
    ¬ TraceDiscrete.Transport L H (sample 1 runt) (sample 1 runtOut) := by
  rintro ⟨f, _, hf⟩
  have := hf 1
  rw [runtOut_one, runt_sample] at this
  exact absurd this (by decide)

/-- **Tie counterexample (the arbiter runt case).** An AND gate whose two
inputs are each a single clean edge, at rest before 0, with the inputs
crossing within one quantum: a continuous `[lo, hi]` behaviour (any band
containing `3/4`) whose samples are NOT a discrete behaviour of the AND gate
with ANY bounds `[L, H]`. -/
theorem tie_counterexample {lo hi : ℝ} (h1 : lo ≤ 3/4) (h2 : 3/4 ≤ hi) :
    Sep 1 up ∧ Sep 1 dn ∧ AtRest (fun t => (up t, dn t)) ∧
    DelayPure.Chan lo hi (fun t => up t && dn t) runtOut ∧
    ∀ L H : ℕ, ¬ TraceDiscrete.Transport L H
      (fun k => sample 1 up k && sample 1 dn k) (sample 1 runtOut) :=
  ⟨up_sep 1, dn_sep 1, pair_atRest, runt_chan h1 h2, runt_no_transport⟩

/-- Consequently the input PAIR is not jointly separated (else
`gate2_sample` would apply): joint separation is necessary. -/
theorem tie_not_sep : ¬ Sep 1 (fun t => (up t, dn t)) := by
  intro hs
  have := gate2_sample (q := 1) (lo := 3/4) (hi := 3/4) (L := 0) (H := 1) one_pos
    (by norm_num) (by norm_num) (fun a b => a && b) (runt_chan le_rfl le_rfl) hs pair_atRest
  exact runt_no_transport 0 1 this

/-- **Mutual exclusion can hold at every grid point and fail between.** With
`g1 = dn` (falls at 1/2) and `g2 = up` (rises at 1/4), each separated alone,
`¬(g1 ∧ g2)` holds at every sample yet both are high at `t = 3/8`. A
`transfer_invariant` result alone therefore does NOT give real-time mutual
exclusion; `invariant_everywhere` needs joint separation. -/
theorem mutex_between :
    (∀ k : ℕ, ¬ (sample 1 dn k = true ∧ sample 1 up k = true)) ∧
    dn (3/8) = true ∧ up (3/8) = true := by
  refine ⟨fun k ⟨h1, h2⟩ => ?_, ?_, ?_⟩
  · have := runt_sample k
    simp only [sample, runt] at this h1 h2
    rw [h1, h2] at this; exact absurd this (by decide)
  · simp only [dn]; norm_num
  · simp only [up]; norm_num

/-- **The lower bound must be rounded DOWN** (`L = ⌊lo/q⌋`, not `⌈lo/q⌉`):
a clean step at `2/5` through a fixed delay `3/2` (`q = 1`) appears in the
samples with a delay of one step, so no discrete channel with `L = 2` admits
it, although the edge itself is perfectly separated. -/
noncomputable def step25 : ℝ → Bool := fun t => if 2/5 ≤ t then true else false

theorem lo_round_down_needed (H : ℕ) :
    DelayPure.Chan (3/2) (3/2) step25 (fun s => step25 (s - 3/2)) ∧ Sep 1 step25 ∧
      AtRest step25 ∧
      ¬ TraceDiscrete.Transport 2 H (sample 1 step25) (sample 1 (fun s => step25 (s - 3/2))) := by
  refine ⟨DelayPure.chan_shift le_rfl le_rfl _, sep_of_monotone fun a b hab ha => ?_, ?_, ?_⟩
  · simp only [step25] at ha ⊢; split_ifs at ha ⊢ <;> first | rfl | (exfalso; linarith)
  · intro t ht; simp only [step25]; split_ifs <;> first | rfl | (exfalso; linarith)
  · rintro ⟨f, F, hf⟩
    have h := hf 2
    have hf2 : f 2 = 0 := by have := F.le_late 2; omega
    rw [hf2] at h
    simp only [sample, step25] at h
    norm_num at h

/-! ## Bridges to shard B's and shard C's discrete channels -/

/-- The warp channel (FIFO) refines shard C's `BoundedDelay` (cause + settle). -/
theorem transport_boundedDelay {L H : ℕ} {i o : ℕ → Bool}
    (h : TraceDiscrete.Transport L H i o) : Formal.Net.BoundedDelay L H i o := by
  obtain ⟨f, F, hf⟩ := h
  constructor
  · intro t ht
    have a1 := F.le_late (t + 1); have a2 := F.early_le (t + 1); have a3 := F.le_late t
    refine ⟨t + 1 - f (t + 1), ?_, by omega, by omega, ?_⟩
    · by_contra hc
      apply ht
      rw [hf, hf]
      have e1 : f t = 0 := by omega
      have e2 : f (t + 1) = 0 := by omega
      rw [e1, e2]
    · rw [hf]; congr 1; omega
  · intro t _ hs
    have a1 := F.le_late t; have a2 := F.early_le t
    rw [hf, hs (f t) (by omega) (by omega), hs t (by omega) le_rfl]

/-- Continuous channel to shard C's `BoundedDelay` on the samples. -/
theorem chan_sample_bd {q lo hi : ℝ} {L H : ℕ} (hq : 0 < q)
    (hL : (L : ℝ) * q ≤ lo) (hH : hi ≤ (H : ℝ) * q)
    {x y : ℝ → Bool} (hc : DelayPure.Chan lo hi x y) (hsep : Sep q x) (hrest : AtRest x) :
    Formal.Net.BoundedDelay L H (sample q x) (sample q y) :=
  transport_boundedDelay (chan_sample hq hL hH hc hsep hrest)

/-- Continuous channel to shard B's window channel `WinDelay` on the samples.
No rest hypothesis: `WinDelay` constrains only steps `≥ H`, whose read times
are `≥ 0`. -/
theorem chan_sample_win {q lo hi : ℝ} {L H : ℕ} (hq : 0 < q)
    (hL : (L : ℝ) * q ≤ lo) (hH : hi ≤ (H : ℝ) * q) (hLH : L ≤ H)
    {x y : ℝ → Bool} (hc : DelayPure.Chan lo hi x y) (hsep : Sep q x) :
    Formal.Cells.CElemTiming.WinDelay L H (sample q x) (sample q y) := by
  obtain ⟨r, e⟩ := hc
  intro t ht
  have hge := r.ge ((t : ℝ) * q)
  have hpos : 0 ≤ r.σ ((t : ℝ) * q) := by
    have h3 : (H : ℝ) ≤ t := by exact_mod_cast ht
    have := mul_le_mul_of_nonneg_right h3 hq.le
    linarith
  have hneg : r.σ ((t : ℝ) * q) < 0 → x (r.σ ((t : ℝ) * q)) = x 0 :=
    fun h => absurd h (not_lt.mpr hpos)
  obtain ⟨hex, b1, b2⟩ := pick_bounds (x := x) (k := t) hq hL hH (by linarith) (r.le _) hneg
  refine ⟨pick q x (r.σ ((t : ℝ) * q)), by omega, by omega, ?_⟩
  show y ((t : ℝ) * q) = x ((pick q x (r.σ ((t : ℝ) * q)) : ℝ) * q)
  rw [e, pick_val hsep hex hneg]

/-- **Shard B's feedback-LUT cell in continuous time.** A continuous
behaviour of the loop (LUT excitation through a `[dlo, dhi]` channel to `O`,
feedback wire `[wlo, whi]` from `O` to `qp`), with the excitation and `O`
separated by one quantum, sampled, is a `Formal.Cells.CElemTiming.Loop` with the widened
bounds. So `c2_follow_hold`, `c2_reset`, `c2_four_phase` hold at all grid
points of every such continuous behaviour. -/
theorem loop_of_continuous {init : ℕ} {a b rst O qp : ℝ → Bool} {q dlo dhi wlo whi : ℝ}
    {Ll Hl Lw Hw : ℕ} (hq : 0 < q)
    (hLl : (Ll : ℝ) * q ≤ dlo) (hHl : dhi ≤ (Hl : ℝ) * q) (hl : Ll ≤ Hl)
    (hLw : (Lw : ℝ) * q ≤ wlo) (hHw : whi ≤ (Hw : ℝ) * q) (hw : Lw ≤ Hw)
    (hpos : 0 < Ll + Lw)
    (hlut : DelayPure.Chan dlo dhi (fun t => Formal.Cells.CElemTiming.exc init (a t) (b t) (qp t) (rst t)) O)
    (hfb : DelayPure.Chan wlo whi O qp)
    (hsepE : Sep q (fun t => Formal.Cells.CElemTiming.exc init (a t) (b t) (qp t) (rst t)))
    (hsepO : Sep q O) :
    Formal.Cells.CElemTiming.Loop init (sample q a) (sample q b) (sample q rst) (sample q O) (sample q qp)
      Ll Hl Lw Hw :=
  ⟨chan_sample_win hq hLl hHl hl hlut hsepE, chan_sample_win hq hLw hHw hw hfb hsepO, hpos⟩

end Formal.Core.Discretize
