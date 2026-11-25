import Formal.Net.RingTimed

/-!
# Probe C-9d (b): bounded PURE (transport, FIFO) delay also gives SI runs

8d proved the bridge "timed trace ⇒ SI run" for inertial and no-overtaking channels and
showed (`BridgeTransport`) that a per-edge transport relation (`Prelim.BoundedDelay`) breaks
it. It left open the physical transport channel: bounded pure delay that never reorders
edges (8d open goal 2). Shard A's `Formal/Core/Delay/Pure.lean` models exactly that channel
in real time (`DelayPure.Chan lo hi`: a nondecreasing read-time map `σ` with
`s - hi ≤ σ s ≤ s - lo`, output `y s = x (σ s)`; pulses can collapse, edges never cross).

`PureFifo lo hi e o` below is the same channel in discrete time (`Nat` ticks; Core imports
Mathlib, shard C's closure does not, so this is a transcription, not an import). The output
before the first delivered input shows its own initial value (`pre`).

* `pure_noOvertake`: in a PERSISTENT network, a trace in which every gate is a `PureFifo`
  channel (per-gate bounds, `lo ≥ 1`) is a `TimedF` trace (no-overtaking channels), so it is
  an SI run (`Bridge.timed_runF`) and every 8d / 9a / 9d result stated for `TimedF` holds.
  Proof: per gate, the number of output edges up to `t` is at most the number of input edges
  up to the read time (`nchg_read`); persistence keeps "input edges minus output edges" in
  `{0, 1}` and equal to the excitation (`alt`); together, an output change at `t` finds the
  gate excited at `t`, which is the no-overtaking condition with `t' = t`.
* `ring_pure_*`: for the `bd_c2n` ring this gives `timed_ring_safe`, `timed_ring_live` and the
  timed balance law on pure-delay traces.
* `unit_pure`: non-vacuity (the unit-delay trace is a `PureFifo` trace with `lo = hi = 1`).
-/

namespace Formal.Net.RingTimedPure
open Formal.Net Formal.Net.Bridge

/-- The input as the channel reads it: index 0 = before any input (the output's own initial
value), index `k+1` = input at time `k`. -/
def pre (v : Bool) (e : Trace) : Nat → Bool
  | 0 => v
  | k + 1 => e k

/-- Bounded pure FIFO delay, discrete time: the output at `t` shows the input read at index
`σ t` (`pre`), `σ` nondecreasing, the age of what is shown is in `[lo, hi]`. -/
structure PureFifo (lo hi : Nat) (e o : Trace) : Prop where
  lo_pos : 1 ≤ lo
  read : ∃ σ : Nat → Nat, (∀ a b, a ≤ b → σ a ≤ σ b) ∧ (∀ t, σ t + lo ≤ t + 1) ∧
    (∀ t, hi ≤ t → t + 1 ≤ σ t + hi) ∧ ∀ t, o t = pre (o 0) e (σ t)

/-- A timed trace whose gates are bounded pure FIFO delays (per-gate bounds). -/
structure TimedP (N : Net) (lo hi : Nat → Nat) (x : Nat → State) : Prop where
  gate  : ∀ i, i < N.n → PureFifo (lo i) (hi i) (fun t => N.f i (x t)) (fun t => x t i)
  frame : ∀ t j, N.n ≤ j → x (t + 1) j = x t j

/-! ## Edge counting -/

/-- Number of changes of `f` between indices `0 … m`. -/
def nchg (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => nchg f m + (if f m = f (m + 1) then 0 else 1)

theorem nchg_mono (f : Nat → Bool) {a b : Nat} (h : a ≤ b) : nchg f a ≤ nchg f b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ b ih =>
    by_cases e : a = b + 1
    · subst e; exact Nat.le_refl _
    · have := ih (by omega); simp only [nchg]; omega

theorem nchg_ne (f : Nat → Bool) {a b : Nat} (h : a ≤ b) (hne : f a ≠ f b) :
    nchg f a + 1 ≤ nchg f b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact absurd rfl hne
  | succ b ih =>
    by_cases e : a = b + 1
    · subst e; exact absurd rfl hne
    · simp only [nchg]
      by_cases hb : f a = f b
      · have : f b ≠ f (b + 1) := by rw [← hb]; exact hne
        simp only [this, ite_false]
        have := nchg_mono f (show a ≤ b by omega); omega
      · have := ih (by omega) hb; split <;> omega

/-- Through a FIFO read map, the output has at most as many edges as the input it read. -/
theorem nchg_read {σ : Nat → Nat} (hm : ∀ a b, a ≤ b → σ a ≤ σ b) (h0 : σ 0 = 0)
    {o E : Nat → Bool} (ho : ∀ t, o t = E (σ t)) : ∀ u, nchg o u ≤ nchg E (σ u) := by
  intro u
  induction u with
  | zero => rw [h0]; exact Nat.le_refl _
  | succ u ih =>
    simp only [nchg]
    by_cases e : o u = o (u + 1)
    · simp only [e, ite_true]
      have := nchg_mono E (hm u (u + 1) (by omega)); omega
    · simp only [e, ite_false]
      rw [ho u, ho (u + 1)] at e
      have := nchg_ne E (hm u (u + 1) (by omega)) e; omega

/-! ## The bridge -/

variable {N : Net} {lo hi : Nat → Nat} {x : Nat → State}

/-- Excitation of gate `i` at `u`, as a number. -/
def X (N : Net) (x : Nat → State) (i u : Nat) : Nat := if N.f i (x u) = x u i then 0 else 1

/-- The alternation invariant: input edges (with the initial "edge" from the output's own
value to the input's) minus output edges equals the excitation. -/
def Alt (N : Net) (x : Nat → State) (i u : Nat) : Prop :=
  nchg (pre (x 0 i) (fun t => N.f i (x t))) (u + 1) = nchg (fun t => x t i) u + X N x i u

theorem alt_zero (x : Nat → State) (i : Nat) : Alt N x i 0 := by
  unfold Alt X nchg nchg
  simp only [pre]
  by_cases h : x 0 i = N.f i (x 0)
  · simp [h]
  · have h' : ¬ N.f i (x 0) = x 0 i := fun e => h e.symm
    simp [h, h']

theorem pre_succ (v : Bool) (e : Trace) (u : Nat) : pre v e (u + 1) = e u := rfl

/-- One step of the alternation invariant. Uses only: if gate `i` changes at `u` it was
excited at `u`; if it does not change and was excited, it stays excited. -/
theorem alt_step {i u : Nat} (ha : Alt N x i u)
    (hfire : x (u + 1) i ≠ x u i → N.f i (x u) ≠ x u i)
    (hkeep : x (u + 1) i = x u i → N.f i (x u) ≠ x u i → N.f i (x (u + 1)) ≠ x (u + 1) i) :
    Alt N x i (u + 1) := by
  unfold Alt at *
  have e1 : nchg (pre (x 0 i) (fun t => N.f i (x t))) (u + 1 + 1) =
      nchg (pre (x 0 i) (fun t => N.f i (x t))) (u + 1) +
        (if N.f i (x u) = N.f i (x (u + 1)) then 0 else 1) := rfl
  have e2 : nchg (fun t => x t i) (u + 1) = nchg (fun t => x t i) u +
      (if x u i = x (u + 1) i then 0 else 1) := rfl
  rw [e1, e2, ha]
  unfold X
  by_cases hc : x (u + 1) i = x u i
  · by_cases hx : N.f i (x u) = x u i
    · rw [hc]; simp only [hx, ite_true]
      by_cases hy : N.f i (x (u + 1)) = x u i
      · simp [hy]
      · have : ¬ x u i = N.f i (x (u + 1)) := fun h => hy h.symm
        simp [hy, this]
    · have k := hkeep hc hx
      rw [hc] at k ⊢
      have : N.f i (x u) = N.f i (x (u + 1)) := by
        revert hx k; cases N.f i (x u) <;> cases N.f i (x (u + 1)) <;> cases x u i <;> simp
      simp [k, this]
  · have hx := hfire hc
    have hc' : ¬ x u i = x (u + 1) i := fun h => hc h.symm
    simp only [hx, hc', ite_false]
    by_cases hy : N.f i (x u) = N.f i (x (u + 1))
    · have : N.f i (x (u + 1)) = x (u + 1) i := by
        rw [← hy]; revert hx hc; cases N.f i (x u) <;> cases x u i <;> cases x (u + 1) i <;> simp
      simp [hy, this]
    · have : ¬ N.f i (x (u + 1)) = x (u + 1) i := by
        revert hx hc hy; cases N.f i (x u) <;> cases N.f i (x (u + 1)) <;> cases x u i <;>
          cases x (u + 1) i <;> simp
      simp [hy, this]

/-- At a change of a pure-delay gate, the alternation invariant forces excitation. -/
theorem fire_of_alt {i t : Nat} (hin : i < N.n) (hx : TimedP N lo hi x) (ha : Alt N x i t)
    (hc : x (t + 1) i ≠ x t i) : N.f i (x t) ≠ x t i := by
  obtain ⟨σ, hm, hlo, _, ho⟩ := (hx.gate i hin).read
  have hl := (hx.gate i hin).lo_pos
  have h0 : σ 0 = 0 := by have := hlo 0; omega
  have cnt := nchg_read hm h0 ho (t + 1)
  have mono := nchg_mono (pre (x 0 i) (fun t => N.f i (x t))) (show σ (t + 1) ≤ t + 1 by
    have := hlo (t + 1); omega)
  have e2 : nchg (fun t => x t i) (t + 1) = nchg (fun t => x t i) t + 1 := by
    show nchg (fun t => x t i) t + (if x t i = x (t + 1) i then 0 else 1) = _
    have : ¬ x t i = x (t + 1) i := fun h => hc h.symm
    simp [this]
  unfold Alt at ha
  unfold X at ha
  intro he
  simp only [he, ite_true] at ha
  omega

/-- **Bounded pure FIFO delay ⇒ no overtaking**, in a persistent network (strong induction in
time, like 8d's `goodF`). -/
theorem goodP {s0 : State} (hp : Persistent N s0) (hx : TimedP N lo hi x) (h0 : x 0 = s0) :
    ∀ t, (∀ u, u ≤ t → Reach N s0 (x u)) ∧
      (∀ u, u < t → ∀ i, i ∈ chg N x u → excited N (x u) i) ∧
      (∀ i, i < N.n → Alt N x i t) := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun u hu => ?_, fun u hu => absurd hu (Nat.not_lt_zero _), fun i _ => alt_zero x i⟩
    have : u = 0 := by omega
    rw [this, h0]; exact .refl
  | succ t ih =>
    obtain ⟨hR, hE, hA⟩ := ih
    have hEt : ∀ i, i ∈ chg N x t → excited N (x t) i := by
      intro i hm
      obtain ⟨hi, hc⟩ := mem_chg.1 hm
      exact ⟨hi, fire_of_alt hi hx (hA i hi) (fun h => hc h.symm)⟩
    have hrun := run_of_excited hp (hR t (Nat.le_refl _)) (chg_nodup x t) hEt
    have hfin := final_chg_frame hx.frame t
    have hR1 : Reach N s0 (x (t + 1)) := by
      rw [← hfin]; exact run_reach (hR t (Nat.le_refl _)) hrun
    refine ⟨fun u hu => ?_, fun u hu => ?_, fun i hi => ?_⟩
    · by_cases e : u = t + 1
      · rw [e]; exact hR1
      · exact hR u (by omega)
    · by_cases e : u = t
      · subst e; exact hEt
      · exact hE u (by omega)
    · apply alt_step (hA i hi)
      · intro hc; exact fire_of_alt hi hx (hA i hi) hc
      · intro hc hx'
        have hni : i ∉ chg N x t := fun h => (mem_chg.1 h).2 hc.symm
        have := persist_run hp (hR t (Nat.le_refl _)) ⟨hi, hx'⟩ hrun hni
        rw [hfin] at this; exact this.2

/-- **The bridge for bounded pure delay**: a persistent network's `TimedP` trace is a
`TimedF` trace (hence an SI run, `Bridge.timed_runF`). -/
theorem pure_noOvertake {s0 : State} (hp : Persistent N s0) (hx : TimedP N lo hi x)
    (h0 : x 0 = s0) : TimedF N hi x where
  frame := hx.frame
  gate i hi' := {
    fifo := fun t hc => by
      have he := (goodP hp hx h0 (t + 1)).2.1 t (Nat.lt_succ_self _) i
        (mem_chg.2 ⟨hi', hc⟩)
      refine ⟨t, Nat.le_refl _, ?_, fun u h1 h2 => by rw [show u = t by omega]⟩
      have h1 : N.f i (x t) ≠ x t i := he.2
      have h2 : x t i ≠ x (t + 1) i := hc
      show N.f i (x t) = x (t + 1) i
      revert h1 h2
      cases N.f i (x t) <;> cases x t i <;> cases x (t + 1) i <;> simp
    settle := fun t ht hs => by
      obtain ⟨σ, _, hlo, hhi, ho⟩ := (hx.gate i hi').read
      have h1 := hlo t
      have h2 := hhi t ht
      have hpos : 1 ≤ σ t := by have := hhi t ht; have := (hx.gate i hi').lo_pos; omega
      show x t i = N.f i (x t)
      rw [ho t]
      obtain ⟨k, hk⟩ : ∃ k, σ t = k + 1 := ⟨σ t - 1, by omega⟩
      rw [hk, pre_succ]
      have a := hs k (by omega) (by omega)
      have b := hs t (by omega) (Nat.le_refl _)
      exact a.trans b.symm }

/-- Non-vacuity: the unit-delay trace is a pure FIFO trace with `lo = hi = 1` (`σ t = t`). -/
theorem unit_pure (N : Net) (s0 : State) :
    TimedP N (fun _ => 1) (fun _ => 1) (unitTrace N s0) where
  gate i hi := {
    lo_pos := Nat.le_refl _
    read := ⟨fun t => t, fun _ _ h => h, fun _ => Nat.le_refl _, fun _ _ => Nat.le_refl _,
      fun t => by
        cases t with
        | zero => rfl
        | succ t => show stepAll N (unitTrace N s0 t) i = _; simp [stepAll, hi, pre]⟩ }
  frame t j hj := by
    show stepAll N (unitTrace N s0 t) j = _
    have : ¬ j < N.n := by omega
    simp [stepAll, this]

/-! ## The ring on pure-delay traces -/

open Formal.Net.Bridge.RingT in
/-- **Ring, pure delay, safety and liveness**: on every bounded pure FIFO delay trace of the
`bd_c2n` ring from a clean reset (`N ≥ 3`, `0 < K < N`), one token at every tick, and some
stage toggles within its upper bound after every instant. -/
theorem ring_pure_safe_live {n K : Nat} (hn : 3 ≤ n) (hK0 : 0 < K) (hKn : K < n)
    {lo hi : Nat → Nat} {x : Nat → State} (hx : TimedP (ringNet n K) lo hi x)
    (h0 : x 0 = Ring.resetState K) :
    (∀ t, Ring.D n (x t) = 2) ∧ RingTimed.LiveAfter n hi x := by
  have hF := pure_noOvertake (ring_persistent n K _) hx h0
  exact ⟨timed_ring_safe hn hK0 hKn hF h0, timed_ring_live hn hK0 hKn hF h0⟩

open Formal.Net.Bridge.RingT in
/-- **Ring, pure delay, `N ≤ 2` dead**: from any state, no stage ever changes. -/
theorem ring_pure_dead {n K : Nat} (hn : n ≤ 2) {lo hi : Nat → Nat} {x : Nat → State}
    (hx : TimedP (ringNet n K) lo hi x) (t : Nat) : x t = x 0 := by
  have hF := pure_noOvertake (ring_persistent n K _) hx rfl
  induction t with
  | zero => rfl
  | succ t ih =>
    funext j
    by_cases hj : j < n
    · have : x (t + 1) j = x t j := by
        apply Classical.byContradiction; intro hc
        have he := (goodP (ring_persistent n K _) hx rfl (t + 1)).2.1 t (Nat.lt_succ_self _) j
          (mem_chg.2 ⟨hj, fun h => hc h.symm⟩)
        exact Ring.dead_of_le_two hn _ j (excited_ring.1 he)
      rw [this, ih]
    · rw [hx.frame t j (by show n ≤ j; omega), ih]

end Formal.Net.RingTimedPure
