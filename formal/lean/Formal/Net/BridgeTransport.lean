import Formal.Net.Bridge

/-!
# Probe 8d: the bridge fails for bounded transport delay (`Prelim.BoundedDelay`)

A 4-gate network, persistent in the SI sense (at most one gate is ever
excited), and a trace in which EVERY gate satisfies `BoundedDelay 1 4`
(H_BOUNDED_DELAY of `Formal/Net/Prelim.lean`), but the trace reaches a state
that no SI run reaches. So SI reasoning is unsound for that channel, and the
bridge of `Bridge.lean` really needs the inertial property.

    g0 = 1                      (a source; starts at 0, so it fires once)
    g1 = g0                     (buffer)
    g2 = g1 ∨ g2                (set by g1, then holds: an SR latch)
    g3 = g3 ∨ (g2 ∧ ¬g1)        (set iff g1 FALLS after g2 was set)

SI: g0, g1, g2 rise once each, in that order; `g3 = 0` forever
(`cx_reach_g3`). Timed (`cxTrace`): g1 rises at 2 (copying g0 at 1, delay 1),
FALLS at 4 by copying the stale `g0 = 0` of time 0 (delay 4, inside
`[1, 4]`), and rises again at 5. That runt is legal for `BoundedDelay` (a
per-change transport delay may deliver an old edge after a newer one), it has
no input pulse behind it, and g2 (already set) and g3 (set by the runt) see
it. On the fabric this is the "older edge overtakes a newer one" case: it
needs the two edges of one net to take paths differing by more than their
separation. `Inertial` forbids it (`inertial_bounded` shows `Inertial` is a
special case of `BoundedDelay`).
-/

namespace Formal.Net.Bridge.Transport
open Formal.Net Formal.Net.Bridge

def cxNet : Net where
  n := 4
  f i s := match i with
    | 0 => true
    | 1 => s 0
    | 2 => s 1 || s 2
    | 3 => s 3 || (s 2 && !s 1)
    | _ => s i

def s0 : State := fun _ => false

/-- SI invariant of `cxNet`. -/
def P (s : State) : Prop :=
  s 3 = false ∧ (s 2 = true → s 1 = true) ∧ (s 1 = true → s 0 = true)

theorem P_step {s : State} (hs : P s) {i : Nat} (he : excited cxNet s i) : P (fire s i) := by
  obtain ⟨hi, hne⟩ := he
  obtain ⟨h3, h21, h10⟩ := hs
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp [cxNet] at hi; omega
  rcases this with rfl | rfl | rfl | rfl <;> simp [cxNet] at hne <;>
    simp only [P, fire] <;> simp <;>
    revert h3 h21 h10 hne <;> cases s 0 <;> cases s 1 <;> cases s 2 <;> cases s 3 <;> simp

theorem cx_reach_P {s : State} (h : Reach cxNet s0 s) : P s := by
  induction h with
  | refl => simp [P, s0]
  | step i _ he ih => exact P_step ih he

/-- The SI invariant: g3 never rises. -/
theorem cx_reach_g3 {s : State} (h : Reach cxNet s0 s) : s 3 = false := (cx_reach_P h).1

/-- At most one gate is excited in any reachable state, so `cxNet` is persistent. -/
theorem cx_unique {s : State} (hs : P s) {i j : Nat} (hi : excited cxNet s i)
    (hj : excited cxNet s j) : i = j := by
  obtain ⟨hil, hie⟩ := hi
  obtain ⟨hjl, hje⟩ := hj
  obtain ⟨h3, h21, h10⟩ := hs
  have ci : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp [cxNet] at hil; omega
  have cj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp [cxNet] at hjl; omega
  rcases ci with rfl | rfl | rfl | rfl <;> rcases cj with rfl | rfl | rfl | rfl <;>
    simp [cxNet] at hie hje <;>
    revert h3 h21 h10 hie hje <;> cases s 0 <;> cases s 1 <;> cases s 2 <;> cases s 3 <;> simp

theorem cx_persistent : Persistent cxNet s0 :=
  fun _ hr _ _ hi hj hij => absurd (cx_unique (cx_reach_P hr) hi hj) hij

/-- The timed trace (node values at each tick). -/
def cxTrace (t : Nat) : State := fun j => match j with
  | 0 => decide (1 ≤ t)
  | 1 => decide (t = 2 ∨ t = 3 ∨ 5 ≤ t)
  | 2 => decide (3 ≤ t)
  | 3 => decide (5 ≤ t)
  | _ => false

theorem cx_late {t : Nat} (ht : 5 ≤ t) (j : Nat) : cxTrace t j = decide (j < 4) := by
  unfold cxTrace
  match j with
  | 0 => simp; omega
  | 1 => simp; omega
  | 2 => simp; omega
  | 3 => simp; omega
  | _ + 4 => simp

theorem cx_frame (t j : Nat) (hj : cxNet.n ≤ j) : cxTrace (t + 1) j = cxTrace t j := by
  simp [cxNet] at hj
  unfold cxTrace
  match j, hj with
  | _ + 4, _ => rfl

/-- Decidable form of `BoundedDelay`'s `cause` on a finite prefix. -/
theorem cause_of_prefix {lo hi : Nat} {e o : Trace} (T : Nat)
    (hpre : ∀ t, t < T → o t ≠ o (t + 1) →
      ∃ d, d < hi + 1 ∧ (lo ≤ d ∧ d ≤ t + 1 ∧ o (t + 1) = e (t + 1 - d)))
    (hlate : ∀ t, T ≤ t → o (t + 1) = o t) :
    ∀ t, changes o t → ∃ d, lo ≤ d ∧ d ≤ hi ∧ d ≤ t + 1 ∧ o (t + 1) = e (t + 1 - d) := by
  intro t hc
  by_cases ht : t < T
  · obtain ⟨d, h1, h2, h3, h4⟩ := hpre t ht hc
    exact ⟨d, h2, by omega, h3, h4⟩
  · exact absurd (hlate t (by omega)).symm hc

theorem cx_cause : ∀ i, i < 4 → ∀ t, t < 5 → cxTrace t i ≠ cxTrace (t + 1) i →
    ∃ d, d < 4 + 1 ∧ (1 ≤ d ∧ d ≤ t + 1 ∧ cxTrace (t + 1) i = cxNet.f i (cxTrace (t + 1 - d))) := by
  decide

/-- **Every gate of `cxNet` satisfies H_BOUNDED_DELAY with `[1, 4]`.** -/
theorem cx_bounded (i : Nat) (hi : i < cxNet.n) :
    BoundedDelay 1 4 (fun t => cxNet.f i (cxTrace t)) (fun t => cxTrace t i) := by
  have late : ∀ t, 5 ≤ t → ∀ j, cxTrace (t + 1) j = cxTrace t j := by
    intro t ht j; rw [cx_late ht, cx_late (by omega)]
  refine ⟨cause_of_prefix (e := fun t => cxNet.f i (cxTrace t)) (o := fun t => cxTrace t i) 5
    (cx_cause i hi) (fun t ht => late t ht i), ?_⟩
  have ci : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp [cxNet] at hi; omega
  rcases ci with rfl | rfl | rfl | rfl
  all_goals
    intro t ht hs
    by_cases h4 : t = 4
    · subst h4
      have := hs 4 (by omega) (by omega)
      revert this; simp [cxNet, cxTrace]
    · have h5 : 5 ≤ t := by omega
      simp only [cxNet, cx_late h5]
      decide

theorem cx_trace0 : cxTrace 0 = s0 := by
  funext j; unfold cxTrace s0
  match j with
  | 0 | 1 | 2 | 3 => rfl
  | _ + 4 => rfl

/-- **The bridge is false for bounded transport delay.** A persistent network
and a trace in which every gate satisfies `BoundedDelay 1 4`, starting at the
SI initial state, that reaches a state no SI run reaches (g3 = 1 at t = 5). -/
theorem transport_breaks_si :
    Persistent cxNet s0 ∧ cxTrace 0 = s0 ∧
    (∀ i, i < cxNet.n → BoundedDelay 1 4 (fun t => cxNet.f i (cxTrace t)) (fun t => cxTrace t i)) ∧
    (∀ t j, cxNet.n ≤ j → cxTrace (t + 1) j = cxTrace t j) ∧
    ¬ Reach cxNet s0 (cxTrace 5) := by
  refine ⟨cx_persistent, cx_trace0, cx_bounded, cx_frame, fun h => ?_⟩
  have := cx_reach_g3 h
  revert this; decide

/-- Under the inertial channel (any bounds) the same network can never do
this: g3 stays 0 on every timed trace (the bridge, `timed_invariant`). -/
theorem cx_inertial_safe {lo hi : Nat → Nat} {x : Nat → State} (hx : Timed cxNet lo hi x)
    (h0 : x 0 = s0) (t : Nat) : x t 3 = false :=
  timed_invariant cx_persistent hx h0 (fun _ h => cx_reach_g3 h) t

end Formal.Net.Bridge.Transport
