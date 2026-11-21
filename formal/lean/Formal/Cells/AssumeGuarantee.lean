/-!
# Probe Bnet (shard B): a circular assume-guarantee rule, sound under strict causality

Bfb/Bfb2 (`LutFbBridge`, `LutFbBridge2`, `LutFbBridge2Env`) leave a circle: each cell's
behaviour (its guarantee) follows from its own environment assumption (`link_lutFb`,
`link_guar`), and that assumption follows from its NEIGHBOURS' guarantees
(`link_link_env`, `fork_env`). Read naively ("each cell is correct if its neighbours are")
the circle proves nothing. This file states the rule that breaks it, and shows exactly
which side condition makes it sound.

## Assumed / proved / NOT covered

**Proved (generic, no circuit content):**
* `ag_time`: events `e : Ev`, each with a time `time e : Nat`. If every event's assumption
  `A e` follows from the guarantees of all events STRICTLY EARLIER in time (H_ENV, the
  causality side condition), and every event's guarantee follows from its own assumption
  (H_CELL), then every guarantee holds. `ag_wf`: the same for any well-founded "depends
  on" relation.
* `ag_step`: the stratified form (McMillan / Abadi-Lamport style), cells `ι`, levels
  `n : Nat` ("up to time n"): `G i 0`; the assumption up to `n` follows from all cells'
  guarantees up to `n`; the guarantee up to `n + 1` follows from the assumption up to `n`.
  Strictness is the `+ 1`.
* **The side condition is needed** (`nonstrict_unsound`): with the non-strict cell rule
  (assumption up to `n` gives the guarantee up to `n`) the rule proves `False`-guarantees.
  `zero_delay_cex` is the circuit form: two zero-delay buffers in a loop, `x = y`,
  `y = x`, on the trace `x = y = true`. Each buffer meets its contract
  ("if my input was 0 before n, my output was 0 before n"), the non-strict rule's
  premises all hold, and its conclusion (`x` is 0) is false. `unit_delay_ok`: the same
  loop with a one-tick delay meets the strict rule, which proves `x = y = 0`.

**NOT covered here:** any circuit; the instances are in `AssumeGuaranteeLinks` (chains of
links; rings), `AssumeGuaranteeFork` (any network of segment contracts, `net_closed`;
link + 2-way fork) and `AssumeGuaranteeCap` (C's `CapstoneNet`).

Core Lean only, no imports.
-/

namespace Formal.Cells.AssumeGuarantee

/-! ## 1. The rule -/

/-- **The assume-guarantee rule, time-measured.** `time e` is the time of event `e` (in
the instances: the end of the `k`-th segment of a cell's node). H_ENV is the causality side
condition: an event's environment assumption needs only the guarantees of events at
STRICTLY smaller times. -/
theorem ag_time {Ev : Type} (time : Ev → Nat) (G A : Ev → Prop)
    (H_CELL : ∀ e, A e → G e)
    (H_ENV : ∀ e, (∀ e', time e' < time e → G e') → A e) : ∀ e, G e := by
  have key : ∀ n e, time e < n → G e := by
    intro n
    induction n with
    | zero => intro e h; omega
    | succ n ih =>
      intro e h
      exact H_CELL e (H_ENV e (fun e' h' => ih e' (by omega)))
  exact fun e => key (time e + 1) e (Nat.lt_succ_self _)

/-- **The rule for any well-founded dependency relation** `dep e' e` ("`e` depends on
`e'`"). -/
theorem ag_wf {Ev : Type} (dep : Ev → Ev → Prop) (hwf : WellFounded dep) (G A : Ev → Prop)
    (H_CELL : ∀ e, A e → G e)
    (H_ENV : ∀ e, (∀ e', dep e' e → G e') → A e) : ∀ e, G e := by
  intro e
  induction e using hwf.induction with
  | _ e ih => exact H_CELL e (H_ENV e ih)

/-- **The stratified rule** (levels `n` = "up to time `n`"). The `+ 1` in H_CELL is strict
causality: a cell whose assumption holds up to `n` guarantees one tick more. -/
theorem ag_step {ι : Type} (G A : ι → Nat → Prop)
    (H_BASE : ∀ i, G i 0)
    (H_ENV : ∀ i n, (∀ i', G i' n) → A i n)
    (H_CELL : ∀ i n, A i n → G i (n + 1)) : ∀ i n, G i n := by
  intro i n
  induction n generalizing i with
  | zero => exact H_BASE i
  | succ n ih => exact H_CELL i n (H_ENV i n ih)

/-! ## 2. Without strict causality the rule is unsound -/

/-- **The non-strict rule is unsound** (abstractly): with `G = A = False` at every level
`≥ 1`, all premises of the non-strict rule hold and its conclusion fails. -/
theorem nonstrict_unsound :
    ∃ (G A : Unit → Nat → Prop),
      (∀ i, G i 0) ∧ (∀ i n, (∀ i', G i' n) → A i n) ∧ (∀ i n, A i n → G i n) ∧
      ¬ (∀ i n, G i n) := by
  refine ⟨fun _ n => n = 0, fun _ n => n = 0, fun _ => rfl, fun _ _ h => h (), fun _ _ h => h, ?_⟩
  intro h; exact absurd (h () 1) (by decide)

/-- The contract of a buffer with input `inp` and output `out`: "if `inp` was 0 before `n`,
`out` was 0 before `n`" (guarantee `out` low up to `n`, assumption `inp` low up to `n`). -/
def Low (x : Nat → Bool) (n : Nat) : Prop := ∀ t, t < n → x t = false

/-- **Counter-example: a zero-delay loop.** Two buffers, `x = y` and `y = x` with no delay,
on the trace `x = y = true`. Each buffer meets its contract in the non-strict form
(`Low y n → Low x n`, `Low x n → Low y n`), the environment premise is the neighbour's
guarantee at the same level, the base level holds, and yet `x` is not low. So the
assume-guarantee circle is unsound without H_LUT_POS-style strict delay. -/
theorem zero_delay_cex :
    ∃ x y : Nat → Bool, (∀ t, x t = y t) ∧ (∀ t, y t = x t) ∧
      -- the non-strict rule's premises, cells `false ↦ x`, `true ↦ y`
      (let G : Bool → Nat → Prop := fun i => if i then Low y else Low x
       let A : Bool → Nat → Prop := fun i => if i then Low x else Low y
       (∀ i, G i 0) ∧ (∀ i n, (∀ i', G i' n) → A i n) ∧ (∀ i n, A i n → G i n) ∧
       ¬ (∀ i n, G i n)) := by
  refine ⟨fun _ => true, fun _ => true, fun _ => rfl, fun _ => rfl, ?_⟩
  refine ⟨fun i => ?_, fun i n h => ?_, fun i n h => ?_, fun h => ?_⟩
  · cases i <;> (intro t ht; omega)
  · cases i
    · exact h true
    · exact h false
  · cases i <;> exact h
  · have := h false 1 0 (by decide); simp at this

/-- **The same loop with a one-tick delay meets the strict rule**, which then proves both
wires low forever: `x (t+1) = y t`, `y (t+1) = x t`, both 0 at power-up. -/
theorem unit_delay_ok (x y : Nat → Bool) (hx : ∀ t, x (t + 1) = y t) (hy : ∀ t, y (t + 1) = x t)
    (hx0 : x 0 = false) (hy0 : y 0 = false) : ∀ t, x t = false ∧ y t = false := by
  have r := ag_step (ι := Bool) (fun i => if i then Low y else Low x)
    (fun i => if i then Low x else Low y)
    (fun i => by cases i <;> (intro t ht; omega))
    (fun i n h => by cases i; exact h true; exact h false)
    (fun i n h => by
      cases i
      · intro t ht
        cases t with
        | zero => exact hx0
        | succ t => rw [hx t]; exact h t (by omega)
      · intro t ht
        cases t with
        | zero => exact hy0
        | succ t => rw [hy t]; exact h t (by omega))
  exact fun t => ⟨r false (t + 1) t (by omega), r true (t + 1) t (by omega)⟩

/-- Non-vacuity of `unit_delay_ok`: the all-zero trace satisfies it (and it is the only
one, by the theorem). -/
theorem unit_delay_witness :
    (∀ t, (fun _ => false : Nat → Bool) (t + 1) = (fun _ => false : Nat → Bool) t) ∧
    (fun _ => false : Nat → Bool) 0 = false := ⟨fun _ => rfl, rfl⟩

end Formal.Cells.AssumeGuarantee
