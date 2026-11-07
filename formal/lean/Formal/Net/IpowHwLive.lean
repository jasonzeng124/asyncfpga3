import Formal.Net.IpowHwProof

/-!
# The bdc ipow graph computes `b^e mod 2^32` on every i32 input, and every run finishes (probe C-8v)

Core Lean only. Combines `ipow_hw_graph_computes_ipowC` (IpowHwProof: the
dataflow graph bdc emits for ipow ends every complete run with the C
function's result) with `ipowC_spec` below (the C function, on every i32 bit
pattern `e < 2^32` and every `b`, terminates within fuel 32 and returns
`b^e mod 2^32` when `e` is a non-negative i32, and `1` when it is negative).

* `ipow_hw_graph_computes_pow`: a complete run exists, and EVERY complete run
  (any schedule, any arbitration of the 2 two-input control_merges) ends in the
  store with exactly `[ipowSpec b e]` on `out0`, the end token on `end`, and
  nothing else.
* Liveness at token level, with no fairness assumption: `ipow_hw_graph_live`,
  `ipow_hw_graph_bounded`, `ipow_hw_graph_no_infinite_run`,
  `ipow_hw_graph_maximal` (same statements as C-8k's for gcd).

Unlike gcd there is no input-range hypothesis beyond "`e` is an i32 bit
pattern": every i32 input terminates (the loop shifts `e` right while
`e > 0`, so at most 31 iterations).

Hypotheses: the token-level ones of C-8i (unbounded FIFO channels,
H_SOURCE_ETERNAL for the 3 source chains bdc leaves live; H_ONE_INVOCATION is
proved from the initial store). `muli` is wrap-around at 32 bits (bdc's
Verilog `*`), so for signed overflow this states what the hardware computes,
which C leaves undefined.
-/

namespace Formal.Net.IpowHw

open Formal.Net.Kahn Formal.Net.GcdHw

/-- The intended meaning, independent of the C and of the graph: for a
non-negative i32 exponent, `b^e` modulo `2^32` (as an i32 bit pattern; equal
mod 2^32 to the signed power for a negative `b`); for a negative exponent the C
loop is never entered and the result is 1. -/
def ipowSpec (b e : Nat) : Nat := if e < 2 ^ 31 then b ^ e % 2 ^ 32 else 1

/-! ## i32 facts -/

theorem gC_iff {e : Nat} (he : e < 2 ^ 32) :
    isT (Ops.cmpi .sgt 32 e 0) = decide (0 < e ∧ e < 2 ^ 31) := by
  have k : (2 ^ (32 - 1) % 2 ^ 32 < (e % 2 ^ 32 + 2 ^ (32 - 1)) % 2 ^ 32) ↔ (0 < e ∧ e < 2 ^ 31) := by
    simp only [Nat.reducePow, Nat.reduceSub] at he ⊢; omega
  unfold Ops.cmpi Ops.flip
  simp only [Nat.zero_mod, Nat.zero_add, isT, Ops.b2n]
  by_cases h : 0 < e ∧ e < 2 ^ 31
  · have h' := k.mpr h
    simp only [h', decide_true, h]; decide
  · have h' : ¬ (2 ^ (32 - 1) % 2 ^ 32 < (e % 2 ^ 32 + 2 ^ (32 - 1)) % 2 ^ 32) := fun x => h (k.mp x)
    simp only [h', decide_false, h]; decide

theorem bit_iff (e : Nat) : isT (Ops.cmpi .eq 32 (Ops.andi 32 e 1) 1) = decide (e % 2 = 1) := by
  rw [andi32_one]
  have : e % 2 = 0 ∨ e % 2 = 1 := by omega
  rcases this with h | h <;> simp [Ops.cmpi, Ops.b2n, isT, h]

theorem shrsi1 {x : Nat} (h : x < 2 ^ 31) : Ops.shrsi 32 x 1 = x / 2 := by
  have h' : x % 2 ^ 32 = x := Nat.mod_eq_of_lt (by omega)
  unfold Ops.shrsi; rw [h', if_pos (by simpa using h), Nat.shiftRight_eq_div_pow]

theorem loop_zero (f r b : Nat) : ipowLoop (f + 1) r b 0 = some r := by
  simp only [ipowLoop]; rw [if_neg (by decide)]

/-- One loop iteration preserves `r * b^e mod 2^32`. -/
theorem step_eq (r b e : Nat) :
    (if decide (e % 2 = 1) = true then Ops.muli 32 r b else r) * (Ops.muli 32 b b) ^ (e / 2) % 2 ^ 32
      = r * b ^ e % 2 ^ 32 := by
  have hp : b ^ e = (b * b) ^ (e / 2) * b ^ (e % 2) := by
    conv => lhs; rw [← Nat.div_add_mod e 2]
    rw [Nat.pow_add, Nat.pow_mul, Nat.pow_two]
  unfold Ops.muli
  rw [Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod]
  have : e % 2 = 0 ∨ e % 2 = 1 := by omega
  rcases this with h | h
  · simp only [h, Nat.zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte] at hp ⊢
    rw [hp, Nat.pow_zero, Nat.mul_one]
  · simp only [h, decide_true, ↓reduceIte] at hp ⊢
    rw [Nat.mod_mul_mod, hp, Nat.pow_one, Nat.mul_assoc, Nat.mul_comm b]

/-- The C loop on a non-negative i32 exponent `e < 2^f` returns
`r * b^e mod 2^32` within `f + 1` iterations. -/
theorem loop_spec : ∀ f r b e, r < 2 ^ 32 → e < 2 ^ 31 → e < 2 ^ f →
    ipowLoop (f + 1) r b e = some (r * b ^ e % 2 ^ 32) := by
  intro f; induction f with
  | zero =>
    intro r b e hr _ hf
    have : e = 0 := by simp at hf; omega
    subst this; rw [loop_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hr]
  | succ f ih =>
    intro r b e hr he hf
    by_cases h0 : e = 0
    · subst h0; rw [loop_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hr]
    have he32 : e < 2 ^ 32 := by omega
    rw [ipowLoop]
    rw [if_pos (by rw [gC_iff he32]; simp only [decide_eq_true_eq]; omega), bit_iff, shrsi1 he]
    have hr' : (if decide (e % 2 = 1) = true then Ops.muli 32 r b else r) < 2 ^ 32 := by
      split
      · exact Nat.mod_lt _ (by decide)
      · exact hr
    rw [ih _ _ _ hr' (by omega) (by rw [Nat.pow_succ] at hf; omega), step_eq]

/-- **The C ipow, on every i32 exponent, terminates within fuel 32 and returns
`ipowSpec b e`.** -/
theorem ipowC_spec (b : Nat) {e : Nat} (he : e < 2 ^ 32) : ipowC 32 b e = some (ipowSpec b e) := by
  unfold ipowC ipowSpec
  by_cases h : e < 2 ^ 31
  · rw [if_pos h, loop_spec 31 1 b e (by decide) h h, Nat.one_mul]
  · rw [if_neg h]; simp only [ipowLoop]
    rw [if_neg (by rw [gC_iff he]; simp only [decide_eq_true_eq]; omega)]

/-! ## The graph -/

/-- Initial store: one token each on `b`, `e`, `start` (see `init_store`). -/
abbrev init (b e : Nat) : Store Nat Nat := St T0 [b, e]
/-- Final store: `[r]` on `out0`, the end token, nothing else (see `final_store`,
`final_store_only`). -/
abbrev final (r : Nat) : Store Nat Nat := St T2 [r]

/-- **The imported ipow graph computes `b^e mod 2^32` on every i32 input.**
Some schedule completes; every complete run, on every schedule and every
control_merge arbitration, ends in `final (ipowSpec b e)`, i.e. with exactly
`[ipowSpec b e]` on `out0`; and no run is longer than a complete one. -/
theorem ipow_hw_graph_computes_pow (b : Nat) {e : Nat} (he : e < 2 ^ 32) :
    (∃ n, Run (step G) (init b e) n (final (ipowSpec b e))) ∧
    (∀ m t, Run (step G) (init b e) m t → Terminal (step G) t →
      t = final (ipowSpec b e) ∧ t chOut = [ipowSpec b e] ∧ t chEnd = [0]) ∧
    (∃ n, ∀ m u, Run (step G) (init b e) m u → m ≤ n) := by
  obtain ⟨h1, h2, h3⟩ := ipow_hw_graph_computes_ipowC (ipowC_spec b he)
  refine ⟨h1, fun m t ht hT => ?_, h3⟩
  have e := h2 m t ht hT
  subst e
  exact ⟨rfl, (final_store _).1, (final_store _).2⟩

theorem closedG : Closed (step G) (GcdHw.Inv spine) :=
  closed_of_check spine rules spine_nodup spine_ok

theorem diamondG : DiamondOn (step G) (GcdHw.Inv spine) :=
  wfOn_diamond (wfOn_of_check spine rules spine_nodup ins_ok outs_ok)

/-- Liveness, prefix form: every partial run from the initial store can be
completed, and every completion ends in `final (ipowSpec b e)` after the same
number of firings. -/
theorem ipow_hw_graph_live (b : Nat) {e : Nat} (he : e < 2 ^ 32) :
    ∀ m u, Run (step G) (init b e) m u →
      ∃ k, Run (step G) u k (final (ipowSpec b e)) ∧
        ∀ k' t, Run (step G) u k' t → Terminal (step G) t → t = final (ipowSpec b e) ∧ k' = k := by
  intro m u hu
  obtain ⟨n, hn⟩ := reach_ipowC (ipowC_spec b he)
  have hT := final_terminal (ipowSpec b e)
  obtain ⟨_, hk⟩ := prefix_run closedG diamondG hu hn hT (init_inv b e)
  refine ⟨n - m, hk, fun k' t hk' ht => ?_⟩
  have := (determinate spine rules spine_nodup ins_ok outs_ok spine_ok (init_inv b e)
    hn hT (run_trans hu hk') ht)
  exact ⟨this.1, by omega⟩

/-- Bounded: one bound on the length of every run from the initial store. -/
theorem ipow_hw_graph_bounded (b : Nat) {e : Nat} (he : e < 2 ^ 32) :
    ∃ N, ∀ m u, Run (step G) (init b e) m u → m ≤ N :=
  (ipow_hw_graph_computes_pow b he).2.2

theorem run_of_seq {σ : Nat → Store Nat Nat}
    (hσ : ∀ i, ∃ l, step G (σ i) l = some (σ (i + 1))) : ∀ i, Run (step G) (σ 0) i (σ i) := by
  intro i; induction i with
  | zero => exact Run.refl _
  | succ i ih =>
    obtain ⟨l, hl⟩ := hσ i
    exact run_trans ih (Run.cons l hl (Run.refl _))

/-- No infinite run from the initial store, on any schedule. -/
theorem ipow_hw_graph_no_infinite_run (b : Nat) {e : Nat} (he : e < 2 ^ 32) :
    ¬ ∃ σ : Nat → Store Nat Nat, σ 0 = init b e ∧ ∀ i, ∃ l, step G (σ i) l = some (σ (i + 1)) := by
  rintro ⟨σ, h0, hσ⟩
  obtain ⟨N, hN⟩ := ipow_hw_graph_bounded b he
  have := hN (N + 1) (σ (N + 1)) (h0 ▸ run_of_seq hσ (N + 1))
  omega

/-- Every maximal run (nothing enabled) is complete and holds `[ipowSpec b e]`
on `out0`. -/
theorem ipow_hw_graph_maximal (b : Nat) {e : Nat} (he : e < 2 ^ 32)
    {m : Nat} {t : Store Nat Nat} (hr : Run (step G) (init b e) m t)
    (hmax : ∀ l, step G t l = none) : t chOut = [ipowSpec b e] :=
  ((ipow_hw_graph_computes_pow b he).2.1 m t hr hmax).2.1

/-! ## Sanity: the spec on the kernel's own `main` vector (3^7), and a negative
exponent. `ipowSpec` is evaluated by the kernel, not pasted from a run. -/

example : ipowSpec 3 7 = 2187 := by decide
example : ipowSpec 3 (2 ^ 32 - 1) = 1 := by decide

end Formal.Net.IpowHw
