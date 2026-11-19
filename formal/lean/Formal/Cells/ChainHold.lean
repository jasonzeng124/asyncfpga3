import Formal.Cells.MuxNDecode

/-!
# Formal.Cells.ChainHold — a chain of forcing gates holds its value for the sum of its minimum delays (shard B, 2026-11-19)

**Problem, plainly.** bdc's divider (`compute.div_datapath`) gates its 32 subtract stages with an enable chain:
`tp[0] = joined | z_ack`, `tp[i] = tp[i-1] & tp[0]` (256 kept LUT2s), and stage s's outputs are 0 until `tp[8(s+1)]`.
So quotient bit 0 (stage 31, `uq[0] = tp[256] & ...`) is 0 until the rise of `tp[0]` has walked 256 LUT hops. Formal's
simx found that a matched delay of 5 elements (research's automatic flow, test_divui) delivers the request long before
that (FOR-RESEARCH B12), but a simulation is a sample of delays. This file gives the bound for EVERY delay in the band.

**Proved.**
* `chain_hold`: gates `g 1 .. g n`, each with a pin `j i` reading node `nd (i-1)` that forces the gate to `v` when it
  shows `v`; node `nd 0` shows `v` on `[A, T]`; pin `j i`'s composite delay is between `L i` and `U i`. Then node
  `nd n` shows `v` on `[A + ΣU, T + ΣL]` (sums over the n pins), every behaviour of the Spec gate model, glitches
  included (the other pins of each gate are unconstrained).
* `chain_hold_const`: the same with one bound per hop: `nd n` shows `v` until at least `T + n * Lmin`.
* Reading for the divider: with `nd 0 = tp[0]` at 0 until it rises at `T` (the join), `tp[256]` and with it `uq[0]` stay
  0 until `T + 256 * Lmin + L(uq)`, whatever the band's delays are. A request that reaches the capture earlier
  (an upper bound of its path, e.g. the line's elements at their maximum) is a bundling violation for every operand
  whose quotient is odd.

**Not shown.** The per-route numbers (the LUT2 hops' minimum composite delays and the request path's maximum, from the
decoded route): the margin tool's or a row emitter's job; that the bench reads out0 at the request (the host model).
-/

namespace Formal.Cells.ChainHold
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Timing.Island Formal.Cells.MuxNDecode

/-- Sum of `f 1 .. f n`. -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f (n + 1)

/-- **A chain of forcing gates holds its value for the sum of its minimum pin delays.** -/
theorem chain_hold {p : DelayPar} {c : ℚ} {x : Beh} (n : Nat) (g : Nat → Gate) (src : Nat → Nat → Nat)
    (arcs : Nat → Nat → List Arc) (S : Nat → Nat) (nd : Nat → Nat) (j : Nat → Nat) (v : Bool) (L U : Nat → Nat)
    (A T : Nat)
    (hg : ∀ i, 1 ≤ i → i ≤ n → (g i).out = nd i ∧ CGateOK p c (g i) (src i) (arcs i) (S i) x)
    (hsrc : ∀ i, 1 ≤ i → i ≤ n → src i (j i) = nd (i - 1))
    (hLU : ∀ i, 1 ≤ i → i ≤ n → j i < (g i).k ∧ ∀ D, SumAdm p c (arcs i (j i)) D → L i ≤ D ∧ D ≤ U i)
    (hF : ∀ i, 1 ≤ i → i ≤ n → ForcesP (g i).k (g i).init ([j i].map fun q => (q, v)) v = true)
    (hS : ∀ i, 1 ≤ i → i ≤ n → S i ≤ A + sumTo U i)
    (h0 : ∀ t, A ≤ t → t ≤ T → x (nd 0) t = v) :
    ∀ t, A + sumTo U n ≤ t → t ≤ T + sumTo L n → x (nd n) t = v := by
  induction n with
  | zero => intro t h1 h2; simp [sumTo] at h1 h2; exact h0 t h1 h2
  | succ m ih =>
    intro t h1 h2
    have ih' := ih (fun i a b => hg i a (by omega)) (fun i a b => hsrc i a (by omega))
      (fun i a b => hLU i a (by omega)) (fun i a b => hF i a (by omega)) (fun i a b => hS i a (by omega))
    obtain ⟨hout, hgo⟩ := hg (m + 1) (by omega) le_rfl
    obtain ⟨hk, hb⟩ := hLU (m + 1) (by omega) le_rfl
    rw [← hout]
    refine gate_window (g (m + 1)) (src (m + 1)) (arcs (m + 1)) (S (m + 1)) [j (m + 1)] (fun _ => v) v
      (fun _ => A + sumTo U m) (fun _ => T + sumTo L m) (fun _ => L (m + 1)) (fun _ => U (m + 1)) hgo
      (fun q hq => by simp at hq; rw [hq]; exact ⟨hk, hb⟩) (hF (m + 1) (by omega) le_rfl)
      (fun q hq t' a b => by
        simp at hq; rw [hq, hsrc (m + 1) (by omega) le_rfl]; exact ih' t' a b)
      t (by have := hS (m + 1) (by omega) le_rfl; simp only [sumTo] at this h1; omega)
      (fun q hq => by simp [sumTo] at h1 h2; omega)

theorem sumTo_const (k n : Nat) : sumTo (fun _ => k) n = n * k := by
  induction n with
  | zero => simp [sumTo]
  | succ m ih => simp [sumTo, ih, Nat.succ_mul]

theorem sumTo_ge (f : Nat → Nat) (k n : Nat) (h : ∀ i, 1 ≤ i → i ≤ n → k ≤ f i) : n * k ≤ sumTo f n := by
  induction n with
  | zero => simp
  | succ m ih =>
    have := ih (fun i a b => h i a (by omega)); have := h (m + 1) (by omega) le_rfl
    simp only [sumTo, Nat.succ_mul]; omega

/-- **One minimum per hop.** If every hop's pin delay is at least `Lmin`, the last node still shows `v` at every time up
to `T + n * Lmin` (from `A + ΣU` on). -/
theorem chain_hold_const {p : DelayPar} {c : ℚ} {x : Beh} (n : Nat) (g : Nat → Gate) (src : Nat → Nat → Nat)
    (arcs : Nat → Nat → List Arc) (S : Nat → Nat) (nd : Nat → Nat) (j : Nat → Nat) (v : Bool) (L U : Nat → Nat)
    (A T Lmin : Nat)
    (hg : ∀ i, 1 ≤ i → i ≤ n → (g i).out = nd i ∧ CGateOK p c (g i) (src i) (arcs i) (S i) x)
    (hsrc : ∀ i, 1 ≤ i → i ≤ n → src i (j i) = nd (i - 1))
    (hLU : ∀ i, 1 ≤ i → i ≤ n → j i < (g i).k ∧ ∀ D, SumAdm p c (arcs i (j i)) D → L i ≤ D ∧ D ≤ U i)
    (hF : ∀ i, 1 ≤ i → i ≤ n → ForcesP (g i).k (g i).init ([j i].map fun q => (q, v)) v = true)
    (hS : ∀ i, 1 ≤ i → i ≤ n → S i ≤ A + sumTo U i)
    (h0 : ∀ t, A ≤ t → t ≤ T → x (nd 0) t = v) (hmin : ∀ i, 1 ≤ i → i ≤ n → Lmin ≤ L i) :
    ∀ t, A + sumTo U n ≤ t → t ≤ T + n * Lmin → x (nd n) t = v := by
  intro t h1 h2
  exact chain_hold n g src arcs S nd j v L U A T hg hsrc hLU hF hS h0 t h1
    (by have := sumTo_ge L Lmin n hmin; omega)

/-- The divider's chain LUT2 (`INIT = 8`: `O = I0 & I1`) is forced to 0 by either pin at 0 (decided). -/
theorem lut2_and_pin0 : ForcesP 2 8 ([0].map fun q => (q, false)) false = true := by decide
theorem lut2_and_pin1 : ForcesP 2 8 ([1].map fun q => (q, false)) false = true := by decide

end Formal.Cells.ChainHold
