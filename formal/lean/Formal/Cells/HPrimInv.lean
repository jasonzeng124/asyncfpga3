import Formal.Core.Delay.InvolutionTrace

/-!
# Formal.Cells.HPrimInv — do read-time / window gate models cover involution channels?

Shard B, THE goal, H_PRIM. Needs Mathlib (ℝ). Companion of `HPrimWin` (Core, Kleene, Int
time). Notes: `formal/notes/B-hprim.md`.

## Problem, plainly

PROGRAM.md asks H_PRIM to use the delay semantics that is pessimistic for what is proved,
or to prove the result for transport, inertial AND involution channels. Spec v1's `GateOK`
(shard A) and B's `WinH` both describe a gate by READ TIMES: the output at `s` is the gate
function of each pin read at some instant whose distance from `s` is an admissible delay
`[lo, hi]`. Transport (fixed or time-varying delay) and inertial swallowing are instances.
Is an involution channel (Függer/Najvirt/Nowak/Schmid, Core `InvolutionPair`, full trace
semantics with cancellation `outSig`) an instance, when its delays are "in the band"?

## Answer

Not in general. An involution channel shortens the trailing edge of a short pulse below
`δ∞` (down to `δmin`), so an output edge can come EARLIER than `lo` after the input edge
that caused it, at an instant where every read-time model already forces the old value.

* `WinR lo hi x y` (binary window relation, one pin): if the input is the constant `c` on
  `[τ - hi, τ - lo]` then `y τ = c`. It is the 1-pin, Boolean case of `WinH`, and it is
  implied by every read-time model: `win_of_readTime` (any read map `σ s ∈ [s - hi, s - lo]`
  with `y s = x (σ s)`; no monotonicity needed, so Spec v1's one-pin `GateOK` read in real
  time and `DelayPure.Chan`, `win_of_chan`, are instances).
* **`rat_not_win`** (counterexample): Core's `ratPair` (`δ(T) = 2 - 1/(T+2)`, `δ∞ = 2`,
  `δmin = 1`), input pulse on `[0, 3/2)`: the output is high on `[2, 17/6)`; at `τ = 29/10`
  the input is steadily 1 on the window `[9/10, 7/5]` of the band `[3/2, 2]`, but the
  output is 0. So this involution channel, whose isolated-edge delay `δ∞ = 2` lies in the
  band and whose every surviving delay is at most `δ∞`, is NOT a read-time behaviour for the
  band `[3/2, 2]`. `rat_not_readTime`: in particular there is no read map at all.
* `inv_sep_win` (positive, with separation): if consecutive input edges are at least `S`
  apart, `S > δ∞ - δmin`, the involution output IS a window behaviour for the band
  `[min δ↑(S - δ∞') δ↓(S - δ∞'), δ∞']` (`δ∞' = max δ∞↑ δ∞↓`), from Core's
  `trace_transfer_sep`, and for every wider band (`winR_widen`).

## What this means for THE theorem

H_PRIM stated by read times (Spec v1) covers transport and inertial behaviours, and
involution channels only where pulses are long (separated inputs) or the band's lower end
is at most the channel's short-pulse delays. Either the theorem is restricted to
read-time gates (the restriction named in the fidelity table: "an involution channel with
`δmin` below the band's lower end is outside H_PRIM"), or the bands' lower ends must be
taken at most `δmin` of the fabric's channels, which prjxray does not report.

## Not covered
The exact characterisation (which bands cover a given involution pair: the violation needs
an output edge with delay below `lo` whose cause is the only input edge in the window;
see notes/B-hprim.md); the Kleene/multi-pin case (it reduces to this one at a buffer).
-/

namespace Formal.Cells.HPrimInv

open Formal.Core.DelayPure Formal.Core.DelayInvolution Formal.Core.DelayInvolutionTransfer
open Formal.Core.DelayInvolution.InvolutionPair

/-- **The binary window relation of a one-pin gate** (`WinH` with `f = id`, Boolean). -/
def WinR (lo hi : ℝ) (x y : Sig) : Prop :=
  ∀ τ c, (∀ t, τ - hi ≤ t → t ≤ τ - lo → x t = c) → y τ = c

/-- Every read-time model implies the window relation. -/
theorem win_of_readTime {lo hi : ℝ} {x y : Sig} (σ : ℝ → ℝ)
    (hσ : ∀ s, s - hi ≤ σ s ∧ σ s ≤ s - lo) (hy : ∀ s, y s = x (σ s)) : WinR lo hi x y := by
  intro τ c hc
  rw [hy τ]
  exact hc _ (hσ τ).1 (hσ τ).2

/-- The bounded pure-delay channel of Core implies the window relation. -/
theorem win_of_chan {lo hi : ℝ} {x y : Sig} (h : Chan lo hi x y) : WinR lo hi x y := by
  obtain ⟨r, hr⟩ := h
  exact win_of_readTime r.σ (fun s => ⟨r.ge s, r.le s⟩) hr

/-- A wider band gives a weaker relation. -/
theorem winR_widen {lo hi lo' hi' : ℝ} {x y : Sig} (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    (h : WinR lo hi x y) : WinR lo' hi' x y :=
  fun τ c hc => h τ c (fun t h1 h2 => hc t (by linarith) (by linarith))

/-- **Positive, separated inputs.** -/
theorem inv_sep_win (P : InvolutionPair) {S : ℝ} (hS : max P.infUp P.infDown - P.dmin < S)
    (t : ℕ → ℝ) (ht : ∀ n, t n + S ≤ t (n + 1)) (N : ℕ) :
    WinR (min (P.up (S - max P.infUp P.infDown)) (P.down (S - max P.infUp P.infDown)))
      (max P.infUp P.infDown) (listSig ((List.range N).map t)) (P.outSig N t) :=
  win_of_chan (P.trace_transfer_sep hS t ht N).2

/-! ## The counterexample -/

/-- Input edge times: `0, 3/2, 3, ...`. Only the first two are used. -/
noncomputable def tin (n : ℕ) : ℝ := 3 / 2 * n

theorem tin_mono (n : ℕ) : tin n < tin (n + 1) := by
  unfold tin; push_cast; linarith

theorem rat_pw : ratPair.pulseWidth (3 / 2) = 5 / 6 := by
  show (3 / 2 - 2) + ratDelay (3 / 2 - 2) = 5 / 6
  norm_num [ratDelay]

/-- The channel's output for the pulse `[0, 3/2)`: edges at `2` and `17/6`. -/
theorem rat_out : ratPair.outList 2 tin = [2, 17 / 6] := by
  have h := (ratPair.pulse_out 0 (3 / 2) (by norm_num) tin (by simp [tin])
    (by simp [tin])).2 (by rw [rat_dmin_eq]; show (2 : ℝ) - 1 < 3 / 2; norm_num)
  rw [h, rat_pw]
  show [0 + (2 : ℝ), 0 + 2 + 5 / 6] = [2, 17 / 6]
  norm_num

/-- **Counterexample.** The involution output violates the window relation of the band
`[3/2, 2]` at `τ = 29/10`. -/
theorem rat_not_win : ¬ WinR (3 / 2) 2 (listSig ((List.range 2).map tin)) (ratPair.outSig 2 tin) := by
  intro h
  have hin : ∀ t : ℝ, (29 / 10 : ℝ) - 2 ≤ t → t ≤ 29 / 10 - 3 / 2 →
      listSig ((List.range 2).map tin) t = true := by
    intro t h1 h2
    have e : (List.range 2).map tin = [0, 3 / 2] := by
      simp [List.range_succ, tin]
    rw [e]
    unfold listSig
    have a1 : (0 : ℝ) ≤ t := by linarith
    have a2 : ¬ ((3 / 2 : ℝ) ≤ t) := by intro hh; linarith
    simp [a1, a2]
  have hout := h (29 / 10) true hin
  unfold outSig at hout
  rw [rat_out] at hout
  unfold listSig at hout
  have b1 : (2 : ℝ) ≤ 29 / 10 := by norm_num
  have b2 : (17 / 6 : ℝ) ≤ 29 / 10 := by norm_num
  simp [b1, b2] at hout

/-- In particular no read map whatsoever (monotone or not) produces this output from this
input with every read delay in `[3/2, 2]`. -/
theorem rat_not_readTime : ¬ ∃ σ : ℝ → ℝ, (∀ s, s - 2 ≤ σ s ∧ σ s ≤ s - 3 / 2) ∧
    ∀ s, ratPair.outSig 2 tin s = listSig ((List.range 2).map tin) (σ s) := by
  rintro ⟨σ, hσ, hy⟩
  exact rat_not_win (win_of_readTime σ hσ hy)

/-- The channel's own numbers: `δ∞ = 2` (in the band `[3/2, 2]`) and `δmin = 1` (below it). -/
theorem rat_numbers : ratPair.infUp = 2 ∧ ratPair.infDown = 2 ∧ ratPair.dmin = 1 :=
  ⟨rfl, rfl, rat_dmin_eq⟩

end Formal.Cells.HPrimInv
