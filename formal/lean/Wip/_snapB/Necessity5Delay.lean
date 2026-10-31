import Formal.Cells.PipeTimedN

/-!
# Necessity5Delay: `bd_delay[FASTRISE].ack_flush` (H_ACK_FLUSH) at the line level

Probe Bnx5 (shard B). Row `bd_delay[FASTRISE].ack_flush`, inequality
`ahi_b ≤ Won_b + alo_b` (margin 0, no strict field), was "sufficient",
backed by `PipeTimedN.fastrise_or` + `orn_hold_true` (its hypothesis `hov`)
inside `pipe_ctl`. What the pipe consumes from the DACK line is
`orn_hold_true`'s conclusion: a high phase of the node on `[a, a + w)`
appears at the stage's I1 pin as ONE high stretch from the fastest copy's
rise to the slowest copy's fall, `[a + alo, a + w + ahi)` (the times
`PN.ackT` uses).

Model here: the DACK line as the OR of `m + 1` copies with FIXED (point,
transport, one-corner) delays `δ k` (for the real chain this IS the line:
`fastrise_or`; `DACK = m + 1`). With point delays `alo = fmin δ m`,
`ahi = fmax δ m`, so H_ACK_FLUSH reads `Flush δ m w : fmax ≤ fmin + w`.

* **Assumed:** point delays; one high pulse of width `w ≥ 1`.
* **Proved:**
  - `pulse_iff`: the line output is exactly one pulse
    `[a + fmin, a + w + fmax)` (`Pulse`) **iff** `Succ`: every copy except
    the slowest has a later copy at most `w` behind it. This is the exact
    condition (line level, point delays).
  - `flush_succ`: H_ACK_FLUSH implies `Succ` (the shipped direction).
  - `two_exact`: with two copies (`m = 1`, `DACK = 2`, the only DACK ≥ 2 case
    instantiated jointly with a pipe, PipeWitness W2/W3) H_ACK_FLUSH is
    EXACT: `Pulse ↔ Flush`.
  - `flush_not_necessary`: with three copies it is NOT necessary:
    `δ = (3, 2, 1)` (the real `DACK = 3` chain at unit hops), `w = 1`:
    `Flush` fails by 1 and the output is still one clean pulse.
  - Real INITs (`BUF 2'h2`, `FR_SIDE 4'hE` through `lutB`), gate equations
    for ALL `t`: `dack3_clean` (DACK = 3, unit hops, width-1 pulse in,
    one pulse `[11, 14)` out, H_ACK_FLUSH off by 1: `dack3_viol`);
    `dack2_glitch` (DACK = 2, buffer 1 + chain hop 2 vs tap 1, width 1:
    H_ACK_FLUSH off by exactly 1 (`dack2_viol`) and the output is TWO
    pulses, low at 12 between the copies) — the boundary counter-run.
* **NOT covered:** window (non-point) delays (a point run is a window run,
  so the counter-run and the non-necessity instance carry over to any
  window containing them; `Succ`'s sufficiency over windows is not proved);
  the pipe level: no `PipeTimedN` run with the glitch was built, so this
  does not refute `pipe_ctl` itself, and `Won` in the pipe is a LOWER bound
  of the high width (a pipe-level counter-run needs a phase of width
  exactly `Won`).

Core Lean only.
-/

namespace Formal.Cells.Necessity5Delay
open Formal.Cells Formal.Cells.PipeTimedN

/-- Offset `x` (from the node's rise) is covered by some copy's high stretch. -/
def Cov (δ : Nat → Nat) (m w x : Nat) : Prop := ∃ k, k ≤ m ∧ δ k ≤ x ∧ x < δ k + w

/-- The OR output is exactly one pulse `[fmin, fmax + w)` (offsets from `a`). -/
def Pulse (δ : Nat → Nat) (m w : Nat) : Prop :=
  ∀ x, Cov δ m w x ↔ (fmin δ m ≤ x ∧ x < fmax δ m + w)

/-- Every copy but the slowest has a later copy at most `w` behind. -/
def Succ (δ : Nat → Nat) (m w : Nat) : Prop :=
  ∀ k, k ≤ m → δ k < fmax δ m → ∃ k', k' ≤ m ∧ δ k < δ k' ∧ δ k' ≤ δ k + w

/-- H_ACK_FLUSH at point delays: `ahi ≤ w + alo`. -/
def Flush (δ : Nat → Nat) (m w : Nat) : Prop := fmax δ m ≤ fmin δ m + w

theorem cov_range (δ : Nat → Nat) (m w x : Nat) (h : Cov δ m w x) :
    fmin δ m ≤ x ∧ x < fmax δ m + w := by
  obtain ⟨k, hk, h1, h2⟩ := h
  have := fmin_le_of δ (δ k) m k hk (Nat.le_refl _)
  have := le_fmax_of δ (δ k) m k hk (Nat.le_refl _)
  omega

theorem cover_from_min (δ : Nat → Nat) (m w : Nat) (hw : 1 ≤ w) (h : Succ δ m w) :
    ∀ n, fmin δ m + n < fmax δ m + w → Cov δ m w (fmin δ m + n) := by
  intro n
  induction n with
  | zero =>
    intro _
    obtain ⟨k, hk, e⟩ := fmin_eq δ m
    exact ⟨k, hk, by omega, by omega⟩
  | succ n ih =>
    intro h2
    obtain ⟨k, hk, c1, c2⟩ := ih (by omega)
    by_cases hc : fmin δ m + (n + 1) < δ k + w
    · exact ⟨k, hk, by omega, hc⟩
    · have hlt : δ k < fmax δ m := by omega
      obtain ⟨k', hk', s1, s2⟩ := h k hk hlt
      exact ⟨k', hk', by omega, by omega⟩

theorem pulse_of_succ (δ : Nat → Nat) (m w : Nat) (hw : 1 ≤ w) (h : Succ δ m w) :
    Pulse δ m w := by
  intro x
  refine ⟨cov_range δ m w x, fun hx => ?_⟩
  have e : x = fmin δ m + (x - fmin δ m) := by omega
  rw [e]; exact cover_from_min δ m w hw h _ (by omega)

theorem succ_of_pulse (δ : Nat → Nat) (m w : Nat) (h : Pulse δ m w) : Succ δ m w := by
  intro k hk hlt
  have := fmin_le_of δ (δ k) m k hk (Nat.le_refl _)
  obtain ⟨k', hk', c1, c2⟩ := (h (δ k + w)).2 ⟨by omega, by omega⟩
  exact ⟨k', hk', by omega, c1⟩

/-- **Exact condition** for the DACK OR line at point delays. -/
theorem pulse_iff (δ : Nat → Nat) (m w : Nat) (hw : 1 ≤ w) : Pulse δ m w ↔ Succ δ m w :=
  ⟨succ_of_pulse δ m w, pulse_of_succ δ m w hw⟩

/-- H_ACK_FLUSH is sufficient (the shipped direction, here at point delays). -/
theorem flush_succ (δ : Nat → Nat) (m w : Nat) (h : Flush δ m w) : Succ δ m w := by
  intro k hk _
  obtain ⟨k', hk', e⟩ := fmax_eq δ m
  have := fmin_le_of δ (δ k) m k hk (Nat.le_refl _)
  unfold Flush at h
  exact ⟨k', hk', by omega, by omega⟩

/-- **Two copies (`DACK = 2`): H_ACK_FLUSH is exact.** -/
theorem two_exact (δ : Nat → Nat) (w : Nat) (hw : 1 ≤ w) : Pulse δ 1 w ↔ Flush δ 1 w := by
  rw [pulse_iff δ 1 w hw]
  constructor
  · intro h
    show max (δ 0) (δ 1) ≤ min (δ 0) (δ 1) + w
    rcases Nat.lt_or_ge (δ 0) (δ 1) with c | c
    · obtain ⟨k', hk', s1, s2⟩ := h 0 (Nat.zero_le _) (by show δ 0 < max (δ 0) (δ 1); omega)
      rcases (by omega : k' = 0 ∨ k' = 1) with rfl | rfl <;> omega
    · rcases Nat.lt_or_ge (δ 1) (δ 0) with c' | c'
      · obtain ⟨k', hk', s1, s2⟩ := h 1 (Nat.le_refl _) (by show δ 1 < max (δ 0) (δ 1); omega)
        rcases (by omega : k' = 0 ∨ k' = 1) with rfl | rfl <;> omega
      · omega
  · exact flush_succ δ 1 w

/-- **Not necessary from three copies on**: `δ = (3, 2, 1)`, `w = 1`. -/
theorem flush_not_necessary :
    ¬ Flush (fun k => 3 - k) 2 1 ∧ Pulse (fun k => 3 - k) 2 1 := by
  refine ⟨by unfold Flush; decide, (pulse_iff _ 2 1 (by decide)).2 ?_⟩
  intro k hk hlt
  have hm : fmax (fun k => 3 - k) 2 = 3 := by decide
  rw [hm] at hlt
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · simp at hlt
  · exact ⟨0, by decide, by decide, by decide⟩
  · exact ⟨1, by decide, by decide, by decide⟩

/-- `Succ` is monotone in the width: every longer phase is clean too. -/
theorem succ_mono (δ : Nat → Nat) (m w w' : Nat) (hw : w ≤ w') (h : Succ δ m w) : Succ δ m w' := by
  intro k hk hlt
  obtain ⟨k', hk', s1, s2⟩ := h k hk hlt
  exact ⟨k', hk', s1, by omega⟩

/-! ## Real-INIT gate-level runs (transport hops, equations for all `t`)

`bd_delay #(.N(n), .FASTRISE(1))`: `s1 = BUF(s0)`, `s(i+1) = FR_SIDE(s i, s0)`
(I0 = chain, I1 = tap). Before `t = hop` the outputs are their power-up
value 0. -/

macro "n5_omega" : tactic =>
  `(tactic| (simp only [← Bool.decide_and, ← Bool.decide_or, ← decide_not, Bool.false_eq,
    Bool.true_eq, decide_eq_decide, decide_eq_true_eq, decide_eq_false_iff_not] at *; omega))

/-- Node pulse of width 1 at `[10, 11)`. -/
def sIn (t : Nat) : Bool := decide (10 ≤ t ∧ t < 11)

section dack3
/-- DACK = 3, every hop 1 tick. -/
def s1 (t : Nat) : Bool := if t < 1 then false else lutB Bundling.BUF [sIn (t - 1)]
def s2 (t : Nat) : Bool := if t < 1 then false else lutB Bundling.FR_SIDE [s1 (t - 1), sIn (t - 1)]
def s3 (t : Nat) : Bool := if t < 1 then false else lutB Bundling.FR_SIDE [s2 (t - 1), sIn (t - 1)]

theorem s1_eq (t : Nat) : s1 (t + 1) = lutB Bundling.BUF [sIn t] := by simp [s1]
theorem s2_eq (t : Nat) : s2 (t + 1) = lutB Bundling.FR_SIDE [s1 t, sIn t] := by simp [s2]
theorem s3_eq (t : Nat) : s3 (t + 1) = lutB Bundling.FR_SIDE [s2 t, sIn t] := by simp [s3]

/-- The output is ONE pulse `[11, 14)` for every `t`. -/
theorem s1_cl (t : Nat) : s1 t = decide (11 ≤ t ∧ t < 12) := by
  unfold s1; split
  · simp only [Bool.false_eq, decide_eq_false_iff_not]; omega
  · rw [Bundling.buf_bin]; simp only [sIn, decide_eq_decide]; omega

theorem s2_cl (t : Nat) : s2 t = decide (11 ≤ t ∧ t < 13) := by
  unfold s2; split
  · simp only [Bool.false_eq, decide_eq_false_iff_not]; omega
  · rw [fr_bin, s1_cl]; simp only [sIn]; n5_omega

/-- The output is ONE pulse `[11, 14)` for every `t`. -/
theorem dack3_clean (t : Nat) : s3 t = decide (11 ≤ t ∧ t < 14) := by
  unfold s3; split
  · simp only [Bool.false_eq, decide_eq_false_iff_not]; omega
  · rw [fr_bin, s2_cl]; simp only [sIn]; n5_omega

/-- Its copies are `δ = (3, 2, 1)`: alo = 1, ahi = 3, w = 1:
H_ACK_FLUSH `ahi ≤ w + alo` fails by exactly 1. -/
theorem dack3_viol : ¬ (3 ≤ 1 + 1) ∧ 3 = 1 + 1 + 1 := by decide
end dack3

section dack2
/-- DACK = 2: buffer 1, chain hop 2 (ripple copy 3), tap hop 1 (copy 1). -/
def u1 (t : Nat) : Bool := if t < 1 then false else lutB Bundling.BUF [sIn (t - 1)]
def u2 (t : Nat) : Bool :=
  if t < 2 then false else lutB Bundling.FR_SIDE [u1 (t - 2), sIn (t - 1)]

theorem u1_eq (t : Nat) : u1 (t + 1) = lutB Bundling.BUF [sIn t] := by simp [u1]
theorem u2_eq (t : Nat) (h : 1 ≤ t) :
    u2 (t + 1) = lutB Bundling.FR_SIDE [u1 (t - 1), sIn t] := by
  simp only [u2]; rw [ite_eq_right_iff.mpr (by omega)]; congr 3 <;> congr 1 <;> omega

theorem u1_cl (t : Nat) : u1 t = decide (11 ≤ t ∧ t < 12) := by
  unfold u1; split
  · simp only [Bool.false_eq, decide_eq_false_iff_not]; omega
  · rw [Bundling.buf_bin]; simp only [sIn, decide_eq_decide]; omega

/-- The output for every `t`: TWO pulses, `[11, 12)` (tap) and `[13, 14)`
(ripple), low at 12 inside the stretch `[11, 14)` the pipe assumes. -/
theorem dack2_out (t : Nat) : u2 t = decide (t = 11 ∨ t = 13) := by
  unfold u2; split
  · simp only [Bool.false_eq, decide_eq_false_iff_not]; omega
  · rw [fr_bin, u1_cl]; simp only [sIn]; n5_omega

theorem dack2_glitch : u2 11 = true ∧ u2 12 = false ∧ u2 13 = true := by
  rw [dack2_out, dack2_out, dack2_out]; decide

/-- Copies `(3, 1)`, w = 1: H_ACK_FLUSH `3 ≤ 1 + 1` fails by exactly 1. -/
theorem dack2_viol : ¬ Flush (fun k => if k = 0 then 3 else 1) 1 1 ∧
    fmax (fun k => if k = 0 then 3 else 1) 1 = fmin (fun k => if k = 0 then 3 else 1) 1 + 1 + 1 := by
  unfold Flush; decide

/-- The same pair of copies with `w = 2` (H_ACK_FLUSH met with equality) is
clean: non-vacuity of the sufficient side at the same delays. -/
theorem dack2_ok : Flush (fun k => if k = 0 then 3 else 1) 1 2 ∧
    Pulse (fun k => if k = 0 then 3 else 1) 1 2 :=
  ⟨by unfold Flush; decide, (two_exact _ 2 (by decide)).2 (by unfold Flush; decide)⟩
end dack2

end Formal.Cells.Necessity5Delay
