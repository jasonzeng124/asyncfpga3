import Formal.Cells.KleeneWin
import Formal.Cells.Necessity5Delay
import Formal.Cells.ResetCapstone
import Formal.Cells.ZeroDelayRefine
import Formal.Cells.OnGcdArbKappaTight

/-!
# SelfAuditB7 (probe Bsa4): checks and gap-fillers from self-audit 4 of shard B's 2026-10-29 work

Notes: `formal/notes/B-self-audit4.md`. Nothing here changes a shipped statement; each item
either fills a gap between a journal/JSON claim and the Lean, or states a degeneracy of a
shipped witness as a theorem, so it is checked rather than asserted.

## Assumed / proved / NOT covered

**Assumed:** nothing beyond the imported files' definitions.

**Proved:**
* `flush_not_necessary_all` (Necessity5Delay gap): the journal/JSON say H_ACK_FLUSH is "NOT
  necessary for DACK ≥ 3"; the shipped `flush_not_necessary` is the single instance DACK = 3.
  Here: for EVERY `m ≥ 2` (DACK = m + 1 ≥ 3), the uniform unit-hop line `δ k = m + 1 - k`,
  `w = 1`, violates `Flush` and is one clean pulse (`Pulse`). Point delays, line level only.
* `steer_win_bound` (KleeneWin / JSON gap): the JSON `strict.x_window` text says "Sufficient
  without the split: +W under H_W_BOUND (c_e + a_l ≤ W for every race pair)"; no Lean theorem
  carried it. Proved here for `bd_steer` only (from `steer_win_exact`); the other cells
  (join, muxn, latch, C-element) by the same one-line argument, NOT written.
* `μW_not_wiring` (ResetCapstone, degeneracy of H_MAP's witness): the joint witness's channel
  map sends the request AND acknowledge of channel 7 and of channel 8 to the same node 65:
  `MapOK` does not constrain wiring (not injective, req = ack allowed). So the headline's
  B-side content is only "the mapped node VALUES at T0 are the RTL reset values".
* `wv_frozen` (ResetCapstoneWit, degeneracy): the "non-degenerate" reset witness `wv` is the
  reset state at every step `k ≤ E` (power-up = reset state, every gate held): no node moves
  before `E`; H_STEER_HOLD on `(F+34, E]` holds because nothing moves.
* `abs_run_indep` (ZeroDelayRefine): the zero-delay link run `lI/lO/lC` that every physical
  behaviour "refines" depends on the behaviour only through one bit (`swOf P`) and the token
  value: the C-side facts (`Link`, `Protocol`, `Held`) are facts about two fixed traces.
* `spread_corr_iff` (OnGcdArbKappaTight): `H_SPREAD_CORRELATED arc` is exactly `arc = litArc`
  (the named hypothesis is the `lit` model itself, so `spread_correlated_safe` is `rt1b_safe`).

**NOT covered:** the other degeneracies listed in the note (frozen C family of
`reset_capstone_nonvac`, all-true zero-delay `pend_fast_nonvacuous`, unit-delay kernels of
the rig witnesses) are already stated in the shipped files; not re-proved here.
-/

namespace Formal.Cells.SelfAuditB7
open Formal.Cells

/-! ## 1. H_ACK_FLUSH is not necessary for every DACK ≥ 3 (point delays, line level) -/

section flush
open Formal.Cells.PipeTimedN Formal.Cells.Necessity5Delay

/-- The uniform unit-hop line with `m + 1` copies: copy `k` arrives `m + 1 - k` after the node. -/
def dU (m : Nat) (k : Nat) : Nat := m + 1 - k

theorem dU_fmax (m : Nat) : fmax (dU m) m = m + 1 := by
  have h1 := le_fmax_of (dU m) (m + 1) m 0 (Nat.zero_le _) (by simp [dU])
  obtain ⟨k, hk, e⟩ := fmax_eq (dU m) m
  have : dU m k ≤ m + 1 := by simp [dU]
  omega

theorem dU_fmin (m : Nat) : fmin (dU m) m = 1 := by
  have h1 := fmin_le_of (dU m) 1 m m (Nat.le_refl _) (by simp [dU])
  obtain ⟨k, hk, e⟩ := fmin_eq (dU m) m
  have : 1 ≤ dU m k := by simp only [dU]; omega
  omega

/-- **H_ACK_FLUSH is not necessary for any DACK = m + 1 ≥ 3** (generalises the shipped
`flush_not_necessary`, which is `m = 2`): the line violates `Flush` and is still one pulse. -/
theorem flush_not_necessary_all (m : Nat) (hm : 2 ≤ m) :
    ¬ Flush (dU m) m 1 ∧ Pulse (dU m) m 1 := by
  refine ⟨?_, (pulse_iff (dU m) m 1 (Nat.le_refl _)).2 ?_⟩
  · unfold Flush; rw [dU_fmax, dU_fmin]; omega
  · intro k hk hlt
    rw [dU_fmax] at hlt
    have hk1 : 1 ≤ k := by simp only [dU] at hlt; omega
    exact ⟨k - 1, by omega, by simp only [dU]; omega, by simp only [dU]; omega⟩

/-- At `m = 2` it is the shipped instance's line (`δ = (3, 2, 1)`). -/
theorem dU_two (k : Nat) : dU 2 k = 3 - k := rfl

end flush

/-! ## 2. H_W_BOUND (window widths bounded by `W` on every race pair) is sufficient: steer -/

section wbound
open Formal.Cells.KleeneWin

/-- **`+W` under H_W_BOUND, `bd_steer`.** If every race pair's trailing + leading half-windows
sum to at most `W` (`cS0 + aR ≤ W`, `cF + aS1 ≤ W`), the binary-edge forms with `+W` are
sufficient for box safety, whatever the split. -/
theorem steer_win_bound (b v : Bool) (Rlo Rhi Slo Shi R F aR cR aF cF S0 cS0 S1 aS1 W : Int)
    (hR : Rlo ≤ Rhi) (hS : Slo ≤ Shi) (hRF : R - aR < F + cF) (hwR : 0 ≤ aR + cR)
    (hwF : 0 ≤ aF + cF)
    (H_W_BOUND : cS0 + aR ≤ W ∧ cF + aS1 ≤ W)
    (h1 : S0 + Shi + W ≤ R + Rlo) (h2 : F + Rhi + W ≤ S1 + Slo) :
    SteerW b v Rlo Rhi Slo Shi R F aR cR aF cF S0 cS0 S1 aS1 :=
  (steer_win_exact b v Rlo Rhi Slo Shi R F aR cR aF cF S0 cS0 S1 aS1 hR hS hRF hwR hwF).2
    ⟨by omega, by omega⟩

/-- Non-vacuity: `W = 1` with the split of `steer_split_matters` (i) (every window width 1,
race sums 1) and binary margins of exactly 1. -/
theorem steer_win_bound_witness (b v : Bool) :
    SteerW b v 300 300 500 500 1001 3000 0 1 1 0 800 0 2801 0 :=
  steer_win_bound b v 300 300 500 500 1001 3000 0 1 1 0 800 0 2801 0 1 (by decide) (by decide)
    (by decide) (by decide) (by decide) ⟨by decide, by decide⟩ (by decide) (by decide)

end wbound

/-! ## 3. ResetCapstone: H_MAP's witness is not a wiring map -/

section capmap
open Formal.Net Formal.Net.CapNet Formal.Cells.ResetCapstone

/-- **`MapOK` does not constrain wiring.** The witness map `μW` (which satisfies `MapOK`,
`μW_ok`) reads the request and the acknowledge of channel 7 and of channel 8 from ONE node
(65, `ufork0`). -/
theorem μW_not_wiring :
    μW.μR ⟨7, by decide⟩ = 65 ∧ μW.μA ⟨7, by decide⟩ = 65 ∧
    μW.μR ⟨8, by decide⟩ = 65 ∧ μW.μA ⟨8, by decide⟩ = 65 ∧ MapOK μW :=
  ⟨rfl, rfl, rfl, rfl, μW_ok⟩

end capmap

/-! ## 4. ResetCapstoneWit: the D = 40 witness is frozen up to E -/

section frozen
open Formal.Cells.ResetCapstoneWit Formal.Cells.TernarySound Formal.Cells.ResetGcd

/-- **The reset witness never moves before `E`**: every non-rst node shows its reset value at
every step `k ≤ E = 1007` (the run starts IN the reset state and every gate holds). -/
theorem wv_frozen : ∀ k i, k ≤ ResetCapstoneWit.E → i ≠ 0 → wv k i = gR i := by
  intro k i hk hi
  rw [wv_lt hk, frz_gate hi]

end frozen

/-! ## 5. ZeroDelayRefine: the abstract run is fixed -/

section zdr
open Formal.Cells.ZeroDelayRefine

/-- The abstract link run depends on the physical behaviour only through `swOf P` and the
token value: two parameter sets with the same switch bit get the same abstract traces. -/
theorem abs_run_indep (sw v : Bool) (w0 u : Nat) (P Q : LinkExact.Par)
    (h : swOf P = sw) (h' : swOf Q = sw) :
    lI (swOf P) v w0 = lI (swOf Q) v w0 ∧ lO (swOf P) v u = lO (swOf Q) v u := by
  rw [h, h']; exact ⟨rfl, rfl⟩

end zdr

/-! ## 6. OnGcdArbKappaTight: H_SPREAD_CORRELATED is the `lit` model -/

section spread
open Formal.Cells.OnGcdArbKappaTight

theorem spread_corr_iff (arc : A7 → CArc) : H_SPREAD_CORRELATED arc ↔ arc = litArc :=
  ⟨fun h => funext h, fun h e => by rw [h]⟩

end spread

end Formal.Cells.SelfAuditB7
