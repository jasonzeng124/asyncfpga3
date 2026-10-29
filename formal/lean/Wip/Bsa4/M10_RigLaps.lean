-- Bsa4 mutant M10 of Formal/Cells/RigLaps.lean: one change, '(H_PEND_FAST : r + 1 + dF + dP ≤ T) : ¬ LapInv a b ch T' -> '(H_PEND_FAST : r + dF + dP ≤ T) : ¬ LapInv a b ch T'. Expected: FAIL.
import Formal.Cells.RigSrc

/-!
# Probe Blap (shard B): gcd_rig's laps, the sink-side SI obligation, and the per-lap cut

Notes: `formal/notes/B-rig-laps.md`.

gcd_rig (`cells/hw/gcd_rig.v`) re-offers `start` after every result. C proved the FIRST
result (`CapstoneRig.gcd_rig_first`) and showed that re-arming at a re-offer fails
(`rearm_fails_at_reoffer`). This file is the cell-level side of "every result".

Traces (rig time): `e` = `env_c` (uenv1, `bd_c2n_set`) = `start.req` (fork wires);
`q` = `env_c0` (uenv0, `bd_c2n`) = `out0.ack`; `o` = `out0.req`; `rr` = `res_req`
(= `urdly`, a 16-element `bd_delay`, applied to `o`).

## Results

* §1 **Lap contract** (`Ring`: RigToken's ring hypotheses, i.e. the step forms `M1`/`M0` that
  `RigToken.set_move`/`c2n_move` derive from the real INITs under H_LUT_FIFO, H_FB_FIRST,
  H_RST_ONE_FALL, H_WIRE_FIFO). Lap `k ≥ 1` begins at start's `k`-th re-offer (the reset level
  is offer 0).
  - `lap_offer`: at the `k`-th re-offer, `out0.ack` has risen exactly `k` times (results
    `0..k-1` consumed) and fallen exactly `k-1` times, and is HIGH during the offer: result
    `k-1`'s handshake is still open (the overlap C found).
  - `lap_close`: at the `k`-th fall of `out0.ack` (result `k-1` closed) the env is exactly in
    its release state (`env_c = 1`, `env_c0 = 0`, equal transition counts), offer `k` has
    already been made, and `start.req` has been high since that offer.
  - `lap_result`: result `k` is consumed (the `k+1`-th rise of `out0.ack`) only after offer `k`.
* §2 **H_SINK_SI** (C's `Sink.wire` for the rig's two sinks) holds, in read-map form:
  `sink_si_upto` (causal), `sink_si`, `out0_sink_si` (uenv0's `a` half behind `urdly`),
  `out0_sink_si_cells` (the same from the real `bd_c2n` INIT via `c2n_move`), `pend_sink_si`
  (`upsnk`). It needs the producer's four-phase send rule and a FIFO (monotone) read map.
  `CXS.nonfifo_breaks_sink`: with every other hypothesis kept and a non-monotone read map
  (a delay line that shows an older `out0_req` after a newer one), `Sink.wire` fails.
* §3 Witness `W.laps_nonvacuous`: a 6-tick periodic env run meeting `Ring` and every
  hypothesis of `sink_si` with 3 re-offers and 3 closes by tick 20; `lap_offer` and
  `lap_close` apply at lap 2.
* §4 In C's vocabulary (imports C's `CapstoneRig` through `RigSrc`; nothing of C edited):
  - `sink_C_of_wire`: H_SINK_SI gives C's `Ops.Gcd.Sink` on `shiftRun T`;
    `rig_out0_sink`: `out0`'s sink model (`K.sink 416`) follows from every OTHER operator's
    `CellR` plus uenv0/urdly's read-map move, the producer's send rule being read off C's
    protocol on frozen runs (no circularity).
  - `LapInv` (the per-lap invariant, in `gcd_rig_first`'s own form: `CellR` on
    `shiftRun T ch`); `gcd_rig_lap`; **`gcd_rig_every`**: `LapInv` at release and after every
    `out0` close ⇒ every `out0` offer and every latched value is `gcd a b`.
  - `lapinv_of_parts`, `lapinv_at_close`: at a close, the sources and `out0`'s sink are
    discharged; only the kernel residual `H_KER_REARM` remains.
  - **`lapinv_pend_idle`, `lapinv_fails_pend_fast`, `lap_cut_fails`**: `LapInv` at a close
    forces `p_end_ack = 0`; under fixed fork/`upsnk` delays it FAILS at the close of every lap
    whose `p_end` loop (`dF + dP`) is shorter than the gap from that lap's re-offer to `out0`'s
    close (H_PEND_FAST). `pend_fast_nonvacuous`.

NOT covered: a non-vacuity witness for `gcd_rig_every` (a gcd_hw run with ≥ 2 invocations
meeting `LapInv` at its cuts); `H_KER_REARM`; a re-entrant cut (channels allowed mid return
phase) that would survive H_PEND_FAST; the joint induction merging `rig_out0_sink` with
`RigSrc.rig_cellR`.

Core Lean only (no Mathlib).
-/

namespace Formal.Cells.RigLaps
open Formal.Cells.RigToken
open Formal.Net.Handshake (cnt riseB fallB)

/-! ## 0. Counting helpers -/

theorem N_chg {x : Nat → Bool} {T0 t : Nat} (ht : T0 ≤ t) (h : x (t + 1) ≠ x t) :
    N x T0 (t + 1) = N x T0 t + 1 := by
  rw [N_succ]
  have : chg x t = true := by
    unfold chg; cases h1 : x t <;> cases h2 : x (t + 1) <;> simp_all
  simp [ht, this]

theorem N_stay {x : Nat → Bool} {T0 t : Nat} (h : x (t + 1) = x t) :
    N x T0 (t + 1) = N x T0 t := by
  rw [N_succ]
  have : chg x t = false := by unfold chg; rw [h]; simp
  simp [this]

theorem R_succ (x : Nat → Bool) (T0 t : Nat) :
    R x T0 (t + 1) = R x T0 t + (if T0 ≤ t ∧ riseB x t = true then 1 else 0) := rfl

theorem R_at (x : Nat → Bool) {T0 t : Nat} (ht : T0 ≤ t) :
    R x T0 t = if x T0 then N x T0 t / 2 else (N x T0 t + 1) / 2 := by
  have := R_of_N x T0 (t - T0)
  rwa [show T0 + (t - T0) = t by omega] at this

/-- If at least `j+1` rises happened in `[T0, t)`, the `j`-th one (0-based) is at some `r`. -/
theorem R_ge (x : Nat → Bool) (T0 : Nat) :
    ∀ t j, j + 1 ≤ R x T0 t → ∃ r, T0 ≤ r ∧ r < t ∧ riseB x r = true ∧ R x T0 r = j
  | 0, j, h => by simp [R] at h
  | t + 1, j, h => by
    rw [R_succ] at h
    by_cases hj : j + 1 ≤ R x T0 t
    · obtain ⟨r, h1, h2, h3, h4⟩ := R_ge x T0 t j hj
      exact ⟨r, h1, by omega, h3, h4⟩
    · by_cases hc : T0 ≤ t ∧ riseB x t = true
      · simp only [hc, and_self, ite_true] at h
        exact ⟨t, hc.1, by omega, hc.2, by omega⟩
      · simp only [hc, ite_false] at h; omega

/-- Falls of `x` at steps in `[T0, t)` (= rises of `¬x`). -/
def Fl (x : Nat → Bool) (T0 : Nat) : Nat → Nat := R (fun s => !x s) T0

theorem N_not (x : Nat → Bool) (T0 : Nat) : ∀ t, N (fun s => !x s) T0 t = N x T0 t
  | 0 => rfl
  | t + 1 => by
    rw [N_succ, N_succ, N_not x T0 t]
    have : chg (fun s => !x s) t = chg x t := by
      unfold chg
      show ((!x t) != (!x (t + 1))) = (x t != x (t + 1))
      cases x t <;> cases x (t + 1) <;> rfl
    rw [this]

theorem Fl_at (x : Nat → Bool) {T0 t : Nat} (ht : T0 ≤ t) :
    Fl x T0 t = if x T0 then (N x T0 t + 1) / 2 else N x T0 t / 2 := by
  unfold Fl
  rw [R_at (fun s => !x s) ht, N_not]
  cases x T0 <;> rfl

theorem riseB_not (x : Nat → Bool) (t : Nat) : riseB (fun s => !x s) t = fallB x t := by
  show (!!x t && !x (t + 1)) = (x t && !x (t + 1))
  cases x t <;> cases x (t + 1) <;> rfl

/-! ## 1. The lap contract -/

/-- RigToken's ring hypotheses (`ring_alternation`), bundled. `e` = `env_c` = `start.req`,
`q` = `env_c0` = `out0.ack`. Quiet start on `[Tq, T0]` at the reset values; from `T0` on
`e` moves only to what uenv1's pin shows of `q` (`M1`, the `a` half of the real
`bd_c2n_set`, `RigToken.set_move`) and `q` only to the complement of what uenv0's pin shows
of `e` (`M0`, the `b` half of the real `bd_c2n`, `RigToken.c2n_move`), both read through
monotone causal maps (H_WIRE_FIFO, H_LUT_FIFO, H_FB_FIRST, H_RST_ONE_FALL behind them).
The kernel (`in_ack`, `res_req`) is arbitrary. -/
structure Ring (e q : Nat → Bool) (T0 Tq : Nat) (φ1 φ0 : Nat → Nat) : Prop where
  H_INIT_E : ∀ s, Tq ≤ s → s ≤ T0 → e s = true
  H_INIT_Q : ∀ s, Tq ≤ s → s ≤ T0 → q s = false
  hφ1m : ∀ t t', T0 ≤ t → t ≤ t' → φ1 t ≤ φ1 t'
  hφ1c : ∀ t, T0 ≤ t → φ1 t ≤ t
  hφ1q : ∀ t, T0 ≤ t → Tq ≤ φ1 t
  hφ0m : ∀ t t', T0 ≤ t → t ≤ t' → φ0 t ≤ φ0 t'
  hφ0c : ∀ t, T0 ≤ t → φ0 t ≤ t
  hφ0q : ∀ t, T0 ≤ t → Tq ≤ φ0 t
  M1 : ∀ t, T0 ≤ t → e (t + 1) ≠ e t → q (φ1 t) = e (t + 1)
  M0 : ∀ t, T0 ≤ t → q (t + 1) ≠ q t → e (φ0 t) = !q (t + 1)

section lap
variable {e q : Nat → Bool} {T0 Tq : Nat} {φ1 φ0 : Nat → Nat}

theorem Ring.tq (H : Ring e q T0 Tq φ1 φ0) : Tq ≤ T0 := by
  have := H.hφ1q T0 (Nat.le_refl _); have := H.hφ1c T0 (Nat.le_refl _); omega

theorem Ring.eT (H : Ring e q T0 Tq φ1 φ0) : e T0 = true := H.H_INIT_E T0 H.tq (Nat.le_refl _)
theorem Ring.qT (H : Ring e q T0 Tq φ1 φ0) : q T0 = false := H.H_INIT_Q T0 H.tq (Nat.le_refl _)

/-- The per-cell counts (RigToken's `cell_count` on each cell) and the alternation. -/
theorem Ring.bounds (H : Ring e q T0 Tq φ1 φ0) :
    (∀ t, T0 ≤ t → N e T0 (t + 1) ≤ N q T0 (φ1 t) + 1) ∧
    (∀ t, T0 ≤ t → N q T0 (t + 1) ≤ N e T0 (φ0 t)) ∧
    (∀ t, N q T0 t ≤ N e T0 t ∧ N e T0 t ≤ N q T0 t + 1) := by
  have eT := H.eT
  have qT := H.qT
  have C1 := cell_count e q T0 Tq φ1 false 1 H.hφ1m H.hφ1c H.hφ1q
    (fun s h1 h2 => by rw [H.H_INIT_Q s h1 h2, qT])
    (fun t ht hne => by rw [Bool.xor_false]; exact H.M1 t ht hne)
    (by rw [qT, eT]; rfl)
  have C0 := cell_count q e T0 Tq φ0 true 0 H.hφ0m H.hφ0c H.hφ0q
    (fun s h1 h2 => by rw [H.H_INIT_E s h1 h2, eT])
    (fun t ht hne => by rw [H.M0 t ht hne]; cases q (t + 1) <;> rfl)
    (by rw [qT, eT]; rfl)
  refine ⟨C1, fun t ht => by have := C0 t ht; omega, ?_⟩
  exact ring_alternation e q T0 Tq φ1 φ0 H.H_INIT_E H.H_INIT_Q H.hφ1m H.hφ1c H.hφ1q
    H.hφ0m H.hφ0c H.hφ0q H.M1 H.M0

theorem Ring.par_e (H : Ring e q T0 Tq φ1 φ0) :
    ∀ t, T0 ≤ t → e t = !decide (N e T0 t % 2 = 1) := by
  intro t ht
  have := par e T0 Tq (fun s h1 h2 => by rw [H.H_INIT_E s h1 h2, H.eT]) t (by have := H.tq; omega)
  rw [this, H.eT]; cases decide (N e T0 t % 2 = 1) <;> rfl

theorem Ring.par_q (H : Ring e q T0 Tq φ1 φ0) :
    ∀ t, T0 ≤ t → q t = decide (N q T0 t % 2 = 1) := by
  intro t ht
  have := par q T0 Tq (fun s h1 h2 => by rw [H.H_INIT_Q s h1 h2, H.qT]) t (by have := H.tq; omega)
  rw [this, H.qT]; cases decide (N q T0 t % 2 = 1) <;> rfl

theorem odd_of_true {n : Nat} {b : Bool} (h : b = decide (n % 2 = 1)) (hb : b = true) :
    n % 2 = 1 := by
  rw [hb] at h; exact of_decide_eq_true h.symm

theorem even_of_false {n : Nat} {b : Bool} (h : b = decide (n % 2 = 1)) (hb : b = false) :
    n % 2 = 0 := by
  rw [hb] at h
  have : ¬ (n % 2 = 1) := of_decide_eq_false h.symm
  omega

theorem dec_odd {n : Nat} (h : n % 2 = 1) : decide (n % 2 = 1) = true := decide_eq_true h
theorem dec_even {n : Nat} (h : n % 2 = 0) : decide (n % 2 = 1) = false :=
  decide_eq_false (by omega)

theorem rise_vals {x : Nat → Bool} {t : Nat} (h : riseB x t = true) :
    x t = false ∧ x (t + 1) = true := by
  unfold riseB at h; cases h1 : x t <;> cases h2 : x (t + 1) <;> simp_all

theorem fall_vals {x : Nat → Bool} {t : Nat} (h : fallB x t = true) :
    x t = true ∧ x (t + 1) = false := by
  unfold fallB at h; cases h1 : x t <;> cases h2 : x (t + 1) <;> simp_all

/-- **Lap `k`'s start offer (`k ≥ 1`).** At the `k`-th rise of `start.req` after release
(`R e T0 r + 1 = k`; the reset level is offer 0), at step `r → r+1`:
* `out0.ack` is high at `r` and at `r + 1`: result `k-1`'s handshake is still OPEN when lap
  `k` is offered (C's `rearm_fails_at_reoffer` is this fact at one instant);
* `out0.ack` has risen exactly `k` times in `[T0, r)` (results `0..k-1` consumed, none more,
  also at `r + 1`) and fallen exactly `k - 1` times;
* the env's transition counts are fixed by `k`: `N e = 2k-1 → 2k`, `N q = 2k-1`. -/
theorem lap_offer (H : Ring e q T0 Tq φ1 φ0) (k r : Nat) (hr : T0 ≤ r)
    (hrise : riseB e r = true) (hk : R e T0 r + 1 = k) :
    q r = true ∧ q (r + 1) = true ∧
    N e T0 r + 1 = 2 * k ∧ N e T0 (r + 1) = 2 * k ∧
    N q T0 r + 1 = 2 * k ∧ N q T0 (r + 1) + 1 = 2 * k ∧
    R q T0 r = k ∧ R q T0 (r + 1) = k ∧ Fl q T0 r + 1 = k ∧ Fl q T0 (r + 1) + 1 = k := by
  obtain ⟨C1, C0, A⟩ := H.bounds
  obtain ⟨e0, e1⟩ := rise_vals hrise
  have hodd : N e T0 r % 2 = 1 := by
    have hp := H.par_e r hr
    rw [e0] at hp
    by_cases hc : N e T0 r % 2 = 1
    · exact hc
    · rw [decide_eq_false hc] at hp; exact absurd hp (by decide)
  have hR := R_at e hr
  rw [H.eT] at hR
  simp only [ite_true] at hR
  have hne : N e T0 r + 1 = 2 * k := by omega
  have hne1 : N e T0 (r + 1) = N e T0 r + 1 := N_chg hr (by rw [e0, e1]; decide)
  have c1 := C1 r hr
  have m1 := N_mono q T0 (H.hφ1c r hr)
  have a1 := (A r).1
  have c0 := C0 r hr
  have m0 := N_mono e T0 (H.hφ0c r hr)
  have mq := N_mono q T0 (show r ≤ r + 1 by omega)
  have nq : N q T0 r + 1 = 2 * k := by omega
  have nq1 : N q T0 (r + 1) + 1 = 2 * k := by omega
  have qr : q r = true := by rw [H.par_q r hr]; exact dec_odd (by omega)
  have qr1 : q (r + 1) = true := by rw [H.par_q (r + 1) (by omega)]; exact dec_odd (by omega)
  have Rq := R_at q hr
  have Rq1 := R_at q (show T0 ≤ r + 1 by omega)
  have Fq := Fl_at q hr
  have Fq1 := Fl_at q (show T0 ≤ r + 1 by omega)
  rw [H.qT] at Rq Rq1 Fq Fq1
  simp only [Bool.false_eq_true, ite_false] at Rq Rq1 Fq Fq1
  refine ⟨qr, qr1, hne, by omega, nq, nq1, by omega, by omega, by omega, by omega⟩

/-- The state half of `lap_close` (everything but the offer witness). -/
theorem lap_close_state (H : Ring e q T0 Tq φ1 φ0) (k s : Nat) (hs : T0 ≤ s)
    (hfall : fallB q s = true) (hk : Fl q T0 s + 1 = k) :
    e s = true ∧ e (s + 1) = true ∧ q (s + 1) = false ∧
    N e T0 (s + 1) = 2 * k ∧ N q T0 (s + 1) = 2 * k ∧
    R e T0 (s + 1) = k ∧ R q T0 (s + 1) = k ∧ Fl q T0 (s + 1) = k := by
  obtain ⟨C1, C0, A⟩ := H.bounds
  obtain ⟨q0, q1⟩ := fall_vals hfall
  have hodd : N q T0 s % 2 = 1 := odd_of_true (H.par_q s hs) q0
  have nq : N q T0 s + 1 = 2 * k := by
    have hF := Fl_at q hs
    rw [H.qT] at hF
    simp only [Bool.false_eq_true, ite_false] at hF
    omega
  have nq1 : N q T0 (s + 1) = 2 * k := by
    rw [N_chg hs (by rw [q0, q1]; decide)]; exact nq
  have ne : N e T0 s = 2 * k := by
    have c0 := C0 s hs
    have m0 := N_mono e T0 (H.hφ0c s hs)
    have a1 := (A s).2
    omega
  have ne1 : N e T0 (s + 1) = 2 * k := by
    have c1 := C1 s hs
    have m1 := N_mono q T0 (H.hφ1c s hs)
    have me := N_mono e T0 (show s ≤ s + 1 by omega)
    omega
  have ev : (2 * k) % 2 = 0 := by omega
  have half : (2 * k) / 2 = k := by omega
  have half1 : (2 * k + 1) / 2 = k := by omega
  have es : e s = true := by rw [H.par_e s hs, ne, dec_even ev]; rfl
  have es1 : e (s + 1) = true := by rw [H.par_e (s + 1) (by omega), ne1, dec_even ev]; rfl
  have Re1 := R_at e (show T0 ≤ s + 1 by omega)
  have Rq1 := R_at q (show T0 ≤ s + 1 by omega)
  have Fq1 := Fl_at q (show T0 ≤ s + 1 by omega)
  rw [H.eT, ne1, half] at Re1
  rw [H.qT, nq1, half1] at Rq1
  rw [H.qT, nq1, half] at Fq1
  exact ⟨es, es1, q1, ne1, nq1, Re1, Rq1, Fq1⟩

/-- **Lap `k`'s close: the env is back in its release state.** At the `k`-th fall of
`out0.ack` (`Fl q T0 s + 1 = k`: result `k-1`'s handshake closes at `s → s+1`):
* `env_c = 1` at `s` and `s+1`, `env_c0 = 0` at `s+1`, and the transition counts are equal
  (`2k` each): exactly the state at release (`e T0 = 1`, `q T0 = 0`, counts `0`);
* `start.req` and `out0.ack` have each risen exactly `k` times in `[T0, s+1)`, and
  `out0.ack` has fallen `k` times;
* the `k`-th re-offer happened at some `r < s` (with `out0.ack` high there), and `start.req`
  has stayed high from `r + 1` through `s + 1`: lap `k` is on offer, as the reset level
  was at release. -/
theorem lap_close (H : Ring e q T0 Tq φ1 φ0) (k s : Nat) (hs : T0 ≤ s)
    (hfall : fallB q s = true) (hk : Fl q T0 s + 1 = k) :
    e s = true ∧ e (s + 1) = true ∧ q (s + 1) = false ∧
    N e T0 (s + 1) = 2 * k ∧ N q T0 (s + 1) = 2 * k ∧
    R e T0 (s + 1) = k ∧ R q T0 (s + 1) = k ∧ Fl q T0 (s + 1) = k ∧
    ∃ r, T0 ≤ r ∧ r < s ∧ riseB e r = true ∧ R e T0 r + 1 = k ∧ q r = true ∧
      ∀ t, r < t → t ≤ s + 1 → e t = true := by
  obtain ⟨es, es1, q1, ne1, nq1, Re1, Rq1, Fq1⟩ := lap_close_state H k s hs hfall hk
  refine ⟨es, es1, q1, ne1, nq1, Re1, Rq1, Fq1, ?_⟩
  have hk1 : 1 ≤ k := by omega
  obtain ⟨r, hr0, hrs, hrr, hRr⟩ := R_ge e T0 (s + 1) (k - 1) (by rw [Re1]; omega)
  obtain ⟨Lq, _, _, Lne1, _⟩ := lap_offer H k r hr0 hrr (by omega)
  have hrs' : r < s := by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hrs) with h | h
    · exact h
    · rw [h] at hrr; rw [(rise_vals hrr).1] at es; exact absurd es (by decide)
  refine ⟨r, hr0, hrs', hrr, by omega, Lq, ?_⟩
  intro t h1 h2
  have u1 := N_mono e T0 (show r + 1 ≤ t by omega)
  have u2 := N_mono e T0 h2
  have ht : N e T0 t = 2 * k := by omega
  rw [H.par_e t (by omega), ht, dec_even (by omega)]; rfl

/-- **Result `k` is consumed only after lap `k` was offered.** At the `(k+1)`-th rise of
`out0.ack` (`R q T0 u = k`), `start.req` has already made `2k+1` transitions; for `k ≥ 1` its
`k`-th re-offer lies strictly before. -/
theorem lap_result (H : Ring e q T0 Tq φ1 φ0) (k u : Nat) (hu : T0 ≤ u)
    (hrise : riseB q u = true) (hk : R q T0 u = k) :
    2 * k + 1 ≤ N e T0 u ∧
    (k = 0 ∨ ∃ r, T0 ≤ r ∧ r < u ∧ riseB e r = true ∧ R e T0 r + 1 = k) := by
  obtain ⟨_, C0, _⟩ := H.bounds
  obtain ⟨q0, q1⟩ := rise_vals hrise
  have hev : N q T0 u % 2 = 0 := even_of_false (H.par_q u hu) q0
  have hR := R_at q hu
  rw [H.qT] at hR
  simp only [Bool.false_eq_true, ite_false] at hR
  have nq1 : N q T0 (u + 1) = N q T0 u + 1 := N_chg hu (by rw [q0, q1]; decide)
  have c0 := C0 u hu
  have m0 := N_mono e T0 (H.hφ0c u hu)
  have hne : 2 * k + 1 ≤ N e T0 u := by omega
  refine ⟨hne, ?_⟩
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · exact Or.inl h0
  · right
    have Re := R_at e hu
    rw [H.eT] at Re
    simp only [ite_true] at Re
    obtain ⟨r, h1, h2, h3, h4⟩ := R_ge e T0 u (k - 1) (by omega)
    exact ⟨r, h1, h2, h3, by omega⟩

end lap

/-! ## 2. H_SINK_SI: C's `Sink.wire` for the rig's sinks, in read-map form -/

/-- Freeze a trace at `T`. -/
def fz (T : Nat) (x : Nat → Bool) : Nat → Bool := fun s => x (min s T)

/-- **H_SINK_SI, causal form.** A sink whose acknowledge moves only to a value its pin shows of
the request (`H_MOVE`, read through a monotone causal map `ρ` that does not reach before
`T0`), on a channel idle at `T0`, whose sender obeys the four-phase send rule (`req` moves only
to `¬ack`) at the steps before `T`. Then at every step `t ∈ [T0, T]` at which the acknowledge
moves, it moves to `req t`: C's `Sink.wire`. -/
theorem sink_si_upto (req ack : Nat → Bool) (T0 T : Nat) (ρ : Nat → Nat)
    (h0r : req T0 = false) (h0a : ack T0 = false)
    (hρm : ∀ t t', T0 ≤ t → t ≤ t' → ρ t ≤ ρ t') (hρc : ∀ t, T0 ≤ t → ρ t ≤ t)
    (hρ0 : ∀ t, T0 ≤ t → T0 ≤ ρ t)
    (H_MOVE : ∀ t, T0 ≤ t → ack (t + 1) ≠ ack t → req (ρ t) = ack (t + 1))
    (H_SEND : ∀ s, T0 ≤ s → s < T → req (s + 1) ≠ req s → req (s + 1) = !ack s) :
    ∀ t, T0 ≤ t → t ≤ T → ack (t + 1) ≠ ack t → ack (t + 1) = req t := by
  intro t ht htT hmv
  have r0 : fz T req T0 = false := by
    show req (min T0 T) = false; rw [Nat.min_eq_left (by omega)]; exact h0r
  have a0 : fz (T + 1) ack T0 = false := by
    show ack (min T0 (T + 1)) = false; rw [Nat.min_eq_left (by omega)]; exact h0a
  have CA := cell_count (fz T req) (fz (T + 1) ack) T0 T0 id true 1
    (fun _ _ _ h => h) (fun _ _ => Nat.le_refl _) (fun _ h => h)
    (fun s h1 h2 => by rw [show s = T0 by omega])
    (fun s hs hne => by
      by_cases hsT : s < T
      · have e1 : fz T req (s + 1) = req (s + 1) := by
          show req (min (s + 1) T) = _; rw [Nat.min_eq_left (by omega)]
        have e2 : fz T req s = req s := by
          show req (min s T) = _; rw [Nat.min_eq_left (by omega)]
        have e3 : fz (T + 1) ack s = ack s := by
          show ack (min s (T + 1)) = _; rw [Nat.min_eq_left (by omega)]
        rw [e1, e2] at hne
        show xor (fz (T + 1) ack s) true = fz T req (s + 1)
        rw [e3, e1, H_SEND s hs hsT hne]; cases ack s <;> rfl
      · exfalso; apply hne
        show req (min (s + 1) T) = req (min s T)
        rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)])
    (by rw [a0, r0]; rfl)
  have CB := cell_count (fz (T + 1) ack) (fz T req) T0 T0 ρ false 0 hρm hρc hρ0
    (fun s h1 h2 => by rw [show s = T0 by omega])
    (fun s hs hne => by
      by_cases hsT : s ≤ T
      · have e1 : fz (T + 1) ack (s + 1) = ack (s + 1) := by
          show ack (min (s + 1) (T + 1)) = _; rw [Nat.min_eq_left (by omega)]
        have e2 : fz (T + 1) ack s = ack s := by
          show ack (min s (T + 1)) = _; rw [Nat.min_eq_left (by omega)]
        have e3 : fz T req (ρ s) = req (ρ s) := by
          show req (min (ρ s) T) = _; rw [Nat.min_eq_left (by have := hρc s hs; omega)]
        rw [e1, e2] at hne
        rw [Bool.xor_false, e3, e1]; exact H_MOVE s hs hne
      · exfalso; apply hne
        show ack (min (s + 1) (T + 1)) = ack (min s (T + 1))
        rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)])
    (by rw [a0, r0]; rfl)
  have e1 : fz (T + 1) ack (t + 1) = ack (t + 1) := by
    show ack (min (t + 1) (T + 1)) = _; rw [Nat.min_eq_left (by omega)]
  have e2 : fz (T + 1) ack t = ack t := by
    show ack (min t (T + 1)) = _; rw [Nat.min_eq_left (by omega)]
  have e3 : fz T req t = req t := by
    show req (min t T) = _; rw [Nat.min_eq_left (by omega)]
  have hm : fz (T + 1) ack (t + 1) ≠ fz (T + 1) ack t := by rw [e1, e2]; exact hmv
  have n1 := N_chg ht hm
  have cb := CB t ht
  have mr := N_mono (fz T req) T0 (hρc t ht)
  have up : N (fz T req) T0 t ≤ N (fz (T + 1) ack) T0 t + 1 := by
    rcases Nat.lt_or_eq_of_le ht with h | h
    · have ca : N (fz T req) T0 (t - 1 + 1) ≤ N (fz (T + 1) ack) T0 (t - 1) + 1 :=
        CA (t - 1) (by omega)
      rw [show t - 1 + 1 = t by omega] at ca
      have := N_mono (fz (T + 1) ack) T0 (show t - 1 ≤ t by omega)
      omega
    · rw [← h, N_pre _ T0 T0 (Nat.le_refl _)]; omega
  have eqN : N (fz T req) T0 t = N (fz (T + 1) ack) T0 (t + 1) := by omega
  have pr := par (fz T req) T0 T0 (fun s h1 h2 => by rw [show s = T0 by omega]) t ht
  have pa := par (fz (T + 1) ack) T0 T0 (fun s h1 h2 => by rw [show s = T0 by omega]) (t + 1)
    (by omega)
  rw [r0, Bool.false_xor] at pr
  rw [a0, Bool.false_xor] at pa
  rw [← e1, ← e3, pr, pa, eqN]

/-- **H_SINK_SI** (all steps): the same with the send rule at every step from `T0`. -/
theorem sink_si (req ack : Nat → Bool) (T0 : Nat) (ρ : Nat → Nat)
    (h0r : req T0 = false) (h0a : ack T0 = false)
    (hρm : ∀ t t', T0 ≤ t → t ≤ t' → ρ t ≤ ρ t') (hρc : ∀ t, T0 ≤ t → ρ t ≤ t)
    (hρ0 : ∀ t, T0 ≤ t → T0 ≤ ρ t)
    (H_MOVE : ∀ t, T0 ≤ t → ack (t + 1) ≠ ack t → req (ρ t) = ack (t + 1))
    (H_SEND : ∀ s, T0 ≤ s → req (s + 1) ≠ req s → req (s + 1) = !ack s) :
    ∀ t, T0 ≤ t → ack (t + 1) ≠ ack t → ack (t + 1) = req t := fun t ht =>
  sink_si_upto req ack T0 t ρ h0r h0a hρm hρc hρ0 H_MOVE (fun s hs _ => H_SEND s hs) t ht
    (Nat.le_refl _)

/-- **H_SINK_SI for `out0`'s sink (uenv0 behind `urdly`).** `q` = `env_c0` = `out0.ack`,
`o` = `out0.req`, `rr` = `res_req` at uenv0's `a` pin.
* `H_UENV0_A`: uenv0 moves only to what its `a` pin shows at its read instant `σ (t+1)`
  (`RigToken.c2n_move`'s first conjunct, from the real `bd_c2n` INIT);
* `H_URDLY_FIFO`: `urdly` (+ route) shows `out0_req` as it was at `δ s`, `δ` monotone;
* the composed read `δ (σ (t+1))` lies in `[T0, t]`;
* `H_SEND`: `out0`'s producer moves `out0_req` only to `¬out0_ack` (C's `SendStep`);
* `out0` idle at `T0`.
Then `out0.ack` moves only to `out0.req` of the previous tick: C's `Sink.wire`. -/
theorem out0_sink_si (o q rr : Nat → Bool) (T0 : Nat) (σ δ : Nat → Nat)
    (h0o : o T0 = false) (h0q : q T0 = false)
    (H_UENV0_A : ∀ t, T0 ≤ t → q (t + 1) ≠ q t → rr (σ (t + 1)) = q (t + 1))
    (H_URDLY_FIFO : ∀ s, rr s = o (δ s))
    (hσm : ∀ t t', t ≤ t' → σ t ≤ σ t') (hδm : ∀ s s', s ≤ s' → δ s ≤ δ s')
    (hrd : ∀ t, T0 ≤ t → T0 ≤ δ (σ (t + 1)) ∧ δ (σ (t + 1)) ≤ t)
    (H_SEND : ∀ s, T0 ≤ s → o (s + 1) ≠ o s → o (s + 1) = !q s) :
    ∀ t, T0 ≤ t → q (t + 1) ≠ q t → q (t + 1) = o t :=
  sink_si o q T0 (fun t => δ (σ (t + 1))) h0o h0q
    (fun t t' _ h => hδm _ _ (hσm _ _ (by omega))) (fun t ht => (hrd t ht).2)
    (fun t ht => (hrd t ht).1)
    (fun t ht hne => by rw [← H_URDLY_FIFO]; exact H_UENV0_A t ht hne) H_SEND

open Formal.Cells.CElemTiming (exc) in
open Formal.Cells.ResetContract (I_c2n) in
/-- **H_SINK_SI for `out0`, from uenv0's real INIT.** The same as `out0_sink_si` with
`H_UENV0_A` derived by `RigToken.c2n_move` from H_LUT_FIFO (`F0`), H_RST_ONE_FALL and
H_FB_FIRST on uenv0 (`b0` = its `env_c` pin, `qp0` its feedback pin, `rst0` its rst pin). -/
theorem out0_sink_si_cells (o q rr b0 qp0 rst0 : Nat → Bool) (T0 Tr : Nat) (σ δ : Nat → Nat)
    (h0o : o T0 = false) (h0q : q T0 = false)
    (F0 : ∀ t, T0 ≤ t → q t = exc I_c2n (rr (σ t)) (b0 (σ t)) (qp0 (σ t)) (rst0 (σ t)))
    (hσm : ∀ t t', t ≤ t' → σ t ≤ σ t') (hσr : ∀ t, T0 ≤ t → Tr ≤ σ t)
    (H_RST0_ONE_FALL : ∀ s s', Tr ≤ s → s ≤ s' → rst0 s' = true → rst0 s = true)
    (H_FB_FIRST0 : ∀ t, T0 ≤ t → q (t + 1) ≠ q t → qp0 (σ (t + 1)) = q t)
    (H_URDLY_FIFO : ∀ s, rr s = o (δ s)) (hδm : ∀ s s', s ≤ s' → δ s ≤ δ s')
    (hrd : ∀ t, T0 ≤ t → T0 ≤ δ (σ (t + 1)) ∧ δ (σ (t + 1)) ≤ t)
    (H_SEND : ∀ s, T0 ≤ s → o (s + 1) ≠ o s → o (s + 1) = !q s) :
    ∀ t, T0 ≤ t → q (t + 1) ≠ q t → q (t + 1) = o t := by
  have m0 := c2n_move F0 hσm hσr H_RST0_ONE_FALL H_FB_FIRST0
  exact out0_sink_si o q rr T0 σ δ h0o h0q (fun t ht hne => (m0 t ht hne).1) H_URDLY_FIFO
    hσm hδm hrd H_SEND

/-- **H_SINK_SI for `p_end`'s sink (`upsnk = bd_delay #2`).** `pa` = `p_end_ack` shows
`p_end_req` (`pr`) as it was at `δ (t+1)` (H_UPSNK_FIFO, `δ` monotone, at least one tick,
not before `T0`); `p_end`'s producer obeys the send rule; `p_end` idle at `T0`. -/
theorem pend_sink_si (pr pa : Nat → Bool) (T0 : Nat) (δ : Nat → Nat)
    (h0r : pr T0 = false) (h0a : pa T0 = false)
    (H_UPSNK_FIFO : ∀ t, T0 ≤ t → pa (t + 1) = pr (δ (t + 1)))
    (hδm : ∀ s s', s ≤ s' → δ s ≤ δ s')
    (hrd : ∀ t, T0 ≤ t → T0 ≤ δ (t + 1) ∧ δ (t + 1) ≤ t)
    (H_SEND : ∀ s, T0 ≤ s → pr (s + 1) ≠ pr s → pr (s + 1) = !pa s) :
    ∀ t, T0 ≤ t → pa (t + 1) ≠ pa t → pa (t + 1) = pr t :=
  sink_si pr pa T0 (fun t => δ (t + 1)) h0r h0a
    (fun t t' _ h => hδm _ _ (by omega)) (fun t ht => (hrd t ht).2) (fun t ht => (hrd t ht).1)
    (fun t ht _ => (H_UPSNK_FIFO t ht).symm) H_SEND

/-! ### The FIFO read is needed (counter-run)

`o` = `out0.req`: `0 1 1 0 0 0 …`; `q` = `out0.ack`: `0 0 1 1 0 1 1 …`; read map `ρ` = id except
`ρ 4 = 2`. Every hypothesis of `sink_si` holds except monotonicity of `ρ` (`ρ 3 = 3 > ρ 4 = 2`:
the delay line shows the older `out0_req = 1` after it has shown the newer `0`), and the sink
acknowledges at 4 → 5 while `out0_req` is low: `Sink.wire` fails, and so does C's receive rule. -/
namespace CXS

def o (t : Nat) : Bool := decide (1 ≤ t ∧ t ≤ 2)
def q (t : Nat) : Bool := decide (t = 2 ∨ t = 3 ∨ 5 ≤ t)
def ρ (t : Nat) : Nat := if t = 4 then 2 else t

theorem small : ∀ t, t < 6 →
    (q (t + 1) ≠ q t → o (ρ t) = q (t + 1)) ∧ (o (t + 1) ≠ o t → o (t + 1) = !q t) := by
  decide

theorem big (t : Nat) (h : 6 ≤ t) : q (t + 1) = q t ∧ o (t + 1) = o t := by
  unfold q o
  constructor
  · rw [decide_eq_true (Or.inr (Or.inr (show 5 ≤ t + 1 by omega))),
      decide_eq_true (Or.inr (Or.inr (show 5 ≤ t by omega)))]
  · rw [decide_eq_false (by omega), decide_eq_false (by omega)]

theorem nonfifo_breaks_sink :
    o 0 = false ∧ q 0 = false ∧ (∀ t, 0 ≤ t → ρ t ≤ t) ∧ (∀ t, 0 ≤ t → 0 ≤ ρ t) ∧
    (∀ t, 0 ≤ t → q (t + 1) ≠ q t → o (ρ t) = q (t + 1)) ∧
    (∀ s, 0 ≤ s → o (s + 1) ≠ o s → o (s + 1) = !q s) ∧
    ¬ (∀ t t', 0 ≤ t → t ≤ t' → ρ t ≤ ρ t') ∧
    ¬ (∀ t, 0 ≤ t → q (t + 1) ≠ q t → q (t + 1) = o t) := by
  refine ⟨rfl, rfl, fun t _ => ?_, fun t _ => Nat.zero_le _, fun t _ hne => ?_, fun s _ hne => ?_,
    fun h => absurd (h 3 4 (Nat.zero_le _) (by decide)) (by decide),
    fun h => absurd (h 4 (Nat.zero_le _) (by decide)) (by decide)⟩
  · unfold ρ; split <;> omega
  · by_cases h : t < 6
    · exact (small t h).1 hne
    · exact absurd (big t (by omega)).1 hne
  · by_cases h : s < 6
    · exact (small s h).2 hne
    · exact absurd (big s (by omega)).2 hne

end CXS

/-! ## 3. Non-vacuity: a periodic env run with several laps

One lap per 6 ticks (`p t`): `e` = env_c, `q` = env_c0 = out0.ack, `o` = out0.req (seen at
uenv0 with zero delay), every read map `id`, `T0 = Tq = 0`.
Lap: `o↑` · `e↓` (in_ack high) · `q↑` · `o↓` · `e↑` (re-offer, `q` still high) · `q↓` (close). -/
namespace W

def eL : List Bool := [true, true, true, false, false, false, true]
def oL : List Bool := [false, false, true, true, true, false, false]
def qL : List Bool := [false, false, false, false, true, true, true]

def p (t : Nat) : Nat := if t = 0 then 0 else 1 + (t - 1) % 6
def nxt (i : Nat) : Nat := if i < 6 then i + 1 else 1

theorem p_lt (t : Nat) : p t < 7 := by
  unfold p; split <;> omega

theorem p_succ (t : Nat) : p (t + 1) = nxt (p t) := by
  unfold p nxt
  cases t with
  | zero => rfl
  | succ s =>
    simp only [show s + 1 + 1 ≠ 0 by omega, show s + 1 ≠ 0 by omega, ite_false]
    split <;> omega

def e (t : Nat) : Bool := eL.getD (p t) false
def o (t : Nat) : Bool := oL.getD (p t) false
def q (t : Nat) : Bool := qL.getD (p t) false

theorem tbl : ∀ i, i < 7 →
    (eL.getD (nxt i) false ≠ eL.getD i false → qL.getD i false = eL.getD (nxt i) false) ∧
    (qL.getD (nxt i) false ≠ qL.getD i false → eL.getD i false = !qL.getD (nxt i) false) ∧
    (qL.getD (nxt i) false ≠ qL.getD i false → oL.getD i false = qL.getD (nxt i) false) ∧
    (oL.getD (nxt i) false ≠ oL.getD i false → oL.getD (nxt i) false = !qL.getD i false) := by
  decide

theorem row (t : Nat) :
    (e (t + 1) ≠ e t → q t = e (t + 1)) ∧ (q (t + 1) ≠ q t → e t = !q (t + 1)) ∧
    (q (t + 1) ≠ q t → o t = q (t + 1)) ∧ (o (t + 1) ≠ o t → o (t + 1) = !q t) := by
  unfold e o q; rw [p_succ]; exact tbl _ (p_lt t)

theorem ring : Ring e q 0 0 id id := by
  have i0 : ∀ s, 0 ≤ s → s ≤ 0 → s = 0 := fun s _ h => by omega
  exact ⟨fun s h1 h2 => by rw [i0 s h1 h2]; rfl, fun s h1 h2 => by rw [i0 s h1 h2]; rfl,
    fun _ _ _ h => h, fun _ _ => Nat.le_refl _, fun _ _ => Nat.zero_le _,
    fun _ _ _ h => h, fun _ _ => Nat.le_refl _, fun _ _ => Nat.zero_le _,
    fun t _ h => (row t).1 h, fun t _ h => (row t).2.1 h⟩

/-- **Non-vacuity of §1 and §2 with several laps.** The run meets `Ring` and every hypothesis
of `sink_si` (on `out0`: `ρ = id`); `start` is re-offered at 5, 11, 17 and `out0` closes at
6, 12, 18 (3 laps by tick 20); lap 2's offer (step 11) and close (step 12) meet the premises
of `lap_offer` / `lap_close` with `k = 2`; and the sink conclusion holds. -/
theorem laps_nonvacuous :
    Ring e q 0 0 id id ∧
    (o 0 = false ∧ q 0 = false ∧
      (∀ t, 0 ≤ t → q (t + 1) ≠ q t → o (id t) = q (t + 1)) ∧
      (∀ s, 0 ≤ s → o (s + 1) ≠ o s → o (s + 1) = !q s)) ∧
    (riseB e 11 = true ∧ R e 0 11 + 1 = 2) ∧ (fallB q 12 = true ∧ Fl q 0 12 + 1 = 2) ∧
    R e 0 20 = 3 ∧ R q 0 20 = 3 ∧ Fl q 0 20 = 3 ∧
    (∀ t, 0 ≤ t → q (t + 1) ≠ q t → q (t + 1) = o t) := by
  have hm : ∀ t, 0 ≤ t → q (t + 1) ≠ q t → o (id t) = q (t + 1) := fun t _ h => (row t).2.2.1 h
  have hs : ∀ s, 0 ≤ s → o (s + 1) ≠ o s → o (s + 1) = !q s := fun s _ h => (row s).2.2.2 h
  refine ⟨ring, ⟨rfl, rfl, hm, hs⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    by decide, by decide, by decide, ?_⟩
  exact sink_si o q 0 id rfl rfl (fun _ _ _ h => h) (fun _ _ => Nat.le_refl _)
    (fun _ _ => Nat.zero_le _) hm hs

end W


/-! ## 4. In C's vocabulary (`Formal/Net/CapstoneRig.lean`): sinks, the per-lap cut, its failure -/

section C
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd

/-- **H_SINK_SI in C's form.** If a channel's acknowledge obeys `Sink.wire` from `T0` on
(`sink_si`, `out0_sink_si`, `pend_sink_si`) and is low at `T ≥ T0`, the channel seen from `T`
(C's `rtC (shf T)`, i.e. `shiftRun T`) meets C's `Ops.Gcd.Sink`. -/
theorem sink_C_of_wire (c : Chan) (T0 T : Nat) (hT : T0 ≤ T)
    (W : ∀ t, T0 ≤ t → c.ack (t + 1) ≠ c.ack t → c.ack (t + 1) = c.req t)
    (h0a : c.ack T = false) : Ops.Gcd.Sink (rtC (shf T) c) := by
  refine ⟨fun t hne => ?_, ?_⟩
  · have hne' : c.ack (t + T + 1) ≠ c.ack (t + T) := by
      have := hne; simp only [rtC, shf] at this
      rwa [show t + 1 + T = t + T + 1 by omega] at this
    show c.ack (t + 1 + T) = c.req (t + T)
    rw [show t + 1 + T = t + T + 1 by omega]
    exact W (t + T) (by omega) hne'
  · show c.ack (0 + T) = false
    rw [Nat.zero_add]; exact h0a

/-- C's `SendStep` is the send rule in the form used by `sink_si`. -/
theorem send_of_step {c : Chan} {s : Nat} (h : SendStep c s) :
    c.req (s + 1) ≠ c.req s → c.req (s + 1) = !c.ack s := by
  intro hne
  have := h hne
  revert hne this
  cases c.req s <;> cases c.req (s + 1) <;> cases c.ack s <;> simp

/-- Sink operators. -/
def isSinkK {n : Nat} : K n → Bool
  | .sink _ => true
  | _ => false

theorem out0_prod_nsink : isSinkK (opAt (prodOf out0)) = false := by decide

/-- **H_SINK_SI discharged inside C's network (causal, no circularity).** If every operator
other than `out0`'s sink meets C's model without `Src.iz` (`CellR`), the buses are bundled, and
uenv0 (behind `urdly`) moves `out0.ack` only to a value of `out0.req` read through a monotone
causal map `ρ` (`out0_sink_si`'s composed read; reads at or after release), with `out0.ack`
low at release: then `out0`'s sink meets C's `Sink`. The producer's send rule is NOT
assumed: at each step it is read off C's `gcd_hw_protocol` on the run frozen there (strong
induction, as in `RigSrc.rig_cellR`). -/
theorem rig_out0_sink (a b : Nat) (ch : Fin NC → Chan) (ρ : Nat → Nat)
    (H_OTHER : ∀ o, opAt o ≠ K.sink out0 → CellR ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (h0a : (ch out0).ack 0 = false)
    (hρm : ∀ t t', t ≤ t' → ρ t ≤ ρ t') (hρc : ∀ t, ρ t ≤ t)
    (H_MOVE : ∀ t, (ch out0).ack (t + 1) ≠ (ch out0).ack t →
      (ch out0).req (ρ t) = (ch out0).ack (t + 1)) :
    Ops.Gcd.Sink (ch out0) := by
  have hpn : opAt (prodOf out0) ≠ K.sink out0 := by
    intro h; have := out0_prod_nsink; rw [h] at this; exact absurd this (by decide)
  have h0r : (ch out0).req 0 = false := by
    have hz : out0 ∈ (opAt (prodOf out0)).outsC := (net.prod_iff out0 (prodOf out0)).2 rfl
    have hc := cell_of_cellR _ out0_prod_nsrc (H_OTHER _ hpn)
    exact (cell_proto ch (srcV a b) _ hc (dist_of _ (ops_ok _))).initOut out0 hz
  have key : ∀ T, ∀ t, t < T → (ch out0).ack (t + 1) ≠ (ch out0).ack t →
      (ch out0).ack (t + 1) = (ch out0).req t := by
    intro T
    induction T with
    | zero => intro t ht; omega
    | succ T ih =>
      intro t ht
      rcases Nat.lt_or_ge t T with hlt | hge
      · exact ih t hlt
      have htT : t = T := by omega
      rw [htT]
      let chF : Fin NC → Chan := fun c => rtC (frz T) (ch c)
      have hCR : ∀ o, CellR chF (srcV a b) (opAt o) := by
        intro o
        by_cases hs : opAt o = K.sink out0
        · rw [hs]
          show Ops.Gcd.Sink (rtC (frz T) (ch out0))
          refine ⟨fun u hne => ?_, ?_⟩
          · by_cases hu : u + 1 ≤ T
            · have m1 : min (u + 1) T = u + 1 := by omega
              have m2 : min u T = u := by omega
              simp only [rtC, frz, m1, m2] at hne ⊢
              exact ih u (by omega) hne
            · have m1 : min (u + 1) T = T := by omega
              have m2 : min u T = T := by omega
              exact absurd (by simp only [rtC, frz, m1, m2]) hne
          · show (ch out0).ack (min 0 T) = false
            rw [Nat.min_eq_left (Nat.zero_le _)]; exact h0a
        · have hc := H_OTHER o hs
          cases hk : opAt o with
          | src z' w' d' =>
            rw [hk] at hc
            have S : SrcR (ch z') (srcV a b w') := hc
            show SrcR (rtC (frz T) (ch z')) (srcV a b w')
            exact ⟨rt_guard (frz_mono T) (ch z').req (fun s s' => (ch z').req s' = !(ch z').ack s)
              S.H_LUT_SI, fun u => S.dat _⟩
          | _ =>
            have hns : isSrcK (opAt o) = false := by rw [hk]; rfl
            have hc' := cell_rt (frz_mono T) (frz_zero T) (opAt o) (cell_of_cellR _ hns hc)
            rw [hk] at hc'
            exact cellR_of _ hc'
      have hC := preRun_cells a b chF hCR
      have hH : ∀ c, Held (preRun chF c) := fun c => held_pc (held_rt (frz_mono T) (H_BUNDLE c))
      have hp := gcd_hw_protocol a b (preRun chF) hC hH
      have hsend : ∀ s, 0 ≤ s → s < T → (ch out0).req (s + 1) ≠ (ch out0).req s →
          (ch out0).req (s + 1) = !(ch out0).ack s := by
        intro s _ hs hne
        have r := ((hp out0).2 (s + 1)).1
        have e1 : frz T (s + 1) = s + 1 := by simp only [frz]; omega
        have e2 : frz T s = s := by simp only [frz]; omega
        have r' : (ch out0).req (frz T (s + 1)) ≠ (ch out0).req (frz T s) →
            (ch out0).req (frz T s) = (ch out0).ack (frz T s) := r
        rw [e1, e2] at r'
        have := r' hne
        revert hne this
        cases (ch out0).req (s + 1) <;> cases (ch out0).req s <;> cases (ch out0).ack s <;> simp
      exact sink_si_upto (ch out0).req (ch out0).ack 0 T ρ h0r h0a
        (fun t t' _ h => hρm t t' h) (fun t _ => hρc t) (fun t _ => Nat.zero_le _)
        (fun t _ hne => H_MOVE t hne) hsend T (Nat.zero_le _) (Nat.le_refl _)
  exact ⟨fun t => key (t + 1) t (Nat.lt_succ_self t), h0a⟩

/-- The per-lap invariant, in exactly the form of `gcd_rig_first`'s hypothesis: C's cell
models without `Src.iz` hold for the run seen from `T` (`shiftRun T ch`), reset fields at `T`
included. -/
def LapInv (a b : Nat) (ch : Fin NC → Chan) (T : Nat) : Prop :=
  ∀ o : Fin NO, CellR (shiftRun T ch) (srcV a b) (opAt o)

theorem shiftRun_zero (ch : Fin NC → Chan) : shiftRun 0 ch = ch := rfl

theorem H_ENV_shift {ch : Fin NC → Chan} (h : H_ENV ch) (T : Nat) : H_ENV (shiftRun T ch) := by
  intro t ht
  have h2 : riseB (ch start).req (t + T) = true := by
    have := ht; simp only [riseB, shiftRun, rtC, shf] at this
    simp only [riseB]; rwa [show t + T + 1 = t + 1 + T by omega]
  exact h (t + T) h2

theorem proto_of_pc {c : Chan} (hp : Protocol (pc c)) (h0 : c.req 0 = false) : Protocol c :=
  ⟨⟨h0, hp.1.2⟩, fun t => ⟨(hp.2 (t + 1)).1, (hp.2 (t + 1)).2⟩⟩

/-- **One lap, from its cut.** If the per-lap invariant holds at `T` (and H_BUNDLE, H_ENV),
then the `out0` offer that follows `T` (the one numbered `cnt (riseB out0.req) T`) carries
`gcd a b`. This is C's `gcd_rig_first` applied to `shiftRun T ch`. -/
theorem gcd_rig_lap (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (T : Nat) (hL : LapInv a b ch T) (H_BUNDLE : ∀ c, Held (ch c)) (hE : H_ENV ch)
    (k r : Nat) (ho : OffAt (ch out0) k r) (hT : T ≤ r)
    (hc : cnt (riseB (ch out0).req) T = k) : (ch out0).dat (r + 1) = Nat.gcd a b := by
  have F := gcd_rig_first a b ha hb (shiftRun T ch) hL
    (fun c => held_rt (shf_mono T) (H_BUNDLE c)) (H_ENV_shift hE T)
  have e1 : r - T + T = r := by omega
  have ho' : OffAt (shiftRun T ch out0) 0 (r - T) := by
    refine ⟨?_, ?_⟩
    · show riseB (fun u => (ch out0).req (shf T u)) (r - T) = true
      simp only [riseB, shf, e1, show r - T + 1 + T = r + 1 by omega]; exact ho.1
    · show cnt (riseB (fun u => (ch out0).req (shf T u))) (r - T) = 0
      have := cnt_shf (ch out0).req T (r - T)
      rw [e1, ho.2, hc] at this; omega
  have := F.1 (r - T) ho'
  simpa [shiftRun, rtC, shf, show r - T + 1 + T = r + 1 by omega] using this

/-- **Every result, given the per-lap invariant at every cut.** Cuts: `T = 0` (release) and
`T = e + 1` after every close `e` of `out0` (`TokAt (ch out0) k e`), where `lap_close` puts the
environment exactly in its release state. If `LapInv` holds at all of them, every value
`out0` offers and every value it latches is `gcd a b`. -/
theorem gcd_rig_every (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (H_LAP0 : LapInv a b ch 0)
    (H_LAP : ∀ k e, TokAt (ch out0) k e → LapInv a b ch (e + 1))
    (H_BUNDLE : ∀ c, Held (ch c)) (hE : H_ENV ch) :
    (∀ k r, OffAt (ch out0) k r → (ch out0).dat (r + 1) = Nat.gcd a b) ∧
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) := by
  have H0 : ∀ o, CellR ch (srcV a b) (opAt o) := H_LAP0
  have hp := gcd_hw_protocol a b (preRun ch) (preRun_cells a b ch H0)
    (fun c => held_pc (H_BUNDLE c)) out0
  have P : Protocol (ch out0) := proto_of_pc hp (out0_req0 a b ch H0)
  have offers : ∀ k r, OffAt (ch out0) k r → (ch out0).dat (r + 1) = Nat.gcd a b := by
    intro k r ho
    have hf := off_falls P ho
    cases k with
    | zero => exact gcd_rig_lap a b ha hb ch 0 H_LAP0 H_BUNDLE hE 0 r ho (Nat.zero_le _) rfl
    | succ k =>
      obtain ⟨e, he, hfe, hce⟩ := cnt_ge (fallB (ch out0).ack) r k (by omega)
      obtain ⟨a1, a0⟩ := fall_vals hfe
      have hre : (ch out0).req e = false := by
        have h := (P.2 e).2 (by rw [a1, a0]; decide)
        rw [a1] at h; cases hq : (ch out0).req e <;> simp_all
      have hre1 : (ch out0).req (e + 1) = false := by
        by_cases hc : (ch out0).req (e + 1) = (ch out0).req e
        · rw [hc, hre]
        · have := (P.2 e).1 hc; rw [hre, a1] at this; exact absurd this (by decide)
      have hi := rise_inv P (e + 1)
      have hfe1 : cnt (fallB (ch out0).ack) (e + 1) = k + 1 := by rw [cnt_succ_of hfe, hce]
      have hin : inTx (ch out0) (e + 1) = false := by simp [inTx, hre1, a0]
      rw [hin, hfe1] at hi
      exact gcd_rig_lap a b ha hb ch (e + 1) (H_LAP k e ⟨hfe, hce⟩) H_BUNDLE hE (k + 1) r ho
        (by omega) (by simpa using hi)
  refine ⟨offers, fun k e ht => ?_⟩
  obtain ⟨r, _, ho⟩ := tok_off P ht
  rw [close_val P (H_BUNDLE out0) ht ho]
  exact offers k r ho

/-- **What the per-lap invariant asks, split.** `LapInv` at `T` follows from (i) the sources'
`SrcR` on the whole run (B's `RigSrc.rig_cellR` proves it; `SrcR` has no reset field, so it
shifts), (ii) `out0`'s sink seen from `T` (`sink_C_of_wire` + `out0_sink_si`), and (iii) the
residual KERNEL part `H_KER_REARM`: every other operator's cell model holds from `T`,
reset fields at `T` included. Only (iii) is open. -/
theorem lapinv_of_parts (a b : Nat) (ch : Fin NC → Chan) (T : Nat)
    (H_SRC : ∀ o, isSrcK (opAt o) = true → CellR ch (srcV a b) (opAt o))
    (H_OUT0_SINK : Ops.Gcd.Sink (shiftRun T ch out0))
    (H_KER_REARM : ∀ o, isSrcK (opAt o) = false → opAt o ≠ K.sink out0 →
      Cell (shiftRun T ch) (srcV a b) (opAt o)) :
    LapInv a b ch T := by
  intro o
  have hK : isSrcK (opAt o) = false → opAt o ≠ K.sink out0 →
      CellR (shiftRun T ch) (srcV a b) (opAt o) := fun h1 h2 =>
    cellR_of _ (H_KER_REARM o h1 h2)
  cases h : opAt o with
  | src z w d =>
    have S : SrcR (ch z) (srcV a b w) := by
      have := H_SRC o (by rw [h]; rfl); rw [h] at this; exact this
    show SrcR (rtC (shf T) (ch z)) (srcV a b w)
    refine ⟨fun t hne => ?_, fun t => S.dat _⟩
    have hne' : (ch z).req (t + T + 1) ≠ (ch z).req (t + T) := by
      have := hne; simp only [rtC, shf] at this
      rwa [show t + 1 + T = t + T + 1 by omega] at this
    show (ch z).req (t + 1 + T) = !(ch z).ack (t + T)
    rw [show t + 1 + T = t + T + 1 by omega]
    exact S.H_LUT_SI (t + T) hne'
  | sink i =>
    by_cases hi : i = out0
    · subst hi; exact H_OUT0_SINK
    · have := hK (by rw [h]; rfl) (by rw [h]; intro hh; injection hh with hh; exact hi hh)
      rw [h] at this; exact this
  | _ =>
    have := hK (by rw [h]; rfl) (by rw [h]; intro hh; cases hh)
    rw [h] at this; exact this

/-- **The env/sink part of the per-lap invariant at a close, discharged.** At the cut after a
close `e ≥ T0` of `out0`, `out0`'s sink seen from `e + 1` meets C's `Sink` (from
H_SINK_SI on the whole run), so `LapInv` there reduces to the sources (`rig_cellR`) and the
kernel residual `H_KER_REARM`. -/
theorem lapinv_at_close (a b : Nat) (ch : Fin NC → Chan) (T0 e : Nat) (he : T0 ≤ e)
    (hfall : fallB (ch out0).ack e = true)
    (H_SRC : ∀ o, isSrcK (opAt o) = true → CellR ch (srcV a b) (opAt o))
    (H_SINK_SI : ∀ t, T0 ≤ t → (ch out0).ack (t + 1) ≠ (ch out0).ack t →
      (ch out0).ack (t + 1) = (ch out0).req t)
    (H_KER_REARM : ∀ o, isSrcK (opAt o) = false → opAt o ≠ K.sink out0 →
      Cell (shiftRun (e + 1) ch) (srcV a b) (opAt o)) :
    LapInv a b ch (e + 1) :=
  lapinv_of_parts a b ch (e + 1) H_SRC
    (sink_C_of_wire (ch out0) T0 (e + 1) (by omega) H_SINK_SI (fall_vals hfall).2) H_KER_REARM

/-- `p_end` (circuit channel 3, `bd_fork` output of `start`) is consumed by `K.sink 3`. -/
def pend : Fin NC := 3

theorem pend_cons_sink : opAt (consOf pend) = K.sink pend := rfl

/-- **A necessary condition of the per-lap invariant**: `p_end`'s acknowledge must be low at the
cut (`Sink.init` of `K.sink 3` on the shifted run). -/
theorem lapinv_pend_idle {a b : Nat} {ch : Fin NC → Chan} {T : Nat} (hL : LapInv a b ch T) :
    (ch pend).ack T = false := by
  have hs : Ops.Gcd.Sink (shiftRun T ch pend) := by
    have := hL (consOf pend); rw [pend_cons_sink] at this; exact this
  have := hs.init
  simpa [shiftRun, rtC, shf] using this

/-- **The per-lap cut fails when the `p_end` loop is fast.** Fixed-delay idealisation of
`bd_fork`'s `p_end` output (`H_FORK_DLY`: `p_end_req` is `start_req` `dF` ticks earlier; the
RTL makes it a wire) and of `upsnk` (`H_UPSNK_DLY`, `dP` ticks). If `start.req` has been high
on `[r+1, T]` with `r + 1 + dF + dP ≤ T` (H_PEND_FAST), `p_end`'s acknowledge is high at `T`
and `LapInv` fails at `T`. -/
theorem lapinv_fails_pend_fast (a b : Nat) (ch : Fin NC → Chan) (T r dF dP : Nat)
    (hst : ∀ t, r + 1 ≤ t → t ≤ T → (ch start).req t = true)
    (H_FORK_DLY : ∀ t, dF ≤ t → (ch pend).req t = (ch start).req (t - dF))
    (H_UPSNK_DLY : ∀ t, dP ≤ t → (ch pend).ack t = (ch pend).req (t - dP))
    (H_PEND_FAST : r + dF + dP ≤ T) : ¬ LapInv a b ch T := by
  intro hL
  have h1 := lapinv_pend_idle hL
  rw [H_UPSNK_DLY T (by omega), H_FORK_DLY (T - dP) (by omega),
    hst (T - dP - dF) (by omega) (by omega)] at h1
  exact absurd h1 (by decide)

/-- **The rig's own laps fail the cut when the `p_end` loop beats `out0`'s return.** Under the
lap contract (`Ring` on `start.req`, `out0.ack`) and the fixed `p_end` delays: at the close
`s` of result `k-1` (`k ≥ 1`), if lap `k`'s offer `r` satisfies `r + 1 + dF + dP ≤ s + 1`,
then `LapInv` fails at `s + 1`. The offer `r < s` exists and `start.req` is high on
`[r+1, s+1]` by `lap_close`. -/
theorem lap_cut_fails (a b : Nat) (ch : Fin NC → Chan) {T0 Tq : Nat} {φ1 φ0 : Nat → Nat}
    (H : Ring (ch start).req (ch out0).ack T0 Tq φ1 φ0) (dF dP k s : Nat) (hs : T0 ≤ s)
    (hfall : fallB (ch out0).ack s = true) (hk : Fl (ch out0).ack T0 s + 1 = k)
    (H_FORK_DLY : ∀ t, dF ≤ t → (ch pend).req t = (ch start).req (t - dF))
    (H_UPSNK_DLY : ∀ t, dP ≤ t → (ch pend).ack t = (ch pend).req (t - dP))
    (H_PEND_FAST : ∀ r, riseB (ch start).req r = true → R (ch start).req T0 r + 1 = k →
      r + 1 + dF + dP ≤ s + 1) :
    ¬ LapInv a b ch (s + 1) := by
  obtain ⟨_, _, _, _, _, _, _, _, r, _, _, hrr, hRr, _, hhi⟩ := lap_close H k s hs hfall hk
  exact lapinv_fails_pend_fast a b ch (s + 1) r dF dP (fun t h1 h2 => hhi t (by omega) h2)
    H_FORK_DLY H_UPSNK_DLY (H_PEND_FAST r hrr hRr)

/-- Non-vacuity of `lapinv_fails_pend_fast`: its hypotheses are jointly satisfiable (every wire
high, zero delays, `r = 0`, `T = 1`). -/
theorem pend_fast_nonvacuous :
    ∃ (ch : Fin NC → Chan) (T r dF dP : Nat),
      (∀ t, r + 1 ≤ t → t ≤ T → (ch start).req t = true) ∧
      (∀ t, dF ≤ t → (ch pend).req t = (ch start).req (t - dF)) ∧
      (∀ t, dP ≤ t → (ch pend).ack t = (ch pend).req (t - dP)) ∧
      r + 1 + dF + dP ≤ T :=
  ⟨fun _ => ⟨fun _ => true, fun _ => true, fun _ => 0⟩, 1, 0, 0, 0,
    fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, by decide⟩

end C

end Formal.Cells.RigLaps
