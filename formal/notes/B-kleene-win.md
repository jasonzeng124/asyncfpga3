# B-kleene-win: per-edge X windows with their own split (probe Bxw)

File: `formal/lean/Formal/Cells/KleeneWin.lean`. It is core Lean and imports
KleeneBox and CElemStrict. Check: `/tmp/claude-0/btools/bcheck.py Formal/Cells/KleeneWin.lean`
gives `OK`, with no warnings. There is no sorry, axiom or native_decide in it. The axioms
of every headline are propext, Classical.choice and Quot.sound, or a subset
(`steer_ct_split_x`, `c2_fbwin_*` and `loopW_exists` use propext and Quot.sound only).

## Question

KleeneBox's edge forms assume **H_X_UNIFORM**: every binary edge `T` of every
signal is X on `[T - a, T + c)`, with the same `(a, c)` everywhere. Under that
assumption each setup and hold gains `w = a + c`, and becomes strict at
`w = 1`. The audit (P8 section 2) points out two problems: the uniform split
is an assumption, and `w = 1` is the grid tick, not a measured value.

This probe asks two things:
1. What are the exact conditions when each edge has its own window?
2. How could `w` be bounded from data?

## 1. Answer (Lean)

**H_X_EDGE.** Each binary edge `T` of each pin has its own window
`[T - a_T, T + c_T)`. Rise and fall, and request, select, data and enable,
are all independent. Only `a_T + c_T ≥ 0` is required. Every other
hypothesis is unchanged from KleeneBox, LibGapLatch and CElemStrict.

**Rule.** Every race condition gains `c(edge that must come first) + a(edge
that must come after)`, and nothing else. The other two halves drop out
exactly, because the pin may be anything outside its definite window.

| cell / race | exact condition (iff) | theorem |
|---|---|---|
| bd_steer setup | `S0 + Shi + (cS0 + aR) ≤ R + Rlo` | `steer_win_exact` |
| bd_steer hold | `F + Rhi + (cF + aS1) ≤ S1 + Slo` | `steer_win_exact` |
| bd_mux join setup / hold | the same, with ctl_req edges `Cr`, `Cf` | `join_win_exact` |
| bdc_muxn selected join | per index bit i: `Ai0 + Ahi + (cAi0 + aCr) ≤ Cr + Clo`, `Cf + Chi + (cCf + aAi1) ≤ Ai1 + Alo` | `muxn_win_exact` |
| bd_latch setup_pulse | `Ton + Ehi + Qhi + (cOn + aOff) ≤ Toff + Elo` | `latch_win_exact` |
| bd_latch setup_data | `Td + Dhi + Qhi + (cD + aOff) ≤ Toff + Elo` | `latch_win_exact` |
| bd_latch hold | `Toff + Ehi + (cOff + aN) ≤ Tnew + Dlo` | `latch_win_exact` |
| C-element own-feedback race (any `Facts` cycle) | `Tf + cf + D + ar ≤ Tr`; in B's terms `cf + dlmax + dwmax + ar ≤ dlmin + E` | `cel_edges_iff`, `cel_env_iff` |
| same, feedback pin with its own window `wq` (H_FB_WIN) | `Tf + cf + D + wq + ar ≤ Tr`; `cf + dlmax + dwmax + Wq + ar ≤ dlmin + E` | `clean_iffW`, `box_iffW`, `cel_env_win_iff` |

Notes on the table:
* bd_steer: `aS0`, `cS1`, `cR` and `aF` do not appear.
* bd_mux join: the request pins and the feedback pin drop out, whatever their
  windows.
* bd_latch: the enable's rise window `aOn` drops out.
* `R, F, S0, S1, Cr, Cf, Ton, Toff, Td, Tnew, Tf, Tr` are binary-edge times.
  `S0` is the edge where the select enters `v` and `S1` the edge where it
  leaves `v`. `Tf` is the follow pin's edge and `Tr` the release pin's edge.

How the proofs work:
* The iffs are corollaries of the definite-window iffs (`steer_box_exact_K`,
  `join_box_exact_K`, `muxn_sel_box_exact_K`, `LibGapLatch.box_exact`,
  `CElemStrict.clean_iff`/`box_iff`), read at `R - aR`, `F + cF`, `S0 + cS0`,
  `S1 - aS1`.
* The necessity halves are the binary counter-traces of LibGapSteer, Mux,
  MuxN and Latch, carried through the embedding with the pulse over the outer
  window edges (`reqW_pulse`).

**Feedback window (new).** H_FB_WIN says the C-element's feedback pin reads
the Kleene join of the root over `[t - D - wq, t - D]`. This is the cell's own
output edge, seen at I2 with its own X window of width `wq`. A leading part of
that window is the same as a smaller `D`.
* `wq = 0` is CElemStrict's H_FB_PURE (`loopW_of_loop`).
* `prefix_okW`, `cleanW`, `hazardW` and `clean_iffW` are re-proved for any
  `Facts` cycle. That covers every C-element variant of CElemStrict2 and the
  latch odd bit (`latch_fbwin_iff`).
* Non-vacuity is a simulator (`simGW`, `sim_loopW`, `loopW_exists`).
* On the real bd_c2 INIT: CElemStrict's `strict_clean` point (`s = 421`,
  `D = 420`, `wb = 1`) becomes a hazard with `wq = 1` (`c2_fbwin_hazard`). It is
  clean at 422 (`c2_fbwin_clean`).

**What this says about "+w, strict at w = 1".** The claim holds only under
H_X_UNIFORM (`steer_win_uniform` recovers it). Without the uniform split it is
neither necessary nor sufficient. In `steer_split_matters`, every edge has a
window of width 1:
* With the request's windows inside its pulse and the select's outside its
  binary window, binary-edge equality is safe.
* With the opposite split on the setup pair (`cS0 = aR = 1`), a setup that is
  strict by one tick in binary-edge times is unsafe.
* `steer_ct_split_x` is the explicit trace for the unsafe case: the unselected
  O5 reads X at 1300, where the spec is definite 0.

**Sufficient forms for the JSON.** The proved conditions use the individual
halves. A row can be stated without knowing the split, as a sufficient but
not exact condition. Under a bound `H_W_BOUND: c_e + a_l ≤ W` for every race
pair, add `+W`. For the C-element race, add `+W` with `W ≥ cf + wq + ar`.
"+1, strict" is the special case `W = 1`, and section 2 shows that nothing
supports `W = 1`.

Non-vacuity witnesses:
* `steer_witness_W`, `join_witness_W` and `latch_witness_W` use a different
  split on every edge, with X on every window.
* `join_witness_W`: on the real uj0/uj1 INITs, the unselected join is definite
  0 at every instant, and the selected join is definite 1.
* `latch_witness_W` reuses LibGapLatch's run.
* For the C-element: `c2_fbwin_clean` and `loopW_exists`.

NOT covered:
* The values of `a_T`, `c_T` and `wq`.
* Windows that the box adversary picks per token. Each theorem is stated for
  given windows; the box quantifies over read maps only.
* bdc_muxn's unselected joins in K3 (`Cover` is binary only, as in KleeneBox).
* A mid-rail select inside the mux tree beyond H_KLEENE_LUT.
* Correlated corners.
* The "lost race" side of the C-element (the output returns to `v` and holds).
  This is used in the test design below, and it is derived by hand from
  `Facts.hz1v` and hold. It is not a Lean theorem.

## 2. What `w` is on the substrate, and how to bound it

**In the digital model.** An X window is the interval in which a LUT input
pin's select is neither rail, because its driver's output is crossing
mid-rail at that pin. It is a property of each arc (the driving net and the
receiving pin), and it is bounded. The race conditions above need only the
sums `c_e + a_l` (plus `wq` on a loop).

**Why none of the existing models gives it:**
* prjxray-db gives delays (fast/slow min/max, R and C for Elmore). It gives no
  transition time or input threshold.
* The routed SDF has none either.
* The research branch's board-fidelity GLS (`cells/gls/fid_core.vh`, F3) delays
  each LUT pin by transport and evaluates a zero-time mux tree on binary
  edges. So `w = 0` by construction, and it cannot bound `w`.
* That GLS does carry an analogous unmeasured parameter: FID_RESOLVE's LUT-loop
  decision window `WIN = 150 ps` (with `TAU`), "an assumption: no figure was
  found" (`research/data/fid/f3_model.md`).
* The formal side uses 1 ps and the GLS uses 150 ps. Neither is measured, and
  the two disagree by two orders of magnitude.
* The existing board data cannot settle it either:
  * `arb_mtbf` sweeps the phase uniformly (two free-running rings). The rate
    of each outcome then depends on where the band lies, not on how wide it
    is.
  * Its detector-floor pulses step by one bd_delay link (about 274 ps), which
    is far coarser than `w`.

**Test design XW-1: the decision band of the cell's own race.**

*Idea.* Use the C-element race itself as the sampler. Its outcome is a LEVEL,
not a pulse:
* If it wins, `q = n` and holds.
* If the release comes before the loop has turned, `q` returns to `v` and
  holds (hz1v, then hold).

So no pulse-detector threshold enters the measurement. In the digital model,
with release-minus-follow offset `Δ = Tr - Tf`:
* The outcome is deterministic `n` for `Δ ≥ D + cf + wq + ar`. This is
  `cel_edges_iff` / `clean_iffW`.
* It is deterministic `v` for `Δ ≤ D - af - cr` (derived by hand, see NOT
  covered).
* In between, either outcome can occur (X).

The band width is therefore `w_f + w_r + wq`. The loop delay `D` cancels, so
the SDF's delay error does not enter. Run-to-run delay scatter
(`Dhi - Dlo`) and stimulus jitter only widen the band. The measured width is
therefore an upper bound on the exact term `cf + wq + ar` that the race
needs.

*What to build* (reuse `cells/hw`: build_hw.sh, the xsdb readback, and
check_fracture-style placement checks):
1. DUT: one `bd_c2` (INIT 00E8.., real pin map: a on I0, b on I1, q to I2,
   rst on I3), LOC-pinned. Record its feedback pips. Use 4 copies:
   * A6 vs A1 for the follow pin (root vs leaf of the mux tree);
   * short vs long (8 extra hops) follow-pin route.
2. Stimulus: one MMCM, VCO 1200 MHz, dynamic phase shift (PSEN/PSINCDEC). The
   step is 1/(56 × 1.2 GHz) = **14.9 ps**.
   * Clock A launches the follow edge (b: 0→1, with a = 1) from an FDRE.
   * Clock B, phase-shifted, launches the release edge (a: 1→0) from an FDRE.
   * Both FDREs are placed next to the DUT.
3. Trial: rst pulse (q = 0), a = 1, b = 0; follow edge; release edge at phase
   φ; sample q with an FDRE 20 ns later. A synchronizer is not needed, because
   q has settled by then. Count the q = 1 outcomes; anything still unsettled
   after 20 ns counts as mixed.
4. Sweep: φ over ±1.5 ns around the SDF-predicted boundary, N = 2000 trials
   per step, at 4 placer seeds (CLAUDE.md: one route is a sample).

*Measurements:*
* `k_lo`: the last step where all N trials give `v`.
* `k_hi`: the first step where all N trials give `n`.
* The bound **W̄ = (k_hi − k_lo) × 14.9 ps**. It is conservative: it includes
  both partial steps. Report the maximum over copies and seeds.

*Controls (each one can fail):*
* **Scale.** Insert one calibrated bd_delay link (ro_top ring-calibrated) in
  the release path. The band must move by that delay ± 1 step.
* **Positive.** Drive the release pin through a 2:1 mux between two routes
  that differ by one link δ, with the select set per trial by an LFSR. The
  bench must report a band ≥ δ. If it reports less, the bench is broken.
* **Instrument.** Replace the DUT by an FDRE that samples the follow edge on
  the release edge. Its band W_ctrl is jitter plus the flop aperture. Report it
  next to W̄, but do NOT subtract it: take the longer number.
* **Slew dependence.** If the long-route copy's band exceeds the short one's
  by more than 1 step, the windows grow with net load. W̄ must then be stated
  per route class, not globally.

*The number that decides it: W̄ in ps.*
* It replaces the `+1` of every "strict" row (for every race pair under
  H_W_BOUND).
* Each row whose guardbanded slack (GUARD_LO/HI applied) is below W̄ is unsafe
  under the model. The rows whose slack is at least W̄ stand.
* If no mixed step is seen, W̄ is one step (14.9 ps), not 1 ps.
* W̄ also replaces the GLS's assumed `WIN` (150 ps). If W̄ is much less than
  150 ps, the GLS is pessimistic there; if W̄ is greater than 150 ps, the GLS
  is optimistic.

*Limits:*
* The C-element bench bounds `w_f + w_r + wq` at one receiving pin pair.
  Carrying that bound to the steer, join and latch pins is the hypothesis
  H_W_BOUND, which the A1/A6 and route-length copies only sample.
* The band includes analog metastability resolution. In the digital model
  that is part of the X behaviour, so the bound stays sound but is not tight.
