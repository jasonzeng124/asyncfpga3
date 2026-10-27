# A-xsim: a timed ternary (X-window) simulator that is sound and computable (shard A)

## Files

- `formal/lean/Formal/Core/XSim.lean` is proved: about 650 lines, core Lean only, about 7 s for the file. Namespace `Formal.Core.XSim`.
  It imports, and does not copy, `Formal.Core.Lut` (which brings in Kleene), `Formal.Core.Circuit` and `Formal.Core.Trace.Discrete`.
- There is no Wip file because nothing is left unproved. The planned extensions are listed below.

Check (from `formal/lean`):

    ../check.sh Formal/Core/XSim.lean      # [audit] 465 declarations checked, [check] OK

There is no sorry, admit, axiom, native_decide or bv_decide. Every `decide` is a kernel `decide`.

## Model

- **Concrete model.** This is Discrete time (`ℕ → Bool`, one step = 1 ps).
  - A gate `LGate n` is a Core `Lut k` with its real INIT and `Lut.eval`. It has a pin wiring `ins : Fin k → Fin n`, an output wire and a band `[lo, hi]`.
  - The relation `LGate.rel` is `TraceDiscrete.Transport lo hi (exc x) (x out)`: a zero-delay LUT function followed by a monotone warp.
  - A routed wire is a `Lut 1` buffer (`Init.delay_buf`) with its own band.
  - A network is a `List (LGate n)`. `toCircuit` turns it into a Core `Circuit (Fin n) Sig`, and `Circuit.Sat` defines the behaviours. Cycles are allowed.
- **Weaker channel `WinCh`.** Each output sample is *some* input sample from `[t-hi, t-lo]`, so the channel is non-FIFO with a delay that varies per step. This is B's `WinDelay` without its power-up gap.
  - `transport_winCh` shows that every transport channel is a `WinCh`.
  - Soundness is proved for `WinCh` networks, so it covers both channels.
- **Abstract model.**
  - A gate output is `win lo hi (fun s => keval(pins at s)) t`. This is the `K3.merge` of the per-time Kleene LUT value over the window. `merge` is the glb in `⊑`, i.e. "X unless all agree". The brief calls it a "join", but in Core's order X is the bottom.
  - Doing `keval` per sample time and *then* merging is tighter than merging the pins first. It is still sound because a LUT samples all its pins at one instant.
  - Primary inputs come from the abstract signals `u`. The driven wires at t = 0 come from `a0`, the power-up row, normally all X.
- **Simulator `hist`.** It is structural recursion on time and builds `[row t, …, row 0]`, where each row is a `List K3` over the wires.
  - `arow` and `val` read rows and single values out of it.
  - Rows are lists rather than functions. The kernel caches whnf of the shared list cells, so each cell is evaluated once and the evaluation is not exponential.

## Theorems (all in `Formal.Core.XSim`)

| name | statement |
|---|---|
| `wmerge_le`, `win_le`, `win_const` | the window is below every sample in it; a constant window equals the constant |
| `transport_winCh`, `LGate.relW_of_rel` | transport ⇒ window channel |
| `win_exact` | **one-gate exactness**: if the window value is X, two legal `WinCh` outputs differ at `t`. So all loss of precision comes from composing gates (correlations through reconvergence and feedback), not from the per-gate abstraction |
| `hist_getD`, `val_zero`, `val_succ`, `mkRow_getD`, `driver_some/none` | simulator bookkeeping |
| **`sound`** | network of window-channel gates, every `lo ≥ 1` (causality, so no zero-delay loop; cycles are allowed), `u` covers the undriven wires, `a0` covers the driven wires at 0 ⇒ `∀ t w, val t w ⊑ ofBool (x w t)` |
| **`sound_circuit`** | the same for `Circuit.Sat (toCircuit gs) x` with Discrete transport gates |
| `defined_eq` | a binary abstract value equals the concrete value, so it is a fact about every delay assignment |
| **`stationary`, `val_stationary`** | inputs constant from `t0`, the last `H ≥ max hi` rows equal, every `lo ≥ 1`, `lo ≤ hi` ⇒ every later row is equal. A `decide` up to horizon T thus becomes a statement for all time |

**Demo: `bd_c2` (`Demo` namespace).**
- Wires: `a_in`, `b_in`, `rst` and `gnd` are ports. `a_pin` and `b_pin` are the routed input nets. `q` is the LUT O output and `qp` is the routed feedback to I2.
- Gates: `Init.bd_c2` with its real INIT and pins `[a_pin, b_pin, qp, rst, gnd, gnd]`, plus three routes. All bands are `[1,3]`.

| name | statement |
|---|---|
| `fp_q_trace`, `fp_rows_fixed` (decide, T = 45) | under four-phase (reset, then a↑10, b↑16, a↓26, b↓32), q follows `specFPq`: X at power-up t=0, 0 on [1,17], X on [18,21], 1 on [22,33], X on [34,37], 0 from 38. The windows were derived from the bands *before* the run (see the docstring), not pasted from it |
| `fp_q_abs` | the same for **all** t, via `stationary` |
| **`fp_q_concrete`** | for **every** concrete behaviour (every route, LUT and feedback delay in [1,3] as monotone warps, any power-up state): `q = 0` on [1,17], `q = 1` on [22,33], `q = 0` for all t ≥ 38. The cell settles, and X only appears in windows of width `Σ(hi−lo)` along the path, plus 1 |
| `hz_q_trace`, `hz_q_abs` | b↑ at 6 (state stays 0), then a↑ and b↓ in the **same** step 16. The abstract q is X for all t ≥ 18, **forever**: the feedback latches the hazard, and X never resolves by itself |
| **`hz_latch_one`, `hz_latch_zero`, `hz_nondeterministic`** | the X is real. With routes a = 1 ps and b = 3 ps the pins see 11 for 2 steps and q latches 1 forever. With a = 3 ps and b = 1 ps the pins see 00 and q stays 0 forever. Both behaviours are proved to satisfy `Circuit.Sat` for all t. So no sound simulator can give a binary q there, and X-forever is the exact answer |

**Comparison with shard B.**
- `CElemTiming.runt_oscillates` exhibits a third legal behaviour, a runt that oscillates in the loop forever. Our X covers all three outcomes: 1, 0, and oscillation.
- B's `c2_four_phase` proves the four-phase result **symbolically** for all bands, under environment-latency hypotheses. Here a single concrete instance is checked automatically.

## Scaling (measured, `decide +kernel`, 4-core shared machine)

Workload: a chain of m `bd_c2` stages. Each stage has a LUT and a feedback route. There are 2 input routes, giving 2m+2 gates and 2m+6 wires. Inputs toggle every 20 steps. The check forces a full row at T.

| gates | T | wall time (including about 2 s of imports) |
|---|---|---|
| 4 | 45 | 3 s (the demo file, all 4 decides, is about 7 s) |
| 4 | 200 | 5 s |
| 4 | 800 | 14 s |
| 10 | 200 | 11 s |
| 34 | 200 | 53 s |
| 34 | 800 | 172 s |
| 130 | 200 | 180 s |

- The cost is roughly linear in T and in wires, at about 2–6 ms per wire-step.
- Plain `decide` first evaluates the instance in the elaborator. That hits the 200k heartbeat limit at 34 gates × 200 steps. `decide +kernel` is kernel-only, adds no axiom and is not `native_decide`, so use it beyond small cells.
- The known overheads are fixable:
  - `driver` is a `find?` over the gate list for every cell.
  - Pins are looked up by `List.getD` on a row, which is O(n).
  - A precomputed driver table, plus a `hist'` with a proved `hist' = hist` lemma, would remove these.
- That lemma was **not needed** for cell-sized checks, so it was not written.

## What does not check / not done

- **B's power-up channel `WinDelay`** leaves the output unconstrained for t < hi, so it is not literally a `WinCh`.
  - Supporting it needs a `cell` variant that outputs X for t < hi. The proof is the same induction, with that case closed by `X_le`, at about 30 min.
  - Today, B's channel is covered only through `transport_winCh`-style refinements, and with `a0` for t = 0.
- **Inertial delay is not covered.** An inertial output can hold a value older than `hi` (B's note). A pulse filter would need its own abstract rule, for example: output X while the input window is non-constant AND shorter than the threshold.
- **Real magnitudes.** LUT delays are about 100–250 ps and routes 100–600 ps.
  - At 1 ps resolution a cell needs a horizon of thousands of steps. That costs about 1 min per 5000 steps for the 4-gate cell, which is still feasible.
  - **Coarsening the time step is not proved sound.** A 1 ps behaviour is not a behaviour on a 10 ps grid. A rounding lemma (floor `lo`, ceil `hi`, cover the inputs on the coarse grid) is the next theorem to prove.
- `lo ≥ 1` is required on every gate, including routes. A zero-delay route has to be merged into its LUT's band.

## Verdict

**Works.** Soundness for cyclic networks, the computable simulator, the all-time lift (`stationary`), one-gate exactness, and the bd_c2 demo all check, including the proof that the latched X is real nondeterminism. It took about 2 h.

**Effort to make it a production engine for C's track 10:**
- About 1 day: the driver table, a `hist'` correctness lemma, B's power-up channel, and inertial rules.
- About 1–2 days: grid coarsening with outward rounding.

## What it buys

A **sound, automatic, delay-band-aware cell checker whose verdicts are theorems**:
- Write the netlist with the real INITs and bands.
- Write the stimulus, or abstract inputs with X windows for environment uncertainty.
- `decide` (or `decide +kernel`) proves the trace up to T.
- `stationary` extends it to all time, and `sound_circuit` + `defined_eq` turn every binary value into a statement about every behaviour.

This replaces hand proofs like B's per-cell timing lemmas for any **concrete** band instance. B's symbolic proofs remain the way to get results parametric in the bands.

For C's verified timing checker (track 10), this is the candidate kernel. The window values of a bundled-data stage are the data-valid and request windows, and X on a data wire at the latch-capture time is exactly a bundling violation. Because the result is already a theorem about `Circuit.Sat`, it composes with the Circuit-layer refinement lemmas.

## Fidelity

- **LUT function.** The real INIT with Core `Lut.eval` (Boolean). The Kleene `keval` is used only as an abstraction of *sets of Boolean values*. The concrete model is binary, so this result does not depend on the `H_KLEENE_LUT` electrical hypothesis.
- **Delays.**
  - Lumped transport per LUT, measured from the instant all pins are sampled, plus one band per routed net.
  - The model assumes all pins of a LUT are sampled at one instant: a zero-delay LUT function after pin routing. Pin-to-O delay differences within the LUT have to be folded into the per-pin route bands. That is a hypothesis.
  - Test: GLS with SDF-annotated per-pin `IOPATH` delays versus the lumped model, or a board ring measurement per pin.
- **Not modelled:**
  - glitches that the transport model passes or annihilates while silicon filters them (inertial);
  - runts and metastability at intermediate voltage. The binary concrete model has no intermediate level. The abstract X does stand for "outcome depends on delays", which includes the runt case B exhibits.
- **The bands are hypotheses.** The source of a band would be the prjxray delay data for min and max, with the guardband applied (`GUARD_LO`/`GUARD_HI`). The check is GLS at the slow and fast corners.
