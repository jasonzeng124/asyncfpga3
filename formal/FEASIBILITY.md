# Gate-level formalization of asyncfpga3: feasibility

Owner's question: can this project's circuits be formalized at gate level and
proved correct (in Lean 4 or similar), and how feasible is that?
Program: `formal/PROGRAM.md`. Shard A writes this file from all three shards'
journals (`JOURNAL.md`, `JOURNAL-B.md`, `JOURNAL-C.md`) and `formal/notes/`.

**Status: DRAFT, updated as probes land (last update: see git log).**

## Short answer (provisional)

Yes for the logic and timing layers, with work: everything the probes have
tried so far at the cell level checks in Lean 4 with no `sorry`, no extra
axiom and no `native_decide`, in hours per probe rather than weeks. Gate-level
statements are cheap because a LUT is a finite object (`decide +kernel`
handles all 3^6 Kleene input vectors of one LUT6 in about 2.5 s). The hard and
expensive parts are not the proofs. They are (1) the **hypotheses about the
silicon** that every theorem needs (the Kleene behaviour of a LUT with a
mid-rail input, delay bands that are correlated across a die, the arbiter's
analog resolution), which no proof can discharge and which need GLS or board
experiments; and (2) **connecting** the proofs to the real routed design
(netlist import, delay numbers per arc), which is engineering.

## How to check

```
formal/setup.sh                 # once: Lean 4.35.0 + Mathlib v4.35.0 (see Toolchain)
formal/check.sh --committed     # build all committed Formal/ modules + axiom audit
formal/check.sh                 # same over every file in Formal/ (incl. uncommitted)
formal/check.sh Formal/Core/Lut.lean ...   # single files (paths relative to formal/lean)
```
The audit runs `collectAxioms` on every declaration in a `Formal.*` module and
fails unless it uses only `propext`, `Classical.choice`, `Quot.sound`. Negative
controls (journal, 2026-10-27): a hidden `sorryAx` fails it, `native_decide`
fails it (`..._native.native_decide.ax_1_1`). Work in progress lives in
`formal/lean/Wip/` (not built, never claimed).

## Verdicts per track

| # | track | verdict | evidence (checks) | effort to finish | buys the project |
|---|---|---|---|---|---|
| 1 | Toolchain | **works, with a workaround** | `formal/setup.sh`, `check.sh` | done | — |
| 2 | Trace representation | **works (all three)**; ℕ-ps discrete chosen for gate/cell proofs, ℝ for analog and fidelity | `Core/Trace/{Discrete,Event,Real}.lean` | discretisation soundness ℝ→ℕ: 1–2 d (probe running) | a common substrate for B and C |
| 3 | Delay channels | pure: **works**; inertial: **works**; involution: pending | `Core/Delay/{Pure,Inertial}.lean` | involution 2–4 d; corner-correlated bounds (probe running) | sound wire abstraction; exact bundling lemma |
| 4 | Kleene LUT | **works** | `Core/{Kleene,Lut,LutTree,Ternary}.lean` | unify K3 types (probe running) | decidable per-cell hazard/settling check |
| 5 | C-element | (shard B) | see `JOURNAL-B.md` | | |
| 6 | Latch / link | (shard B) | | | |
| 7 | Arbiter | (shard B) | | | |
| 8 | Composition | (shard C) | see `JOURNAL-C.md` | | |
| 9 | Ring needs 3 stages | (shard C) | | | |
| 10 | Verified timing checker | (shard C) | | | |
| 11 | Netlist import | (shard C) | | | |
| 12 | Other tools | (shard C) | | | |
| 13 | Literature | **done** | `notes/A-lit-1.md`, `notes/A-lit-2.md` | — | positioning; nothing like this exists in Lean |

### 1. Toolchain
Lean 4.35.0, Mathlib v4.35.0, lake project `formal/lean`. The sandbox proxy
blocks release.lean-lang.org, Reservoir, cache.mathlib.org and
lakecache.blob.core.windows.net, so Lean comes from the GitHub release zip and
Mathlib is built from source, only the modules imported (rule: never
`import Mathlib`). Most Core and Cells files need only core Lean. 4 cores /
15 GB: `slot.sh` allows 3 concurrent Lean processes.

### 2. Traces
Three representations did the same benchmark (B0 definitions, B1 fixed delay
composition, B2 bounded transport relation with composition and monotonicity,
B3 pulses, B4 inertial, B5 an AND gate in a conjunction circuit):
- **ℕ → Bool, 1 ps** (`Core/Trace/Discrete.lean`, 505 lines, core Lean, ~2 h):
  all of B0–B5. Non-Zeno for free; ties (simultaneous arrival) exact; `decide`
  does bounded model checks (256 inputs × 10 steps in ~10 s). Rounding to 1 ps
  costs ≤ 1 ps per arc. Weakness: sub-quantum runts are invisible; soundness
  w.r.t. real time needs a separation hypothesis (probe running).
- **Event lists** (`Core/Trace/Event.lean`, 625 lines, ℝ times): all of B0–B5;
  composition is `List.map`; but every n-input gate needs an event-list merge
  (200 lines for one 2-input gate); only finitely many transitions in total
  (no free-running ring).
- **ℝ → Bool**: (pending, `A-trace-real.md`).
Decision so far: ℕ-ps for gate and cell proofs (shards B and C chose it
independently), ℝ for analog loops and for the fidelity bridge from prjxray.

### 3. Delay channels
- **Bounded pure (transport) delay** (`Core/Delay/Pure.lean`): channel = FIFO
  retiming with delay in [lo, hi]. Series composition is *exactly* the sum
  band (`chan_comp_iff`); a pulse of width w comes out with width in
  w ± (hi−lo) and can vanish iff w ≤ hi−lo (`pulse_vanish_iff`); the
  bundling lemma `bundle_two_wires`: data stable at request arrival when
  ts + hi_data ≤ lo_req.
- **Inertial** (`Core/Delay/Inertial.lean`): filtering of pulses < ρ;
  output pulse width discontinuous at ρ; inertial channels are **not closed
  under composition** (`inertial_comp_1_2_not_inertialRD`); on runt-free
  inputs inertial = transport (`inertialRD_of_noShort`). Consequence: a GLS
  with inertial LUT paths (today's iverilog GLS) cannot show a LUT runt, so it
  is not evidence of runt-freedom; proofs must never use inertial filtering
  as a hypothesis.
- **Involution** (Függer et al.): pending.
- **Corner correlation**: the independent band [fast-min, slow-max] is 3–4×
  wide (A-fidelity), so no matched-delay (bundling) condition is provable from
  independent bands; a shared-corner + local-scatter model is being probed.

### 4. Kleene LUT
- `Core/Kleene.lean`, `Core/Lut.lean`: shared K3 and LUT API (INIT as
  `BitVec (2^k)`, I0 = LSB, LUT6_2 O5/O6). Kleene eval equals the INIT-table
  definition for every k; monotone; single-input change never hazardous
  (`no_static_hazard_single`); two-input change can be — on the C-element itself,
  a b 01→10 with q=0 gives X (`Init.bd_c2_two_change_hazard`). 23 cell INITs
  transcribed with `*_eval` theorems that confirm the RTL header comments.
- `Core/LutTree.lean` (gate fidelity): the LUT as a pass-transistor mux tree.
  Mux-tree Kleene eval = INIT-table semantics for every k, INIT, input
  (`evalTree_eq_tableEval`); tree order irrelevant; with arbitrary per-mux
  delays a single-input change with equal endpoint values never glitches
  (`sic_glitch_free`), under named hypotheses `H_mux_kleene`, `H_sram`.
- `Core/Ternary.lean`: Eichelberger ternary simulation is sound for every
  causal delay behaviour (gate/wire transport, inertial, GMW) and settles
  under bounded staleness; bd_c2's every single-input flip settles with no
  static hazard. This is a decidable, delay-independent per-cell check.

### 13. Literature
`notes/A-lit-1.md` (async/SI/DI verification, involution model,
metastability-containing logic, arbiter theory; 40 sources) and
`notes/A-lit-2.md` (proof-assistant hardware work). Closest prior art:
ACL2 link-joint self-timed proofs (Chau/Hunt/Kaufmann/Roncken/Sutherland);
Graphiti (Lean 4, Dynamatic dataflow rewrites, ASPLOS'26) as the token-level
target; Lutsig (HOL4, 7-series LUT/CARRY4, synchronous). Nobody has
mechanised LUT-built async cells, bundled-data timing together with gate
function, or a gate-level arbiter.

## Fidelity per primitive

(From `notes/A-fidelity.md`, `A-lut-tree.md`, `A-kleene-lut.md`; to be
completed with shard B's cell notes.)

| primitive | model in Lean | fidelity | hypothesis | how to test |
|---|---|---|---|---|
| LUT function | Kleene mux tree from INIT | logic exact (INIT = function, proved for all k) | `H_mux_kleene`: a mid-rail select with equal data inputs passes the data, no charge-sharing dip; `H_sram` | board: masked-pin toggle into a fabric edge counter; SPICE |
| LUT timing | per-mux delays, arbitrary | order of tree (A6 at root per UG474) only affects delays | prjxray LUT arcs are flat; pin dependence is in site-pin delays (A1 slow ≤ 0.516 ns) | per-pin delay ring |
| routing pip | bounded transport [fast-min, slow-max] per sink arc | all INT_L pips in prjxray zynq7 are buffered; RC tree responds monotonically (no glitch) | band from prjxray via Elmore per sink arc (not summed per pip); shared corner + local scatter (pending) | n=128 ring periods inside summed bands |
| MUXF7/F8, CARRY4 | settle within hi | only in datapath cones, never in control | "anything before hi" | — |
| FF (FDRE) | — | only `bd_mlink` and test rigs | standard setup/hold (slow corner only in prjxray) | — |
| delay model in today's GLS | inertial on cell outputs, one value per arc | disagrees with silicon: swallows runts; ignores the 3–4× band and fanout | — | GLS with transport LUT paths, diffed |

Note: prjxray-db's `timings/*.sdf` triples are (FAST)(SLOW), not rise/fall;
a standard SDF reader misreads them (A-fidelity).

## Findings for the main project (to verify, not confirmed defects)
- The research GLS's `SLICE_LUTX` builds the LUT mux tree with A6 at the
  leaves; the silicon has A6 at the root (UG474). Harmless for logic values,
  differs in timing (A-lut-tree).
- Shard B (7b): the bd_arbiter A0 hold relies on a fork ordering H_A0_FORK
  (A0's fall must reach ua2 before A0 → ustate → q → ugrant → g2 does).
