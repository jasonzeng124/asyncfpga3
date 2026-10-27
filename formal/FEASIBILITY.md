# Gate-level formalization of asyncfpga3: feasibility

Owner's question: can this project's circuits be formalized at gate level and
proved correct (in Lean 4 or similar), and how feasible is that?
Program: `formal/PROGRAM.md`. Shard A writes this file from all three shards'
journals (`JOURNAL.md`, `JOURNAL-B.md`, `JOURNAL-C.md`) and `formal/notes/`.

**Status: verdicts in for tracks 1–11 and 13; track 12 pending (shard C). Updated as probes land.**

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
| 2 | Trace representation | **works (all three)**; ℕ-ps discrete chosen for gate/cell proofs, ℝ for analog and fidelity; discretisation proved sound | `Core/Trace/{Discrete,Event,Real,Bridge}.lean`, `Core/Discretize.lean`, `Core/Circuit.lean` | ternary discrete model without separation: ~1 d (XSim probe running) | one substrate for B and C; their discrete proofs transfer to real time |
| 3 | Delay channels | pure, inertial, involution, corner-correlated: **all work** | `Core/Delay/{Pure,Inertial,Involution,Corner}.lean`, `Core/Fidelity.lean` | involution exp/log instance 1 h, full trace semantics 1–2 d; GLS sample-at-fire channel (probe running) | sound wire abstraction; exact bundling lemma |
| 4 | Kleene LUT | **works**, incl. a hazard audit of all 43 cell LUTs generated from the RTL | `Core/{Kleene,Lut,LutTree,Ternary,Bridge,LutCells,LutAudit}.lean`, `tools-A/lut_extract.py` | mechanised environment model (which multi-input changes the protocol allows): 1–2 d | decidable per-cell hazard/settling check |
| 5 | C-element | **works** (B) | `Cells/{CElemFn,CElemTiming,CTree}.lean`; A: `Core/{Ternary,XSim,LutAudit}` bd_c2 results | 1–2 d: port to Core, inertial/involution regimes, c3/c4 timing | INITs machine-checked; exact timing condition per cell (enabling input ≥ LUT + feedback delay, tight); the ack wait shown necessary |
| 6 | Latch / link | **works** (B) | `Cells/{Latch,LinkHandshake,Bundling}.lean` | 2–3 d: link stage = C-element + latch, W-bit lift | derived spec for tighten.py rules H/I/F (rules I and F each miss a term; guardband covers them today) |
| 7 | Arbiter | **works** for binary race, Kleene, handover (B); digital race is the primary model (PROGRAM.md item 4, owner 2026-10-27) | `Cells/{ArbBinary,ArbKleene,ArbHandover,...}.lean`; A: `Core/LutAudit` (same-sense tie hazard), `Core/Discretize` (`mutex_between`) | race windows for every property (B, phase 2) | exclusion tiers made precise; header claims corrected (runt from same-sense moves; handover exclusion is relative timing) |
| 8 | Composition | **works** at protocol level + Muller stage (C) | `Net/Handshake*.lean` | Kahn/gcd, forks/joins/merges (phase 3) | n-stage four-phase pipeline is a live FIFO given per-link obligations = rules I/H |
| 9 | Ring needs 3 stages | **works** (C) | `Net/Ring.lean` (`ring_three`, `k_tokens`: N ≥ 2k+1) | 1–2 d: tie to bounded-delay traces; H_ONE_TOKEN | the project's rule proved, and generalised to k tokens |
| 10 | Verified timing checker | **works** on toy netlists (C) | `Timing/{Semantics,Checker,CheckerToy,Rules}.lean` | 1–2 weeks for routed designs (phase 2); blocker is delay *data* (nextpnr SDF has slow max only) | rules E/A/J each get a proved counterexample; a checker makes them exact relative to a stated delay model |
| 11 | Netlist import | **works** (C): yosys JSON for 11 cells, and FASM read back from the bitstream for bd_c2/bd_c2n | `formal/tools/import/import.sh --check`, `formal/tools/fasm2lean/check.sh` | whole designs 2–3 weeks | proofs about generated terms: a flipped INIT bit fails the build; placer pin permutation is real and moves delay by up to ~0.5 ns |
| 12 | Other tools | pending (C) | | | |
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
- **ℝ → Bool** (`Core/Trace/Real.lean`, 511 lines, ~1.5 h): all of B0–B5,
  channel as a strictly increasing time warp (composition ~10 lines; the
  event-level reading is *proved* from it). B4 carries a named hypothesis
  `RealComplete` (Mathlib proves it; the module was not built yet). Costs:
  every "first event" argument needs completeness; concrete waveforms are
  verbose (ε choices); nothing computes, so no `decide`. Finding: the
  order-preserving warp can never lose a pulse, which is unsound for runts
  (w ≤ hi−lo); the over-approximation `Window lo hi` (output at t equals
  input at some instant in [t−hi, t−lo]) is the sound default for safety.
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
- **Involution** (`Core/Delay/Involution.lean`, Függer/Najvirt/Nowak/Schmid):
  all hypotheses are fields of `InvolutionPair`. Consecutive outputs cancel
  iff t(n+1) − o(n) ≤ −δmin (`cancel_iff`); output pulse width is strictly
  increasing in input width and shrinks continuously to 0 at the threshold
  (`pulseWidth_small`: the property that makes the model faithful to
  short-pulse filtration), in contrast to inertial (`inertial_gap`). Exp
  channel derived from a first-order RC (exp/log as hypotheses). **Transfer
  lemma:** with input separation T0 the involution channel is a bounded pure
  delay in [δ(T0), δ∞) with no cancellation, so cell proofs can use pure delay
  plus a separation hypothesis and need involution only for runts/hazards.
  For bd_arb: in the faithful model the arbiter loop has no bounded settling
  time, so handover exclusion cannot be unconditional (no MTBF: that needs
  the analog layer, shard B 7c/7d).
- **Corner correlation**: the independent band [fast-min, slow-max] is 3–4×
  wide (A-fidelity), so no matched-delay (bundling) condition is provable from
  independent bands; a shared-corner + local-scatter model is being probed.

### 2b. Circuit layer and discretisation
- `Core/Circuit.lean`: the owner's layering, representation-independent:
  `Gate := Beh W σ → Prop`, `Circuit := List Gate`, `Sat`, composition is
  conjunction (`sat_compose`), refinement, hiding internal wires by
  projection, assume-guarantee chaining. `Core/Trace/Bridge.lean`: event lists
  denote exactly the right-continuous ℝ → Bool functions with finitely many
  changes (`range_toFun`), so the trace choice locks nothing in.
- `Core/Discretize.lean`: if a continuous behaviour satisfies a bounded
  transport channel and its input has no two transitions within one quantum
  q, its grid samples satisfy the discrete channel with bounds
  [⌊lo/q⌋, ⌈hi/q⌉] (`chan_sample`), and likewise for gates and circuits
  (`circuit_sample`, `transfer`); joint separation over a gate's inputs is
  needed. Shard B's C-element theorems therefore hold at grid points of every
  separated continuous behaviour (`loop_of_continuous`). Without separation a
  sub-quantum runt is invisible: grant exclusion can hold at every grid point
  and fail between them (`mutex_between`) -- exactly the arbiter tie.

### 3b. Corner correlation (`Core/Delay/Corner.lean`)
With one shared PVT corner c and affine nominal delays per arc plus local
scatter |ε| ≤ κ, a bundling condition at both corner endpoints is equivalent to
it at every corner (`bundle_ratio_affine_iff`); monotone nominal delays alone
are not enough (`monotone_not_enough`). The project's guardbands become exact
scatter limits: skew.py rule E is sound iff κ ≤ 383/1927 ≈ 19.9% (`ruleE_sound`,
`ruleE_tight`); tighten.py rule A iff κ ≤ 1/11 ≈ 9.1% (`ruleA_sound_rel`,
`ruleA_tight`). Soft evidence that κ can be larger: the 7-link ring ratios
0.773..1.470 (cells/hw/README.md) imply κ ≥ 31% *if* ring-ratio spread is local
path scatter (`ring_kappa_lower`); rings measure absolute loop delay, not a
two-path difference, so this is not a refutation. **κ estimator** (`formal/tools-A/kappa/kappa.py`,
`notes/A-kappa.md`; `python3 kappa.py selftest`, `python3 kappa.py repo`): on
the 128-ring data the per-path κ ≥ 0.311 (7-link class; no common offset in
[0, 988] ps lowers it), so the *per-path* hypotheses of `ruleE_sound` and
`ruleA_sound_rel` are refuted. The rules compare two paths, so what they need
is κ on a path *difference*, which nothing in the repo measures: whether rules
E and A are safe is open. Proposed board experiment: a ring with a shared body
splitting into two tails rejoined at a scan-selected LUT mux (the shared body,
offset included, cancels), ≥ 64 pairs per class, 4 seeds, two temperatures; or,
cheaper, commit the `ro_many` per-ring raw logs (`kappa.py rawlogs` parses
them).

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
- **The research GLS's LUT delay can propagate an edge early**
  (`notes/A-gls-compare.md`, `tools-A/gls-compare/run_all.sh`). iverilog
  specify paths on `SLICE_LUTX` behave as "sample at fire": a change at t
  schedules an update at t+d that copies the function value when it fires,
  with no cancellation (fits 140/140 random traces; inertial 48, transport 4).
  An edge following an earlier change within d arrives early (reproduced: a
  rise at 1130 ps seen at 1244 ps through a 124 ps arc; down to 4 ps in the
  probe). GLS bundled-data margins can therefore be optimistic for glitchy
  data cones. Not measured: how often in a routed design. The GLS's annotated
  and baked builds also treat wire pulses differently (LUT-like vs transport).
- X-propagation of the GLS LUT/MUXF7 models equals Core `kevalSpec` on all
  43,767 vectors tested; bd_c2 single-input flips clean in both. bd_c2 a,b
  01→10 at q=0: Lean says hazard (X); the GLS shows a sharp skew threshold
  with a clean flip, and endless oscillation with a transport feedback wire.
- The research GLS's `SLICE_LUTX` builds the LUT mux tree with A6 at the
  leaves; the silicon has A6 at the root (UG474). Harmless for logic values,
  differs in timing (A-lut-tree).
- **bd_arb header: "a tie is resolved deterministically" is not true for a
  same-sense tie.** Both requests rising together from idle is a static hazard
  on q for either held q (`LutAudit.arb_tie_from_idle_hazard`; shard B 7a
  reached the same conclusion independently in timed form). Same-sense
  near-ties should be in the MTBF experiment (cells/verify/MTBF.md).
- **The losing grant can pulse without metastability**
  (`LutAudit.arb_grant_near_tie_runt`): q rising while r2 rises, with routing
  skew between the q branches. A2 = C(g2, A0) absorbs it, but bdc/emit.py's
  `won = g2 | ack` drives `index` directly, so index sees the pulse: an
  unchecked bundling margin, not a demonstrated failure.
- Shard B (7b): the bd_arbiter A0 hold relies on a fork ordering H_A0_FORK
  (A0's fall must reach ua2 before A0 → ustate → q → ugrant → g2 does).
