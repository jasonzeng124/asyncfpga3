# Gate-level formalization of asyncfpga3: feasibility

Owner's question: can this project's circuits be formalized at gate level and
proved correct (in Lean 4 or similar), and how feasible is that?
Program: `formal/PROGRAM.md`. Shard A writes this file from all three shards'
journals (`JOURNAL.md`, `JOURNAL-B.md`, `JOURNAL-C.md`) and `formal/notes/`.

**Status: a verdict for every track (1–13). Updated as the 48-hour phases (PROGRAM.md) land.**

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

## Status against the owner's three goals (2026-10-28 ~03:00 UTC)

1. **A correct model of the chip.** LUT as mux tree with per-pin delays, per-edge
   bands only where the data has them (prjxray has none: fast/slow corners only),
   pure/inertial/involution/SAF channels, shared corner plus local scatter κ.
   Proved since the last update: the involution transfer lemma (corrected,
   `InvolutionTransfer`), ternary soundness for transport/inertial channels with a
   positive lower bound (`TernaryChannels`), what a passing SAF GLS run implies
   (`GLSPass`, fixed 2026-10-29; `GLSPass2` for the per-pin fid model). Open (probes running 2026-10-28): full involution trace semantics,
   MUXF7/F8/CARRY4/LUT6_2 and flop/latch primitives in Core (today only in C's
   generated files), the per-pin fid GLS model, the CARRY4/latch/flop fidelity gaps of
   the research GLS (FOR-RESEARCH §8).
2. **A correct gcd.** Token level: the bdc graph computes the C gcd (C, `GcdHw*`).
   Circuit level, safety: C's `gcd_hw_circuit_safe''` -- every out0 latch of the
   concrete network is `Nat.gcd a b` (a, b < 2^31) under H_CELLS, H_BUNDLE,
   H_START_ONCE, H_WALK (first rig lap; H_BUNDLE on zero-delay traces, the
   physical -> zero-delay refinement is C's open 8x). Liveness: C's
   `gcd_hw_live_final` (8z) -- first out0 within an explicit bound, value gcd, under
   bounded-delay/env hypotheses plus one open network obligation H_NO_DEADLOCK'
   (8u's `gcd_hw_live` is likely vacuous; not cited). Routed timing: A's
   `Events8.design_verdict8` -- the 4 routed gcd_hw seeds are CLEAN at the slow and
   fast corners under SatPin, constant wires/reset, H_ARB, SelOK, SelPart, HDsub
   (HDsub and the bridges for the others are probes running). Arbiters (B,
   `OnGcdArbKappa`): all 36 gcd_hw arbiters safe for κ ≤ 16587/374773 ≈ 0.044 in the
   literal endpoint reading; box and SLOW-only checks unsound for κ > 0
   (`ConstraintsKappa`). These pieces are not yet one theorem: see
   `out/gcd_hw_hypotheses.md`.
3. **Reusable on other designs.** `out/HOWTO-new-kernel.md`. Run on collatz (4 seeds,
   verified toolchain): xevents5/7 CLEAN at slow and fast on every seed, 0 structural
   residuals; xaudit certifies one transaction at slowmax only. ipow and xorshift:
   probe running. C's capstone generator gives ipow at circuit level
   (`ipow_circuit_safe3`).

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
| 3 | Delay channels | pure, inertial, involution, corner-correlated: **all work** | `Core/Delay/{Pure,Inertial,Involution,Corner}.lean`, `Core/Fidelity.lean` | involution exp/log instance 1 h, full trace semantics 1–2 d; GLS sample-at-fire channel done (`Core/Delay/SAF.lean`); what a passing GLS run implies: `Core/Delay/GLSPass.lean` (audit REFUTED it 2026-10-29 as not compiling under autoImplicit=false; fixed by binding `d` in `skew_fval`, statement unchanged, 263 decls OK under the fixed check.sh) and, for research's current per-pin fid GLS, `Core/Delay/{GLSFid,GLSPass2}.lean` (one run fixes final values past the STA horizon; min/max runs bracket the band only for acyclic monotone nets with rising inputs; counterexamples otherwise) (only SAF silicon at the annotated delays; counterexamples inside the band; one-run-covers-band only for acyclic monotone nets with rising inputs) | sound wire abstraction; exact bundling lemma |
| 4 | Kleene LUT | **works**, incl. a hazard audit of all 43 cell LUTs generated from the RTL, and SI environment models (Env/EnvFast: bd_c2, latch, link W=1,2, merge) | `Core/{Kleene,Lut,LutTree,Ternary,Bridge,LutCells,LutAudit}.lean`, `tools-A/lut_extract.py` | mechanised environment model (which multi-input changes the protocol allows): 1–2 d | decidable per-cell hazard/settling check |
| 5 | C-element | **works** (B) | `Cells/{CElemFn,CElemTiming,CTree}.lean`; A: `Core/{Ternary,XSim,LutAudit}` bd_c2 results | 1–2 d: port to Core, inertial/involution regimes, c3/c4 timing | INITs machine-checked; exact timing condition per cell (enabling input ≥ LUT + feedback delay, tight); the ack wait shown necessary |
| 6 | Latch / link | **works** (B) | `Cells/{Latch,LinkHandshake,Bundling}.lean` | 2–3 d: link stage = C-element + latch, W-bit lift | derived spec for tighten.py rules H/I/F (rules I and F each miss a term; guardband covers them today) |
| 7 | Arbiter | **works** for binary race, Kleene, handover (B); digital race is the primary model (PROGRAM.md item 4, owner 2026-10-27) | `Cells/{ArbBinary,ArbKleene,ArbHandover,...}.lean`; A: `Core/LutAudit` (same-sense tie hazard), `Core/Discretize` (`mutex_between`) | race windows for every property (B, phase 2) | exclusion tiers made precise; header claims corrected (runt from same-sense moves; handover exclusion is relative timing) |
| 8 | Composition | **works** at protocol level + Muller stage (C) | `Net/Handshake*.lean` | Kahn/gcd, forks/joins/merges (phase 3) | n-stage four-phase pipeline is a live FIFO given per-link obligations = rules I/H |
| 9 | Ring needs 3 stages | **works** (C) | `Net/Ring.lean` (`ring_three`, `k_tokens`: N ≥ 2k+1) | 1–2 d: tie to bounded-delay traces; H_ONE_TOKEN | the project's rule proved, and generalised to k tokens |
| 10 | Verified timing checker | **works** on toy netlists (C) | `Timing/{Semantics,Checker,CheckerToy,Rules}.lean` | 1–2 weeks for routed designs (phase 2); blocker is delay *data* (nextpnr SDF has slow max only) | rules E/A/J each get a proved counterexample; a checker makes them exact relative to a stated delay model |
| 11 | Netlist import | **works** (C): yosys JSON for 11 cells, and FASM read back from the bitstream for bd_c2/bd_c2n | `formal/tools/import/import.sh --check`, `formal/tools/fasm2lean/check.sh` | whole designs 2–3 weeks | proofs about generated terms: a flipped INIT bit fails the build; placer pin permutation is real and moves delay by up to ~0.5 ns |
| 12 | Other tools | **works as a bound-finder, not a prover** (C): ~1 day per tool | z3/SMT and Storm give exact delay thresholds and witness traces in seconds for fixed integer delays (C-element: env min response ≥ feedback max; arbiter: server latency ≥ ~60 ps); nothing for all delays; UPPAAL/Workcraft/PRISM downloads blocked | zone-based dense time (TChecker) pending | find the bound fast, then prove it in Lean; A's Env/EnvFast is the kernel-checked SI analogue of Workcraft (~1000s of states vs 10^6+) |
| 13 | Literature | **done** | `notes/A-lit-1.md`, `notes/A-lit-2.md`, `notes/A-lit-3.md` (2026-10-27: paper hosts unreachable from the sandbox, entries tagged abstract/snippet/memory) | — | positioning; nothing like this exists in Lean or any proof assistant (no mechanised involution channels, no verified STA, no async Lean work); κ≈0.1 per arc plausible from 7-series intra-die data (5–8%), 0.2 conservative |

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
  `RealComplete`, since discharged from Mathlib (audit: this line was stale). Costs:
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
  increasing in input width and tends to 0 as the input width decreases to the threshold (`pulseWidth_small`: right-hand limit 0 at the threshold; continuity elsewhere not stated)
  (`pulseWidth_small`: the property that makes the model faithful to
  short-pulse filtration), in contrast to inertial (`inertial_gap`). Exp
  channel derived from a first-order RC (exp/log as hypotheses). **Transfer
  lemma, corrected and proved (`Core/Delay/InvolutionTransfer.lean`, answering the
  audit's OVERSTATED row).** `transfer_sep`: if consecutive inputs are at least S apart
  with S > D − δmin (D = max(δ∞↑, δ∞↓)), nothing cancels, each input transition gives
  exactly one output transition with delay in [min(δ↑, δ↓)(S − D), D], and the output
  is a `Pure.Chan` behaviour of the input with that band (`chan_sigOf`). The old
  wording (separation T0, band [δ(T0), δ∞)) was wrong in all three parts.
  `sep_threshold_sharp`: at 0 < S ≤ δ∞↑ − δmin evenly spaced inputs cancel, so the
  threshold is exact for symmetric channels. A concrete instance (`ratPair`,
  δ(T) = 2 − 1/(T+2)) shows the class is non-vacuous. `Core/Delay/InvolutionDMin.lean` removes the `IsDMin`
  hypothesis (δmin exists for every `InvolutionPair`, from its fields alone) and
  closes the asymmetric gap: S-separated inputs never cancel iff
  δ∞↑ − δmin < S and δ∞↓ − δmin ≤ S (`sep_threshold_exact`). Not covered: the
  filtered output under chained cancellation; an exp-channel instance.
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
`ruleE_tight`); rule A *with exact division Pd/5* iff κ ≤ 1/11 ≈ 9.1% (`ruleA_sound_rel`,
`ruleA_tight`); tighten.py's gate as coded (`max(int(0.2*t),200)`, SLACK = 0) is sound iff κ ≤ 25/276 ≈ 9.06% (`Core/Delay/CornerCode.lean`: `ruleA_code_sound`, `ruleA_code_tight`, worst case t_data 1004, t_req 1204, confirming the audit); with SLACK ≥ 1 (resize.sh's search) it is again κ ≤ 1/11. Assumed, not proved in Lean: Python's `int(0.2*t)` = ⌊t/5⌋ for 0 ≤ t < 2^50 (argument plus scans). Soft evidence that κ can be larger: the 7-link ring ratios
0.773..1.470 (cells/hw/README.md) imply κ ≥ 31% *if* ring-ratio spread is local
path scatter (`ring_kappa_lower`); rings measure absolute loop delay, not a
two-path difference, so this is not a refutation. **Correction (2026-10-27 ~07:00):** the ring ratios behind κ ≥ 0.311 are
measured/predicted against SDFs written *before*
`patches/nextpnr-xilinx-lut-perm-sink.patch` (shard C,
`notes/C-10c-prjxdelay.md`): those SDFs charged 0–150 ps for permuted LUT pins
where the routed hop is ~295 ps, on ~85% of chain hops. Against corrected
predictions, comparable rings agree to 1.1% (prjxray median) / 6.7% (current
SDF), population against population. So the 0.311 bound measures that SDF bug,
not silicon scatter, and does **not** refute the per-path hypotheses of
`ruleE_sound`/`ruleA_sound_rel`. κ (per path and on differences) is unmeasured
on the current toolchain; the per-ring data and bitstreams needed to redo it
are not in the tree.
**κ estimator** (`formal/tools-A/kappa/kappa.py`,
`notes/A-kappa.md`; `python3 kappa.py selftest`, `python3 kappa.py repo`): on
the 128-ring data the per-path κ ≥ 0.311 (7-link class; no common offset in
[0, 988] ps lowers it), so the *per-path* hypotheses of `ruleE_sound` and
`ruleA_sound_rel` are refuted. The rules compare two paths, so what they need
is κ on a path *difference*, which nothing in the repo measures: whether rules
E and A are safe is open. `Core/Delay/CornerDiff.lean` makes this exact: both
rules are sound under a *difference* scatter bound κd with the same limits
(`ruleE_sound_diff`, `ruleA_sound_diff`, both tight); per-path κ implies κd but
not conversely (`diff_not_imp_scat`), and the ring pair bound is attained
(`ring_kappa_iff`), so ring data cannot decide κd either way. Proposed board experiment: a ring with a shared body
splitting into two tails rejoined at a scan-selected LUT mux (the shared body,
offset included, cancels), ≥ 64 pairs per class, 4 seeds, two temperatures; or,
cheaper, commit the `ro_many` per-ring raw logs (`kappa.py rawlogs` parses
them).

### 4. Kleene LUT
- `Core/Kleene.lean`, `Core/Lut.lean`: shared K3 and LUT API (INIT as
  `BitVec (2^k)`, I0 = LSB, LUT6_2 O5/O6). Kleene eval equals the INIT-table
  definition for every k; monotone; single-input change never hazardous
  (`no_static_hazard_single`); two-input change can be — on the C-element itself,
  a b 01→10 with q=0 gives X (`Init.bd_c2_two_change_hazard`). 19 cell INIT constants (23 `*_eval` theorems)
  transcribed with `*_eval` theorems that confirm the RTL header comments.
- `Core/LutTree.lean` (gate fidelity): the LUT as a pass-transistor mux tree.
  Mux-tree Kleene eval = INIT-table semantics for every k, INIT, input
  (`evalTree_eq_tableEval`); tree order irrelevant; with arbitrary per-mux
  delays a single-input change with equal endpoint values never glitches
  (`sic_glitch_free`), under named hypotheses `H_mux_kleene`, `H_sram`.
- `Core/Ternary.lean` + `Core/TernaryChannels.lean`: Eichelberger ternary
  simulation is sound for discrete-time causal behaviours (`Causal`, which
  includes GMW, `gmw_causal`, and discrete transport with lower bound ≥ 1
  step, `causal_of_transport`), and, in continuous time, for every network
  whose nodes are zero-delay gates followed by `Core/Delay` transport
  (`Chan`) or inertial (`InertialRD`/`BoundedInertial`) channels with a
  positive lower delay bound (`ternary_noGlitch_channels`). Settling
  (algorithm B) holds within `|ν|·D` for both channel kinds, `D` the largest
  upper delay bound (`ternary_settle_channels`; for inertial channels via
  `SettlesWithin`, not `Stale`). A zero lower delay bound makes it unsound
  (`zero_delay_chan_unsound`, `zero_delay_inertial_unsound`); grid samples
  of continuous behaviours are `Causal` only under separation
  (`causal_of_sample`; counterexample `sample_not_causal`). bd_c2's every
  single-input flip settles with no static hazard. This is a decidable,
  delay-independent per-cell check.

### 4b. Whole-cell and whole-design checks (A, phases 1–2)
- **Substrate** (`Core/Substrate.lean`, `Substrate/{Chan,CornerNat,Real,Legacy}.lean`;
  guide `notes/A-substrate.md`): the one API for B and C. Delay relation
  `Win lo hi` (fixed ⊂ transport ⊂ `WinR` ⊂ `Win`; GLS SAF ⊂ `WinR 1 d`), composes
  with summed bounds; the corner model in ℕ ps with an endpoint check sound for
  every real corner and real delay within κ (`endpoints_sound_real`).
- **Timed ternary simulation** (`Core/XSim.lean`): sound for every behaviour in
  the bands, feedback allowed; `decide +kernel` verdicts are theorems (130 gates
  × 200 steps in 180 s).
- **SI environment model** (`Core/Env.lean`): bd_c2, the bd_latch pair and
  bd_link (1-bit) are speed-independent under rules H, L and isoEn, each proved
  necessary. Limit: ~1000 states per kernel certificate (a bit-packed checker,
  EnvFast, is in progress).
- **xaudit** (`lake build xaudit`; `formal/tools-A/xaudit/run_all.sh`): a
  compiled whole-design X/hazard audit whose engine is proved equal to XSim and
  to Ternary A/B; the JSON parser and the compiler are trusted, one verdict is
  re-checked by the kernel. On a hand-flattened 3-stage pipeline: clean at one
  corner, hold-violation control flagged, and a C-element race flagged when
  the cell's own feedback is slower than a neighbour's response (an obligation
  not found among tighten.py's rules). Not run on gcd_hw yet (no routed JSON in
  this sandbox; loops need a FIFO-aware abstract domain for precision).
- **xaudit on the real routed gcd_hw R5** (`notes/A-xaudit-gcd.md`, 4 seeds,
  prjxray per-arc bands via the research branch's `xray_delay.py`; 47,894
  wires, 4,599 storage nodes): with bands ≤ 2% wide it **certifies a whole gcd
  transaction** (a=7, b=0) for every delay in band and every power-up state, and
  the negative control is flagged. At prjxray's one-corner widths (~17%) the
  window domain loses precision after 4–11 ns: imprecision, not a race (520
  concrete samples correct; no static own-feedback candidate). With fast and
  slow corners mixed per element, 4–10 own-feedback race candidates per seed;
  one reproduced concretely (a 9 ps runt in `ucontrol_merge4.uarb1.ua2`, seed d).
  The C-element feedback assumption holds at each corner and fails once corners
  mix, so it rests on the shared-corner hypothesis and on κ.
- **gcd_hw control at real prjxray widths** (`Core/XAudit/Events4.lean`,
  `notes/A-events4.md`; seed d only; analysis in Python over a recogniser shared
  with `lake exe xevents4`, rule arithmetic proved, end-to-end `Beh4.safe` still
  open): at one corner, 402/405 C-element stages clean for all time and all
  select sequences (Back margin ≥ 961 ps slow / 434 ps fast). With fast and slow
  mixed per element: 331/405 clean; the two own-feedback races fbrace found, plus
  guarded-ack races (arbiter A_b to −1278 ps, umux3/umux4 −51..−187 ps) and
  a FASTFALL delay-line finding that turned out to be a model artefact
  (Events5: the shared chain after two taps meet was double-counted; corrected,
  64 → 1/4/0/0 lines per seed). All of these need corner mixing, i.e. local
  scatter, which is unmeasured. **Events5** (all 4 seeds, strict margins,
  `Beh4.safe` proved, so the verdict is a theorem about the model; the netlist
  link `design_beh4` and the guard timing are still open): slow and fast corners
  402/405 on every seed (3 = the cascaded arbiter, outside the domain); at
  skew.py's own guardband (one die, 0.668–1.0 × slow max) four items fail:
  three arbiter re-arm entries on seed d (−52, −26, −9 ps) and the rig's `uenv1`
  (−19 ps, seed 5). The real FASTFALL residual is rule F's missing in-flight term
  at the head of `bd_delay_gated` (g[0] is a plain buffer): −365/−726 ps on
  mixed dies, not reached at the rig's ~260 ns source low phase.
  **Events6** (`lake exe xevents5`): the netlist link `design_beh4` is proved
  (per-pin, no `H_ATOMIC_LUT`), so the checker's verdict on the parsed routed
  netlist is a theorem, but for gcd_hw it is still conditional on 45 residual
  obligations per seed (branch labels through merges, the 3-way merge, the
  cascaded arbiter, and 6 guarded acks arriving through delay lines whose
  obligation is expected to be false until the domain gets a guarded
  multi-copy pin kind). No seed is certified yet: about 3 days of work left.
- **Per-pin race checker** (`lake exe xevents2pin`, `Events2Pin*.lean`): sound
  without the all-pins-at-one-instant assumption (`H_ATOMIC_LUT`); with prjxray
  per-physical-pin bands, per-pin skew costs 11–79 ps of margin. One corner: no
  failing pin on ring3/pipe3/gcd_hw (4 seeds). Mixed corners: 1–4 pins per seed
  on ring3/pipe3, 6–8 on gcd_hw. Site-pin differences (−468..+308 ps) make any
  SDF-fed race check unreliable.
- **Event-count domain** (`Core/XAudit/Events*.lean`, `Events2*.lean`;
  `lake exe xevents`): per-wire transition counts with min-plus timing (timed
  marked graph) over the behaviour's own monotone warps. Closed and open
  Muller networks of real-INIT n-input C-elements with delay chains stay
  binary for all time under explicit decidable obligations (`Back`/`Race`:
  own feedback hi ≤ the lo-sum of the loop back through each neighbour); ring3
  and pipe3 period bounds [135, 171] steps, both attained, via exact cycle-ratio
  certificates. Finding: at an open boundary the race margin is only the port
  route's lo plus the environment's response minus feedback hi (30 ps + env on
  illustrative bands, vs 930 ps inside). Choice (mux/steer) and bundling inside
  loops are the remaining steps toward gcd_hw.

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

### Against the research GLS at 6524fa3 (probe Fid3, 2026-10-29; iverilog/Float experiments, not theorems; notes/A-fid3.md, run: `formal/tools-A/glsdiff3/run-1029/run.sh`)

Grades: A = measured on this part or fixed by a vendor document; B = documented structure or faithful physical model, unmeasured; C = unsourced assumption or known wrong.

| primitive | formal model (Lean) | research GLS (6524fa3, `GLS_MODEL=fid`) | silicon: what is known (source) | grade formal / GLS | test that would settle it |
|---|---|---|---|---|---|
| **LUT function and X** | Kleene mux tree from INIT, A6 at the root (`Core/LutTree`, `Lut.keval = kevalSpec`); hypothesis `H_mux_kleene` (a mid-rail select with equal data passes the data) | `?:` mux tree on the delayed pins (leaf-first; the order does not change values). Equal to Lean on 43,767/43,767 vectors | Structure: LUT6 = two LUT5 + A6 mux (UG474). Single-input change does not glitch (P. Alfke, comp.arch.fpga, informal, not a datasheet). Mid-rail select behaviour: no source | B / B (same model) | board: masked-pin toggle into a fabric edge counter (A-fidelity); SPICE of a pass-gate mux leaf |
| **LUT per-pin arcs** | per-pin bounded transport `[lo, hi]` then the zero-time function (`Events2Pin`, `Pure.Chan`) | per-pin transport, one SDF point per pin (`FID_LUT6`), 1 ps output sampler; `+FID_LEVEL_PS` for internal skew (default 0) | prjxray LUT arcs are flat per output; pin dependence is in site-pin delays (A-fidelity). Internal tree skew: unknown | B / B. GLS = one point of Lean's band (60/60 + 60/60) | per-pin delay ring (A-fidelity) |
| **LUT glitch / runt** | transport passes every pulse; inertial and involution channels are available (`Delay/{Inertial,Involution}`); which one is silicon is a hypothesis | every pulse ≥ 1 ps passes (transport) | no 7-series LUT pulse-rejection figure found (research f3_model.md, A-fidelity: estimated 15-50 ps from R·C, not measured) | B / B: transport is the hazard-pessimistic side; it is optimistic only for a proof that needs a narrow pulse to die | pulse-shrink experiment: XOR with a k-LUT-delayed copy into N hops and a toggle counter (A-fidelity R1) |
| **routing, buffered pips** | `Fidelity.DelayBound` per sink arc [FAST_MIN, SLOW_MAX]; Elmore `rcBound` with κ; shared corner + scatter \|ε\| ≤ κ (`Corner.lean`) | `fid/xray_delay.py`: prjxray `timing.py` RC tree (Buffer per buffered pip, Elmore over the downstream subtree, site-pin delays, fanout C). Transport ICBUF per sink. One SDF column (or `band` = one shared lerp) per run | all 3737 INT_L pips are `is_pass_transistor = 0` (A-fidelity scan of prjxray-db). prjxray's model is ±1.5% from Vivado (not silicon). Board: n=128 ring periods fall inside the summed bands (FEASIBILITY) | B / B for the band. GLS **scatter is unbounded Gaussian**, outside every κ-bounded theorem (FOR-RESEARCH §8, unchanged) | already partly done (ring periods); per-wire scatter from more rings |
| **routing, pass-transistor pips** | zero-delay alias (`H_alias`) | `PassTransistor(R)` in the RC tree (the only ones are fixed CLB site-pin aliases with `delay=null`, `res=0`) | prjxray-db: pass-transistor pips exist only as fixed tile-wire→site-pin aliases on this part (A-fidelity R2) | B / B (agree) | not separately observable |
| **MUXF7/F8** | `kmux` (Kleene), settle within hi; `H_muxf_kleene` for S toggles with D0 = D1 | `FID_MUX2`: per-pin transport, Kleene `?:` | structure per UG474; S-toggle with equal data: no source | B / B | board: D0 = D1 = 1, toggle S at ring rate, count OUT falls (expect 0) (A-fidelity M1) |
| **CARRY4** | Gen/Netlist: UG474 MUXCY/XORCY equations gate by gate, Kleene; band per arc | **per-(pin, output) transport, then the same equations** (78de9c2). E1: 60/60 exact on multi-pin random traces | MUXCY/XORCY structure (UG474); arcs per (pin, site output) from prjxray SDF. Note CARRY4 is read-once (each pin has one path to each output), so per-(pin, output) transport is what a transport cascade gives; the SDF arcs need not be additive (they end at site pins) | B / B (now agree; was GLS C) | carry-chain TDC style: launch an edge into CIN/S, sample the CO taps (standard TDC papers) |
| **FF (FDRE/FDSE) function and X** | master-slave Kleene tables `FDRE_M`, `FFQ_SYNC` (Gen/Netlist; PrimsSeq probe in progress) | `if (SR)` / `if (CE)` (default), `sr === 1` / `if (ce)` (fid): **x on SR or CE is read as 0** | an x (mid-rail or unknown) SR/CE gives an unknown next state; nothing documents a definite value | B / **C** (GLS wrong, optimistic: hides X). Fix tested: `patch/prims_x.diff` | `run-1029/run.sh` E7: F1, F2 must print x |
| **FF timing (CK→Q, setup/hold, aperture, min pulse width)** | named hypotheses only (`H_HK_STA`, rig `idx_setup`); no aperture or metastability model in Core | transport CK→Q; SDF SETUPHOLD aperture (negative SETUPHOLDs read since 666ea57) with an old/new choice and t_r = TAU_FF·ln(ap/2\|δ\|), TAU_FF = 75 ps; CK min pulse width TMPW 70 ± 20 ps | SETUPHOLD per pin in prjxray-db (Vivado numbers). Flop τ: Beer et al. ASYNC 2010, 57/51/73 ps at 130/90/65 nm; no 28 nm figure. Min pulse width: none found in prjxray-db (research could not read DS187) | B (timing as hypotheses) / C (TAU_FF, TMPW assumed) | hw/arb_mtbf-style synchroniser sweep (MMCM fine phase shift) for TAU_FF; CK runt sweep for TMPW |
| **latch (SLICE_LATX, LDCE/LDPE)** | `LDCE_INIT` via `Lut.keval` | per-pin transport (78de9c2); **X pessimistic** (closed + CE = x → x; CLR = x → x even when the result is SRVAL); no metastability at gate close (stated) | UG474: latch-mode storage element, gate on CK, enable CE, async SR. **No design uses LDCE/LDPE**: `bd_latch` stores on LUTs (cells/rtl/bd_latch.v header) | B / C (pessimistic, harmless today). Fix tested: `patch/prims_x.diff` | E7: L1-L3 must print 0 |
| **LUT state loop: C-element, LUT latch, arbiter q** (metastability) | B: `ArbInvolution` (`stF_runt`), `CElemInvolution.orb`; proved: a critical runt s* exists in (δ∞ − δ(0), δ∞) (`arb_eternal`). Float orbit (§3): s* = 0.50-0.58·TLOOP, deterministic either side; near s* the loop **circulates a pulse train** and resolves with TAU_eff ≈ 1.2-17·TLOOP | `FID_RESOLVE` on self-loop LUTs (gen.py): runt p < TLOOP decided at **TLOOP − WIN/2** (349 of 424 ps), N(0, WIN/4) noise, t_r = TAU·ln(WIN/2\|δ\|), TAU = WIN = 150 ps (assumption). During resolution the node **holds a clean value** (default) or x (`+META_X=1`); one runt reaches fanout, echoes ignored. Multi-cell loops get no resolver | none measured. Without the resolver (`+META_OFF=1`) the GLS's own transport loop circulates the runt forever with period TLOOP (E4: Q 1124↑ 1473↓ 1548↑ 1897↓ …), i.e. the echo is physical and the "rejection" is a modelling choice | B (Lean channel family, unmeasured) / **C** (centre has no derivation; TAU optimistic under involution; clean hold hides the pulse train) | **hw/arb_mtbf**: sweep the r1→r2 skew (MMCM fine phase or IDELAYE2 taps) and record P(r1 wins): the 50% point is at TLOOP/2 (involution) or TLOOP − WIN/2 (GLS), 137 ps apart at TLOOP 424; count q toggles per race with a ripple counter (train vs single runt); resolution-time histogram for TAU |
| **BUFGCTRL** | not modelled (clock only in rigs) | transport I0→O (fid) | no BUFG min pulse width in prjxray-db | — / B | — |
| **DSP48E1** | not modelled | combinational and registered modes; still iverilog module paths (SAF) | — | — / C (SAF) | only if a design's bundled cone runs through a DSP |

### Earlier table

(From `notes/A-fidelity.md`, `A-lut-tree.md`, `A-kleene-lut.md`; to be
completed with shard B's cell notes.)

| primitive | model in Lean | fidelity | hypothesis | how to test |
|---|---|---|---|---|
| LUT function | Kleene mux tree from INIT | logic exact (INIT = function, proved for all k) | `H_mux_kleene`: a mid-rail select with equal data inputs passes the data, no charge-sharing dip; `H_sram` | board: masked-pin toggle into a fabric edge counter; SPICE |
| LUT timing | per-mux delays, arbitrary | order of tree (A6 at root per UG474) only affects delays | prjxray LUT arcs are flat; pin dependence is in site-pin delays (A1 slow ≤ 0.516 ns) | per-pin delay ring |
| routing pip | bounded transport [fast-min, slow-max] per sink arc | all INT_L pips in prjxray zynq7 are buffered; RC tree responds monotonically (no glitch) | band from prjxray via Elmore per sink arc (not summed per pip); shared corner + local scatter (pending) | n=128 ring periods inside summed bands |
| MUXF7/F8, CARRY4 | settle within hi | only in datapath cones, never in control | "anything before hi" | — |
| FF (FDRE) | — | only `bd_mlink` and test rigs | standard setup/hold (slow corner only in prjxray) | — |
| delay model in the GLS at research 5d535d7 (superseded: see the 6524fa3 table above; CARRY4/latch early edge FIXED under fid in 78de9c2) | default: sample-at-fire (SAF) on every specify path; `GLS_MODEL=fid`: per-pin transport for LUT and MUXF7/8 (equal to Lean's per-pin transport on 60/60 + 60/60 traces), still SAF for CARRY4, latch, DSP, BUFG | default disagrees with silicon (early edges, swallows runts); fid fixes LUT/MUXF but CARRY4 still propagates edges early (23 ps after the cause through a 223 ps arc) | — | FOR-RESEARCH §8 |

Note: prjxray-db's `timings/*.sdf` triples are (FAST)(SLOW), not rise/fall;
a standard SDF reader misreads them (A-fidelity).

## Findings for the main project (to verify, not confirmed defects)
- **C-element own-feedback obligation, unchecked by the flow** (two shards,
  independently). A's `xaudit` flags C-element glitches in a 3-stage pipe
  when a cell's own feedback is slower than a neighbour's response; C (track 8
  Muller timed, `H_FB_BEFORE_INPUT` / `FbBound`: feedback hi < lo-sum of each
  neighbour loop, strict) derives the same bound and finds it
  placement-dependent: the shortest LUT-to-LUT route of 11b fails it, the
  seed-1 route passes. No tighten.py rule checks it.
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
- **bd_mux: three obligations the RTL header does not state**
  (`EnvFast/Mux*.lean`, notes/A-envfast-2.md): return-to-zero (the previous
  token's x_ack/y_ack fall before the next z_ack rises; shard B's H_MUX_RTZ,
  found independently); select held until ctl_req's fall has passed the join
  LUT uj1 (the header says until ctl_ack falls); fork conditions on the z_ack
  and ctl_req branches. Each is shown necessary. bd_merge with its data mux is
  sound under exclusivity and the matched delay; an earlier `selFast`
  obligation is withdrawn (it only bites while the output window is closed).
- Shard B (7b): the bd_arbiter A0 hold relies on a fork ordering H_A0_FORK
  (A0's fall must reach ua2 before A0 → ustate → q → ugrant → g2 does).
