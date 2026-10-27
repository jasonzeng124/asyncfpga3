# A / substrate: one discrete substrate, one delay relation, one delay model

Phase 1, shard A (PROGRAM.md, "After the feasibility verdicts", Phase 1, item A).
This is the API that shards B (`Cells/`) and C (`Net/`, `Timing/`) port to.

## Files

| file | content | imports |
|---|---|---|
| `formal/lean/Formal/Core/Substrate/Chan.lean` | `Sig`, `KSig`, `Covers`, edge vocabulary, **`Win`**, `WinR`, `Start`, inclusions and strictness, window algebra, stability, causality, bundling, K3 view, `DNet` (nets and their behaviours) | core Lean only: `Trace.Discrete`, `XSim`, `Delay.SAF` |
| `formal/lean/Formal/Core/Substrate/CornerNat.lean` | the corner model in ℕ ps: `Kappa`, `CArc`, `Corner`, `Scat`, `CornerModel`, `Realizes`, bands, paths, endpoint sufficiency | `Mathlib.Tactic.{Linarith,Ring}` |
| `formal/lean/Formal/Core/Substrate/Real.lean` | the ℝ bridge: discretisation into `Win`/`WinR`/`DNet`, ℕ↔ℝ corner model | `Discretize`, `Delay.Corner`, `FieldSimp`, Archimedean ℝ |
| `formal/lean/Formal/Core/Substrate/Legacy.lean` | bridges to B's `WinDelay`/`Loop` and C's `BoundedDelay`/`Run`/`shift` (porting aid; delete with `Prelim`) | `Cells.CElemTiming`, `Net.Prelim`, `Timing.Semantics` |
| `formal/lean/Formal/Core/Substrate.lean` | the API module (imports Chan, CornerNat, Real; NOT Legacy), the ℝ bridge stated once, end-to-end bundling examples | the three above |
| `formal/lean/Wip/Substrate.lean` | two open statements (`sorry`), not built | |

Check (from `formal/lean`, dependency order):

    ../check.sh Formal/Core/Substrate/Chan.lean Formal/Core/Substrate/CornerNat.lean \
      Formal/Core/Substrate/Real.lean Formal/Core/Substrate/Legacy.lean Formal/Core/Substrate.lean

Result (2026-10-27): every file checks, `[audit] 1391 declarations checked`, `[check] OK`
(no sorry, no axiom beyond propext / Classical.choice / Quot.sound, no native_decide).
Chan.lean checks in about 2 s, the whole set in about 30 s.

No existing file was edited.

## 1. Time, signals, the delay relation

- Time is `Nat`, one step = 1 ps (**H_GRID**). `Sig := Nat → Bool`
  (`= TraceDiscrete.Sig = Cells.CElemTiming.Trace = Net.Trace`, all definitionally equal),
  `KSig := Nat → K3` (Core's `K3`), `Covers a x := ∀ t, a t ⊑ ofBool (x t)`.
- **`Win lo hi i o`** (THE relation): `∀ t, hi ≤ t → ∃ s, t ≤ s + hi ∧ s + lo ≤ t ∧ o t = i s`.
  The output at `t` shows the input from some step in `[t-hi, t-lo]`. The delay may vary from step
  to step, so this is non-FIFO. Before `hi` the output is unconstrained (power-up).
- `WinR lo hi i o` := `XSim.WinCh` (truncated subtraction: the input is read as constant before
  time 0). `winR_iff : WinR ↔ lo ≤ hi ∧ Win ∧ Start`.

Inclusions, all proved (`⊊` means the converse fails, with a proved counterexample):

    delay d ⊆ Transport lo hi ⊊ WinR lo hi ⊊ Win lo hi   (lo ≤ d ≤ hi)
      delay_transport', transport_winR, winR_win; winR_not_transport, win_not_winR
    shift (o (t+d) = i t, prefix free) ⊆ Win               shift_win
    DelaySAF.saf d ⊆ Transport 1 d ⊆ WinR 1 d             saf_winR, saf_win
    inertial δ ⊄ Win lo hi  (pulse with hi-lo < w ≤ δ)     inertial_not_win
    WinR lo hi ⊊ Net.BoundedDelay lo hi                    winR_boundedDelay, boundedDelay_not_winR (Legacy)
    Win lo hi = Cells.CElemTiming.WinDelay lo hi           win_iff_winDelay (Iff.rfl, Legacy)

Toolkit for `Win`: `win_le`, `win_total_iff` / `winR_total_iff` (non-vacuity: every input has an
output iff `lo ≤ hi`), `win_mono`, `win_comp`, `winR_comp`, `win_map`, `win_stable`,
`win_stableFrom`, `win_after`, `winR_after`, `win_bundle` (discrete bundled-data lemma),
`win_covered`, `winR_covered` (the X-window of `XSim` lies below every behaviour), `winR_exact`.

Nets: `DNet N` (driven flag, zero-delay gate function, `lo`, `hi` per node; same shape as
`Discretize.DCircuit`). Behaviours: `Beh` (Win), `BehR` (WinR), `BehT` (Transport), `BehFixed`
(one delay per node). `DNet.refines`: a property proved for all `Beh` holds for every `BehR`,
`BehT` and `BehFixed` behaviour. `ofLGates`, `ofLGates_relW`: `XSim`'s LUT-gate lists as a `DNet`,
so `XSim.sound` applies to `BehR` behaviours.

### Recommendation: which relation to state theorems with

**State hypotheses with `Win`**, and with `WinR` only where the proof needs the quiescent start
(C's timing runs need it, `winR_quiet`; B's cell theorems mostly do not). Reasons:
1. A theorem with a `Win` hypothesis covers fixed delay, transport, `BehFixed` (C's `FixedRun`
   reading) and the research GLS's sample-at-fire LUT channel (`saf_win`) at once.
2. It is sound for runts and glitches. It can drop a pulse narrower than the spread, as transport
   can, and it can also create a glitch from a clean edge (`winR_not_transport`), which a slow,
   noisy edge on a real wire can do. Inertial filtering is never derivable from it
   (`inertial_not_win`), which is right, because proofs must not rely on filtering
   (A-delay-inertial).
3. It is compositional: `win_comp` gives summed bounds. Whether C's `BoundedDelay` composes
   with summed bounds is open (Wip).
4. The discretisation theorem produces `Win` with no rest hypothesis (`chan_sample_win`).
5. `XSim` (timed ternary simulation) is proved sound for it.

`Net.BoundedDelay` (shard C) is a strictly larger set than `WinR`: it also lets an output hold an
old value for as long as the input keeps chattering. That is an inertial-like behaviour, and no
bounded-delay wire has it (`boundedDelay_not_winR`). So C's theorems about `BoundedDelay` still
apply to substrate behaviours (`runOfWinR`). New theorems should take `Win`/`WinR` hypotheses,
which are closer to the silicon and compose.

## 2. The corner model (ℕ ps, decidable)

- `Kappa` (κ = num/den, 0 ≤ κ ≤ 1), `CArc` (fast `F` ≤ slow `S`, ps), `Corner` (weights `w0, w1`,
  c = w1/(w0+w1)), `nom c a = w0·F + w1·S` (W times the nominal delay).
- `Scat κ c a d`: `(den-num)·nom ≤ den·W·d ≤ (den+num)·nom`, which is `(1-κ)D(c) ≤ d ≤ (1+κ)D(c)`
  with the denominators cleared. Decidable.
- `CornerModel A` (an `arc : A → CArc` and a `κ`), `RealizesAt c d`, `Realizes d := ∃ c, RealizesAt c d`,
  `RealizesOn c d l` (decidable for a given `c`). Non-vacuous: `realizes_fast`.
- Bands, rounded outward to whole ps: `bandLo κ c a = ⌊(1-κ)D(c)⌋`, `bandHi = ⌈(1+κ)D(c)⌉`,
  and the corner-independent `indLo = ⌊(1-κ)F⌋`, `indHi = ⌈(1+κ)S⌉`.
  `scat_band`, `band_le`, `band_sub_ind` (the corner band lies inside the independent band),
  `scat_ind`.
- Composition: `CArc.add`, `pathArc`, `CornerModel.path`, `nom_add`, `scat_add`, `scat_path`,
  `nom_path`, `pathDelay`, `sumOver`.
- **Endpoint sufficiency**: `EndpointOK κ D R m` is
  `(1+κ)·D + m ≤ (1-κ)·R` at the fast AND at the slow endpoint. It is decidable.
  `endpoint_nom`, `bundle_endpoints`, `bundle_paths`, `bundle_realizes` give
  `data delay + m ≤ request delay` at every corner, for every scatter ≤ κ.
  `bundle_band`: with margin `m + |P| + |Q|`, one ps of rounding per arc, you get
  `Σ bandHi(data) + m ≤ Σ bandLo(request)` at every corner. That is the hypothesis of
  `win_bundle`. `independent_implies_endpoint`. `imux_example_nat`: kernel `decide` shows that one
  IMUX against two IMUX passes the endpoint check at κ = 1/5 and fails the independent check.

### ℝ link (Real.lean)
- `Kappa.toReal`, `Corner.toReal`, `CArc.toArc : Corner.Arc`, `kappa_lo_real`, `kappa_hi_real`,
  `nom_real`, `scat_real`, `realizesAt_real`: an ℕ realisation is an ℝ `Corner.Scat` realisation.
- `endpoint_real`, **`endpoints_sound_real`**: the ℕ check `EndpointOK` implies the bundling
  inequality for every REAL corner `c ∈ [0,1]` and every REAL delays within scatter κ, through
  `Corner.bundle_ratio_affine`. The die's corner needs no rationality and no rounding assumption.
- `pathArc_F`, `pathArc_S`: ℕ path endpoints = `Corner.pathF` / `Corner.pathS`.
- `ind_encloses`, `band_encloses`, `corner_chan_sample_ind`, `corner_chan_sample_band`: a real
  corner-model channel, sampled at 1 ps, is a `Win` channel with the ℕ band.
- In `Substrate.lean`: `bundle_real_of_check` (real time, any real corner: `Corner.bundle_corner`
  with both endpoint hypotheses discharged by the ℕ check), `win_bundle_corner` (discrete, both
  wires as corner-band `Win` channels at one corner), `tight_band_bundle` + `floor_ceil_exist`
  (any real corner, whole-ps bands tight to 1 ps).

### What a checker (C, phase 2) should consume
Per arc, the `CArc` endpoints from prjxray (or nextpnr SDF, if it ever has both columns), plus one
`Kappa`. Per bundling pair (data path P, request path Q, settling margin), decide
`EndpointOK κ (M.path P) (M.path Q) (m + |P| + |Q|)`. Its soundness is `bundle_band` (discrete
traces), `bundle_paths` (ℕ delays) and `endpoints_sound_real` (real delays). A checker that ignores
correlation uses `indLo`/`indHi` per arc. The corner model never rejects what that accepts
(`independent_implies_endpoint`).

## 3. The ℝ bridge (Real.lean, summarised at the top of Substrate.lean)

- `chan_sample_win`: continuous FIFO channel `[lo, hi]` with **H_SEP** on its input gives
  `Win L H` on the grid, for `L·q ≤ lo`, `hi ≤ H·q`. No rest hypothesis, and no `L ≤ H` hypothesis
  (it is derived). `chan_sample_winR` gives `WinR` with **H_REST**.
- `circuit_sample_win` (`GridBounds` + `Sep` on each excitation) gives `(C.toDNet L H).Beh`
  of the samples. `circuit_sample_winR` gives `BehR` (via `Discretize.circuit_sample`).
  `dcircuit_beh_iff`: `Discretize.DCircuit.Beh` is `DNet.BehT`.
- `transfer_win`, `transfer_win_invariant`: anything proved for all `DNet.Beh` holds of the samples
  of every separated continuous behaviour.
- `invariant_real_time`: with joint separation and rest, a grid invariant holds at every real
  time. The Archimedean witness that `Discretize.invariant_everywhere` took as a hypothesis is now
  discharged.
- Limits, unchanged: without separation the transfer is false (`Discretize.tie_counterexample`,
  `mutex_between`). The ternary route (`chan_sample_hull`, `XSim`) is the sound one for
  sub-quantum ties.

## 4. Porting guide

### Name map (old → substrate)

| old | new | how |
|---|---|---|
| `TraceDiscrete.Sig`, `Cells.CElemTiming.Trace`, `Net.Trace` | `Substrate.Sig` | defeq |
| `Net.rises/falls/changes/stableOn` | `Substrate.rises/falls/changes/stableOn` | same definitions; `changes_iff_tr` |
| `Cells.CElemTiming.WinDelay lo hi` | `Win lo hi` | `win_iff_winDelay` (Iff.rfl) |
| `CElemTiming.winDelay_comp`, `winDelay_le`, `transport_winDelay` | `win_comp`, `win_le`, `shift_win` / `transport_fixed_win` | |
| `CElemTiming.Loop` | `Win (exc) O ∧ Win O qp ∧ 0 < dlmin+dwmin` | `loop_iff` |
| `CElemTiming.Inertial` | none on purpose (`TraceDiscrete.inertial` for counterexamples) | `inertial_not_win` |
| `Net.BoundedDelay lo hi` (+ H_QUIESCENT) | `WinR lo hi` | `winR_boundedDelay`, `winR_quiet` |
| `Timing.Run` | built from `WinR` pins | `runOfWinR` |
| `Timing.shift d` | `TraceDiscrete.delay d` | `timing_shift_eq_delay` |
| `XSim.WinCh`, `XSim.transport_winCh` | `WinR`, `transport_winR` | abbrev |
| `Discretize.chan_sample_win`, `circuit_sample`, `transfer` | `chan_sample_win`, `circuit_sample_win(R)`, `transfer_win` | no `L ≤ H`, no rest needed |
| `Discretize.loop_of_continuous` | `chan_sample_win` twice + `loop_iff` | |
| `Corner.Arc`, `Corner.Scat` (ℝ) | `CArc`, `Scat` (ℕ) | `CArc.toArc`, `scat_real` |
| `Corner.bundle_ratio_affine`, `path_scatter`, `corner_refines_band`, `bundle_corner` | `bundle_endpoints`, `scat_path`, `band_sub_ind`, `win_bundle_corner` / `bundle_real_of_check` | |
| `Fidelity.DelayBound` (independent, ℝ) | `indLo`/`indHi` (ℕ) | `ind_encloses` |
| `Cells.K3`, `lutB`, `lutK`, `muxTree` | `Core.K3`, `Lut.eval`, `Lut.keval`, `LutTree` | `Core.Bridge`: `isoCells`, `cells_lutB_eq_eval`, `cells_lutK_eq_keval`, `cells_muxTree_eq_keval` |

### Shard B (`Cells.Prelim` → Core)
1. Values: replace `Formal.Cells.K3`/`lutB`/`lutK` by `Formal.Core.K3`, `Lut.eval`, `Lut.keval`
   on `Lut 6` built from the INIT `BitVec` (or from C's generated terms). `Core.Bridge` proves the
   two agree for every INIT, so each cell lemma can be restated and closed by rewriting with
   `cells_lutB_eq_eval` / `cells_lutK_eq_keval`.
2. Traces: `Trace` → `Sig` (defeq). `WinDelay` → `Win` (defeq), so cell proofs need no change
   beyond renaming. `Loop`'s fields are already `Win` (`loop_iff`).
3. Fixed transport counterexamples (`runt_oscillates`): `CElemTiming.Transport d` →
   `shift_win`/`delay_win`. The counterexample is still a legal behaviour of every window.
4. Continuous time: `chan_sample_win` (or `circuit_sample_win` on a `DNet`) instead of
   `Discretize.loop_of_continuous`.
5. Delay numbers: state the timing condition (for example `H_ENV_LATENCY`) on `bandLo`/`bandHi`
   of the cell's arcs, or as an `EndpointOK` between the two paths, so phase 2's
   `cell_constraints.json` is exactly a list of `EndpointOK` instances.
6. Then delete `Prelim` and `Substrate/Legacy.lean`'s shard-B section, and fix `Core/Bridge.lean`'s
   and `Core/Discretize.lean`'s Prelim imports. Shard A does those two; they are listed below.

### Shard C (`Net.Prelim` → Core)
1. `Trace`, `rises`, `falls`, `changes`, `stableOn` → the substrate versions (same definitions).
2. `BoundedDelay` hypotheses: keep the proved C theorems (they apply through `runOfWinR`). State
   new ones with `WinR` (timing runs need the quiescent start) or `Win`.
3. Arc intervals in `Timing.Arc`: from the corner model, `indLo`/`indHi` for a correlation-free
   check, or `EndpointOK` on path pairs for the correlated check. Soundness: `bundle_band`,
   `bundle_paths`, `endpoints_sound_real`.
4. LUT semantics: `Core.Lut` (`Lut.eval`), and prove the generated terms equal to the INITs there.
5. Then delete `Net.Prelim` and the shard-C section of `Legacy.lean`.

### Left for shard A, when Prelim goes
`Core/Discretize.lean` imports `Net.Prelim` and `Cells.CElemTiming` only for its last section of
bridges (`transport_boundedDelay`, `chan_sample_bd`, `chan_sample_win`, `loop_of_continuous`).
Its replacements are in `Substrate/Real.lean` and `Legacy.lean`. `Core/Bridge.lean` imports
`Cells.Prelim` for `isoCells` and the `cells_*` lemmas. Both need that section removed when Prelim
is deleted. Substrate.lean itself depends on Prelim only through `Discretize`'s import.

## 5. Hypotheses the substrate makes (graded as in the fidelity table)

A = established, B = credible but untested, C = doubtful.

| name | where | statement | grade | how to test |
|---|---|---|---|---|
| H_GRID | everything | time and delays in whole ps; prjxray endpoints are ns with 3 decimals, so they are exact in ps | A (data) | none needed for data. For signals it is not assumed: see H_SEP |
| H_SEP | `chan_sample_win`, `circuit_sample_win`, `transfer_win` | each gate's excitation has no two transitions within one quantum q, jointly over its fan-in | B for data paths and handshake nets at q = 1 ps; **C for arbiter inputs and same-sense near-ties** (`tie_counterexample`) | GLS: histogram of minimum inter-transition gap per net excitation at 1 ps. Any gap < 1 ps marks a net where only the K3 route is sound |
| H_REST | `WinR`, `chan_sample_winR`, `invariant_real_time` | signals are constant before time 0 (quiescent start) | A after reset; `Win` drops it | GLS from reset |
| H_BOUNDED (the window) | `Win`/`WinR` | output at t is a binary input value from [t-hi, t-lo] | B: right for buffered pips and LUT paths as long as edges are clean. A slow or mid-rail edge is outside the binary model and is handled by the K3 view (`win_covered`) | GLS with transport LUT paths against the window (does any output sample fall outside its window?); board ring periods inside summed bands |
| H_ZERO_DELAY_FN | `DNet` | a gate is a zero-delay Boolean function of its pin values followed by one channel | B. A LUT is a mux tree with per-pin delays (`LutTree`): per-pin arcs, as in C's `Run` (pins carry their own delay), are the finer form | `LutTree` hazard results; A-gls-compare |
| H_ENDPOINTS | `CArc` | each arc's delay is driven by a fast and a slow endpoint (prjxray FAST/SLOW, Elmore per sink arc) | B | 128-ring periods against summed endpoints (cells/hw) |
| H_AFFINE | `nom`, `Corner` | nominal delay is affine in ONE corner scalar c ∈ [0,1] | **C** in general (PVT is 3 axes, and arc types respond differently), B for matched paths built from the same arc types. `Corner.bundle_ratio_chord` is the weaker sufficient form | two ring types (LUT-heavy, wire-heavy) at ≥ 3 temperature or VCCINT points: are the period pairs collinear? |
| H_SHARED_CORNER | `RealizesAt c` (one c for all arcs) | one corner per die, at least for one handshake | B (slot and group permutation tests p = 0.73 and 0.66, no visible gradient) | 128 rings at two die temperatures: spread of period ratios |
| H_SCATTER κ | `Scat`, `Kappa` | every arc's delay is within ±κ of its nominal value at the shared corner | form B; **value C** for κ ≤ 0.2 (path-level ring data give κ ≥ 0.31, though that is absolute delay, not the two-path difference that bundling needs) | per-route two-path (differential) measurements; κ estimator (A-delay-corner), not yet run on data |
| H_ONE_DELAY_PER_ARC | `BehFixed`, `Realizes` (one d per arc) | an arc's delay is fixed for the run | B. Not needed by `Win` theorems: `Win` lets the delay move inside its band from one transition to the next, which also absorbs slow temperature drift | GLS with drawn per-transition delays |
| H_BINARY | `Win` on `Sig` | wires carry 0/1 | B for settled logic, C at arbiter ties. The K3 layer (`KSig`, `XSim`) drops it | `Covers` / XSim |

## 6. What does not check, and what is not done

- `Wip/Substrate.lean`:
  - `realizes_rational_of_real` (1-D Helly: an ℕ delay vector realised at a real corner is also
    realised at a rational corner). About 2 h. Not needed for soundness, because
    `endpoints_sound_real` and `tight_band_bundle` cover real corners directly.
  - `boundedDelay_comp_counterexample`: whether C's `BoundedDelay` composes with summed bounds.
    Open either way.
- In ℕ the endpoint check is sufficient but not necessary: rounding to whole ps loses tightness.
  Necessity holds in ℝ (`Corner.bundle_ratio_affine_iff`).
- The κ *estimator* (PROGRAM Phase 1 A, "so it can run on per-route two-path data") is not in
  this file. The estimator is specified in A-delay-corner.md; the data do not exist yet.
- Rise/fall-specific windows are not modelled. The window has one band per arc. If the data ever
  separate rise from fall, use two `Win`s on the rising and falling edges, which is future work.

## 7. Verdict

**Works.** One substrate (`Formal.Core.Substrate`), 5 files, about 1,500 lines, all checked by
`check.sh` with the axiom audit. It took about 3 h. Every existing channel variant is placed
relative to `Win` with proved inclusions and strictness. The corner model is decidable in ℕ, with
a proved link to the ℝ model and to real corners. The ℝ bridge is restated against `Win`
(rest-free) and against `DNet` circuits. Effort for B and C to port: mostly renaming (`WinDelay`
is `Win`, defeq). For C's timing semantics, `runOfWinR` lets the existing proofs stand while new
ones use `WinR`.

What it buys: B and C now state theorems in one model, with one delay model whose checks are
decidable in ℕ and proved sound for real silicon under named, graded hypotheses (H_AFFINE,
H_SHARED_CORNER, H_SCATTER), and with a one-line transfer to real time under H_SEP.
