# C-10d: the verified timing checker on a REAL routed netlist (tracks 10+11)

Shard C, probe 10d, 2026-10-27.

## Verdict

**Works.** 10a's checker now runs, by kernel `decide`, on netlists read back from real
bitstreams.
- **ce_pair, seed 1:** 38-50 arcs per launch, about 2 s.
- **64-stage Muller pipeline:** 64 relative-timing instances, 3.6k arcs per interval
  variant, about 30 s. A single 1227-arc DAG takes about 1 s.

There is no sorry, axiom or native_decide. `formal/check.sh` passes on all 9 files (624
declarations audited), and the axioms used are propext, Quot.sound and Classical.choice.
The `decide +kernel` used everywhere is plain kernel `decide`: no `ofReduceBool`.

**Main finding:** with the prjxray data, the RT_FB hold requirement (defined below) fails
on 12 of the 64 routed Muller C-elements under the one-corner models, down to −138 ps.
nextpnr's SDF reports +419 ps on 11 of those 12. The cause is the placer putting a
C-element's feedback on the slowest LUT pin (`*1`, 420-531 ps at the slow corner) while
its neighbours land on fast pins. This is 10b's site-pin finding, now as a margin problem
in a shipped cell.

## What checks (run it)

    formal/tools/routed2lean/run.sh      # ~3 min: regenerate all data, compile, axiom audit -> "routed2lean PASS"
    formal/tools/routed2lean/pipe/route.sh 1 64   # re-route the Muller pipeline (~10 s), then run.sh
    cd formal && ./check.sh Formal/Timing/WinArray.lean Formal/Timing/WinArrayB.lean \
      Formal/Timing/RoutedCePairS1Fork.lean Formal/Timing/RoutedCePairS1Loop.lean \
      Formal/Timing/RoutedCePairS1Input.lean Formal/Timing/RoutedCePair.lean \
      Formal/Timing/RoutedMuller64S1.lean Formal/Timing/RoutedMuller64S1Wave.lean \
      Formal/Timing/RoutedMuller.lean    # -> [check] OK (624 declarations)

Last run: PASS. Toolchain: `cells/verify/toolchain.sh` ok, **nextpnr sha256
9c732bc6303458df**, `fasm_audit.py` PASS. The flow is cells/flow.sh's options plus
`--freq 100 --seed 1`.

### Files

| file | content |
|---|---|
| `formal/lean/Formal/Timing/WinArray.lean` | One-pass `Array` fold `winTable`, plus `winArr`, `checkArr`, `slackArr`, proved equal to 10a: `winArr_eq`, `checkArr_eq`, `slackArr_eq`, `checkArr_sound`, `changes_in_winArr`. Also proves `collect` is permutation invariant (`collect_perm`). |
| `formal/lean/Formal/Timing/WinArrayB.lean` | The kernel-friendly one-pass version: in-arc buckets plus a cons table (`ofBuckets`, `tabB`, `winB`, `checkB`, `slackB`). Proved: `winB_eq`, `checkB_eq`, `slackB_eq`, `checkB_sound`, `changes_in_winB`. Many-instance form: `RTEntry`, `rtOne`, `wfOne`, `sepOne`, `rtOne_sound`, `rtOne_exact`. |
| `formal/lean/Formal/Timing/RoutedCePairS1{Fork,Loop,Input}.lean` | Generated data: ce_pair seed 1 launched at q1's O6, at input `a` on q1's pin B4, and at `a`'s IOB. Each has 6 variants. |
| `formal/lean/Formal/Timing/RoutedCePair.lean` | ce_pair theorems (below) |
| `formal/lean/Formal/Timing/RoutedMuller64S1.lean` | Generated: 64 RT_FB instances × 6 variants (600 kB) |
| `formal/lean/Formal/Timing/RoutedMuller64S1Wave.lean` | Generated: the whole pipeline from `req` (1165 nodes, 1227 arcs) |
| `formal/lean/Formal/Timing/RoutedMuller.lean` | Muller theorems (below) |
| `formal/tools/routed2lean/routed2lean.py` | Generator: fasm2lean JSON + prjxray-db → 10a netlist |
| `formal/tools/routed2lean/rt_all.py` | RT_FB for every C-element of a netlist |
| `formal/tools/routed2lean/run.sh`, `pipe/` (`muller_pipe.v`, `.xdc`, `route.sh`) | Pipeline script, and the Muller design with its route script |
| `formal/tools/routed2lean/fixture/` | Read-back FASM, SDF, toolchain stamp, audit and cell→BEL maps; the reports `fork.txt`, `loop.txt`, `input.txt`, `muller64_rt.txt`, `muller64_wave.txt` (windows per node and variant) |
| `formal/lean/Wip/C10d/` | Scaling benchmarks (`Lad*`, `LadB*`, `LadOld*`, `WaveBench`). They are not claims. |

`build/` holds 16 MB of routing intermediates and is not for git.

## (1) A one-pass `win` that scales, proved equal to 10a's `win`

10a's `win` rebuilds the table and scans every arc per node. That is O(n²·arcs) in the
kernel.

**`WinArray.winTable`** (arcs sorted by source, `Array.setIfInBounds` fold):
- It is proved equal (`winArr_eq : net.WF → winArr net v = win net v` for every netlist).
  When the arcs are unsorted it falls back to `win`.
- It is the right algorithm for compiled code.
- **In the kernel it is no faster**, because reduction is lazy. After k updates, reading
  one entry walks k unevaluated `List.set` layers.

**`WinArrayB.winB`** fixes this:
- The generator emits each netlist as in-arc buckets (entry v = the arcs into v; the
  `Netlist` is `ofBuckets B = ⟨B.flatten⟩`).
- One pass over the nodes conses each window onto an already evaluated list. Every arc is
  read once.
- It is proved equal for every `B`: `winB_eq : (ofBuckets B).WF → winB B v = win (ofBuckets B) v`.
  If the buckets are mislabelled, `bucketsOK` fails and it falls back to `win`.

Measured cost of `decide +kernel` on literal ladder netlists (`Wip/C10d`; CPU seconds and
max RSS of the whole `lean` process, including the ~0.5 s import):

| arcs (nodes) | 10a `check` | `checkArr` (Array) | bucketed `winB` |
|---|---|---|---|
| 90 (61) | 0.9 s, 0.56 GB | 1.3 s, 0.62 GB | – |
| 300 (201) | 11.9 s, 1.5 GB | 17.6 s, 2.1 GB | 1.3 s, 0.50 GB |
| 900 (601) | – | killed (OOM, shared machine) | 2.2 s, 0.57 GB |
| 3000 (2001) | – | – | 7.9 s, 0.80 GB |
| 1227 (1165), the real routed pipeline | – | – | ~1 s (`wave_qn`, two windows) |

Kernel decide was not too slow at any size tried; the largest is 3000 arcs. The
generated data files cost more to *elaborate* than to check: the 600 kB Muller file takes
41 s.

## (2) The generator: `formal/tools/routed2lean/routed2lean.py`

**Input.** The JSON written by 11b's `fasm2lean.py --json`, which is read back from the
`.bit`. It has every LUT's physical pins and, per sink, every pip with its 4-corner
intrinsic delay, the site-pin delay and the Elmore term. The generator reuses those
numbers unchanged.

**Arcs.** It adds prjxray-db's LUT6 cell arcs from `timings/CLBLM_R.sdf`: `LUT6` or
`LUT_OR_MEM6LRAM`, `Ak → O6` = (45::56)(100::124). Then it emits one arc for each of:
- every pip (pass/zero-delay pips as [0,0]),
- the route's RC (Elmore) term (the "wire" arc),
- the LUT site input pin,
- every LUT cell arc.

**Routes.** Each sink gets its own chain (11b's H_ROUTE per sink). For a chain, any total
in [Σlo, Σhi] splits into per-arc delays, so the hypothesis is exactly "each sink's route
delay lies in its summed interval".

**Unrolling and numbering.**
- Loops are unrolled by a DFS from the launch. A back edge ends in a LAP node
  (`…O6@lap`). `--hops` bounds the depth, and `--no-lap` drops the LUT arcs that close
  loops (they only leave both cones).
- Nodes are numbered topologically and arcs are emitted in buckets.
- `--name KEY=NODE` emits the node index and its *part* (backward cone without the launch,
  closed forward), which is the `P` for 10a's `Separated`.

**Interval variants** (same nodes and arcs). The corner hypothesis is stated in both
forms:

| variant | hypothesis | element interval | RC arc |
|---|---|---|---|
| `indep` | **H_INDEP**: every element independently anywhere in its full range | [fast_min, slow_max] | [0, ⌈E⌉] |
| `fast` / `slow` | **H_ONE_CORNER**: the whole die at one prjxray corner (10b: needed for non-vacuous results) | [corner_min, corner_max] | [0, ⌈E⌉] |
| `fastE` / `slowE` | H_ONE_CORNER + **H_RC_EXACT**: prjxray/timing.py's model, delay = intrinsic(corner) + RC, RC corner-free | as above | [⌊E⌋, ⌈E⌉] |
| `sdf` | nextpnr's SDF number on the same path. Comparison only, not a bound. | [0,0] on pips and pins | INTERCONNECT d, IOPATH on the LUT arc |

The theorem form of H_ONE_CORNER is a disjunction of the two corner models
(`ce_pair_s1_rt_fb_oneCornerE`).

## (3) Results

### ce_pair (seed 1; q1 = SLICE_X42Y95.BLUT, q2 = SLICE_X42Y94.ALUT)

**Windows (ps, from q1's O6 edge):**

| node | indep | fast | slow | slowE | SDF |
|---|---|---|---|---|---|
| q1 feedback pin B1 | 213..709 | 213..315 | **534**..709 | 583..709 | **295** |
| q2 input pin A1 | 262..859 | 262..385 | **650**..859 | 708..859 | **435** |
| q2 O6 | 307..983 | 307..441 | 750..983 | 808..983 | 559 |
| q1 loop (lap) | 258..833 | 258..371 | 634..833 | 683..833 | 419 |

**Agreement with 11b** (proved, `rfl`-linked to 11b's generated `pinDelay`):
- `fork_fb_eq_11b`: the B1 window is fasm2lean's `pinDelay` (213, 709).
- `fork_q2pin_eq_11b`: the A1 window is (262, 859).
- `loop_fb_window`, `loop_fb_hi_eq_11b`, `loop_fb_in_window`: from `a` at B4, the
  feedback reaches B1 in [258, **833**] ps. The 833 equals 124 + 709, the hold length that
  11b's `q1_follow_hold_s1_ps` assumes, and it is now computed by the checker and true in
  every run.

**Disagreement with the SDF** (`fork_sdf_vs_slow`):
- The SDF puts B1 at 295 ps and A1 at 435 ps. Both are **below the slow-corner minimum**
  of the same routes (534 and 650).
- The SDF's flat 25 ps site pin against prjxray's 420/428 ps slow min is the whole
  difference.
- So on a real route, nextpnr's single "slow max" SDF number is not even inside the slow
  corner.

**RT_FB check** (q1's feedback reaches B1 before q2's output can switch; setup 0;
`fork_check_*`, `fork_slacks`):

| variant | indep | fast | slow | fastE | slowE | SDF |
|---|---|---|---|---|---|---|
| slack (ps) | −402 | −8 | +41 | +50 | +99 | +264 |

- `ce_pair_s1_rt_fb_oneCornerE` (**the kernel-checked theorem for the routed instance**):
  under H_ONE_CORNER + H_RC_EXACT, in every `Run`, every change of q1.B1 is at or before
  every change of q2.O6.
- `ce_pair_s1_rt_fb_slow`: the same at the slow corner without H_RC_EXACT.
- `ce_pair_s1_rt_fb_indep_violated` and `_fast_violated`: under H_INDEP, and at the fast
  corner with RC allowed to be 0, there is a fixed-delay run that really violates it
  (10a's `check_exact_disjoint`; the cones share only the launch, `fork_separated`). The
  fast-corner verdict therefore hangs on the RC lower bound (8 ps).

**Input path** (`input_windows`): `a` at its IOB → B4 334..1163, q1 379..1287,
q2 686..2270 (H_INDEP); the SDF gives 1664 at q2.

### 64-stage Muller pipeline (`c[i] = C(c[i-1], ~c[i+1])`, bd_c2n, seed 1, 64 LUTs, 486 pips)

**RT_FB(i):** c[i]'s feedback reaches its own LUT pin before either neighbour's response
to c[i]'s edge reaches one of c[i]'s pins.
- The neighbour's path is its input route + its LUT arc + its route back, all routed.
- If RT_FB fails, c[i]'s inputs disagree while its feedback pin still shows the old
  value. The majority LUT then flips back (a glitch of up to the negative slack). This is
  the hold hypothesis of B's `c2_follow_hold`.
- With the earliest neighbour response the check is necessary as well as sufficient in
  the model: `rtOne_exact` builds the violating run.

`m64_counts` (kernel; per-stage table in `fixture/muller64_rt.txt`):

| variant | indep | fast | slow | fastE | slowE | SDF |
|---|---|---|---|---|---|---|
| RT_FB holds | 22/64 | 48/64 | 50/64 | 52/64 | 52/64 | 63/64 |
| worst slack (ps) | −643 | −117 | −187 | −47 | −138 | −7 |

- **Passing stages:** `m64_rt_sound_slowE` / `_fastE` prove that every passing stage
  satisfies RT_FB in every run.
- **Failing stages:** `m64_rt_violated_slowE` / `_fastE` / `_indep` give each failing
  stage a real violating fixed-delay run. So each count is exact for its model.
- **Worst stage** (`m64_worst_slowE`): SLICE_X38Y98.ALUT, with its feedback on A3 via a
  FAN_ALT/FAN_BOUNCE detour (7 pips) and the D LUT of the same slice answering on A4.
  Slack −138 ps.
- **The other 11 failures** all have the feedback on physical pin B1/C1 (the slowest
  site pin), with a same-slice neighbour on pin 5.
- **Not a CPPR artefact:** the routes share at most 3 pips with the neighbour route
  (31 ps of slow spread).

`wave_qn`, `wave_qn_in_window`: from `req` to `qn` through all 64 stages the window is
[13.9, 47.4] ns (H_INDEP) and [38.4, 47.4] ns (slowE). The SDF gives 32.5 ns, which is
below the slow-corner minimum again.

**Evidence, NOT proof (Python, labelled as such).** If every element sits at the *same*
point of its range, for example all at slow_max, all at slow_min, all at fast_max or all
at fast_min (with RC = E), then all 64 stages pass, with worst margins of only 2 / 10 / 2 /
6 ps. So RT_FB on this route holds only if on-die delays are almost perfectly
correlated. The failures come entirely from within-corner independence (slow_min/slow_max
≈ 0.82-0.87).

## What does not work / is not done

- **The 11b `Spec` (logic) theorem was not proved for the Muller pipeline.** Only its
  timing is used. The LUT INITs are the read-back ones, and `fasm_audit` passes on
  nextpnr's view.
- **No CPPR/shared-route model.** Per-sink chains ignore pips shared between the sinks of
  one net. This is conservative for FixedRun and exact for 10a's per-event `Run`. Its
  size is bounded here at ≤31 ps.
- **H_ENV_ZERO (ce_pair only):** the environment between q2 and q1's inputs is credited
  0 ps. The Muller instances need no environment.
- **Not in the data, so not modelled:**
  - the OUTMUX `O6→?MUX` site-internal delay (q1 leaves through BMUX; prjxray-db has no
    arc for it);
  - IBUF/OBUF pad delays;
  - rise vs fall (prjxray has one number per corner).
- **Elmore numbers:** 11b's, not cross-checked against `prjxray/timing.py`, so
  H_RC_EXACT rests on them.
- **One seed** (CLAUDE.md: one route is a sample). Seeds 2..4 of ce_pair have fixtures;
  `run.sh` does seed 1. The Muller pipeline was routed on one seed only.

## Fidelity of each primitive model

| primitive | model | how faithful | test |
|---|---|---|---|
| pip | BoundedDelay [lo,hi] from prjxray's 4-tuple. Every pip with a delay is buffered (11b). | As good as prjxray's per-pip-type numbers. It does not model slew or the input-transition dependence. | GLS with per-element corners; board ring measurements. |
| wire RC | One arc per sink, [0 or ⌊E⌋, ⌈E⌉], E = 11b's lumped Elmore | Unvalidated (11b). The fanout load is included. | Compare with `prjxray/timing.py` on the same nets. |
| LUT site pin | prjxray site-pin 4-tuple per physical pin | This is the term the SDF drops (25 ps flat vs 2-531 ps). | 128-ring re-prediction (10b's proposal). |
| LUT cell | per-pin arc `Ak→O6` (45..56 fast, 100..124 slow) + zero-delay function (10a H_ZERO_DELAY_FN) | prjxray gives the same numbers for all six pins. Mux-tree depth effects are not modelled. | – |
| channel | 10a's `Run` (per-event delay, pulses pass) for soundness; `FixedRun` for the violation witnesses | Soundness holds for both. A real LUT filters short pulses, so a violation is a hazard, not necessarily a board failure. | Inject the computed glitch into the routed GLS. |
| corner | H_INDEP / H_ONE_CORNER / H_RC_EXACT as above | The meaning of prjxray's slow_min..slow_max is undocumented (die spread? pip-type spread?), and the RT_FB verdict hinges on it (52/64 vs 64/64 at a common point). | Measure on-die variation (rings at many sites) and turn it into a band hypothesis. |
| H_LAUNCH / H_QUIESCENT | one edge from rest (10a) | One phase of one transition | – |

## Effort to finish, what it buys

- **Muller RT_FB on 4+ seeds** with mean and range: run `pipe/route.sh` and `run.sh` per
  seed, under an hour.
- **A CPPR-aware variant** (shared pips as shared arcs, FixedRun-exact checker): about
  1-2 days.
- **A band hypothesis** (H_ONE_CORNER ∧ every element within ±x% of a common quantile) to
  replace H_INDEP-within-corner. This is the model the Python evidence suggests. It needs
  a linear-in-θ argument, about 1-2 days of Lean, plus a measured x.
- **Whole shipped designs:** blocked on fasm2lean's FF/carry support (11b: 2-3 weeks).
  The checker side already scales to thousands of arcs per decide.

**What it buys:**
- The project's timing claims can now be theorems about the bits.
- The first real result is a design issue that nextpnr's SDF cannot show: the placer's
  LUT-pin choice for C-element feedback. The fix is to keep feedback on A6/A5 (pin locks
  or a lut-perm cost), and it is checkable with this tool on every build.

## Decisions taken (no one to ask)

- **Kept both one-pass versions.** The Array one was asked for, is proved, and is the
  right one for compiled `#eval`. The bucketed one is what kernel `decide` can afford.
- **RT_FB is the property checked.** ce_pair has no bundled-data pair, and RT_FB is the
  C-element's hold condition (B's `c2_follow_hold`, 11b's 833 ps).
- **Routed my own Muller pipeline** under `formal/tools/routed2lean/pipe/`, with the same
  flow as fasm2lean's `route.sh`, because ce_pair is too small to show scaling or a
  per-cell result.
- **Did not edit 10a's, 11b's or anyone else's files.** fasm2lean is run as a tool, and
  its `CePairS1.pinDelay` is imported.
- **No git** (brief).
