# A-xaudit-gcd: the verified X/hazard audit on the REAL routed gcd_hw

## Verdict

**It runs on the real route, end to end, and it is sound. With signoff-width bands it cannot
certify one gcd transaction, and every flag traced here is imprecision. With bands about 2%
wide it does certify one.**

- **Real route.** gcd_hw R5, BOARD-QUEUE #2's build, routed on 4 placer seeds. On the default
  seed the SDF md5 is a9c4e265, the same as the journal's R5 build. The audit takes the rig's
  control network: the compiled kernel plus the handshake environment and the checker, cut from
  the clocked shell. It also takes the datapath, because the control reads it.
  - Size: 47,894 wires, 9,959 LUT/MUXF/CARRY gates, 37,928 routed arcs.
  - Storage: 4,599 storage nodes, of which 414 are control and 4,185 are data-latch bits.
  - Bands: one band per arc, from prjxray (`xray_delay.py`), not from the SDF.
- **One-corner bands (prjxray `[SLOW_MIN, SLOW_MAX]` or `[FAST_MIN, FAST_MAX]` per element).**
  The audit stops being able to tell anything about 10.7 ns after reset release on the slow
  corner and 4.3 ns after it on the fast corner. Seeds d/3/4/5 agree within 0.5 ns.
  - The first flags are always the same nodes: the joins of `ucond_br9/10/11`, then
    `ulink_n8__1` stage 0.
  - From there X spreads through the handshake loops, and `out0_req` / `rig_lap` / `rig_ok`
    never become binary.
  - **Every flag examined is abstraction imprecision, not a race.** Three pieces of evidence:
    1. the static own-feedback check finds 0 candidates at either corner, on all 4 seeds;
    2. 520 concrete fixed-delay samples (480 on vector 1, 40 on vector 2) give the right answer,
       and every storage node toggles exactly as in every other sample;
    3. the flag mechanism has been traced by hand (§4).
- **Narrow bands, `[(1-w)·SLOW_MAX, SLOW_MAX]` per element (plus up to 25 ps of rounding).**
  - At w = 0 and at w = 0.02 xaudit **certifies the transaction**. The w = 0.02 run's numbers
    hold for both, since the w = 0 bands lie inside the w = 0.02 bands. For every delay
    assignment in these bands and every power-up state:
    - rig_lap is 0 on [13.1, 78.1] ns and 1 from 83.15 ns to the 100 ns horizon;
    - all 32 bits of rig_res_data are binary on [65.2, 87.95] ns, and equal 7 there;
    - rig_ok = 1 on [86.6, 92.0] ns;
    - rig_err = 0 on [15.3, 92.9] ns.
  - At w = 0.05 the certification is lost.
  - **Negative control:** I delayed the checker's view of `mism` by 20 ns. rig_err then becomes X
    on [82.7, 89.6] ns, and the concrete sim shows the real error pulse.
- **Corner-mixed bands (`[FAST_MIN, SLOW_MAX]` per element, the lead's "[fast, slow]"):
  real races.**
  - The static check finds 4 / 7 / 10 / 9 own-feedback candidates on seeds d / 3 / 4 / 5. They
    are LUT C-elements, arbiter A-loops and latch bits.
  - One of them, `ucontrol_merge4.uarb1.ua2` on seed d (margin −9 ps), **is reproduced
    concretely**:
    - in sample `indep ends seed 11`, vector 2, a 9 ps runt appears at 295.04 ns;
    - it then circulates in the arbiter's own A2 loop for the rest of the run, 96 times.
  - This is the pipe3 relative-timing obligation ("own feedback < fastest neighbour response")
    on the real route. It holds at every one-corner band and fails only when one die is allowed
    to be fast on some arcs and slow on others.

The answer was derived from C, not from a run. The rig's vector 1 is a = 7, b = 0, and
`gcd_kernel.c` (Dynamatic's gcd, `audit/oracle/gcd_kernel.c` on claude/audit) does
`if (b == 0) return a;`, so the answer is **7**. It is non-zero, so it is not the failure value.
For vector 2 (12, 18), I hand-traced the C: 12|18 is even, so k = 1, a = 6 and b = 9. Then
a = 3, and the loop gives 3 → 6. The answer is **6**, the rig's g.

## 1. Build (seeds, fingerprint)

- **Worktree.** `/tmp/gcdwt`, a detached worktree of HEAD cbe4a52. It was removed at the end.
- **Frontend.** Dynamatic is not in this container, so `build/frontend/gcd` comes from
  `cloud/fixtures/frontend` (`cloud/setup-toolchain.sh` does the same).
- **Command.** The one in BOARD-QUEUE #2, run from `cells/`:

      [NEXTPNR_SEED=N] BD_SIZES=../research/data/gcd_hw_sizes_R5.vh \
        BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw

- **Toolchain.** `cells/verify/toolchain.sh` passed: all 9 patch fingerprints "ok", nextpnr
  sha256 **9c732bc6303458df**. That is the patch set the journal names for R5. Yosys is v0.62
  from `$TC`.
  - The restored toolchain lacked runtime libraries: `libtcl8.6` for yosys, and boost
    1.83 python/filesystem/program_options for nextpnr. I installed them with apt. The
    toolchain check cannot see this, because it only greps the binary.
- **No `--freq`.** `build_hw.sh` passes `--freq` only when `NEXTPNR_FREQ` is set, and BOARD-QUEUE
  #2 does not set it. I kept the shipped command so that the route can be compared by md5. No
  frequency is reported anywhere here.
- **Seeds d, 3, 4, 5.**
  - All four placed and routed with 0 RLOC groups dropped and `fasm_audit PASS` (7442 LUT sites).
  - The bitstream step failed on every seed with `textx` missing. That is not needed: no
    bitstream was used or kept.
  - SDF md5s: d a9c4e265 (= journal R5), 3 e0d4202b, 4 b1b4b951, 5 030c36bd. The four are
    distinct, so the seeds really differed.
- **prjxray delays.** `xray_delay.py` (read from origin/claude/research) ran on each route in
  about 45 s:
  - 50,025 interconnect arcs, 41,311 of them from prjxray;
  - the rest are constant (8,710), global (341) or no-sink nets;
  - 44,438 IOPATH arcs, all from prjxray.

  It needed simplejson (a 1-line shim) and intervaltree (pip, into `/tmp`).

## 2. `routed2x.py`: routed JSON → xaudit netlist and per-arc bands

`formal/tools-A/xaudit/routed2x.py`. The docstring holds the full contract.

### The cut

- **Kept cells.** Every cell named `urig.*`, i.e. the rig: kernel `bdc_gcd`, env C-elements,
  fork, delays and checker.
- **Pulled in.** Their combinational fan-in through LUT/MUXF/CARRY cells that yosys hoisted out
  of the hierarchy: 68 cells. They are the vector ROM `a_v/b_v/g_v` and the mismatch reduction
  `mism`.
- **Stops.** The fan-in stops at FF/BUFG/BSCAN outputs, and at the net `rig_rst`
  (`--cut-net`).
- **Free inputs.** These stops leave exactly 5 free inputs:
  - `idx[3:0]`, which are FF Q outputs;
  - `rig_rst`.

  So the stimulus drives the rig's own reset and vector index, which is gcd_rig.v's contract.
- **Outputs.** The 123 nets the shell reads are observed outputs. The sticky LUTs, the BUFG
  clocks and the counters are not simulated.
- **Constants.** 912 constant nets are folded: PSEUDO_GND/VCC, and packer LUTs whose inputs are
  all constant.

### Primitives

All of them are emitted as yosys `LUTk` cells, so the proved engine is unchanged.
**No Lean change was needed, and `Prims.lean` was not written.** The reason is that `Lut.keval`
is the exact ternary extension of the INIT, so a LUT3 with INIT 0xCA *is* the Kleene mux.

- **`SLICE_LUTX`.** A LUTk over the cell's used **physical** pins. The INIT is re-encoded from the
  logical INIT through `X_ORIG_PORT_A<k>`, which is fasm_audit's encoding.
  - So a physical pin that carries two logical inputs is one wire with one arc, as in silicon.
    Splitting it would invent incoherence between two copies of one signal.
- **`SELMUX2_1` (MUXF7 ×824, MUXF8 ×341).** A LUT3 with I0 = '0', I1 = '1', I2 = S0 and INIT 0xCA.
- **`CARRY4` (×38).** Four MUXCY LUT3s (0xCA on DI/ci/S) and the used XORCY LUT2s (0x6 on S/ci).
  - The carry-in is CIN, else CYINIT, else PRECYINIT_CONST.
  - The script checks every prjxray CARRY4 IO row against the decomposition:
    - **hi:** the model's summed hi must cover the real hi on every input→output path, else it
      exits 1. That check caught one 1 ps under-cover in an early version, which is fixed;
    - **lo:** the paths where the model's 1-step-per-element floor exceeds the real lo are
      listed (see fidelity).

### Bands

One band per routed arc, from the `IC` row of (driver pin, sink pin). Each gate gets
[min lo, max hi] over the IOPATH rows to its output. The corners are:

| corner | band per element |
|---|---|
| `slow` | [SLOW_MIN, SLOW_MAX] |
| `fast` | [FAST_MIN, FAST_MAX] |
| `indep` | [FAST_MIN, SLOW_MAX] |
| `slowmax --widen w` | [(1-w)·SLOW_MAX, SLOW_MAX], the precision sweep only |

- The SDF fallback (`--sdf --kappa`, default [0.35·d, d]) is implemented but **not used** for
  any result. The 0.35 is the median prjxray FAST_MIN/SLOW_MAX ratio of the IC arcs, 0.40.
- Median arc bands, seed d:

| corner | lo | hi | width |
|---|---|---|---|
| slow | 736 | 897 | 153 |
| fast | 341 | 402 | 61 |
| indep | 341 | 897 | 566 |

  The largest arc, rig_rst's fanout, reaches 7.2 ns.

## 3. Runs

The stimulus is in `gcd/inputs/v1_100ns.stim.json` / `v1_70ns.stim.json`:

- rig_rst = 1 and idx = 1 from power-up, with everything else all-X;
- rig_rst = 0 at 20 ns;
- the horizon is 100 ns (70 ns on the fast corner);
- 1 step = 25 ps, so 4,000 (2,800) steps;
- timed engine (`--timed-only --all`).

Concrete latency for vector 1 with hi delays is 82 ns slow and 47 ns fast.

`analyze.py` splits storage into control and data-latch bits (`.lat.` in the cell name). A data
bit that is X from power-up to the horizon is a latch this transaction never writes. That is
expected, and it is not a flag.

| run (seed d unless noted) | control: clean / flagged | first flag (ns, after power-up) | rig_lap binary 1? | wall s, peak RSS |
|---|---|---|---|---|
| slow | 307 / 107 (4 "STORED", 103 UNRESOLVED) | 30.7 `ucond_br11_j` | no (X from 69.4) | 616, 1.78 GB |
| slow, seed 3 | 386 / 28 | 30.9 `ucond_br11_j` | no | 952* |
| slow, seed 4 | 309 / 105 (+20 data-latch GLITCH, 10 UNRESOLVED) | 31.2 `ucond_br11_j` | no | 967* |
| slow, seed 5 | 307 / 107 | 30.9 `ucond_br9_j` | no | 952* |
| fast | 187 / 227 | 24.3 `ucond_br11_j` | no (X from 39.1) | 359, 1.29 GB |
| slowmax w = 0 | 387 / 27 "STORED" (all bounded 0→X→1 transitions, >2 ns) | — | **yes, 83.15 ns, res = 7 (binary on [65.2, 89.25] ns), ok = 1 on [86.6, 93.4], err = 0 on [15.3, 94.2]** | 404, 1.78 GB |
| slowmax w = 0.02 | 386 / 26 "STORED" + 2 UNRESOLVED (at 85 ns, after the lap) | — | **yes, 83.15 ns, res = 7** | 467, 1.78 GB |
| slowmax w = 0.05 | 386 / 8 "STORED" + 20 UNRESOLVED | 48.0 `ucond_br13_j` | no (X from 76.7) | 507, 1.78 GB |
| negative control (w = 0, mism +20 ns) | as w = 0 | — | yes, 7; **rig_err X on [82.7, 89.6] ns**, rig_ok X on [82.3, 91.5] | 392, 1.78 GB |

Notes on the table:

- \* Three runs shared 4 cores.
- **"STORED".** xaudit labels any 0→X→1 longer than `--xmax` (2 ns) "STORED X POSSIBLE". In
  these runs those are bounded transitions with 2-3 ns of accumulated timing uncertainty, not
  stored X. Only UNRESOLVED and GLITCH are real losses.
- **Band fix.** The seed 3/4/5 runs and the first seed-d runs used bands from before the CARRY4
  band fix. That fix changed only the lo of 21 chained `carry4#xor0` gates by one step. On seed d
  the rerun with the fixed bands gives an **identical** summary (slow and fast).

### Scale

- 47,894 wires, 4,000 steps.
- About 0.15 s per step, i.e. 3 µs per wire-step, plus about 17 s of parsing.
- About 0.44 MB per stored row: `histF` keeps every row, so peak RSS ≈ 0.45 MB × steps.
- A vector-2 transaction is out of reach for the arrays: 0.7 µs slow / 0.3 µs fast is 28k / 13k
  steps, i.e. 12 / 6 GB. It is also pointless, because the one-corner precision is gone after
  about 11 ns.

## 4. Classification of the flags

### Mechanism (seed d, slow; the other seeds have the same first nodes)

1. **The joins go X.** `ucond_br9/10/11` join outputs go 0→X→1 over 2.8-3.1 ns windows
   (30.7-34.6 ns).
   - The width is the honest accumulated uncertainty of about 11 ns of path at 150 ps of band
     width per arc.
   - The condition request `n7_req` (`ucond_br9` LUT5) has the same window.
2. **The handshake windows overlap.** `ulink_n8__1` stage 0's C-element goes 0→X→1 on
   [32.5, 35.8] ns. Its neighbour, stage 1, starts going X at 34.3 ns, and the returning ack
   `a[1]` at 35.3 ns.
   - So the neighbour's response window opens **before** stage 0's own window closes.
   - The window domain cannot express "stage 1 moves after stage 0 has moved". The ack is X while
     stage 0 is X, stage 0 holds on its X feedback, and the pair is UNRESOLVED from 36.0 ns.
3. **It spreads.** From there X spreads through every handshake loop the token visits.

This is the ring3 imprecision of `A-xaudit.md` (W2, a non-FIFO window channel), now on a real
route. It appears as soon as one loop's window is wider than that loop's response time.

### Evidence that these are not real races at one corner

1. **The static own-feedback check finds nothing.** `fbrace.py` checks own feedback hi against the
   fastest structural response lo, for every storage node and only on pins the INIT depends on.
   It finds **0** candidates at `slow` and **0** at `fast`, on all 4 seeds.

   The tightest are latch bits at −2/−5 ps. Those appear only if the ignored pins of fractured
   LUT5s are counted, and then they are not real dependencies.
2. **Concrete samples (`csim.py`).** Fixed delays per element in the band, binary, pure
   transport, power-up 0; `samples/summary.txt`.
   - Vector 1: 100 `rand` + 100 `ends` at slow, 50 `ends` at fast and 50 `ends` at indep on seed
     d, plus 30 slow + 30 indep `ends` on each of seeds 3/4/5. That is 480 samples.
     (`rand`: each element uniform in its band; `ends`: each element at lo or hi, chosen at
     random.)
     - **Every one gives 0x7 on three consecutive laps**, ok rising and err never rising.
     - **The per-period transition count of every one of the 4,599 storage nets is identical
       across all samples in each group.** A glitch would add 2.
     - The flagged nodes toggle exactly 2 per lap in every sample.
   - Vector 2: 20 slow `ends` + 20 indep `ends` give **0x6** every time. The control counts
     differ only by ±1, where a toggle falls on either side of the lap cut.
   - **Sampling cannot prove absence.** The proof for the one-corner case is missing: it is
     W2.
3. **No GLITCH at the start.** The data-latch GLITCH flags of seed 4 (38 ns) come after its
   control is already X: the latch enable is undetermined. They are consequences of the same
   loss, and the samples show no extra latch toggles on seed 4.

### Corner-mixed bands (indep): real races under the bands

- `fbrace` finds these own-feedback candidates (margins in ps, the larger ones are latch bits):

| seed | candidates | examples |
|---|---|---|
| d | 4 | `ulink_n_falseResult_41` stage 2 C-element −190, a latch bit −184, `ucontrol_merge4.uarb1.ua2` −9 |
| 3 | 7 | `ulink_n145__2` latch −378, `ulink_n_falseResult_77` C −265, ... |
| 4 | 10 | latch bits to −1169, `ucontrol_merge10.uarb1.ua1` −167, `umux9.uj1` −143 |
| 5 | 9 | `ulink_n145__2` latch −1195, `uenv1` (the rig's env C-element) −395, ... |

- **Reproduced concretely on seed d, vector 2, indep ends seed 11.** `ucontrol_merge4_ack` rises
  at 293.07 ns, and A2 = `n_falseResult_41_ack` rises at 294.02 ns. The neighbour then withdraws
  `g2[1]`, which reaches ua2/I2 at 294.917 ns. The own-feedback arc, at 909 ps (its SLOW_MAX), only
  arrives at 294.926 ns.
  - The LUT therefore sees a stale hold and emits a **9 ps runt**, at 295.041-295.050 ns. That
    equals the static margin of −9 ps.
  - Under transport delay the runt then circulates in the A2 self-loop: 96 toggles.
  - The gcd answer stayed right in that sample. The defect is still a real behaviour of the
    netlist under those bands.
- **What decides whether this is a silicon race** is whether one die can put an own-feedback arc
  at slow-max and the neighbour's arcs near fast-min. H_ONE_CORNER says no, and then 0
  candidates remain. The project's own guardband (`skew.py`'s 0.772/1.155) is in between. A
  board or TDC experiment that measures own-feedback against neighbour delay on one die would
  settle it.

## 5. Fidelity (gate-fidelity rule)

| item | model | status / how to test |
|---|---|---|
| LUT (O6/O5) | physical-pin LUTk, exact INIT (fasm_audit encoding); Kleene under X | exact functionally; X = H_KLEENE_LUT (A-kleene-lut) |
| MUXF7/F8 | LUT3 Kleene mux | exact functionally; delay = [min, max] of the prjxray SELMUX rows. Its data inputs from the LUT's O6 are dedicated (0 ps in prjxray), raised to 1 step (25 ps) |
| CARRY4 | MUXCY/XORCY chain; internal arcs [0, max per-bit increment] | hi checked to cover every prjxray path. **lo is NOT sound below the floor**: 1 step per element gives a floor above the real fast lo on 30 paths (slow) / 194 (fast, indep), e.g. CIN→CO3 real 40 ps against a 175 ps floor. Datapath only; it could hide a hold-type data race on adder outputs. Fix: a finer unit (5-10 ps, ×2.5-5 cost) or a k > 6 / chain primitive in Lean |
| routed arc | own wire and band per (net, sink pin), prjxray Elmore + intrinsic, RC term in every column | as `xray_delay.py`: prjxray reports ±1.5% against Vivado, except clocks. Site pips other than the OUTMUX are 0 (that file's weakest choice) |
| sub-step elements | 2,334 (slow) / 2,675 elements with lo < 25 ps are raised to 1 step; all are MUXF dedicated inputs or carry internals | the same unsoundness as the row above, datapath only |
| power-up | all X; the 20 ns reset resolves every control node (15.3 ns at the latest) | sound for any power-up state. Data latches stay X until written |
| clocked shell | cut: idx FFs and rig_rst are free inputs, held constant except the reset release | matches gcd_rig.v's contract (idx moves only under reset). Not modelled: rig_rst's glitch-freedom from the shell |
| arbiters | the bd_arb LUT loops as plain LUTs; X = "either / in transit"; no metastability value | single-token runs never contend. The indep runt above is a model behaviour (transport); silicon would filter a 9 ps pulse inertially, or not |
| time | 25 ps steps; lo rounded down (≥ 1 step), hi rounded up | widens every band by up to 25 ps a side |

## 6. What it buys, and what is next

- **On the real 48k-wire route, the proved engine:**
  - gives a **certified transaction** (any power-up state, every delay in about 2%-wide bands
    around SLOW_MAX), with the answer derived from C;
  - gives a **negative control** that fails as it should;
  - **localises** where one-corner precision is lost: the same nodes on 4 seeds.
- A cheap static check (`fbrace.py`) closes the C-element own-feedback race class: 0 candidates
  per corner, real candidates once corners mix, and one of them reproduced concretely.
- **For a whole-transaction certificate at real prjxray widths, W2 (a FIFO/correlation-aware
  domain) is THE blocker,** as predicted in `A-xaudit.md`. It is now measured: precision holds at
  2% width and is lost at 5%, while prjxray one-corner widths are about 17%.
  - Second blocker: memory. `histF` keeps every row, about 0.45 MB per step here. A
    sliding-window `histF` (refinement proof like `histF_spec`) would fix it, at 1-2 days.
  - The CARRY4/MUXF lo floor needs a finer unit or a chain primitive.
- **Untimed engine.** Not run: its `Causal` model flags every LUT C-element NO SETTLE
  (A-xaudit pipe3), and it would say nothing new here.

## Files

| file | what |
|---|---|
| `formal/tools-A/xaudit/routed2x.py` | converter (cut, primitives, per-arc bands, CARRY4 hi check) |
| `formal/tools-A/xaudit/gcd/run.sh` | reproduction recipe (build, prjxray, routed2x, xaudit, fbrace) |
| `formal/tools-A/xaudit/gcd/analyze.py` | report summariser (control / data split, observables) |
| `formal/tools-A/xaudit/gcd/fbrace.py` | static own-feedback vs neighbour-response check |
| `formal/tools-A/xaudit/gcd/csim.py` | concrete fixed-delay transport simulator (cross-check only) |
| `formal/tools-A/xaudit/gcd/sample.sh`, `sampsum.py`, `sigsum.py` | sampling driver and summaries (scratch paths under /tmp/gcdx hard-coded) |
| `formal/tools-A/xaudit/gcd/inputs/` | seed-d netlist and band files (xz), stimuli, routed2x reports (all seeds), build md5s |
| `formal/tools-A/xaudit/gcd/results/` | xaudit reports (xz) and summaries, fbrace outputs, sample summaries |

No Lean file was written or changed.
