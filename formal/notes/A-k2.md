# A-k2: the model, netlist import and verified checkers on a second kernel (collatz)

PROGRAM.md north-star goal 3. Shard A, probe K2, 2026-10-27.

## Verdict

**Done for collatz.** The FPGA toolchain was restored and verified. A collatz rig was routed on 4
placer seeds. Both verified tools ran on it through the same front ends as on gcd_hw. The
procedure is written up in `formal/out/HOWTO-new-kernel.md`.

- **Toolchain.** Restored from `origin/toolchain-cache/d7ce266cff0c8e1e`. The key equals
  `cloud/toolchain-cache.sh key`. `cells/verify/toolchain.sh` exits 0: 9/9 patch fingerprints
  "ok", nextpnr sha256 **9c732bc6303458df**, the same binary as every gcd_hw number.
- **Design.** `collatz_hw` = gcd_hw's rig and clocked shell around `bdc_collatz`
  (`k2/collatz_rig.v`, `k2/collatz_hw.v`). It uses collatz's route-measured T3 sizes, renamed
  for the rig.
  - Seeds d, 4, 5, 6 routed. **Seed 3 did not place**: the nextpnr post-placement validity error
    that gcd_hw R5 seed 2 also hit. Seed 6 replaced it.
  - The `cells/` audits on all 4 routes (informative, not gated): rules A/H/I/F 0, rule E 0/18,
    arb_fork OK, rule D 6 (the screen).
- **xevents5** (`Events6.design_verdict`, the strongest event-level checker in the tree):

| seed | slow | fast | gb | mixed (indep) |
|---|---|---|---|---|
| d | **CLEAN** | **CLEAN** | **CLEAN** | RESIDUAL 3 |
| 4 | **CLEAN** | **CLEAN** | **CLEAN** | RESIDUAL 3 |
| 5 | **CLEAN** | **CLEAN** | RESIDUAL 2 (uenv1 −9, uenv0 0 ps) | RESIDUAL 2 |
| 6 | **CLEAN** | **CLEAN** | **CLEAN** | RESIDUAL 5 |

  - Every residual item is a timing margin ≤ 0. None is a structural gap.
  - On gcd_hw the same checker left 45 structural residual items per seed (A-events6). Collatz's
    control has none of those shapes: no reconverging-merge labels, no 3-way merge, no arbiter
    cascade.
  - The negative controls fail as they must (§2).
- **xaudit** (one transaction, vector 1: n = 2 → 1, seed d):
  - **one-corner bands do not certify it.** The first flag is at 32 ns slow and 25 ns fast,
    against 30.7 ns slow on gcd_hw;
  - **at w = 0 (the SLOW_MAX delay assignment, every power-up state) it certifies only at a
    10 ps step.** At 25 ps it does not, and at w = 0.02 it does not even at 10 ps (§3).
  - This is weaker than gcd_hw, which certified at w = 0.02 with 25 ps steps.
  - 6 concrete random samples at slow give the right answer (1).

## 1. Build (toolchain, seeds, md5s)

Everything is in `formal/tools-A/xaudit/k2/results/builds.txt`. In short:

- **Source.** `git archive 0922b8bc` exported to `~/k2src`, outside the repo. No worktree and no
  checkout. The frontend comes from `cloud/fixtures/frontend/collatz`.
- **Rig.**
  - `k2/collatz_rig.v` = `cells/hw/gcd_rig.v` with `bdc_collatz`, a 2-way fork (n, start), no
    probes, and a `{expected, n}` ROM derived from `kernels/collatz/collatz.c`. Vector 1 is
    n = 2 → 1 step: non-zero, so it is not the failure value.
  - `k2/collatz_hw.v` = `cells/hw/gcd_hw.v` minus the abs/cmp probe instrumentation.
  - `build_hw.sh` gets a `collatz_hw` case in the export only, by `k2/build_k2.sh`.
- **Command.** BOARD-QUEUE #2's, with the kernel swapped:

      [NEXTPNR_SEED=N] BD_SIZES=<T3 renamed> BDC_SELECT_PADS=<{}> BD_RLOC=v4 ./hw/build_hw.sh collatz_hw

  - The sizes are `research/data/collatz_sizes_T3.vh` with `BD_SZ_UUT_*` renamed to
    `BD_SZ_URIG_UDUT_*`. All 40 names match a `DELAY_` parameter of the emitted kernel.
  - The pads file is `{}`, i.e. emit's default, which is what the T3 build used.
  - No `--freq`, as in BOARD-QUEUE #2. No frequency is reported.
- **Routes.** About 30 s per seed. All four have 0 RLOC groups dropped and `fasm_audit PASS` (2089
  LUT sites). The bitstream step fails because textx is missing; no bitstream is needed or used.

| seed | collatz_hw.sdf | collatz_hw_routed.json |
|---|---|---|
| d | 054ca45d3b4a5b45 | 682c889bba672b33 |
| 4 | 96d2d94364d7eaf0 | b450db4da276b634 |
| 5 | 3ffc02e9068d899c | 48b7d037e5ba4569 |
| 6 | b136e8da8ceb5667 | 9427fe33981f4e60 |

- **Delays.** `xray_delay.py` is research 7dc5dde (md5 3e69bf6a), which is **newer than the
  gcd_hw runs' 801db02**: it also charges the slice routing-BEL muxes. It needs
  `XRAY_DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7`.
  - Per seed: 12,948 IC arcs, 10,523 of them from prjxray; about 11,595 IOPATH arcs.
- **Netlist.** `routed2x.py`, unchanged defaults (`--keep-prefix urig. --cut-net rig_rst`):
  - 2,324 cells kept, 2,436 LUT cells, 8,340 routed arcs (about a quarter of gcd_hw);
  - free inputs exactly `idx[3:0]` and `rig_rst`, the same cut shape as gcd_hw.

**No front-end change was needed** (routed2x, skel, cert6, ana5, analyze, fbrace and csim, as
committed). The k2 scripts are wrappers plus three generalisations:

- `negctl_k2.py`: finds the own-feedback pin from the netlist, because `events4/negctl.py`
  hard-codes gcd's `/I0` and pins are permuted per route;
- `--fuel 256`;
- a native-link fix (§4).

## 2. xevents5 on collatz (`k2/run_events_k2.sh`; results `k2/results/xe5_*.txt`, `table.txt`)

Pipeline per seed and corner: `events4/skel.py` → `events6/cert6.py` (untrusted) → `xevents5`
(Lean). `events5/ana5.py` runs alongside for comparison.

- **Skeleton.** 417 LUTs, of which 77 are storage with reset, and 5 cut nets.
- **Certificate.** 92 nodes: 8 virtual (H_ARB, the two control_merge arbiters) and 11 merges.
  - 161 Back pins: 138 plain, 23 multi, 22 filt, 10 guard;
  - 23 line pins;
  - cert6 errors 0 on every row.

**Fuel.** At the executable's default `--fuel 64`, seed d slow printed `VERDICT NOT RECOGNISED`
with 4 RECOG-FAIL lines (`k2/results/xe5_d_slow_fuel64.txt`):

- `ucond_br7_j`, `ulink_n28__1.ctl`, `umux1.uj0` and `umux1.uj1`;
- each has a pin path of 65 or 73 elements (cert6's `paths`), longer than the fuel.

`Recog6 … fuel` is a hypothesis of `design_verdict` for any fuel value, so 256 is as sound as 64.
At 256, Recog6 has 0 failures on every row. All rows below use `--fuel 256`.

Every row reads `Design.WF true; Recog6 node failures 0; Net4.OK true`.

| row | verdict line (as printed) | Back min margin | line min margin | ana5 |
|---|---|---|---|---|
| d slow | VERDICT CLEAN | 1111 | 2681 | MET |
| d fast | VERDICT CLEAN | 501 | 1237 | MET |
| d gb | VERDICT CLEAN | 705 | 1923 | MET |
| d indep | RECOGNISED, RESIDUAL 3 | −78 | −76 | NOT MET (3) |
| 4 slow / fast / gb | CLEAN / CLEAN / CLEAN | 228 / 98 / 65 | 3143 / 1461 / 2159 | MET |
| 4 indep | RECOGNISED, RESIDUAL 3 | −234 | 56 | NOT MET (3) |
| 5 slow / fast | CLEAN / CLEAN | 218 / 64 | 2754 / 1206 | MET |
| 5 gb | RECOGNISED, RESIDUAL 2 | −9 | 2005 | **MET** |
| 5 indep | RECOGNISED, RESIDUAL 2 | −516 | 159 | NOT MET (2) |
| 6 slow / fast / gb | CLEAN / CLEAN / CLEAN | 805 / 386 / 454 | 2596 / 1164 / 1484 | MET |
| 6 indep | RECOGNISED, RESIDUAL 5 | −196 | −579 | NOT MET (6) |

The residual items, exactly as printed:

- **d indep**:
  - Back `umux1.uj0` pin0 −78;
  - Line `ucontrol_merge1_f` pin0 −76 (W 1786, window 1862);
  - Line `ulink_n_index_11.many.stage[0]` pin0 −76.
- **4 indep**:
  - Back `ulink_n_falseResult_7.many.stage[2]` pin1 −121;
  - Back `urig.uenv1` pin1 −234;
  - Back `urig.uenv0` pin1 −27.
- **5 indep**:
  - Back `urig.uenv1` pin0 −516;
  - Back `urig.uenv0` pin0 −507.
- **5 gb**:
  - Back `urig.uenv1` pin0 −9;
  - Back `urig.uenv0` pin0 margin **0**. Strict margins are used, so 0 is a FAIL.
- **6 indep**:
  - Back `urig.uenv1` pin0 −196;
  - Back `umux0.uj1` pin0 −76;
  - Back `ulink_n_falseResult_7.many.stage[1]` pin0 −138;
  - Line `ucontrol_merge1_f` pin0 −579 (W 2054, window 2633);
  - Line `ulink_n_index_11.many.stage[0]` pin0 −579.

Notes on these:

- **5 gb.** It is the same element as gcd_hw's only gb residual, which was on seed 5 too (`uenv1
  ← uenv0`, −61 ps). It is the rig's environment C-elements, not the kernel. ana5 calls it MET,
  because it is not strict at 0 and uses another per-pin rule. The Lean checker is the one that
  counts.
- **gcd vs collatz.** On gcd_hw, xevents5 left 45 structural items per seed at one corner (U3,
  the 3-way merge, the cascade, guarded multi-copy pins). On collatz it leaves none. The newer
  xevents7, which closes those classes on gcd, is described in `notes/A-events7.md`, but its
  `Events7Cert/Beh/Main.lean` are not in the tree (only `Events7Core`/`Events7Excl`;
  `git log --all` has no `Events7Main.lean`). At the time of §2, therefore, xevents5 was the strongest checker that could be run. They have since been rebuilt (E7r); see §5.

**What a CLEAN row is.** It is a theorem instance of `Events6.design_verdict` about every
behaviour of the parsed routed netlist: every real control node's output is the phase of its
event counter.

- Hypotheses:
  - per-pin `SatPin`: every element is in its band, and the bands are prjxray's through the
    trusted parser;
  - `H_ARB`: the 8 arbiter virtual nodes, unchecked;
  - `SelOK`: select bundling, the question of rule E. skew.py says 0/18 violated, but that is not
    proved;
  - `GuardOK`: 10 guarded pins, W-E4g, open;
  - `hrst`: one reset pulse from t = 0.
- Not covered: datapath values and the answer; metastability; the clocked shell; anything outside
  the bands; any other route.
- One route is a sample: 4 seeds are the spread. The gb row is clean on 3 of 4.

**Negative controls** (seed d slow; `k2/results/xe5_d_slow_NEG*.txt`, `neg.txt`):

- **NEG-fb1500**: +1500 ps on `ucontrol_merge0.uarb1.ua2`'s own feedback (I4, found by
  `negctl_k2.py`), gcd_hw's value. It prints **CLEAN**, with that pin's Back margin moved to 554
  ps (the lowest). The stage's original margin is 2054 ps, so 1500 ps is too small a defect on
  this route. That is why the control below exists.
- **NEG-fb3000**: `RESIDUAL Back urig.udut.ucontrol_merge0.uarb1.ua2.u pin1: margin -946`,
  `VERDICT RECOGNISED, RESIDUAL 1`. It fails, as it must.
- **NEG-recog** (the certificate claims `ucmpi2.ujoin`'s feedback input is its reset input):
  `RECOG-FAIL urig.udut.ucmpi2.ujoin.u.genblk1.g2.u.u`, `VERDICT NOT RECOGNISED`. It fails, as it
  must.

## 3. xaudit on collatz (`k2/run_xaudit_k2.sh`; results `k2/results/xa_d_*.summary.txt`)

The run:

- seed d, vector 1, `rig_rst` released at 20 ns, timed engine with `--timed-only --all`;
- native xaudit, built by `mk_k2.sh` + `build.sh` + Parse (§4). It is byte-identical to the stored
  `results/pipe3_slow_corner.txt` on pipe3;
- concrete latency (`gcd/csim.py --mode hi`): rig_lap rises at 181.1 ns slow and 89.2 ns fast,
  with `rig_res_data = 0x1`.

| bands (step) | control storage: clean / STORED / UNRESOLVED (of 77) | first flag | rig_lap binary 1? | wall, RSS |
|---|---|---|---|---|
| slow (25 ps), 220 ns | 5 / 5 / 67 | 32.35 ns STORED `ucond_br2_j`; first UNRESOLVED 34.8 ns `ulink_n_falseResult_3` stage 0 | no (X from 148.4 ns) | 249 s, 0.95 GB |
| fast (25 ps), 120 ns | 5 / 4 / 68 | 25.2 ns `ucond_br2_j` | no (X from 70.2 ns) | 100 s, 0.56 GB |
| slowmax w = 0 (25 ps) | 18 / 26 / 33 | 61.2 ns STORED `umux0.uj0`; UNRESOLVED from 135.7 ns (`ulink_n_trueResult_4`) | no (X from 173.2 ns) | 101 s |
| slowmax w = 0.02 (25 ps) | 18 / 30 / 29 | 46.2 ns | no | 115 s |
| slowmax w = 0.05 (25 ps) | 5 / 25 (+1 GLITCH) / 46 | 45.5 ns | no | 173 s |
| **slowmax w = 0 (10 ps)** | 18 / 48 / 11 (all at ≥ 206.8 ns, after the lap) | 120.2 ns STORED (bounded) | **yes, from 183.12 ns; res = 1** | 309 s, 2.25 GB |
| slowmax w = 0.02 (10 ps) | 18 / 32 / 27 | UNRESOLVED from 138.0 ns `ulink_n_trueResult_4` | no (X from 176.5 ns) | 486 s, 2.25 GB |
| slowmax w = 0.05 (10 ps) | 18 / 30 / 29 | 46.1 ns STORED `ulink_n14__1` stage 0 | no (X from 170.6 ns) | 537 s, 2.25 GB |

**The certified run** is slowmax w = 0 at a 10 ps step. For every power-up state, with every
element at its SLOW_MAX delay (± its 10 ps rounding):

- rig_lap is 0 on [14.8, 179.1] ns and 1 from 183.12 ns to the 220 ns horizon;
- rig_res_data = 1 (binary) at 183.12 ns;
- rig_ok = 1 on [186.9, 214.4] ns;
- rig_err = 0 on [16.5, 215.8] ns.

It is one delay assignment, not a band. The 25 ps run of the same assignment loses it: the
per-element rounding is up to 1 step, accumulates over the ~180 ns path, and the STORED windows
grow to 7 ns by 140 ns.

**The flags are imprecision, not races, on the evidence available:**

- `gcd/fbrace.py` (`k2/results/fbrace_all.txt`) finds 0 own-feedback candidates at slow and
  fast on all 4 seeds, and at indep on seed d. Seeds 4, 5 and 6 at indep have 1 each:
  `ulink_n_falseResult_7` stage 2 (−42 ps), `urig.uenv0` (−428 ps) and
  `ulink_n_falseResult_7` stage 1 (−59 ps). The same elements show up in xevents5's mixed
  residuals;
- 6 random concrete samples in the slow bands all deliver `rig_res_data = 0x1` at 165.1–166.6 ns
  (`k2/results/csim_d_slow_rand.txt`);
- the w = 0.02 loss starts at a cond_br output (`ulink_n_trueResult_4`, 138 ns), where the
  select's X window (the n == 1 / parity compare, through CARRY4 chains) overlaps the request's.

That is the bundling margin as the X-window abstraction sees it. It is not a demonstrated race.
**Unlike gcd_hw (certified at w = 0.02 with 25 ps steps), collatz's transaction is not certified
for any band of non-zero width.**

## 4. Tooling notes (what had to be worked around)

- **Lean.** Mathlib was still building from source. Neither executable imports Mathlib, so
  `k2/mk_k2.sh` compiled their 27 dependency modules through `lean.sh`/`slot.sh` into
  `~/k2olean`, with no lake build. All exited 0; the logs contain no "sorry" and no "error".
  - `xevents5` ran as `lean --run Formal/Core/XAudit/Events5Main.lean`, with the overlay, all
    jobs in one slot.
  - Native xaudit (Parse step run by hand, then codified in `mk_k2.sh NATIVE=1`): `build.sh` fails to link (`undefined symbol:
    initialize_formal_Formal_Core_XAudit_Parse`) because its MINE list predates `Parse.lean`.
    `mk_k2.sh NATIVE=1` emits Parse's C and relinks. **Lead: add
    `Formal/Core/XAudit/Parse` to `build.sh`'s MINE**, or rely on `lake exe xaudit`.
- **Toolchain.** The restored binaries need apt `libtcl8.6` and boost 1.83
  python/filesystem/program_options, plus `zstd` and `iverilog`. `toolchain.sh` cannot see this.
  xray_delay needs `XRAY_DB` and pip `simplejson` + `intervaltree` (in `~/k2tools/pylib`).
- **The cells audits** need `tighten.py --osc dhk --osc invhk`, as `tighten_loop.sh` passes for
  gcd_hw. Without it they abort on the housekeeping ring.

## 5. xevents7 on collatz (added after the Events7 rebuild, E7r)

`k2/run_events7_k2.sh`; results `k2/results/xe7_*.txt`, `cert7_*.txt`, `table7.txt`.

- **How it was run.** The pipeline is `skel.py` → `events7/cert7.py` (untrusted) → `xevents7`.
  - xevents7 runs as `lean --run Formal/Core/XAudit/Events7Main.lean` on `~/k2olean`, through
    slot.sh, at most 2 jobs at once, with `--fuel 256`.
  - `Events7{Core,Excl,Cert,Beh}` were compiled into that overlay with `lean.sh`. All exited 0,
    with no error or sorry in the logs.
  - All 18 outputs are non-empty. The full batch took 5 min.
- **Verdicts.** They are identical to xevents5 on every row, with the same residual items, names
  and margins, row by row:
  - slow and fast: CLEAN on d, 4, 5 and 6;
  - gb: CLEAN on d, 4 and 6; seed 5 has RESIDUAL 2 (`urig.uenv1` −9, `urig.uenv0` 0);
  - mixed: RESIDUAL 3 / 3 / 2 / 5.
- **What every row prints.**
  - `Net4.OK7 true; guarded delay-line pins 0`;
  - `select partitions (SelPart): []`, so the SelPart hypothesis is vacuous here;
  - the derivation log is accepted by `runLog`;
  - merges 11/11, 0 of them with more than 2 arms;
  - cert7 errors 0.
- **Negative controls.**
  - NEG-fb3000 gives `RESIDUAL Back urig.udut.ucontrol_merge0.uarb1.ua2.u pin1: margin -946`,
    `RESIDUAL 1`.
  - NEG-recog gives `RECOG-FAIL urig.udut.ucmpi2.ujoin…` and `NOT RECOGNISED`.
  - Both fail, as they must.
- **Reading.** Collatz's control has none of the shapes xevents7 adds over xevents5: U3 labels
  through reconverging merges, n-ary merges, the cascade, and guarded multi-copy pins. So on this
  kernel the two checkers certify the same rows.
  - A CLEAN row from xevents7 is an instance of `Events7.design_verdict7`.
  - Its hypotheses are per-pin SatPin, H_ARB (HARB7), SelOK, SelPart (vacuous here), GuardOK and
    the reset pulse.
  - It does not cover the datapath, the answer, metastability or other routes.
- **Which checker to prefer.** Use xevents7 for any new kernel. On gcd_hw and collatz it certified
  every row xevents5 certified (an observation, not a theorem), and it also closes the gcd_hw
  classes. Run xevents5 only as a cross-check.

## Files

| file | status |
|---|---|
| `formal/tools-A/xaudit/k2/collatz_rig.v`, `collatz_hw.v` | the rig and shell (built only in the export; never on a board) |
| `k2/build_k2.sh` | export + build_hw case + sizes rename + 4-seed build + md5 |
| `k2/bands_k2.sh` | xray_delay + routed2x at slow / fast / indep / gb |
| `k2/run_events_k2.sh` | skel → cert6 → xevents5 (`--fuel 256`, one slot) + ana5 + negative controls |
| `k2/run_xaudit_k2.sh` | xaudit runs + analyze.py + fbrace |
| `k2/run_events7_k2.sh` | skel → cert7 → xevents7 (≤ 2 jobs, `--fuel 256`) + NEG-fb3000 / NEG-recog |
| `k2/negctl_k2.py` | NEG-fb with the feedback pin found from the netlist |
| `k2/mk_k2.sh` | oleans without lake build; `NATIVE=1` native xaudit |
| `k2/v1_220ns.stim.json`, `v1_120ns.stim.json` | stimuli |
| `k2/results/*` | builds.txt, table.txt, xe5_* (16 + fuel64 + 3 NEG), cert6_*, ana5_*, xa_d_*.summary.txt, fbrace_d.txt, fbrace_all.txt, csim_d_slow_rand.txt, neg.txt |
| `formal/out/HOWTO-new-kernel.md` | the procedure, verdict meanings and hypotheses |

No Lean file was written. No lakefile or root-import change is needed for this probe. One request
to the lead: add `Formal/Core/XAudit/Parse` to `tools-A/xaudit/build.sh`'s MINE list, or rely on
`lake exe xaudit` once it is built.
