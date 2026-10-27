# BQ#1 audit: routed GLS of gcd_hw (default seed, pads 13/14/13, BD_RLOC=v4)

Auditor subagent, 2026-10-27. All of my own files are in `audit/bq1/`. Build outputs are in the
untracked `cells/build/` of `/home/user/wt-rb1` (detached at claude/research 19a93c1). I did not
edit any tracked file, and I did not touch git, wt-research or wt-formal.

## Claim under test
BOARD-QUEUE #1: on this route (sdf md5 6f8b99e6), routed GLS gives "16/16 vectors, errs=0, laps
19-2719 per 150 us window".

## Inputs
- Route: `/home/user/wt-rb1/cells/build/hw/gcd_hw/`, already rebuilt by the caller.
  - sdf md5 is `6f8b99e6c49bb7ef8855c881cecabe5c`, which matches the claim.
  - **routed.json md5 is `5703039032088ede6776809354a260fa`. BOARD-QUEUE says `1c6a1fb9`.** The
    SDF and the bit payload match, so this is likely non-deterministic serialisation in the
    nextpnr JSON. It is not resolved here: BOARD-QUEUE's json md5 does not reproduce.
- Provenance printed by build.sh: `audit/bq1/build.log`.

## 1. Their flow (the system under test)
    source ~/auditlogs/export_dev2.sh
    cd /home/user/wt-rb1/cells
    bash gls/build.sh gcd_hw         # audit/bq1/build.log
    bash gls/run.sh gcd_hw -j 3      # audit/bq1/run_sh.log, ~5 min

Their verdict lines, all `RESULT timeout`, each with errs=0 and oks=laps:

| vec | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| laps (run.sh) | 2650 | 1888 | 164 | 137 | 325 | 119 | 24 | 86 | 77 | 74 | 325 | 34 | 19 | 28 | 134 | 89 |

I did **not** run `vvp gate.vvp`, the SDF-annotator acceptance gate (ANNOTATE_DONE with 0 SDF
warnings). That part of the claim is UNVERIFIED by me.

## 2. Independent judge (no MISM / rig_err / rig_ok)
How the judge is built:
- **Testbench:** `audit/bq1/tb_judge.v` is my own top. It instantiates the same `top dut()` and
  drives it the way tb_run.v does: it forces hk_fb low for 50 ns and forces the idx flops to the
  vector. Everything else is the design's own.
- **Net names:** these come from nextpnr's `routed.json` netnames through my
  `audit/bq1/mkvh.py`, not from their signals.vh. I checked that gen.py names a net `n<json bit>`
  (rig_res_data[0] = n53078, rig_lap = n56021).
- **What it prints:** `rig_res_data[31:0]` (= `urig.res_data` = out0_data) at every rise and fall
  of rig_lap, any change of res_data while lap is high, and idx at the release of rig reset.
- **Compile:** I used their exact compile line against their netlist_baked.v, from
  `audit/bq1/nominal/`:

      iverilog -gspecify -DGLS_TRANSPORT_IC -I. -o judge.vvp ../tb_judge.v <WORK>/netlist_baked.v cells/gls/prims.v
      vvp judge.vvp +VEC=v +TEND=150000      (16 vectors, -P 3)

- **Checker:** `audit/bq1/check.py` compares every captured value, at rise and at fall, to
  `audit/oracle/oracle_out.txt`. A vector passes only if laps > 0, every value equals the oracle
  gcd, and idx at reset release equals the vector.

Result (`audit/bq1/check_nominal.txt`):

| vec | a | b | gcd | laps (mine, 0-150 us) | laps (run.sh) | values seen | correct |
|---|---|---|---|---|---|---|---|
| 0 | 0 | 5 | 5 | 2633 | 2650 | 0x5 | Y |
| 1 | 7 | 0 | 7 | 1876 | 1888 | 0x7 | Y |
| 2 | c | 12 | 6 | 163 | 164 | 0x6 | Y |
| 3 | 30 | 12 | 6 | 136 | 137 | 0x6 | Y |
| 4 | 1 | 1 | 1 | 323 | 325 | 0x1 | Y |
| 5 | 11 | 5 | 1 | 118 | 119 | 0x1 | Y |
| 6 | 798f20 | 12b87ca0 | 20 | 24 | 24 | 0x20 | Y |
| 7 | 42f | 1ce | 15 | 85 | 86 | 0x15 | Y |
| 8 | 10e | c0 | 6 | 76 | 77 | 0x6 | Y |
| 9 | 10000 | 1000 | 1000 | 74 | 74 | 0x1000 | Y |
| 10 | 18697 | 18697 | 18697 | 323 | 325 | 0x18697 | Y |
| 11 | 1e240 | c0a14 | c | 34 | 34 | 0xc | Y |
| 12 | 7fffffff | 2 | 1 | 19 | 19 | 0x1 | Y |
| 13 | f4240 | f423f | 1 | 28 | 28 | 0x1 | Y |
| 14 | 24 | 3c | c | 133 | 134 | 0xc | Y |
| 15 | 400 | 300 | 100 | 88 | 89 | 0x100 | Y |

Across 16/16 vectors, every delivered value matches the oracle. That is 6,149 laps checked at
both edges, with 0 mid-lap changes and idx correct on all 16.

My lap counts are about 0-17 lower than run.sh's. This is expected: tb_run.v stops at the 1 us
watchdog tick after TEND, so it simulates 151 us, while mine stops at exactly 150 us. Vector 0
runs at about 56 ns/lap, so one extra microsecond is about 17 laps.

**Limitations:**
- res_data is sampled at its driver net (LUT output), not at the rig's compare sinks.
- The kernel's a/b operands are constants folded from idx, so they cannot be observed directly.
  Vector selection is checked through the idx nets plus distinct lap counts. Several vectors share
  a gcd (4/5/12/13 all give 1; 2/3 both give 6).
- As in their bench, only the first window is run, with idx forced and the sequencer not
  exercised.

## 3. Laps compared with what research reports
The JOURNAL 2026-10-25 21:50 table aggregates 4 seeds (d, 2, 3, 4):

| vec | journal range (4 seeds) | this route |
|---|---|---|
| 0 | 2650-2719 | 2650 |
| 4 | 325-333 | 325 |
| 6 | 24-26 | 24 |
| 12 | 19-20 | 19 |
| 13 | 28-29 | 28 |

All of this route's numbers fall inside the journal's ranges, at the low end. This route's range
is 19-2650, inside the claimed "19-2719", whose upper end comes from another seed. I found no
per-vector lap list in JOURNAL for the default-seed route itself; the journal says the full logs
are in session-local r2/*.gls_run.log. The "19 to 2626" at JOURNAL 19:21 belongs to an earlier
pad set (sdf e9bbd1f2), not to this route.

## 4. Negative controls
**A. uori4 matched delay zeroed.**
- **How the SDF was made:** `audit/bq1/zero_uori4.py` writes a copy of the SDF with uori4's
  bd_delay_gated chain set to 0: 84 chain INTERCONNECTs and 167 IOPATHs. The gate wires from
  ujoin are kept. The copy is `audit/bq1/neg_uori4.sdf`, md5 51b61186.
- **Where it was built:** as the separate design dir `cells/build/hw/gcd_hw_neguori4/` (same
  routed.json, mtime preserved), with `build.sh gcd_hw_neguori4`. The baked netlist differs from
  nominal in exactly 168 lines (84 ICBUF + 84 cell arcs).
- **Result** for vectors 6, 12 and 13, from their run_baked.vvp and from my judge
  (`audit/bq1/check_neg.txt`):

  | vec | their verdict | my judge |
  |---|---|---|
  | 6 | `laps=1 errs=1 oks=1` | FAIL: 1 lap, value `xxxxxxxx`, then the ring wedges |
  | 12 | `laps=1 errs=1 oks=1` | FAIL: 1 lap, value `xxxxxxxx`, then the ring wedges |
  | 13 | `laps=1 errs=1 oks=1` | FAIL: 1 lap, value `xxxxxxxx`, then the ring wedges |

  Both judges flag the fault. The failing answer is X, not a definite wrong number. Side note: the
  rig's compare of an X raises *both* err and ok, so the in-rig "oks" count is not a correctness
  witness on its own.

**A'. uori4 chain scaled to 25%** (`scale_uori4.py`, SCALE=0.25, design dir
`gcd_hw_neguori4q`):

| vec | laps | correct |
|---|---|---|
| 6 | 33 | all correct |
| 12 | 26 | all correct |
| 13 | 37 | all correct |

All three still pass, in both their flow and mine (`check_negq.txt`). So uori4's emitted delay
carries more than 4x slack in this simulation, which matches the journal's remark that the emitted
estimates are oversized. The negative control only bites near 0.

**B. Trivial checker control.** I changed vector 6's gcd to 0x21 in `oracle_corrupt_v6.txt`.
check.py then flags vector 6 FAIL (48 of 48 samples bad) and leaves vector 12 PASS
(`check_corrupt_oracle.txt`).

## Verdicts
- **"16/16 vectors, errs=0 in routed GLS" on the BQ#1 route (sdf 6f8b99e6): CONFIRMED.**
  - Their own flow gives 16/16 errs=0.
  - My judge, independent of the rig, finds every delivered gcd correct against the dynamatic
    oracle, on every lap, on all 16 vectors.
  - Laps are consistent with the journal's ranges.
  - Caveats: the annotator gate (`vvp gate.vvp`, no SDF warnings) is UNVERIFIED by me, and
    routed.json's md5 does not match BOARD-QUEUE's `1c6a1fb9`.
- **Negative control: CONFIRMED.** The GLS plus both judges fail when uori4's matched delay is
  removed: X result, then deadlock, on 6/12/13. The checker fails on a corrupted oracle. Caveat: the
  fault has to be severe (25% of nominal still passes).
