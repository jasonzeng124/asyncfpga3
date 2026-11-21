# C-10e: tcheck, the verified timing checker as a compiled executable on real routes

## Verdict

**It works for rules H and I (the link obligations Hold and Sep/capture) on four real
gcd_hw routes. Rules A, E, F and J are not covered yet; that would take about 1-2 days more.**

- `tcheck` is a `lake exe` built from core Lean. Its core is 10a's proved checker, run
  through 10d's one-pass `checkArr`.
- An untrusted Python front end (`extract.py`) turns a routed gcd_hw (nextpnr routed JSON,
  SDF and FASM) into race netlists. It produces 1398 instances per route: 233 obligations
  times 6 corner variants.
- tcheck checks all of them in about 0.5 s per route.

Row-by-row results against tighten.py on the same route:
- **H:** 157/158 rows agree on seeds d and 2, and 158/158 on seeds 3 and 4.
- **I:** 75/75 rows agree on all four seeds.
- **Disagreements:** there are 2 in 932 rows, both on rule H. Both are cases where rule H
  passes and tcheck fails, and they are explained below.
- **Not audited:** both tools leave the same 21 H rows and 104 I rows unaudited.

### Theorems (file `formal/tools/tcheck/Tcheck/Sound.lean`, no sorry, axiom or native_decide)
The axiom audit (`test/Axioms.lean`) shows only propext, Classical.choice and Quot.sound.
- `Tcheck.verdict_sound`: suppose `verdict i = true`, which is what tcheck prints as PASS
  (`decide WF && checkArr`). Then in every 10a `Run` of the instance's netlist, every data
  change precedes every request change by at least `setup`.
- `Tcheck.verdict_sound_fixed`: the same for `FixedRun`.
- `Tcheck.margin_eq`: the printed margin is 10a's `slack`.
- `Tcheck.window_eq`: the printed windows are 10a's `win`, which are sound and exact by
  `changes_in_window` and `win_exact`.

### What is trusted rather than proved
- the Lean compiler, because `lake exe` runs compiled code;
- the 60-line text parser in `Main.lean`;
- that the netlist `extract.py` emits is the right netlist for the routed circuit. This is
  the large part; see the hypotheses below.

## Run it

    cells/verify/toolchain.sh                     # all ok; nextpnr sha256 9c732bc6303458df
    formal/tools/tcheck/route.sh d                # also 2, 3, 4. Each copies cells/ and bdc/ into
                                                  # build/tree_SEED, runs build_hw.sh gcd_hw, then
                                                  # skew.py, tighten.py and arb_fork.py
    formal/tools/tcheck/run.sh d 2 3 4            # drift check, lake build, toy self-test,
                                                  # extract, tcheck and compare for each seed

- **Outputs** go to `formal/tools/tcheck/build/` (gitignored):
  - `obl_S.tc`: the instances;
  - `tcheck_S.out`: the verdicts;
  - `compare_S.tsv`: one row per controller;
  - `obl_S.json`: the obligation list plus a census of fallback arcs.
- **One lake command:** `FORMAL_SLOT_CWD=$PWD ../../slot.sh lake build`. Without
  FORMAL_SLOT_CWD, slot.sh cds into formal/lean. See "Incident".
- **Self-test:** `test/toy.tc` against `test/toy.expected`. It has a pass (+208), a fail
  (-172) and an ill-formed netlist. It is the negative control that shows the checker can
  fail; the two real H failures show the same on real data.

## Routes (one route is a sample: 4 seeds)

All four routes come from nextpnr **9c732bc6303458df** (toolchain.sh all ok). They use the
journal's 21:40 settings: `BDC_SELECT_PADS=cells/hw/gcd_hw_pads.json` (13/14/13), `BD_RLOC=v4`,
and `NEXTPNR_SEED` = default, 2, 3 and 4. The FASM files are distinct.

| seed | fasm sha256 | routed.json | sdf | rule E | rule J | tighten problems |
|---|---|---|---|---|---|---|
| d | b73e1ba0e4cba92f | d1c47c14a5d10750 | b238cc1aacf4d54c | 0/118 violated | pass | 38, all rule D (the documented screen) |
| 2 | 1ee50d56638ef0b3 | 440d6ac779127dff | a7e7806746f83ac2 | 0/118 | pass | 38 D |
| 3 | 855635c4ebed15e5 | a9cf84a060d48473 | b6613fcb0eea5b0f | 0/118 | pass | 38 D |
| 4 | b56d32b1eecdaed9 | dc1e100f3c870c88 | 8186915de320055b | 0/118 | pass | 38 D |

This reproduces research/JOURNAL.md 21:40: rules E, J, A, H and I clean, 38 D. Seeds d and 3
failed only at the bitstream step: FASM2FRAMES raised a circular-import error in the fasm
Python package. That is very likely a race between the four parallel builds compiling the
package's .pyc files. The route, SDF and FASM were complete, so the rules were run by hand
on them. No bitstream is needed here.

## Corner model (the variants; every instance is emitted in all six)

| variant | per-arc interval | reading |
|---|---|---|
| `sdf` | [d, d], nextpnr's number | what the rules read; for comparing the algorithm |
| `sdfband` | [0.772 d, 1.155 d] | skew.py's GUARD_LO/GUARD_HI applied to the SDF |
| `fast` / `slow` | prjxray [fast_min, fast_max] / [slow_min, slow_max], plus Elmore RC | H_ONE_CORNER, H_RC_EXACT |
| `fastG` / `slowG` | the corner interval widened by 0.772/1.155 | H_ONE_CORNER plus local scatter = the project's guard band |

- **tcheck VERDICT** = PASS at both fastG and slowG, with setup 0. The corner and scatter
  band replace rule A/H/I's `max(0.2 t, 200)` guard.
- **prjxray numbers per arc:**
  - LUT pin to O6/O5: prjxray-db LUT6 arc for the physical pin.
  - CLB-LUT-pin interconnect: an RC tree over the ON pips of the driver's site pin, found
    by walking the FASM back from the sink's physical pin (prjxdelay's `ringdelay.Net` and
    fasm2lean's `Extract.walk`, imported read-only).
  - The LUT's own feedback wire is handled the same way.
- **Fallback (H_FALLBACK_BAND):** about 7.5k of 72k arcs per route have no prjxray number
  and keep the SDF band in every prjxray variant. These are MUXF7/F8 (SELMUX2_1), CARRY4,
  FF, site-internal hops, and about 100-130 sinks where fasm2lean's walk dies on a
  "floating" long-line node (LV/LVB). Each instance prints `fallback=k/n`.
  - **H rows:** 0 fallback arcs.
  - **I rows:** 68-92 of 365 arcs fall back, all on the data (compute) side. At the fast
    corner that is pessimistic, because the SDF band does not shrink; at the slow corner it
    is roughly neutral.

## Obligations (`extract.py`)

These are per bd_latch controller `ctl` (one link stage), using tighten.py's own structural
helpers: `latch_enables`, `latch_data_pins`, `starts_reaching`, the false-arc cut, storage
census, `--osc dhk --osc invhk`, and the FASTFALL/FASTRISE side-arc sets.

- **I (capture: 8e's Sep plus latch setup).**
  - Launch: the rise of an upstream `up` whose latch feeds `ctl`.
  - Request (must be late): up→ctl (rise), ctl→up (ack), up→ctl (fall), then ctl→enable→
    latch out, merged as "first bit closes".
  - Data (must be early): up→up's enable→its latch Q→all paths→ctl's D pins→latch out→own
    feedback pin.
  - A storage crossing on the request side is passed through from the input on the path.
    A C-element fires on its last input, so this is a lower bound on the side that must be
    late, which is sound.
- **H (hold: 8e's Hold).**
  - Launch: the fall of `ctl`.
  - Data (must be early): ctl→enable→latch out.
  - Request (must be late): the earliest disturbance of a D pin of ctl's own latch,
    crossing state nodes, as in `earliest_disturbance`.
  - **H_EXTRACT_MIN (unverified):** the state-node path is picked by Dijkstra in Python on
    the SDF lower bounds and emitted as one chain. The checker's lower bound is only as good
    as that choice, and with prjxray numbers a different path could be shorter.
- **Unrolling:** every segment between state nodes is the sub-DAG of all arcs on its paths
  that do not pass through storage. Rules H and I collapse a segment to one min or max
  number; here the checker computes it. Segments are unrolled with node copies, which gives
  a DAG with launch = node 0.

## Row-by-row comparison and every disagreement

**Algorithm agreement (variant `sdf` against tighten's raw margin, before the guard):**
- Most rows are identical to the picosecond. For example, H on
  ulink_n106__1 stage[0]: data 7349, enable 867, raw 6482 in both.
- Some rows differ (per route: H 5-10 of 158, I 7-11 of 75), all explicable:
  - **I** (36 rows over 4 seeds): tcheck is higher by 3..229 ps. tighten adds the max LUT
    arc and the max loop wire of the latch instance, independently of the bit. tcheck
    follows each D pin through its own output and its own feedback pin, so it is exact per
    path where tighten is decomposed.
  - **H** (33 rows): tcheck is lower, so more conservative, by 2..556 ps. The likely cause
    is not verified: my Dijkstra lets the path re-cross `ctl` itself after the first state
    node, using its FASTRISE taps, and tighten never re-enters the start node. Either way
    tcheck's number is a bound that is no larger, so no verdict flips from this.

**Verdict disagreements (tcheck FAIL, tighten PASS): 2 of 932 rows, both H, both 7-arc paths
with 0 fallback arcs:**

| seed | controller | tighten (guarded / raw) | tcheck sdf / sdfband | fast / slow | fastG / slowG |
|---|---|---|---|---|---|
| d | ulink_n_falseResult_55 stage[1] | +654 / 854 | 854 / 494 | 138 / 373 | **-28 / -19** |
| 2 | ulink_n143 stage[1] | +564 / 764 | 764 / 343 | 136 / 230 | **-60 / -207** |

- **Why:** the disturbance is short: ctl falls, 2 state nodes fire, about 1.27 ns in the
  SDF. The enable-close path costs 419 ps in the SDF but 800 ps at the prjxray slow corner.
  The SDF charges 25 ps per site pin; prjxray charges up to about 0.5 ns on A1/A2. This is
  10b's site-pin finding, now on a shipped route.
- **What it means:** unguarded, both prjxray corners pass (+136..+373 ps), so this is not a
  predicted failure. It fails only once the project's own 0.772/1.155 scatter band is
  applied to the prjxray corner. tighten's flat 200 ps guard on SDF numbers is weaker than
  that band, which is 10b's rule A finding, here on rule H. These are 1 route in 4 and 1 in
  4, so the margin is thin, not violated.
- **Fixed during the run:** an earlier extract run reported 1-3 I failures per seed at
  fastG. They came from my bug: I classed the LUT's own routed feedback wire (O6→own A pin,
  an INTERCONNECT) as a cell arc, so it fell back to the SDF band. With the fix every I row
  agrees.

**Minimum margins per route** (ps; tighten guarded; tcheck by variant):

| seed | rule | tighten | sdf | sdfband | fast | slow | fastG | slowG |
|---|---|---|---|---|---|---|---|---|
| d | H | 514 | 714 | 386 | 138 | 373 | -28 | -19 |
| 2 | H | 514 | 714 | 343 | 136 | 230 | -60 | -207 |
| 3 | H | 514 | 714 | 386 | 196 | 435 | 11 | 23 |
| 4 | H | 514 | 714 | 386 | 440 | 988 | 208 | 461 |
| d | I | 2704 | 3057 | 1525 | 1001 | 2350 | 213 | 570 |
| 2 | I | 2472 | 2908 | 1327 | 944 | 2168 | 233 | 563 |
| 3 | I | 2663 | 2917 | 1534 | 1260 | 2906 | 366 | 957 |
| 4 | I | 2068 | 2627 | 939 | 893 | 1952 | 289 | 586 |

- **I:** the worst fastG margin is about 200-370 ps, roughly 10% of the tighten margin. The
  fast corner shrinks the long request side (four segments of LUT chains) more than the data
  side, partly because of fallback.
- **H:** the worst row moves by route: from -207 to +208 ps at the guarded slow corner.
  That spread is route scatter.

## Not done, and why
- **Rules A, E, F, J.** The same machinery applies: a segment DAG plus variants.
  - **E** needs skew.py's launch choice (cand[:4]) and its level/lap rule. 10b shows the lap
    rule is a protocol fact, not a timing one.
  - **A** needs `check`/`check_bundled`'s confine sets.
  - **J** needs arb_fork's paths.
  - Estimate: 1-2 days, mostly reproducing each rule's pairing.
- **B's `cell_constraints.json`** was not read: it does not exist yet (`formal/out/` is
  absent).
- **H's "outside" data branch** (tighten's `t_ext`, data released by the environment) is not
  modelled. On these routes tighten's worst rows were all "sender".
- **bd_link_dc controllers** are skipped. gcd_hw has none on this build: every row with
  `skip` would show up, and none did (checked: 0 skipped).
- **The SDF alternative for intervals** is the `sdf`/`sdfband` variants (nextpnr's SDF);
  that is supported. **The FASM-derived netlist** is used only for the per-sink prjxray
  delays. The graph is the SDF/routed-JSON one, so a netlist built from the bits (11b) is
  not the graph source.
- **The 10d array checker** (`WinArray`) is reused verbatim. 10d's `routed2lean` (LUT-only,
  per-launch DAGs, emitted as Lean data) is not used: tcheck needs no kernel `decide`.

## Hypotheses (each needs a test)
- **10a `Run` semantics:** H_LAUNCH, H_BOUNDED_DELAY per arc, H_QUIESCENT, H_LOCAL and
  H_ZERO_DELAY_FN. The windows are hulls, so polarity is ignored: prjxray has no rise/fall
  split. Test: GLS at the corners.
- **H_ONE_CORNER plus scatter band:** the die sits at one prjxray corner and each element
  lies within 0.772/1.155 of that corner's interval. Unvalidated: 10c shows silicon at
  0.61-0.68 x slow_max for the ring population, which is inside, but within-die scatter is
  not measured per route. Test: two-path on-die measurements, the κ estimator of shard A.
- **H_FALLBACK_BAND:** arcs with no prjxray number lie in the SDF band. Not a bound, and
  pessimistic at the fast corner. Fix: add the CARRY4/MUXF/FF arcs from prjxray-db
  slicel.sdf, and follow LV long lines in fasm2lean.
- **H_EXTRACT_MIN** (rule H, see above); **H_SEGMENT** (storage crossing as pass-through on
  the late side).
- **Structural identification:** the obligation shapes come from tighten.py's helpers,
  unverified; their link to 8e's `checkPipe` races is by hand, not by theorem. Closing that
  gap means emitting 8e's `race2` instances per stage from the netlist (Phase 3).

## Incident (the lead should know)
- **What happened.** My first `../../slot.sh lake build` ran from formal/tools/tcheck, but
  slot.sh cds into formal/lean unless `FORMAL_SLOT_CWD` is set. So it ran
  **`lake build` in formal/lean**, which the brief forbids.
- **How long and what it touched.** It was compiling Mathlib/Aesop/Batteries under
  formal/lean/.lake/packages for about 17 minutes until I killed it (pid 1673). It touched
  only formal/lean/.lake (packages' build dirs); no source, lakefile or manifest. The proxy
  log shows refused connections to cache.mathlib.org from it.
- **What to check.** Whether any half-written olean or trace was left under
  formal/lean/.lake/packages/*/.lake/build. lake writes per module, so a killed module has
  no olean.
- **Fixed.** `run.sh` now always passes `FORMAL_SLOT_CWD`.

## Dependency decision
I did not `require formal from "../../lean"`, because formal/lean's lakefile requires
Mathlib from git, and lake would resolve it. Lake also builds a path dependency into that
dependency's own `.lake/build`, which other shards are compiling into. The four core-only
modules (`Formal/Net/Prelim`, `Formal/Timing/{Semantics,Checker,WinArray}`) are copied
verbatim by `sync.sh`. `sync.sh --check` (the first step of `run.sh`) fails on any byte of
drift; the current sha256 prefixes are d2864a28903a, 730ae7ba613e, 98b29a00de4e and
3488e0883589.

## What it buys
- **Rules H and I now have a checker whose arithmetic is a theorem.** It reproduces their
  verdicts and, with `sdf` data, their numbers. On prjxray data with the project's own band,
  it finds two thin hold margins that tighten's flat guard does not see.
- **Next:**
  1. Add the prjxray CARRY4/MUXF/FF arcs, which removes most fallback.
  2. Rules E and A.
  3. Emit 8e's per-stage races directly, so the end-to-end theorem's `checkPipe` is
     evaluated on the real route.
