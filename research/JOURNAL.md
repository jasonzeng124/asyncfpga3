# Research journal

Newest entry last. Format and rules: `research/PROGRAM.md`.

## 2026-10-25 -- branch created
Branched from `devin/1789854262-reconvergent-fusion` (PR #1, 14 commits ahead of
main, unmerged). Toolchain: none yet in the cloud; `cloud/setup-toolchain.sh` has
never run there. First job: get it working and get `cells/verify/toolchain.sh`
passing on all fingerprints, including Devin's three new patches.

Note: the owner's local toolchain carries only main's 4 patches plus a
pybindings change (now `patches/nextpnr-xilinx-pybindings.patch`), not
ff-timing / lut-perm-sink / place-weight. A board build on that machine needs
a rebuild first.

## Session 2026-10-25 18:16 -- cloud toolchain builds, passes every fingerprint and is cached; the inherited branch is red on two gates
Toolchain: patches sha 789a7120c912d393, nextpnr-xilinx sha256 9c732bc6303458df (bfdeaf7c + all 8 patches), chipdb sha256 64c9d2a43de684ef   Seeds: flow.sh default + NEXTPNR_SEED 1,2,3,4
Did:
- Made `cloud/setup-toolchain.sh` work from cold on the cloud image (4 fixes, one commit each):
  apt env assignment under an empty `$SUDO`; prjxray pip ran outside the checkout
  (`-e third_party/fasm`) and as the wrong interpreter (`pip3` is /usr/bin's, `python3` is
  /usr/local 3.11), now its own import-guarded block; Cython; fasm's antlr C++ parser does not
  compile here (antlr4 tool 4.9.2 vs runtime 4.10), so it falls back to fasm's textX parser;
  nextpnr's CMake picked Python 3.13 headers while Boost.Python is built for 3.12, now pinned
  via sysconfig. `cells/verify/toolchain.sh` was not touched: 9/9 fingerprints ok.
- The owner's new cache step published `toolchain-cache/d7ce266cff0c8e1e` (branch fallback; gh
  has no valid token here). The next session should restore it instead of rebuilding.
- `cells/check.sh` on claude/research (= Devin's PR #1 tip plus research files): SOME GATES FAILED.
  Both failures are inherited, not caused by this session, and bisected:
  1. **flow.sh: placement fails** (`Unable to find legal placement` for a LUT in
     `bdspine_upipe_many_stage_3__u_rdly_chain` group, RLOC_COL -1), also with BD_NO_TIGHTEN=1,
     4/4 seeds, same cell. **origin/main passes flow.sh with this same binary**, as do ff80891,
     f4a51c8, 9e609ca~1 and 9e609ca. 431917a, c197434, 1295656 and HEAD fail. bcaf7fe can't be
     tested with this binary (its older rloc-group fingerprint is MISSING, as it should be).
     With `--placer sa` the design places but routing then fails: `No wire found for port O6 on
     source cell upipe.many.stage[3].u.rdly.chain.g[4].u`, a delay-chain side-tap LUT in the
     same group. So the multi-column/slot-ordered RLOC packing in the committed
     `nextpnr-xilinx-rloc-group.patch` puts a chain LUT on a BEL it cannot drive out of. Either
     the committed patch is not the one the README's routed numbers were made with, or the
     cloud chipdb differs. tighten.py, teeth.sh and rule E then fail downstream (no SDF).
  2. **run_sim.sh arc-only (BD_ROUTE_PS=0): tb_link and tb_ctl FAIL** (tb_link: every token
     reads XX). Both pass at BD_ROUTE_PS=354. main and 9e609ca~1 pass both regimes under this
     iverilog 12.0, so the simulator is not the cause; 9e609ca is the first bad commit.
     Mechanism, from an event trace: stage 0's node is high for only 124 ps (8016 to 8140 ps),
     because stage 1's node rises one SDELAY element plus one controller arc (112 ps) later and
     the testbench source returns to zero at once. The latch's x->0 fall arc (124-152 ps) loses
     that race and stage 0 captures X. This is the fill race 9e609ca's own message describes;
     one SDELAY element does not cover it with zero routing. Control: probe copies of the
     benches with `.SDELAY(2)` (and 3) pass in both regimes; `.SDELAY(1)` fails. rtl/ is frozen
     and the default only sets the placeholder (rule I sizes SDELAY on a route), so the default
     was NOT changed: that needs a routed GLS run, which didn't fit in this session.
- Unit tests: `pytest bdc/ cells/verify/` passes 94 and skips 4 (fixtures not yet copied at
  the time). An earlier run with 16 failures was iverilog still being installed by apt.
Measured:
| what | result | n | vs previous |
|---|---|---|---|
| toolchain.sh fingerprints | 9/9 ok | 1 build | first cloud build |
| flow.sh, origin/main, BD_NO_TIGHTEN=1 | PASS | 1 (default seed) | -- |
| flow.sh, HEAD, BD_NO_TIGHTEN=1 | placement FAIL | 5 (default, seeds 1-4) | README rows claim routed results |
| tb_link / tb_ctl, BD_ROUTE_PS=0, SDELAY=1 | FAIL | deterministic | main: PASS |
| tb_link / tb_ctl, BD_ROUTE_PS=0 and 354, SDELAY=2 | PASS | deterministic | -- |
Does NOT show: that SDELAY=2 is the right default on a route, or that it is enough under
routing scatter (sim only); that the RLOC failure is a patch bug and not a chipdb difference
(the owner's local binary was never compared); that fasm2frames with the textX parser makes a
correct bitstream (not run; nothing reached a bitstream this session). No speed numbers.
Next:
1. Restore the cached toolchain (`cloud/setup-toolchain.sh` should fetch d7ce266cff0c8e1e).
2. Fix the RLOC placement failure: dump the BEL the g[4]/g[6] chain LUTs land on in the SA
   run (`--placer sa`, then the routed JSON), check against the patch's slot-to-BEL mapping
   for side-tap LUT2s sharing a site with LUT1s (O5/O6 fracture). Compare against the owner's
   local binary if a sha is recorded in build/toolchain.log on their machine.
3. Then SDELAY: change the bd_pipe default 1 -> 2 only with a routed GLS of xorshift_round
   across 4 seeds showing it (rules in CLAUDE.md for cells/rtl/).

## Session 2026-10-25 19:21 -- flow.sh green again: MUXF7/F8 LUTs no longer RLOC-stamped; in-site mux wires pass the zero-arc gate
Toolchain: patches 789a7120c912d393, nextpnr sha256 9c732bc6303458df, yosys v0.62 (cloud cache d7ce266cff0c8e1e)   Seeds: 1 2 3 4
### progress 19:30
- Root cause of the inherited placement failure: this yosys maps soak_top's two 8-input
  functions to 4 LUT6 + 2 MUXF7 + 1 MUXF8 each. rloc_stamp v8 (stamp_datapath) gave those LUTs
  side slots in columns 0 and 1 of one group (seen in soak.json: four `lk1...lut0/lut1` LUT6s at
  (col,slot) (0,10) (0,11) (0,12) (1,12)); an F8 tree lives in one SLICE, so no anchor is legal.
  Not a patch bug and not a chipdb bug. Fix: stamp_datapath skips any LUT driving a MUXF7/F8
  I0/I1 (8 LUTs here); unit test added, fails on the old code.
- v4/v5 (which did place) then failed the zero-INTERCONNECT gate on exactly 12 arcs, all
  LUT->F7 / F7->F8 site wires. New verify/zero_arcs.py exempts only a SELMUX2_1 data pin fed from
  the same routed SLICE; three negative controls FAIL it.
- BD_NO_TIGHTEN=1 flow.sh (v8 default): PASS on seeds 1-4, four distinct bitstreams, 0 groups
  dropped (was: placement FAIL 5/5).
### progress 19:45
- Arc-only tb_link/tb_ctl: every real bd_pipe instance (emit.py, soak_top.v) sets SDELAY, and
  rule I audits every pipe controller on a route, so the rtl default only reaches unsized uses.
  The two zero-routing benches now size their own boundary (`BD_TB_SDELAY`, 2) with the measured
  reason in a comment; rtl/ untouched. Both PASS in both regimes; control at SDELAY=1 still FAILs.
- `cells/check.sh`: **ALL GATES PASS** (first time on this branch in the cloud). pytest 99 passed.
### progress 19:45 (routed xorshift_round)
`bdc/fusion_bench.py --route --kernels xorshift_round --caps 4 --no-baseline --seeds 3 --route-seeds 4`
(fusion on, cap 4; resize route plus fresh seeds 4/5/6, four distinct bitstreams). Every route:
tighten pass, skew pass, both GLS pass, gate.log has ANNOTATE_DONE and no SDF warning or error.

| xorshift_round fusion on cap 4 | mean | range | n | vs README row |
|---|---|---|---|---|
| routed latency | 7.73 ns | 7.61-7.90 | 4 | 7.6-7.9 |
| fast-source interval | 5.68 ns | 5.60-5.81 | 4 | 5.35-5.83 |
| stalled-consumer interval | 13.84 ns | 13.72-14.02 | 4 | 13.4-13.7 |
| LUT sites incl. harness | 217 | 217 | 4 | 218 |

So the cloud toolchain reproduces the owner's routed numbers within route scatter. That is the
toolchain agreeing with itself, not with silicon.
- Draft PR #2 claude/research -> main opened.
- Started: `hw/build_bench.sh gcd` (tighten loop), aiming for a cloud-built kernel bitstream
  -> routed GLS -> BOARD-QUEUE.
