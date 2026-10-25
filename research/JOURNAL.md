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
