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
### progress 19:55
- `hw/build_hw.sh gcd_hw` (the routed-GLS target) was broken on this branch: its
  `--probe n138,n136_u,n135__2` names channels that op fusion (the emitter default) folds into
  select1's fused cell, and emit.py refuses them. Now only n138 is probed by default; the cmp
  probes and gcd_rig.v's `GCD_RIG_CMP_PROBE` come back with BDC_OP_FUSION=0 (emission checked
  both ways). With fusion on, cmp_seen is 0 by construction, which voids cmp_bad.
- Running: gcd_bench_gen tighten loop (main tree), gcd_hw converge (scratch worktree).
### progress 20:10 (gcd_hw placement)
- Same bug class as soak_top, larger: gcd_hw's data path has 21 CARRY4 and 35 MUXF7. Stamped
  LUTs drove CARRY4 S/DI, so nextpnr dropped 5 bank groups ("member already has an absolute-z
  constraint") and placement failed. rloc_stamp now leaves every LUT on a CARRY4 S/DI or a
  MUXF7/F8 data input to its site (1112 LUTs in gcd_hw). Unit test fails on the old code;
  soak_top's seed-1 bitstream is byte-identical (cmp) to the MUXF-only fix.
- After that: 0 groups dropped, yet placement still fails (latch `lat.odd.u` of ulink_n64__2).
  Geometry: 48 of the 90 v8 spine groups use three columns, and the {-1,0,1} -> dx {-1,0,3}
  pattern holds at only 4 of 22 logic columns. 8-9-tile groups in 25-row runs give roughly 30-40
  legal homes for 48 groups. So v8 does not fit gcd_hw. Not a bug in any one cell; v8 was only
  ever measured on xorshift_round. Next: gcd_hw with BD_RLOC=v4.
### progress 20:20 (gcd_hw, v4)
- `BD_RLOC=v4 hw/build_hw.sh gcd_hw` places and routes (5 min). Rule E converge then gives up
  after iteration 2: 118 select gates, 6 violated, and the same three links (ulink_n31, n164,
  n165) measure short again after being padded (margins 76-400 ps, needing 3-4 more elements
  each). converge.sh's own verdict: the padding moves the route as fast as it fixes it. This is
  the "rule E blocks tightening" lead, reproduced in the cloud on gcd. No GLS (no converged
  build). Running: the same build with v6 and with v2.
### progress 20:30 (gcd_hw, rule E convergence)
- v6 and v2 placements behave like v4: same short links (v6: 17 then 14 violated, adds
  ulink_n90__0; v2: 6 then 6). In every case the failure is n31/n164/n165.
- Why it chases: rule E's guardband is proportional (0.772*req vs 1.155*sel). umux20 (v2):
  iteration 1 raw +1818 ps, guarded -621; after +2 elements on n165 the request moved +542 ps
  but the select moved +716 ps (5286 -> 6002), guarded -1029. Exact padding is inside route
  noise. Added `CONVERGE_HEADROOM=K` to converge.sh (pad K elements beyond the deficit;
  default 0 = unchanged) since too long only costs time. Running v4 with K=3 and K=6.
### progress 20:45 (rule E's knob was the wrong link)
- Headroom did not help: v4 with K=3 and K=6 (n165 at 8 and 11 elements) still has the same 6
  violations. Six extra elements (~2.5 ns nominal) moved umux20's request by +609 ps, i.e. the
  pad was not on the measured path at all.
- Cause, in skew.py's attribution: it pads the LAUNCH's link, assuming the launch is the C node
  of the link whose req/data pair is checked. On gcd_hw the launch is umux20's OUTPUT pipe
  (ulink_n165 stage[0], the shared acknowledge); its DELAY pads stage[1]'s req_out, which is on
  neither leg. The link that owns the checked request is the mux's select channel ulink_n166__1
  (ctl_req vs s). Same for umux19 (n164 -> n166__0) and umux2 (n31 -> n32__2).
- Fix: skew.py takes the knob from the measured request path (the storage crossing nearest the
  request pin, only if the path leaves it through its rdly chain or its req_out C node, in a
  pipe's last stage); otherwise the violation is reported, not padded.
- Gate hole found and closed: converge.sh declared CONVERGED whenever the pad file was empty,
  including when every violation was unattributed. It now also requires rule E's own
  "0 violated".
- check.sh: ALL GATES PASS with both changes (soak rule E 3/3, 0 violated). pytest verify/ 49 pass.
- Running: gcd_hw converge with the fixed knob, v4 and v6.
### progress 21:00 (gcd_hw converges)
- With the knob fix, `BD_RLOC=v4 hw/build_hw.sh gcd_hw` CONVERGES in 2 iterations: pads
  ulink_n166__0=12, ulink_n166__1=13, ulink_n32__2=11 (36 elements added), rule E 0/118 violated.
  v6 still does not converge (17 -> 9 violated, n166__0 and n90__0 short again): v6 placement is
  worse for gcd's selects.
- tighten.py on that route (`--osc dhk --osc invhk`, the harness's free-running housekeeping
  ring): rules A, H, I 0 violations; the 38 reported problems are all rule D, the documented
  screen (check.sh: "on gcd it calls 38 of 39 branches violations").
- cloud/setup-toolchain.sh: apt `time` added (gls/run.sh needs /usr/bin/time; the cache key is
  unchanged).
- Running: routed GLS of this route (16 vectors), and seeds 2/3/4 with the converged pads.
### progress 21:20 (gcd_hw routed GLS)
- Route 1 (converge's final route, build_hw default seed, pads n166__0=12/n166__1=13/n32__2=11,
  routed.json md5 13643a10, sdf md5 e9bbd1f2): `gls/build.sh gcd_hw`, `vvp gate.vvp` ->
  ANNOTATE_DONE, 0 SDF warnings/errors (11 min); `gls/run.sh gcd_hw` (TEND 150 us): **16/16
  vectors complete laps with errs=0**, including 5, 6, 7, 8, 11, 12, 13 (the board's historical
  seven). Laps per vector 19 to 2626. Expected values re-checked here against math.gcd: 16/16,
  none degenerate.
- Same pads on fresh seeds: seed 2 and 4 rule E 0 violated; seed 3 rule E 1 violated (umux2,
  -29 ps guarded on +2292 raw, wants +1 on n32__2). Rules A/H/I 0 on all four; D 38 (screen).
  So the converged pads are marginal on 1 route in 4. Taking the longer number: pads +1/+1/+2
  (13/14/13) are being re-checked on 4 seeds (default, 2, 3, 4), then GLS on each.
### progress 21:40
- Pads 13/14/13 (`cells/hw/gcd_hw_pads.json`, committed): seeds d/2/3/4, four distinct bitstreams,
  rule E 0/118 violated on all four, rules A/H/I 0, D 38 (screen). GLS of all four running.
  Reproduce one route: `cd cells && BDC_SELECT_PADS=hw/gcd_hw_pads.json BD_RLOC=v4 [NEXTPNR_SEED=N]
  ./hw/build_hw.sh gcd_hw`.
### progress 21:50 (gcd_hw top of the ladder -> BOARD-QUEUE #1)
GLS of all four 13/14/13 routes (seeds d, 2, 3, 4): each gate ANNOTATE_DONE with 0 SDF
warnings/errors; each 16/16 vectors with errs=0 and laps>0. Board queue entry #1 with the
default-seed bitstream committed (`research/board/gcd_hw_03e82630.bit`).

| gcd_hw (v4, pads 13/14/13) per 150 us GLS window | laps mean | range | n | ns/lap upper bound |
|---|---|---|---|---|
| vec 0 (a=0) | 2689.5 | 2650-2719 | 4 | 56 |
| vec 4 (1,1) | 328.8 | 325-333 | 4 | 456 |
| vec 6 (gcd.c's main pair, deepest k-loop) | 25.0 | 24-26 | 4 | 6000 |
| vec 12 (2^31-1, 2) | 19.2 | 19-20 | 4 | 7792 |
| vec 13 (1000000, 999999) | 28.2 | 28-29 | 4 | 5310 |
(ns/lap = 150 us / laps, so it includes the window's reset and settling; it is an upper bound
on latency, not a measurement of it. All 16 vectors are in r2/*.gls_run.log in the session.)
### progress 23:00 (benches; owner: no board for a long time)
- Owner's PROGRAM.md update (1acd25b): no board for the foreseeable future, so strengthen the
  off-board evidence: 8+ seeds with the worst one reported, routed GLS at corners and under delay
  scatter, negative controls for every check, the August silicon failures as regressions. One
  bitstream is already committed (BOARD-QUEUE #1); no more will be.
- `hw/build_bench.sh xorshift` (tighten loop, rule A outer, rule E inner, with the fixed rule E
  knob): CONVERGED after 4 iterations; rule A 0 on the final route; 39 measured sizes.
- `hw/build_bench.sh gcd`: NOT converged in 6 iterations (62 min). Rule A violations per
  iteration 5, 74, 23, 12, 18, 10, 8, a different set each time (compute units ucmpi*/uori4/
  uselect1/ushrsi3, merges, DACK lines). The script falls back to emit.py's estimate sizes and
  still writes a bitstream, and its iteration-0 route already had 5 rule A violations. So the
  gcd bench bitstream it produces does not pass rule A. This is the route-sensitivity problem
  CLAUDE.md describes (rule A tightening to exact sizes, 2 of 8 fail). Not fixed here; noted for
  a later lead (tightening with headroom, or sizing against several routes at once, as
  resize.sh does for xorshift_round).
- gls/gen.py: opt-in delay perturbation (GLS_DELAY_SCALE, GLS_SCATTER + _SEED, GLS_SCALE_INST
  for a targeted fault). With none set, the generated netlist, baked netlist, SDF and name map
  are byte-identical to before (cmp). Running: negative control, uselect1's 94-link matched
  delay scaled to 0 on the default-seed gcd_hw route.
### progress 23:30 (gcd_hw GLS negative controls)
On the default-seed route (pads 13/14/13), baked GLS via GLS_SCALE_INST:
| fault | arcs scaled | vectors correct | note |
|---|---|---|---|
| none | 0 | 16/16 | as above |
| uselect1.udly x0 (its 94-link, 45 ns chain) | 374 | 16/16 | not a failure of the check: rule A says the request trails the data by 38.6 ns with the chain; 94 links is grossly oversized for these vectors ("tighten to 14") |
| every compute unit's udly x0 (50 units) | 4270 | 1/16 | 15 vectors: one WRONG answer, then the ring wedges (laps=1, errs=1). Vector 0 (a=0) is the C's early return and touches no datapath |
So the routed GLS does catch a bundling fault, when the fault is real on the vectors' paths. The
single-unit control shows how much slack the emitted estimates carry (a speed lead: tighten the
compute chains, which `build_bench.sh gcd` could not do stably).
- Seeds 5 and 6 (pads 13/14/13): rule E 0, A/H/I 0. Running: seeds 7, 8; GLS corner
  (x0.9, x1.1) and scatter (sigma 8.5% x3 draws, 17% x2, 25% x2) sweeps.
### progress 23:25 (gcd_hw: 8 seeds, corners, scatter -- first failure is NOT seen by any audit)
- Seeds 5, 6, 7, 8 (pads 13/14/13): rule E 0, A/H/I 0, D 38 on each. **8/8 routes** (d, 2-8) clean
  on every audit, 8 distinct bitstreams. GLS on d, 2, 3, 4: 16/16 each (seeds 5-8 not yet GLS'd).
- GLS perturbation sweep on the default-seed route (baked run, 16 vectors, TEND 150 us):

| delays | vectors correct |
|---|---|
| x0.90 (fast corner) | 16/16 |
| x1.10 (slow corner) | 16/16 |
| scatter sigma 8.5% (median ring scatter), 3 draws | 16/16, 16/16, 16/16 |
| scatter sigma 17%, 2 draws | 16/16, 16/16 |
| scatter sigma 25%, 2 draws | **11/16** (draw 1), 16/16 (draw 2) |

- The sigma-25% draw-1 failure is liveness, not data: vectors 6, 9, 11, 14, 15 complete no gcd
  (laps=0, errs=0). No wrong answer anywhere.
- **No audit sees it.** The same perturbed delays written back into an SDF (scratch tool
  perturb_sdf.py, same regexes and draw order as gen.py) pass rule E (0/118), A, H, I (0 each);
  D 38 as always.
- Localised on vector 6 (tb_wedge + probe.vh): a true deadlock about 200 ns after the rig's
  reset releases (450 -> ~655 ns), no control node X. The loop-header muxes umux0/1/2 hold valid
  back-edge data (n_trueResult_22/24/26: req=1, ack=0; ulink_n_trueResult_22 really passed a
  token), but control_merge2 never delivers the next index (its inputs n_trueResult_18/28 idle),
  and source n33's fork waits on one output. So a CONTROL token is lost in the first loop
  iteration. Not yet found where; candidates are a timing relation none of A/D/E/H/I models,
  for example a multi-input change on a LUT C-element when per-arc delays diverge by tens of
  percent.
- Running: sigma 20% x3 draws, 25% x2 more, 25% on the seed-2 route x2.
### progress 00:00 (the first margin to fail under scatter: bd_arbiter's A0 fork)
- More scatter draws: sigma 20% x3 -> 11/16 (draw 1), 16/16, 16/16; sigma 25% draws 3, 4 ->
  16/16, 16/16. Draw 1 fails at both 20% and 25% (same random sequence, smaller amplitude).
  Total at >=20%: 2 failing of 7 draws on the default-seed route.
- Bisection with GLS_SCATTER_ONLY (each arc keeps its draw-1 factor): of 355 kernel units, the
  deadlock needs ucontrol_merge2 alone (the loop-header control merge, bdc_amerge2_0 = bd_arbiter
  between loop entry and back edge). Of its 21 cells it needs exactly two together:
  **uarb1.ua2.u** (A2 = C(g2, A0)) and **uarb1.ustate$LUT6** (q, held while A0 is high). Either
  alone passes.
- What the draw did to them: A0 (the fork ack, one net) reaches ustate's hold pin at 777 ps
  (x0.52) but ua2 at 2378 ps (x1.59), 1.6 ns of skew between two branches of the same net.
  So q unfreezes at A0-fall and starts the next grant long before ua2 has seen A0 fall. bd_arb.v
  says the handover ordering is "a post-route check, not a defect" and that alternation holds by
  "one arc of margin, not by construction". **No such post-route check exists**: rules A, D, E,
  H and I do not look inside the arbiter, and all pass on this perturbed SDF.
- Confirmed with no scatter (GLS_SCALE_INST on every arc into ua2): x1.6 -> 5 correct laps;
  x2.5 (A0 about 2.2 ns later at ua2) -> deadlock; x4 -> deadlock. The nominal margin on this
  route is therefore roughly 0.9-2.2 ns of extra A0->ua2 delay.
- Realism: the two A0 branches share one net and much of its route, so independent per-arc
  scatter overstates their divergence; nominally the margin is positive on 8/8 routes (all pass
  GLS where run). But it is an unaudited timing dependency in a cell every kernel with a loop
  emits, and its margin is not measured anywhere.
- **Next (goal 1, highest value):** add the missing post-route check, call it rule J. For every
  bd_arbiter, the A0 fall must reach ua1/ua2 (plus their C-element arc) before q's re-decision
  can raise R0 and bring A0 back up, with the guardband. Prove it can fail (ua2 x2.5 above is a
  ready negative control), then run it on all 8 gcd_hw routes and on xorshift/the benches.
### progress 00:30 (rule J: verify/arb_fork.py)
- Exact race from a time-ordered trace (ua2 arcs x2.5, no scatter): client 1 acked (608.8 ns);
  A0 falls (659.3); ustate sees it, q flips to client 2 (660.9), g2 rises (661.3); **ua2 =
  C(g2, A0) rises at 662.7 because A0's fall has not reached it yet**; client 2 drops r2, g2 and
  R0 fall, and the merge's gated delay flushes before z_req ever rises. The control token is gone.
  This is the very handover bug bd_arb.v's hold was added for; the hold only works if A0 reaches
  ua_k no later than q -> ugrant -> g_k does.
- New audit `cells/verify/arb_fork.py` (rule J): per arbiter and client, late = A0 -> ua_k +
  ua_k's A0 arc; early = A0 -> ustate + ustate arc + q -> ugrant + grant arc + g_k -> ua_k +
  ua_k's g arc; guarded = 0.772*early - 1.155*late > 0. Pins resolved from the routed JSON; rst
  is told from A0 by fanout. Exit 1 on violation, 2 on an unresolved arbiter.
- Validation against GLS (default-seed route, same delays in both):

| delays | rule J raw (worst) | rule J guarded | GLS vector 6 |
|---|---|---|---|
| sigma 25% draw 1 (merge2) | -1090 | -1921 | deadlock |
| ua2 x2.5 (merge2) | -607 | -1944 | deadlock |
| ua2 x1.6 (merge2) | +344 | -696 | 5 correct laps |
| nominal (merge2) | +864 | +48 | correct |

  Raw sign predicts the GLS outcome in all four cases. The guard flags x1.6 as well, as intended.
- **On the 8 nominal routes: guarded violations on 3 (d: -96, 5: -150, 6: -80; worst is always
  ucontrol_merge9 client 1); raw positive on all 8.** BOARD-QUEUE #1 is the d route, so it is
  downgraded: it does not pass every check.
- Next: a placement fix. Put each bd_arbiter's ustate, ugrant, ua1 and ua2 in one slice
  (rloc_stamp) so A0's branches into them are near-equal and the grant path decides. Then rule J
  and GLS again on 8 seeds. An rtl alternative (hold q on the acks rather than A0) does not work
  as such: the idle client's ack does not change when A0 falls, so it cannot be observed.
### progress 00:50 (rule J with shared route credit; arbiter grouping measured, rejected)
- `BD_RLOC_ARB=1` (one SLICE per arbiter), 8 seeds, pads 13/14/13: rules A/E/H/I 0 on all eight.
  Rule J WITHOUT a shared-route credit: still short on 3 of 8 (d -288, 7 -198, 8 -102). Packing
  the four LUTs into one slice does not shorten A0, which comes from far away (merge9's arbiter
  sits at X2, the die edge). Most of each branch is the same wire.
- The flaw was in rule J, not the route: it guarded each leg's full A0 interconnect (x0.772 vs
  x1.155) as if the branches were independent wires. arb_fork.py now walks each net's ROUTING
  tree to where the two sinks diverge (physical site pins, since the route is post-permutation)
  and leaves the shared prefix unguarded, like skew.py's divergence point. Its delay is an
  ESTIMATE (each sink's interconnect times its shared-pip fraction, the smaller of the two),
  because the routed JSON has no per-pip delays.
- Validation still holds: draw-1 scatter -> guarded -1698 (GLS deadlock); ua2 x2.5 -> -1516
  (deadlock); ua2 x1.6 -> -267 (GLS passes; flagged, conservative); nominal -> pass.

| rule J, 8 seeds each | violated | worst guarded | worst raw |
|---|---|---|---|
| v4, pads 13/14/13 (BOARD-QUEUE #1 config) | 0/8 | +272 (seed 6) | +718 |
| same + BD_RLOC_ARB=1 | 0/8 | +280 (seed 6) | +618 |

  Grouping buys nothing, so it stays opt-in and off. BOARD-QUEUE #1 is restored with that caveat.
- What the sigma-25% deadlock was: gen.py's scatter draws one factor per SINK interconnect,
  so two sinks sharing 0.6-1.1 ns of one physical wire get independent factors. The deadlock
  needed A0's two branches to diverge by ~1.6 ns. A per-wire scatter model would be more
  physical, and is the next improvement to the GLS perturbation (it needs per-pip delays,
  which the SDF does not have).
### summary so far (01:00)
Measured (toolchain patches 789a7120c912d393, nextpnr 9c732bc6303458df, yosys v0.62):

| what | result | n | vs previous |
|---|---|---|---|
| cells/check.sh | ALL GATES PASS | 3 runs | was red (flow.sh placement, arc-only sims) |
| flow.sh (soak, v8), BD_NO_TIGHTEN | PASS | seeds 1-4 | was placement FAIL 5/5 |
| xorshift_round fusion cap 4, routed | 4/4 routes pass audits + both GLS; latency 7.73 ns (7.61-7.90), fast interval 5.68 ns (5.60-5.81) | 4 | README 7.6-7.9 / 5.35-5.83 |
| gcd_hw (v4, pads 13/14/13): rule E | 0/118 violated on every route | 8 seeds | never converged before (v2/v4/v6) |
| gcd_hw: tighten A/H/I | 0 violations every route (D 38 = screen) | 8 | -- |
| gcd_hw: rule J (new) | 0/8 violated, worst guarded +272 ps, raw >= +718 | 8 | new check |
| gcd_hw: routed GLS | 16/16 vectors, errs=0, every route; gate clean | 8 | first cloud kernel GLS |
| gcd_hw GLS x0.9 / x1.1 | 16/16 / 16/16 | 1 route | -- |
| gcd_hw GLS scatter 8.5% / 17% / 20% / 25% | 3/3, 2/2, 2/3, 3/4 draws all-correct | 1 route (+2 draws on seed 2) | first-failing: bd_arbiter A0 fork |
| GLS negative control (all compute delays x0) | 1/16 (the a=0 early return) | 1 | proves GLS can fail |
| build_bench.sh xorshift | converged | 1 | -- |
| build_bench.sh gcd | rule A not converged in 6 iterations | 1 | open |

Does NOT show: anything on silicon (no board for the foreseeable future); that rule J's shared-route
credit is exact (it is a pip-fraction estimate); that the per-sink scatter model is physical (it
is not: shared wires get independent factors, which is what made the 25% deadlock possible); that
the other kernels' benches pass rule A/E/J or GLS (only gcd_hw has a GLS rig); xorshift bench GLS.
Next:
1. A per-WIRE scatter model in gls/gen.py (one factor per route segment, shared by every sink
   that uses it); that needs per-pip delays, so start from nextpnr's chipdb or a pip-count model,
   and check that it reproduces nominal exactly at sigma 0.
2. Rule J into the standard audit path (build_hw/converge, check.sh once a design with an
   arbiter is in the gate); run it on xorshift's and the other benches' routes.
3. gcd bench rule A non-convergence (tightening with headroom, or sizing against several routes).
4. Speed: uselect1's 94-link (45 ns) chain is 6.7 ns longer than its whole request path needs on
   these vectors (rule A: "tighten to 14"); gcd_hw's compute chains are emit.py estimates.
### progress 01:30 (rule J in the standard paths)
- Rule J on the bench routes still on disk: xorshift_bench_gen (2 arbiters) pass, gcd_bench_gen
  (9 arbiters, the non-converged fallback build) pass.
- converge.sh: a run whose rule E converged is now NOT SHIPPABLE (exit 1) if rule J fails or
  cannot resolve an arbiter on the same route. tighten_loop.sh: same check on the final bitstream's
  route, exit 1. A design with no arbiter passes trivially (soak_top). Re-ran `BD_RLOC=v4
  hw/build_hw.sh gcd_hw` from scratch: rule J line printed, CONVERGED after 2 iterations at the
  same pads as the first run (12/13/11), so converge is reproducible on the default seed.
### progress 02:00 (wire-model scatter)
GLS on the default-seed gcd_hw route, GLS_SCATTER_MODE=wire (one factor per pip, shared by every
sink using it; arc = mean over its path; cell IOPATHs still one draw each):

| per-pip sigma | draws | vectors correct |
|---|---|---|
| 17% | 1 | 16/16 |
| 25% | 4 | 16/16 x4 (per-arc mode: 3/4 draws) |
| 35% | 3 | 16/16 x3 |

Caveat: averaging over ~9 pips makes an arc's effective spread about sigma/3, so these sigmas
are not comparable to per-arc mode's. What the two modes do show together: the only failure
mechanism found needs two branches of one net to diverge by ~1.6 ns. Per-arc mode makes that
possible; a model where shared wire scatters together does not reach it even at 35% per pip.
Rule J watches that margin directly on every route.
### progress 02:30 (gcd bench: rule A sizing converges with 600 ps of search slack)
`BD_TIGHTEN_SLACK=<ps> hw/build_bench.sh gcd` (tighten.py --slack on the sizing proposals only;
the rule A gate on each route runs without it):

| slack | rule A violations per iteration | outcome |
|---|---|---|
| 0 (earlier) | 5, 74, 23, 12, 18, 10, 8 | no sized build passed; falls back to estimates |
| 300 ps | 5, 53, 15, 6, 4, 3, 5 | no sized build passed |
| 600 ps | 2, 25, 13, 2, 1, 0, 2; restored best: 0 | **sized build passes rule A on its route** |

The 600 ps build carries 208.6 ns of matched delay against the unsized estimate's 572.9 ns
(2.75x less). On its final route: rule E 0/118 violated, rule J pass, 213 measured sizes. ONE
route; fresh seeds 2/3/4 with the sizes fixed are running. No speed number: the bench reads its
cycles through the PS, which has no GLS model, and there is no board.
### progress 02:45 (gcd bench sized at 600 ps slack: does NOT survive fresh seeds)
Rebuilt with the 213 sizes fixed (`BD_SIZES=... NEXTPNR_SEED=s hw/build_bench.sh gcd`):

| seed | build_bench rule A gate | audits on the route it reached |
|---|---|---|
| 2 | SIZES REJECTED (3 cells), no bitstream | A 2, H 1, I 0, E 0, J pass |
| 3 | SIZES REJECTED (1 cell), no bitstream | A 0 / I 1, E 0, J pass |
| 4 | SIZES REJECTED (2 cells), no bitstream | A 2, E 1, J pass |

So the 600 ps result is a property of the route it was sized on (0 of 3 fresh routes accept
it), the failure CLAUDE.md describes for xorshift ("rebuilds violate rule A 2 times in 8").
Negative result, not shippable. To make a sized gcd bench robust, size against several routes
at once (resize.sh's --seeds approach for xorshift_round) rather than one route plus slack.

## Session 2026-10-26 04:13 -- (in progress)
Toolchain: patches 789a7120c912d393, nextpnr 9c732bc6303458df, yosys v0.62   Seeds: TBD
- Took the lock at 04:13 (previous holder's lock dated 02:43, past 90 min). Toolchain restored
  from cache, toolchain.sh all ok. Machine: 4 cores, 15 GB.
- Plan: (1) per-cell matched-delay sizes for gcd_hw (the GLS-able rig), sized against several
  routes, then GLS laps vs the emit.py-estimate baseline: the only speed lead the routed GLS can
  check end to end; (2) in parallel, routed GLS of gcd_hw seeds 5-8 (8/8 GLS for BOARD-QUEUE #1)
  and slow/fast corners on more than one route.
### progress 04:30 (gcd_hw sizing hook works; seeds 5/6 audits reproduced)
- `BD_SIZES` for gcd_hw (16ee9c8): checked in synth.log that the sized build elaborates bdc_gcd with
  the file's values (DELAY_USELECT1 = 15 against the default 94); unset, gcd_rig.v is unchanged.
- `BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 BD_TIGHTEN_SEEDS="2 3" BD_TIGHTEN_SLACK=300
  hw/tighten_loop.sh gcd_hw 8` (running): unsized route 547.7 ns of matched delay built, 166.9 ns
  needed, rule A 0. Pass 1 (207 sizes): 103.6 ns built, rule A 54 violations, rejected and
  ratcheting, as the loop expects on its first pass.
- Seeds 5 and 6 (pads 13/14/13) rebuilt: rule E 0/118, A/H/I 0, rule J pass, as in the last
  session. GLS (nominal, x0.9, x1.1) running; then seeds 7, 8.
### progress 05:00 (gcd_hw seeds 5/6 GLS; sizing loop reaches rule A 0 on its route)
- Seeds 5, 6 (pads 13/14/13): GLS gate ANNOTATE_DONE, 0 SDF warnings/errors; **16/16 vectors,
  errs=0, laps>0 on both** (vec 6: 24/24 laps, vec 12: 19/18, vec 13: 28/27 per 150 us, in line with
  d/2/3/4). So 6 of 8 seeds now have nominal GLS. x0.9/x1.1 on them and seeds 7/8 running.
- gcd_hw sizing: rule A violations per pass 54, 7, 5, 0. Pass 4 on the default seed: **163.8 ns
  built (unsized 547.7 ns, 3.3x less), rule A 0**. It is now being rebuilt under seeds 2 and 3
  (BD_TIGHTEN_SEEDS) before it counts as a candidate.
### progress 05:45 (collatz: first routed GLS of a loop kernel besides gcd; subagent, reviewed and committed here)
- `bdc/fusion_bench.py --mlir <frontend mlir> --route --nextpnr-seeds ...` (new): zero-delay RTL check,
  then per pinned seed flow.sh, tighten.py (A/H/I/B/C/D), skew.py (E), arb_fork.py (J), and routed
  GLS (fast source and stalled consumer), one invocation at a time, oracle = simcheck.REFS (the
  kernels' C, transcribed) on simcheck.VECTORS + 8 seeded random vectors, `$fatal` on mismatch,
  bd_monitor on the protocol. Audits are recorded, not enforced, so a violating route still runs.
- zero_arcs.py (flow.sh gate) blocked every collatz route: 64 CARRY4 S<k> arcs at 0 ps. All were
  LUT O6 -> CARRY4 S<k> in the same SLICE with the LUT letter matching k, the hard-wired propagate
  input (delay carried by the CARRY4 S->O/CO IOPATH, 210-472 ps). That case is now accepted with
  the same same-site test as the F7/F8 exception; DI/CIN/CYINIT stay checked. Negative control:
  swapping S0/S1 sink names in a copy of the SDF makes it fail (32 arcs). pytest verify/ 52 pass.

| collatz, 4 seeds (1-4) | rule E violated | rule J | A/H/I | GLS fast / stalled |
|---|---|---|---|---|
| emit placeholders | 4, 3, 4, 5 of 18 (umux0/1/2) | 4/4 ok | 0 | pass, pass, **FAIL, FAIL** |
| + rule E pads (research/data/collatz_rulee_sizes.vh) | 0 on all 4 | 4/4 ok | 0 | pass on all 4 |

- The seed-3 GLS failure is the rule E violation itself: umux0's join sees vector 1's request at
  5100.798 ns while its select (ulink_n14__0) settles at 5101.033 ns, the -235 ps raw deficit skew.py
  reports on that route. So routed GLS and rule E agree, and rule E is load-bearing on collatz.
- Latency (padded, 4 seeds): **158.2 ns per loop iteration (156.3-160.2)**, slope of latency against
  Collatz steps over 16 vectors; n=1 40.9 ns (39.8-41.3); n=27 (111 steps) 17.57 us (17.37-17.79).
  Zero-delay RTL: 18.4 ns per iteration.
- Negative control: one expected value changed (n=27: 111 -> 112) fails both RTL and routed GLS.
- Does NOT show: tightened delays (placeholders + 3 pads; the 158 ns is not a speed result); the pads
  were derived from and re-checked on the same seeds 1-4 (fresh seeds still owed); corners or
  scatter; rule D (tighten.py exits 1 on the 6 ucond_br screens, which rule E passes); check.sh
  not re-run after the zero_arcs change; isprime/ipow (the mode has their vectors, not run).
### progress 06:15 (gcd_hw seeds 5/6 at both corners)
- Seeds 5 and 6 (pads 13/14/13), routed GLS with every delay x0.9 and x1.1: **16/16 vectors,
  errs=0, laps>0 at both corners on both routes** (laps scale about 1/factor, e.g. seed 6 vec 6:
  26 / 24 / 22). Corners were on 1 route before; now 3. Seeds 7/8 running.
- gcd_hw sizing, rule A per pass: 54, 7, 5, 0 (rejected by fresh seeds 2 and 3), 2, 1, ...: one new
  binding cell per route, chain 170.8 ns at pass 6.
### progress 06:50 (gcd_hw: 8/8 seeds pass nominal routed GLS; sizing run 1 did not converge)
- Seeds 7, 8 (pads 13/14/13): rule E 0/118, A/H/I 0, rule J pass, gate clean, **16/16 vectors errs=0**.
  BOARD-QUEUE #1's configuration now has nominal routed GLS on all 8 seeds (d, 2-8), and x0.9/x1.1 on
  d, 5, 6 (7/8 corners running).
- Sizing run 1 (`tighten_loop.sh gcd_hw 8`, seeds d + fresh 2 3, slack 300): rule A per pass 54, 7, 5,
  0*, 2, 1, 0*, 0* (* = passed its own route, then rejected by a fresh seed: 2 rejected pass 4 with 7
  cells, seed 3 pass 7 with 2, seed 2 pass 8 with 1). Chain 163.8 -> 171.5 ns. No candidate accepted
  in 8 passes, so it shipped nothing (fallback to emit's estimate, as designed). Resumed from the
  ratchet (BD_RESUME=1, 10 more passes); the requirement is still rising by 1-3 cells per new route.
### progress 07:05 (gcd_hw corners on 5 routes)
- Seeds 7, 8: routed GLS x0.9 and x1.1, 16/16 errs=0 on both. **Corners now pass on 5 of 8 routes
  (d, 5, 6, 7, 8); nominal on 8/8.** Running: per-arc scatter (8.5% x2 draws, 17% x2) on the seed-8
  route; the run-1 pass-8 sizes (171.5 ns, rule A 0 on the default seed only) built and GLS'd on the
  default seed, to see whether 3.2x less matched delay buys laps at all (exploratory: those sizes
  failed a fresh seed and are not a candidate).
### progress 07:45 (gcd_hw sizing is worth ~2.2x in routed GLS; seed-8 scatter clean)
Exploratory, ONE route, NOT a candidate: run 1's pass-8 sizes (`sizes.8.vh`, 207 sizes, 171.5 ns of
matched delay against 547.7 unsized) rebuilt on build_hw's default seed (pads 13/14/13, v4):
rule E 0/118, A/H/I 0, rule J pass, GLS gate clean, **16/16 vectors errs=0**. These sizes were
rejected by fresh seed 2 (rule A, 1 cell), so they are not shippable.

| laps per 150 us GLS window | unsized (seed 5) | sized pass 8 (seed d) | ratio |
|---|---|---|---|
| vec 0 (a=0, no loop) | 2509 | 4432 | 1.77 |
| vec 4 (1,1) | 323 | 733 | 2.27 |
| vec 6 (gcd.c's pair) | 24 | 53 | 2.2 |
| vec 12 (2^31-1, 2) | 19 | 44 | 2.3 |
| vec 13 (1000000, 999999) | 28 | 63 | 2.25 |
(unsized seeds d/2-8 agree within a lap or two on vecs 6/12/13: 24-26, 18-20, 27-29.)

So the matched delay is on the critical cycle, and sizing it to the route buys about 2.2x laps in the
routed GLS, the same size of effect as the board's 1.99x for rule-A-only sizing of xorshift in August.
What stops it shipping is the route-sensitivity long tail: each fresh route finds 1-2 more cells short.
- Seed-8 route, per-arc scatter: 8.5% draws 1, 2 and 17% draw 1: 16/16 each (17% draw 2 running).
### progress 08:20 (scatter on a second route; sized route at corners; ratchet + 1 link)
- Seed-8 route (unsized, pads 13/14/13), per-arc scatter 8.5% x2 and 17% x2 draws: 16/16 on all four.
- The exploratory sized route (pass-8 sizes, default seed): x0.9 and x1.1 also 16/16.
- New candidate "r1" = the resumed loop's ratchet (207 sizes) + 1 link on every cell (taking the longer
  number instead of chasing one binding cell per route): rules E/A/H/I/J clean on seeds d and 2 so far;
  seeds 3-8 running (two worktrees). The resumed loop itself is still finding 1-2 short cells per fresh route.
### progress 08:55 (gcd_hw multi-seed sizing converges)
- Resumed loop (`BD_RESUME=1 ... tighten_loop.sh gcd_hw 10`): pass 7 passed rule A on its own route
  AND on fresh seeds 2 and 3, ACCEPTED, then CONVERGED (proposal stopped moving). **182.1 ns of matched
  delay (unsized 547.7), 207 sizes, rule J pass on the final route.** Committed as
  research/data/gcd_hw_sizes_L7.vh. Total passes across both runs: 8 + 7 builds plus 2 fresh-seed
  builds each.
- Candidate r1 (an earlier ratchet + 1 link everywhere, research/data/gcd_hw_sizes_r1.vh; 198 links more
  than L7 in total but 1 cell shorter): rules E/A/H/I/J clean on **7 seeds (d, 2, 3, 4, 5, 7, 8)**;
  seed 6 running. GLS of r1 on d and 2 running. L7 on fresh seeds 4-8 running.
### progress 09:20 (collatz pads on fresh seeds and corners; isprime routed GLS; subagent, reviewed)
- `cells/check.sh`: ALL GATES PASS with the zero_arcs CARRY4-S change (flow.sh: "12 in-site F7/F8 mux /
  CARRY4 S input wire(s) are 0 ps by construction").
- collatz with research/data/collatz_rulee_sizes.vh on FRESH seeds 5-8: A/H/I 0, rule E 0/18, rule J ok,
  GLS fast and stalled pass on all 4; 160.4 ns per iteration (157.0-164.2). **All 8 seeds: 159.3 ns
  (156.3-164.2).** Seed 1 at x0.9 and x1.1: both GLS pass (n=27 latency 15.66 / 19.08 us, so the scale
  took effect). Uniform scaling cannot flip a race's sign; scatter on collatz not run.
- isprime: default BD_DSP=1 has no routed GLS (cells/gls has no DSP48E1 model: gen.py KeyError); its
  audits on 4 seeds: A/H/I 0, rule E 16-18/86 violated, rule J 0/14. With BD_DSP=0 (LUT multiplier):
  fusion_bench's routed_signals() now finds a result bit no net name carries (out0_data[31], folded into
  $PACKER_GND_NET since the answer is 0 or 1) through the leaf pin it reaches.

| isprime BD_DSP=0 | rule E violated /86 | A/H/I | GLS fast/stalled |
|---|---|---|---|
| placeholders, seeds 1-4 | 16, 23, 21, 16 (worst raw -960..-1690 ps) | 0 | pass, **deadlock (n=4)**, **deadlock (n=4)**, **out-of-phase out0_req** |
| + pads (research/data/isprime_rulee_sizes.vh), seeds 1-8 (5-8 fresh) | 5, 3, 2, 2, 3, 2, 3, 0 | 0, except seed 1 rule I 1 | pass on all 8 |

  Remaining rule E violations all have POSITIVE raw margins and fail only after the guardband:
  ucond_br16 on 7/8 (raw +4.5..+7.9 ns, guarded -1.1..-4.1 ns; request crosses 4 storage stages, ~25 ns,
  so the proportional guard grows with it; skew.py: no link DELAY is on the request path, nothing to
  pad), and umux2/4/7 (raw +0.9..+2.0 ns, guarded -16..-539 ps, paddable: a second round).
  Latency over 8 seeds (fast): n=91 5.74 us (5.62-5.92), n=97 7.76 us (7.60-8.00), n=997 38.55 us
  (37.66-39.83).
- Does NOT show: isprime's shipped (DSP) build in GLS; isprime passing the audits (it does not: rule E
  guarded on 7/8, rule I on 1); scatter on either kernel.
### progress 09:45 (L7 fails a fresh seed; r1 clean on 8/8; candidate R2)
- L7 (the loop's converged sizes, validated on d/2/3) on fresh seed 4: **rule A 1 violation** (ucmpi3
  14 links, margin -96 ps, wants 15). A three-seed acceptance is not enough on gcd_hw; the long tail
  continues on fresh routes. L7 is not a candidate; its remaining seeds were stopped.
- r1 (ratchet + 1 link everywhere): rules E/A/H/I/J clean on **all 8 seeds (d, 2-8)**. r1 has ucmpi3 at
  15 already, but uori4 at 18 where an L7 route asked for 19. Taking the longer number:
  **R2 = max(L7, r1) per cell** (research/data/gcd_hw_sizes_R2.vh) is the shipping candidate; its 8-seed
  audit is running. GLS of r1 on d/2/3/4 is running (r1 and R2 differ by one link on one cell, but a
  netlist change is a new route, so R2 gets its own GLS).
### progress 10:20 (r1 in routed GLS: 16/16 at ~2.1x; R2 audits 5/8 clean so far)
- r1 sizes, routed GLS nominal, seeds d and 3: gate clean, **16/16 vectors errs=0** on both.
  laps per 150 us: vec 0 4603/4872, vec 4 653/684, vec 6 51/52, vec 12 41/41, vec 13 59/61
  (unsized, 8 seeds: vec 6 24-26, vec 12 18-20, vec 13 27-29), i.e. **~2.1x**.
- R2 (= max(L7, r1)): rules E/A/H/I/J clean on seeds d, 2, 3, 4, 5 so far. Queued: R2 routed GLS
  (nominal, x0.9, x1.1) on seeds d, 2, 3, 4, 5, 6.
### progress 10:50 (R2 sizes: every audit clean on 8/8 seeds)
`BD_SIZES=research/data/gcd_hw_sizes_R2.vh BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4
[NEXTPNR_SEED=s] hw/build_hw.sh gcd_hw`, seeds d and 2-8:

| seed | rule E /118 | A | H | I | J | matched delay built | worst rule-A guarded margin |
|---|---|---|---|---|---|---|---|
| d | 0 | 0 | 0 | 0 | pass | 200.2 ns | +918 ps |
| 2 | 0 | 0 | 0 | 0 | pass | 200.1 | +190 |
| 3 | 0 | 0 | 0 | 0 | pass | 200.9 | +769 |
| 4 | 0 | 0 | 0 | 0 | pass | 200.5 | +253 |
| 5 | 0 | 0 | 0 | 0 | pass | 198.6 | +916 |
| 6 | 0 | 0 | 0 | 0 | pass | 200.1 | +1051 |
| 7 | 0 | 0 | 0 | 0 | pass | 199.4 | +400 |
| 8 | 0 | 0 | 0 | 0 | pass | 199.4 | +241 |

Mean 199.9 ns of matched delay (unsized 547.7 ns on the same pads: 2.74x less); worst seed's worst
margin +190 ps after the guardband. r1 (one link less on uori4) also passed x0.9 on d and 3. R2 routed
GLS (nominal + corners) running on d, 2, 3 first, then 4, 5, 6.
### progress 11:40 (R2 in routed GLS: 16/16 on 3 seeds at ~1.95x laps)
| laps per 150 us | unsized (8 seeds) | R2 seed d | R2 seed 2 | R2 seed 3 |
|---|---|---|---|---|
| vec 4 (1,1) | 323-333 | 623 | 664 | 650 |
| vec 6 | 24-26 | 47 | 48 | 48 |
| vec 12 | 18-20 | 38 | 38 | 39 |
| vec 13 | 27-29 | 55 | 57 | 55 |
All three: gate clean (ANNOTATE_DONE, 0 SDF warnings), **16/16 vectors errs=0**. R2 is a little slower
than r1/the exploratory pass-8 sizes (vec 6: 47-48 vs 51-53) because it carries the most headroom.
r1 also passed x0.9 and x1.1 on d and 3. R2 corners and seeds 4, 5, 6 running.
### progress 12:30 (DSP48E1 GLS model; ipow and isprime with DSPs; isprime pad round 2; ucond_br16; subagent, reviewed)
- **cells/gls DSP48E1 model** (prims.v `DSP48E1_DSP48E1`, gen.py `dsp_config()`): models exactly the
  configuration flow.sh's DSP cascade uses (no pipeline registers, INMODE/ALUMODE/CARRYIN* 0, OPMODE X=Y=M
  with Z in {000, 001, 101}, A direct or cascade, 25x18 signed multiply) and REFUSES anything else by name
  (checked by injecting PREG=1, a flipped OPMODE inversion and a dropped ALUMODE inversion: each exits 1).
  Timing: the SDF's per-bit IOPATHs, each set to its (input group, output group) maximum (on this chipdb
  each group has one value anyway: A->P 5400, B->P 3850, PCIN->P 1710 ps). Checks: unit test against the
  UG479 equations, 200 random operands x 6 configurations PASS, 1200 mismatches with `-DGLS_DSP_FAULT=5`;
  gate ANNOTATE_DONE with 0 warnings and claimed = emitted IOPATHs (isprime 80004, 38682 of them DSP);
  renaming one DSP arc's pin in the SDF yields an SDF WARNING (the arcs really are matched). Fault
  injection in routed GLS fails ipow ("got 13 expected 3") and isprime (n=9).
  **Non-DSP designs unchanged:** old and new gen.py on the seed-5 gcd_hw route give byte-identical
  netlist.v, netlist_baked.v, annot.sdf, names.map (cmp).
- ipow BD_DSP=1 (shipped config), placeholder lengths, seeds 1-4: A/H/I 0, rule J 0/4, **rule E 3-4/24
  violated on every seed (worst raw -279..-2295 ps; umux1/2/3)**, routed GLS fast+stalled pass on all 4;
  96.9 ns per loop iteration (95.7-98.2; iterations = bit length of e). 4 of its 8 random vectors expect 0
  (power wraps): weak vectors; 12 of 16 non-zero. GLS passing with raw rule E deficits up to -2.3 ns says
  this GLS does not exercise those races; rule E is the evidence there. fusion_bench: a channel with no
  bd_link latch reading it (ipow's b enters a loop-entry mux) now keeps bd_source's default 3000 ps setup,
  recorded as None (unmeasured).
- isprime BD_DSP=1 seed 1 GLS: all 18 values right (incl. 97, 113, 997, which need the DSP d*d), then a
  protocol $fatal (out0 X pulse) on a route with 16 rule E violations: the same signature as collatz's
  rule E failures.
- isprime BD_DSP=0 second pad round (research/data/isprime_rulee2_sizes.vh), seeds 1 (re-check) and fresh
  9-12: rule E 0, 3, 2, 3, 0 of 86; rule I 1 on seed 9; GLS pass on all 5. Remaining: ucond_br16 (raw
  +6.2..+8.6 ns), umux1 (paddable), ulink_n_index_71 SDELAY (rule I).
- **ucond_br16 is a rule E measurement artifact (analysis only, no rule changed).** skew.py measures the
  select from ulink_n18__1's latch outputs, and its request path from there runs through ucond_br16's OWN
  select pin and ack, round the loop (ufork6, ufork30, ulink_n76 C node and latch) to the NEXT token's
  request: a lap, not the bundled request. The right common launch is ulink_n18__1's C node (latch enable
  -> select, 1 crossing; ucmpi2 join -> its delay -> ucond_br16_j -> request, 2 crossings): raw +31.8 ns,
  guarded +16.7 ns there. skew.py never evaluates it: it ranks launches by select crossings and keeps
  cand[:4], and the 32-bit latch bank alone supplies 64 zero-crossing candidates (C node is #96 of 2061).
  The error direction is a FALSE violation (conservative). Fix candidate: always evaluate the C node of
  the select's feeding link; needs a negative control showing rule E can still fail there.
### progress 13:20 (R2 -> BOARD-QUEUE #2)
- R2 seed 5 routed GLS: gate clean, 16/16 (vec 6 53 laps, vec 12 43, vec 13 61). R2 seed d, 2, 3 at
  x0.9 and x1.1: 16/16 each. R2 now has nominal routed GLS on 4 seeds and corners on 3, every audit on 8:
  BOARD-QUEUE #2 written (rebuild command + md5s, no bitstream committed). Seeds 4/6 GLS and corners on 5
  still running.
### progress 14:30 (R2: routed GLS + corners on 6 seeds)
- R2 seeds 4, 5, 6: gate clean, nominal 16/16 (vec 6: 48 / 53 / 54 laps; vec 12: 39 / 43 / 44), x0.9
  16/16, x1.1 16/16. **R2 now passes nominal, x0.9 and x1.1 routed GLS on 6 seeds (d, 2-6)**, every audit
  on 8. Running: seeds 7, 8; per-arc scatter (8.5% x2, 17% x2, 25% x1) on the R2 default-seed route.
### progress 15:40 (R2: 7 seeds full GLS, scatter clean to 25%; collatz sizing started)
- R2 seed 7: gate clean, 16/16 at nominal (vec 6 50 laps), x0.9 and x1.1. **7 seeds (d, 2-7) pass nominal +
  both corners.** Seed 8 running.
- R2 per-arc scatter, default-seed route: 8.5% x2, 17% x2, 25% x1 all 16/16. Seed-2 route (the worst rule A
  margin, +190 ps): 8.5% x2, 17% x2 all 16/16; 25% running. (Unsized seed d failed 1 of 2 draws at >=20%
  via the bd_arbiter A0 fork, now watched by rule J.)
- Next speed lead started: collatz sizing. tighten.py on the 8 padded collatz routes says the placeholders
  are generous (e.g. uaddi0 80 links, "tighten to 24"). Running a ratchet over seeds 1-4 (per-cell max of
  every route's proposal, never below the rule E pads) until rules A and E are clean on all four; then
  fresh seeds with headroom, as for gcd_hw.
### progress 16:50 (R2: routed GLS 16/16 on all 8 seeds, ~2.0x)
| laps per 150 us GLS window | R2, seeds d,2,3,4,5,6,7,8 | mean | unsized (seeds d,2-8) | ratio of means |
|---|---|---|---|---|
| vec 6 (gcd.c's pair) | 47 48 48 48 53 54 50 48 | 49.5 | 24-26 (seeds 5-8: 24 24 25 24) | ~2.0x |
| vec 12 (2^31-1, 2) | 38 38 39 39 43 44 40 39 | 40.0 | 18-20 | ~2.1x |
| vec 13 (1000000, 999999) | 55 57 55 56 61 64 59 56 | 57.9 | 27-29 | ~2.1x |
Worst seed (fewest laps): d at 47/38/55, still 1.9x the best unsized seed. Every R2 route: gate clean,
16/16 errs=0. x0.9/x1.1 16/16 on d, 2-7 (seed 8 corners running). Scatter on R2 d: 8.5% x2, 17% x2, 20% x2,
25% x1 all 16/16; seed 2: 8.5% x2, 17% x2, 25% x1 all 16/16.
- collatz sizing ratchet (seeds 1-4): pass 1 latency 0.52-0.55x of the padded build on every vector and
  seed (GLS passes) but rule A 3-4 per seed; pass 2 rule A 1-3; pass 3 rule A 1-3 and rule E 1-2 (shorter
  compute chains make requests earlier, so the select pads must grow): the merge now also takes skew.py's
  fix asks (current + ask + 1). Continuing.
### progress 17:45 (collatz sizing ratchet converges on seeds 1-4)
- Ratchet (fusion_bench --sizes, seeds 1-4, merge = per-cell max of every route's tighten.py proposal,
  never below the rule E pads, plus skew.py's fix asks as current+ask+1 from pass 3 on): rule A per seed
  (3,3,4,4) -> (1,2,1,3) -> (1,2,1,3)+E(1,2,0,0) -> (0,1,2,2) -> (1,1,0,1) -> **(0,0,0,0), rule E 0 on all**
  (pass 6, research/data/collatz_sizes_S5.vh). The binding cells move every pass (control merges, then
  muxes, uselect0), as on gcd_hw.
- Candidate CR = S5 + 1 link on every cell (research/data/collatz_sizes_CR.vh), being validated on seeds 1-8
  with every audit and routed GLS. R2 seed 8 x0.9 16/16; R2 d scatter 20% x2 and 25% draw 2 16/16.
- R2 seed 8 x1.1 16/16: **R2 passes nominal, x0.9 and x1.1 routed GLS on all 8 seeds.** Running: wire-mode scatter (per pip, 25% x1, 35% x2) on R2 seed 2.
### progress 18:30 (rule E finds more with the C-node launch; R2 on hold; ipow/isprime DSP pads)
- **skew.py (rule E): the select's feeding-link C node is now always among the launches evaluated** (subagent's
  "Part A", committed here). The verdict was and stays the MIN guarded margin over every launch evaluated,
  so this can only make rule E stricter. Why: launches are ranked by select crossings and only cand[:4]
  evaluated; a 32-bit latch bank fills those with its own outputs and the C node, where request and select
  really diverge, could sit at #96. Subagent's comparison of every gate's worst row (old -> new): soak_top 3
  gates 0 changed; collatz 18 gates 12 stricter; ipow 24/16 stricter; xorshift 24/14 stricter; isprime 86/58
  stricter (one new violation, ucond_br31 -178 ps); **gcd_hw BOARD-QUEUE #1 recipe seeds 1-8: 28 stricter,
  0 verdicts changed, worst guarded margin per seed unchanged (174-520 ps)**; nowhere more permissive.
  Negative control: isprime with ucmpi2's delay removed: ucond_br16 flagged (raw -16.3 ns) in old and new.
  pytest verify 52 pass. NOT committed: the subagent's opt-in "Part B" (stop the request walk at the gate's
  own pins, which clears the isprime ucond_br16 false violation): it also loosens rows whose binding launch
  is not the C node (gcd_hw ucond_br23/28/41, +66..+1449 ps), so it removes more than the artifact.
- **R2 under the new rule E: seeds 2 and 6 violate** (seed 2: ucond_br42 -520, ucond_br46 -167, ucond_br10
  -10 ps guarded, raw +2.3..+3.9 ns, from ulink_n145__3 / ulink_n1__1 C nodes; seed 6: 8 rows). Seeds d, 3,
  4, 5, 7, 8: 0. So the sized design has select margins the old rule E did not measure. BOARD-QUEUE #2 is ON
  HOLD; building R3 = R2 + skew.py's asks + 1 from all 8 routes, to be re-audited on 8 seeds and GLS'd.
- Subagent round 4 (ipow and isprime, BD_DSP=1, all audits on the OLD skew.py): ipow two pad rounds, rule E
  clean on 5 of 8 fresh routes (seed 12 still -568 ps guarded), GLS 8/8, 101.0 ns per iteration (99.0-102.6),
  vectors now non-degenerate except one deliberate wrap (65536^2). isprime: two rounds, rule E clean on 3 of 8
  fresh routes (ucond_br16 artifact plus umux6/7/9), **first rule J violation seen in the wild**: seed 11
  ucontrol_merge3.uarb1 client 2, raw +956, guarded -45 ps, no knob; GLS 8/8. Neither kernel is clean.
- collatz CR (= S5 + 1 link everywhere): rules E/H/I/J clean on 8/8 but **rule A 1 on 7 of 8**, always
  ucontrol_merge1 (6 links; margins -125..-1022 ps): the extra link elsewhere moved its data peak later.
  Ratcheting CR on its own 8 routes (CR2).
- R2 d scatter 25% draws 2-4 also 16/16.
### progress 19:30 (R3, collatz 8-seed ratchet, wire scatter)
- R2 seed 2 (tightest rule A route), GLS_SCATTER_MODE=wire (one factor per pip): 25% x1, 35% x2 all 16/16.
- R3 (R2 + C-node rule E asks + 1 on ulink_n112__1, n145__3, n1__1, n94__1) under the new rule E: seeds d, 2,
  5, 6, 7 clean on every audit; **seed 3: ucond_br33 -83 ps guarded (raw +2863), asks +1 on ulink_n106__1**.
  The rule E long tail now, as rule A had: each route finds one more paddable link.
- collatz: CR's 8 routes pass the new rule E (0 on all). T1 = CR + ucontrol_merge1 9: rules A 0 on 8/8, rule E
  0 on 7/8 (seed 4: 2, padding in T2). Running T2 on 8 seeds.
### progress 21:30 (collatz sized: 1.56x per iteration, every audit + routed GLS clean on 8 seeds; gcd_hw R4)
- **collatz T3** (research/data/collatz_sizes_T3.vh, 42 sizes): the ratchet continued on 8 seeds from CR
  (T1: ucontrol_merge1 9; T2 = T1 because the ratchet's merge dropped a rule E ask for a link with no
  size macro -- fixed: it now falls back to the kernel's DELAY default; T3: ulink_n1__1 0 -> 2).
  `fusion_bench.py --mlir .../collatz/... --sizes research/data/collatz_sizes_T3.vh --route
  --nextpnr-seeds 1 2 3 4 5 6 7 8`: rules A/E(new, C-node launches)/H/I/J 0 on all 8, gate clean on all 8,
  **routed GLS fast + stalled pass on all 8**.

| collatz, ns per loop iteration (slope over 16 vectors) | seeds 1..8 | mean | range |
|---|---|---|---|
| padded (rule E pads only) | 156.3 160.2 156.6 159.6 158.6 164.2 161.9 157.0 | 159.3 | 156.3-164.2 |
| **T3 (route-measured sizes)** | 98.3 101.3 106.1 107.5 99.6 103.4 102.6 99.3 | **102.3** | 98.3-107.5 |
  1.56x (worst T3 seed 107.5 vs best padded 156.3: still 1.45x). Zero-delay RTL is 18.4 ns, so ~84 ns of
  each iteration is still routing and the remaining delay lines. Merge script committed as
  research/data/collatz_ratchet_merge.py (scratch tool, not a flow).
- gcd_hw R4 (= R3 + rule E ask on n106__1 + umux10/umux6 headroom): every audit clean on 7 of 8 seeds;
  seed 7: ucond_br42/45 -64/-222 ps guarded (raw +4.4 ns) from yet another link (ulink_n155__1). New:
  `skew.py --slack <ps>` (706f697) prices fixes for gates within <ps> of the guard, to buy headroom across
  routes instead of chasing one link per route; measuring R4's 8 routes at --slack 500 to build R5.
- The sandbox disk filled (GLS build dirs, ~900 MB each); cleaned. One slack measurement (R4 seed 8)
  failed on it and is being rerun.
### progress 23:00 (collatz T3 robustness; R5; xorshift ratchet started)
- collatz T3, seeds 1 and 4: routed GLS at x0.9, x1.1, per-arc scatter 8.5% x2 and 17% x1: fast and stalled
  pass on all 10 runs.
- gcd_hw R5 = R4 + `skew.py --slack 500` asks over R4's 8 routes (links n129__0/1, n151__1, n155__1, n32__0,
  n59__3, n8__1, n90__0; research/data/gcd_hw_sizes_R5.vh). Audit running: d and 5 clean so far. **Seed 2:
  nextpnr placement failed** ("post-placement validity check failed for Bel SLICE_X18Y90/A5FF (no cell)"),
  a placer legality failure on this netlist+seed, not an audit result; seed 9 substituted. First time this
  error is recorded here; worth a look if it recurs (RLOC v4 groups vs packing).
- xorshift (frontend kernel, fusion_bench --mlir, placeholders fail rule E per the subagent) ratchet started
  on 8 seeds with the collatz procedure.
### progress 00:30 (R5 audits: 7/7 placed routes clean)
- gcd_hw R5 under the C-node rule E: rules E/A/H/I/J clean on seeds d, 3, 4, 5, 6, 7, 8 (seed 2 did not place,
  see above; seed 9 running as its substitute). The --slack 500 step closed the long tail seen R2 -> R3 -> R4
  (one new short steer link per route). R5 routed GLS (nominal + corners) running on d, 3, 5, 6.
- xorshift ratchet: placeholders fail rule E on 8/8 seeds (1-6 each; GLS passes 8/8); pass 1: rule A 4-8,
  rule E 2-8 per seed (shorter compute makes requests earlier; pads catching up). Continuing.
### progress 01:30 (xorshift sized: 1.70x per round, every audit + routed GLS clean on 8 seeds)
- **xorshift T3** (research/data/xorshift_sizes_T3.vh), fusion_bench --mlir .../xorshift/... (the frontend
  kernel, fork fusion + cap 4), ratchet over seeds 1-8 from placeholders (rule E fix asks + rule A proposals,
  per-cell max), 3 passes: rules A/E(C-node)/H/I/J 0 on all 8, gate clean on all 8, routed GLS fast+stalled
  pass on all 8.

| xorshift, ns per round (slope over 6 vectors, rounds 0-4) | seeds 1..8 | mean | range |
|---|---|---|---|
| placeholders (FAIL rule E on 8/8: 1-6 gates each) | 102.2 103.0 102.3 102.9 102.0 100.8 105.4 101.5 | 102.5 | 100.8-105.4 |
| **T3** | 61.6 60.1 61.6 61.4 61.4 59.1 59.4 56.8 | **60.2** | 56.8-61.6 |
  1.70x, against a baseline that is itself unsafe (it needs rule E pads, which add delay), so the speedup
  over a SAFE unsized build is larger. Only 6 vectors (simcheck's; fusion_bench adds random ones only for
  collatz/isprime/ipow): a thin oracle, though non-degenerate.
- gcd_hw R5: seed 9 clean too: every audit clean on 8 placed routes (d, 3-9; seed 2 unplaceable).
- xorshift T3 re-validated with 14 vectors (simcheck's 6 + 8 seeded random nonzero states, rounds 0-8;
  fusion_bench commit above), seeds 1-8 rerouted: rules A/E/H/I/J 0 (tighten.py's exit 1 is rule D's 8
  screens), GLS fast+stalled pass on all 8. Per round over 14 vectors: **64.3 ns (60.7-65.9)** (the 6-vector
  fit said 60.2; the wider round range is the better fit).
### progress 02:30 (ipow DSP pads clean on fresh seeds; isprime DSP: rule E and GLS agree on a real failure; rule J in the wild)
Subagent round 5 (committed rule E, BD_DSP=1, the shipped config), reviewed:
- **ipow** with research/data/ipow_dsp1_rulee3_sizes.vh (placeholders + 4 select-link pads), FRESH seeds
  13-16: rules A/E/H/I/J 0, gate clean, GLS fast+stalled pass (17 vectors, 16 non-zero + the deliberate
  65536^2 wrap); 103.4 ns per iteration (101.6-106.1). Pads only, compute at placeholders: a ratchet run
  on ipow (my loop, seeds 1-8, from these pads) is in progress.
- **isprime** with research/data/isprime_dsp1_rulee3_sizes.vh, fresh seeds 13-16: rule E 4, 0, 4, 1 of 86;
  **seed 13: umux1 raw -676 ps (negative BEFORE the guardband) and routed GLS FAILS** (out0 req out of
  phase, X pulse; all values seen before were correct). So on a route where rule E reports a raw-negative
  margin, the routed GLS fails too: another case where rule E is load-bearing and GLS agrees.
  Seed 15: rule J violated on ucontrol_merge5.uarb1 client 2 (raw +1010, guarded -103 ps, shared 591 ps):
  the second arbiter-fork violation found in the wild (both isprime); no delay knob, placement only.
  The ucond_br16 false violation remains on seed 13 only (raw +8.5 ns).
  Remaining paddable asks: ulink_n29__1 +9, ulink_n66__2 +5.
### progress 03:30 (rule J survey over 168 routes; isprime DSP round 4)
Subagent round 6, reviewed:
- isprime BD_DSP=1 round-4 pads (research/data/isprime_dsp1_rulee4_sizes.vh; n29__1 21, n66__2 17), fresh
  seeds 17-20: A/H/I/J 0, rule E 1/0/0/0 (seed 17: umux11 raw +1329, guarded -1094, asks +4 on ulink_n79__1),
  gate clean, GLS fast+stalled pass on 4/4; ucond_br16 not flagged on any. n=997 39.72 us (39.62-39.77).
- **Rule J survey** (arb_fork.py on 168 routed SDFs, 1562 arbiter x client rows; script + rows in
  research/data/ruleJ_survey/): **minimum RAW margin +618 ps over all rows** -- the arbiter's handover
  ordering holds on every route; both violations ever seen (isprime DSP1, -45 and -103 ps) exist only after
  the 0.772/1.155 guardband. The tail is set by how far A0 travels (A0 > 2 ns: min -103, median +590; < 1 ns:
  min +204, median +711) and by arbiter count (isprime 7 arbiters: ~1 route in 8 fails, a fifth within
  200 ps; gcd_hw 9 arbiters: 0 of 40 fail, worst +185; 2-arbiter kernels: none below +272). So: seed selection
  suffices for gcd_hw and the 2-arbiter kernels; isprime has a systematic guardband tail. Candidate fix is
  placement (BD_RLOC_ARB=1 grouping, which flow.sh cannot enable today); note that on gcd_hw (2026-10-26
  00:50) grouping changed the worst rule J margin by +8 ps only, because A0 itself comes from far away.
### progress 04:20 (BOARD-QUEUE #2 is now R5)
- R5 routed GLS: d, 3, 7, 9 16/16 at nominal (vec 6: 47, 42, 48, 48 laps), d and 7 also x0.9/x1.1 16/16.
  BOARD-QUEUE #2 rewritten for R5 (rebuild command, md5s ce596deb / 7be3c1cf / a9c4e265). Seeds 5, 6 GLS
  still running.
- ipow ratchet: placeholder + rule E pads are already clean on 8/8 (it0); T1 = pads + it0's tightened
  proposals, running.
- R5 seeds 3 and 9 also pass x0.9/x1.1: R5 routed GLS nominal + both corners 16/16 on d, 3, 7, 9.
### progress 15:42 (correction: this session's progress times)
- The "### progress HH:MM" times in this session's entry after the first few were ESTIMATES and drifted far
  from real time (e.g. the note headed "04:20" was written around 15:15 UTC). The commit times in
  `git log` are the true ones. From here on every heading comes from `date -u +%H:%M` (PROGRAM.md, 17edbba).
### progress 15:54 (arbiter grouping fixes isprime's rule J tail; flow.sh opt-in)
Subagent round 7, reviewed:
- cells/flow.sh: opt-in BD_RLOC_ARB (rloc_stamp.py --arb-groups, as build_hw.sh). Unset: same seed gives a
  byte-identical soak.fasm/xdc/rloc.log, and soak.json/sdf/routed.json identical after path normalisation.
- isprime BD_DSP=1, round-5 pads (research/data/isprime_dsp1_rulee5_sizes.vh), seeds 21-24, grouping off vs on:
  rule J worst guarded -105 (violation, merge7) -> **+142 ps (0 violations)**; rule E violations 9 -> 3 (clean
  seeds 0/4 -> 2/4); GLS passes in both arms; n=997 latency 40.95 -> 39.02 us. Raw margins barely move; the
  shared part of A0's route doubles (median 243 -> 489 ps), and the guard applies only past the split. Unlike
  gcd_hw (+8 ps) because isprime's A0 nets are long (median 1.1-1.2 ns, max 3.0 ns).
- Grouping is INCOMPLETE: 4 of 7 arbiters grouped; ucontrol_merge7 (4-input merge, a tree of 3 arbiters) is
  not -- stamp_arbiters() only uniquifies one level below a singly-instantiated module. Fix next.
### progress 16:11 (collatz and xorshift sized builds hold on FRESH seeds)
- collatz T3 and xorshift T3 (both ratcheted on seeds 1-8) on fresh seeds 9-12: rules A/E/H/I/J 0 and
  routed GLS fast+stalled pass on 4/4 each (xorshift with the 14-vector set). So both now pass every check
  on 12 routes, 4 of them never seen by the sizing loop.
- gcd_hw R5 seed 5 routed GLS 16/16 (vec 6 49 laps): nominal GLS on 5 seeds (d, 3, 5, 7, 9).
### progress 16:31 (isprime: all 7 arbiters grouped; rule J clean on fresh seeds; only ucond_br16 remains)
Subagent round 8, reviewed and committed:
- rloc_stamp.py --arb-groups (only under BD_RLOC_ARB): (a) an arbiter LUT already claimed by a spine group
  leaves it for its own bdarb_ group (isprime's 4-input merge, bdc_amerge4, had all 12 LUTs in v8 spine
  groups, which is why it was skipped, not depth); (b) uniquification repeats until every module holding an
  arbiter is instantiated once. Stamped netlists unchanged for soak_top v8/v4, gcd_hw v4 (on and off) and
  isprime off; changed only where intended (isprime v8+arb: 4 -> 7 grouped; soak_top v8+arb: 0 -> 1). 4 new
  unit tests (2 fail on the old code); pytest verify 56 pass.
- isprime BD_DSP=1, BD_RLOC_ARB=1, research/data/isprime_dsp1_rulee6_sizes.vh, FRESH seeds 25-28: 7/7 arbiters
  grouped; rules A/H/I/J 0 (rule J worst +266 ps); rule E 0 on 2 seeds, and on the other 2 ONLY ucond_br16
  (raw +8.1/+8.4 ns, the launch-selection false violation; no knob); GLS fast+stalled pass 4/4; n=997
  38.97 us (38.39-39.49). Groups are tile-sized: 1-2 arbiters per seed straddle the tile's two slices.
- Decision kept: skew.py's Part B (which would clear ucond_br16) stays out; isprime is reported as not
  clean on rule E rather than loosening the audit.
### progress 17:05 (container restart)
- The container restarted around 16:40-17:00 UTC; every background job died (ipow ratchet at pass 3, R5 GLS
  seed 6, both subagents: August-failure regressions, gcd RTZ tail analysis). Toolchain still in place,
  toolchain.sh all ok. Restarting them.
### progress 17:08 (gcd critical cycle, hop by hop: where a lap goes; RTZ = 36%)
Subagent round 9 (analysis, one route: gcd_hw R5, default seed, all audits clean, GLS gate clean; tools in
research/tools/rtz/): VCD of every routed net for one 3154.3 ns lap of vector 6, back-traced event by event
(5229 hops, each matched exactly: t_in + wire + arc = t_out).
- **Falling (return-to-zero) edges are 35.7% of the critical path** (1126 of 3154 ns); wire is 79% (2501 ns)
  vs cell arcs 654 ns. Rise: compute matched delays 956 ns, gates 334, link rdly 244, link C nodes 203.
  Fall: link rdly 227 (no fast fall), compute udly 223 (FASTFALL already), C nodes 221, gates 197.
- One ctz-loop iteration (28 per lap) = 43.0 ns: rise 26.9 (uori4's 19-link delay 10.4 alone), fall 16.1
  (umux15 3.1, ulink_n151__0 rdly 2.8, ulink_n145__3 rdly 2.5 at full cost on the fall). One wire,
  ucond_br45_j -> ucond_br45, costs 1.77 ns on each edge.
- **The board's "23-cycle RTZ tail" (cells/hw/README.md) is not the kernel's:** its output RTZ in this rig is
  ~14 ns (~1.5 board cycles). The tail is a gen_bench harness interaction (its FSM's S_RTZ waits on a
  synchronised o_req); a routed GLS of gcd_bench_gen would settle it (not run). rtz_cost_results.tsv now shows
  12.1, not 23.
- Speed proposals, each to be gated by audits + GLS on >=4 seeds: (P1) fast fall for bd_link rdly and
  mux/merge output delays (~7.6% lap, frozen rtl/: needs routed-GLS justification); (P2) uori4 19 -> 13
  links (rule A here says so, but R5 keeps 19 because other routes asked for it); (P3) RLOC-group each steer
  join with its steer (~5% lap from one wire on the ctz ring); (P4) two-phase links on loop rings (removes
  the falling lap, large change).
### progress 17:34 (August silicon failures as board-free regression tests; FASM audit on every build)
Subagent (August regressions), reviewed; cells/check.sh ALL GATES PASS end to end with everything applied
(17m39s, in its worktree); pytest verify 75 pass here.
- **verify/fasm_audit.py, now run by flow.sh and build_hw.sh after routing (exit 0 pass, 1 mismatch, 2 cannot
  check; any nonzero stops the build):** reads every LUT site's INIT and every DSP48E1 register/const-pin bit
  back out of the FASM and checks it against the yosys netlist (hierarchical names resolved strictly).
  Catches the three August FASM-writer bugs: lut-pinmap (run-together X_ORIG_PORT; emulated unpatched writer:
  58 corrupted LUT sites on a gcd_hw route, 90 on ipow), dsp-constpins (packer half and inversion half, 24 and
  24 on the probe), dsp-areg (4 on the probe). Gate verify/fasm/check.sh runs a probe with each encoding plus
  each bug re-applied as a negative control. PASS on soak, gcd_hw (8925 sites), collatz, xorshift, ipow DSP.
  Note: toolchain.sh's dsp-areg fingerprint ("ZAREG_2_ACASCREG_1") CANNOT fail -- the string is already in
  unpatched fasm.cc; not changed (toolchain.sh is frozen against weakening; the FASM audit now covers it).
- verify/cdc_fsm.py + cdc_bench.sh (gate): the bench FSM reads the kernel only through a two-flop
  synchroniser; on all 6 kernels; the August wiring and a one-flop version both fail it. 5 unit tests.
- verify/harness_pss.sh (gate): the synthesised bench harness passes tb_gcd_bench_gen (guards the hist[]
  memory-inference class; the specific August bug does not reproduce on yosys 0.62, so this guards the class).
- tb_gcd_bench_gen drives out0_data to X outside req-up..ack-up; verify/bench_window.sh re-applies the August
  late read (isprime 0x80000000) and checks that it fails.
- Not reproducible without the board: the gcd_hw sweep stale-result (settle window) and the cmpb probe's stale
  operands (an instrument's silicon timing; the probe no longer exists with fusion on).
- Anomaly, R5 seed 6 GLS: the first `vvp gate.vvp` printed 4 SDF errors ("Invalid/malformed IOPATH" at
  annot.sdf:94016, "Too many errors"); a rerun on the identical files (routed.json/sdf md5 = the route's,
  annot.sdf unchanged since its write at 17:22) gives ANNOTATE_DONE with 0 warnings/errors. Most likely the
  first gate read the file before it was completely on disk (this was right after the container restart). The
  vector runs use netlist_baked.v from the same gen.py run, so they stand; flagged here in case it recurs.
### progress 17:48 (correction: the "restart" did not kill everything; R5 seed 6 GLS discarded)
- After the container notice, some pre-restart jobs were in fact still running: the old ipow loop (already at
  pass 4) and the old R5 GLS chain (which finished seed 6 at 17:38). My restarted duplicates wrote into the
  same directories, so **both R5 seed 6 GLS results are discarded** (the transient gate parse error above is
  explained by this: two gen.py runs, nominal and x1.1, writing the same annot.sdf). Seed 6 is being rerun in a
  fresh worktree. The duplicate ipow loop was killed; the surviving loop redoes pass 3 from T3 (same inputs).
  Rule kept: after a restart notice, check `ps` before restarting anything.
### progress 18:46 (R5 routed GLS on 6 seeds)
- R5 seed 6 rerun in a fresh worktree: every audit clean, gate clean, 16/16 at nominal (vec 6 50 laps), x0.9,
  x1.1. R5 now: every audit clean on 8 placed routes; routed GLS nominal + both corners 16/16 on 6 (d, 3, 5,
  6, 7, 9). BOARD-QUEUE #2 updated.
- ipow ratchet pass 3: rules A+E clean on seeds 1, 5, 6, 7; A <= 2 and E <= 4 elsewhere; pass 4 running.
### progress 19:47
- R5 seed 4: every audit clean, gate clean, 16/16 at nominal (vec 6 45 laps), x0.9, x1.1. R5 routed GLS
  (nominal + corners) now on 7 seeds (d, 3, 4, 5, 6, 7, 9); seed 8 running.
- ipow ratchet pass 4: rules A+E clean on 7 of 8 seeds (seed 1: rule A 1); pass 5 running.
### progress 20:38 (R5 complete: every audit + routed GLS with corners on all 8 placed routes)
| R5, laps per 150 us | d | 3 | 4 | 5 | 6 | 7 | 8 | 9 | mean | unsized |
|---|---|---|---|---|---|---|---|---|---|---|
| vec 6 | 47 | 42 | 45 | 49 | 50 | 48 | 49 | 48 | 47.3 | 24-26 |
| vec 12 | 38 | 34 | 37 | 39 | 41 | 39 | 39 | 38 | 38.1 | 18-20 |
| vec 13 | 56 | 49 | 53 | 57 | 59 | 56 | 57 | 56 | 55.4 | 27-29 |
Every route: rules A/E(C-node)/H/I/J 0, gate clean, 16/16 errs=0 at nominal, x0.9 and x1.1. Worst seed (3)
still 1.6x the best unsized seed. BOARD-QUEUE #2 updated.
### progress 20:54 (ipow sized, with DSPs: 1.36x per iteration, every audit + routed GLS clean on 8 seeds)
- **ipow T6** (research/data/ipow_dsp1_sizes_T6.vh; BD_DSP=1, the shipped config; routed GLS through the new
  DSP48E1 model): ratchet over seeds 1-8 from the rule E pads (research/data/ipow_dsp1_rulee3_sizes.vh, which
  were already clean at placeholder compute), 6 passes (rule A per pass: 3-6, 3-5, 0-2, 0-1, 0-1, 0): rules
  A/E(C-node)/H/I/J 0, gate clean, GLS fast+stalled pass on all 8 (17 vectors, one deliberate wrap).

| ipow, ns per loop iteration (slope vs bit length of e) | seeds 1..8 | mean | range |
|---|---|---|---|
| placeholder compute + rule E pads | 103.6 105.4 103.0 107.6 105.4 105.7 106.1 107.6 | 105.6 | 103.0-107.6 |
| **T6 (route-measured sizes)** | 73.8 77.7 79.7 76.0 78.0 78.7 78.8 76.8 | **77.4** | 73.8-79.7 |
  1.36x (worst T6 seed 79.7 vs best baseline 103.0: 1.29x). Smaller gain than collatz/xorshift: the DSP
  cascade's own arcs (A->P 5.4 ns per DSP) dominate the multiply and are not a delay line.
- R5 seed 4 per-arc scatter 8.5%: 16/16 (17%, 25% x2 running).
### progress 21:18 (ipow T6 on fresh seeds: rule I short on 2 of 4; T7)
- ipow T6 on fresh seeds 9-12: GLS pass 4/4, rules A/E/H/J clean on 11 and 12, but **rule I short on seeds 9
  and 10** (ulink_n13 stage[1] -20/-11 ps, falseResult_11 stage[1] -179 ps; SDELAY asks). So T6 (validated on
  the 8 seeds it was ratcheted on) is not yet a fresh-seed-safe size set -- same lesson as gcd L7.
- T7 = T6 + those routes' proposals + 1 link on each raised cell (ulink_n13 SDELAY 2 -> 4, falseResult_11
  SDELAY 0 -> 2; research/data/ipow_dsp1_sizes_T7.vh); validating on 8 more fresh seeds 13-20.
- R5 seed 4 scatter: 8.5%, 17%, 25% draw 1 all 16/16.
### progress 21:40 (P3 steer-join grouping: safe, no speedup -- negative result; round-9 hop corrected)
- Correction to the round-9 trace: the 1.77 ns hop is uori4's delay-chain end (g[18]/O6) -> ucond_br45_j/A3,
  not ucond_br45_j -> ucond_br45 (the back-tracer labels a hop by its receiving cell). The join -> steer net is
  already the 295 ps minimum on every route.
- P3 implemented as an opt-in (rloc_stamp --steer-join-groups / BD_RLOC_STEERJ; default off byte-identical; 4
  unit tests) and A/B'd on gcd_hw R5, seeds d/3/4/5 both arms: every audit clean in both arms, routed GLS 16/16
  (ON arm also x0.9/x1.1 on 2 seeds). 37/38 steers land with their join; the join->steer wire unchanged (295 ps),
  the uori4->join wire moves with placement (775-2504 off, 776-1899 on). Lap change per seed on vec 6: +2.0,
  -15.2, -3.6, +1.2% (mean -4.2%, carried by one seed whose OFF route was the slowest; OFF alone spans 16%).
  **Not a speedup; not committed** (diff kept as research/data/p3_steer_join_groups.diff).
- R5 scatter: seed 4 8.5/17/25/25% all 16/16; seed 3 17% 16/16.
### progress 22:02 (ipow T7 on 8 fresh seeds; T8; P1 fast fall reviewed, check.sh running)
- ipow T7 on fresh seeds 13-20: every audit clean and GLS pass on 7 of 8; seed 19 rule I short (ulink_n17__0
  stage[1] SDELAY, -366 ps). Rule I has the same long tail rule A and E had. T8 = T7 + 1 on every SDELAY (15) +
  that ask (research/data/ipow_dsp1_sizes_T8.vh); validating on fresh seeds 21-28.
- Subagent: P1 (fast fall on bd_link rdly and rtl bd_mux output delay, opt-in BDC_LINK_FASTFALL=1, default
  byte-identical) with a NEW tighten.py rule F ("a fast-fall line is flushed before its input can rise again":
  an undrained line lets the next token's request skip links -- unaudited until now, for the existing compute
  FASTFALL lines too). A/B on gcd_hw R5 seeds d/3/4/5: every audit incl. F clean in both arms; routed GLS 16/16;
  laps +8.2% (vec 6), +8.1% (12), +8.4% (13); ON-arm corners and 17% scatter clean on 2 routes. Being checked
  with cells/check.sh before commit.
- gcd_hw R5 with BD_RLOC_ARB=1 (seeds d, 3) running, to see whether arbiter grouping speeds gcd as it did isprime.
### progress 22:10 (P1 committed: fast fall on link/mux request delays, opt-in; rule F)
- Committed: rtl/bd_link.v RFAST and rtl/bd_mux.v FASTFALL parameters (default 0, unchanged netlists; stated
  reason in each header), bdc/emit.py BDC_LINK_FASTFALL=1 (refused for kernels with memory), tighten.py rule F
  + rule I padding-estimate fix, 2 tests. cells/check.sh ALL GATES PASS with it applied (run here in a clean
  worktree); pytest verify 77 pass. Default-off identity: emitted Verilog cmp-identical for 8 kernels; gcd_hw
  R5 default seed fasm/frames byte-identical, SDF md5 a9c4e265 (= BOARD-QUEUE #2's).
- Evidence for the rtl/ change (routed GLS, gcd_hw R5, seeds d/3/4/5 per arm): every audit incl. F clean;
  laps OFF -> ON: vec 6 45.75 -> 49.5 (+8.2%), vec 12 37.0 -> 40.0 (+8.1%), vec 13 53.75 -> 58.25 (+8.4%), vec 4
  +1.7%; ON corners x0.9/x1.1 and 17% scatter clean on d and 3. Rule F worst margin: new lines >= +2.7 ns; the
  existing compute line ucontrol_merge12.udly is the tightest (+770..+1341 ps).
- Not yet: rule F re-run on previously claimed routes (BOARD-QUEUE #1/#2, collatz/xorshift/ipow sizes); P1 as a
  BOARD-QUEUE candidate (needs 8 seeds + corners).
### progress 22:43 (ipow T8: 7/8 fresh; T9 with compute headroom; arbiter grouping on gcd)
- ipow T8 on fresh seeds 21-28: every audit + GLS clean on 7 of 8; seed 24 rule A ushrsi0 (28 links, -146 ps).
  T9 = T8 + 1 link on every compute cell (14) + that ask (research/data/ipow_dsp1_sizes_T9.vh), the recipe that
  closed gcd (r1/R2); validating on fresh seeds 29-36.
- gcd_hw R5 with BD_RLOC_ARB=1, default seed: every audit clean, GLS 16/16, laps vec 6 47 (ungrouped 47), x0.9
  16/16. No speedup on gcd (isprime's gain came from its long A0 nets). Seed 3 running.
- gcd_hw R5 + BD_RLOC_ARB=1: seeds d and 3 every audit clean, GLS 16/16 (d also x0.9/x1.1); vec 6 laps 47 / 46
  vs ungrouped 47 / 42. Two seeds, within route scatter: no demonstrated speedup on gcd; not pursued.
### progress 23:25 (ipow T9: clean on 8 fresh seeds)
- **ipow T9** (research/data/ipow_dsp1_sizes_T9.vh = T8 + 1 link on every compute cell), FRESH seeds 29-36 (none
  ever fed the ratchet): rules A/E/H/I/J 0, routed GLS fast+stalled pass on all 8 (seed 36's log, written after
  the tighten.py update, also shows rule F 0). **76.2 ns per iteration (74.6-78.6)** vs 105.6 for pads-only
  compute: **1.39x**; the headroom costs nothing measurable (T6 77.4 on other seeds). T6/T7/T8 each failed one
  fresh route in four-to-eight; T9 is the first ipow size set clean on a full fresh 8.
### progress 23:28 (link fast fall on xorshift: -9% per round)
- xorshift T3 sizes + BDC_LINK_FASTFALL=1 (13 fast-fall instances emitted), seeds 1-4, 14 vectors: rules
  A/E/F/H/I/J 0, routed GLS fast+stalled pass on 4/4. Per round: **65.4 -> 59.5 ns (-9.0%)** vs T3 without fast
  fall on the same seeds (65.9/64.4/65.4/65.7 -> 59.6/59.7/59.9/58.7). Combined with sizing: 102.5 -> 59.5 ns
  per round vs the placeholder build (1.72x). collatz the same way running.
### progress 23:31 (rule E: opt-in removal of the own-gate lap; a fwd() bug found)
Subagent round 11, reviewed, committed as OPT-IN only (skew.py --own-gate-laps-off-strict; default off):
- For a gate where Part A added a feeding-link C node, the request walk from that link's latch-output (lap)
  launches may not expand through the gate's own pins. Flag off: -v output byte-identical (soak, gcd R5, isprime,
  negctl); check.sh's rule E gate identical. Over 96 routes: 174 rows change, every one verified to be a lap
  through the gate's own select (path replay, t_req match, strict margin never lower), 0 others move. isprime
  rule-E-clean routes 13 -> 23 of 50 (ucond_br16: 53 VIOL -> ok, all now binding at the C node, min +9.5 ns).
  Negative controls still flag: ucmpi2-delay-removed isprime (ucond_br14-17 ~ -20 ns, both arms); uori4 delay
  zeroed in a gcd R5 SDF (ucond_br41-46 -1.4..-3.6 ns, both arms). pytest verify 75 pass here.
- **Side finding, pre-existing, NOT fixed:** skew.py fwd() can overwrite a storage node that seeded a level with a
  later within-level arrival without re-expanding it, so pred/tab disagree; path_to() replay -- used by the
  divergence point t_c (shared-route credit) and req_knob() -- can follow a wrong chain on lap paths. A wrong t_c
  could over-credit (permissive). Effect on committed verdicts not yet measured: next round. Until then the
  strict flag stays off by default.
### progress 23:46 (link fast fall on collatz: -12% per iteration)
- collatz T3 sizes + BDC_LINK_FASTFALL=1 (17 fast-fall instances), seeds 1-4: rules A/E/F/H/I/J 0, routed GLS fast+
  stalled pass on 4/4. Per iteration 98.3/101.3/106.1/107.5 -> 92.8/93.3/87.4/90.8 ns: **103.3 -> 91.1 (-11.8%)**.
  With sizing: 159.3 (padded) -> 91.1 ns per iteration, 1.75x. gcd_hw R5 + BD_RLOC_ARB seed 3 x0.9/x1.1 16/16.
- Next: fast fall needs the same fresh-seed / 8-seed / corners treatment as the sizes before it is a default or a
  board candidate (subagent doing gcd_hw R5+FF to 8 seeds; ipow+FF running).
### progress 23:50 (link fast fall on ipow: -6% per iteration)
- ipow T9 + BDC_LINK_FASTFALL=1 (11 instances, BD_DSP=1), seeds 29-32: rules A/E/F/H/I/J 0, GLS fast+stalled pass
  4/4. Per iteration 74.6/77.9/74.9/77.1 -> 71.3/70.3/74.3/71.0: **76.1 -> 71.7 ns (-5.8%)**; with sizing 105.6 ->
  71.7 (1.47x). Smallest gain of the three kernels (fewest link/mux delays on its cycle; the DSP cascade dominates).
| link fast fall, 4 seeds each | without | with | change |
|---|---|---|---|
| gcd_hw R5, vec 6 laps (more = faster) | 45.75 | 49.5 | +8.2% |
| collatz T3, ns/iteration | 103.3 | 91.1 | -11.8% |
| xorshift T3, ns/round | 65.4 | 59.5 | -9.0% |
| ipow T9 (DSP), ns/iteration | 76.1 | 71.7 | -5.8% |
### progress 23:56 (collatz and xorshift with link fast fall: 8 seeds clean)
- collatz T3 + FF, seeds 1-8: rules A/E/F/H/I/J 0, GLS fast+stalled pass on 8/8; **92.1 ns/iteration (87.4-95.6)**
  (T3 alone 102.3; padded 159.3: 1.73x overall).
- xorshift T3 + FF, seeds 1-8 (14 vectors): same, **60.0 ns/round (58.7-62.1)** (T3 alone 64.3; placeholders
  102.5: 1.71x overall).
- ipow T9 + FF seeds 33-36 running (29-32 clean, 71.7 ns).
### progress 00:07 (collatz + FF: corners and scatter clean)
- collatz T3 + link fast fall, seeds 1 and 4: routed GLS at x0.9, x1.1, per-arc scatter 8.5% x2 and 17% x1: fast and
  stalled pass on all 10 runs.
- xorshift T3 + link fast fall, seeds 1 and 4: x0.9, x1.1, scatter 8.5% x2 and 17%: fast+stalled pass on all 10 runs.
### progress 00:11 (ipow + FF on 8 seeds; collatz64 vectors)
- ipow T9 + link fast fall, seeds 29-36: rules A/E/F/H/I/J 0, GLS fast+stalled pass on 8/8 (per-iteration numbers in
  the commit message).
- fusion_bench: collatz64 gets 8 seeded random vectors whose trajectory peak exceeds 2^31 (the reason the 64-bit
  kernel exists); simcheck had 3. A first collatz64 routed GLS (placeholders, 3 vectors) is running; it will be rerun
  with the 11.
  ipow T9 + FF over seeds 29-36: **72.2 ns/iteration (70.3-74.3)** (T9 alone 76.2; pads-only 105.6: 1.46x).
### progress 00:26 (collatz64: first routed GLS -- fails, and rule E agrees)
- collatz64 (64-bit datapath), placeholder lengths, seeds 1-4: rules A/F/H/I/J 0 but **rule E 3-4 violated on every
  seed** (umux0/umux1; two rows raw-negative, -210 and -810 ps), and **routed GLS fails on all 4** (fast and
  stalled): every value checked was correct, then "req fell out of phase on out0" -- the select-deficit signature
  seen on collatz and isprime. Rule E and routed GLS agree again. Ratchet (rule E pads + rule A sizes, seeds 1-8,
  11 vectors) running; seeds 5-8 at placeholders with 11 vectors also running.
### progress 00:42 (rule F holds retroactively; P1 -> BOARD-QUEUE #3)
- Rule F (committed tighten.py) re-run on every route already claimed: gcd_hw R5 (8), BOARD-QUEUE #1 (3 incl. the
  committed route, sdf md5 6f8b99e6), collatz (12), xorshift (20), ipow (16): **0 violations, worst +463 ps**. No
  shipped claim changes.
- P1 (R5 + link fast fall) on 8 routes (d, 3-9): every audit clean, fasm_audit PASS, routed GLS 16/16 at nominal on
  8, corners on 6, 17% scatter on 2; vec 6 50.0 laps (46-52) vs 45.75 without. Written up as BOARD-QUEUE #3. #2's
  entry now says to check routed.json/sdf md5s, since the .bit md5 is not reproducible (header bytes).
### progress 01:12 (sizing ratchet is now a tool: bdc/size_kernel.py)
- `bdc/size_kernel.py` (+ 11 tests) replaces the scratch loops and `research/data/collatz_ratchet_merge.py`: ratchet
  (per-cell max of T<k>, tighten --emit, rule E asks as current+N+1, dut.v default fallback; never lowers), stops
  NOT CONVERGED instead of padding when F/J fail or a merge changes nothing; `--headroom` (+1 link per compute cell);
  `--fresh-seeds` validation. Enforces A/B/C/F/H/I/K/L, E, J and routed GLS fast+stalled; D reported only. Its merge
  reproduces the scratch xorshift T1-T3 byte for byte on the scratch inputs.
- xorshift from placeholders, seeds 1-4, defaults (no FF): converged at it4 (4/4 clean); T4H on fresh seeds 9-12
  every enforced rule 0, GLS pass: **66.5 ns/round (65.1-67.6)**; T3 on the same 4 fresh seeds 64.4. 4 seeds per arm
  cannot split headroom from scatter. Data: `research/data/size_kernel_xorshift/`.
- **Routed GLS passed on every route of it1-it3, where static audits found 2-9 violations per seed** (short delays):
  GLS is not a substitute for the audits, again.
- Method weakness, not fixed: UCONTROL_MERGE1 went 12 -> 1 (it0 proposals) -> 32 (tighten prices rule-A padding with
  the 124 ps cell arc rather than the ~419 ps per-link hop) and "never lower" keeps 32 although routes then say 4.
  Costs nothing measurable on training seeds (64.9 vs 65.4) -- inference, not proof that it is off the critical cycle.
### progress 01:31 (tighten.py: rule A link pricing)
- Rule A turned a deficit into links at chain_ps/n -- at n=1 the bare 124 ps LUT arc, so ucontrol_merge1 was told
  "PAD to 32" when a routed link costs ~419 ps. The same average priced *tighten-to* proposals, in the unsafe
  direction: uxori1 (xorshift it1 seed 1) margin 425 ps, real link 489 ps, old proposal "tighten to 2" (64 ps short).
- Fix: price at the cell's own routed chain (LUT arc + hop, from the SDF); without one, pad at the route's cheapest
  link and tighten at its dearest (both err longer); old price only if the route has no 2+ link chain. Re-priced on
  the 16 xorshift it1-it4 routes: only ucontrol_merge1 it1 32->11 and uxori2 it1 7->6 get smaller (each <= what all
  later routes ask); violation counts unchanged in every old/new log. 5 tests, 4 fail on a chain/n mutant.
- No shipped claim is touched: verdicts come from measured margins, not proposals, and every claimed sizes file was
  re-audited after its last merge. Rules H/B/C still price at chain/n (not changed). New sizes not yet routed.
### progress 01:34 (container restart; jobs re-launched)
- Restart at ~01:30 killed every job. BQ#3 FF default-seed reproduction had finished: md5s match (routed.json
  f9c4597d, sdf 61e14755), rules E/A/H/I/J 0, gate ANNOTATE_DONE with 0 SDF warn/err, nominal GLS 16/16 correct
  (errs=0). Corners and wire scatter re-launched on the same build (md5 re-checked first).
- After the restart `cells/verify/toolchain.sh` failed with its default TC path (resolved to a /home/jayjay
  path); with TC=/root/dev2/lib/fpgatoolchain it passes, nextpnr 9c732bc6303458df, unchanged.
- collatz64 ratchet restarted at it1 (T1 = it0 merge: rule E 3-6 per seed on all 8, rule A 0).
### progress 01:47 (skew.py walk fix; strict stays opt-in)
- skew.py's level walk let a seeded storage output (or the launch at level 0) be re-relaxed through its own cell arc
  inside the same level, overwriting its tab entry and predecessor; replays then broke and t_c fell back to 0. Fix:
  skip seeded nodes inside their level (2 tests, both fail with the skip removed). On 96 routes / 12918 walks:
  t_req, t_sel, t_c, guarded margins and every verdict unchanged; only the padding target (req_knob) moves on 122
  rows. check.sh's rule E gate output is byte-identical.
- Consequence: isprime ucond_br16's lap (54 violated rows) now names a knob, so --select-pads would ask 4 links on
  ulink_n78 (isprime_dsp1_pad5 s21). The subagent recommends making --own-gate-laps-off-strict the default.
  **Not done:** that would relax a safety audit on static evidence only (no GLS or board test of the lap argument);
  over-padding only costs isprime latency, which is not a claimed number. Strict stays opt-in until a routed-GLS
  negative control shows a lap row can be ignored safely.
### progress 02:16 (BQ#3 route reproduced; wire scatter to 35% clean)
- BQ#3 (gcd_hw R5 + link fast fall), default seed rebuilt independently: routed.json/sdf md5s identical to the
  committed evidence; rules A/E/H/I/J 0; gate ANNOTATE_DONE, 0 SDF warn/err; routed GLS 16/16 errs=0 at nominal,
  x0.9, x1.1, wire scatter 25% x1 and 35% x2. Added to BOARD-QUEUE #3.
- collatz64 ratchet it1: rule A 4-12 / rule E 6-7 per seed, GLS fails (out0 out of phase) on all 8 -- audits and
  GLS agree; it2 running.
### progress 02:21 (owner: board-fidelity GLS is THE priority -- re-planned)
- Read the owner's cbb347e/eb4380c/976cf90 (PROGRAM.md "THE priority", CLAUDE.md, TC default fix). Speed work stops;
  the collatz64 ratchet keeps running only as an idle-core filler (renice +10). Rule gates stay exactly as they are
  until the new GLS passes acceptance.
- prjxray-db zynq7 (commit 0a0added, 2021-12-14) sparse-cloned to /root/dev2/lib/xray/prjxray-db (91 MB): tile_type
  pip/wire delays at 4 corners + R/C, timings/*.sdf, segbits, xc7z010clg400-1. prjxray.timing imports from the
  openxc7-src checkout via PYTHONPATH. (pip-installing fasm/sdf-timing from git was refused by the session; not
  needed so far.)
- Four workstreams (subagents, shared brief): F1 prjxray RC-tree delay calculator -> min:typ:max SDF for gen.py, hand
  checks, comparison with nextpnr's SDF, ring validation; F2 netlist from FASM (fasm2bels or focused converter),
  equivalence on BQ#3's route, lut-pinmap negative control; F3 transport/hazard LUT model, metastability,
  correlated + per-wire variation from the ring data, with negative controls; F4 acceptance suite: inventory of every
  silicon measurement and August failure with its reproducible bitstream/route, harness, baseline on today's GLS.
- Committed before the redirect (rule tooling, now "heuristics"): rule A link pricing (e68dcd6), skew walk fix
  (9b6596d), size_kernel tool (54e0247). BQ#3 reproduction + scatter clean (cbe2206).
### progress 03:06 (tighten.py: rules H/B/C share rule A's link pricing)
- One pricing function for A/H/B/C (pad at own link cost, else route min; tighten never deeper than the old price).
  On 52 routes (16 xorshift, the RAM soak, 35 gcd_hw): per-section VIOLATION counts and exit codes identical; of
  ~8000 proposals 0 got smaller, 4 rule H tightens got 1 link longer. First draft priced tightens at the own step
  only and would have taken 12 gcd_hw rule-H lines to 0 links unsafely (the hop into the line is lost too) -- caught
  by the A/B and fixed. Rules B/C rest on one route (soak). Heuristic tooling; no gate changed.
- Coordination slip: I put two subagents in the same worktree (wt_aug); one's checkout wiped the other's uncommitted
  edits, which it rebuilt from copies. Each workstream now gets its own worktree.
### progress 03:08 (F1: prjxray delay calculator -- nextpnr misses the site input-pin delay)
- `cells/gls/fid/xray_delay.py`: nextpnr routed.json -> prjxray node model -> RC tree with prjxray timing.py ->
  SDF (FAST_MIN:SLOW_MIN:SLOW_MAX) on nextpnr's SDF as template; gen.py GLS_SDF_FIELD=min|typ|max, build.sh GLS_SDF.
  Default reproduces old gen outputs byte for byte (ro_top). Zynq7 db was fuzzed on xc7z020-1 (= board's -1); the
  4-tuple is [FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX]; timings/*.sdf groups are (fast)(slow), not rise/fall.
- Mapping proven by re-deriving nextpnr's getPipDelay from the resolved pips: within 1 ps on 41091/41096 (gcd),
  7746/7749, 2444/2444, 8365/8456 arcs (misses: one pad route-through); wrong-pip negative control drops it to 483/2444.
  Hand Elmore checks agree to 0.1 ps (buffered pip, fanout-6 with/without branches, synthetic pass-transistor chain).
- vs nextpnr, slow max: interconnect median x1.44 (+287 ps), growing with length (+166 ps at 1 pip, +727 at 13+).
  The biggest class is the **site input-pin delay nextpnr never charges** (+338 ps mean; LUT A1/A2 ~0.51 ns, A6
  ~0.005 ns), then fanout loading (25 ps median at fanout 1, 327 ps at 64+), OUTMUX; minus nextpnr's 25 ps site pips
  and 35 ps tie epsilon. Cell arcs equal except CK->Q (303 vs 340) and DSP (A->P 3841 vs 5400). Clock nets untrusted.
- Rings (across routes only; per-ring board periods for n=128 are not in the repo and that route predates the
  lut-perm-sink patch): no measured ring is above slow max (worst 0.72 of it); the board sits at ~0.35-0.41 of the
  [fast min, slow max] band on long rings, 0.25-0.58 on short ones. A fixed band position reproduces the measured
  0.938 slope and +309 of the +988 ps offset. Model spread is about half the measured ring scatter.
- Not shown: per-ring agreement, a full GLS run on the new SDF (only ANNOTATE_DONE/0 warnings on ro_top and gcd).
### progress 03:28 (F2: GLS netlist from the bitstream -- equivalent on BQ#3's route)
- `cells/gls/fid/fasm2net.py`: .bit -> bitread/bit2fasm (8 s) -> per-sink upstream trace over active pips, pseudo
  pips, tileconn joins and default IMUX pseudo pips -> nextpnr-shaped JSON that gen.py runs unchanged, plus the
  SDF re-keyed onto bels. Site models SLICEL/M (LUT6/5, F7/F8, CARRY4, FF), BUFGCTRL, BUFHCE, OLOGIC, IOB33, BSCAN;
  latch/LUTRAM/DSP/BRAM refused, not guessed. Every configured feature not consumed is listed (none on gcd_hw).
  fasm2frames/xc7frames2bit of the shipped FASM is byte-identical to the shipped payload.
- BQ#3 route (bit b40e4e41, json f9c4597d, sdf 61e14755): `fasm_equiv.py` EQUIVALENT -- 10136/10136 LUT functions,
  all 34975 driver->sink pairs, 12092/12092 nets with the same pip set; GLS from the bits 16/16, all SUMMARY lines
  byte-identical to the routed-JSON GLS; gate ANNOTATE_DONE, 0 SDF warn/err.
- Negative control: the *real* unpatched lut-pinmap writer changes 58 INITs on this route but 0 functions (every
  run-together pin is on GND, on all 19 gcd_hw routes in scratch) -- the August bug cannot recur from today's flow.
  Injecting its mechanism on live pins (97 pins / 81 LUTs under ucmpi*): fasm_equiv NOT EQUIVALENT (81 functions),
  FASM-built GLS 0/16 (no gcd completes; the August "absent result" signature) while routed-JSON GLS stays 16/16.
  Hard-test caveat: an injection, not the August bitstream (none archived).
- Not shown: delays (still nextpnr's), DSP/latch sites, corners/scatter on the FASM netlist, other designs.
### progress 04:01 (F2 phase 2: DSP48E1 + latches from the bits; DSP bitstream bugs detected)
- fasm2net decodes DSP48E1 (register bits, control pins through routing with DSP_GND/VCC bits and inverters) and
  LDCE/LDPE; anything outside the modelled configuration is refused by name. gen.py now emits a real latch
  (SLICE_LATX in prims.v) for LDCE/LDPE -- before, it simulated one as an edge-triggered flop. No current design
  instantiates LDCE (bd_latch keeps storage on LUTs), so no committed result changes.
- ipow BD_DSP=1 fresh7 seed13: bits EQUIVALENT (6 DSPs, same decoded words); GLS from routed JSON, .fasm and .bit
  identical latencies. Controls via `bit_control.py ROUTE KIND` (one CONTROL line, exit 0/1/2): dsp_constpins and
  dsp_constpins_inv (real unpatched writers) decode INMODE 11111 / ALUMODE 1100 / OPMODE6 1 on all 6 DSPs -- matching
  the patch README's board measurement -- NOT EQUIVALENT, GLS refuses ("A input gated to zero"). dsp_areg: the real
  writer is harmless on this route, so the bug was injected; detected. Caveat: refused, not simulated as numbers.
- xorshift fresh seed9: the real unpatched lut-pinmap writer changes 1 reachable LUT function (a harness C-element,
  1 of 8 input rows) that equivalence catches and **GLS does not** (vectors never reach it); live-pin injection
  fails GLS. Equivalence is the stronger bitstream check; GLS alone is not enough.
- Possible nextpnr defect (not on board, no shipped design affected): LDCE with .CLR(1'b0) is packed as VCC +
  IS_CLR_INVERTED, but a slice SR has no inverter, so the latch is held cleared (bits and both GLS agree).
### progress 04:15 (collatz64: ratchet converged at T4 -- filler work)
- collatz64 (64-bit datapath, 11 vectors incl. 8 with trajectory peak > 2^31), from placeholders: it0-it3 failed
  (rule E 3-7 and rule A up to 12 per seed; routed GLS failed on all 8 at it0/it1 with "req out of phase on out0",
  agreeing with rule E). **it4 (T4): rules A/E/F/H/I/J 0 and routed GLS fast+stalled pass on all 8 seeds** (rule D
  screen 6 per seed, informational). T4H (+1 link on 10 compute cells) on fresh seeds 9-16 running.
  Data: research/data/collatz64_sizes_T4{,H}.vh. Tool: scratch loop in wt_coll (8977190 tighten/skew), not
  size_kernel.py -- the run began before the tool landed.
### progress 04:32 (F4: acceptance inventory + harness; baseline on today's GLS)
- research/data/fid/inventory.{json,md}: 17 silicon items graded with source lines. **No August measured bitstream
  or route is archived, none has a recorded md5.** HARD: ring128 (n=128, self-checking readback, 0.052% repeat) --
  blocked, per-ring data only on the owner's machine; lut-pinmap (emulated on BQ#1's route, sdf 6f8b99e6 matches,
  and on an August-shaped BDC_OP_FUSION=0 route); dsp_constpins(_inv) (emulated on ipow T9 seed 29); dsp_areg
  (property only). SOFT: the 5-ring routes, abs_negative (cause revised), bench_hang (5/8 stochastic), isprime late
  read, every kernel timing (routes not archived), mem_dco edge_cap only. EXCLUDED: cmpb probe (stale operands).
- cells/gls/fid/acceptance.py with --sdf-cmd (F1) and --netlist-cmd (F2) hooks; hard/soft reported apart, exit 1
  only on a hard mismatch, blocked != pass. Baseline (today's GLS): every runnable hard bitstream test MISMATCHES --
  it passes bitstreams the board failed because it never reads the FASM. On the fusion-on gcd route the 58 corrupted
  sites are all latch odd-bit LUTs and the sim passes even with them corrupted, so that route cannot discriminate;
  the fusion-off route can: with a FASM-reading stand-in, unpatched completes 9/16, the missing 7 (5-8, 11-13,
  errs=0) are exactly BOARD-QUEUE #1's August list (patches/README says 7/16 -- records disagree; vector set soft).
- Soft cross-route rings: today's SDF reads ~+9.5% slow at 127 links on both August routes (which agree to 0.3%).
- ro_many_measure.py gains RO_OFFLINE/RO_MEAS_TSV so the owner can export the per-ring table without a board
  (BOARD-QUEUE owner-side request updated with the command).

## Session 2026-10-27 06:13 -- (in progress) board-fidelity GLS: F1+F2 integration, F3 silicon-like model; audit rows answered
Toolchain: patches 789a7120c912d393, nextpnr 9c732bc6303458df (cloud/setup-toolchain.sh from cache, 2m35s, all fingerprints ok)
### progress 06:13 (start; audit read)
- Lock was 2 h old (dead); taken. 4 cores, 15 GB. The prjxray-db clone xray_delay.py defaults to was lost with the
  container; the toolchain's own copy (openXC7 prjxray-db 0.8.2) has tile_type_*.json and timings -- an F5
  subagent checks whether it equals 0a0added before switching the default.
- Audit (origin/claude/audit REPORT.md) rows on this branch, answered:
  - bd_prims_sim.v 56/124 as rise/fall (REFUTED, still present): handed to the F3 subagent with the re-run list
    (tb_arb_overlap, arb_mtbf, null-gen tbs). Open until that lands.
  - BQ#1/#2 routed.json md5s do not reproduce (REFUTED): BOARD-QUEUE now says compare the SDF md5 only; #2's
    recorded routed.json md5 was probably from another build. No claim depended on it (the sdf md5s match).
  - BQ#3 "~9% more laps" (OVERSTATED): it compared 8 routes with 4. Same 8 routes: +5.8% (vec 6), +6.0%, +5.8%.
    Title and body corrected.
  - xorshift "102.5 -> 60.0 (1.71x)" (REFUTED as a comparison): 102.5 is a 6-vector fit, 60.0 a 14-vector fit,
    and the vector set alone moves the slope 6.9%. **Withdrawn**; the placeholder baseline was never fitted on 14
    vectors, so the true ratio is unknown until it is (queued as filler work).
  - ipow 1.39x/1.46x/1.47x, collatz 1.75x (UNVERIFIED): different seed sets in numerator and denominator. Collatz on
    the same seeds is 1.737x (audit). Treat the ipow ratios as unverified until re-measured on one seed set.
  - collatz64 T4 provenance (OVERSTATED): the T4 run used 8977190's tighten/skew (no rule F, older rule E) and the
    journal's "11 vectors" for it is right only for the later runs. The audit's seed-3 re-run with current tools is
    clean. **Re-run of all 8 seeds with current tools queued** (filler).
  - dsp_areg control "DETECTED" (OVERSTATED): agreed -- it is detected only by decoder refusal of an injected state
    the old writer never produced. README and bit_control's CONTROL line now say so; it stays a property, not a
    hard acceptance test (inventory already said "property only").
  - fasm_equiv misses unrouted GND-tied A6 pins that read VCC on silicon (NOT EQUIVALENT on BQ#1 per audit):
    harmless on that route (functions ignore the pin), but the checker must classify it; handed to the F5 subagent.
  - GLS "sample at fire" early edge and inertial LUT paths (CONFIRMED defects): F3 subagent builds an opt-in
    transport per-pin LUT model and reproduces the audit's 1130->1244 and XOR3 examples.
### progress 06:16 (rule F: the fall still in flight on the ripple wire)
- Audit rules.md #4 (CONFIRMED gap): rule F's t_flush was the latest stage OUTPUT fall, but a re-rise that reaches
  stage i's side tap before the fall has crossed the ripple wire into stage i passes straight through and skips the
  links before it. tighten.py now also takes, per stage, latest ripple-input arrival minus fastest side tap. The
  audit's example (arcs 124, hop 600, tap 295) gives t_flush 724 instead of 419. 2 new tests fail on the old code;
  one old test asserted a pass on exactly such a line (1000 ps ripple, 10 ps taps) and is now a failing case.
  cells/verify tests 92/92.
- **Not yet re-run on routes**: no claimed fast-fall route is on disk after the container restart. BQ#3's route is
  being rebuilt by the F5 subagent; rule F on it (and the fast-fall table's gcd/collatz/xorshift/ipow routes) must
  be re-checked before BQ#3 stands. Until then BQ#3's "rule F worst +888 ps" is the old rule's number.
### progress 06:18 (bd_link_dc uack: classified FASTFALL, so rule F audits it)
- Audit rules.md side note: in the opt-in bd_link_dc family uack is FASTFALL(1), but tighten.py classed every
  `.uack` tap as FASTRISE by name, so those lines escaped rule F and were walked with the wrong edge sense. Now a
  `.uack` is FASTRISE only when its link has no `ctl.ub` (the dc controller). 2 tests; 94/94 in cells/verify.
  No claimed design uses BD_LINK_DC (only cells/tb and flow.sh's BD_SYN_DEFS), so no claim changes; not run on a
  routed dc design.
### progress 07:40 (collatz64 T4 re-checked with current tools: clean on 8 seeds)
- Answers the audit's provenance row. `bdc/size_kernel.py --start research/data/collatz64_sizes_T4.vh --seeds 1-8
  --max-iter 1` at 818e90e (current tighten/skew/arb_fork; rule F's in-flight fix landed later but collatz64 has no
  fast-fall line, so rule F has no rows), 11 vectors from the C oracle:
  | collatz64 T4 | ns/iteration | n |
  |---|---|---|
  | seeds 1-8, routed GLS fast+stalled pass, A/B/C/F/H/I/E/J 0 | mean 102.65, range 99.7-104.8 (worst seed 3: 104.8) | 8 |
- **Coverage hole, same on all 8 seeds (identical list):** rule H skips 6 controllers ("no path from this node
  back to its own data": the four ulink_n21 lanes, n7, n8) and rule I skips 22 stages ("data enters from outside the
  design, or from no link stage that also requests"). Those stages are covered by routed GLS only. So "clean" means
  clean where the rules look. Data: research/data/collatz64_T4_recheck/ (log, seed-1 tighten.log, sdf md5s).
- Does NOT show: fresh seeds (all 8 were T4's fitting seeds -- the T4H fresh-seed run is still the validation and
  was not repeated); corners; anything on the board.
### progress 08:23 (xorshift placeholder baseline refitted on the 14-vector set)
- Replaces the withdrawn 6-vector-vs-14-vector comparison. Placeholder sizes, seeds 1-8, 14 vectors, 9452a14:
  | xorshift, ns/round, seeds 1-8, 14 vectors | mean | range | n |
  |---|---|---|---|
  | placeholders | 105.37 | 103.5-108.6 | 8 |
  | T3 (journal 1008, same seeds and vectors) | 64.3 | -- | 8 |
  | T3 + link fast fall (journal 1008) | 60.0 | 58.7-62.1 | 8 |
  Same-seed, same-vector ratios: **1.64x (T3), 1.76x (T3+FF)**. (The withdrawn figure was 1.71x.)
- Caveats: the placeholder design itself is NOT clean (rule E 1-6 violated per seed; routed GLS passes), so the
  baseline is the unsized reference, not a verified design. The T3+FF number predates today's rule F fix and must
  be re-audited before it is quoted as verified. Tool version differs between the arms (T3 measured at the 10-26
  tools). Data: research/data/xorshift_placeholder_14vec/.
### progress 08:47 (F3: opt-in silicon-like primitive model GLS_MODEL=fid -- landed except bd_prims_sim)
- Subagent F3, write-up research/data/fid/f3_model.md. Opt-in (GLS_MODEL=fid / -DGLS_FID); default GLS unchanged:
  gen.py outputs md5-identical on a fresh arb_mtbf route (json 43e15fb7, sdf 814299ac), also with GLS_SCATTER=0.1 in
  arc and wire mode, and a 3 us routed GLS with old vs new prims.v has identical histories on all 124,240 signals.
  Only arb_mtbf was checked this way.
- LUT/MUXF7/F8 transport per input pin: the audit's examples now come out right (1130 edge lands at 1254, was 1244;
  XOR3 cone settles 1224, was 1124 -> a request at 1200 has -24 ps, was +76). Narrow pulses and a 30 ps two-input
  XOR hazard pass. No published 7-series pulse-filter figure found (only Alfke's posts), so every pulse passes.
- Metastability: same-LUT loops and flops resolve near-simultaneous arrivals randomly with an exponential tail
  (tau/window ASSUMED: 150 ps LUT loop, 75 ps flop, >= the 57/51/73 ps of Beer et al. ASYNC 2010). Arbiter race x200:
  default r1 200/200, fid 125/75, no settled double grant (transient overlaps <= 26 ps). Routed arb_mtbf 20 us:
  99 / 94 resolver events (seeds 1/2), no x.
- Variation: GLS_SCATTER_REGION (per 10x10-slice block) on top of per-wire scatter; region 0.16 + wire 0.126 gives
  8.33% median ring scatter on ro_many_top's 128 rings (target 8.5%); per-wire alone 0.65%. The split is not
  identifiable without the per-ring board data. GLS_SDF_FIELD=band places delays inside an arc's fast/slow range.
- Library hazard census: every multi-input hazard in cells/rtl state LUTs is excluded by the 4-phase protocol, is
  the arbitration race, or is the existing bundling constraint; 11 cell tbs under fid: 0 library resolver events.
- Controls: cells/gls/fid/f3/run_f3.sh -- each tb must FAIL on the default model and PASS on fid; re-run here: all ok.
- **Held back:** the bd_prims_sim.v one-corner fix (audit REFUTED row) turns check.sh's run_sim gate red
  (tb_arb_overlap's "hazard must appear arc-only" was a corner-mix artefact; tb_ctl's decoupled ATTEMPT now
  deadlocks instead of losing data, and the bench waits forever). Sent back to make both benches assert what is true
  without weakening them. bd_arb.v's "rising grant wins by 16 ps" header is unproven under one corner.
- Does NOT show: no full kernel (gcd_hw/BQ#3) GLS under fid yet; CARRY4/DSP/latch/BUFG/flop clock pins still
  sample-at-fire; multi-cell loops get no resolver; taus unmeasured.

## Session 2026-10-27 10:12 -- (in progress) board-fidelity GLS: the full stack (bits netlist + prjxray SDF + fid primitives) on BQ#3; one-corner cell sims
Toolchain: patches 789a7120c912d393, nextpnr 9c732bc6303458df (cloud/setup-toolchain.sh from cache, 2m06s, all fingerprints ok)
### progress 10:17 (start; audit read)
- Lock 08:23 (109 min, dead); taken. 4 cores, 15 GB. Fresh container: no routes on disk; prjxray-db zynq7 re-cloned
  at 0a0added (91 MB) to the path xray_delay.py defaults to.
- Audit pass 5 rows on this branch: 6119060 xorshift re-baseline CONFIRMED (seeds 5-8 sized means unpublished --
  noted); 9452a14 collatz64 "clean" OVERSTATED as coverage wording (rule H audits 29 of 35 controllers, rule I 12 of
  34 stages; agreed, this is the correct reading of the progress note); 5567170 fid model OVERSTATED in parts:
  OUTMUX not modelled in xray_delay (subagent S2 on it), per-pin LUT arcs add little because prjxray's A1..A6->O6 are
  equal (agreed: the gain is transport, not per-pin), metastability window pessimistic (a request 360 ps later
  still wins 75/200 -- stated assumption, to be revisited), and f3_model.md lists bd_prims_sim.v/tb_end.v as changed
  but they are not in the commit (true: held back; subagent S1 redoes it now). Still open from earlier passes: BQ#3
  rule A `ushrsi1` -36 ps at one consistent fast corner with interval semantics -- this is what the full-stack GLS at
  the fast corner is for (below).
- Plan: main thread runs the integrated stack on BQ#3's default-seed route at FAST_MIN, SLOW_MAX and band; S1 lands
  the single-corner bd_prims_sim.v; S2 fixes OUTMUX in xray_delay.py and the A6 GND/VCC class in fasm_equiv.py.
- build_fid.sh now takes GLS_SDF (re-keyed in place of nextpnr's SDF) and GLS_MODEL=fid, read as gls/build.sh reads
  them; default output unchanged (both only add when set).
### progress 10:53 (full stack runs on BQ#3; S1 and S2 landed)
- Routes rebuilt from scratch and reproduced: BQ#3 (sdf 61e14755, routed.json f9c4597d), BQ#1 (sdf 6f8b99e6).
- **Full stack** = netlist decoded from the .bit (fasm2net) + prjxray RC-tree SDF (xray_delay) + GLS_MODEL=fid
  primitives, on BQ#3's default-seed route, SLOW_MAX column, 150 us per vector: **16/16 vectors, errs=0**, both before
  (sdf f71b407c) and after (ef6d6e77) S2's routing-BEL fix. Equivalence of the bits vs routed JSON: EQUIVALENT.
  Laps per 150 us at SLOW_MAX: vec 6 33, vec 12 27, vec 13 39 (nextpnr-SDF nominal on this route: 51/42/60 per the
  audit's own run) -- the prjxray slow corner runs this route ~1.55x slower than nextpnr's SDF. The OUTMUX charge moved
  laps by <1% (vec 0 3122 -> 3096): the loop's critical cycle is mostly O6 paths.
- 16133 sink pins get 0 ps interconnect in the re-keyed SDF: 15845 are VCC ties (unused LUT pins), the rest are
  in-site hops (LUT -> F7/F8/CARRY4/FF D) whose delay is in the cell arc or the routing-BEL charge. Recorded, not a gap
  on a live path as far as checked.
- S2 landed: xray_delay charges every slice routing-BEL mux from slicel/slicem.sdf (hand check exact at 4
  corners); fasm_equiv: the audit's 3 A6 pins on BQ#1 are HARMLESS, a function that reads one is NOT EQUIVALENT.
- S1 landed: bd_prims_sim.v at one corner; run_sim suite 27/27 at slow max and fast min, route 0 and 354; 11 negative
  controls fail as intended. Closes the audit's REFUTED bd_prims_sim row. Open from it: bd_pipe_deco (an attempt,
  not a library cell) livelocks at slow max; the semi trigger-1 race is magnitude-dependent, not root-caused.
- lut_pinmap control on today's BQ#1 route: the real unpatched writer changes 58 INITs; one of them
  (ucontrol_merge12, SLICE_X22Y84/B6LUT under an F7AMUX) is written with no INIT at all, so equivalence now says NOT
  EQUIVALENT (earlier: "0 functions change"). Whether it changes a vector is queued (full stack on the bug bitstream).
- August-shaped route rebuilt: BDC_OP_FUSION=0 BD_NO_TIGHTEN=1 BD_RLOC=v4 (sdf c647eb1a); the pad-converge recipe does
  not converge on it (ulink_n32__2 measured short again after padding), so SELECT_PAD=4 as F4 recorded.
  lut_pinmap control: NOT EQUIVALENT (LUT FUNCTION DIFFERS). Full stack on good vs bug bitstream queued -- the hard test.
### progress 11:19 (fast corner, rule F re-check, rings, DSP controls under the full stack)
- **BQ#3 full stack at FAST_MIN: 16/16, errs=0** (laps vec 6 91, vec 12 75, vec 13 108; ~2.75x the SLOW_MAX laps).
  With SLOW_MAX (above) that is both consistent prjxray corners passing on the netlist decoded from the bits. Answers
  the audit's tcheck row 40 in part: the -36 ps on ushrsi1 needs req at FAST_MIN and data at FAST_MAX at once
  (Vivado's OCV box, ~24% spread inside one corner); no single corner fails, and within-die variation is being
  injected as measured-size scatter instead (queued: region 0.16 + wire 0.126 at min/max/band, and a 2x tail).
  Whether the OCV box or the measured ring scatter is the right size for within-die spread is open: the ring scatter
  (8.5% median) is the only silicon datum and it bounds within-die spread from above for long rings.
- **Rule F re-run with the in-flight fix** on today's BQ#3 route: 65 fast-fall lines, worst +888 ps
  (ucontrol_merge12.udly) -- the same number as before the fix, so BQ#3's figure stands. BQ#1: 29 lines, worst +1343.
  research/data/fid/bq3_tighten_today.log.gz.
- **Rings after the OUTMUX fix** (research/data/fid/rings_outmux.md, today's ro_top route, across routes = soft):
  all 10 measured periods lie inside [FAST_MIN, SLOW_MAX]; band position 0.36/0.37 at 127 links on both August
  routes, 0.25-0.58 on short rings. Unchanged by the fix (ro_top's rings route no O5 through an OUTMUX).
- soak_fid.py takes GLS_SDF and GLS_MODEL=fid too. **ipow T9 seed 29 (BD_DSP=1) full stack at SLOW_MAX, good bits:
  PASS fast + stalled**, latencies 1.54x nextpnr's SDF. dsp_constpins / dsp_constpins_inv unpatched writers:
  DETECTED -- but by the decoder REFUSING the configuration (INMODE 11111 etc.), not by simulating the gated product.
  Graded: hard datum, detection mechanism = refusal (weaker than a simulated wrong answer; same caveat the audit gave
  dsp_areg). Note: today's fusion_bench defaults fastfall on, so this seed-29 route is not F4's route.
### progress 11:47 (HARD acceptance item reproduced by the full stack: lut-pinmap on the August-shaped netlist)
- Full stack (bits-decoded netlist + prjxray SDF + fid primitives), SLOW_MAX, nofuse route (BDC_OP_FUSION=0
  BD_NO_TIGHTEN=1 BD_RLOC=v4, sdf c647eb1a):
  | bits | equivalence | vectors complete | errs | never complete |
  |---|---|---|---|---|
  | patched (as built) | EQUIVALENT | 16/16 | 0 | - |
  | unpatched lut-pinmap writer (fasm_audit --write-unpatched pinmap) | NOT EQUIVALENT | 9/16 | 0 | 5,6,7,8,11,12,13 |
  The failure is absent results, not wrong ones (the board's signature), and the dead set is exactly BOARD-QUEUE
  #1's recorded August list. **First hard acceptance item MATCHED by the full board-fidelity stack** (before: today's
  GLS MISMATCHED it, baseline.md). Caveat (inventory): an emulated defect on a rebuilt route, not the August
  bitstream; which vectors fail is soft (patches/README says 7/16 complete -- the records disagree), that it fails is
  the hard claim. The GLS reads the bits, so this is the sim detecting it, not the equivalence checker.
- Also 16/16 errs=0: BQ#3 at band 0.38 (laps v6/v12/v13 55/45/64 -- 8% MORE than nextpnr's SDF predicts, 51/42/60);
  BQ#1 at SLOW_MAX (16/12/18). Table: research/data/fid/fullstack.md (regenerated as runs land).
- Audit r5 3g (metastability window pessimistic): agreed and kept as is for now -- TAU=WIN=150 ps is a stress
  setting that exercises both outcomes far more often than silicon would; fid meta-event counts are not rates. A
  silicon-sized window needs the board (hw/arb_mtbf).
### progress 12:07 (OOM lost two vectors; BQ#1 bug bits; 8-seed full stack queued)
- **Lost data, recorded:** a full-stack vvp is ~3.1 GB RSS and its iverilog compile ~3.7 GB; four sims plus a compile
  overran 15 GB and the OOM killer silently truncated BQ#1 FAST_MIN vectors 6 and 14 (run_fid printed "no verdict
  line"; every other completed run was checked: no other truncation). The run is discarded and re-queued; at most 3
  vvp-class jobs at once from now on. A truncated log must never be read as a pass: run_fid's "no verdict line" is
  the tell.
- BQ#1 route, unpatched lut-pinmap bits (58 INITs changed, one LUT left with no INIT), full stack SLOW_MAX: **16/16,
  errs=0**, laps within 1-6% of the patched bits' (vec 6 16 vs 16). So the bug is harmless on this fusion-on route in
  the full stack too, as F4 found with a LUT-only reader: this route does not discriminate, the nofuse one does.
- BQ#3 seeds 3-8 rebuilt (sdf b238ca95, a0d20c19, c71ed2cb, a1abd66d, ec9a75df, a81e16ee; seed 9 building);
  full stack at FAST_MIN and SLOW_MAX queued for each, after the scatter draws.
- Subagent S3: acceptance.py `--stack full`, so the harness itself runs the hard items on the full stack.

(The 2026-10-27 10:12 session ended without a closing note after progress 12:07; its lock went stale at 12:50.
Its queued 8-seed full-stack runs and the S3 harness change are not on the branch: no results from them exist.)

## Session 2026-10-28 23:11 -- (in progress) board-fidelity GLS: 8-seed full stack on BQ#3, scatter draws, acceptance --stack full
### progress 23:11 (start)
- Lock 12:50 on 10-27 (34 h old, dead); taken. 4 cores, 15 GB. Fresh container again: no routes on disk.
- Audit: no new pass since 10-27 12:42 (pass 6 queued, unpublished); every research row was answered last session.
- Plan: rebuild BQ#3 seeds d,3-9 (one nextpnr per core, at most 3 vvp-class jobs), full stack at FAST_MIN and
  SLOW_MAX on each, then region 0.16 + wire 0.126 scatter draws; subagent S3 redoes acceptance.py --stack full.
### progress 23:17 (toolchain up; 8 BQ#3 routes building; S3, S4 out)
- cloud/setup-toolchain.sh from cache: EXIT 0, all fingerprints ok; patches 789a7120c912d393, nextpnr 9c732bc6303458df.
  prjxray-db zynq7 re-cloned at 0a0added.
- cells/gls/fid/seeds_fid.py: worktree per seed, build_hw.sh with the BQ#3 recipe, xray_delay SDF, build_fid +
  run_fid per column, one row per run; a vector without a SUMMARY line makes the run INCOMPLETE (the OOM lesson).
  Default-seed rebuild: sdf 61e14755, BQ#3's recorded md5 (routed.json f1b7814f, path-dependent as recorded).
- S4 (new): model the DSP48E1 in the configurations the unpatched constpins writers produce instead of refusing
  them, so the dsp hard items fail by a simulated wrong product, not by decoder refusal (audit r3 1).
### progress 23:40 (S4 landed: DSP constpins items now fail by simulated wrong products; 8 routes up)
- S4 (14d7b81): the bits-built GLS simulates the combinational DSP48E1 modes the unpatched constpins writers leave
  (INMODE 11111, ALUMODE 1100, OPMODE6=1) instead of refusing them. ipow T9 seed 29 BD_DSP=1 soak route:
  dsp_constpins and dsp_constpins_inv DETECTED by GLS FAIL (15/17 vectors wrong, every product 0); good bits PASS
  with the same latencies; default-configuration gen.py/fasm2net outputs md5-identical to HEAD. Hand check against
  the UG479 formulas 7680/0 mismatches, fault control 7680/7680 (re-run here).
  **Hard-item mismatch, recorded:** the board before the patch had 965/2016 ipow products right (48%) and one mult2
  DSP fully right; the model gives all zeros. Same bug, different route and vector set, so the *fraction* is soft --
  but "every product 0" cannot give 48%. Either silicon does not compute X AND Z with M=0 here, or the board's ipow
  used the DSP differently (e.g. some products not routed through the gated A). Next: read the August ipow/mult2
  records for which DSPs and operands were right; check which of the 5 INMODE/ALUMODE/OPMODE6 pins the board's
  route actually left without a tile bit (dsp_constpins depends entirely on "no bit reads 1").
- All 8 BQ#3 routes (d,3-9) built and every build_hw gate passed; xray SDFs complete. Full stack at FAST_MIN and
  SLOW_MAX running 2 at a time (~2 min per vector); region 0.16 + wire 0.126 (1x) and 0.32 + 0.252 (2x) draws at
  band 0.38 in a third slot.
- Note: gls/prims.v and gen.py changed (S4) while the sweep runs from the main tree; gcd_hw has no DSP and the
  default netlist text is unchanged, so runs before and after are comparable.
### progress 23:53 (DSP gated-logic mode now x; S5 CARRY4/latch transport held until the sweep compiles)
- 007e895: S4's model assumed a gated multiplier hands the ALU two zero partial products, so the unpatched constpins
  config (X AND Z on M) gave every product 0 -- contradicted by the board's 965/2016 right. UG479 fixes only their
  sum, so that case now simulates every output bit as x (MUNK). Re-run: dsp_constpins --good --gls DETECTED, bug
  bits "vector 1: out0 got xxxxxxxx expected 00000003" in both harnesses, good bits PASS.
- First full-stack vectors on today's routes: default seed FAST_MIN vec 6 = 91 laps, the same as last session's
  bq3_min (reproduced); seed 3 FAST_MIN vec 6 = 89; 0 errs so far everywhere, including the first region+wire draw.
- S5 returned: CARRY4 and SLICE_LATX per-pin transport under GLS_FID (default preprocessed text and a 124k-event
  VCD byte-identical; tb_f3_carry fails 5/5 on default, tb_f3_latch 2/5, both pass on fid; x-semantics check
  can fail). NOT applied yet: the running sweep compiles prims.v from this tree, and mixing models inside one
  8-seed table would make it unreadable. Applied after the last sweep compile.
  S5 finding: the DEFAULT CARRY4 chains CO1..3/O1..3 off its own path-delayed CO outputs, so every output moves at
  max(own arc, upstream CO arc): CIN->CO3 lands at 271 ps instead of the SDF's 114. Reading: prjxray's CIN->CO0
  (271) includes the slice output driver to general routing, while CO3->COUT is the dedicated chain, so 114 < 271 is
  not acausal; the internal ripple does not pass through the CO0 output pin. So the default GLS is PESSIMISTIC on
  carry ripple and the fid model (per-pin arcs, as nextpnr's timing analysis) is the faithful one. Not changing the
  default model (it is the shipped gate; pessimism there is safe).
- No board-queue change.
### progress 00:27 (sweep restarted on 78de9c2 from a frozen worktree; first rows)
- Stopped the sweep after ~30 min and restarted it from a detached worktree at 78de9c2 (S5's CARRY4/latch transport
  in), so every row of the 8-seed table is one model and later commits cannot change it mid-run.
- Rows so far (full stack: bits netlist + prjxray SDF + fid; laps vec 6/12/13 per 150 us):
  | seed | column | sdf / xray sdf | verdict | laps 6/12/13 |
  |---|---|---|---|---|
  | d | SLOW_MAX | 61e14755 / ef6d6e77 | PASS 16/16 errs 0 | 33/27/39 (identical to last session's, before S5) |
  | d | band 0.38, region 0.16 + wire 0.126, draw 1 | same | PASS 16/16 errs 0 | 53/42/62 (no scatter: 55/45/64) |
### progress 01:15 (6/32 full-stack runs, all PASS)
- seed d max: sdf 61e14755 xray ef6d6e77 PASS 16/16 errs 0 laps 33/27/39
- seed d band_s0.16-0.126-1: sdf 61e14755 xray ef6d6e77 PASS 16/16 errs 0 laps 53/42/62
- seed d min: sdf 61e14755 xray ef6d6e77 PASS 16/16 errs 0 laps 91/75/108
- seed d band_s0.32-0.252-1: sdf 61e14755 xray ef6d6e77 PASS 16/16 errs 0 laps 50/39/59
- seed 3 min: sdf b238ca95 xray 6dc1edca PASS 16/16 errs 0 laps 89/72/103
- seed 3 max: sdf b238ca95 xray 6dc1edca PASS 16/16 errs 0 laps 32/26/38
### progress 02:00 (S3 landed: acceptance.py --stack full; end-to-end lut-pinmap run started)
- 87100ea: acceptance.py --stack full (bits netlist + prjxray SDF at --corner min/max/band + fid primitives);
  test_acceptance 16/16; refusal-only detection reported as MATCH (WEAK); identical bitstreams or an unchanged
  writer can never MATCH. Default stack unchanged on the paths that run without routes.
- Nofuse route rebuilt by S3: sdf c647eb1a (the journal's), bit 951e767b. Running now from a worktree at 87100ea:
  `acceptance.py --stack full --corner max --items lutpinmap_gcd_nofuse` (expected several hours, one vvp).
  Last session's hand run on this route: patched 16/16, unpatched 9/16 with 5-8,11-13 never complete.
- Sweep: 9/32 runs done, all PASS.
### progress 02:31 (12/32 sweep rows PASS; acceptance retried after an OOM)
- The first --stack full acceptance run died in the fid compile (iverilog exit 137, OOM: three 2.5 GB vvps plus the
  3.7 GB compile). The harness reported ERROR, not a pass. Paused the scatter driver (seeds d and 3 done, both
  draws) to make room; retried; it is in its ANNOTATE gate now. Scatter for seeds 4-9 resumes after.
- seed 4 max: sdf a0d20c19 xray e9bb3663 PASS 16/16 errs 0 laps 31/24/36
- seed 3 band_s0.16-0.126-1: sdf b238ca95 xray 6dc1edca PASS 16/16 errs 0 laps 54/43/63
- seed 4 min: sdf a0d20c19 xray e9bb3663 PASS 16/16 errs 0 laps 83/66/98
- seed 3 band_s0.32-0.252-1: sdf b238ca95 xray 6dc1edca PASS 16/16 errs 0 laps 53/43/63
- seed 5 max: sdf c71ed2cb xray f3ca9bea PASS 16/16 errs 0 laps 34/27/40
- seed 5 min: sdf c71ed2cb xray f3ca9bea PASS 16/16 errs 0 laps 93/76/109
### progress 03:53 (seed 7 "livelock" was a decoder bug, fixed: 54f2ce6)
- BQ#3 seed 7 (sdf ec9a75df) full stack: vector 1 never completed (0 laps, errs 0) at FAST_MIN and SLOW_MAX; the
  bits-vs-JSON check said NOT EQUIVALENT (17 LUT functions differ, all $PACKER_GND_NET$LUT$* LUT1 buffers).
  Traced: nextpnr routes GND out of an UNUSED LUT (GND_WIRE -> SITEWIRE/SLICE_X18Y95/A -> always-on
  CLBLL_LOGIC_OUTS12 ppip -> SE6/EE2 -> IMUX1 -> the GND LUT's A3). The pips are in the bits; the source LUT and
  its whole tile have no bits, so fasm2net never decoded the slice, the source node floated, and the IMUX fell back
  to its VCC default ("pip driven from a floating node", 65 on seed 7, 8 on seed 5, 0 on d/3/4/6/8). The GND LUTs
  then output 1. A decoder defect, not a design or toolchain one: on silicon an LUT with no INIT bit outputs 0,
  which is what nextpnr relies on.
- Fix: decode every CLB tile; an unconfigured LUT6's O6 resolves to constant 0 (const/unused-lut). fasm_equiv also
  folds a json-only always-ppip that only feeds dead-route pips into that dead route. Seed 7: EQUIVALENT; seed d
  decode md5-identical before/after; lut_pinmap and lut_pinmap_live controls on seed 7 still DETECTED with the good
  bits passing. The nofuse acceptance route had no floating pips (unaffected).
- Seed 7's old rows (FAIL 15/16, vector 1) and seed 5's (PASS) are kept in the scratch dirs as *_olddecoder and
  are superseded; both seeds re-run on a frozen worktree at 54f2ce6 (same fid model as 78de9c2; only the decoder
  differs, and it is byte-identical on the other seeds).
- Lesson: an equivalence verdict of NOT EQUIVALENT on a shipped-recipe route is a stop sign for the sim result,
  whichever side is wrong; seeds_fid.py should put the equivalence verdict in its row (next).
### progress 03:56 (hard item MATCHED by the harness itself: acceptance.py --stack full)
- `acceptance.py --stack full --corner max --items lutpinmap_gcd_nofuse` (worktree at 87100ea; nofuse route sdf
  c647eb1a, xray sdf b2036378, patched bit 951e767b, unpatched 66379152; 126 FASM lines differ):
  **[MATCH]** patched 16/16 (EQUIVALENT), unpatched 9/16 (NOT EQUIVALENT: LUT FUNCTION DIFFERS), never complete
  5,6,7,8,11,12,13 -- the same set as last session's hand run and BOARD-QUEUE #1's August list. No hand step.
  Log and JSON: research/data/fid/acceptance_full_nofuse_max.{log,json}.
  Note: the patched FASM re-assembled here differs from the build's .bit (the harness used the build's own .bit;
  bitstreams are known not to be byte-reproducible, see BQ#3 "bit ... not reproducible").
- Scatter draws resumed for seeds 4,6,8,9,7,5 on the fixed decoder (54f2ce6).
### progress 04:35 (sweep 19/32 + re-runs; still no real failure)
- Seed 8 SLOW_MAX 34/28/40, FAST_MIN 94/76/109, both PASS; seed 4 region+wire 1x PASS 47/37/55; seed 9 decodes
  EQUIVALENT with no floating pips (its rows on the 78de9c2 decoder stand). Seeds 5 and 7 re-running.
### progress 05:02 (DSP hard items MATCH on the full stack, non-weak)
- `acceptance.py --stack full --corner max --items dsp_constpins,dsp_constpins_inv` (worktree dc2f93f; ipow T9
  seed 29 BD_DSP=1 soak route, routed.json e7a27380, sdf 5ef854a9, xray sdf bc6cb638): **both [MATCH], not WEAK**:
  good bits PASS both harnesses; the unpatched writers' bits FAIL with "vector 1: out0 got xxxxxxxx expected
  00000003" (dsp_model MUNK: a logic ALUMODE on a gated multiplier is unknown). Before today these were detected
  only by the decoder refusing the configuration (audit r3 1, graded weak). Data:
  research/data/fid/acceptance_full_dsp_max.{log,json}.
  Still soft: the board's 965/2016 correct products; the model now says "unknown", which neither predicts nor
  contradicts a fraction. dsp_constpins still rests on "a control pin with no tile bit reads 1".
- Seed 7 FAST_MIN on the fixed decoder: PASS 16/16, laps 87/70/101. Seed 9: SLOW_MAX 32/26/38, FAST_MIN 88/71/103.
- Running: acceptance lut-pinmap at FAST_MIN; seed 7 SLOW_MAX and seed 5 re-runs; scatter draws.
### progress 05:04 (soft ring items through the harness: inside the band, band 0.38 within a few %)
- ro_top rebuilt today (sdf 4875ce2b; ring periods from the xray SDF of the bits-decoded netlist, no sim), acceptance
  ring5_a/ring5_b --stack full at min/max/band: every measured period lies inside [FAST_MIN, SLOW_MAX] (min under-
  predicts by 33-54%, max over-predicts by 39-99%); at band 0.38 the long rings land within +-4% (127 links: +1.8%
  route A; 63 links: +1.3% / -3.6%), short rings -18.5..+16.7% (7 and 31 links, where per-route scatter is largest:
  the board itself showed 25% route-to-route at 7 links). SOFT (across routes; the measured routes are gone), and
  0.38 was fitted to these same rings last session, so the band agreement is a consistency check, not a prediction.
  Logs: research/data/fid/acceptance_full_ring5_{min,max,band}.log.
### progress 05:40 (S6 landed; gen.py SETUPHOLD bug fixed: the default flop check was silent on 284/326 flops)
- 923305d (S6): under fid, SLICE_FFX input pins are transport, CK runts judged against an ASSUMED 70 ps min pulse
  width (no source: prjxray-db has no WIDTH check; DS187 unreachable), SR inside the aperture is resolved
  metastably; BUFGCTRL I0->O transport. run_f3 all ok (tb_f3_ff 8/8 fail default, pass fid; mutated control
  differs 318/3000); default preprocessed text identical.
- 666ea57: gen.py's SETUPHOLD regex dropped every line with a negative number, i.e. all D and CE checks (84 of
  1218 parsed on BQ#3 d). Fixed; BQ#3 default seed, default GLS: 16/16, no violations, laps 51/42/60 (record).
  Every gen.py-based gate is now stricter on flops; other kernels' gates not yet re-run.
- DSP items at FAST_MIN: both MATCH too (good bits PASS, bug bits x).
### progress 06:25 (S7 landed: dsp_areg is a property test; decoder rule narrowed)
- d4896fe (S7): registered DSP48E1 decode + model; on verify/fasm/probe.v's route the patched FASM's AREG=1 DSP
  simulates 1 A stage, the unpatched writer's decodes AREG=2/ACASCREG=1 with CEA1 tied 0 (yosys's AREG=1 mapping),
  so A never loads and P is 0 every cycle (full GLS vs a probe.v oracle: 197/197 vs 102/197). Mutant decoder and
  mutant model each break it, so the property can fail both ways. S7's reading of the board record: the August
  A/B on the areg patch ran while constpins gated A to 0, so the board could not see AREG at all -- the
  "bit-identical before/after" is explained by that, not by "read ms later". Still unverified on silicon.
- 2nd decoder fix (after S7 flagged it): an all-zero LUT is const 0 only in a slice with no configuration; a real
  LUT whose INIT expands to 0 stays a cell. ipow --good passes again; seeds 5/7 still EQUIVALENT; d identical.
- Sweep: 26 rows, all PASS; seed 5 FAST_MIN 93/76/109 on the fixed decoder.
### progress 06:28 (BQ#3: 8 seeds x 2 corners on the full stack, 16/16 PASS each)
| BQ#3 full stack (bits netlist + prjxray SDF + fid) | n | pass | laps vec 6 mean (range) | vec 12 | vec 13 |
|---|---|---|---|---|---|
| FAST_MIN | 8 | 8 | 89.6 (83-94) | 72.6 (66-76) | 104.9 (98-109) |
| SLOW_MAX | 8 | 8 | 32.8 (31-34) | 26.2 (24-28) | 38.5 (36-40) |
| band 0.38 + region 0.16/wire 0.126 | 4 (d,3,4,6) | 4 | 51.5 (47-54) | 41.0 | 60.2 |
| band 0.38 + 2x scatter (0.32/0.252) | 4 (d,3,4,6) | 4 | 49.0 (44-53) | 38.8 | 57.5 |
Seeds: d,3,4,5,6,7,8,9. nextpnr-SDF nominal on the same 8 routes (BQ#3 record): vec 6 mean 50.0. Worst seed at
SLOW_MAX: 4 (31/24/36). Data research/data/fid/bq3_fullstack_8seed.tsv; BOARD-QUEUE #3 updated.
Does NOT show: silicon; scatter on seeds 5,7,8,9 (running); the board-fidelity sim is not yet accepted (ring128
blocked on the owner's raw data), so the rule gates stay.
### progress 06:50 (dsp_areg acceptance MATCH; disk filled and was cleaned; BQ#2 8-seed full stack started)
- 781eeae (S8): acceptance.py --items dsp_areg runs the property on verify/fasm/probe.v's route: **[MATCH]** in both
  stacks (patched X1Y14 1/1 stage; unpatched decodes AREG=2/BREG=2 with CE*1 tied 0, no product). Also: .bit md5
  guards now compare payloads from the sync word (xc7frames2bit writes the frames path into the header, so the
  old "bitstreams identical" guard could never fire). inventory.md now has a generator (inventory_md.py --check).
- Hard acceptance items on the full stack, as of now: lutpinmap_gcd_nofuse MATCH (SLOW_MAX; FAST_MIN running),
  dsp_constpins MATCH x2 corners, dsp_constpins_inv MATCH x2, dsp_areg MATCH (property, one route), ring128 BLOCKED
  (owner's raw per-ring data), lutpinmap_gcd (BQ#1 fusion route, where the bug is harmless) not run.
- The scratch disk reached 92% (each compiled full-stack sim is ~600 MB); 30 finished sims deleted, seeds_fid now
  deletes its .vvp after parsing. A BQ#2 sweep launched during the full-disk window ran twice on one dir and
  produced BUILD_FAIL/INCOMPLETE rows; discarded, relaunched once (default-seed sdf a9c4e265 = BQ#2's record).
### progress 07:47 (lut-pinmap MATCH at FAST_MIN too; acceptance status table)
- acceptance --stack full --corner min, lutpinmap_gcd_nofuse: [MATCH], patched 16/16, unpatched 9/16, never
  complete 5,6,7,8,11,12,13 (same set as SLOW_MAX). research/data/fid/acceptance_status.md summarises every item:
  all runnable hard items MATCH at both corners; ring128 BLOCKED (owner data), so not accepted and gates stay.
### progress 08:01 (BQ#2 full stack started passing; BQ#3 scatter on seed 8)
- BQ#2 default seed (sdf a9c4e265, BQ#2's recorded md5), full stack SLOW_MAX: PASS 16/16, EQUIVALENT, laps
  31/25/36 (BQ#3 same seed: 33/27/39, so fast fall is +6% at SLOW_MAX too). BQ#3 seed 8: 1x and 2x scatter PASS
  (51/41/59, 46/37/53). seeds_fid now serialises compiles machine-wide (the BQ#2 relaunch).
- S9 (new): a distribution-level ring128 check from the published per-length summary quantiles (formal branch's
  ro_many_2026-08-23_summary.csv); the per-ring table is still missing.
### progress 08:31 (ring128 at the distribution level: soft MISMATCH, and a re-reading of "short rings are slow")
S9's ring128_summary (commit above): the full-stack model is a soft MISMATCH against the published 128-ring
  quantiles (4/7 vs the emulated August denominator, 6/7 vs today's nextpnr). The 7-link "slower than predicted"
  effect reappears for every delay model once the old nextpnr's in-tile under-charge is emulated in the
  denominator, so it is most likely an artefact of the August SDF, not silicon; and with that denominator the F3
  region scatter (0.16) looks double-counted (wire-only fits the shape). Not acted on yet: region 0.16 stays the
  injected scatter (too much scatter only makes GLS stricter); revisit when the per-ring data arrives.
### progress 09:21 (first full-stack failure: BQ#3 seed 9 under 2x within-die scatter)
- BQ#3 scatter draws done: 1x (region 0.16 + wire 0.126) PASS on all 8 seeds; 2x (0.32 + 0.252) PASS on d,3,4,
  5,6,7,8 and **FAIL on seed 9** (sdf 74511ca2, draw 1): vectors 2,3,9,11,13,15 each produce lap 1 with
  "mism=x", OK then ERR 120 ps later, then no further lap in 150 us; errs 6. Bits EQUIVALENT. Not yet known
  whether this is a genuine bundling margin at the 2x tail (the "which margin fails first" PROGRAM asks for) or a
  model artefact (e.g. 1 + 0.32 N clamped at 0 for N < -3.1). Subagent S10 is tracing the X back.
  Until explained, BQ#3's claim is "1x scatter clean on 8 seeds, 2x clean on 7 of 8".
- Draft PR #2 description updated. BQ#1 8-seed full stack queued behind the scatter driver (now starting).
### progress 10:21 (seed 9 at 2x scatter: a GENUINE bundling violation from correlated variation; rules blind to it)
- S10 traced the X (vector 13): ucond_br23..27 steer on select n74_data, the output of fused unit urig.udut.uori2;
  in the draw the request n74_req rose at 449409 ps and n74_data settled at 452494 (request led data by 3085 ps;
  at the five steer pins the select is late by 1646-2940 ps). bd_steer computes req & s with no storage, so the X
  (the select's datapath had not yet computed) enters the C-elements/latches and the handshake stays X. On
  silicon: a token steered on a stale select. Not clamping (one clamped arc, on a VCC-tied pin), not the
  metastability resolver (META_X off), no flops involved. Data-dependent: 6 of 16 vectors.
- Mechanism: region factors are one die map (md5(seed, region), route-independent). Seed 9 placed uori2's matched
  delay (BD_SZ_URIG_UDUT_UORI2 = 19, X34-35 Y21-23, region factor 0.20 at 2x) ~30 slice rows from the comparator's
  CARRY4 chain it tracks (X30-31 Y50-52, factor 1.45). Bisection on the same draw: margin roughly linear in scale;
  1x -1449 ps (safe), 1.3125x -82 ps, 1.375x +195 ps (fails) -> **threshold ~1.33x the calibrated scatter**
  (region sigma ~0.21), i.e. a ~2.8x speed ratio between the two regions. Log-normal factors at 2x: still fails.
- The rules do not see it: rule A gives uori2 +1510 ps after its guard (17th of 50); rule A's tightest line is
  ushli0 (+289 ps) and it did not fail in this draw (why: not determined). None of the rules model correlated
  variation between a chain and a distant datapath.
- Reading: the 2x point (2.8-3.5x region speed ratio on one die) is beyond what the ring data supports, and S9
  suggests even 1x region scatter is double-counted; so BQ#3 stays queued. But it exposes a real robustness
  weakness: **matched delays placed far from the datapath they track.** Next leads: (a) a post-route screen for
  chain/datapath distance (report it, rank by it), (b) place each bd_delay chain next to its datapath (RLOC /
  placement), never shortening it; (c) run every candidate at a fixed set of region draws with log-normal factors
  and report the scale at which it first fails (a margin in units of the calibrated scatter).
### progress 11:30 (BQ#2 full stack 7/16 runs PASS; BQ#3 seed 7 passes 2x)
- BQ#2: d/3/4 at both corners and 5 SLOW_MAX: all PASS 16/16, EQUIVALENT (vec 6 SLOW_MAX 28-32, FAST_MIN 77-86).
- BQ#3 seed 7 at 2x scatter: PASS (59/47/70). Seed 5 scatter running; then BQ#1's sweep.
### progress 12:07 (worker restart; sweeps survived)
- The session's worker restarted (~12:05); the detached sweep drivers survived, S11's background jobs did not
  (asked to resume). BQ#2: 5 FAST_MIN 88/71/102, 6 SLOW_MAX 33/27/39, both PASS (10/16 runs, all PASS).
  BQ#3 seed 5 1x scatter PASS.

## Session 2026-10-29 14:41 -- (in progress) fid resolver: explicit feedback (audit r16 follow_lost fixed); r18 double-ack open
Toolchain: patches 789a7120c912d393, nextpnr 9c732bc6303458df   Seeds: (BQ#2 6,7,8,9 routing)
- Lock 12:07 (2 h 34 min, dead); taken. 4 cores, 15 GB. toolchain.sh ok. Audit read (pass 11a, db195be4): two open
  rows on research files: r16 (FID_RESOLVE "applied late, not lost" REFUTED) and r18 (arb_double_ack CONFIRMED in
  the fid model; research's arbiter tests blind to it; bd_prims_sim.v has no BD_FID path although f3_model.md and
  fid_core.vh say it does -- `git log -S BD_FID` on bd_prims_sim.v is empty, so that path was never committed).
- 055edd7: FID_RESOLVE rewritten so the feedback pin is evaluated from the node's committed state (FB6/FB5 masks
  from gen.py); no echo window, nothing ignored. A drive away from the held value during a resolution ends it.
  tb_f3_follow (new, in run_f3.sh): old resolver loses the 200 ps follow pulse 40/40 (the audit's number), new one
  latches 40/40 (600 and 200 ps) and resolves the 150 ps follow runt both ways (30/10); default model FAILs it.
  All other F3 benches unchanged (tb_f3_meta A 125/75, B 119/81). Not yet re-run on a routed design.
- setup-toolchain.sh now clones prjxray-db 0a0added (zynq7) for xray_delay.py (every session re-cloned it by hand;
  this one lost a first BQ#2 route pass to the missing db).
### progress 15:11 (first routed run of the new resolver OOM-killed; relaunched at 2 sims)
- BQ#2 seeds 6-9 routed (build_hw PASS incl. fasm_audit; xray SDFs made). gen.py finds 4711 LUT state nodes on
  seed 6 (loop delay 125/330/1742 ps). The first full-stack compile under 055edd7 was OOM-killed: iverilog now
  peaks ~5.5 GB (was ~3.7) and each vvp ~3.7 GB (was ~3.1), from the forced-feedback trees on every state node.
  Relaunched with --sim-jobs 2 (seeds_fid docstring updated). No result yet.
- chain_dist.py (7833f62): matched delays vs their datapath on BQ#2 routes: far distance median 14-16, p90 26-35,
  max 51-63 slices; uori2 (the seed-9 BQ#3 bundle) is 16 on seed 6. A screen, gates nothing.
- Literature (a9a409b, meta_sources.md): no 7-series source for TAU/WIN, TAU_FF, aperture, CK MPW or LUT pulse
  rejection. Measured flop tau 35-75 ps at 130-65 nm puts TAU_FF 75 at the slow (pessimistic) end. A datasheet
  CK minimum pulse width (~0.5 ns, unconfirmed) would make 70-500 ps CK runts spec violations; not acted on.
- Running: S12 (arbiter near-tie double-ack under the new resolver + gcd_hw grant->A0 round trips); BQ#3 8 reroutes.
### progress 15:25 (audit r18 answered with data: model requirement derived, gcd_hw's arbiters clear it)
- 089d00e + 7d21f37 (S12): bd_arbiter near tie re-measured under the 055edd7 resolver (tb_f3_arbtie, own bench
  built the gen.py way). Double acks persist, rarer: TLOOP 424 S=600 303/9200 (r18 old resolver 1097/10440),
  clean from S=1095 (was 1200); TLOOP 200 clean from 915 (was 1000). Grants never overlap. Requirement derived
  and checked: RT + a >= trp_max + GP + c - skew (predicts 1088/909 vs measured 1080-1095/905-915), so
  bd_arb.v's "one loop delay" consumer obligation is NOT sufficient in the model. The hold-release race
  (re-request at A0-fall) gives the same failure and the same threshold.
  On BQ#2 seed 6 (prjxray FAST_MIN; static lower bounds; arb_roundtrip.py / arb_holdreach.py): all 18 ack
  C-elements of the 9 arbiters clear it, worst margin 878 ps (merge9.uarb1); re-requests clear the hold window
  by >= 399 ps. --naive negative control flags 3. run_f3.sh +3 arms, rc 0.
  Reading for r18: the mechanism is real in the model and silicon-plausible; its cutoff rests on the assumed
  TAU (878 ps ~ 5.9 TAU); gcd_hw is not exposed on this route. bd_arb.v's comment is now known to understate
  the obligation; cells/rtl is frozen, so the correction lives in arbtie.md (no RTL change: the cell is fine,
  the comment's rule is too weak).
- BQ#2 seeds 6/7 SLOW_MAX under the new resolver: vectors 0-1 PASS so far (seed 6 laps 3070/1907); ~3.5 min per
  vector, 8 sims at 2 at a time, ~4 h. BQ#3 8 reroutes in progress (for the same re-run).
### progress 16:12 (BQ#3 rerouted, md5 reproduced; arbiter check on 12 routes; chain distance alone does not predict)
- BQ#3 8 seeds rerouted (all build_hw PASS; default sdf 61e14755 = the record). arb_roundtrip: 0/18 below the
  arbiter requirement on all 8 (worst 691 ps, seed d; BQ#2 worst 878).
- chain_dist on the 8 BQ#3 routes: far median 11-18, p90 27-43. Seed 9's uori2 (the 2x-scatter failure) is 33,
  the largest uori2 of the 8 seeds, with the traced bbox X34-35 Y21-23, but only 7th on its own route: six
  farther chains survived the same draw. Distance alone does not rank failures; next: weight by rule A's margin
  and datapath delay (the exposure is margin / (delay x regional speed difference)).
- BQ#2 seeds 6, 7 SLOW_MAX: 13/16 vectors done each, all completed with errs 0 so far.
### progress 16:43 (first routed results under the 055edd7 resolver: unchanged)
- BQ#2 full stack, SLOW_MAX, new resolver: seed 6 PASS 16/16 errs 0 laps 33/27/39 (EQUIVALENT) -- identical
  to last session's old-resolver row (33/27/39); seed 7 PASS 16/16 laps 31/25/36. FAST_MIN and seeds 8/9 running,
  then BQ#3 x8 x2 corners on the new resolver.
- S13 started: region/wire scatter applied to the nextpnr-named SDF, then rule A, as a static predictor of the
  seed-9 2x-scatter failure (rule A was blind to it on the unscaled SDF: uori2 +1510 ps).
### progress 19:46 (BQ#2 seeds 6, 7 both corners PASS under the new resolver)
| BQ#2 full stack, 055edd7 resolver | sdf | xray sdf | verdict | laps v6/v12/v13 |
|---|---|---|---|---|
| seed 6 SLOW_MAX | c4ec8664 | 1f7f03ea | PASS 16/16 errs 0, EQUIVALENT | 33/27/39 |
| seed 6 FAST_MIN | c4ec8664 | 1f7f03ea | PASS 16/16 errs 0, EQUIVALENT | 93/76/109 |
| seed 7 SLOW_MAX | ae90c9ef | 042034d2 | PASS 16/16 errs 0, EQUIVALENT | 31/25/36 |
| seed 7 FAST_MIN | ae90c9ef | 042034d2 | PASS 16/16 errs 0, EQUIVALENT | 86/69/100 |
FAST_MIN sims take ~2 h each (vs ~1 h SLOW_MAX). Seeds 8, 9 next, then BQ#3 x8 x2 corners.
### progress 19:47 (NEGATIVE: rule A on a scatter-scaled SDF does not predict the GLS failure)
- S13 (research/tools/scatter_ruleA/, data scatter_ruleA_seed9_mc.txt): scale_sdf.py imports gen.py and reproduces
  its scatter factors exactly (draw 1, 2x: 44567/44567 IOPATH, 50148/50148 INTERCONNECT identical to the GLS's
  annot.sdf), maps them to nextpnr names, and tighten.py (rule A) runs on the scaled xray-band SDF.
  On BQ#3 seed 9, draw 1, uori2 is the worst rule-A cell and the mechanism matches the GLS (chain 7839 -> 1549 ps,
  data 5234 -> 5764). But rule A's zero crossing is ~0.74x guarded / ~0.97x raw against the GLS's 1.31-1.38x
  (same slope, ~1.3 ns pessimistic offset). Across BQ#3 seeds, draw 1: rule A flags 6/8 routes at 1x (GLS passes
  all 8) and 8/8 at 2x (GLS fails only seed 9); seed 9's raw -3976 overlaps passing seeds 3 and 4. Monte Carlo on
  seed 9: 34/38 draws negative at 1x. Verdict: correct factors, unusable predictor; rule A's one-sided worst case
  cannot separate fail from pass under correlated variation. Rule A stays a proposer, not a judge. Only the GLS
  can rank these draws.
### progress 21:48 (BQ#2 SLOW_MAX on seeds 6-9 all PASS under the new resolver)
- BQ#2 seed 8 SLOW_MAX PASS 16/16 laps 31/25/37 (sdf b7733e23); seed 9 SLOW_MAX PASS 16/16 laps 31/25/36
  (sdf 4a9b218e); both EQUIVALENT. Seeds 8, 9 FAST_MIN running, then BQ#3.
### progress 23:19 (owner's PROGRAM change ea7dafa read and followed)
- Owner commit ea7dafa (one session a day; the "use far more parallelism"/"most subagents" text removed) landed
  mid-session; my lock push was rejected as non-fast-forward, the remote LOCK was still this session's, so it was
  rebased on top, not a lock conflict. From here: the main thread stays on the full-stack GLS, no new subagents
  unless a lead needs one; background sims keep the machine busy.
- BQ#2 seed 8 FAST_MIN PASS 16/16 laps 87/70/102. Seed 9 FAST_MIN 12/16 vectors, then BQ#3.
### progress 23:56 (BQ#2 full stack complete: 8 seeds x 2 corners PASS)
- BQ#2 seed 9 FAST_MIN PASS 16/16 laps 86/69/100. With last session's d,3,4,5 (old resolver): BQ#2 passes the full
  stack on 8 seeds at both corners (16/16 runs). BOARD-QUEUE #2 updated; data bq2_fullstack_s6-9.tsv.
- The chain now runs BQ#3 x8 x2 corners on the new resolver (~1.5 h per pair of sims, ~12 h).
### progress 01:57 (BQ#3 on the new resolver: first rows identical to the old)
- BQ#3 d SLOW_MAX PASS 33/27/39 (sdf 61e14755); seed 4 SLOW_MAX PASS 31/24/36 (sdf a0d20c19, xray e9bb3663) --
  both identical to the old-resolver rows of bq3_fullstack_8seed.tsv. So far the 055edd7 resolver changes no
  gcd_hw result (6 of 6 comparable runs identical or new passes).
### progress 03:38 (worker restart; detached chain survived)
- The session worker restarted (~03:35); the detached sim chain survived. BQ#3 new-resolver rows so far: d max
  33/27/39, d min 91/75/108, 3 max 32/26/38, 4 max 31/24/36 -- all PASS 16/16, EQUIVALENT, all identical to the
  old-resolver rows.
### progress 14:28 (BQ#3 seed-9 2x-scatter failure reproduces on the new resolver)
- BQ#3 seed 9, band 0.38, region 0.32 + wire 0.252, draw 1, resolver 055edd7: FAIL, errs 6, the same six vectors
  (2,3,9,11,13,15: one lap with an error, then stall) as on the old resolver; bits EQUIVALENT. The failure is the
  uori2 bundling violation, not a resolver artefact. BQ#3 new-resolver sweep: 15/16 corner runs PASS so far,
  all identical to the old rows (seed 9 FAST_MIN running).
### progress 15:18 (BQ#3 full stack on the new resolver: 16/16 corner runs PASS, all identical)
| BQ#3 full stack, resolver 055edd7 | n | pass | vec 6 laps mean (range) | vs old resolver |
|---|---|---|---|---|
| SLOW_MAX | 8 (d,3-9) | 8 | 32.75 (31-34) | identical per seed |
| FAST_MIN | 8 | 8 | 89.6 (83-94) | identical per seed |
| 2x scatter, seed 9 draw 1 | 1 | 0 | 53 (vec 13: 1) | same failure, same 6 vectors |
Reading: the resolver fix (audit r16) changes no gcd_hw result on 20 comparable runs (BQ#2 + BQ#3); resolver
events evidently never land in the follow-pulse case on these routes. BOARD-QUEUE #3 updated. Data:
research/data/fid/bq3_fullstack_newresolver.tsv. Running: BQ#2 within-die scatter 1x and 2x, draw 1, seeds 6-9.
### progress 16:34 (BQ#2 within-die scatter: first rows pass; worker restart, drivers survived)
- BQ#2 band 0.38 + scatter, draw 1, new resolver: seed 6 1x (0.16/0.126) PASS 16/16 laps 51/42/61; seed 8 2x
  (0.32/0.252) PASS 16/16 laps 46/36/53. Remaining seeds running (two serial drivers).
### progress 17:46 (second full-stack failure: BQ#2 seed 6 at 2x scatter; suspect uori3, same mechanism)
- BQ#2 seed 6, band 0.38 + region 0.32 / wire 0.252, draw 1 (new resolver): FAIL errs 3, vectors 7, 8, 12 (one lap
  with mism=x, then stall); bits EQUIVALENT. Same signature as BQ#3 seed 9's uori2 failure (same draw 1).
- Suspect: urig.udut.uori3. Rule A on this draw's exactly scaled SDF (research/tools/scatter_ruleA) puts uori3 at
  -3325 ps, far below the next cell (ushrsi0 -1306); uori3's chain (X12-13 Y53-55) is in region (1,5), factor
  0.49 at 2x, its datapath (X0-5 Y56-76) in regions (0,5)/(0,6) at 1.56/1.54: a ~3.1x speed ratio. chain_dist had
  it at 28 slices on this route. Running: vectors 12/7/8 with uori3's 20 chain LUTs scaled x2.03 (undoing the
  region factor) -- if they pass, uori3 is the cause.
- BQ#2 1x draw 1: seeds 6, 7 PASS (51/42/61, 53/42/61). 2x draw 1: seed 8 PASS (46/36/53), seed 6 FAIL.
- gen.py quirk found: under GLS_SCATTER_ONLY, a non-matching cell ARC drops its region factor (perturb) but a
  non-matching INTERCONNECT arc keeps it (wire path), so SCATTER_ONLY does not isolate region effects. Not fixed
  yet (no result depends on it: SCATTER_ONLY was only used without region scatter).
### progress 18:13 (BQ#2 seed-6 2x failure CONFIRMED as uori3's chain/datapath region split)
- Intervention on the failing draw (GLS_SCALE_INST on uori3's 20 chain LUTs x2.03 = 1/0.492, cell arcs AND
  interconnect, which needed 9c39512): vectors 12, 7, 8 PASS 39/175/146 laps, errs 0 (unfixed: 1 lap, errs 1 each;
  the first attempt before 9c39512 scaled only the 120 cell arcs and still failed). Only that chain's speed was
  changed, so uori3 is the cause.
- Two genuine full-stack failures now, both fused "ori" compute units (uori2 on BQ#3 seed 9, uori3 on BQ#2 seed 6),
  both at 2x region scatter with draw 1, both a ~3x speed ratio between a matched chain and its datapath 20-30
  slices away. Neither recipe fails at 1x. Lead (b) from 2026-10-29 now has two data points: keep each matched
  chain inside its datapath's region (placement), never shorten it.
### progress 18:21 (chain-region placement prototype: routes, rule A clean, chains closer)
- BD_CHAIN_REGIONS (cells/hw/chain_regions.py + chain_regions_preplace.py) on BQ#2 seed 6: rectangles of
  +-2 cols / +-3 rows did not legalize (ucmpi1's chain); +-4 / +-6 routes. Iterated from the previous pass's route:
  | BQ#2 seed 6 | chain-to-datapath centroid distance, mean / max (slices) | chains > 15 slices off |
  |---|---|---|
  | unconstrained (sdf c4ec8664) | 12.9 / 49.1 | 16/50 |
  | pass 2 (regions from unconstrained) | 9.8 / 37.8 | 9/50 |
  | pass 3 (regions from pass 2; file research/data/fid/chain_regions/) | 9.0 / 25.9 | 11/50 |
  Rule A on pass 2: 46 cells, none negative, worst +1055 (unconstrained worst +914); rule D screen lines unchanged
  (38). build_hw + fasm_audit PASS on both. One seed only.
- Queued (after the BQ#2 scatter drivers): pass-3 route full stack at both corners + 2x draws 1-3, and the
  unconstrained seed-6 route at 2x draws 2-3, i.e. does the constraint remove 2x failures. Not yet a claim.
- BQ#2 scatter so far: 1x PASS seeds 6, 7; 2x PASS seed 8, FAIL seed 6 (uori3, confirmed).
### progress 19:01 (BQ#2 scatter: 2x seed 7 PASS; seed 9 2x OOM-killed, requeued)
- BQ#2 2x draw 1: seed 7 PASS 16/16 laps 54/42/63; seed 8 1x PASS 49/39/57. Seed 9's 2x compile was OOM-killed
  (my side builds overlapped two sims; INCOMPLETE, never a pass) and is requeued after the chain-region GLS.
  Lesson repeated: one compile (5.5 GB) + two vvp (3.7 GB each) is the ceiling on 15 GB; side jobs must wait.
### progress 20:04 (BQ#2 1x scatter 4/4 PASS; chain-region route SLOW_MAX PASS)
- BQ#2 1x (region 0.16 + wire 0.126) draw 1: PASS on seeds 6, 7, 8, 9 (vec 6 laps 51/53/49/50).
- Chain-region route (BQ#2 seed 6 pass 3, sdf d5cc5f09 reproduces the pass-3 build): SLOW_MAX PASS 16/16 laps
  31/25/37 (unconstrained 33/27/39, -6% on vec 6; one seed).
### progress 20:38 (NEGATIVE: chain-only regions do not fix the 2x failure -- the datapath moves)
- Chain-region route (BQ#2 seed 6 pass 3, sdf d5cc5f09): corners PASS (SLOW_MAX 31/25/37, FAST_MIN 85/69/100;
  unconstrained 33/27/39 and 93/76/109), but 2x draw 1 FAILS (errs 4: vectors 2, 3, 9, 15, uori2's signature from
  BQ#3 seed 9). Rule A on this draw's exactly scaled SDF: uori2 -804, ushli0 -165, rest positive.
- Why: the regions are computed from the previous pass's datapath position, and the datapath moves on the next
  pass. On pass 3, uori3's chain is again 32 slices from its datapath (X8-9 Y55-57 vs X0-5 Y67-81). Iterating
  does not converge (centroid distance 12.9 -> 9.8 -> 9.0 mean, but per unit it jumps around).
- Next: constrain each compute unit's chain AND datapath to one rectangle (a per-unit region), so co-location
  holds by construction; check legality, rule A, corners, then the 2x draws.
### progress 20:41 (placement lead parked: per-unit regions do not legalize in this nextpnr)
- chain_regions.py --unit (chain + datapath + control of each compute unit in one rectangle, ~2x the slices it
  needs) on BQ#2 seed 6: three tries, all "Unable to find legal placement" on a CARRY4 (uselect1, then uori2 with
  the rectangle >= CARRY4 count + 2 tall, then uselect1 again with every CARRY4 left unconstrained -- the LUTs
  packed into a carry cluster still constrain it). Chain-only regions legalize but do not converge (above).
- Parked. What it would take: in the pre-place script, skip every cell of a carry cluster (needs the cluster
  parent from the Python API, not probed yet) or a nextpnr patch that pulls a bd_delay chain toward the centroid
  of a named cell set (soft, like the place-weight patch). Not worth it while the only failures are at 2x the
  calibrated scatter, which S9 suggests is already double-counted at 1x.
### progress 21:43 (chain-region route fails 2x draw 2 as well)
- Chain-region route (BQ#2 s6 pass 3), 2x draw 2: FAIL errs 2 (laps 50/40/60). With draw 1's FAIL, 0/2 2x draws
  pass on this route; the unconstrained route's draws 2 and 3 are next for the comparison.
