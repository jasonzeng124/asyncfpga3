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
