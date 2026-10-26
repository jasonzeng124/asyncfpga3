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
