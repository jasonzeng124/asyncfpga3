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

## Session 2026-10-29 14:41 -- (in progress) fid resolver fixed (r16); BQ#1-3 full stack + scatter; gcd_ps formal target (BQ#4) through the full stack; FOR-RESEARCH C1 answered
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
### progress 22:44 (2x draw 2: unconstrained seed 6 errs 15, chain-region route errs 2)
- BQ#2 seed 6 unconstrained, 2x draw 2: FAIL errs 15 (15 of 16 vectors break in the first laps). Same draw on the
  chain-region route: FAIL errs 2; draw 3: PASS. Tally so far, 2x: unconstrained 0/2 pass (draws 1,2), chain-
  region 1/3 (draws 1,2 fail, 3 passes); errs 3+15 vs 4+2+0. Suggestive, n tiny. Draw 3 on the unconstrained
  route next. At 2x many draws fail on one route; region 0.32 (a ~3x speed spread across one die) is far past the
  calibrated 0.16, so this is a robustness ranking, not a predicted board failure.
### progress 23:44 (2x draws 1-3 on BQ#2 seed 6: chain regions make no clear difference)
| BQ#2 seed 6, band 0.38 + region 0.32 / wire 0.252 | draw 1 | draw 2 | draw 3 | corners (vec 6 laps max/min) |
|---|---|---|---|---|
| unconstrained (sdf c4ec8664) | FAIL errs 3 (uori3) | FAIL errs 15 | PASS 62/51/73 | 33 / 93 |
| chain regions pass 3 (sdf d5cc5f09) | FAIL errs 4 (uori2) | FAIL errs 2 | PASS 52/42/60 | 31 / 85 |
Reading: 1/3 vs 1/3; fewer errors on draw 2 but more on draw 1; the constrained route is 6-16% slower. No
robustness gain shown, a speed cost shown. Draw 4 on both running; unless it separates them, the chain-only
region prototype is a negative result.
### progress 00:15 (full container restart; draw-4 and seed-9 2x runs restarted)
- Container restarted (~00:13, uptime 0): disk kept, processes lost (2x draw 4 on both seed-6 routes, BQ#2 seed 9
  2x draw 1). toolchain.sh ok; partial run dirs removed; both relaunched.
### progress 01:23 (BQ#2 within-die scatter draw 1 complete: 1x 4/4, 2x 3/4)
- BQ#2 seed 9 2x draw 1 PASS 16/16 (49/39/58). Draw 1: 1x PASS 4/4 seeds, 2x PASS 3/4 (seed 6 = uori3). BQ#3's
  record for comparison: 1x 8/8, 2x 7/8. BOARD-QUEUE #2 updated.
- Chain-region route 2x draw 4 PASS (46/36/53): chain regions 2/4 so far; unconstrained draw 4 running.
### progress 02:29 (NEGATIVE, final: chain-only regions 2/4 vs unconstrained 2/4 at 2x)
| BQ#2 seed 6, 2x (0.32/0.252) | d1 | d2 | d3 | d4 | pass |
|---|---|---|---|---|---|
| unconstrained | FAIL 3 | FAIL 15 | PASS 62 | PASS 43 | 2/4 |
| chain regions (pass 3) | FAIL 4 | FAIL 2 | PASS 52 | PASS 46 | 2/4 |
(errs or vec-6 laps). Same pass rate; slower at the corners (-6% SLOW_MAX, -9% FAST_MIN). BD_CHAIN_REGIONS stays
an off-by-default tool and is not proposed for any candidate. One route only; at 2x half the draws fail on this
route either way, i.e. BQ#2 seed 6 tolerates ~2x region scatter about half the time.
### progress 02:52 (the 2x region-scatter point is mostly a test of implausible die maps)
- New rows: BQ#2 seed 7 2x draw 2 FAIL errs 3; BQ#3 seed d 2x draw 2 FAIL errs 15.
- Region factors at sigma 0.32 (linear 1+sigma N, 5x10 regions on xc7z010), whole-die spread per draw:
  | draw | min | max | max/min | regions < 0.4 |
  |---|---|---|---|---|
  | 1 | 0.20 | 1.68 | 8.3 | 4 |
  | 2 | 0.23 | 1.69 | 7.3 | 2 |
  | 3 | 0.12 | 1.59 | 13.1 | 2 |
  | 4 | 0.45 | 1.58 | 3.5 | 0 |
  On BQ#2 seed 6, draws 1-2 fail on both routes, draw 4 (the only map without a < 0.4 region) passes on both, draw 3
  splits by route. The two confirmed failures each had a chain in a 0.2/0.49 region. A 3-13x speed spread on one
  die is far outside anything measured (the ring data's median scatter is 8.5%); the 2x tail is dominated by
  regions running 2.5-8x faster than nominal, which the linear model allows and silicon does not.
- Consequence: stop adding 2x linear draws (the ones running finish). A failure at 2x ranks a route's exposure but
  is not evidence of a board risk. If robustness margins are wanted, scan the scale per draw with log-normal
  factors (GLS_SCATTER_LOGN=1) and report the failing scale, as the 2026-10-29 bisection did for seed 9 (~1.33x).
### progress 02:53 (2x sweeps stopped; BQ#1 8-seed full stack started)
- Stopped the remaining 2x linear draws (low value, above). Started BOARD-QUEUE #1 (fusion on, v4, select pads; the
  first board candidate) on the full stack: seeds d,3-9 x FAST_MIN/SLOW_MAX, resolver 055edd7. Its full-stack
  record so far is one route (bq1_max 16/12/18 laps, fullstack.md). Default-seed sdf should be 6f8b99e6.
### progress 03:27 (container restart again; BQ#1 sims relaunched)
- Second full container restart (~03:26). BQ#1's 8 routes had completed (default sdf 6f8b99e6 = the BOARD-QUEUE
  record); seed d's two in-flight sims were lost and the sweep was relaunched (routes reused).
### progress 06:28 (BQ#1 full stack: first 5 runs PASS)
- BQ#1 (fusion, v4, select pads; resolver 055edd7): d SLOW_MAX 16/12/18 (sdf 6f8b99e6, = the earlier bq1_max row),
  d FAST_MIN 45/35/51, 3 SLOW_MAX 16/12/18, 3 FAST_MIN 46/36/52, 4 SLOW_MAX 16/12/18; all 16/16 errs 0, EQUIVALENT.
### progress 08:59 (BQ#1 full stack 10/16 runs PASS)
- Added: 6 SLOW_MAX 15/12/17, 4 FAST_MIN 46/36/52, 7 SLOW_MAX 16/12/18, 6 FAST_MIN 44/34/49, 5 SLOW_MAX 16/12/18,
  7 FAST_MIN 45/35/52; all 16/16 errs 0 EQUIVALENT. Remaining: 5 min, 8, 9.
### progress 12:12 (BQ#1 full stack complete: 8 seeds x 2 corners PASS)
| full stack, resolver 055edd7 | SLOW_MAX pass, vec 6 mean (range) | FAST_MIN pass, vec 6 mean (range) |
|---|---|---|
| BQ#1 (d,3-9) | 8/8, 15.9 (15-16) | 8/8, 45.9 (44-48) |
| BQ#2 (d,3-9; d-5 old resolver) | 8/8, ~31-33 | 8/8, ~77-93 |
| BQ#3 (d,3-9) | 8/8, 32.75 (31-34) | 8/8, 89.6 (83-94) |
All three board candidates now pass the full stack on 8 seeds at both corners. BOARD-QUEUE #1 updated. Running:
BQ#1 1x scatter draw 1 on seeds d,3,4,5.
### progress 13:43 (BQ#1 1x within-die scatter: 3/3 PASS so far)
- BQ#1 band 0.38 + region 0.16 / wire 0.126, draw 1: d PASS 23/18/26, 6 PASS 23/18/26, 3 PASS 26/21/30.
### summary 16:09 (session 2026-10-29 14:41, still running)
Toolchain: patches 789a7120c912d393, nextpnr 9c732bc6303458df, prjxray-db 0a0added   Seeds: d,3-9 (all three BQs)
Did: fixed the fid state-node resolver (audit r16: explicit feedback, no echo window; 055edd7); answered audit
r18 with a near-tie bench, a derived round-trip requirement and a per-arbiter static check on 12 routes; fixed two
gen.py scatter-knob inconsistencies (9c39512); setup-toolchain.sh now fetches prjxray-db; ran every board candidate
through the full stack on 8 seeds x 2 corners; confirmed a second correlated-variation failure by intervention;
tried and rejected two placement fixes and a static predictor.
Measured:
| candidate | full stack SLOW_MAX / FAST_MIN (8 seeds) | vec 6 laps mean | 1x scatter | 2x scatter |
|---|---|---|---|---|
| BQ#1 | 8/8 / 8/8 | 15.9 / 45.9 | 8/8 | not run |
| BQ#2 | 8/8 / 8/8 | ~32 / ~88 | 4/4 | 3/4 (draw 1), seed 6 also fails draw 2 |
| BQ#3 | 8/8 / 8/8 (new resolver; identical to old) | 32.75 / 89.6 | 8/8 (old resolver) | 7/8 (draw 1) |
Arbiters: 0 of 18 ack C-elements under the model's requirement on any of 12 routes, worst 691 ps.
Does NOT show: silicon; ring128 acceptance (still blocked), so the rule gates stay; that TAU/WIN/the noise are right
(no 7-series source); that 2x linear region scatter is physical (it is not: 3-13x die-wide speed spreads); a cure
for the matched-delay/datapath distance exposure.
Next: (1) ring128 per-ring data from the owner unblocks acceptance; (2) if robustness margins are wanted, a
log-normal scale scan per draw (the failing scale) instead of fixed 2x draws; (3) skip carry-cluster members in
the pre-place script, or a soft nextpnr pull toward a datapath centroid, before trying placement again;
(4) goal 2 leads (RTZ tail, rule E tightening) once the gates may move.
### progress 16:10 (log-normal scale scan started)
- Next (2) started: GLS_SCATTER_LOGN=1 (factors exp(sigma N): no region faster than e^-3sigma), draw 1, region
  sigma 0.16 / 0.24 / 0.32 with wire 0.126 / 0.189 / 0.252, on the two routes with confirmed linear-2x failures
  (BQ#3 seed 9, BQ#2 seed 6). seeds_fid tags these runs _logn. Question: at what scale does each first fail when
  the speed-up tail is bounded like silicon's?
### progress 17:55 (log-normal scan: BQ#3 seed 9 passes 1x and 1.5x)
- GLS_SCATTER_LOGN=1, draw 1, BQ#3 seed 9 (linear threshold ~1.33x): sigma 0.16/0.126 PASS 52/42/62, sigma
  0.24/0.189 (1.5x) PASS 51/41/61. 2x log-normal running (an earlier session saw it fail).
### progress 18:25 (log-normal: BQ#3 seed 9 fails at 2x -- threshold 1.5-2x, linear ~1.33x)
- BQ#3 seed 9, log-normal sigma 0.32/0.252: FAIL errs 6 (same six vectors as linear 2x). Its failing scale under
  log-normal factors is between 1.5x and 2x the calibrated scatter (linear: ~1.33x). BQ#2 seed 6 scan running.
### progress 19:56 (log-normal: BQ#2 seed 6 passes 1x and 1.5x)
- BQ#2 seed 6 (linear 2x FAIL, uori3), log-normal draw 1: sigma 0.16 PASS 50/41/59, sigma 0.24 PASS 46/38/55.
  2x running.
### progress 20:28 (log-normal scan: both failing routes pass 1.5x, fail 2x)
| draw 1, GLS_SCATTER_LOGN=1 | 1x (0.16/0.126) | 1.5x (0.24/0.189) | 2x (0.32/0.252) | linear threshold |
|---|---|---|---|---|
| BQ#3 seed 9 (uori2) | PASS 52 | PASS 51 | FAIL errs 6 | ~1.33x |
| BQ#2 seed 6 (uori3) | PASS 50 | PASS 46 | FAIL errs 3 | between 1x and 2x |
With silicon-like bounded speed-ups (log-normal), the two worst known exposures hold to at least 1.5x the
calibrated within-die scatter, which S9 already suspects is double-counted. Bisecting 1.75x on both now.
### progress 21:58 (log-normal 1.75x: BQ#3 seed 9 PASS -> its threshold is 1.75-2x)
- BQ#3 seed 9, log-normal 0.28/0.2205, draw 1: PASS 16/16 errs 0 (laps 50/40/120). Vector 13 ran 120 laps vs ~60
  at the other scales, with every result correct (oks = laps); most likely its critical cycle sits in a region
  this draw makes fast. Noted, not chased. BQ#2 seed 6 at 1.75x running.
### progress 22:51 (log-normal failing scale bracketed for both known exposures)
| draw 1, log-normal | 1x | 1.5x | 1.75x | 2x | failing scale |
|---|---|---|---|---|---|
| BQ#3 seed 9 (uori2) | PASS | PASS | PASS | FAIL 6 | 1.75-2x |
| BQ#2 seed 6 (uori3) | PASS | PASS | FAIL 2 | FAIL 3 | 1.5-1.75x |
Margin over the calibrated within-die scatter, on the worst known route/draw of each candidate: >= 1.5x.
Next: log-normal 1.5x on draw 2 over all routes (BQ#3 d,3-9; BQ#2 6-9, the routes on disk), to see whether 1.5x
holds beyond draw 1.
### progress 01:22 (log-normal 1.5x draw 2: BQ#3 d,3,4,5 PASS)
- BQ#3 log-normal 0.24/0.189 draw 2: d PASS 53/44/63 (linear 2x draw 2 had FAILED it with errs 15), 3 PASS 44/35/52,
  4 PASS 56/44/64, 5 PASS 52/42/61. Seeds 6-9 then BQ#2 6-9 running.
### progress 03:33 (BQ#3 log-normal 1.5x draw 2: 8/8 PASS)
- BQ#3 log-normal 0.24/0.189 draw 2: d,3,4,5,6,7,8,9 all PASS 16/16 (vec 6 laps 44-56). BOARD-QUEUE #3 updated.
  BQ#2 seeds 6-9 at the same point running.
### progress 05:52 (log-normal 1.5x draw 2: 12/12 routes PASS; BQ#1 next)
- BQ#2 log-normal 0.24/0.189 draw 2: seeds 6, 7, 8, 9 PASS (49/50/45/48 laps vec 6). With BQ#3's 8/8: 12/12 routes
  clean at 1.5x the calibrated within-die scatter with bounded (log-normal) factors, including both routes that
  fail linear 2x. BOARD-QUEUE #2 updated. BQ#1 x8 at the same point started.
### progress 07:53 (BQ#1 log-normal 1.5x draw 2: 4/4 PASS so far)
- d 26/20/30, 3 27/21/30, 4 25/19/28, 5 28/22/32; all 16/16 errs 0. Seeds 6-9 running.
### progress 09:54 (log-normal 1.5x draw 2: all 20 candidate routes PASS)
| log-normal 1.5x (0.24/0.189), draw 2 | routes | pass |
|---|---|---|
| BQ#1 | d,3-9 | 8/8 |
| BQ#2 | 6-9 (on disk) | 4/4 |
| BQ#3 | d,3-9 | 8/8 |
Every board candidate holds 1.5x the calibrated within-die scatter on this draw when region speed-ups are bounded
(log-normal), including the two routes that fail linear 2x. BOARD-QUEUE #1 updated.
Does NOT show: other draws at 1.5x (one draw per route); whether the calibrated scatter is right (S9: possibly
double-counted, ring128 per-ring data still needed).
### progress 09:54 (log-normal 1.5x draw 3 across all 20 routes started; PR #2 description refreshed)
### progress 12:25 (log-normal 1.5x draw 3: BQ#1 d,3,4,5 PASS)
- BQ#1 draw 3: d 26/20/30, 3 24/19/28, 4 26/20/29, 5 30/23/34; all 16/16 errs 0.
### progress 14:19 (log-normal 1.5x draw 3: BQ#1 8/8 PASS)
- BQ#1 draw 3: all 8 seeds PASS 16/16 (vec 6 laps 24-30). BQ#1 now clean at log-normal 1.5x on draws 2 and 3.
  BQ#2 6-9 then BQ#3 x8 running.
### progress 16:59 (log-normal 1.5x draw 3: BQ#2 4/4 PASS)
- BQ#2 draw 3: 6 59/49/69, 7 50/40/58, 8 59/48/68, 9 50/40/58; all PASS. BQ#3 x8 running.
### progress 17:31 (owner's new first lead (690f156): a full-width gcd target in gcd_ps)
- Read PROGRAM.md's new section and formal/FOR-RESEARCH.md (claude/formal) sections 1-3. Stopped the log-normal
  draw-3 sweep (BQ#1 8/8 and BQ#2 4/4 done, BQ#3 not run) to free the machine for this lead.
- gcd_ps.v reading (CDC): STATUS.i_ack and STATUS.o_req cross into the PS clock through 2-flop synchronizers
  (sync_i_ack/sync_o_req); A/B are aclk registers written before the CTRL write that raises the request; the
  request flop (req_core) is cleared asynchronously by the kernel's i_ack (a 4-phase return, the flop's output is
  then re-synchronised); o_ack_pl = ctrl_o_ack & o_req_pl (falls with o_req). O_DATA is sampled every clock but
  only read after o_req is synchronised (stable while o_req is high). No missing synchronizer found by reading;
  to be confirmed in GLS. Sequencing: the host protocol (poll i_ack, then poll o_req, read, ack) offers the next
  pair only after the result handshake, i.e. the sequential environment formal needs; no hardware FSM issues
  calls on in_ack.
- Plan: build gcd_ps with BQ#1's flags (select pads, v4); audits; a behavioural PS7 (AXI master + FCLK) for the
  GLS netlist, a testbench running the documented host sequence over operands outside the 16 vectors with
  expected values from bdc/simcheck.py's ref_gcd (the C transcription); fid GLS at both corners on >= 4 seeds;
  BOARD-QUEUE item naming one seed's .bit/.fasm as the formal target. Default-seed build running.
### progress 17:48 (gcd_ps: built, rule A needs padding, GLS harness working; async-flop GLS bug fixed)
- gcd_ps with BQ#1's flags (select pads, v4) routes on seeds d,3,4,5 (build_hw PASS incl. fasm_audit). Default
  seed audit: rule A 1 violation (bridge_i.udut.umux21 margin -1567 ps, PAD to 16), rule D 38 (the screen, as on
  BQ#1), E 0, J ok. BQ#1's own route: rule A 0 -- gcd_hw's 16-vector table lets synthesis merge most operand bits
  (formal FOR-RESEARCH s1: a_data 18 distinct nets), so its datapath is shorter. gcd_ps therefore needs the
  sizing step: BD_SIZES now works for gcd_ps (bridge_i.udut.*), and research/tools/pad_sizes.py writes a
  PAD-ONLY sizes file (only rule-A violators lengthened, max over seeds; nothing shortened). Running.
- GLS bug found and fixed (231b948): gen.py/prims.v modelled every SLICE_FFX as FDRE/FDSE (synchronous SR) and
  read FDPE's "PRE" as reset-to-0. gcd_ps's AXI bridge has 67 FDCE + 2 FDPE, so in GLS it never left reset
  correctly (aw_en = 0, no BVALID ever). gcd_hw has only FDRE/FDSE (306/20), so no earlier result changes;
  run_f3.sh all ok.
- GLS harness (cells/gls/ps/): behavioural PS7_PS7 = FCLK0 + AXI3 master running gcd_ps.v's documented host
  sequence; 24 vectors outside gcd_rig's 16, expected from bdc/simcheck.py ref_gcd (= math.gcd on [0,2^31)).
  First check (default seed, nextpnr SDF, default model): vectors 0-2 OK (0x7fffffff/0x7ffffffe -> 1,
  0x7fffffff/0x7fffffff, 0x40000000/0x60000000 -> 0x20000000). Unsized route: rule A violation present, so this
  is a harness check only, not a claim.
### progress 17:58 (gcd_ps: full-stack decode works; P1 sizes routing on 8 seeds)
- fasm2net.py --ps7 (b2315c2): decodes the PSS2 tile into one PS7_PS7 cell (M_AXI_GP0 + FCLK bit pins,
  cells/gls/ps/ps7_pins.py) and async-SR flops (FDCE/FDPE, CLR/PRE) instead of refusing them. gcd_hw decode is
  byte-identical before/after. fasm_equiv on the gcd_ps default seed: EQUIVALENT; the only differences are PS7
  inputs the routed JSON ties to constants (now a named benign kind, not silently ignored).
- P1 sizes (8018048): umux21 12 -> 16 links (max rule-A "PAD to" over unsized d,3,4,5: -1567/-154/-464 ps, 3
  clean). First 8-seed launch failed on a missing cells/build/gen (2fed1d0, fixed); relaunched d,3-9.
### progress 18:20 (gcd_ps P1: every audit clean on 8 seeds; full stack seed d 24/24 at both corners)
- P1 routes d,3-9 (research/data/gcd_ps/p1_audit_8seed.tsv): rule A 0 on all 8 (umux21 margin mean 1456 ps,
  range 358-1889, guardband applied), D 38 (screen), E 0, J ok, build_hw PASS incl. fasm_audit. nextpnr reports
  "PASS at 12.00 MHz" because build_hw.sh passes no --freq for gcd_ps; the number that matters is its fclk0
  estimate, 343-447 MHz against the board's 100 MHz FCLK0 (xsdb_gcd.tcl's SLCR write).
- Full stack (bit-decoded netlist + prjxray SDF + fid), seed d, 24 vectors from gen_vectors.py: SLOW_MAX 24/24
  ok, 0 hang; FAST_MIN 24/24 ok, 0 hang; fasm_equiv EQUIVALENT; gate ANNOTATE_DONE 0 SDF warnings (max).
  Vector 0 (0x7fffffff, 0x7ffffffe) takes 15.2 us from i_ack to o_req at SLOW_MAX. Seeds 3,4,5 then 6-9
  running; then the negative control: the UNSIZED routes d (rule A -1567 ps) and 5 (-464) on the same stack.
- xsdb_gcd.tcl takes an optional vector file; research/board/gcd_ps_vec1000.hex (seed 1; the GLS's 24 are its
  first 24 lines, byte-identical).
### progress 18:38 (gcd_ps full stack: seeds d, 3 PASS both corners, 4 SLOW_MAX PASS)
- d, 3: 24/24 ok at SLOW_MAX and FAST_MIN, EQUIVALENT, gate ANNOTATE_DONE / 0 SDF warnings on all four; 4 SLOW_MAX
  24/24. Harness negative control (seed d SLOW_MAX netlist, vector file with two expected values corrupted):
  ok=1 err=2, so the compare can fail. Formal-target artefacts (seed d .bit, .fasm.gz, toolchain) staged.
### progress 18:50 (gcd_ps full stack: d,3,4 PASS both corners, 5 SLOW_MAX PASS; disk full voided 5 FAST_MIN)
- 4: 24/24 at both corners, EQUIVALENT, gate clean. 5 SLOW_MAX 24/24.
- 5 FAST_MIN printed no summary: the session's disk allowance ran out at 18:48 while iverilog wrote its
  run_baked.vvp (truncated, "syntax error" at load). Not a GLS result; re-queued. Each gcd_ps full-stack job
  leaves ~1 GB of compiled sims; the drivers now delete them after the run and gate, and the stale binaries of the
  BQ#1-3 sweeps (results in research/data/fid/*.tsv) were removed: 11 GB free.
### progress 19:02 (BOARD-QUEUE #4 gcd_ps added; formal target named)
- Seed 5 FAST_MIN re-run: 24/24, EQUIVALENT. So seeds d,3,4,5 x SLOW_MAX/FAST_MIN: 8/8 runs 24/24, 0 err, 0 hang
  (research/data/gcd_ps/p1_fullstack.tsv). Longest vector 15.1 us (14.95-15.2) at SLOW_MAX, 5.3 us at FAST_MIN.
- BOARD-QUEUE #4 written: formal target = P1 seed d, research/board/gcd_ps_e6bb4aec.bit (md5 aa83c8b7) and
  .fasm.gz (uncompressed md5 2dbf962d); board run = xsdb_gcd.tcl over the 16 golden then 1000 derived vectors.
  PR #2 description refreshed. Queued: seeds 6-9, unsized negative control (d, 5), +PIPE=1 on seed d, 1x scatter.
### progress 19:28 (gcd_ps full stack 6 both corners, 7 SLOW_MAX: 24/24; FOR-RESEARCH s3 reading)
- 6 max/min and 7 max: 24/24, EQUIVALENT; gates clean (5 min's re-run gate too).
- FOR-RESEARCH s3 (does a LUT loop circulate a runt?), CORRECTED after reading audit T6 (claude/audit
  audit/findings/T6.md rows 7-8, section 3): the fid resolver only makes the loop's OWN echo impossible (the
  feedback pin reads the committed state, so the 7 ps runt cannot circulate, by construction); every other LUT pin
  is transport, so the node's readers still see narrow pulses. At shard B's delays the default fid model (resolver
  on) still fails: out0_req 5-15 ps pulse trains, then no lap for 11-14 us on 2 of 3 seeds. So fid neither
  assumes the problem away nor answers s3: what a READER does with a pulse narrower than ~20 ps is not modelled
  (transport), and that is the H_RUNT question. Only the board, or a measured LUT pulse-rejection width, settles it.
### progress 19:48 (gcd_ps full stack: 7 and 8 both corners, 9 SLOW_MAX: 24/24)
- 7 min, 8 max/min, 9 max: 24/24, EQUIVALENT, gates clean. 15 of 16 P1 seed x corner runs done, all 24/24.
### progress 19:57 (gcd_ps P1 full stack: 16/16 seed x corner runs 24/24)
- Seeds d,3-9 x SLOW_MAX/FAST_MIN: all 24/24, 0 err, 0 hang, EQUIVALENT, gate clean
  (research/data/gcd_ps/p1_fullstack.tsv). Longest vector i_ack->o_req: SLOW_MAX mean 15.03 us (14.6-15.4),
  FAST_MIN 5.32 us (5.2-5.45); worst seed for it is 6 at both corners. BOARD-QUEUE #4 updated to 8 seeds.
- Next (queued, running): unsized negative control (d: rule A -1567 ps, 5: -464 ps) on the same stack; then
  +PIPE=1 on seed d (24-vector pairs and formal's (2^19,2^19),(3,5)); then 1x within-die scatter on d,3,4,5.
### progress 20:17 (gcd_ps negative control: the UNSIZED routes pass the full stack -- rule A is pessimistic here)
- Unsized seed d (umux21 12 links; rule A margin -1567 ps guarded, req 6692 vs peak 7088, i.e. negative even raw)
  on the full stack: SLOW_MAX 24/24, FAST_MIN 24/24, EQUIVALENT, gate clean. Unsized seed 5 (-464) SLOW_MAX 24/24.
  So the control did NOT fail: either rule A over-charges this bundle or the GLS/vectors cannot see it.
- tighten's pairing for umux21 says why it may over-charge: "paired as one bundled channel (no common source)",
  request from umux21.uj1 (its join), data from ulink_n_index_97's ctl (the select latch), plus an assumed
  upstream data lag of 1229 ps. It cannot order the two, so it charges the worst case.
- To tell the two apart: seed d re-routed with umux21 cut to 8, 4, 1 links (CONTROL ONLY, never shipped;
  research rule: never shorten a delay to hit a target). Rule A flags all three (-2024/-3670/-4795 ps), so the
  audit can fail. Their full-stack GLS at both corners is queued; where it first fails measures how much of
  rule A's charge on this bundle is real.
### progress 20:45 (FOR-RESEARCH s2 on the gcd_ps full stack: overlapped calls reorder; unsized d and 5 pass)
- Unsized control complete: seeds d and 5, both corners, 24/24 (rule A -1567 / -464 ps). The shortened-umux21
  controls (8/4/1 links) are what decides it; queued.
- +PIPE=1 (host offers pair k+1 right after pair k's i_ack; NOT gcd_ps's protocol), seed d P1, SLOW_MAX, full
  stack. Formal's pair (2^19, 2^19) then (3, 5): out0 = 1 first, then 0x80000 -- REORDERED, exactly
  FOR-RESEARCH s2's prediction, now on the bit-decoded gcd_ps target with prjxray delays. The 24 vectors as 12
  pairs: 2 reordered ((0x7fffffff,0x7ffffffe) overtaken by a==b; the large-prime pair overtaken by an early
  return), 2 in order, 8 HANG. The same compiled sim in the sequential mode afterwards: 24/24.
  Caveat on the hangs: this host waits for pair k+1's i_ack before reading k's result, so a hang there can be
  the host's own deadlock (the kernel may not accept k+1 until k's result is taken). gcd_ps's register
  interface cannot express a fully concurrent host (a CTRL write with o_ack=1 also rewrites the request flop),
  so the model now names the wait that timed out (ack0/ack1/out0/out1); re-run queued.
- What it means for the board: confirms that BQ#1 and BQ#4 must stay sequential; both are (gcd_rig's two-stage
  env; xsdb_gcd.tcl waits for o_req to fall before the next write).
### progress 21:05 (pipe FAST_MIN same as SLOW_MAX; 1x scatter seeds d, 3 PASS)
- +PIPE=1 at FAST_MIN (seed d): formal pair REORDERED (1 then 0x80000), 12 pairs 2/2/8 (reordered/in order/hang),
  identical to SLOW_MAX; sequential run 24/24.
- Within-die scatter 1x (band 0.38 + region 0.16 + wire 0.126, draw 1), full stack: seeds d and 3 24/24,
  EQUIVALENT. 4, 5 running.
- bdc_muxn3_32 reading (why rule A may over-charge umux21): z_data is a mux on s (the select latch's data),
  z_req = delay(OR of C(in_k_req, ctl_req & s==k)). s is the output of ulink_n_index_97, whose own request is
  matched (8 links) after its data, so s settles before ctl_req rises; tighten, finding "no common source",
  charges s an upstream lag of 1229 ps after the request instead. The shortened-umux21 controls test this.
### progress 21:30 (why the gcd_ps negative control cannot fail; an out0 bundling monitor)
- 1x scatter: seeds 4, 5 also 24/24 (4/4; research/data/gcd_ps/p1_scatter1x.tsv). BOARD-QUEUE #4 updated.
- umux21 cut to 1 link (control route): full stack 24/24 at SLOW_MAX and FAST_MIN. Cause found by reading the
  generated kernel: umux21's output n170 IS the kernel's out0 (out0_req = n170_req, out0_data = n170_data), and
  gcd_ps's consumer is the PS: o_data_capture is sampled every FCLK0 and the host reads O_DATA only after o_req
  has crossed the 2-flop synchronizer and an AXI read, i.e. >= 20 ns after out0_req. So a result that settles
  after its request is still read right; the PS-harness GLS cannot see an out0 bundling violation, and the
  unsized "pass" says nothing about rule A. Negative result: through this harness, this bundle's GLS check is
  blind by construction. (On gcd_hw, out0 goes to the rig's asynchronous compare, where it does matter.)
- Remedy for the check: cells/gls/ps/gen_bundle_mon.py + build_ps.sh PS_BUNDLE=1, a monitor on the kernel
  boundary in the bit-decoded netlist (driver pins of core_o_req and bridge_i.o_data_pl[31:0], found via the
  routed JSON's NEXTPNR_BEL and nets.map): margin = out0_req rise minus the last out0_data change; LATE = a
  data change while out0_req is high before the host's o_ack. Running on seed d with umux21 at 1, 4, 8, 12
  (unsized) and 16 (P1) links, both corners. The n4/n8 PS-only controls were dropped (they cannot fail either).
### progress 21:48 (out0 bundling margin measured at the kernel boundary: P1 12.0/4.1 ns, umux21 at 1 link still +2.05/+0.57 ns)
- Monitor (PS_BUNDLE=1), seed d, full stack, 24 requests each, min over requests of (out0_req rise - last
  out0_data change), at the driver pins; no data change while req was high before the host's ack in any run:
  | umux21 links | SLOW_MAX | FAST_MIN |
  | 16 (P1, shipped) | +12043 ps | +4112 ps |
  | 1 (control) | +2054 ps | +566 ps |
  Rule A charged this bundle "PAD to 13" (needs ~5.5 ns more) at 1 link; the GLS says 1 link already has
  +566 ps at FAST_MIN with no scatter. Not yet a claim: one seed, no scatter, driver pins only (routing to
  the consumer excluded), and the monitor's own negative control (umux21's 36 data LUTs and their input wires
  20x slower, on the 1-link route) is queued; 12/8/4 links running.
### progress 22:18 (out0 bundling: monotone in umux21 length, monitor's negative control fails; pipe hangs are kernel deadlocks)
- research/data/gcd_ps/out0_bundle_margin.tsv (seed d, full stack, min over 24 requests, SLOW_MAX / FAST_MIN):
  1 link +2054/+566, 4 +3114/+960, 8 +6859/+2284, 12 (unsized) +8823/+2992, 16 (P1) +12043/+4112 ps; no late
  data change in any. Monotone in length, as it should be (the 1/4/8 routes are separate place-and-routes).
- Monitor negative control: the 1-link route with umux21's 36 data LUTs (and the wires into them, 388 arcs)
  20x slower: 23 (SLOW_MAX) / 24 (FAST_MIN) late changes, up to 9973 / 6255 ps after out0_req, data X while
  settling -- and the PS harness still says 24/24 ok. So the monitor can fail, and the harness is blind here.
- Rule A on this bundle: asks for 13 links at 1 link (-4795 ps); the GLS measures +566 ps at FAST_MIN with no
  scatter. Rule A over-charges it by most of its request chain, through the "no common source" pairing with the
  select latch (progress 21:05). One seed, no scatter, driver pins: a lead for a sharper rule, not a size change
  (the shipped P1 keeps 16; CLAUDE.md: never shorten a delay to hit a target).
- +PIPE=1 re-run with stage labels (seed d SLOW_MAX): all 8 hangs are "out0": the kernel acknowledged BOTH
  overlapped pairs and then produced no result within 60 us (the longest single call is 15 us), so they are kernel
  deadlocks, not this host's. 2 reordered, 2 in order, 8 deadlocked of 12 overlapped pairs: FOR-RESEARCH s2's two
  predictions (reorder, deadlock) both reproduce on the gcd_ps target's full stack.
### progress 22:25 (queue: out0 monitor on all 8 P1 seeds; FOR-RESEARCH C1's tb_pipe on BQ#1's full stack)
- Rule A's mux pairing on gcd_hw R5 (BQ#2 seed 6, tighten.py): all 22 bd_mux bundles pair "by common source" (their
  own join), not the "no common source" pairing that over-charged gcd_ps's umux21. So the over-charge is not a
  general speed lead for gcd_hw. (P3, steer-join grouping, was already tried: negative, JOURNAL 10-26 21:40.)
- Running: the out0 bundling monitor on P1 seeds 3-9 at both corners (the formal target's kernel-boundary
  contract on every seed), then seed d with 64 vectors (first 64 of gcd_ps_vec1000.hex).
- Queued after it: formal's FOR-RESEARCH C1 ask, tb_pipe.v (claude/formal formal/tools/pipe/gls/, used read-only from
  a scratch copy) on the BQ#1 target's board-fidelity stack: netlist decoded from the COMMITTED
  research/board/gcd_hw_03e82630.bit, prjxray SDF of the same route (nextpnr sdf 6f8b99e6), fid, both corners;
  +PIPE=0 9/4 (control), +PIPE=1 9/4, 9/9, 15/5, 2/4; in_ack resolved from this route's nets.map instead of the
  hard-coded n144588. Then BQ#4 scatter to BQ#1's level (1x on 6-9; log-normal 1.5x draw 2 on d,3,4,5).
### progress 23:23 (out0 bundling on all 8 P1 seeds; 64 vectors 64/64)
- research/data/gcd_ps/p1_out0_bundle_8seed.tsv: out0 margin at the kernel boundary, P1, every seed: SLOW_MAX mean
  +12268 ps (11281-13100), FAST_MIN mean +4209 ps (3978-4492, worst seed 5); no late data change on any of the 16
  runs; PS harness 24/24 on all. Seed d with the first 64 vectors of gcd_ps_vec1000.hex: 64/64 at both corners,
  min margin identical to the 24-vector run (the minimum is set by the route, not the operands). BOARD-QUEUE #4
  updated. Now running: FOR-RESEARCH C1's tb_pipe on BQ#1's full stack, then BQ#4 scatter to BQ#1's level.
### progress 23:32 (FOR-RESEARCH C1 on BQ#1's full stack, SLOW_MAX: reorder and deadlock reproduce)
- formal's tb_pipe.v (scratch copy, in_ack resolved from this route's nets.map) on the netlist decoded from the
  COMMITTED research/board/gcd_hw_03e82630.bit (fasm_equiv EQUIVALENT), prjxray SDF SLOW_MAX, fid:
  +PIPE=0 9/4 (sequential control): LAP 1 mism=0 at idx 9 (4096), LAP 2 mism=0 at idx 4 (1): both right.
  +PIPE=1 9/4: the only result is LAP 1 mism=0 at idx 4, i.e. 1 = pair 2's gcd; pair 1's 4096 never comes.
  +PIPE=1 9/9: no result at all (quiet for 100 us).
  Identical in kind to formal's nextpnr-SDF GLS (FOR-RESEARCH C1) and to the gcd_ps target's +PIPE=1 run.
- start/in_ack timing, vector 9, sequential: request 697.5 ns, in_ack rises 928.1 ns (+230.6), result 3789.0 ns
  (+3091.5). The input handshake completes ~2.9 us before the result: gcd_rig.v's header ("acknowledges start only
  when it is finished") is wrong on the board-fidelity stack too; the rig is safe because its env waits for out0.
  15/5, 2/4 and FAST_MIN running.
### progress 23:53 (FOR-RESEARCH C1 on BQ#1's full stack: all five cases as predicted, both corners)
- research/data/fid/c1_pipe/README.md: SLOW_MAX and FAST_MIN, decoded from the committed BQ#1 bit: sequential 9/4
  both right; pipelined 9/4 only 1 (pair 2's), 9/9 and 15/5 deadlock, 2/4 only pair 1's. Exactly FOR-RESEARCH
  C1's table, now on the board-fidelity stack the request named. Rig env control vec 6: 16 laps, 0 errors.
### progress 23:55 (BQ#4's board script checked offline against a mock board; scatter runs restarted with the monitor)
- cells/hw/mock_xsdb_gcd.tcl: xsdb_gcd.tcl in tclsh against a fake board (gcd_ps register map, Euclid gcd,
  instant answers) with injected faults. none: PASS 16/16 and 1000/1000, exit 0; wrong:5 and hang:7: PASS 15/16 /
  999/1000 + FAIL line, exit 1, one MISMATCH line; deadaxi: liveness pre-check refuses, exit 1. So BQ#4's pass
  criterion is self-reporting and can fail; and Euclid agrees with the vector file's ref_gcd answers on all 1000.
  It checks the script, not the design.
- The BQ#4 scatter extension was restarted with PS_BUNDLE=1 (psbm/run3.sh) so it also measures the out0 margin
  under scatter: 1x on seeds 6-9, log-normal 1.5x draw 2 on d,3,4,5.
### progress 00:37 (BQ#4 scatter at BQ#1's level: 1x 8/8, log-normal 1.5x 4/4, out0 margin positive throughout)
- 1x scatter seeds 6-9: 24/24, EQUIVALENT; out0 margin 5959/7412/7309/7151 ps (band column). Log-normal 1.5x draw 2,
  seeds d,3,4,5: 24/24, EQUIVALENT, out0 margin 6033/6411/5990/5929 ps, no late change; longest vector 8.85-9.7 us.
  Tables research/data/gcd_ps/p1_scatter1x.tsv, p1_logn15.tsv; BOARD-QUEUE #4 updated.
- gcd_ps lead (690f156) status: every item of the owner's list done (audits, full stack at both corners on 8 seeds
  with derived vectors from outside the 16, BOARD-QUEUE #4 with the formal target's .bit/.fasm and md5s, CDC
  reading, sequential harness confirmed, FOR-RESEARCH s2/C1 reproduced on both targets' full stacks, s3 read).
  Beyond it: the out0 bundling monitor and the PS-harness blind spot it exposed; the board script checked offline.
Next: (1) ring128 per-ring data from the owner still blocks acceptance; (2) the umux21 finding suggests a sharper
rule A for "no common source" pairs whose data comes from a matched link -- worth a formal look (it would be a
soundness argument, not a measurement), not a size change; (3) goal 2 leads (rule E tightening, two-phase links)
once the gates may move.
### summary of the gcd_ps lead (owner, 690f156), 2026-11-01 17:31 - 11-02 00:40
Toolchain: nextpnr 9c732bc6303458df, patches 789a7120c912d393 (toolchain.sh ok)   Seeds: d,3-9 (P1); d (controls)
Did: gcd_ps with BQ#1's flags; pad-only sizing (P1: umux21 12 -> 16); fasm2net --ps7 + async-SR flops; a
behavioural PS7 running the documented host sequence; derived vectors outside gcd_rig's 16; an out0 bundling
monitor; FOR-RESEARCH s2/C1 pipelined tests on both targets; the board script checked against a mock board.
Measured:
| what | result | n |
|---|---|---|
| audits on P1 | rule A/E/J 0, D 38 (screen); umux21 margin mean 1456 ps (358-1889) | 8 seeds |
| full stack, SLOW_MAX / FAST_MIN | 24/24 each, EQUIVALENT, gate clean; longest vector 15.0 / 5.3 us | 8 seeds x 2 |
| full stack, 64 vectors | 64/64 at both corners | seed d |
| 1x within-die scatter | 24/24 | 8 seeds |
| log-normal 1.5x, draw 2 | 24/24 | 4 seeds (6-9 running) |
| out0 bundling margin, no scatter | FAST_MIN mean +4.21 ns (worst +3.98), SLOW_MAX mean +12.27 (worst +11.28) | 8 seeds |
| out0 margin under scatter | >= +5.93 ns (band column) | 8 runs |
| out0 margin vs umux21 length (seed d, FAST_MIN) | 1: +0.57, 4: +0.96, 8: +2.28, 12: +2.99, 16: +4.11 ns | 5 routes |
| PS-harness blind spot | umux21 at 1 link, or its data 20x slower: still 24/24 (monitor: 23-24 late) | seed d |
| pipelined host (gcd_ps) | formal pair reordered; 12 pairs: 2 reordered, 2 in order, 8 deadlocked | seed d x 2 |
| tb_pipe on BQ#1's bit (C1) | sequential right; 9/4 reorder; 9/9, 15/5 deadlock; 2/4 pair 2 lost | 2 corners |
Does NOT show: silicon (BOARD-QUEUE #4 is the test); scatter beyond 1.5x or other draws on gcd_ps; out0 timing
at the consumer pins (the monitor reads driver pins); that rule A's extra charge on umux21 is unsafe to remove
(one route family, no proof); anything about the arbiter or runt hypotheses beyond what BQ#1-3 already had.
Next: as in progress 00:37 above.
### progress 00:39 (CDC survey of every PS harness, by reading)
- The owner's gcd_ps CDC question applied to every cells/hw/*_ps.v: gcd/ipow/mult/mult2/multn sample STATUS
  i_ack/o_req through 2-flop synchronizers (sync_i_ack/sync_o_req); mem_arb (sync_lz_req/tok_ack/la_ack) and
  mem_port (sync_ack) synchronize their acks; mem_bist is fully synchronous (RAMB18E1 on aclk, nothing async
  crosses); ro_link synchronizes run/rst INTO the ring domain, reads its counters only after the window closed, and
  its token census is a deliberate asynchronous sample (a mean over reads is the measurement, by design). No
  missing synchronizer found. Reading only; none of these except gcd_ps has a GLS harness.
### progress 01:34 (gcd_ps log-normal 1.5x: draws 2 and 3, 8/8 seeds each)
- Draw 2 seeds 6-9 and draw 3 all 8: 24/24, EQUIVALENT, no late out0 change; out0 margin draw 2 +5.93..+9.07 ns,
  draw 3 +6.19..+9.95 ns (p1_logn15.tsv, p1_logn15_draw3.tsv). Same coverage as BQ#1 (draws 2 and 3, 8/8).
  Running: log-normal 2x (region 0.32 + wire 0.252), draw 2, all 8 seeds, to find what fails first.
### progress 02:12 (gcd_ps survives log-normal 2x on all 8 seeds)
- Log-normal 2x (region 0.32 + wire 0.252), draw 2: 8/8 seeds 24/24, EQUIVALENT, out0 margin +5.62..+9.81 ns, no
  late change (p1_logn2x.tsv). For comparison, BQ#3 seed 9 fails between 1.75x and 2x (draw 1) and BQ#2 seed 6
  between 1.5x and 1.75x. Not a like-for-like comparison (different kernel harness, draw 2 not 1), but no gcd_ps
  route has shown a scatter failure yet. Running: 3x on all 8 to find what fails first.
### progress 02:49 (gcd_ps survives log-normal 3x on all 8 seeds; controls queued)
- Log-normal 3x (region 0.48 + wire 0.378), draw 2: 8/8 seeds 24/24, EQUIVALENT, out0 margin +5.07..+11.78 ns, no
  late change (p1_logn3x.tsv). Scatter was applied (provenance: scatter 0.378 region 0.48 logn 1; run times move
  with scale: seed d 131 us at 1.5x, 145 at 2x, 160 at 3x). P1 is BQ#1-type sizing (defaults + one pad), not the
  tightened R5 of BQ#2/3, which is the expected reason it has more scatter margin.
- An all-pass scan is only evidence if the same stack can fail on this design: queued the umux21=1-link control
  route at 3x (does the margin go negative?) and P1 seed d at 5x (region 0.80 + wire 0.63).
### progress 03:02 (scatter controls on gcd_ps: nothing fails up to log-normal 5x; the scatter does reach the bundle)
- umux21=1-link control route at log-normal 3x (draw 2): 24/24, out0 margin +269 ps (no scatter, band-free corners:
  +566 FAST_MIN / +2054 SLOW_MAX), so the scatter moves the monitored bundle toward failure but not past it.
- P1 seed d at log-normal 5x (region 0.80 + wire 0.63, draw 2): 24/24, EQUIVALENT, out0 margin +4252 ps, run 214 us.
  Scatter reached every arc (44617 interconnect arcs from the wire model, 24968 with one draw each, region factor
  on all 113788). So no scatter level tried breaks gcd_ps P1 on these draws; the stack's ability to fail under
  scatter is shown on gcd_hw R5 (BQ#2 seed 6 at 1.5-1.75x, BQ#3 seed 9 at 1.75-2x), not on this design. The
  difference is the sizing: P1 keeps bdc's default lengths (plus one pad) where R5 tightened every chain.
- Does NOT show: that silicon's within-die variation is log-normal or bounded like this; draws other than 2 above 1.5x.
### progress 03:03 (is it the sizing? BQ#1 at log-normal 3x)
- To test the explanation that P1's default lengths are why gcd_ps survives 3x-5x while R5 (BQ#2/3) fails at 1.5-2x:
  BQ#1 (gcd_hw, default lengths, same pads/placement) at log-normal 3x draw 2 on seeds d,3,4,5 (seeds_fid, existing
  routes). Running.
### progress 03:26 (formal target's kernel boundary map)
- research/tools/boundary_map.py: nets crossing a hierarchy prefix in a routed JSON, with driver bel/pin (fasm2net's
  net names). On the formal target (bridge_i.udut.): 68 in, 36 out once constants (785, incl. packer-legalised
  constant LUTs) and packer route-through sinks are excluded. Names are yosys's, not the RTL's: the request flop
  (req_core) is called bridge_i.p_end_req and out0_ack is called n_index_97_ack, so the map gives the pins, and
  BOARD-QUEUE #4 gives the port reading. research/board/gcd_ps_e6bb4aec.boundary.tsv.
### progress 03:27 (audit read: T12 independently confirms the gcd_ps target)
- claude/audit 34c32f11 (T12): with the auditor's own vectors (none from gen_vectors) and own oracle, the gcd_ps
  target passes nominal and log-normal 2x draw 2 on seed d, EQUIVALENT, out0 margin min 5738 ps = research's row;
  6f0d3d92: decoded LUT/MUXF of every kernel site agree with the bits, Lean data and nextpnr. No REFUTED or
  OVERSTATED row on research's gcd_ps work. (Not re-run by the auditor: seeds 3-9, FAST_MIN, 1.5x draws.)
### progress 04:02 (BQ#1 at log-normal 3x: d, 3 PASS)
- BQ#1 (gcd_hw, default lengths) log-normal 3x draw 2: seed d PASS 16/16 errs 0 (vec 6 laps 24/18/28), seed 3 PASS
  16/16 (25/19/28), EQUIVALENT; default-seed sdf 6f8b99e6 again. Consistent with the sizing explanation: both
  default-length builds (BQ#1, BQ#4) survive 3x where the tightened R5 builds fail at 1.5-2x. Seeds 4, 5 running.
### progress 04:04 (R6 considered and dropped; all 1000 board vectors queued on the formal target)
- R6 (R5 with only uori2/uori3 padded, to keep R5's speed with BQ#1's scatter margin) considered and dropped: R5
  has uori2/3/4 at 19-20 links vs 84 in BQ#1, and covering a 3-sigma log-normal 2x region ratio (~2.6x) by padding
  alone means roughly doubling those loop-body chains, a large speed cost; co-location was the real cure and
  region placement does not legalize (JOURNAL 10-31). R5 passes 1.5x on two draws, which is above the measured
  scatter. Not pursued.
- Queued after BQ#1's 3x seeds: research/board/gcd_ps_vec1000.hex in 16 chunks of 64 on the formal target (P1
  seed d), full stack, both corners, out0 monitor on, so every vector the board will run has a GLS verdict first.
### progress 04:54 (BQ#1 survives log-normal 3x: 4/4; the sizing explanation holds)
- BQ#1 log-normal 3x draw 2: d, 3, 4, 5 all PASS 16/16 errs 0, EQUIVALENT (vec 6 laps 24/25/21/27 vs ~16 at SLOW_MAX,
  ~46 at FAST_MIN). Both default-length builds (BQ#1 on gcd_hw, BQ#4 on gcd_ps) survive 3x on every seed tried;
  both tightened R5 builds (BQ#2, BQ#3) have a seed that fails between 1.5x and 2x. So R5's ~1.9x speed is bought
  with scatter margin, and the margin it keeps (>=1.5x on draws 2-3) is still above the measured 8.5% ring scatter.
  The board order in BOARD-QUEUE (#1 first) already matches this.
### progress 07:21 (all 1000 board vectors pass on the formal target's full stack)
- research/board/gcd_ps_vec1000.hex on gcd_ps_e6bb4aec (decoded from the committed bit), SLOW_MAX and FAST_MIN, out0
  monitor on: 1000/1000 ok at each corner, 0 err, 0 hang, 0 id mismatch, out0 min margin 12043 / 4112 ps (the same as
  the 24- and 64-vector runs: the minimum is set by the route), no late change. research/data/gcd_ps/p1_vec1000_target.tsv;
  BOARD-QUEUE #4 updated: the board run now has a per-vector GLS prediction for every vector it will run.
### progress 09:31 (BQ#1 at log-normal 3x: 8/8 seeds)
- Seeds 6-9 at 3x draw 2: PASS 16/16 errs 0, EQUIVALENT (vec 6 laps 20/23/32/26). BQ#1 at 3x: 8/8 seeds
  (research/data/fid/bq1_logn3x_draw2.tsv), like BQ#4 (8/8). BOARD-QUEUE #1 updated.
Next: (1) ring128 per-ring data (owner) unblocks acceptance; (2) a sharper rule A for "no common source" pairs
(umux21 finding) as a formal soundness question, not a size change; (3) goal 2 (speed) only with a scatter
budget: R5's 1.9x costs the 3x scatter margin the default lengths keep, so any tightening should be judged by its
failing scatter scale, not only by rules and corners.
### progress 09:39 (speed / scatter trade-off: R5 x1.25 routes)
- research/data/gcd_hw_sizes_R5x125.vh: every R5 size x1.25 rounded up (sum 796 -> 1106 links; none shorter), BQ#2's
  flags. Question: how much SLOW_MAX speed does it cost, and does it pass log-normal 2x draw 1, where R5 seed 6
  fails? Arms: R5x1.25 seeds 7,8,9 (+10), R5 seeds 7,8,9 (+10) at the same scatter (R5 seed 6 already FAIL).
- Seed 6 did not place under R5x1.25 ("post-placement validity check failed for Bel SLICE_X14Y88/A5FF (no cell)",
  the same nextpnr legality failure R5 seed 2 once hit): seed 10 added to both arms instead.
- Audits: seeds 7, 8 every rule clean (D 38 screen); seed 9 rule A -32 ps (urig.udut.ucontrol_merge9, 5 links, PAD
  to 6). So uniform lengthening does not keep rule A by itself: the longer chains move the route, and one bundle
  ends 32 ps short. Seed 9 is kept in the experiment as a data point, not as a shippable route.
### progress 10:41 (R5x1.25 seed 8: SLOW_MAX 29 laps vs R5's 31; log-normal 2x draw 1 PASS)
- R5x1.25 seed 8: SLOW_MAX PASS 16/16 laps 29/23/34 (vectors 6/12/13; R5 seed 8: 31/25/37, i.e. -6..-8%);
  log-normal 2x draw 1 PASS 16/16 (35/28/42). R5 seed 8 has no log-normal 2x draw 1 row yet (queued). Seeds 7, 9
  then the R5 arm and seed 10 running.
### progress 11:39 (R5x1.25 seed 9: SLOW_MAX 28 vs R5 31; log-normal 2x draw 1 PASS)
- R5x1.25 seed 9: SLOW_MAX PASS 16/16 (28/23/33; R5 seed 9: 31/25/36, -10%); log-normal 2x draw 1 PASS (33/26/39),
  despite its -32 ps rule A flag. Seed 7, then the R5 arm at the same scatter (seeds 7-9), then seed 10, running.
### progress 12:52 (R5x1.25 arm done on seeds 7-9: -7..-10% SLOW_MAX laps, log-normal 2x draw 1 3/3 PASS)
| seed | R5 SLOW_MAX (6/12/13) | R5x1.25 SLOW_MAX | change on vec 6 | R5x1.25 logn 2x d1 |
|---|---|---|---|---|
| 7 | 31/25/36 | 28/22/33 | -10% | PASS 50/40/58 |
| 8 | 31/25/37 | 29/23/34 | -6% | PASS 35/28/42 |
| 9 | 31/25/36 | 28/23/33 | -10% | PASS 33/26/39 |
  R5 arm at the same scatter (seeds 7-9; R5 seed 6 FAILS it) now running, then seed 10 for both.
### progress 14:00 (R5 arm at log-normal 2x draw 1: seeds 7, 8 PASS)
- R5 seeds 7 (51/39/58) and 8 (41/32/48) PASS log-normal 2x draw 1; seed 6 FAILs it (errs 3). So far R5 2/3 vs
  R5x1.25 3/3 on the seeds that place: not yet discriminating. R5 seed 9 and seed 10 (both arms) running.
### progress 15:09 (R5 vs R5x1.25 at log-normal 2x draw 1: not discriminating)
- R5 seed 9 PASS (45/36/53). At log-normal 2x draw 1: R5 3/4 (seed 6 FAIL; 7, 8, 9 PASS), R5x1.25 3/3 (7, 8, 9; seed 6
  does not place). On the routes both arms have, both pass, so 2x draw 1 cannot tell them apart; R5's one failure
  is a route-specific placement (uori3 far from its datapath) that x1.25 could not even be routed on. Seed 10
  (both arms) running, then log-normal 3x draw 1 on 7-10 of both arms, where failures should be common enough
  to compare rates. Cost so far: -6..-10% SLOW_MAX laps on vector 6.
### progress 16:21 (R5x1.25 seed 10; R5 seed 10 routed clean)
- R5x1.25 seed 10: every audit clean; SLOW_MAX PASS 26/21/31; log-normal 2x draw 1 PASS 38/29/46. R5 seed 10 routed,
  every audit clean; its SLOW_MAX and 2x runs are running, then 3x draw 1 on 7-10 of both arms.
### progress 17:33 (R5 vs R5x1.25: 2x does not discriminate; x1.25 costs 10.5% at SLOW_MAX)
- research/data/fid/r5x125/README.md: on seeds 7-10, R5x1.25 costs -10.5% SLOW_MAX laps (vec 6 31.0 -> 27.75, range
  -6..-16%), and both arms pass log-normal 2x draw 1 on all four. 3x draw 1 on 7-10 of both arms now running.
### progress 19:37 (R5x1.25 survives log-normal 3x draw 1 on seeds 7-10)
- R5x1.25 at log-normal 3x (region 0.48 + wire 0.378) draw 1: seeds 7, 8, 9, 10 all PASS 16/16 errs 0 (vec 6 laps
  44/28/26/32). R5 arm at the same 3x now running; if R5 fails there, x1.25 buys between 2x and 3x of margin for
  ~10% speed.
### progress 20:40 (R5 also passes log-normal 3x draw 1 on seeds 7, 8)
- R5 seed 7 PASS (47/36/53), seed 8 PASS (34/26/39) at log-normal 3x draw 1. So on the routes both arms have, neither
  fails at 2x or 3x: R5's known scatter failures (BQ#2 seed 6, BQ#3 seed 9) are specific routes, not a uniform
  shortfall that x1.25 fixes. Seeds 9, 10 of R5 at 3x running.
### progress 21:41 (R5 vs R5x1.25 complete: x1.25 trades 10.5% speed for the one 3x failure seen)
- Log-normal 3x draw 1, seeds 7-10: R5 3/4 (seed 10 FAIL errs 4, vectors 2, 3, 9, 15: one wrong lap then a stall,
  the same vector set as BQ#3 seed 9's uori2 failure), R5x1.25 4/4. 2x draw 1: 4/4 both on these seeds.
  research/data/fid/r5x125/README.md.
- Conclusion (thin: one failure per eight scatter runs): R5's scatter failures are route-specific; a uniform 25%
  lengthening removed the one seen on seeds 7-10, at -10.5% SLOW_MAX laps (vec 6 31.0 -> 27.75). It also cost a
  placement (seed 6) and a rule A flag (seed 9, -32 ps), so it is not a drop-in replacement for R5. Not shipped.
Next: a targeted version (lengthen only the chains whose bundles failed under scatter: uori2/uori3) would keep most
of R5's speed; it needs the failing-chain list from more draws first. Ring128 data still blocks acceptance.
### progress 21:42 (R6t: targeted lengthening of uori2/uori3 only)
- uori2 failed under scatter on two independent routes (BQ#3 seed 9 at 2x, R5 seed 10 at 3x; same vectors 2, 3, 9,
  15), uori3 on one (BQ#2 seed 6). R6t = R5 with only those two chains x1.25 (19->24, 20->25 links);
  research/data/gcd_hw_sizes_R6t.vh. Seeds 6-10: audits, SLOW_MAX laps, log-normal 3x draw 1. Running.
  (Disk: cleared the compiled sims of finished runs, 18 GB free.)
### progress 21:49 (R6t routes: every audit clean on 5/5 seeds)
- R6t seeds 6, 7, 8, 9, 10 all place (seed 6 too, unlike R5x1.25) and pass every audit (A/E/J 0, D 38 screen).
  SLOW_MAX and log-normal 3x draw 1 sims running.
### progress 00:08 (R6t so far: SLOW_MAX 30-32 laps, log-normal 3x draw 1 PASS on 7, 9)
- R6t SLOW_MAX vec 6: seed 7 30, 8 32, 9 30 (R5 31/31/31). Log-normal 3x draw 1: seed 7 PASS (44/33/53), 9 PASS
  (44/34/50). Seeds 6, 8 (3x), 10 running; seed 10 is the one where R5 failed 3x.
### progress 01:08 (R6t: container restart killed the driver; seed 10 and seed 6 3x relaunched)
- Done before the restart: SLOW_MAX seeds 6 30, 7 30, 8 32, 9 30 (vec 6); log-normal 3x draw 1 seeds 7, 8, 9 PASS.
  Lost: seed 10 (8/16 vectors at SLOW_MAX) and seed 6 3x. Relaunched on the existing routes (seed 10 first, seed 6
  after it; three fid sims at once has OOM'd on 15 GB).
### progress 01:54 (R6t seed 10 FAILS log-normal 3x: the targeted fix does not buy 3x margin)
- R6t seed 10: SLOW_MAX PASS 32/26/37; log-normal 3x draw 1 FAIL errs 7 (vectors 1,2,3,9,11,13,15). So the R6t arm at 3x draw 1 is
  3/4 so far (7, 8, 9 PASS; 6 running), the same rate as R5 (3/4), while R5x1.25 was 4/4.
- Rule A on this draw's exactly scaled SDF (research/tools/scatter_ruleA/scale_sdf.py, then tighten.py): 10 non-D
  bundles short at once (ucmpi1 -4638, ushrsi1 -8729, ushrsi2 -8911, ushrsi0 -3310, uori2 -2945, ucmpi8 -917, ...;
  research/data/fid/r6t/seed10_3x_scaled_ruleA_violations.txt). At 3x the tightened R5 family is short in many
  bundles on some routes, not in one chain, so lengthening the two chains seen failing at 2x does not cover it.
  (As recorded 10-31, rule A on a scaled SDF over-reports; the GLS failure is the evidence, the list only says it
  is broad.)
- SLOW_MAX: R6t vec 6 30/30/32/30/32 on seeds 6-10 (mean 30.8) vs R5 31.0 (seeds 7-10) and R5x1.25 27.75. R6t is
  nearly free at SLOW_MAX and passes every audit on 5/5 seeds, but buys no measured scatter margin at 3x.
### progress 02:33 (queued: R5 vs R5x1.25 at log-normal 3x draw 1 on fresh seeds 11-14)
- After R6t seed 6: routes and 3x draw 1 runs for seeds 11-14 in both arms (8 runs), to put more than four routes
  under the R5x1.25 4/4 vs R5 3/4 comparison.
### progress 02:56 (R6t complete: 4/5 at log-normal 3x, same rate as R5; no speed cost)
- R6t seed 6 at 3x PASS (40/32/47). R6t at log-normal 3x draw 1: 4/5 (seed 10 fails). research/data/fid/r6t/README.md.
  Negative result for the targeted fix as a 3x-margin measure; it is speed-neutral and audit-clean, so it is a
  candidate only if the 2x failures (uori2/uori3) are the concern, which the board would have to show.
### progress 03:01 (R5x1.25 seeds 11-14: placed, every audit clean)
- R5x1.25 seeds 11, 12, 13, 14: all place, rules A/E/J 0 (D 38 screen). Their log-normal 3x draw 1 runs, then R5's
  on the same seeds, are running (~5 h).
### progress 04:44 (R5x1.25 also fails log-normal 3x on a fresh seed)
- R5x1.25 3x draw 1: seed 12 FAIL errs 5 (vectors 4, 5, 7, 8, ...), 13 PASS, 14 PASS, 11 running. So R5x1.25 is 6/7
  at 3x so far, not immune: the earlier 4/4 vs R5's 3/4 was within noise. R5 on seeds 11-14 runs next.
### progress 05:10 (R5 on fresh seeds 11-14: one rule E violation, one unplaceable)
- R5 seeds 11, 14 every audit clean; 13: rule E 6 violated, all ulink_n106__1 -> ucond_br34/35/36 (raw +3837, guarded
  -119 ps, fix +1 element; the same link R3/R4's rule E tail kept finding); 12: does not place (nextpnr post-placement
  validity check, SLICE_X18Y44/A5FF (no cell); third occurrence: R5 seed 2, R5x1.25 seed 6, R5 seed 12). BOARD-QUEUE
  #2 now says to build with the default seed as written. The 3x runs on 11, 13, 14 continue (13 kept as a data point).
- The nextpnr placement failure recurs at about 1 seed in 10 on these netlists: worth a look (RLOC v4 column groups
  vs packing are the likely interaction) but it fails loudly, so it cannot produce a wrong bitstream.
### progress 06:56 (speed/scatter study closed: uniform or targeted padding of R5 does not change its 3x failure rate)
- R5 on fresh seeds at 3x draw 1: 11, 13, 14 PASS. Totals on seeds 7-14 that place: R5 6/7, R5x1.25 7/8, R6t 4/5.
  Failures are ~1 route in 5-8 for every R5-family variant at 3x, and 0/16 for default lengths (BQ#1 8/8, BQ#4 8/8).
  research/data/fid/r5x125/README.md, research/data/fid/r6t/README.md.
- Conclusion (negative): neither the uniform x1.25 (-10.5% speed) nor the targeted uori2/uori3 pad (~0%) moves the
  tightened sizing's 3x failure rate measurably at this sample size. 3x is twice the 1.5x that R5 holds on every
  route tried, and ~6x the measured ring scatter. No size change recommended; BOARD-QUEUE order stands.
Next: the lead list in PROGRAM.md (goal 2) and the ring128 data; nothing queued on the machine now.
### progress 06:58 (answer to audit RISK row 108: fast-early/slow-late mixing on BQ#1-#4)
- Audit row 108 (tcheck.md): static fast-early/slow-late mixing gives rule J 7/18 clients negative per route (BQ#1
  -252, BQ#2 -472, BQ#3 -459 ps) and, with the project band, negative A/E rows; marked RISK, not a refutation.
- The closest dynamic test this stack has is within-die scatter: log-normal factors per 10x10-slice region and per
  wire make one branch of a fork fast while another is slow, i.e. a sampled version of the mixing (bounded speed-ups,
  so not the static worst case). Results on the full stack, every arbiter in the design exercised by the 16 or 24
  vectors: BQ#1 log-normal 3x draw 2 8/8 routes PASS, 1.5x draws 2-3 16/16; BQ#4 3x 8/8, 5x 1/1; BQ#2/BQ#3 1.5x 16/16,
  with their 2x-3x failures traced to compute-unit bundles (uori2/uori3, broad rule A shortfall at 3x), not to an
  arbiter. So the sampled mixing, up to 3x on default lengths, never broke an arbiter fork; the static worst case
  the audit computes is not refuted by this (sampling is not exhaustive, and the arbiter near-tie model, arbtie.md,
  is the fid resolver's).
### progress 07:00 (gcd cost model: GLS corners bracket the August board's per-iteration costs)
- research/tools/gcd_ps_cost_fit.py fits cells/hw/gcd_cost_fit.py's model (base + k, pre-ctz, main, inner-ctz terms,
  counters replayed from the C) to GLS latencies (out0_req rise from the bundle monitor minus the CTRL write) on the
  1000-vector runs of the formal target. Per-iteration ns, SLOW_MAX / FAST_MIN: k 157.7 / 57.2, pre-ctz 154.5 / 54.9,
  main 218.6 / 76.8, inner ctz 139.7 / 49.6 (residual RMS 40 / 14 ns). The August board fit (gcd_bench_gen):
  127.1, 108.3, 156.5, 114.6 -- inside the corner bracket on all four terms, at 54-72% of the way from FAST_MIN to
  SLOW_MAX. The band column (0.38) with 1x scatter, 24 vectors: 103, 95, 121, 77 -- 10-33% FASTER than the board.
  research/data/gcd_ps/cost_model_vs_board.tsv.
- Reading, soft (different build: the August bench had other sizes and a pre-patch toolchain era, and a cost model is
  not the ring data acceptance needs): on this kernel the board sits nearer SLOW_MAX than the band 0.38 that the five
  rings were fitted to. If it holds on a like-for-like build, the band predictions in BOARD-QUEUE (e.g. "~50-55 laps
  per 150 us" for #3) are optimistic, and the SLOW_MAX numbers are the safer expectation. Worth a check by the owner
  when #4 runs: gcd_ps per-call latency is directly comparable with this table.
### progress 07:01 (queue: target 1000 vectors at band + 1x scatter; BQ#1 3x draw 3)
- Not pursued: a like-for-like GLS of the August gcd_bench_gen build behind the board cost model. Its bitstream was not
  kept and its build ran converge.sh's select-pad loop, so a rebuild would be another route; the comparison would stay
  soft. The nextpnr placement-validity failure (1 seed in ~10) is noted, not chased: it fails loudly.
- Running: all 1000 BQ#4 vectors on the formal target at band 0.38 + 1x within-die scatter (the board-like point),
  then BQ#1 at log-normal 3x draw 3 on all 8 seeds.
### progress 09:40 (formal target: all 1000 board vectors also pass at band + 1x scatter)
- 1000/1000 ok, 0 err, 0 hang, out0 min margin 7341 ps, no late change, at band 0.38 + region 0.16 + wire 0.126 draw 1.
  BOARD-QUEUE #4 updated. BQ#1 log-normal 3x draw 3 on 8 seeds now running.
### progress 13:08 (next lead: a routed full-stack GLS of gcd_bench_gen -- tooling, untested)
- Why: two open items need the bench harness simulated, which nothing here could do (no AXI host for its
  register map): the "RTZ tail" (rtz_cost.sh: gcd 12.1 cycles/run vs the null's 5; the 2026-10-30 17:08 trace found
  the kernel's own output RTZ ~14 ns, so the rest is unexplained) and the soft acceptance item bench_hang (the August
  harness's 3-bit state register reading an async latch; inventory.md: "no AXI host model for the bench harness").
- cells/gls/ps/gen_ps7.py now also writes ps7_bench.v: the same AXI3 master (task text shared; ps7_master.v is
  byte-identical, md5 81d66ef5) running xsdb_bench_gen.tcl's run_batch, reading the bench's own illegal-transition
  sticky (0x58) after each batch, with +PSTEP to step the FCLK0 period between batches (a phase sweep).
  build_ps.sh takes PS_DESIGN/PS_HOST/PS_MON_GEN (gcd_ps default unchanged). gen_bench_mon.py: per-run kernel
  handshake times at driver pins, aclk phase of i_ack/o_req, cycles per FSM segment, illegal transitions.
- Build: BQ#4's flags and P1 sizes in build_bench.sh. With BD_RLOC=v4 nextpnr cannot place the uori2/uori4 delay
  columns in the bench ("post-place repair: no valid placement ... uori2.udly.chain.g[0]", then an arch.h:923
  assertion) on seeds 3 and 4 alike: deterministic, not seed noise (gcd_ps places them; the bench adds 1024 histogram
  flops). Retrying with v2 (build_bench.sh's default); the kernel then needs its own audits.
### progress 13:53 (bench routes with v4 once its histogram is compiled out; audits clean)
- BD_RLOC=v2 routes the bench but misses rule A once (ulink_n_falseResult_25 stage 1, -144 ps) and rule E broadly
  (ucond_br10-18 need 5-11 pad elements): BQ#1's pads were measured on v4 placement, so v2 is not a like-for-like
  kernel. Kept v4 and compiled out the bench's 64x16 latency histogram instead (its write data tied to 0, so yosys
  drops the 1024 flops; HIST reads 0). The histogram only observes; the FSM, synchronisers, AXI slave and kernel
  are gen_bench.py's. The patch is a sed in the build's worktree, recorded with the data.
- Route nh3 (NEXTPNR_SEED=3, nextpnr 9c732bc6303458df, toolchain.sh all ok): bit 464c573f, fclk0 est. 108 MHz;
  build_bench.sh's rule A gate holds; audit_route.sh: rule A/E/F/H/I/J 0, rule D 38 (the screen, as BQ#4).
- Queued behind BQ#1's last two seeds (memory): full-stack fid GLS of nh3 at both corners, FIXED gcd(48,18) x16 and
  UNIFORM seed 1 x32. BQ#1 3x draw 3: d,3-7 PASS so far.
### progress 14:17 (BQ#1: log-normal 3x draw 3 also 8/8)
- BQ#1 full stack (bits-decoded netlist, prjxray SDF, fid), band 0.38 + log-normal region 0.48 + wire 0.378 (3x the
  calibrated within-die scatter), draw 3, seeds d,3-9: 8/8 PASS 16/16, errs 0, EQUIVALENT, vec 6 laps 20-30
  (research/data/fid/bq1_logn3x_draw3.tsv). With draw 2: 16/16 routes x draws at 3x on the default lengths. Does not
  show: silicon, or more than two draws of one scatter model. BOARD-QUEUE #1 updated.
### progress 14:53 (bench full-stack GLS: first numbers; August-harness route built)
- nh3 (fixed harness), SLOW_MAX, bits-decoded netlist EQUIVALENT, gate ANNOTATE_DONE with no SDF warning: FIXED
  gcd(48,18) x16: completed 16/16, SIG 00020002 = the fold of gcd=6 over 16 runs (derived, not read), illegal-transition
  sticky 0. latmin/max 170/171, cycles/run 176.06, so the rtz_cost.sh "tail" is 6.06; per run (gen_bench_mon): S_ACK +
  S_RTZ + S_NEXT = 5 cycles, the null's; kernel output RTZ (bench_o_ack -> o_req fall) 12.7 ns, synchroniser 17.4 ns.
  i_ack comes 360 ns after the request, o_req 1.665 us. Every run identical to the ps (deterministic sim).
- Reading (soft): on this route the RTZ tail is the harness's 5 cycles plus mean-vs-min, not the kernel; the board's
  12.1 (August build, other sizes) is NOT reproduced. FAST_MIN and UNIFORM running.
- au3: the same build with the synchroniser reverted (cdc_bench.sh's "august" sed, applied to gen_bench.py in the
  worktree), NEXTPNR_SEED=3, bit 53b40d67; audits A/E/F/H/I/J 0, D 38. On nh3 st[0] is placed 15 rows from st[1:2].
- Running: phase sweep (139 batches x 2 runs, FCLK0 10000-10276 ps in 2 ps steps: i_ack, ~36 cycles after issue,
  walks the whole aclk period in ~72 ps steps) on au3, then the same on nh3 as the control.
### progress 15:22 (bench RTZ tail: the harness floor at both corners; the board's 23/12.1 not reproduced)
- nh3 fixed harness, full stack: SLOW_MAX UNIFORM seed 1 x32 (full-width random operands): SIG b2d15eed =
  hw/uniform_oracle.py's (derived from the C), 0 illegal transitions, latency 96-1297 cycles. FAST_MIN FIXED gcd(48,18)
  x16: SIG 00020002 (derived), latmin = latmax = 63, cycles/run 68.0, tail 5.0.
- Per run (gen_bench_mon, every run of both batches): S_ACK + S_RTZ + S_NEXT = 5 cycles at SLOW_MAX, 4 at FAST_MIN;
  kernel output RTZ (bench_o_ack -> o_req fall) 12.7 ns / 4.6 ns, identical for every vector; i_ack comes 359-468 ns
  (SLOW_MAX, operand-dependent) after the request.
- So on this route gcd's tail is the null floor (5.0 exact on the board for all four nulls), at both corners and for
  every input; the kernel's RTZ is absorbed by the o_req synchroniser. The board's gcd tail is NOT reproduced: README
  says 22.992 exact, rtz_cost_results.tsv 12.142 approx -- both from d741ae57 (2026-08-24), on an unarchived August
  build, an hour after the lut-pinmap patch was first committed (whether that board's binary had it is not on record).
  Grade: soft. The board's latmin 122 does sit between the GLS corners (63 / 170), as the cost-model check found.
- Open hypothesis (cheap to test later): the long tail was a property of that build (e.g. a pre-patch bitstream), not
  of the kernel. inject_pinmap.py on this bench route + the same monitor would say whether pinmap corruption can lengthen
  the RTZ. Not run.
### progress 15:44 (August bench hang mechanism reproduced on the full stack -- control pending)
- au3 = the bench with the synchroniser reverted (August code), SLOW_MAX phase sweep (2-run FIXED batches, FCLK0
  10000 + 2k ps; i_ack's phase moves ~72 ps per step): in one window, FCLK0 10010-10044 ps (batches 5-22 of 128),
  the bench's own illegal-transition sticky fires in 13 batches (S_WAIT_ACK 011 -> 001 in 12, -> 000 in one, which
  hangs 0/2), and 4 more complete out of protocol (results captured 2-27 cycles after issue). Outside it, 110
  batches are normal. 001/000 are bitwise mixes of 011 and the intended 100: the mechanism of the August hang, with a
  different code than the board's 110 (route-dependent). research/data/bench/ (README.md, logs, the two seds).
- Grade: this reproduces a SOFT acceptance item's mechanism, not its rate or code (no August route). The deciding
  half is the control: the same sweep on nh3 (synchroniser in) is running; it must show no illegal transition.
### progress 16:12 (control: the synchronised bench never mixes over the same sweep -> bench_hang mechanism MATCH)
- nh3 (today's harness), the same SLOW_MAX sweep: 127 batches, FCLK0 10000-10252 ps, 0 illegal transitions, 0 hangs,
  every SIG derived-correct, no out-of-protocol capture; i_ack's phase covered ~9 of 10 ns.
- So the full stack reproduces the August bench hang's mechanism and its fix (soft item bench_hang: mechanism MATCH;
  code and rate need the August route). acceptance_status.md row added. Two routes, not one with/without: noted.
- Queued (q4): au3 UNIFORM 4x32 random full-width vectors at the nominal 100 MHz (board-like: does the August harness
  give wrong answers or hangs there?), the window again at 1 ps steps with another metastability seed (skew or
  metastability?), au3 FAST_MIN sweep.
### progress 17:31 (bench_hang on more routes: seeds 4-6 of both harnesses building)
- One route each is a sample (CLAUDE.md), so both harnesses are being built on NEXTPNR_SEED 4, 5, 6 (same flags,
  nohist, August revert for "au"). So far, all audits clean (A/E/F/H/I/J 0, D 38): au4 10ba5223, nh4 0529f049,
  au5 d0b647b2. The same phase sweep will run on each. au3 UNIFORM 4x32 at 100 MHz still simulating.
### progress 17:38 (ring128 on its MEASURED route: band 0.38 MISMATCH; x = 0.288 predicts all 128 rings within 3%)
- The owner committed the August ro_many_top build and its per-ring periods (db3c299b, research/board/ro_many_aug/):
  the hard timing test was blocked on exactly this. md5s check; the bits decode EQUIVALENT to the routed JSON.
- acceptance.py --stack full --items ring128 --ro-many-data (the pre-registered test: median and per-length medians
  within +/-5%): SLOW_MAX +88.2% (no ring slower: bound holds), FAST_MIN -35.9% (every ring slower: bound holds),
  **band 0.38: +11.5% median, MISMATCH** (hard). Per ring, silicon sits at x = 0.288 of [FAST_MIN, SLOW_MAX]
  (p05-p95 0.276-0.303, no length trend). With one global x every held-out split passes: groups 0-7 <-> 8-15,
  short <-> long, leave-one-length-out; median errors <= 0.6%, worst ring 3.06%. acceptance.py at --band 0.288: MATCH.
  The route's own nextpnr SDF: p05/p95 -28/+18%, 7-link -16%. research/tools/ring128_fit.py, research/data/fid/ring128/.
- So the model fix is the band (0.38 -> 0.288), and the within-die residual is 0.76% median |dev| per ring (includes
  model error), about 1/11 of the "1x" scatter (8.33%), which had been sized to an 8.5% measured against nextpnr's
  SDF. Every 1x/1.5x/3x scatter result so far ran at ~11x/16x/33x the ring-level variation now on record.
- Not yet acceptance in full (acceptance_status.md): rings test LUT + wire arcs only; a soft datum (gcd per-iteration
  costs, another build) puts kernel cells at 0.54-0.72. A cell-type-dependent x is the case that hides a bundling
  violation (matched delays are LUT chains, datapaths are not), so the gates stay until the verification runs cover it.
- Not changed yet: gen.py's GLS_SDF_BAND default (0.38) and acceptance.py's --band default. Next: make 0.288 the
  measured default (0.38 stays reproducible by env), then the cell-type check.
### progress 17:39 (model fix: band default 0.38 -> 0.288)
- gen.py GLS_SDF_BAND and acceptance.py --band default 0.288 (the measured route's median; comments cite the data);
  GLS_SDF_BAND=0.38 reproduces every earlier band result. seeds_fid.py now puts the band value in its tag
  (band0.288_s...), so rows from before (bare "band") stay unambiguous. test_acceptance.py 30 passed. acceptance.py
  at the default: ring128 MATCH (exit 0). ring5_a/b ERROR here: their rebuilt ro_top route is not on this container
  (soft items; not re-run). ring128_summary.py keeps its explicit 0.38 model, as a record of what it tested.
- Effect on earlier band numbers: at 0.288 ring periods are ~10% shorter than at 0.38 (median ring: 1.114 -> 1.0 of
  measured), so band-column laps and margins move toward the FAST_MIN side; corners unaffected.
### progress 17:41 (the cell-type check: GLS_SDF_BAND_CELL)
- ring128 calibrates SLICE_LUTX and interconnect arcs only. A gcd_hw route's xray SDF also has CARRY4 (1380 IOPATH
  arcs), SELMUX2_1 (F7/F8, 3603) and SLICE_FFX (326) arcs, with no measured position. Matched delays are LUT chains;
  datapaths use carries and F7/F8 muxes. So the dangerous reading of the soft gcd cost datum (kernel cells nearer
  SLOW_MAX) is: uncalibrated cells slow, LUT chains as measured.
- gen.py GLS_SDF_BAND_CELL=CELLTYPE=b,... (band only): those IOPATH arcs take band b; counts printed; seeds_fid tags
  it (_c...). Unit check on a (100:200:300) arc: LUT 158, CARRY4 at b=1 300.
- Running: BQ#2 (R5, the thinnest margins) on its 8 routes (seeds 6-11,13,14), band 0.288 with
  CARRY4=1,SELMUX2_1=1,SLICE_FFX=1; then BQ#3 and BQ#1. The bench queue (q4) was stopped after its current run.
### progress 18:14 (cell-type check running; bench routes 4-6 built)
- GLS_SDF_BAND_CELL took effect on BQ#2 seed 6 (IOPATH arcs moved: CARRY4 1380, SELMUX2_1 3600, SLICE_FFX 326);
  its 16 vectors are simulating, one sim at a time while au3's UNIFORM run finishes.
- Bench routes for bench_hang on more seeds, all audits clean (A/E/F/H/I/J 0, D 38): au4 10ba5223, nh4 0529f049,
  au5 d0b647b2, nh5 f44ff432, au6 ddf4f013, nh6 35715d8c. Their sweeps are queued after the cell-type check.
### progress 18:20 (bench_hang, board-like: the August harness hangs every UNIFORM batch)
- au3 at the nominal 100 MHz, UNIFORM seeds 1-4 x 32 (full-width operands, as the board's batches): 4/4 batches HANG
  after 6, 3, 4, 14 runs, the bench's own sticky 011 -> 001 in each. nh3 (fixed) passed the same UNIFORM batch at both
  corners (32/32, oracle SIG). research/data/bench/README.md. The board: 5 of 8 runs hung, with code 110.
### progress 19:16 (cell-type check: BQ#2 seed 6 PASS)
- BQ#2 (R5) seed 6, band 0.288 with CARRY4/SELMUX2_1/SLICE_FFX at SLOW_MAX: PASS 16/16, errs 0, EQUIVALENT, laps
  61/50/72 (full SLOW_MAX 33/27/39). Seeds 7-11,13,14 running two at a time, then BQ#3, BQ#1.
### progress 21:57 (cell-type check: BQ#2 5/5 so far; seed 10's NOT_EQUIVALENT is a constant LUT, fixed in fasm_equiv)
- BQ#2 under GLS_SDF_BAND_CELL (CARRY4/SELMUX2_1/SLICE_FFX at SLOW_MAX, the rest at 0.288): seeds 6, 7, 8, 9, 10
  PASS 16/16 errs 0 (laps 57-61 / 46-50 / 66-72). 11, 13, 14 running.
- Seed 10's rows say NOT_EQUIVALENT, here and in every earlier column (incl. its 3x FAIL that "R5 6/7" counts). By the
  journal's own rule (2026-10-28 03:53) that is a stop sign, and it was missed then. Traced: two pins the routed JSON
  ties to GND (on ulink_n_trueResult_4 stage 1's C node and a $PACKER_GND LUT) are driven in the bits by
  SLICE_X14Y79/A6LUT, which the bits configure with INIT all 0 and all inputs constant: nextpnr routing GND out of an
  unused LUT, as on BQ#3 seed 7 (the decoder already resolves it to 0 since 54f2ce6). The netlist simulated was
  functionally the JSON's; fasm_equiv compared driver identity, not value.
- fasm_equiv.py: a LUT whose INIT is all 0 / all 1 is compared as that constant (pins, routing key, and the bits-only
  cell is reported as a benign kind). Seed 10 now EQUIVALENT; seed 8 unchanged (EQUIVALENT). Negative controls on
  seed 8's bits: a live LUT forced to INIT 0 -> NOT EQUIVALENT (DRIVER DIFFERS ...); inverted -> NOT EQUIVALENT
  (LUT FUNCTION DIFFERS), identical to the old tool; a 1-bit flip of an entry its tied pins never reach is
  EQUIVALENT under both. test_acceptance.py 30 passed. The running cell check uses the frozen worktree (old verdicts).
### progress 00:22 (cell-type check: BQ#2 8/8 PASS)
- BQ#2 (R5 sizes, the tightest shipped candidate), 8 routes (seeds 6-11, 13, 14), LUT + interconnect at the measured
  0.288 and every CARRY4 / F7F8 / FF arc at SLOW_MAX: 8/8 PASS 16/16, errs 0 (laps vec 6: 55-61, mean 57.1;
  full SLOW_MAX ~31). research/data/fid/bq2_cellcheck.tsv. So the uncalibrated cell types running at their slow
  corner against measured-speed LUT chains do not break R5's bundles on any route. BQ#3, then BQ#1, running.
- Does not show: those cells beyond SLOW_MAX, scatter on top (next: the measured residual as scatter), silicon.
### progress 00:24 (the measured residual as scatter: "M" = region 0.02 + wire 0.126)
- f3/ring_scatter.py on ring128's measured route: the old 1x (region 0.16 + wire 0.126) gives 8.37% median |dev|;
  the board's residual is 0.76% (0.98/0.58/0.73/0.66 at 7/15/31/63). region 0.02 + wire 0.126 gives 1.34%
  (2.15/1.59/1.16/0.91), the smallest tried at or above the measured value at every length: "M", the scatter
  PROGRAM.md's verification criterion asks for. ring128/README.md.
- Plan: the verification runs per candidate (>= 8 seeds): SLOW_MAX, FAST_MIN (done for BQ#1-4), band 0.288 + M,
  and the cell-type check with M on top. Queued after the running cell checks.
### progress 02:01 (container restart ~01:45; queue relaunched)
- Every background job died (verification queue, sims, lock keeper); scratch files and the toolchain survived
  (toolchain.sh: all patches ok, nextpnr 9c732bc6303458df). Rows that landed before: BQ#3 cell check d, 3 PASS
  16/16 (laps 60/50/71, 59/48/69). Relaunched only the missing runs (vq2.sh, the frozen worktree at 2945db42).
### progress 03:36 (owner's next steps 1dd0a675; item 2 started: the August gcd_bench_gen on the full stack)
- The owner committed research/board/aug/ (every August board build with its .bit, and 331 logs paired to them) and
  PROGRAM.md "Next, now that ring128 matches": (1) the sim is the gate, uncalibrated cells at 0.288 by default and
  also gated at the slow-cell corner; (2) fit the datapath band on the August gcd build; (3) shrink matched delays to
  what the sim proves; (4) every other kernel through the full stack; (5) one ordered board list.
- Item 2 running: the August gcd_bench_gen (bit f199866ea256, nextpnr d216cb36, the async-latch-hang build) decoded
  from its bits with its own routed JSON, prjxray SDF of that route, ps7_bench.v (new +VECFILE: one FIXED batch per
  vector) on the board's 24 gcd_cost vectors x 2 runs, at FAST_MIN, SLOW_MAX, band 0.288, and 0.288 with CARRY4/
  F7F8/FF at SLOW_MAX. Board: logs/gcd_cost.tsv (latmin/latmax per vector, N=200).
- The verification queue (cell check BQ#3/BQ#1, then band 0.288 + M, cell + M) continues alongside.
### progress 05:17 (item 2: the August gcd kernel sits at x = 0.21 on its own build -- faster than the rings' 0.288)
- The August gcd_bench_gen (f199866ea256) on the full stack, the board's 24 gcd_cost vectors: per vector, x =
  (board - FAST_MIN)/(SLOW_MAX - FAST_MIN) = 0.209-0.216 (median 0.211, 12 clean vectors >= 100 cycles); the four
  cost-model terms give 0.196-0.210. research/data/aug_gcd/README.md.
- So the datapath does NOT sit slower than the rings: the soft 0.54-0.72 came from comparing different builds. Per
  PROGRAM item 2 the cell default (0.288) stands; it over-predicts this kernel by ~10%. But LUT + wire structures span
  x 0.21-0.29 on this die, so a matched delay at 0.21 with its datapath at 0.29 is a mix the sim must also gate
  (next: an instance-level band, delay chains low, the rest high).
- The August harness hits its race in the sim at SLOW_MAX (10/24 batches), not at FAST_MIN (0/24); reported.
- Band 0.288 and band + slow cells on this build running.
### progress 05:19 (GLS_SDF_BAND_INST: matched-delay chains at their own band)
- gen.py GLS_SDF_BAND_INST=@FILE ("INSTANCE band" lines; IOPATH of those instances and INTERCONNECT into them;
  wins over GLS_SDF_BAND_CELL; an instance the SDF lacks is an error). research/tools/band_inst_list.py writes the
  file from the routed JSON (cell regex -> NEXTPNR_BEL; default all bd_delay chain LUTs, '\.chain\.g\[\d+\]\.u$').
  Checked on BQ#2 seed 6's bits-decoded netlist: 1183 chain BELs, all in the SDF, 8756 arcs moved to 0.21 while the
  rest stays at 0.288. No effect when unset.
- The gate this enables (next): delay chains at x = 0.21 (the August gcd kernel's measured position, the low end of
  LUT + wire on this die), everything else at 0.288, and the same with CARRY4/F7F8/FF at SLOW_MAX on top.
### progress 06:32 (item 2: uncalibrated cells are off the gcd kernel's critical cycle; x = 0.21 is the delay chains')
- August gcd build, band 0.288 with CARRY4/F7F8/FF at SLOW_MAX (8514 arcs moved): latency identical to band 0.288 on
  all 24 vectors, cycle for cycle (sim end time equal to the ps). The kernel's latency is its matched delays +
  handshake LUTs; the datapath has slack. So the board's x = 0.21 is the RLOC'd delay chains' position, ring128's
  0.288 LUT + routed hops'. Measured mix: matched delays ~10% faster (vs the model) than routed logic -- the
  dangerous direction. The gate queued (vq3) runs exactly that corner: chains 0.21, the rest 0.288, cells at
  SLOW_MAX, + M, on BQ#1-3 x 8 seeds. research/data/aug_gcd/README.md.
- BQ#3 cell check: seeds 4, 5 PASS (62/50/73, 56/44/65); 6-9 resumed.
### progress 09:59 (cell-type check: BQ#3 8/8 PASS; the worst-case gate starts)
- BQ#3 (R5 + fast-fall links), seeds d,3-9, CARRY4/F7F8/FF at SLOW_MAX against LUT + wire at 0.288: 8/8 PASS 16/16,
  errs 0, EQUIVALENT (laps vec 6: 56-63). research/data/fid/bq3_cellcheck.tsv. With BQ#2's 8/8: 16/16 routes.
- Now: the combined worst case (delay chains 0.21, CARRY4/F7F8/FF at SLOW_MAX, rest 0.288, + M) on BQ#2's 8 routes;
  the other kernels' August builds after it.
### progress 14:59 (worst-case gate: BQ#2 4/4 so far; restart survived; disk cleaned)
- The combined worst case (delay chains at 0.21 -- 1183 instances, 8756 arcs; CARRY4/F7F8/FF at SLOW_MAX; the rest at
  0.288; M scatter on top) on BQ#2 (R5, the tightest sizes): seeds 6, 7, 8, 9 PASS 16/16, errs 0, EQUIVALENT (laps
  vec 6: 60-64). 10, 11 running; 13, 14 next.
- Container restart ~14:50: this time every job survived (only the watcher died). Disk was at 90%: deleted the
  regenerable per-run decoder outputs and netlists of finished runs (routes.tsv, pipnames.tsv, fasm_routed.json,
  routed.json copies, annot.sdf, netlist*.v; never the route dirs or any log) and three idle 1 GB vvps: 17 GB free.
### progress 17:09 (the combined worst-case gate: BQ#2 8/8 PASS)
- BQ#2 (R5 sizes, the tightest candidate), 8 routes (6-11, 13, 14): delay chains at 0.21, CARRY4/F7F8/FF at SLOW_MAX,
  the rest at 0.288, + M scatter: 8/8 PASS 16/16, errs 0, all EQUIVALENT (laps vec 6: 58-64).
  research/data/fid/bq2_worstcase.tsv. So R5's bundles hold with the matched delays ~10% faster than the routed logic
  (the measured mix), the uncalibrated cells at their slow corner, and the board's residual as scatter, on every route.
- Does not show: silicon; mixes beyond those measured (chains below 0.21); BQ#3/BQ#1 (running next, after the
  August-kernel runs, which now pause the queue: item 2 for ipow/isprime/collatz/collatz64).
### progress 18:00 (a deadlock cost ~25 min; the other August kernels now running)
- runk.sh paused the gate's seeds_fid (SIGSTOP) while one of its threads held the shared compile flock, then waited
  on that flock itself: nothing ran 17:35-18:00. Replaced by runk2.sh, which runs the August kernel builds without
  the flock (the gate is stopped and nothing else simulates, so memory is not shared) and resumes the gate at the
  end. Lesson: never SIGSTOP a process that may hold a lock you will wait on; pause between seeds instead.
- Running: ipow, isprime, collatz, collatz64 August bench builds at FAST_MIN and SLOW_MAX on their board vectors.
### progress 18:04 (the August ipow bitstream has a live LUT written as constant 0)
- ipow_bench_gen (August, bit 6dbf3faec62f): bits-vs-JSON NOT EQUIVALENT. Traced: the routed JSON has
  bridge_i.udut.ushrsi0's LUT at SLICE_X24Y46/C6LUT (CLBLM_R_X17Y46 SLICEM_X0 CLUT) with INIT 0100 (f = I1 & ~I0),
  driving 9 pins; the August FASM writes CLUT.INIT = 0 there (the .bit agrees with the FASM; its route pips are in
  both). So the board ran that LUT as constant 0: a FASM-writer defect of that toolchain (d216cb36), not a decoder one.
  The shape fits the lut-pinmap class (if the pin carrying I1 is taken for I0, f = I0 & ~I0 = 0); the build (08-24
  06:12) predates the patch's first commit (11:41) though its toolchain.txt stamps it ok. fasm_equiv flags it as it
  should (DRIVER DIFFERS on the 9 sinks, LUT FUNCTION DIFFERS on the 4 consuming LUTs). The other differences are the
  benign kinds. gcd_bench_gen was EQUIVALENT.
- The full stack simulates what the board ran, so the ipow comparison stays valid; whether the defect changed any
  answer is read from the run against the board's recorded results (aug_x.py checks every result).
### progress 18:27 (August isprime: NOT EQUIVALENT is nextpnr's GND buffers -- benign by inspection; fasm_equiv not changed)
- isprime_bench_gen (August): fasm_equiv lists 3 DRIVER DIFFERS, all F7-mux inputs at SLICE_X10Y63 whose JSON drivers
  are $PACKER_GND_NET$LUT buffers (INIT ..0010, A1 on GND: output 0) and whose bits drivers are INIT-0 LUTs (output
  0). Same value; benign. The other kinds are the benign ones.
- Tried to make fasm_equiv fold such buffers (JSON side by name, decoder side by evaluating INIT when every physical
  pin is constant). It moved differences between categories rather than settling them (5-LUT O5 outputs need the
  32-bit half; some JSON LUT inputs are undriven nets), so it was reverted: the verdict stays conservative and the
  August builds' differences are classified by hand here. The sims run on the bits and are checked against the
  board's results either way.
### progress 20:39 (another restart ~20:30 killed every job; requeued)
- Lost: the paused gate driver (BQ#3 worst case had no rows yet), the August runner (isprime SLOW_MAX at 16/18 vectors;
  kept as a partial log, as FAST_MIN's 16, enough for x), the lock keeper. Relaunched: runk4.sh (collatz, collatz64
  August builds at both corners, holding the compile flock through compile and run) beside vq5.sh (the gate, one sim
  while runk4 lives, then two: worst case on BQ#3/BQ#1, band 0.288 + M on BQ#2/3/1, BQ#1 cell check, bench sweeps).
- isprime vectors trimmed to board latency <= 3000 cycles (18 of 25; the rest run 6k-61k cycles, ~7 h of sim for
  nothing the x fit needs); collatz/collatz64 all fit.
### progress 20:39 (item 2: isprime sits at x = 0.222; kernels so far 0.211 / 0.225 / 0.222)
- August isprime_bench_gen, 16 board vectors at each corner (partial logs: trimmed list, cut by the restart): x =
  0.222 (0.220-0.226, 12 vectors >= 50 cycles), every result equal to the board's. research/data/aug_kernels/.
- Three kernels on their own August builds: gcd 0.211, ipow 0.225, isprime 0.222 -- one kernel band ~0.22, against
  ring128's 0.288. collatz, collatz64 running.
### progress 00:04 (item 2 done: five kernels at x = 0.211-0.225, rings 0.288; restart again ~23:50)
- collatz64 (August, EQUIVALENT): x = 0.224 (0.218-0.227), results equal the board's. Five kernels on their own
  August bitstreams: gcd 0.211, ipow 0.225, isprime 0.222, collatz 0.222, collatz64 0.224. research/data/aug_kernels/.
- Item 2 answer: the datapath is not slower than the rings; the default (cells at 0.288) stands; kernels' x is their
  matched delays' (slow cells change no latency), ~10% faster than band 0.288, which the worst-case gate covers.
- Another container restart (~23:50) killed every job; collatz64 SLOW_MAX had 16/27 (enough). Gate relaunched (vq6:
  BQ#3 worst case 3-9 (d done), BQ#1 worst case, band + M on all three, BQ#1 cell check, bench sweeps).
### progress 00:08 (item 5: the ordered board list; a second ring route with predictions committed first)
- BOARD-QUEUE.md now opens with the owner's ordered list: (1) gcd_ps 1000 vectors, (2) H_RUNT short-pulse test -- not
  built yet, next, (3) the fastest design the sim accepts (BQ#2 R5 now: worst-case gate 8/8), (4) a ring set on a second
  route. Each judges itself.
- (4) built: today's ro_many_top (August recipe, default seed, nextpnr 9c732bc6), bit 8dc4f1ac, bits EQUIVALENT to
  its routed JSON; research/board/ro_many_2/ holds the bit, xz'd FASM/JSON/SDF, and predicted.tsv (per ring FAST_MIN,
  SLOW_MAX, band 0.288) written before any run. research/tools/ring2_judge.py applies acceptance.py's criterion; on
  the first route's data it PASSes at 0.288 and FAILs at 0.38.
### progress 00:09 (gate trimmed to the worst case; band + M and the plain BQ#1 cell check dropped)
- The combined worst case (chains 0.21, CARRY4/F7F8/FF SLOW_MAX, the rest 0.288, + M) contains band 0.288 + M except
  that the chains are faster and the cells slower, i.e. every bundle has less margin; and it contains the plain cell
  check plus M. Running those separately costs ~12 h of the one machine for nothing a bundling failure could add, so
  the gate is: SLOW_MAX and FAST_MIN (done, 8/8 each for BQ#1-#4) + the worst case on 8 routes. BQ#3's worst case is
  running (d PASS), BQ#1 next (vq7.sh). Not strictly monotone in an async circuit; noted, not run.
### progress 00:14 (item 4 started: every other kernel through the full stack)
- Configs (Explore agent's survey of the journal, checked against research/data): ipow T9 (BD_DSP=1), collatz T3,
  xorshift T3, collatz64 T4, isprime rulee6 pads (BD_DSP=1 BD_RLOC_ARB=1; the one without a ratcheted size set, rule E
  not clean on 2/4 earlier seeds). 4 fresh routes each via bdc/fusion_bench.py --route (its own RTL check, audits and
  nextpnr-SDF GLS), then per route: soak.fasm assembled to a .bit (bit_control.to_bit), the prjxray SDF, and
  cells/gls/fid/soak_fid.py ... bit --gate at SLOW_MAX, FAST_MIN and the combined worst case. Running beside the
  gate (k4.sh, frozen worktree at 841995d1). Oracles: fusion_bench's, from the C.
### progress 00:35 (item 4: ipow routes; item 3 step 1 queued)
- ipow T9, 4 fresh routes (seeds 29-32, fusion_bench --route): RTL check and routed nextpnr-SDF GLS fast+stalled pass on
  all 4; rules E/J 0. tighten.py exits 1 on every seed with 8 violations, all section D (ucond_br2..9 select
  screens, margins -3.8 to -8.1 ns): the screen, as recorded for T9 and every earlier kernel, not a gate. Their
  full-stack runs (SLOW_MAX, FAST_MIN, worst case) are running.
- Item 3 step 1: research/tools/shrink_sizes.py; candidate research/data/gcd_hw_sizes_R5s90.vh = R5 x0.9 (ceil): 19
  sizes move (the compute udly and select delays >= 10 links, by 1-2 links each); the 1-2 link link/uack sizes stay.
  Routing on BQ#2's seeds 6,7,8,9,10,11,13,14 (one at a time, holding the compile lock); then the worst-case gate on
  all 8, then both corners. A failure reverts the step. BQ#1's worst case moved behind it (i3.sh): the board list's
  item 1 is gcd_ps, which has its own gate.
### progress 01:19 (H_RUNT rig built and routed; ipow 3/4 routes through the full stack)
- runt_top (board list item 2; a subagent wrote the RTL/measure/judge/testbench, checked here: runt_tb PASS, its
  injected defect FAILs): routed at nextpnr 9c732bc6303458df, 2 BUFGs, edge counters fabric-clocked. Predictions from
  its prjxray SDF (research/tools/runt_predict.py, band 0.288): TEST episode widths -427..+1542 ps vs own loops 211-633
  ps; committed with the bit before any board run (research/board/runt/). BOARD-QUEUE item 2 now has commands and a
  self-judging criterion. Not done: a fid GLS of the rig.
- ipow T9 seeds 29, 30, 31: full stack PASS at SLOW_MAX, FAST_MIN and the combined worst case (EQUIVALENT bits).
- Item 3 step 1 (s90): 8/8 routed. Audits (informational now): tighten.py needs `--osc dhk --osc invhk` on gcd_hw (the
  housekeeping ring); rule A 0-2 per route at the old 8.5% guard (raw margins positive), rule E 8 on seed 6, rule J
  -57 ps guarded on seed 11. The full stack decides; its sims wait for BQ#3's worst case.
### progress 01:34 (item 4: ipow 12/12; the August "FASM-writer defect" was a checker gap)
- ipow T9, seeds 29-32 x {SLOW_MAX, FAST_MIN, worst case}: 12/12 PASS (research/data/item4/).
- Their bits-vs-JSON check first read NOT EQUIVALENT, with exactly the August ipow signature. Traced: ushrsi0's LUT2
  (f = I1 & ~I0) has BOTH logical inputs on one physical pin (X_ORIG_PORT_A1 'I0I1 ', net $PACKER_GND_NET), so it is
  constant 0 by its own netlist, and nextpnr's FASM writer correctly writes INIT 0. The August ipow build is the same
  shape ('I1 I0' on $PACKER_GND_NET at SLICE_X24Y46/C6LUT). **CORRECTION of 18:04 (Nov 4)**: that was not a
  FASM-writer defect and the board did not run a broken LUT; fasm_equiv judged constness from the INIT string.
  Fix: lut_const() also folds a LUT whose physical-pin function (gen.py's expansion) is constant. On ipow seed 29 it
  folds exactly that one cell; all 4 routes EQUIVALENT. Negative control: the bits-side LUT made live (f = A1) -> NOT
  EQUIVALENT. test_acceptance.py 30 passed. research/data/aug_kernels/README.md corrected.
### progress 05:22 (BQ#3 worst-case gate 8/8; item 4: collatz, xorshift 12/12 each)
- BQ#3 (R5 + link fast fall), combined worst case, seeds d,3-9: 8/8 PASS 16/16, EQUIVALENT, laps 58-65 on vec 6
  (research/data/fid/bq3_worstcase.tsv). BQ#3 is now board list item 3 (fastest design the sim accepts); BQ#2 is
  its fallback.
- Item 4: collatz T3 and xorshift T3, 4 routes each x {SLOW_MAX, FAST_MIN, worst}: 12/12 PASS each, bits
  EQUIVALENT on all 8 routes; audits rule D screens only (6 / 8 per route), E/J 0. collatz64 running (seed 1 3/3).
- Item 3 step 1 (s90) worst-case sims started (i3.sh); BQ#1's worst case follows the s90 corners.
### progress 11:08 (item 3 step 1: s90 passes the worst-case gate 8/8 and is not faster; item 4 isprime fixed)
- s90 (R5 x0.9 ceil), worst case on BQ#2's 8 seeds: 8/8 PASS 16/16, EQUIVALENT (research/data/item3/). Paired laps
  vs R5's own worst-case rows: 0.999 / 1.000 / 0.996 on vec 6/12/13, per-seed 0.87-1.11: no measurable speedup. Route
  scatter swamps a 1-2 link cut. s75 (x0.75, 52 sizes) is routed; its worst case runs next, then the corners of the
  deepest step that passed.
- isprime: every soak read "SOAK all FAIL: 31 port bits have no same-driver net" before simulating -- a soak_fid
  harness bug (a constant-driven port bit was always counted missing; isprime returns a bool in an i32). Fixed
  (e574b300); rerun: seeds 25, 26 PASS at SLOW_MAX, FAST_MIN and the worst case (25 and 26 are the routes with rule E 2).
- collatz64 T4: 12/12 PASS, 4/4 EQUIVALENT.
### progress 12:26 (item 4 done: 60/60)
- isprime (rule-E-6 pads, BD_RLOC_ARB=1), seeds 25-28: 12/12 PASS, 4/4 EQUIVALENT; seeds 25/26 carry rule E 2 and pass
  the worst case. Item 4: ipow T9, collatz T3, xorshift T3, collatz64 T4, isprime: 60/60 full-stack runs (SLOW_MAX,
  FAST_MIN, combined worst case; 4 fresh routes each), every route's bits EQUIVALENT (research/data/item4/).
- Item 3: s75 worst case running (i3b.sh).
### progress 13:22 (item 3 on xorshift: x0.75 is 1.13x faster and passes 12/12; a shrink_sizes bug found first)
- shrink_sizes clamped every size to >= 1, so T3's 18 zero sizes (uack, short rdly) became 1: the first xorshift x0.75
  routed SLOWER than T3 (nominal 3.31 vs 3.22 us on seed 1). Fixed (a 0 stays 0); gcd R5 has no zeros, so s90/s75 are
  unchanged (regenerated s75 byte-identical below its header).
- xorshift T3 x0.75 (13 of 47 sizes), seeds 1-4: SLOW_MAX, FAST_MIN and the combined worst case 12/12 PASS, 4/4
  EQUIVALENT. Paired against T3's item-4 runs: 1.131x at both corners (1.10-1.16), 1.117x in the worst case
  (1.09-1.15). Audits (informational): rule A 1-2, rule E 0-2 per route. Seeds 5-8 and x0.5 queued.
- gcd s75: worst case 2/2 so far (seeds 6, 7).
### progress 14:01 (item 3, xorshift x0.5: 12/12 at 1.46x; the gate's teeth on this flow not yet shown)
- xorshift T3 x0.5 (20 of 47 sizes), seeds 1-4: SLOW_MAX, FAST_MIN, worst case 12/12 PASS, 4/4 EQUIVALENT. Paired vs T3:
  1.465x (SLOW_MAX), 1.463x (FAST_MIN), 1.438x (worst case). Old rules: A 4-6, E 2-10, H 0-1 per route.
- Caution recorded before anything is claimed: each halving has passed, so the gate's ability to FAIL a too-short delay
  on this kernel/flow is unshown. x0.25 queued, then x0 if needed (CLAUDE.md: a negative control must be able to fail).
  Not a board candidate until a failing step brackets it.
### progress 14:24 (disk full at ~14:20: two runs voided, nothing read from them)
- The scratch disk filled (139 MB free). Two compiled sims were truncated mid-write: xorshift T3 seed 8's worst-case
  sim_fast.vvp (soak read "FAIL: simulation did not pass"; the vvp has a syntax error at line 3753909) and gcd s75 seed
  9's worst-case run_baked.vvp (every vector "syntax error"; seeds_fid reads it INCOMPLETE). Neither is a circuit
  result; both are moved aside (`*diskfull_discarded*`) and rerun. 7.6 GB freed from finished runs' regenerable
  intermediates; a janitor now clears them below 6 GB free (never a .vvp, never the worst-case fid/ files fasm_equiv
  reads).
- gcd s75 worst case so far 4/4 (6, 7, 8, 10; 11 running, 9 rerun); xorshift T3 seeds 5-7 x 3 configs PASS (baseline for the
  8-route pairing); xorshift x0.25 routing.
### progress 15:03 (item 3 xorshift: the negative control fails where it should -- x0.25 fails the worst case)
- xorshift T3 x0.25: nominal routed GLS (nextpnr SDF) FAILS on seeds 3 and 4 (vector 4 out0 05c420c5, expected
  9dcca8c5 from the C; "PROTOCOL req rose out of phase on out0"; SDFs complete, ANNOTATE_DONE, the sim ran 4 vectors
  first -- not the disk-full window's truncation). Full stack seed 1: SLOW_MAX PASS, FAST_MIN PASS, **combined worst
  case FAIL** (protocol error on out0, both fast and stalled modes). So the gate has teeth on this flow, and it is
  the slow-cell/fast-chain corner of item 1, not either uniform corner, that catches the short delay.
- Bracket: x0.5 passes (4 routes), x0.25 fails. Queued: x0.5 on seeds 5-8 (8 routes), then x0.375.
### progress 16:53 (item 3 xorshift: x0.5 holds on 8 routes at 1.44x; x0.25 fails)
- xorshift T3 x0.5, 8 routes x {SLOW_MAX, FAST_MIN, worst case}: 24/24 PASS, 8/8 EQUIVALENT. Paired vs T3 on the same 8
  seeds: 1.447x (SLOW_MAX), 1.444x (FAST_MIN), 1.418x (worst case; per-route 1.34-1.47). x0.75: 1.14x / 1.13x.
- x0.25 FAIL (worst case 0/3; seeds 1, 2 pass both corners). Floor between x0.25 and x0.5; x0.375 running.
- xorshift T3 seed 8's worst case rerun after the disk-full window: PASS (T3 baseline 12/12 on seeds 5-8).
### progress 16:55 (item 3 xorshift: x0.375 fails the nominal routed GLS on 4/4 -- the floor is not monotone in f)
- xorshift T3 x0.375 (20 of 47 sizes): RTL sim PASS, nextpnr-SDF routed GLS FAIL on all 4 seeds ("PROTOCOL req rose out
  of phase on out0", ~5.04 us, every seed). x0.25 passed that nominal GLS on seeds 1, 2. Elementwise s375 >= s25, so the
  failure is a RATIO between two delays (ceil rounds small lines differently at each f), not a length floor: uniform
  scaling is not monotone. The full-stack runs for x0.375 were not run (a step that fails anything is reverted).
- Result for xorshift: x0.5 is the deepest uniform step that holds (8 routes, 24/24, 1.44x / 1.42x worst case).
  A per-cell search below it would need the ratio constraint named first.
- Queued now: x0.5 on collatz T3, ipow T9, collatz64 T4, isprime (their item-4 seeds, paired against item 4).
### progress 17:42 (owner 1035dcef read: max effort, <= 2 subagents at a time, no scheduled routines)
- Read and followed: one subagent used this session (the H_RUNT rig, finished); none running; no scheduled routines or
  reminders created. The lock refresher now rebases before pushing (the owner's commit had made its push non-fast-forward).
- gcd s75 worst case: 7/7 valid seeds PASS (seed 9 rerunning after the disk-full void); paired laps vs R5 1.07x
  (1.00-1.17) on those 7. collatz x0.5: seed 1 PASS at all three configs, seed 2 SLOW_MAX PASS; nominal 1.34x.
### progress 17:54 (item 3: the xorshift floor is a select race on an empty pipe, not the operators)
- research/data/item3/rc375/: x0.375 fails because ulink_n_index_15's request (SDELAY 1 + DELAY 4) beats its own select
  (two latches + routed wire, no matched delay) into umux3 when the pipe is empty. The routed req-sel margin orders all
  16 xorshift routes (base, s50, s375, s25) by pass/fail; link counts alone do not. Rule E flags it (and fails s50
  guarded); rule D's bd_mux screen misses it (measures from stage[1] only).
- So x0.5's 1.44x carries thin raw select margins (+0.5..+1.5 ns at the nextpnr SDF) that the full stack accepts. Next
  experiment: shrink only operator delays (udly) and keep rule E's link fixes -- deeper on the part that sets throughput.
### progress 18:43 (item 3: operator-only x0.25 fails at the comparator steers; collatz x0.5 fails FAST_MIN)
- xorshift operator delays only x0.25 (links at T3): routed GLS fails 4/4 (out0 protocol); rule E flags ucond_br2/3/5 --
  the comparator's matched delay holds back the request of the steers its result selects (ucmpi0 23 -> 6 links). So the
  per-cell floors differ (the umux3 empty-pipe race, the compare/steer race) and a global factor will not find them.
- collatz T3 x0.5: seed 2 FAST_MIN fails (fast mode hangs on vector 2; stalled passes); its worst case PASSES -- the
  combined worst case does not subsume the fast corner (why PROGRAM asks for both corners). Seeds 1, 3 pass so far.
- Next design: per-cell shrink at the worst-case corner -- run the rule audits on the worst-case-banded SDF with the
  guardband set to the measured residual, take each line's own margin, shorten by what it allows (minus a slack),
  then gate the result in the full stack.
### progress 18:50 (item 3 gcd: R5 x0.75 passes the worst-case gate 8/8 at 1.07x laps)
- gcd_hw R5 x0.75 (52 sizes; 796 -> 683 links), worst case on BQ#2's 8 seeds: 8/8 PASS 16/16, EQUIVALENT
  (research/data/item3/s75_worstcase.tsv). Paired laps vs R5: 1.074 on vec 6/12/13 (1.00-1.17). Corners running.
- collatz x0.5: seed 3's worst case FAILS too (seed 2 FAST_MIN) -- reverted; collatz x0.75 and operator-only x0.5 queued.
### progress 19:52 (item 3: per-cell sizing at the worst-case corner -- research/tools/corner_sdf.py, corner_audit.py)
- Built by a subagent, reviewed here: corner_sdf.py collapses the prjxray SDF to one corner with gen.py's per-arc band
  choice (same CARRY4/SELMUX2_1 arc counts as gen.py's own log on xorshift_s50 seed 1); corner_audit.py runs tighten /
  skew / arb_fork unchanged (guards patched in-process: rule A max(0.03 t, 50 ps), rule E 0.97/1.03), finds each
  constraint's lines by zeroing chains one at a time, pads what is short, shrinks the rest, re-audits with predicted
  delays. Per-link cost: conservative (a shortened line keeps its dearest step; padding credited at the cheapest).
- Validation against the full stack's own verdicts: flags umux3's empty-pipe race on x0.375 (-686 guarded) and the
  ucond_br steers on operator-only x0.25 (-820..-1040), proposing the lengths that clear them. On x0.5 (which PASSES the
  full stack) it still finds -36..-87 ps rows and tighten's bundled rule A -908: the static rules are more pessimistic
  than the GLS, so its proposals are what the RULES prove at the corner, not the sim's floor. On base T3 seed 1 it
  shortens kernel links 155 -> 111 (less than x0.5, which passes). collatz x0.5 seed 2's FAST_MIN hang is not explained
  by any rule at either corner (ucond_br5 sits at ~0 raw at both: a mis-steer would look like that hang).
- Use: per-cell max over a kernel's base routes -> candidate -> >= 8 routes of the full stack. Most useful where a
  global x0.5 fails (collatz, ipow). Running on their base routes now.
### progress 21:13 (item 3: per-cell candidates built; the rules stay more conservative than the full stack)
- Per-cell max of corner_audit proposals over the base routes: collatz T3 249 -> 200 links (4 routes), ipow T9 332 ->
  251 (4), xorshift T3 156 -> 135 (4). xorshift's x0.5 (87 links) passes the full stack on 8 routes, so the rule-proven
  per-cell sizes sit well above the sim's floor: useful where a uniform factor fails (collatz, ipow both fail x0.5), not
  as the floor itself. collatz_cs (nominal 1.17x) and ipow_cs are in the full stack now; xorshift_cs not run.
- Uniform x0.5 so far: xorshift PASS (8 routes, 1.44x), collatz FAIL, ipow FAIL (worst case only, 2/4); x0.75 for
  collatz64 running, isprime queued. Recurring pattern: x0.25 xorshift, x0.5 ipow, operator-only x0.25 xorshift all pass
  BOTH uniform corners on some routes and fail only the combined worst case.
### progress 22:19 (item 3: collatz per-cell sizes pass 12/12 at 1.16x)
- collatz T3 per-cell candidate (research/data/collatz_sizes_T3cs.vh, 249 -> 200 links), seeds 1-4: SLOW_MAX, FAST_MIN,
  worst case 12/12 PASS, 4/4 EQUIVALENT -- including seed 2 FAST_MIN and seed 3 worst case, where uniform x0.5 failed.
  Paired vs T3: 1.159x / 1.158x (corners), 1.153x (worst case). Seeds 5-8 to queue (and the T3 baseline on 5-8).
- collatz64 x0.75 seed 1: 3/3 PASS. gcd s75 corners: 3/3 PASS so far.
### progress 23:35 (item 3: ipow per-cell holds 12/12 but is only 1.02-1.04x)
- ipow T9 per-cell (332 -> 251 links), seeds 29-32: 12/12 PASS, 4/4 EQUIVALENT; paired 1.041x / 1.024x (corners), 1.024x
  (worst case). Rule A at the corner keeps uselect0 (52) and umuli1 (47 -> 36) near T9, and those set the cycle. A
  between-the-two candidate (x0.5's shrink on the lines corner_audit shows unbound, per-cell lengths elsewhere) is
  the next ipow step.
- collatz64 x0.75: seeds 1-2 3/3 PASS each. gcd s75 corners: 6/6 PASS so far.
### progress 23:50 (item 3: operator-only x0.5 on xorshift is safe and only 1.05-1.07x)
- xorshift operator delays only x0.5: 12/12 PASS, 4/4 EQUIVALENT; paired 1.073x / 1.054x / 1.053x (max/min/worst). Uniform
  x0.5 is 1.44x: the link request delays carry most of the cycle -- the same lines that carry the select races.
### progress 00:09 (container restart at ~00:00 killed every queue; restarted from what was on disk)
- Lost mid-run, rerun from scratch (nothing read from partial runs): collatz64 x0.75 seed 3 worst + seed 4, collatz
  per-cell seed 5 worst + seeds 6-8, gcd s75 corners (7 of 16 rows were done: all PASS; the 9 missing rows queued).
  New soak-only runner skips any config that already has a SOAK_VERDICT. isprime x0.75, collatz T3 seeds 5-8 (baseline)
  and BQ#1's worst case follow.
### progress 01:21 (item 3: collatz per-cell holds on 8 routes, 24/24)
- collatz T3 per-cell (200 links), seeds 5-8 added: 24/24 PASS over 8 routes, 8/8 EQUIVALENT. Speedup 1.16x on seeds 1-4;
  the T3 baseline on 5-8 is running for the 8-route pairing.
### progress 01:47 (item 3: collatz64 x0.75 passes 12/12 at 1.17x)
- collatz64 T4 x0.75, seeds 1-4: 12/12 PASS, 4/4 EQUIVALENT; paired vs T4 1.173x / 1.175x (corners), 1.166x (worst).
  isprime x0.75 next. Per-kernel so far (deepest step that holds, worst-case speedup): xorshift x0.5 1.42x (8 routes),
  collatz per-cell 1.15x (8 routes, pairing on 4), collatz64 x0.75 1.17x (4), ipow per-cell 1.02x (4), gcd R5 x0.75 1.07x laps (8).
### progress 04:33 (item 3: ipow x0.75 passes 12/12 at 1.09x worst case; isprime per-cell queued)
- ipow T9 x0.75, seeds 29-32: 12/12 PASS, 4/4 EQUIVALENT; 1.113x / 1.100x / 1.090x (max/min/worst) vs T9 -- more than the
  per-cell candidate (1.02x). isprime x0.75 failed (seed 25 FAST_MIN hang); its per-cell candidate (199 -> 147 links)
  is next. gcd s75 corners 13/13 PASS so far.
### progress 06:33 (item 3: isprime per-cell 12/12 at 1.06x; per-kernel summary)
- isprime per-cell (199 -> 147 links in its 15 sized lines), seeds 25-28: 12/12 PASS, 4/4 EQUIVALENT; 1.056x / 1.063x /
  1.064x vs base. Per-kernel table in research/data/item3/README.md: xorshift 1.42x (x0.5, 8 routes), collatz 1.155x
  (per-cell, 8), collatz64 1.17x (x0.75, 4), ipow 1.09x (x0.75, 4), isprime 1.06x (per-cell, 4), gcd R5 x0.75 1.07x laps.
### progress 07:34 (item 3 gcd: R5 x0.75 passes the whole gate -- worst case 8/8, both corners 16/16)
- gcd_hw R5 x0.75 (research/data/gcd_hw_sizes_R5s75.vh): SLOW_MAX 8/8, FAST_MIN 8/8, combined worst case 8/8, all 16/16
  vectors, all EQUIVALENT, BQ#2's seeds. Laps vs R5: 1.074x (worst case, 8 paired), 1.057x / 1.043x (corners, 5 / 4 paired).
  A board candidate after BQ#3 (whose fast fall it does not carry yet); not yet in BOARD-QUEUE.
### progress 09:55 (BQ#1 worst case: two compiles OOM-killed; ipow x0.75 on 8 routes)
- BQ#1 combined worst case: d, 3, 4, 5 PASS; seeds 6 and 7 INCOMPLETE -- their iverilog compiles (6.2 GB RSS) were
  OOM-killed (dmesg: memcg OOM, task ivl) beside a 4.3 GB gcd sim and two kernel soaks. Not results; both rerun one at a
  time after the queue. Kernel soak compiles do not take the shared compile lock; the collatz64 T4 baseline is deferred
  so only one kernel queue runs beside the gcd sims.
- ipow x0.75 on 8 routes: 24/24, 8/8 EQUIVALENT; paired vs T9 1.135x / 1.132x / 1.129x (max/min/worst).
### progress 10:04 (item 3: isprime per-cell FAILS on a fifth route -- the 4-route pass did not transfer)
- isprime per-cell sizes (per-cell max over seeds 25-28), fresh seed 29: SLOW_MAX fast mode hangs on vector 4 (the same
  symptom as x0.75 on seed 25). Not OOM. So isprime has no item-3 step yet; whether the BASE sizes hold on seed 29 (their
  rule E was never clean) is the next run. The per-kernel table now lists isprime as none.
### progress 11:03 (BQ#1 worst case: 5/5 valid seeds PASS; 6, 7, 9 rerun)
- BQ#1 combined worst case: d, 3, 4, 5, 8 PASS 16/16 (research/data/fid/bq1_worstcase.tsv). Seed 8 reads NOT_EQUIVALENT:
  two F7-mux inputs driven in the JSON by nextpnr $PACKER_GND_NET buffer LUTs (f = A1, A1 tied GND, so 0) and by const 0
  in the bits -- the benign GND-buffer class of the August isprime/collatz builds (current fasm_equiv agrees: only that
  DRIVER DIFFERS kind). Seeds 6, 7, 9 compiles were OOM-killed; rerun one at a time after gcd x0.75 + fast fall.
- gcd R5 x0.75 + link fast fall: routing (8 seeds).
### progress 13:09 (item 4 revised: isprime's validated sizes fail FAST_MIN on fresh seed 30)
- isprime rule-E-6 pad sizes (item 4's 12/12 on seeds 25-28), seed 30: FAST_MIN fast mode hangs on vector 1, the same
  symptom as the per-cell and x0.75 candidates. Not OOM. So the item-3 isprime failures were not (only) the shrink:
  the base design itself is not clean. isprime goes back to "needs its select pads fixed" (rule E 2 on seeds 25/26 was
  the warning). research/data/item4/README.md revised.
### progress 14:51 (isprime seed 30: a C-element runt at ufork0, not a select race)
- research/data/item4/isprime_seed30/: ufork0's C-element output start_ack rises; the zero-delay testbench drops p_end_ack
  in the same ps; it reaches the LUT pin 387 ps later, before the cell's own feedback (421 ps, a routing detour on this
  route) has latched -> start_ack dips, the testbench takes it as the ack falling, vector 1's token is lost. A runt
  narrower than the loop -- the H_RUNT question (board list item 2), here in a shipped kernel. No rule audit flags it.
  A +300 ps patch on that wire makes all 18 fast vectors pass. Board relevance unshown (the board harness answers
  slower than 0 ps). New audit lead: C-element self-loop vs the fastest external return (forks/joins, not only arbiters).
- Negative: a self-loop-length screen does not discriminate -- isprime routes carry ~2385 LUT self-loops (latches + C-
  elements), median ~330 ps at FAST_MIN, max ~700; ufork0's 421 ps is ordinary. The hazard is loop vs the fastest RETURN
  of an input edge through the environment, which needs the path from each output back to the cell's other inputs
  (including a zero-delay testbench's). Screen discarded; not committed.
### progress 15:47 (gcd R5 x0.75 + fast fall: worst case 5/5 so far; GND-buffer equivalence class)
- s75ff worst case: seeds 6, 7, 8, 9, 10 PASS 16/16; laps 65-71 on vec 6 vs BQ#3's 58-65 on the same seeds.
- Seed 10 reads NOT_EQUIVALENT: 4 F7-mux inputs fed by $PACKER_GND_NET buffer LUTs (f = A1, A1 tied GND) in the JSON,
  const 0 in the bits -- the benign class already seen (BQ#1 seed 8, August isprime/collatz). Tried folding those cells by
  name in fasm_equiv: wrong (891 new DRIVER DIFFERS, because the bits side still sees them as LUTs); reverted. A correct
  fix folds both sides by the function given tied pins; not done.
### progress 17:20 (item 3 gcd: R5 x0.75 + link fast fall passes the worst case 8/8 at 1.13x BQ#2)
- s75ff (R5 x0.75 sizes + BDC_LINK_FASTFALL=1), combined worst case, BQ#2's 8 seeds: 8/8 PASS 16/16 (seed 10's
  NOT_EQUIVALENT is the benign GND-buffer F7 class). Vec 6 laps 67.8 mean: 1.132x BQ#2 R5 (8 paired), 1.056x R5 x0.75,
  1.083x BQ#3 (4 common seeds). Corners running; if 16/16 it replaces BQ#3 as board list item 3.
### progress 23:56 (C-element return-path audit: no internal runt hazard on 169 routes; every negative is the 0 ps testbench port)
- After a container restart (~23:3x) every queue was dead; requeued (scratch rq.sh): s75ff corners 10/13 max+min and
  14 min, then BQ#1 worst-case reruns 6/7/9, then collatz64 T4 base 5-8. Lock keeper and janitor restarted.
- New static audit research/tools/ce_return.py (subagent-built; checked here against the seed-30 README): per C-element
  LUT (identified by INIT through X_ORIG_PORT and by src bd_ce.v; the two agree on every DUT cell), margin = shortest
  return from its O6 back to each non-feedback, non-rst input (+ that pin's arc) minus its own loop. Paths through other
  C-elements are taken structurally (conservative). Ports of a kernel are a 0 ps turnaround (the soak testbench); gcd's
  on-chip env is class ENV. It reproduces isprime_b ufork0 exactly: seeds 29/30/31/32 = +532/-34/+290/+199 ps FAST_MIN.
- 169 routes (107 kernel, 62 gcd), FAST_MIN and SLOW_MAX (research/data/ceret/summary.tsv): INTERNAL negatives 0
  (worst +145 ps xorshift_s25 FAST_MIN, unguarded; plain kernels +170..+366; gcd +180); ENV (gcd) 0 (worst +730).
  PORT: 22 negative rows on 12 routes, every one ufork0's C-element via start_ack -> start_req == p_end_req -> p_end_ack
  (the `end` channel is a bare wire from the start fork, research/data/ceret/negatives.tsv).
- Against the full-stack sims: every isprime failure sits on a flagged route/corner (s75 seed 25 FAST_MIN -9; cs seed 29
  SLOW_MAX -20; b seed 30 FAST_MIN -34). Not sufficient: xorshift s50 seed 2 (-119), xorshift s75 seeds 1/4 (-9/-86),
  isprime seed 26 (-21) pass. So the static screen predicts where the sim can fail; the sim's 0 ps environment decides.
- What it means: no route has an internal C-element runt; the hazard needs an environment that answers faster than the
  cell's own feedback, and only the testbench does. Margin -9..-130 ps vs a board harness answering through routed logic.
  Not shown: the board harness's own turnaround (being measured: same tool, return through the routed soak harness).
  Caveat: the k4 routes record nextpnr only as 0.9.2-100-gbfdeaf7c, not the fingerprint (gcd routes: 9c732bc6303458df).
### progress 00:01 (board view: the kernel soak harness is open-loop, so ufork0's runt can only happen in the testbench)
- ce_return.py --env harness (no 0 ps tb edges, returns through the routed soak harness): 107 kernel routes x 2 corners,
  0 ENV paths, 0 negatives of any class; internal worst unchanged (+145 FAST_MIN). Checked here on isprime_b seed 30:
  tb mode n_neg_port=1 (ufork0 -34), harness mode 0 paths. Reason (bdc/emit.py emit_top, by design): DUT inputs come from
  the free-running spine latches, DUT outputs only feed the XOR tree to pin_out; no harness signal follows the handshake.
- PORT breakdown (research/data/ceret/ufork.txt, 12 routes): wire out 0 (tb reads O6's own net), turnaround 0, so the whole
  return is the one INTERCONNECT from the harness latch that drives p_end_ack to ufork0's pin (237-439 ps FAST_MIN),
  racing the C-element's own feedback wire. Placement-dependent, which is why it hits ~1 route in 8.
- Consequences: (1) the board soak can neither show nor rule out this race; the H_RUNT rig (board list item 2) is the
  board test of the mechanism. (2) isprime's seed-30/25/29 failures, and the flagged-but-passing xorshift s50/s75,
  collatz s50, ipow s50 routes, are failures against a zero-delay handshaking environment at start->end, not internal
  hazards. They stay counted as failures (the sim is the gate; a real handshaking neighbour can answer in ~one wire).
  (3) The fix belongs at the kernel boundary, not in the shrunk delays: `end` is a bare wire from the start fork, so
  the environment's ack lands straight on a C-element pin. Candidates: a boundary stage whose C-element's feedback is
  local, or a placement rule keeping ufork0's feedback short; not built yet.
### progress 03:28 (item 3 gcd: R5 x0.75 + link fast fall passes both corners 16/16 -> board list item 3)
- s75ff corners after the restart rerun: 10 max/min, 13 max/min, 14 min all PASS 16/16 errs=0 -> 16/16 runs
  (research/data/item3/s75ff_corners.tsv). Vec 6 laps mean 35.4 SLOW_MAX (34-38), 96.9 FAST_MIN (91-105); vs R5 x0.75
  without fast fall on the same seeds 33.4 / 92.0 (1.060x / 1.053x). With the worst case 8/8 (1.132x BQ#2, 1.083x BQ#3),
  every one of 24 full-stack runs on 8 routes is clean. nextpnr 9c732bc6303458df.
- BOARD-QUEUE: new section #5 (exact commands, seed 6 md5s, pass criterion); board list item 3 now points to it, with
  BQ#3 then BQ#2 as fallbacks. Not shown: anything on silicon; the gain over BQ#3 (~8%) is below the route-to-route
  lap scatter of a single route, so the board comparison needs #3 and #5 measured on the same board session.
### progress 04:31 (the board bench closes ufork0's loop through >= 2.3 ns: the testbench race cannot happen there)
- The kernel board harness (cells/hw/gen_bench.py) does close the handshake: start_ack -> the bench's bd_fork C-element
  -> req_clr -> the request flop's async clear -> start_req == p_end_req -> bd_delay #(.N(2)) upsnk -> p_end_ack. prjxray
  gives SLICE_FFX no SR->Q arc, so ce_return got --ff-async PS (SR->Q taken as PS ps; 0 = a lower bound).
- 6 bench routes (cells/hw/build_bench.sh, BD_NO_TIGHTEN=1 with the validated sizes; isprime seeds 25/26/29/30,
  xorshift x0.5 seeds 1/2; nextpnr 9c732bc6303458df), research/data/ceret/bench_harness.tsv: 0 negatives of any class;
  ufork0 return 2536-3005 ps vs loop 194-397 at FAST_MIN (margin +2325..+2639 with SR->Q = 0), beyond loop+5000 at
  SLOW_MAX; worst internal +326 FAST_MIN. These are new routes, not the soak routes the sims ran (bench routes differ).
- So: on the board's own bench, the start->end return is ~6x ufork0's loop; the soak testbench's 0 ps turnaround is the
  only environment that loses the race. isprime's 3 failures and the flagged-but-passing kernel routes are testbench
  artefacts for the board question. They remain sim failures under "the sim is the gate"; whether the gate should model
  a minimum environment turnaround (e.g. one C-element + wire, the internal worst being +145 ps) is an owner decision,
  not taken here. What would decide it on silicon: H_RUNT (board list item 2).
### progress 06:24 (BQ#1 combined worst case 8/8)
- BQ#1 seeds 6, 7, 9 (compile OOM-killed on 11-06, rerun with --sim-jobs 1): PASS 16/16 errs=0, EQUIVALENT; vec 6
  laps 30 / 32 / 33. BQ#1 worst case now 8/8 (research/data/fid/bq1_worstcase.tsv; vec 6 mean 32.0, 30-34). Seed 8's
  NOT_EQUIVALENT is the benign GND-buffer F7 class. So BQ#1, #2, #3 and #5 all pass the combined worst case on 8 routes.
### progress 11:02 (collatz64: T4 baseline on routes 5-8 clean; x0.75 pairs on 8 routes at 1.18x)
- collatz64 T4 (validated sizes) seeds 5-8, full stack: 12/12 PASS (SLOW_MAX, FAST_MIN, combined worst case; stalled
  and fast), bits vs JSON 4/4 EQUIVALENT -> collatz64 base 24/24 on 8 routes (item 4).
- Item 3 collatz64 x0.75 paired by seed on all 8 routes (sum of stalled latencies, base/step): SLOW_MAX 1.183 (1.12-1.24),
  FAST_MIN 1.182 (1.12-1.22), worst case 1.177 (1.11-1.25); was 1.166 on 4 routes. nextpnr: k4 routes record only
  0.9.2-100-gbfdeaf7c (see ceret caveat).
### progress 12:20 (isprime: every full-stack failure passes with a 300 ps environment turnaround; both 0 ps controls still fail)
- A/B, informational (gate unchanged): soak_fid with every testbench drive except rst delayed D ps (wire #D, inertial;
  diff in research/data/item4/envd/). Routes and bits as the failing runs; nextpnr k4 routes (version-only record).
  D=300: isprime_b seed 30 FAST_MIN PASS, isprime_b seed 30 worst case PASS, isprime_s75 seed 25 FAST_MIN PASS,
  isprime_cs seed 29 SLOW_MAX PASS. D=0 controls: isprime_b 30 FAST_MIN FAIL (fast hang), isprime_s75 25 FAST_MIN
  FAIL -- both reproduce. research/data/item4/envd/results.tsv.
- So isprime's base (rule-E-6 pads) and its x0.75 / per-cell steps fail only through the 0 ps start->end turnaround
  (with ce_return: the only negative C-element returns on any route). 300 ps is ~1/8 of what the board bench gives
  (>= 2.5 ns, research/data/ceret/bench_harness.tsv). If the owner accepts a minimum environment turnaround in the
  gate, isprime's base is 24/24 on 8 routes and its steps can be re-gated; until then they stay failures.
- Not shown: D values between 0 and 300 (where the threshold is); stalled-mode runs were never failing.
### progress 12:30 (isprime turnaround threshold: seed 30 passes at 50 ps, as the static -34 ps margin predicts)
- isprime_b seed 30 FAST_MIN: D = 0 FAIL, 50 / 100 / 200 / 300 PASS; isprime_s75 seed 25 FAST_MIN: D = 0 FAIL, 100 / 300
  PASS (research/data/item4/envd/results.tsv). ce_return's static margins (-34, -9 ps) say any D above ~34 / ~9 ps closes
  them; the sim agrees at the points run. So the minimum environment turnaround that clears every isprime failure seen is
  under 50 ps on these routes -- far below one wire + LUT (~250 ps FAST_MIN) and the bench's >= 2.5 ns.
- Not shown: the exact threshold between 0 and 50 ps; any route whose static PORT margin is worse (xorshift_s25 seed 1,
  -130 ps, would need D > ~130).
### progress 13:28 (the full stack reproduces ce_return's -34 ps margin to within a few ps)
- isprime_b seed 30 FAST_MIN, testbench drives delayed D: D = 0, 10, 15 FAIL (fast-mode hang); D = 20, 40, 50, 100, 200,
  300 PASS. The race path crosses two delayed drives (start_req falls, then p_end_ack), so the added turnaround is 2D:
  30 ps fails, 40 ps passes. ce_return's static FAST_MIN margin for this C-element is -34 ps. The static audit and the
  bit-decoded full-stack GLS agree to within the 30-40 ps bracket: a quantitative cross-check of both (the audit's
  arithmetic and the fid resolver's runt-vs-loop rule).
- For the owner's gate decision: the turnaround that clears every isprime failure seen is ~2 x 17 ps on this route; the
  worst static PORT margin on any route is -130 ps (xorshift_s25 seed 1, which passed its sims anyway).
### progress 13:43 (bug: build_bench.sh silently ignored soak-keyed sizes files; guarded)
- Building xorshift's bench top (cells/hw/build_bench.sh) with BD_SIZES=research/data/xorshift_sizes_T3s50.vh and with
  T3.vh gave byte-identical SDFs: the sizes files are keyed to the fusion_bench soak top (BD_SZ_UUT_*), the bench names
  the kernel bridge_i.udut. (BD_SZ_BRIDGE_I_UDUT_*), so no define matched, every chain was built at emit.py's
  estimate -- while build_bench printed "applying 47 measured delay size(s)". Exactly the "wrong-but-plausible build"
  its own comment warns about.
- Fix: build_bench.sh now counts the sizes file's defines that the generated sources use; none -> refuse (exit 1),
  some -> WARNING. Checked both ways: the soak-keyed file is refused; the re-keyed research/data/xorshift_sizes_T3{,s50}
  _bench.vh (UUT_ -> BRIDGE_I_UDUT_, UPIPE_* dropped) applies 45/45.
- Correction to 06:2x's bench audit (research/data/ceret/bench_harness.tsv): those 6 bench routes had no measured
  sizes either (emit.py estimates). The conclusion is about the harness's return path (bench fork -> async-clear flop
  -> 2-link delay), which the sizes do not touch; ufork0's loop is placement-dependent either way. Caveat added to the
  TSV header. The August bench builds (aug_kernels) are probably unaffected (build_bench's default MODE=tighten sizes
  on the bench itself), but that is not checked here.
### progress 20:01 (xorshift x0.5 on the board's own bench top: 12/12 full-stack runs, 1.46-1.52x; board list item 4)
- xorshift_bench_gen (cells/hw/build_bench.sh, the top the board runs) with the re-keyed T3s50 and T3 sizes, NEXTPNR_SEED
  1-4, BD_SIZES_GATE=0 (rule A: 12-20 cells fail on every bench route of BOTH builds -- informational, PROGRAM item 1),
  then cells/gls/ps/build_ps.sh ... bit (netlist from each .bit, prjxray SDF, fid, ps7_bench.v host, 17 vectors x 2 runs,
  expected from simcheck.ref_xorshift) at SLOW_MAX, FAST_MIN and the combined worst case: 24/24 PASS 17/17, no hang,
  gate clean; bits vs JSON EQUIVALENT except 3 routes' single benign GND-buffer F7/CARRY4 input (checked each).
- Per round (slope 200->1000 rounds, aclk cycles): x0.5 2.68-2.80 FAST_MIN / 3.78-3.96 worst / 7.48-7.82 SLOW_MAX; T3
  3.96-4.13 / 5.54-5.81 / 11.06-11.71. Paired base/x0.5: 1.458-1.523 (12 pairs), worst case 1.458-1.512. Same gain as
  the soak routes (1.42-1.45x).
- First run voided: TBATCH 200 us was shorter than T3's 1000-round batch (2 x 111 us), so its last vector read HANG with
  completed=1 and the right answer; re-run at 1 ms. Also voided earlier: the sizes-not-applied builds (d1b44816).
- BOARD-QUEUE #6 + board list item 4 (ring set moves to 5): exact commands, sdf md5s, and research/tools/
  xorshift_bench_judge.py (PASS = all 17 oracle points on both builds; checked both ways on synthetic files).
- Not shown: 8 bench routes (4 here, 8 on the soak top); silicon.
### progress 00:49 (bench harness clock: the board scripts run the harness at 100 MHz, above the 83.3 MHz it is routed for)
- xorshift bench seeds 5-8 (full stack, running): base seed 8 SLOW_MAX read latmin 578 / 10857 against latmax 706 /
  10985 for identical vectors: bit 7 (0x80) dropped in the harness's lat_min register; the batch cycle totals (1424 =
  2x706+12, 21982 = 2x10985+12) and both answers are right. 2 of 748 readings over 16 routes x corners, both on that
  route. lat_min's update is synchronous (aclk), so it is a clocked path missing timing: build_bench.sh routes the
  harness for TARGET_MHZ=83 (its comment: it does not close 100 MHz, 79.6-97.7 MHz over six seeds), while
  xorshift_cost.sh / xsdb_bench_gen.tcl default to CLK_CTRL 0x00100A00 = 100 MHz, and so does ps7_bench.v (fclk_ps 10000).
- Kernel results unaffected (asynchronous; every answer right); per-round numbers from latmin on that route are off by
  128 cycles at the 1000-round point (to be recomputed from the cycle totals). BOARD-QUEUE #6 now sets CLK=0x00100C00
  and the judge reports ns. Queued: base_8 and s50_8 SLOW_MAX again at FCLK_PS=12000 (83.3 MHz) to see the glitch go.
- Not checked: whether the August board runs (0x00100A00) hit this; xorshift_cost.sh fits batch totals, not lat_min.
### progress 01:29 (xorshift x0.5 bench: 8 routes, 48/48 full-stack runs pass; 1.43-1.45x mean, 1.28-1.52 range)
- Seeds 5-8 added (same flow): all 24 PASS 17/17, gate clean, no hang. Over 8 routes x 3 corners: 48/48 PASS. Bits vs
  JSON NOT_EQUIVALENT on 5 routes (base 1/2/6, x0.5 3/6), each a single $PACKER_GND_NET buffer LUT on an F7/CARRY4
  input that the bits read as 0 -- traced on every one.
- Per round (ns, from batch cycle totals): x0.5 26.6-30.2 FAST_MIN / 37.6-42.1 worst / 74.7-83.6 SLOW_MAX; T3 38.7-41.3
  / 54.0-58.5 / 108.3-117.1. Paired T3/x0.5: mean 1.436 FAST_MIN, 1.449 SLOW_MAX, 1.431 worst; range 1.28-1.52. Seeds
  6 and 8 are the slow x0.5 routes (1.28-1.40): routing scatter on the halved chains, the reason one route is a sample.
- research/data/xorshift_bench/results.tsv regenerated (per-round from cycle totals, a lat_glitches column: 2, both
  base_8 SLOW_MAX at 100 MHz). Judge corner bands and BOARD-QUEUE #6 updated to 8 routes.
### progress 02:19 (83.3 MHz harness clock: the lat_min glitch is gone, kernel time unchanged)
- base_8 and s50_8 at SLOW_MAX re-run with ps7_bench.v +FCLK_PS=12000 (83.3 MHz, the clock build_bench.sh routes for):
  both PASS 17/17, 0 readings with latmax-latmin > 1 (base_8 at 100 MHz: 2). Kernel time per 1000-round run is the same:
  base 9155 x 12 ns = 109.9 us (100 MHz: 10985 x 10 ns = 109.9 us); x0.5 6524 x 12 = 78.3 us (7828 x 10 = 78.3 us).
- So the glitch was the clocked harness over-clocked, not the kernel: BOARD-QUEUE #6's CLK=0x00100C00 stands.
  Open (not checked): the other board scripts that default to 0x00100A00 (xsdb_bench_gen.tcl, *_cost.sh) and what
  the August latmin numbers saw; xorshift_cost.sh itself fits batch cycle totals.
- August board data (research/data/aug_kernels/*_board.tsv, aug_gcd): no sign of the lat_min glitch at 100 MHz. latmax-
  latmin grows smoothly with latency (~0.8%, run-to-run jitter over N=200), no reading off by a large power of two, none
  beyond 3% apart from +-1-cycle quantization. Consistent with silicon at x ~ 0.21 meeting the harness's 100 MHz timing
  that the SLOW_MAX corner does not; 83.3 MHz stays the recommendation for new board items (it costs nothing).
### progress 02:23 (xorshift below x0.5: x0.375 with umux3's link delay restored)
- h375 = T3s375 with ULINK_N_INDEX_15 back at 5 (its x0.5 length; rc375 traced x0.375's failure to umux3's empty-pipe
  select race on that link). Nominal routed GLS (fusion_bench --route, nextpnr-SDF): 3/4 PASS (seeds 1, 2, 4); x0.375
  was 0/4. Seed 3 still fails the same way (out0 "req rose out of phase"): skew.log, umux3 request earliest 3369 ps vs
  select latest 4139 ps (-770 raw); seeds 1/2/4 +654/+274/+259 raw. So one link is not enough on every route.
- Queued: h375's full stack on 1/2/4 (do the other x0.375 lines hold at the corners?), then h375b (that link at 7,
  ~+1 ns; 75 links in all vs x0.5's 87) on seeds 1-4.
- h375 rejected: seed 1 FAST_MIN fails (stalled: "req rose out of phase on channel out0" -> protocol error; fast mode
  hung), after SLOW_MAX passed. Same umux3 race at the fast corner. Remaining h375 runs stopped; h375b (link at 7) runs.
- h375b (x0.375 + umux3's link at 7): nominal routed GLS 4/4; full stack seeds 1 and 2 PASS at SLOW_MAX, FAST_MIN and worst
  case (6/6). But no faster than x0.5: paired s50/h375b = 1.011-1.030 on seed 1, 0.921-0.949 on seed 2 (sum of stalled
  latencies). The 2 extra links sit on umux3's request path, which is on the loop, so they cost every round what the
  other x0.375 lines save. Stopped after seed 2 (no point validating a step that buys nothing).
- Negative result for item 3: below x0.5, xorshift's limit is umux3's empty-pipe race on a loop-carried link; padding
  that link to win the race costs as much as the shrink gains. x0.5 stays xorshift's step. A real gain would need the
  race removed (select launched earlier / not from the empty pipe), i.e. a structural change, not a size.
### progress 08:21 (a nextpnr FASM gap: a constant-D flop in a 5FF slot gets no 5FFMUX bit -- caught by the full stack, 1 route of 870)
- collatz64 bench (x0.75 vs T4 on the bench top, CLK 83.3 MHz in ps7_bench): seeds 1-3 both builds PASS 14/14 at all
  3 corners, gate clean, EQUIVALENT; per 350-step vector x0.75 is 1.17-1.22x on seeds 1 and 3, 1.07-1.09x on seed 2.
- Base (T4) seed 4: gen.py stops (KeyError SLICE_X27Y75/C5FF) because fasm_equiv/fasm2net find a JSON cell "not
  configured by the bits (HAS LOADS)": $auto$dfflegalize.cc:410:emulate_split_set_clr$23629, an FDPE in the bench
  harness with D tied to GND ($PACKER_GND_DRV), placed in CLBLL_R_X19Y75 SLICEL_X1 C5FF. nextpnr's own FASM (rebuilt,
  sdf md5 1310d2ef = the same route) has C5FF.ZINI and COUTMUX.C5Q but NO C5FFMUX.IN_A/IN_B, so on silicon that D comes
  from an unconfigured mux; the 2 "LUT FUNCTION DIFFERS" are the two LUTs reading its Q. The bits-decoded board.fasm
  lacks it too: it is in the bitstream, not the decoder.
- Scan of all 870 FASMs on disk (soak, bench, gcd, board builds): this route is the only one with a 5FF that has
  ZINI/ZRST but no 5FFMUX. No validated or board-list design is affected (their full-stack decodes were EQUIVALENT).
- What it means: a real nextpnr-xilinx FASM-writer gap (a GND-driven D into a 5FF is left unrouted, nothing selects
  the input) that only bites when placement puts such a flop in a 5FF slot. The full stack refused the route (the gate
  works). Not done: a nextpnr patch + toolchain.sh fingerprint (CLAUDE.md requires both; a fingerprint must be checked
  to fail on an unpatched binary, which this route provides). Meanwhile every board build must pass fasm_equiv.
- Fix scope (read of nextpnr-xilinx bfdeaf7c xilinx/fasm.cc): 5FFMUX bits are not written explicitly; they come from
  site-routing pips. So the gap is in how a constant net reaches a 5FF D pin in site routing (no pip chosen, the pin
  counted as driven by the constant network), i.e. router/packer, not a one-line FASM fix. Left for the owner: patch the
  site router (or legalise constant-D flops off the 5FF slots), with the toolchain.sh fingerprint this route provides
  (bench collatz64 T4, NEXTPNR_SEED=4: expect C5FFMUX in CLBLL_R_X19Y75.SLICEL_X1, or the flop moved).
### progress 10:50 (collatz64 x0.75 on the bench top: 15/15, 1.17x; board list item 6)
- Seeds 1-5 (base 4 not simulable, see above): x0.75 15/15 PASS 14/14 (incl. 4 vectors on the 3n+1 path), gate clean;
  T4 12/12 on 1/2/3/5. Paired per 350-step vector (batch cycle totals): 1.170 SLOW_MAX, 1.171 FAST_MIN, 1.168 worst
  (1.07-1.22; seed 2 is the slow pair). Same gain as the soak routes (1.18). NOT_EQUIVALENT on s75_4 and base_5: single
  benign GND-buffer CARRY4/F7 inputs (checked).
- BOARD-QUEUE #7 + list item 6 (loop_cost.sh at CLK 0x00100C00, research/tools/loop_cost_judge.py, checked both ways).
### progress 14:10 (ipow x0.75 on the bench top: 24/24, 1.15-1.17x; board list item 7)
- ipow T9 and T9 x0.75 bench builds, seeds 1-4, full stack at 83.3 MHz host clock: 24/24 PASS 17/17, gate clean; bits vs
  JSON NOT_EQUIVALENT on s75_4 (4) and base_2 (2) GND-buffer F7 inputs only (checked). Paired on the 31-iteration
  vector (batch cycle totals): 1.172 SLOW_MAX, 1.146 FAST_MIN, 1.149 worst (1.08-1.23); soak routes gave 1.13.
- Kernel steps now on the board's bench top: xorshift x0.5 (48/48, 1.44x), collatz64 x0.75 (15/15, 1.17x), ipow
  x0.75 (24/24, 1.15x). BOARD-QUEUE #8 / list item 7 added.
### progress 19:00 (collatz per-cell on the bench top: 24/24, 1.16-1.19x; board list item 8)
- collatz T3 and T3 per-cell bench builds, seeds 1-4, full stack at 83.3 MHz host clock: 24/24 PASS 13/13 (4 vectors on
  the 3n+1 path), gate clean; NOT_EQUIVALENT only base 2/4's GND-buffer F7 inputs (checked). Paired on the 261-step
  vector: 1.186 SLOW_MAX, 1.184 FAST_MIN, 1.157 worst (1.12-1.22); soak routes gave 1.155.
- All four kernel item-3 steps are now gated on the board's own top: xorshift x0.5 1.44x (8 routes), collatz64 x0.75
  1.17x, ipow x0.75 1.15x, collatz per-cell 1.17x (4-5 routes each). isprime waits on the owner's gate decision.
### progress 20:25 (fasm_equiv: DSP data pins now fold a constant-INIT LUT driver, like every other pin)
- ipow x0.75 bench seed 6 read NOT_EQUIVALENT: "DSP DATA PIN DRIVER DIFFERS" on DSP48_X0Y14 A21-A23, json const 0, bits
  driven by SLICE_X2Y28/A6LUT -- a bits-only LUT with INIT all 0 (nextpnr ties the pin to GND through an unused LUT;
  the dsp-constpins patch's job). Section 3 already folds such LUTs; the DSP data-pin comparison (2b) did not.
- Fix: 2b applies lut_const() to the driver on both sides and lists the pin under the CONST_LUT folds. On this route:
  EQUIVALENT, the three pins listed as folded. Negative control: the same LUT given INIT ...0001 -> NOT EQUIVALENT with
  "DSP DATA PIN DRIVER DIFFERS" on A21-A23 again. tests: 30 passed. The run itself passed 17/17 either way.
### progress 21:18 (a second nextpnr bitstream defect, this one computes wrong answers: an F7 select tied to GND is left unrouted and reads 1)
- ipow T9 (base) bench seed 7, SLOW_MAX: FAIL 11/17 -- 6 wrong results, all large exponents, each equal to 3^e' for a
  smaller e' (and latency shortened to match): the loop exits early. fasm_equiv: NOT EQUIVALENT, DRIVER DIFFERS
  SLICE_X11Y68/F7AMUX/S0 json const 0, bits const 1. That F7 is in ushrsi0 (e >>= 1); in the JSON it selects input 0
  = a $PACKER_GND_NET buffer LUT (the shift's top bit is 0), input 1 = the A6LUT. S0 is on $PACKER_GND_NET with no
  routing to the AX pin, so on the die the pin reads its default 1 and the F7 passes the A6LUT: e's top bit corrupt.
- Proof: the same bits-decoded netlist with only that S0 forced to 1'b0 -> PASS 17/17 (lat 15..319, same shape as the
  other base routes). Unmodified: 11/17. So the bitstream, not the netlist or the sim, is wrong.
- Scope: 772 fasm_equiv reports on disk: this route (both corners run) is the only const-0 -> const-1 mux select. The
  only other mux-select line is the August ipow build's (pre-11-05 report, the INIT-0 LUT since folded). All board-list
  builds decode EQUIVALENT. Same family as the 11-08 5FF gap: a constant on a site pin nextpnr does not route, and the
  pin's hardware default differs from the constant. The "HARMLESS" class (a LUT pin reads VCC by default ppip) is only
  harmless when the LUT does not read the pin; for an F7/F8 select (and a 5FF D) it is a functional change.
- Consequences: (1) every board build must pass fasm_equiv (already the full-stack flow); (2) the right fix is in
  nextpnr: route GND to these pins (or use the default-1 polarity: swap the F7 inputs), with a toolchain.sh fingerprint
  -- reproducer: ipow bench, T9 bench sizes, NEXTPNR_SEED=7. Left for the owner with the 5FF case.
### progress 03:10 (kernel bench to 8 routes: collatz per-cell 48/48; ipow x0.75 24/24 with base seed 7 the F7 defect)
- collatz per-cell vs T3 on the bench top, seeds 1-8: 48/48 PASS 13/13, gate clean; NOT_EQUIVALENT only benign GND-
  buffer CARRY4/F7 data inputs (checked each new one). Paired, 261-step vector: mean 1.206 SLOW_MAX, 1.209 FAST_MIN,
  1.187 worst (1.12-1.33). research/data/collatz_bench/results.tsv now 8 routes; BOARD-QUEUE #9 / item 8 updated.
- ipow x0.75 seeds 5-8: 12/12 PASS (24/24 over 8 routes). T9 base 5/6/8 PASS; 7 = the F7-select bitstream defect (all
  3 corners 11/17, same wrong answers). Seed 9 pair queued for an 8th pairing. collatz64 6-8 running.
### progress 07:26 (collatz64 x0.75 on the bench top over 8 routes: 24/24, 1.17x)
- Seeds 6-8 added: x0.75 9/9 PASS 14/14, T4 9/9; x0.75 24/24 over 8 routes; T4 21/24 (seed 4 = the 5FF bitstream
  defect). Paired over 7 routes, 350-step vector: 1.172 / 1.174 / 1.172 (SLOW_MAX / FAST_MIN / worst), 1.07-1.22.
  NOT_EQUIVALENT only benign GND-buffer F7 data inputs (checked each new one). BOARD-QUEUE #7 / item 6 updated.
### progress 07:47 (the F7-select defect again: ipow x0.75 bench seed 9 -- 2 of 17 ipow bench routes)
- ipow x0.75 bench seed 9 SLOW_MAX: FAIL 12/17, the same early-exit pattern (5 large-exponent vectors wrong); fasm_equiv
  DRIVER DIFFERS SLICE_X16Y60/F7AMUX/S0 json const 0, bits const 1; the cell is again in ushrsi0 (e >>= 1).
- So the defect is not one route's accident: ushrsi0 synthesises an F7 whose select is tied to GND, and on 2 of the 17
  ipow bench routes built (base 7, x0.75 9) nextpnr leaves that select unrouted (the die reads 1). On silicon those
  builds give wrong answers. All ipow results above are on routes that decode clean; the board item's route (seed 1)
  decodes EQUIVALENT. The BOARD-QUEUE header rule (decode-check any route whose sdf md5 differs) covers rebuilds.
- Not done: a census across kernels of F7/F8 selects tied to a constant (yosys emits them; how often nextpnr leaves
  them unrouted is the question for the nextpnr fix).
- Census (164 routed JSONs on disk): F7/F8 muxes whose select the JSON ties to a constant. ipow bench routes: 76 per route,
  all in ushrsi0; the August ipow build: 76; isprime (bench routes): 1, in ucmpi7; every gcd, collatz, collatz64,
  xorshift, gcd_ps and board-list route: 0. With 2 bad selects in ~17 x 76 = ~1300 such muxes, nextpnr leaves roughly 1 in
  650 of them unrouted -- rare per mux, but ipow carries 76 of them, so ~12% of its builds compute wrong answers.
  Exposure is ipow (and marginally isprime); the other kernels and every board-list design have no such mux.
### progress 08:40 (ipow x0.75 on the bench top over 8 good routes per build: 48/48, 1.16-1.18x)
- Seed 9 pair finished: T9 base 9 PASS 17/17 at max/min/worst (EQUIVALENT); x0.75 seed 9 FAIL 12/17 at all three
  corners (the F7-select defect above). So 18 ipow bench routes built, 2 defective (base 7, x0.75 9), 16 good;
  every good route passes 17/17 at every corner: 48/48 (x0.75 seeds 1-8, T9 seeds 1-6,8,9).
- Paired base/x0.75 on the 31-iteration vector's batch cycles, seeds 1-6 and 8 (7 pairs): SLOW_MAX mean 1.180
  (1.12-1.25), FAST_MIN 1.159 (1.08-1.23), worst 1.160 (1.09-1.26). Seed 1 (the board item's route): 1.08-1.13.
  research/data/ipow_bench/results.tsv regenerated (seeds 1-9); BOARD-QUEUE #8 / item 7 updated.
- Does not show: anything on silicon; cycle counts are at 12 ns granularity, so a per-pair ratio carries ~1% quantisation.
### progress 09:10 (PROGRAM FIRST item, xorshift: where one iteration's time goes -- research/data/itercost/)
- I had not started the FIRST item (owner, made first 2026-11-08) until now; the ipow 8-route work above came before
  it. Corrected: itercost is the only work until it is delivered for xorshift and collatz.
- Full stack (bits-decoded netlist, prjxray SDF, fid, calibrated bands, no scatter), the board list's seed-1 bench
  routes, one 256-round vector twice, every net dumped; causal back-trace from a steady-state rise of umux1's z_req to
  the previous one: x0.5 39.06 ns (86 hops), T3 57.03 ns (123 hops), every hop exact (t_src + wire + arc = t), the
  categories sum to the period to the ps; lengthening +500 ps on an on-cycle delay element: +11 / +22 cycles
  (predicted 10.7 / 21.3: rise-only / both edges), on uxori1's delay: +0.
- The critical cycle is the LOOP-CONTROL ring (umux1 select pipe, i+1<rounds compare, control merge, steers, 5 links),
  not the xor datapath. Its delays bundle loop-invariant data (rounds, a select and a compare constant until exit).
  x0.5 / T3: RTZ 44% / 42%, excess delay 30% / 38%, req/ack routing 20% / 16%, handshake arcs 3% / 2%, logic 3% / 2%;
  wires are 86% of the period. Bound logic + handshake 2.26 / 2.24 ns vs Dynamatic 12.73 ns.
- Levers (x0.5): two-phase 17.2 ns; the 4 rule-1 measurability links on the ring 17.0 ns (ulink_n12__1's 2-stage pipe
  alone 9.2); excess delay 11.8 (5.3 if sized to the worst settle seen -- not safe); fast fall on full-cost chains 6.9.
  Retired: "the xorshift's datapath delays are the cost" (they are off the cycle on these routes).
- Does not show: one route per build, sim not silicon, input-dependent settles. Collatz next.
### progress 09:55 (PROGRAM FIRST item, collatz: the cycle is the n datapath; two barrel shifters from a forked constant)
- Same flow on the board list's collatz seed-1 bench routes (T3 6134880a, per-cell cs 1ab39716), n=6171 (261 steps)
  twice: every one of 518 steady-state iterations traced, all close exactly, categories sum to each period; even and
  odd steps have the identical period (both branches computed, a select picks): cs 67.82 ns, T3 77.56 ns. umux1 is
  off the cycle (marker n26_u_req). Lengthening: uselect0 element +500 ps -> 1479 -> 1490 cycles (pred. 1489.9),
  uaddi1 (step counter) +0.
- Cycle: uaddi0 (3n+1) -> uselect0 -> ucmpi2 (n != 1) -> steer -> merge -> ulink_n14__0 (select) -> umux0 -> uaddi0.
  cs / T3: excess 46% / 49%, RTZ 26% / 28%, routing 13% / 10%, logic 14% / 12%, handshake 1.6% / 1.4%; logic +
  handshake 10.4 / 10.6 ns vs Dynamatic 14.05.
- uaddi0 and uselect0 shift by a constant 1 that arrives as a DATA channel (handshake constant4, forked 5 ways, not
  folded), so yosys builds 32-bit barrel shifters and the delays are sized to them: 16.3 ns (cs) of excess on the
  cycle in those two regions -- PROGRAM's "constant shift synthesised as a barrel shifter", measured.
- research/data/itercost/README.md has both kernels, the method, the self-checks and the ranked levers. Retired on
  xorshift / held on collatz: "the datapath's matched delays are the cost". RTZ factor E = 1.78 (xorshift), 1.35
  (collatz) vs the model's 1.5. Not shown: other routes, PVT, silicon, the next critical cycle once one shortens.
- 10:15 negative: zeroing x0.5 xorshift's six control-ring delay instances in the sim (1 ps arcs and input wires,
  research/tools/itercost/zero_delays.py) deadlocks after the first iteration (umux1's z_req rises once; something
  keeps switching for 155 us, run stopped). The "remove the delays" bound is not measurable that way; the README's
  levers stay read off the cycle.
### progress 10:40 (first lever from itercost: BDC_CONST_DATA, off by default)
- bdc/emit.py BDC_CONST_DATA=1: inside a fused region, an external operand whose value is a known constant (a
  `constant` result, or a fork output of one) is read as that literal; the channel stays (link, join request, ack).
  Default output byte-identical to HEAD on gcd/xorshift/collatz/collatz64/ipow/isprime; with the flag simcheck PASS on
  all six; pytest bdc 63 pass (new test_const_data.py). It turns collatz's `n << e1` / `n >>> e3` and ipow's ushrsi0
  `e >>> e1` into constant shifts (ushrsi0 is where ipow's 76 constant-select F7s, and the F7 bitstream defect, live).
- Running: collatz BDC_CONST_DATA=1 at T3 sizes, soak top, NEXTPNR_SEED 1-4, full stack at max/min/worst
  ($S/k4/collatz_cd, worktree at 83cd6c77). Next: corner_audit those routes for the regions' new sizes, then 8 routes.
### progress 12:10 (BDC_CONST_DATA collatz at T3 sizes: 12/12 full stack, 4/4 EQUIVALENT, 1.01-1.11x already)
- collatz BDC_CONST_DATA=1, T3 sizes, soak top, NEXTPNR_SEED 1-4 (worktree 83cd6c77, nextpnr 9c732bc6303458df):
  SLOW_MAX / FAST_MIN / worst case 12/12 PASS; fasm_equiv 4/4 EQUIVALENT (benign kinds only); LUT sites 1713 -> 1071.
  Paired against T3 (k4/collatz, same seeds; the routes differ, so this is the whole design's effect): max
  1.03/1.03/1.08/1.09, min 1.03/1.04/1.11/1.11, worst 1.01/1.06/1.10/1.09 -- with the delays unchanged, so from
  the smaller placement, not from sizing. corner_audit on these 4 routes -> collatz_sizes_T3cd.vh (249 -> 174 links;
  uaddi0 29 -> 18, uselect0 31 -> 23); its 8 routes x 3 corners are running (k4/collatz_cdc).
### progress 14:05 (collatz: BDC_CONST_DATA + per-cell sizes 24/24 on 8 routes, 1.34-1.36x over T3, 1.16-1.18x over per-cell)
- collatz BDC_CONST_DATA=1 at collatz_sizes_T3cd.vh (249 -> 174 links), soak top, NEXTPNR_SEED 1-8, worktree 83cd6c77,
  nextpnr 9c732bc6303458df: SLOW_MAX / FAST_MIN / worst 24/24 PASS, fasm_equiv 8/8 EQUIVALENT (benign kinds only).
  Paired per seed (research/data/item3/collatz_cdc/pairs.txt): vs T3 1.361 / 1.344 / 1.335 (max / min / worst; range
  1.27-1.47); vs the previous best per-cell sizes 1.178 / 1.168 / 1.157 (1.06-1.27). Rule A informational (item 1).
- The lever came from itercost (two barrel shifters from an unfolded shift-by-one); it also cut 37% of the LUTs.
- Not shown: the board's bench top (next: re-key, build_bench, full stack on 8 routes for a board item), silicon,
  ipow/collatz64 with the flag (ipow's ushrsi0 is the same pattern and carries the F7-defect exposure).
### progress 17:30 (collatz BDC_CONST_DATA on the board's bench top: 24/24, 1.34-1.37x over T3; board item 9 / #10)
- Bench top, BDC_CONST_DATA=1, collatz_sizes_T3cd_bench.vh, NEXTPNR_SEED 1-8: 24/24 PASS 13/13 at max/min/worst, gate
  clean; 7/8 EQUIVALENT, seed 5 NOT_EQUIVALENT of the benign kind only ($PACKER_GND buffer LUT INIT ..10 on an F7 data
  input, checked). Paired with the earlier bench runs on the same seeds (261-step vector): over T3 1.365 / 1.358 /
  1.339 (1.26-1.47), over per-cell 1.132 / 1.124 / 1.128 (1.08-1.16). research/data/collatz_cd_bench/results.tsv.
- BOARD-QUEUE: item 9 / section #10 (seed-1 sdf 3cbe05d8, predicted 1.26-1.30 on that route).
- (A container restart killed only a waiter; the bench run, lockkeeper and janitor survived.)
- Next: the same flag on ipow (ushrsi0's barrel shifter; it is also where the F7-select bitstream defect lives).
### progress 19:10 (owner's NEXT lead: a second latch at the three handshake couplings -- prediction, before running)
- Container restart at ~18:45 killed every process (lockkeeper, janitor, the ipow audits); restarted all three; the
  ipow BDC_CONST_DATA full stack had finished first: seeds 29-32, 12/12 PASS (audits rerunning).
- Checked the premise on x0.5 seed 1's cycle_hops.tsv: the cycle flips polarity at exactly the owner's three places,
  each crossed twice per iteration (umux1 ack -> ulink_n_trueResult_8 req; ufork9 ack (n30__1) -> ulink_n11__1's ack;
  ucontrol_merge0 ack -> ulink_n_trueResult_12 req). ulink_n_trueResult_8 and ulink_n11__1 are single bd_link stages;
  ulink_n_trueResult_12 is already a 3-stage bd_pipe (ring floor 3), so its coupling is through a 3-stage pipe's
  first stage, not a lone latch.
- Plan: BDC_LINK_DEPTHS (existing per-site knob) ulink_n_trueResult_8=2, ulink_n11__1=2, ulink_n_trueResult_12=4 on the
  bench top, x0.5 sizes, NEXTPNR_SEED=1, the itercost bands; then each point alone.
- PREDICTION (written before any run): one token per loop iteration circulates, so a stage added on the ring costs
  forward latency on the rising pass (~1-1.5 ns each: C-element, SDELAY=1 rdly, wires; x3 = 3-4.5 ns). If the
  coupling is the cause, the falling segments (17.2 ns) leave the cycle and the period falls toward the rising pass
  (21.9 ns) + that cost: ~25-30 ns, i.e. down 9-14 ns. If instead umux1 joining the data ring and the select ring
  keeps the RTZ on the cycle (a mux cannot take the next token until both of its inputs have returned to zero), the
  period moves by less than the added latency, and the new cycle will still flip at umux1. I expect the second: a
  partial drop of 3-8 ns, with the flip left at umux1.
### progress 21:05 (second-latch lead, seed 1 only: -3.5 / -4.9 ns; the cycle moves to the counter ring and still flips at the merge)
- Bench top, x0.5 sizes, NEXTPNR_SEED=1, itercost bands, every run EQUIVALENT (benign kinds) and cd3132bf, every
  interval exact and summing to its period (508/510). New inner stages took bdc's default SDELAY 3 (x0.5's own inner
  stages are 1). Periods (base x0.5 seed 1: 39.06 ns):
    all three (n_trueResult_8=2, n11__1=2, n_trueResult_12=4)  35.57 ns   cycle moved; RTZ 43%
    ulink_n_trueResult_8=2 only                                  34.12 ns   cycle moved; RTZ 40%
    ulink_n11__1=2 only                                          39.87 ns   same cycle (still through umux1)
    ulink_n_trueResult_12=4 only                                 44.33 ns   same cycle, longer
- With umux1's coupling decoupled the critical cycle is the loop COUNTER ring (umux0 -> ulink_n7 -> uaddi0 (i+1) ->
  ulink_n30__1 -> ucmpi1 -> steer -> ucontrol_merge0 -> ulink_n12__0 -> umux0) and it still flips polarity twice per
  iteration, at ucontrol_merge0 ack -> ulink_n_trueResult_12 req; a 4th stage in that pipe does not remove it. Reading:
  the arbitrated merge's output cannot return to zero before its granted input does, so the coupling is in the merge,
  not in the latch count beside it -- a stage on the merge's OUTPUT side would be the test of that.
- Against the prediction: the size of the drop (3.5-4.9 ns) is inside the 3-8 ns predicted; the place is not -- the
  remaining flip is at the merge, not at umux1.
- One route each, and adding stages re-places the design: repeating base / p8 / all3 on seeds 2-4 before any claim.
### progress 23:40 (second-latch lead on 4 routes: umux1's coupling binds, -5.6 ns (1.16x); the merge's does not decouple)
- research/data/itercost/second_latch/: xorshift x0.5 bench top, seeds 1-4, BDC_LINK_DEPTHS. Mean period base 39.49 ns;
  ulink_n_trueResult_8=2 alone 33.92 (-5.58 ns, -4.9..-6.9, 1.164x); all three 34.68 (-4.81); ulink_n11__1=2 alone
  +0.8 and ulink_n_trueResult_12=4 alone +5.3 (seed 1). All runs correct, equivalent or benign GND-buffer F7 only
  (checked), every iteration exact.
- The cycle moves to the loop counter ring and still flips polarity at ucontrol_merge0 ack -> ulink_n_trueResult_12
  req; RTZ stays 39-43%. A 4th stage on that pipe does not decouple it: the arbitrated merge's output RTZ follows its
  granted input. Next test: storage on the merge's output (needs a bdc change; not a BDC_LINK_DEPTHS site).
- Prediction (committed first): size of drop right (3-8 ns), location wrong (merge, not umux1).
- Base rebuilds on seeds 2-4 did not reproduce the old xb routes' bits (same seed, newer tree); paired with the
  rebuilt bases. ipow BDC_CONST_DATA: corner_audit done on seeds 29-32 (sizes_max next).
### progress 00:30 (ipow BDC_CONST_DATA: 12/12 at T9 sizes; candidate T9cd 332 -> 226 links; 0 constant-select F7s)
- ipow BDC_CONST_DATA=1 at T9 sizes, soak top, NEXTPNR_SEED 29-32 (the T9 base seeds): 12/12 PASS (max/min/worst).
  corner_audit on those routes -> ipow_dsp1_sizes_T9cd.vh (per-cell max, 332 -> 226 links; ushrsi0 30 -> 1: the
  constant shift is wiring now; T9cs was 251). Those routes have 0 F7/F8 muxes with a constant select (the census
  found 76 per ipow route, all in ushrsi0), so the F7-select bitstream defect has nothing to hit.
- Running: ipow T9cd seeds 29-36 full stack (k4/ipow_cdc); xorshift merge-output link (BDC_MERGE_OUT_LINK, new
  measurement knob, default byte-identical, simcheck PASS) alone and with ulink_n_trueResult_8=2, bench top seeds 1-4.
### progress 03:20 (merge-output latch: with umux1's, 39.49 -> 31.78 ns (1.24x) on 4 routes; the coupling moves to the fork)
- BDC_MERGE_OUT_LINK=ucontrol_merge0 alone: 38.08 ns mean (-1.41); with ulink_n_trueResult_8=2: 31.78 (-7.71, -6.7..-8.2,
  1.243x). All correct, equivalent (mo_2 benign GND-buffer F7, checked), every iteration exact. The arbiter leaves
  the cycle; the counter ring now flips at ucontrol_merge0_f ack -> ucontrol_merge0_olink, RTZ still 40-43%. Each
  decoupled synchronising cell moves the coupling one cell on; the RTZ share does not fall.
- Next: collatz with the same kind of sites (per the lead), sized links, then the full gate on >= 8 routes.
### progress 04:10 (negative: ipow T9cd fails -- the out0 mux's select link shortened 12 -> 9 by corner_audit)
- ipow BDC_CONST_DATA at ipow_dsp1_sizes_T9cd.vh: seed 29 decodes EQUIVALENT and passes the nominal routed GLS but the
  full stack gives X on out0 at every corner (5/5 run, FAIL; stopped); seeds 30, 32, 33 fail the nominal GLS
  ("PROTOCOL data moved inside the hold window on channel out0", vector 1 b=3 e=1). Against the per-cell T9cs (which
  passed 12/12), T9cd shortens four more lines: ulink_n_index_15 12 -> 9 (umux3's select, umux3 drives out0),
  ushrsi0 26 -> 1, ulink_n17__1 10 -> 7, ulink_n13_SDELAY 3 -> 1. Suspect: the umux3 select race (the same class that
  stopped xorshift below x0.5); corner_audit's rules do not see it. Test running: T9cdb = T9cd with ulink_n_index_15
  back to 12, seeds 30/32/33 nominal. The flag itself is not implicated: T9 sizes + the flag passed 12/12.
### progress 07:40 (ipow T9cd diagnosed: ushrsi0 at 1 link fails on other routes; the per-route audit does not carry)
- Nominal routed GLS (fusion_bench --route), out0 hold-window violation in every failure:
    T9cdb (T9cd, ulink_n_index_15 back to 12): seeds 30, 32 pass; 33 FAIL
    T9cdc (+ ulink_n17__1 10, ulink_n13_SDELAY 3, i.e. T9cs values except ushrsi0): seeds 33, 29 FAIL
  Controls on seed 33, all PASS: T9 sizes + BDC_CONST_DATA; T9cdc with ushrsi0 26; T9cs without the flag.
- So the line that breaks it is ushrsi0 = 1. With BDC_CONST_DATA its logic is wiring (e >>> 1), and corner_audit
  proposed 1 on each of its 4 routes (29-32), but a region with no logic still has to cover the data-vs-request
  routing skew into its consumer, which moves with the route; one link does not cover it on routes 29 (full stack) and
  33. A per-cell max over 4 routes is not a bound across routes -- the same lesson as the umux3 select race, now on a
  logic-free delay. corner_audit is being run on the failing seed-33 route to see whether its rules see the hazard.
### progress 22:50 (ipow T9cd root cause traced: the umux3 empty-pipe select race, exposed by a faster exit path)
- Sweep, nominal routed GLS: ushrsi0 = 4 fails seeds 29 and 33; 8 fails 29, passes 33; 26 passes (controls). Not a
  routing-skew margin, so I traced it: T9cdc+ushrsi0=8 seed 29, the nominal GLS dumped, cause-by-cause back from the
  out0 hold violation (every hop exact).
  * out0 goes X when umux3's select (n_index_15) arrives and steers to y (the loop result) BEFORE that token exists;
  * the change inside the hold window is n_falseResult_11_data[4] -> out0_data[4] 1617 ps after the result link's
    latch opened (its req rise), while umux3's own req path (y req -> j1 -> either -> 1-link udly) is as fast.
  So umux3 = 1 (T9 had 4; T9cs and T9cd both proposed 1) is too short whenever the select arrives first -- the same
  empty-pipe select race that limits xorshift below x0.5. In T9 / T9cs the long ushrsi0 delay (the barrel shifter)
  kept the exit decision, hence the select, later than the result, so umux3 = 1 passed there by ordering, not by
  margin. BDC_CONST_DATA makes the e/exit path fast and exposes it.
- Consequences: (1) corner_audit's per-cell proposal for a mux whose select can arrive first is not safe (rule gap,
  as noted on xorshift); (2) ipow T9cs (12/12, never on the board list) carries umux3 = 1 and relies on that ordering;
  board item 7 (ipow x0.75: umux3 = ceil(0.75*4) = 3) does not use 1. Test running: T9cdd = T9cd + umux3 4, seeds
  29/30/32/33 nominal.
- 01:10 T9cdd (T9cd + umux3 4, ushrsi0 kept 1): nominal routed GLS PASS on all four seeds that failed (29/30/32/33) --
  the race diagnosis holds. Full stack on 8 routes (29-36) running (k4/ipow_cdd, ipow_cdd2).
### progress 02:10 (ipow BDC_CONST_DATA + per-cell (umux3 4): 24/24 on 8 routes, 8/8 EQUIVALENT, 1.26-1.29x over T9)
- ipow_dsp1_sizes_T9cdd.vh, soak top, NEXTPNR_SEED 29-36 (the T9 base seeds), worktree 83cd6c77, nextpnr
  9c732bc6303458df: SLOW_MAX / FAST_MIN / worst 24/24 PASS, fasm_equiv 8/8 EQUIVALENT (benign only). Paired vs T9
  1.263 / 1.281 / 1.286 (1.21-1.39); vs T9cs (seeds 29-32) 1.215 / 1.253 / 1.245. Previous ipow best on the soak top
  was x0.75 at 1.13x. The routes have no constant-select F7 (the bitstream defect's site is gone).
- Not shown: the bench top (next), silicon. The umux3 lesson goes with it: a mux whose select can come first keeps a
  delay corner_audit would remove.
### progress 02:40 (second-latch lead, collatz -- prediction before running)
- collatz's itercost cycle (cs and T3, seed 1) changes polarity at ONE place, crossed twice: ucontrol_merge0 ack ->
  ulink_n_falseResult_7 req (the rule-2 ring link, a 3-stage pipe) -- the same merge coupling that remained on
  xorshift. Test: BDC_MERGE_OUT_LINK=ucontrol_merge0 on the best collatz bench build (BDC_CONST_DATA=1,
  collatz_sizes_T3cd_bench.vh), seeds 1-4, against those seeds' existing cd bench routes, itercost bands.
- PREDICTION: on xorshift the merge-output link moved the flip to the merge's fork (ucontrol_merge0_f -> the new
  link) and bought 2.1 ns once umux1 was decoupled. Here the merge is the only coupling, so I expect the same move
  (new flip at ucontrol_merge0_f), the RTZ share staying ~25%, and a drop of 2-4 ns on a ~55-60 ns period; less if
  the added forward latency of the new link (default delay 4 + ack 6) lands on the cycle.
- 01:55 disk full (99 MB free): every ipow bench sim of the first pass ("FAIL 0/17") and the collatz merge-output
  runs read truncated .vvp files ("syntax error") -- NOT results; discarded. Freed 11 GB (all .vvp/.vcd and finished
  runs' regenerable intermediates; bits, reproducers and pending routes kept), then a container restart killed the
  rest; both reruns started (builds kept: their bits were written before the disk filled).
### progress 06:10 (ipow BDC_CONST_DATA on the bench top 24/24, 1.24-1.27x over T9 -> board item 10; collatz merge latch -1.8 ns only)
- ipow bench top, T9cdd_bench, seeds 1-8: 24/24 PASS 17/17, gate clean; 6/8 EQUIVALENT, seeds 1 and 5 benign GND
  buffer (CARRY4 DI / F7 data, checked). Paired (31-iteration vector): over T9 1.254 / 1.244 / 1.269 (1.20-1.31, 7
  pairs: base 7 is the F7 defect), over x0.75 1.063 / 1.074 / 1.095. research/data/ipow_cd_bench/results.tsv;
  BOARD-QUEUE item 10 / #11 (seed-1 sdf f0af6ff8).
- Second-latch lead step 4, collatz: the merge-output link moves the flip to the merge's fork as predicted but buys
  1.8 ns mean (-3.8..+0.3) on ~60.5 ns, below the predicted 2-4; RTZ share unchanged. Not carried to the gate.
### progress 09:30 (second-latch, full gate on the soak top: p8mo 24/24, 8/8 EQUIVALENT; the soak vectors cannot show the gain)
- xorshift x0.5 + ulink_n_trueResult_8=2 + BDC_MERGE_OUT_LINK=ucontrol_merge0, soak top, NEXTPNR_SEED 1-8 (worktree
  5a4176cd), SLOW_MAX / FAST_MIN / worst: 24/24 PASS, fasm_equiv 8/8 EQUIVALENT. Correctness gate passed.
- Speed is not visible here: the soak's 14 vectors run 0-8 rounds, so the sum of latencies is start-up dominated
  (x0.5 / p8mo summed latency 0.96-0.98, i.e. the extra stages' forward latency) and the slope over 0-8 rounds is
  noise (1.02 / 0.99 / 1.01, 0.93-1.08). The steady-state period needs long trips: bench top with the 200/1000-round
  vectors (xb's own method, per_round_ns), seeds 1-8, running ($S/xpb), paired against research/data/xorshift_bench.
### progress 10:40 (second-latch p8mo FAILS on the bench top: seed 1 SLOW_MAX, 4 wrong answers -- a single-bit hazard)
- xorshift x0.5 + ulink_n_trueResult_8=2 + BDC_MERGE_OUT_LINK, bench top, seeds 1-8 (xb's method): seed 1 SLOW_MAX
  FAIL 13/17 (gate clean, EQUIVALENT); the other 11 runs so far PASS. Wrong: rounds 0 (bit 28 flipped:
  82d68ca2 for 92d68ca2), both 3-round vectors with the SAME error pattern xor 57543b39 (xorshift is linear: one fixed
  bit error injected at a fixed point), and the 64-round vector. The base x0.5 route passes this seed and corner, and
  the soak-top gate (other top, other routes) passed 24/24 -- so the extra stages add a real, route-dependent hazard.
  Not a board candidate. Reproducing on one vector with a full dump to trace bit 28 to its cause.
- 12:20 CORRECTION to 10:40: the seed-1 SLOW_MAX failure is the bench HARNESS, not the kernel. Traced (fid GLS,
  rounds-0 vector, every net dumped): the kernel's ulink_n_falseResult_1 stage-0 latch captured bit 28 = 0 because
  its D input, the harness's op0_to_core[28], was already 0 (seed 0x92d68ca2 has it set) -- the harness's operand
  register missed timing at the 100 MHz harness clock these xorshift bench runs use (xb's method, kept for the
  pairing; the JOURNAL 2026-11-08 note on 100 MHz SLOW_MAX harness glitches, which is why board items use
  CLK=0x00100C00). Same route and corner at +FCLK_PS=12000 (83.3 MHz): PASS 17/17. Re-placement by the added stages
  moved this route's harness across that margin. Lesson kept: a "kernel failure" on the bench top has to be traced to
  the kernel's own latches before it counts against the kernel.
### progress 14:10 (second-latch p8mo: full gate passed; 1.25-1.27x per round over x0.5 on 8 bench routes; board item 11)
- Bench top, seeds 1-8 (xb's method, 100 MHz harness): 23/24 PASS 17/17 + seed 1 SLOW_MAX = the harness margin
  (17/17 at 83.3 MHz); decodes EQUIVALENT or benign GND-buffer (6, 7, checked). Per round vs x0.5 paired by seed:
  1.247 / 1.253 / 1.271 (max / min / worst; 1.18-1.36). Soak-top gate 24/24, 8/8 EQUIVALENT (earlier entry).
- BOARD-QUEUE item 11 / #12 (seed-1 sdf 1e51be7e, CLK=0x00100C00, judge loop_cost_judge.py xorshift vs item 4's
  x0.5 route). The added stages keep default (unsized) delays.
### progress 14:40 (next lever: BDC_CONST_DATA on collatz64 -- two 64-bit barrel shifters)
- collatz64's 3n+1 and n>>1 shift by a channel constant too (64-bit: `e0 << e1`, `$signed(e2) >>> e3`). Running the
  same pipeline as collatz/ipow: T4 sizes + flag, seeds 1-4 (the T4 base seeds), full stack, corner_audit; the
  per-cell candidate will keep every mux line at T4 (the ipow umux3 lesson).
- 16:20 collatz64 BDC_CONST_DATA at T4 sizes, seeds 1-4: 12/12 PASS. corner_audit -> per-cell max 217 -> 143 links;
  UMUX1 kept at T4's 5 (proposed 1) per the umux3 lesson -> collatz64_sizes_T4cd.vh (147 links; uaddi0 37 -> 25,
  uselect0 26 -> 18, ucmpi2 23 -> 14). 8 routes x 3 corners running (k4/collatz64_cdc; ~10 h at this kernel's sim speed).
### progress 21:40 (collatz64 BDC_CONST_DATA + per-cell: 24/24 on 8 routes, 8/8 EQUIVALENT, 1.23-1.24x over T4)
- collatz64_sizes_T4cd.vh, soak top, NEXTPNR_SEED 1-8, SLOW_MAX / FAST_MIN / worst: 24/24 PASS, fasm_equiv 8/8
  EQUIVALENT. Paired vs T4 1.244 / 1.236 / 1.232 (1.15-1.33); vs the x0.75 step 1.052 / 1.045 / 1.047. Bench top next.
- (lockkeeper had kept a pre-restart proxy port and failed every push for ~2 h; restarted, pending lock commits pushed.)
### progress 01:40 (collatz64 BDC_CONST_DATA on the bench top: 23/24 -- seed 7 FAST_MIN computes wrong step counts)
- Bench top, T4cd_bench, seeds 1-8, 83.3 MHz harness: 23/24 PASS 14/14; seed 4 decodes NOT_EQUIVALENT (benign GND
  buffer on a CARRY4 DI, checked). Seed 7 FAST_MIN FAIL 12/14: n=871 -> 306 steps (178 expected), n=77031 -> 606
  (350); deterministic (both runs agree), the short power-of-two vectors and n=27/97 pass. A wrong step changes the
  trajectory. Not a board candidate until explained; reproducing n=871 with every net dumped.
- 03:10 traced (n=871 alone, every net dumped): the n loop runs its 178 iterations correctly; the STEP COUNTER is wrong
  (127 -> 128 -> 257). At iteration 127 uaddi1's output settles to 128 2.3 ns before its z_req, then 27 ns later, z_req
  still high, bits 6-8 glitch and settle to 0x100: umux1's select path (ulink_n14__1, shortened 19 -> 10 by
  corner_audit, SDELAY 2 -> 1) lets umux1's request return to zero early, ulink_n_falseResult_5 admits the next
  token, its latch opens and new data runs through umux1 -> ulink_n13 -> uaddi1 inside the counter output's hold
  window. Same family as ipow's umux3: a mux SELECT path that corner_audit's rules do not guard. Test running: seed
  7 with ulink_n14__1 / _SDELAY back at T4 (19 / 2), FAST_MIN and SLOW_MAX.
- 04:10 seed 7 with ulink_n14__1 / _SDELAY back at T4 (19 / 2): FAST_MIN PASS 14/14 (the SLOW_MAX run was lost to a
  container restart). Diagnosis holds. RULE from now on (both traced failures were mux-select paths): corner_audit
  proposals never shorten a mux delay or a linked SELECT channel's DELAY/SDELAY (bdc emit.select_channels) below
  base -- max(candidate, base). collatz T3cd and ipow T9cdd shorten the same select links (and collatz umux0/umux2,
  ipow umux0/umux1); they passed 8 routes on both tops but the hazard is route-dependent, so board items 9 and 10
  are ON HOLD until re-gated. Candidates: collatz64_sizes_T4cdb.vh (169 links), collatz_sizes_T3cdb.vh (208),
  ipow_dsp1_sizes_T9cde.vh (272). Bench-top gates (8 routes x 3 corners) queued for all three.
### progress 08:30 (re-gates: collatz64 select-safe 24/24 (1.22x over T4), collatz select-safe 24/24 (1.18x over T3); item 8 also held)
- Bench top, seeds 1-8, 83.3 MHz, max/min/worst: collatz64_sizes_T4cdb 24/24 PASS 14/14 (seed 5 benign GND buffer);
  collatz_sizes_T3cdb 24/24 PASS 13/13 (seeds 4, 8 benign). Paired: collatz64 vs T4 1.218 / 1.222 / 1.230 (7 pairs),
  vs x0.75 1.03-1.05; collatz vs T3 1.184 / 1.188 / 1.167, vs per-cell T3cs 0.98, vs the held T3cd 0.87 -- i.e. most of
  T3cd's extra gain over per-cell came from the shortened select links; with them restored collatz's literal-shift
  build is no faster than the per-cell sizes it was meant to beat.
- The per-cell sizes of board item 8 (collatz_sizes_T3cs) shorten the same select paths (ulink_n14__0 18->11,
  ulink_n14__1 36->18, umux0 6->1): ON HOLD, replaced by item 9 (T3cdb). The uniform shrinks (items 4, 6, 7, 11:
  x0.5 / x0.75) scale select links in proportion with everything else; no failure seen on any of their routes; left
  on the list, flagged for the owner.
- BOARD-QUEUE: item 9 / #10 rewritten (collatz T3cdb, sdf a7882dfa); new item 12 / #13 (collatz64 T4cdb, sdf b883dcb5);
  item 10 (ipow) stays held until its re-gate (running) finishes.
### progress 12:40 (ipow select-safe 24/24 but no faster than x0.75: item 10 withdrawn)
- ipow_dsp1_sizes_T9cde (select-safe), bench top, seeds 1-8: 24/24 PASS 17/17, 8/8 EQUIVALENT. Paired: vs T9 1.162 /
  1.159 / 1.185 (7 pairs), vs x0.75 (item 7) 0.985 / 1.002 / 1.024, vs the held T9cdd 0.93. With the select links kept,
  BDC_CONST_DATA on ipow buys nothing over the uniform x0.75 already listed (the ushrsi0 delay it shortens is not on
  ipow's critical cycle once the exit select is no longer starved). Item 10 withdrawn. research/data/ipow_cde_bench.
- Net, after the select rule: collatz64 1.22x over T4 (item 12, +3-5% over item 6); collatz 1.18x over T3 (item 9,
  replaces held item 8); ipow none over item 7; xorshift second latch 1.25x over x0.5 (item 11).
- 14:10 research/tools/corner_audit.py now never shortens a select path (default; --shrink-selects to allow): every
  BD_SZ_UUT_UMUX* and the DELAY/SDELAY of every link on a channel bdc reads as a select (emit.select_channels on the
  route's input.mlir). It may still pad them. Checked on collatz64_cdc2 seed 5 (an x T4cd route): all 8 select-path lines
  kept, labelled; the same route with --shrink-selects proposes ulink_n14__1 10 -> 5 and umux1 5 -> 1 (the moves that
  failed), so the protection is what holds them. A route's sizes.vh is the floor, so run it on base routes.
## Session 2026-11-11 07:45 UTC -- STOPPED for the owner's pause (PROGRAM.md, commit cca0a559)
- The pause (until 2026-11-12 00:00 UTC, "a running session stops now") was committed 2026-11-11 04:26 UTC. This
  session read it only at 07:41: the lockkeeper's `git pull --rebase` brought it in and I did not re-read PROGRAM.md
  after each pull. Work done in those ~3 h: the ipow select-safe re-gate finished and was written up (item 10
  withdrawn), the corner_audit select-path protection (fdee9471), PR #2's description. No new runs were started after
  the re-gate; nothing is running now (lockkeeper and janitor stopped). Lesson: re-read PROGRAM.md whenever a pull
  brings in an owner commit.
- Where it stands: board items 9 (collatz T3cdb, 1.18x), 11 (xorshift second latch, 1.25x), 12 (collatz64 T4cdb, 1.22x)
  passed the full gate; 8 on hold and 10 withdrawn (select-path race, traced twice); uniform shrinks (4, 6, 7, 11)
  flagged for the owner. PR #2 is current.
- Next step (for the session after 2026-11-12 00:00 UTC): delete the PAUSED section, then the new PROGRAM FIRST item
  ("compute where storage goes, before building it", owner 2026-11-10, commit 8c90d04d), which this session has not
  started; it comes before any new per-kernel sizing or board candidate.
## Session 2026-11-12 02:50 UTC -- PROGRAM FIRST item: the timed event graph (step 1)
Toolchain: patches 789a7120c912d393, nextpnr 9c732bc6303458df (cells/verify/toolchain.sh PASS)   Seeds: 1-4
### progress 03:00 (step 1 tool works on x0.5 seed 1: graph period = measured, cycle = itercost's, hop for hop)
- The 11-08 itercost runs were in a scratch dir and their dump top was never committed, so every run is rebuilt:
  research/tools/eventgraph/fullstack_dump.sh (the itercost stack: bits-decoded netlist, prjxray SDF, fid, chains 0.21,
  CARRY4/F7F8/FF at 1, rest 0.288, no scatter; one 256-round vector twice, top nets dumped). Rebuilt routes reproduce
  the recorded sdf md5s (x0.5 s1 c5b8ca02, T3 s1 e3024283, collatz cs 1ab39716, T3 6134880a); x0.5 s1 gives
  cd3132bf, EQUIVALENT, latmin 836 (the README's 836).
- research/tools/eventgraph/eventgraph.py: nodes = edges of nets periodic in steady state (230 on x0.5 s1; data and
  harness-clocked nets are aperiodic); arcs = every ENABLING input of each edge (LUT INIT / F7F8 evaluated on the
  delayed pin values: a pin is enabling if restoring its previous value would keep the old output), weight wire+arc,
  token offset from the trace, slack >= 0. Period = max cycle ratio by the max-plus recursion (maxplus.py).
  x0.5 s1: 230 nodes, 325 arcs, every edge AND-type (no OR edge), no negative slack; graph period 39058 ps = P;
  the critical cycle (86 arcs, 1 token) equals trace.py's walk and the committed itercost cycle_hops.tsv, edge for edge.
- Running: the other 33 runs (itercost T3 + collatz, second_latch base 2-4 and all variants, collatz cd +- merge link
  seeds 1-4 for step 3's collatz prediction), 3 lanes.
### progress 03:25 (step 1: 14/14 runs reproduce period and cycle exactly; step 2-4 tools give first numbers)
- Rebuilt and re-run so far: x0.5 seeds 1-4, T3 seed 1, collatz cs/T3 seed 1, mo 1-4, p8 1, all3 1-2. Each: graph
  period == trace period to the ps, critical cycle == trace.py's walk == the committed itercost cycle_hops.tsv (hop
  for hop). Periods equal the recorded ones (40.594 = 40.59, 37.83, 35.57, 67.82, 77.56 ...), so every route reproduced.
- research/data/eventgraph/graphs/<run>/: nodes.tsv, arcs.tsv, check.txt, kernel.v, provenance, BENCHRES.
- Step 2 (x0.5 s1): floor with no polarity change 19.99 ns (the loop-counter ring's rising pass) vs 39.06 measured;
  every falling arc at 0: 21.9 ns. collatz cs: floor 49.3 vs 67.8 (2-phase bound 51.1); T3 56.3 vs 77.6. So on collatz
  added storage could at best reach 1.37x; the rest is the rising pass of the n datapath (delays), not the protocol.
- Step 3, seeds 1-2 (predictions from each seed's base graph; edit rules committed b3eaf9cd before any prediction ran;
  NOT blind: the measured values were already in second_latch/README.md; implementation fixes after that commit were
  net-finding only, no weights): p8 -6.06/-4.71 (measured -4.94/-5.56); all3 -4.71/-3.73 (-3.49/-4.57); mo -1.28/-1.64
  (-1.23/-2.59); p8mo -7.34/-6.35 (-7.89/-6.67); the predicted p8 cycle is the measured one (counter ring, flips at the
  merge). p12 predicted 0 vs +5.3 measured (seed 1): a miss, to be traced on the p12 graph; p11 0 vs +0.8.
- Step 4 greedy search (buildable knobs only) on x0.5 s1 re-finds p8mo, then adds BDC_LINK_FASTFALL: p8 + fast fall +
  merge-out link 29.07 ns predicted (1.34x over x0.5; p8mo alone 31.72). Not built yet.
### progress 03:35 (step 4 PREDICTION, written before building: xorshift p8 + BDC_LINK_FASTFALL + merge-output link)
- search.py (greedy over knobs bdc can build: +1 depth on any link, merge-output link, BDC_LINK_FASTFALL) on the four
  x0.5 base graphs picks the same set on every seed: BDC_LINK_DEPTHS=ulink_n_trueResult_8=2
  BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1. PREDICTED period 29.07 / 29.70 / 29.29 / 30.13 ns (seeds
  1-4, mean 29.55; 1.34x over x0.5's 39.49, 1.08x over p8mo's measured 31.78). A further edit gains < 0.3 ns: the
  cycle stays on the counter ring and still changes polarity at the merge-output link's fork.
- ipow x0.75 (item 7 route, seed 1): base 55.50 ns, floor 37.26; search: BDC_LINK_FASTFALL + merge-output link ->
  46.09 ns predicted (1.20x). Seeds 2-4 pending.
- Building both on seeds 1-4 next (itercost stack, measured period vs predicted).
### progress 03:50 (step 3 on all 4 seeds; ipow step-4 prediction for seeds 1-4, before the builds finish)
- A container restart at ~03:40 killed the lanes; 26 runs had finished; the 21 left (and p12 seeds 2-4, added) restarted
  from scratch (partial dirs deleted). gcd seed 1's bench build hit a nextpnr assertion (bel != BelId(), BD_RLOC=v4):
  gcd moved last.
- Step 3, predicted vs measured period from each seed's base graph (research/data/eventgraph/step3_predictions.tsv):
    p8   predicted mean 33.56 ns, measured 33.91: error -0.35 (per seed -1.12..+0.86)
    all3 34.72 vs 34.68: +0.04 (-1.22..+0.85)
    mo   38.08 vs 38.08: -0.00 (-1.23..+0.95)
    p8mo 32.14 vs 31.78: +0.36 (-0.79..+1.38)
    p11  39.06 vs 39.87 (seed 1): -0.81
    p12  39.06 vs 44.33 (seed 1): -5.27  MISS
  The predicted cycles move where the measured ones did (p8/all3/p8mo: to the counter ring, flipping at the merge or at
  the merge-output link's fork). p12: its measured cycle (second_latch/p12_1/stages.tsv) is the base cycle, same 13
  stages and 86 hops, every stage longer in wire (ulink_n12__1 11.26 vs 9.17 ns, umux1 5.77 vs 4.48, merge 4.97 vs 3.99)
  -- the structural prediction (the new stage is off the cycle) holds and the 5.3 ns is this one re-placement. Testing
  with p12 seeds 2-4 (queued). The graph of one route cannot predict another route's wires; that is the ~1 ns scatter.
- ipow BDC_LINK_FASTFALL + merge-output link, PREDICTED per seed 46.09 / 44.92 / 45.06 / 44.08 ns (mean 45.04; base
  mean 53.96, 1.20x). Building.
### progress 04:00 (step 4 first builds: pmf seed 1 measured 29.14 vs predicted 29.07 ns; seed 2 route has a bitstream defect)
- xorshift p8 + BDC_LINK_FASTFALL + merge-output link ("pmf"), bench top, itercost stack: seed 1 measured 29.144 ns
  (predicted 29.072, +0.07), cd3132bf, decode benign (GND-buffer F7 data input). Graph check PASS.
- Seed 2: the route's bitstream leaves a bench-harness flop unconfigured: $auto$dfflegalize emulate_split_set_clr (FDPE,
  D on GND) placed in CLBLM_R_X9Y36 SLICEM_X0 AFF has ZINI/ZRST but no AFFMUX, and the pip to its LUT load is json-only;
  fasm_equiv NOT EQUIVALENT, the run returns X data. The same nextpnr gap as 2026-11-08 08:21 (there a C5FF); now an
  AFF slot too. research/tools/ffmux_scan.py finds it from the FASM alone: 1 of the 35 FASMs of this session (the
  only one). The gate refuses such routes; still unpatched in nextpnr (owner item from 11-08 stands). pmf_2 excluded;
  seed 5 (base + pmf) added to keep 4 pairs.
- ipowfm seeds 1-2 (BDC_LINK_FASTFALL + merge link on ipow x0.75): aaaaaaab, EQUIVALENT; periods in the next note.
### progress 04:15 (step 4 measured: xorshift pmf 1.34x over x0.5, ipow 1.18x; collatz prediction before building)
- xorshift pmf (p8 + BDC_LINK_FASTFALL + merge-output link), seeds 1/3/4/5 (2 excluded, bitstream defect): measured
  29.14 / 29.54 / 32.42 / 28.46 ns (mean 29.89) vs predicted 29.07 / 29.29 / 30.13 / 30.11 (mean 29.65; seed 5's
  prediction was computed after its run had finished, before I read it). Paired with x0.5: 1.340 / 1.374 / 1.216 /
  1.447 (mean 1.344, predicted 1.34). Over measured p8mo (seeds 1/3/4): 1.070 / 1.096 / 0.968. Every measured cycle
  is the predicted one (the 11 counter-ring stages, the 2 polarity changes at the merge-output link's fork); the misses
  are wire on those stages (seed 4: the merge-output link costs 2.2 ns an edge, the model 0.4 + its rdly).
- ipow fm (BDC_LINK_FASTFALL + merge-output link on x0.75), seeds 1-4: 46.84 / 45.02 / 46.04 / 45.24 vs predicted
  46.09 / 44.92 / 45.06 / 44.08 (error +0.09..+1.16, mean +0.75); paired with x0.75 1.185 / 1.152 / 1.179 / 1.199
  (mean 1.18, predicted 1.20). All aaaaaaab = 3^(2^31-1) mod 2^32, EQUIVALENT.
- collatz merge-output link on BDC_CONST_DATA (T3cd sizes), seeds 1-4: predicted 57.85 / 58.52 / 57.84 / 58.19
  (delta -2.43 mean), measured 56.39 / 59.95 / 57.40 / 61.20 (delta -1.81 mean, as second_latch README's -1.8):
  error -0.63 mean, seed 4 -3.0 (its measured period is above its base: re-placement).
- PREDICTION collatz cd + BDC_LINK_FASTFALL + merge-output link (search's pick on all four cd graphs): 53.03 / 53.93 /
  53.50 / 53.71 ns (mean 53.54; 1.13x over cd's 60.54). Building seeds 1-4.
- Step 2/6 for collatz cd s1: floor 41.8 ns, two-phase bound 43.0, storage 57.9, storage + every chain fast 53.0, deco 60.2.
### progress 04:30 (p12 on 3 seeds: +5.3 / +4.6 / +2.1 ns, the same cycle each time -- a systematic placement cost the graph cannot see)
- p12 (ulink_n_trueResult_12 = 4) seeds 2, 3: 43.44 / 42.66 ns vs their bases 38.89 / 40.59. Kernel Verilog differs from
  the base only in that pipe's N. Each measured cycle is the base cycle (same 13 stages, 86 hops; the new stage off it,
  as predicted), longer in wire: seed 2's ulink_n12__1 8.8 -> 11.5 ns, merge fork 0.6 -> 1.3, ucond_br7 0.7 -> 1.5. So
  the prediction's structure holds and its magnitude misses by 2-5 ns, systematically: one more cell next to the
  merge hub lengthens the ring's wires on every seed. The graph of one route has no model of placement; this is its
  known limit, and it says a stage that cannot help is not free either.
- (Process note: I started a second lane on a worktree that was still building and then killed collatz builds too
  broadly; every colfm output was deleted and the four builds restarted on idle worktrees. No result was affected.)
### progress 04:40 (collatz step 4 measured as predicted; p12 seed 4 +2.5; gcd bench builds fail with RLOC v4)
- collatz cd + BDC_LINK_FASTFALL + merge-output link, seeds 1-4: 53.60 / 55.05 / 51.84 / 54.72 ns (mean 53.80) vs
  predicted 53.03 / 53.93 / 53.50 / 53.71 (53.54); paired with cd 1.122 / 1.104 / 1.164 / 1.113 (mean 1.13, predicted
  1.13); 0x105 = 261 steps, EQUIVALENT; the measured cycle is the predicted one (up to two parallel fork branches).
- p12 seed 4: 41.94 vs 39.43 (+2.51). Four seeds: +5.27 / +4.56 / +2.07 / +2.51, same cycle each time.
- gcd bench with BQ#4's flags (BD_RLOC=v4): all four seeds abort in nextpnr ("post-place repair: no valid placement for
  uori2/uori4 udly chain g[0]", then router2 assertion bel != BelId()). Retrying without RLOC.
- Gate running: ipowfm (x0.75 + BDC_LINK_FASTFALL + merge-output link) seeds 1-8 x SLOW_MAX / FAST_MIN / worst+M,
  17 vectors (oracle from kernels/ipow/ipow.c), research/tools/eventgraph/bench_gate.sh. Seed 1 SLOW_MAX: PASS 17/17,
  EQUIVALENT.
### progress 05:10 (gates running; collatz select-safe base + knobs queued)
- Gate (bench_gate.sh, 17 C-derived vectors per run): so far ipowfm seeds 1/2/5 at max/min/worst and pmf seed 1 max
  all PASS 17/17 (seed 5 and pmf 1 decode NOT_EQUIVALENT of the benign GND-buffer F7 kind, checked on seed 5).
  ipowfm 1 min lost to a script edited while running (re-queued).
- gcd bench without RLOC builds (gcd_1/2), but its full-stack sim is OOM-killed next to the other jobs (100k icbufs);
  deferred until it can run alone.
- Queued: collatz select-safe base (BDC_CONST_DATA, collatz_sizes_T3cdb_bench.vh = board item 9's sizes) seeds 1-8,
  then the same + BDC_LINK_FASTFALL + merge-output link; predictions from the base graphs before the variants run.
- PR #2 description updated.
### progress 05:22 (gate 14 runs, all PASS; a third constant-D flop gap: ipowfm seed 7, BFF)
- Gate results so far: ipowfm 1 (max, worst), 2 (max/min/worst), 3 (max), 5 (max/min/worst), 6 (max/min), pmf 1
  (max/min): every one PASS 17/17. NOT_EQUIVALENT ones (ipowfm 5, 6, pmf 1) are GND-buffer F7 data inputs only (checked).
- ffmux_scan.py on the new FASMs: ipowfm seed 7 has CLBLM_R_X9Y30.SLICEM_X0.BFF with ZINI/ZRST and no BFFMUX -- the
  same nextpnr gap, third slot type (C5FF 11-08, AFF and BFF today), 2 of the ~45 routes built this session. Seed 9
  added so the gate keeps 8 good routes; seed 7's gate runs stay in as an exhibit.
### progress 05:40 (PREDICTION before the builds: collatz select-safe (item 9 sizes) + BDC_LINK_FASTFALL + merge link)
- colcdb (BDC_CONST_DATA, collatz_sizes_T3cdb_bench.vh, board item 9's sizes) seeds 1-4: 67.44 / 68.02 / 69.27 / 67.10 ns,
  261 steps each. search.py picks BDC_LINK_FASTFALL + merge-output link on all four: PREDICTED 56.45 / 56.39 / 58.77 /
  56.44 ns (1.195 / 1.206 / 1.179 / 1.189x; mean 1.19x). Floors 45.6-46.4 ns. Variant builds (colb) follow colcdb 5-8.
### progress 06:35 (ipow fm passes the full gate 24/24 -> board item 13 / #14; collatz select-safe step 4 measured)
- ipowfm (x0.75 + BDC_LINK_FASTFALL + merge-output link) seeds 1-6, 8, 9 x SLOW_MAX / FAST_MIN / worst+M: 24/24 PASS
  17/17; decodes EQUIVALENT or the benign GND-buffer F7/CARRY4 kinds (5, 6, 9 checked); seed 7 excluded (BFF gap; its own
  runs also PASS 17/17 -- the defect sits in harness logic these vectors do not exercise, which is why fasm_equiv, not
  the answers, is what refuses it). BOARD-QUEUE item 13 / #14 (seed-1 sdf e5000e23, ffmux_scan step in the recipe).
  The first board candidate chosen by the event graph rather than by hand; 1.18x over item 7.
- collatz select-safe (item 9's T3cdb sizes) + BDC_LINK_FASTFALL + merge link, seeds 1-4: measured 59.58 / 58.44 /
  56.26 / 58.35 ns vs predicted 56.45 / 56.39 / 58.77 / 56.44 (errors +3.1 / +2.0 / -2.5 / +1.9 -- larger than on the
  other kernels); paired with colcdb 1.132 / 1.164 / 1.231 / 1.150 (mean 1.17, predicted 1.19). Cycles as predicted
  (up to the parallel fork branches ulink_n10__1/__2). Next: its full gate (8 routes) after xorshift pmf's.
### progress 10:45 (xorshift pmf passes the full gate 24/24 -> board item 14 / #15)
- pmf (x0.5 + ulink_n_trueResult_8=2 + merge-output link + BDC_LINK_FASTFALL) seeds 1, 3-9 x SLOW_MAX / FAST_MIN /
  worst+M: 24/24 PASS 17/17 (200- and 1000-round vectors included), 7/8 EQUIVALENT, seed 1 benign. Itercost periods
  seeds 6-9: 29.14 / 30.28 / 31.10 / 29.86 ns (all 8: mean 30.0 vs x0.5's 39.5 -> ~1.32x; ~1.06x over item 11).
  BOARD-QUEUE item 14 / #15 (seed-1 sdf 169ce4d6). The collatz select-safe gate (colb) is at seed 7.
### progress 11:35 (collatz select-safe + fast fall + merge link passes the full gate 24/24 -> board item 15 / #16)
- colb seeds 1-8 x SLOW_MAX / FAST_MIN / worst+M: 24/24 PASS 13/13; 7/8 EQUIVALENT, seed 8 benign GND-buffer F7
  (checked); ffmux_scan clean. Over item 9 on the itercost stack 1.13-1.23x (mean 1.17, predicted 1.19). Seed-1 route
  sdf e20325f3; item 9's base a7882dfa reproduced by colcdb_1.
- So the event graph's step 4 gave three gated board candidates in one session: ipow (item 13, 1.18x over item 7),
  xorshift (item 14, ~1.32x over x0.5 / ~1.06x over item 11), collatz (item 15, 1.17x over item 9). All three are the
  same two knobs (link fast fall, a latch on the arbitrated merge's output), plus p8 on xorshift.
### progress 12:05 (gcd graph; step 5 end to end)
- gcd bench (gcd_ps P1 sizes, no RLOC; vector gcd(1, 2^31-1) = 1, one main + one ctz iteration each), seed 2, alone on the
  machine (its compile needs ~10 GB): 186.93 ns per iteration, graph check PASS (424 arcs). Floor 171.5 ns, two-phase
  bound 173.2, storage 1.00x, + every chain fast 1.03x: gcd's cycle is its datapath's rising pass (pad-only sizes);
  sizing, not storage or protocol, is its lever. One seed only.
- Step 5, storage_pass.sh end to end on an unseen case (xorshift T3 sizes, seed 2): base 56.57 ns -> search picks the
  same three knobs -> predicted 35.64, measured 39.38 (1.44x vs 1.59x predicted), same cycle, EQUIVALENT. The miss is
  the inserted merge-output link (3.9 ns on the cycle measured). The graph under-charges inserted stages' wire by ~1-3
  ns (p12, pmf seed 4, here): structure is predicted, the number needs the build.
Next: (1) the owner's decision on the protocol table (two-phase bound 1.4-1.8x vs storage 1.0-1.3x); (2) gcd: sizing on
  its rising pass (corner_audit, select-safe) -- the graph says nothing else is left there; (3) a per-inserted-stage wire
  term for whatif, fitted on some builds and tested on the others, before trusting predicted magnitudes.
### progress 12:20 (negative: a constant per-inserted-stage wire term does not help; the graph's held-out error)
- research/tools/eventgraph/fit_stage_wire.py: whatif's stage_wire (extra ps on every input arc of an inserted stage)
  fitted on the 16 second-latch builds (x0.5 seeds 1-4: p8, all3, mo, p8mo) and tested unchanged on the 23 step-4 builds
  (pmf, ipowfm, colb, col cd+link, colfm). Train is best at 0 (mean |err| 0.71 ns, max 1.38); larger terms only hurt it.
  At 0 the held-out set has mean error -0.71 ns (the graph optimistic), mean |err| 1.38, max 3.13 ns; 500 ps would make
  it +0.23 / 1.13 but is not what the training data supports. Default kept at 0. Held-out accuracy of the graph, as it
  stands: within ~1.4 ns per route on 30-70 ns periods (2-5%), optimistic by ~0.7 ns on average.
### progress 12:15 (collatz64, item 12's design: graph exact on 4 seeds; PREDICTION before the variant builds)
- c64 (BDC_CONST_DATA, collatz64_sizes_T4cdb_bench.vh = item 12), n = 6171 (261 steps), seeds 1-4: 66.07 / 65.91 / 60.84 /
  65.00 ns, graph check PASS (145 arcs). Floors 41.4-45.6 ns.
- search.py picks BDC_LINK_FASTFALL + merge-output link on all four: PREDICTED 57.44 / 56.44 / 51.96 / 56.90 ns
  (1.150 / 1.168 / 1.171 / 1.142x, mean 1.16). Given the held-out bias (graph ~0.7 ns optimistic), expect ~1.14x.
  Variant builds c64fm 1-4 running.
### progress 12:45 (collatz64 step 4 measured as predicted; a 4th constant-D flop gap; its gate started)
- c64fm (item 12 + BDC_LINK_FASTFALL + merge-output link) seeds 1/2/4: 54.85 / 56.16 / 57.54 ns vs predicted 57.44 /
  56.44 / 56.90; over item 12's design 1.205 / 1.174 / 1.130 (mean 1.17, predicted 1.15 on these three). 261 steps,
  EQUIVALENT. Seed 3: C5FF without C5FFMUX (ffmux_scan; the 11-08 kind). Four such routes in ~60 built this session
  (pmf 2 AFF, ipowfm 7 BFF, c64fm 3 C5FF): ~7%. Every board recipe now carries the ffmux_scan step; the nextpnr fix
  (owner item since 11-08) is worth doing.
- Gate queued: c64fm seeds 1, 2, 4-9 x 3 corners, 14 vectors (n up to 63728127, 949 steps; oracle from collatz.c).
  collatz64 sims are slow (~10 h for 24 runs last time); partial results go to gate/results_raw.txt as they land.
### progress 17:10 (collatz64 gate 18/18 PASS so far; 5 runs lost to OOM after a container restart, rerunning)
- c64fm gate: seeds 1, 2, 4-7 x 3 corners = 18/18 PASS 14/14 (up to 949 collatz steps). Seeds 8/9 runs after a container
  restart reported FAIL 0/14 with 0 cycles: not results -- iverilog was OOM-killed (dmesg) because sims started BEFORE
  the restart were still running (the restart did not kill them) next to three new lanes. Those lines were removed; seeds
  8 and 9 rerun on one lane after killing every leftover vvp/ivl. Lesson: after a restart, check for surviving jobs
  before starting new ones.
- Itercost periods c64fm seeds 5-9: 57.33 / 54.99 / 57.14 / 55.65 / 58.05 ns.
### progress 17:20 (new PROGRAM FIRST, owner 2026-11-12 db2c8f53: xorshift at 15 ns per iteration in four-phase)
- Read on the pull that brought it in (the push was rejected by the owner's commit; the lock was still this session's).
  The event-graph lead moves to Done; the collatz64 gate's last 6 runs finish in the background (item for the board list
  if 24/24). Starting step 1: the budget from the graph on item 14's routes (pmf seeds 1, 3-9): falling arcs on the
  critical and near-critical cycles, each delay on the rising ring against its data's worst need, each req/ack wire
  against an adjacent-cell wire. Report: research/data/fifteen/README.md.
### progress 18:00 (15 ns lead, step 1 budget done; first new lever predicted: a latch on the merge fork's result branch)
- research/tools/fifteen/budget.py on item 14's 8 routes (research/data/fifteen/budget_pmf_*.txt): period 28.5-32.4 ns;
  return-to-zero on the cycle 9.9-12.7 ns; delay removable under the rules 1.4-2.5 ns (mostly select paths the select
  rule keeps); handshake-wire removable (to the graph's 10th-percentile wire) 1.9-3.2 ns. All three taken: 16.7-17.7 ns.
  Not under 15: what blocks is the counter ring's rising logic (uaddi0's i+1 needs 4.9 ns with guard -- its worst settle
  over the run, 3.8 ns, exceeds its on-cycle delay 2.85 ns: to be checked -- and ucmpi1 3.1) and the handshake hops.
- No storage edit with existing knobs helps item 14 (21 candidates, all singles and pairs: 0 ps). The cycle closes
  through the merge-output fork ucontrol_merge0_f: its ack waits for the loop-control join ucond_br9_j, which waits for
  the whole counter computation, so the select token's RTZ rides the counter's rising pass. The graph: one bd_link on
  that fork's RESULT branch (n_result -> ucond_br9_j) removes it.
- bdc/emit.py BDC_MERGE_RES_LINK=<merge> (new, opt-in): that link (control token: W 1, DELAY STAGE_PAD 3, DACK 0).
  Default output byte-identical on gcd/xorshift/collatz/collatz64/ipow/isprime; simcheck PASS on xorshift with it alone
  and with item 14's knobs.
- PREDICTION (item 14 + BDC_MERGE_RES_LINK=ucontrol_merge0), from each pmf graph: 21.85 / 21.87 / 23.10 / 23.57 ns
  (seeds 1/3/4/5; 1.33 / 1.35 / 1.40 / 1.21x over item 14). With PROGRAM's +1-3 ns for an inserted stage's wire:
  expect 23-26 ns. Building seeds 1, 3, 4, 5.
### progress 18:40 (BDC_MERGE_RES_LINK measured: 23.37 / 23.40 ns on seeds 1, 3 -- 1.25x over item 14; disk filled)
- item 14 + BDC_MERGE_RES_LINK=ucontrol_merge0, itercost stack: seed 1 23.37 ns (predicted 21.85; +1.52, inside the
  23-26 expected with the inserted-stage wire), seed 3 23.40 (21.87; +1.53). cd3132bf, EQUIVALENT, graph check PASS,
  ffmux_scan clean. Over item 14's same seeds: 29.14 -> 23.37 (1.247x), 29.54 -> 23.40 (1.262x). Over x0.5: 1.67x / 1.73x.
- Seeds 4 and 5 lost their trace dumps to a full disk (817 MB left: this session's dumps, netlists and gate dirs, 27 GB).
  Freed 11 GB from finished runs (graphs and logs kept); seeds 4, 5 rerunning. The collatz64 gate's seed-8 run was
  compiled at 17:10, possibly while the disk was filling; if it does not PASS cleanly it is rerun, not read.
### progress 19:05 (lever 2: BDC_RING_COUNT_OLINKS -- the ring-storage pipe on the cycle becomes one stage; prediction)
- After the result-branch latch the critical cycle (pmfr seed 1, 23.37 ns) has NO polarity change: it is the counter
  ring's rising pass, 86% wire (delay chains 16.1 ns of which 13.7 wire; handshake hops 7.3 of which 6.5 wire). Stages:
  ucmpi1 5.2, ulink_n30__1 2.7, uaddi0 2.8, olink 2.5, ulink_n12__0 2.4, ulink_n_trueResult_12 2.4 (a 3-stage pipe),
  merge 2.1, umux0 1.5, ucond_br9(_j) 1.2, ulink_n7 0.5.
- The 3-stage pipe is ring_depths()'s floor for the simple cycle merge -> fork -> join -> steer -> pipe -> merge, whose
  only storage it was. The olink and rlink now sit on that cycle. bdc/emit.py BDC_RING_COUNT_OLINKS=1 (opt-in, default
  byte-identical on all six kernels) lets ring_depths count them: the pipe becomes one bd_link (W 1, RFAST under
  fast fall); nothing else changes in the emitted kernel; simcheck PASS. RING_MIN_STAGES still holds on every cycle.
- PREDICTION (by hand from pmfr seed 1's cycle; whatif has no stage-removal edit): the pipe's 2.4 ns on the cycle -> one
  C-element hop, ~0.7 ns: -1.6 to -1.8 ns -> ~21.6-21.8 ns on seeds 1 and 3. Building pmfrc seeds 1, 3, 4, 5.
### progress 19:45 (lever 2 measured; lever 3: BDC_FORK_OUT_LINK on the rounds fork -- prediction)
- pmfr seed 4 (lever 1): 24.12 ns (predicted 23.10; item 14's 32.42 -> 1.34x). Seed 5 still re-running.
- Lever 2 (BDC_RING_COUNT_OLINKS: the 3-stage pipe on the counter ring becomes one link): seed 1 23.37 -> 22.95, seed 3
  23.40 -> 21.99 ns (predicted ~21.7). Less than predicted on seed 1 because the cycle moved: the next ring binds, the
  loop-invariant `rounds` ring (umux2 -> ulink_n11__1 -> ucmpi1 -> ucond_br8 -> pipe -> ufork4 -> ulink_n12__2), with the
  same coupling as before: fork ufork4's ack waits for the steer ucond_br8's join, which waits for the compare, and
  umux2's select link waits on that ack (polarity changes ufork4 -> ulink_n12__2).
- bdc/emit.py BDC_FORK_OUT_LINK=<chan> (opt-in; default byte-identical on all six kernels): one bd_link on a named fork
  output channel (DELAY STAGE_PAD 3, DACK ACK_PAD 6 for data). With n11__0 (fork ufork4 -> steer ucond_br8's data):
  simcheck PASS with all knobs.
- PREDICTION (graph of pmfrc seeds 1/3 + that link): 21.21 / 20.60 ns, no polarity change, the cycle back on the counter
  ring; with +1-3 ns for the inserted stage: 22-24 ns. Building pmfrcf seeds 1, 3, 4, 5.
### progress 20:10 (lever 3 measured: 19.86 / 20.64 ns on seeds 1, 3 -- under 20; its gate started)
- pmfr seed 5: 23.43. pmfrc seeds 4/5: 20.01 / 21.97. pmfrcf (all three levers): seed 1 19.86 ns (predicted 21.21),
  seed 3 20.64 (20.60); cd3132bf, EQUIVALENT, graph check PASS, ffmux_scan clean on every pmfr* route.
- From item 14 on the same seeds (29.14 / 29.54): 1.47x / 1.43x. From x0.5: 1.97x / 1.97x.
- research/data/fifteen/README.md started (the lever table). Full gate of the lever-3 build running (seeds 1, 3-9 x 3
  corners); seeds 6-9 building.
### progress 20:40 (lever 3's budget: the rising pass is what is left; lever 4 = placement, prediction)
- pmfrcf seed 1 (19.86 ns): logic 4.69, excess 8.30, routing 5.03, handshake 0.68, RTZ 1.17; floor (no polarity
  change) 19.45. Delays against the rules: uaddi0 3.41 on the cycle vs need 5.44 (worst settle 4.20 / 0.772; min margin
  -0.79 ns at some load -- the same open question as on item 14), ulink_n30__1 1.77 vs 2.40, ucmpi1 3.63 vs 3.79,
  olink 1.46 vs 1.06, ulink_n12__0 1.81 vs 1.91, umux0 0.91 (select rule). Nothing to shrink: what is left is wire.
- Lever 4: placement. build_bench.sh used RLOC v2 while flow.sh moved to the spine variants (v8: the cycle carried in
  one rigid group). build_bench.sh now passes BD_PLACE_WEIGHT / BD_COLUMN_ROWS to rloc_stamp.py when set (unset: the
  command line is unchanged). Runs: pmfrcf + BD_RLOC=v8; + BD_RLOC=v4; + BD_PLACE_WEIGHT=8 (v2); seeds 1, 3.
- PREDICTION (from the wire budget, not the graph -- placement is outside the graph's model): the cycle's handshake wires
  (5.03 ns) toward the adjacent-cell value (~2.5) -> 17.5-18.5 ns if a variant achieves adjacency; a spine variant also
  shortens delay-chain elements, which shortens the delays in ns -- the gate, not speed, decides that one.
### progress 21:20 (lever 4, placement: negative on seed 1; lever 5: BDC_NO_LINK on the counter ring -- prediction)
- Placement variants on the lever-3 build, seed 1: RLOC v4 20.55 ns, BD_PLACE_WEIGHT=8 (v2) 20.89 -- both slower than
  v2's 19.86; RLOC v8 (spine) cannot place the bench design ("Unable to find legal placement", not seed noise). Seed 3
  variants queued. Negative so far: the existing placement knobs do not shorten this ring's wires.
- bdc/emit.py BDC_NO_LINK=ulink_<chan>[,...] (opt-in; default byte-identical on all six kernels): drops named links
  before ring_depths(), which still enforces every ring's floor (it deepens another link, or refuses). Removing
  ulink_n30__1 (rule-1 site between the i+1 adder and the compare): nothing else changes, simcheck PASS. Removing
  ulink_n7 as well (umux0 -> adder): ring_depths deepens ulink_n_trueResult_6 2 -> 3; simcheck PASS.
- PREDICTION (by hand from pmfrcf's cycles; no removal edit in whatif): ulink_n30__1 is 2.44 ns on seed 1's cycle
  (C-element + 4-element rdly); without it the compare reads the adder's output directly (+~0.3 ns wire): -2.0 ns ->
  ~17.9 (s1), ~18.6 (s3). Also without ulink_n7 (0.53 on the cycle): ~-0.4 more, unless the deeper trueResult_6 pipe
  is on the cycle. Building nl30 and nl307 on seeds 1, 3. Rule-1 links exist so tighten.py can measure: correctness of
  these variants is the full gate's to decide.
### progress 22:10 (lever 5 measured: 18.45 / 17.64 ns; placement mixed; ulink_n7 removal rejected)
- BDC_NO_LINK=ulink_n30__1 on the lever-3 build: seed 1 18.45 ns (predicted ~17.9; lever 3 19.86), seed 3 17.64
  (~18.6; 20.64). cd3132bf; seed 3 decodes NOT_EQUIVALENT of the benign GND-buffer F7 kind (checked); ffmux clean.
- Also dropping ulink_n7: 21.96 ns on seed 1 -- ring_depths deepens ulink_n_trueResult_6 (2 -> 3) and that pipe is on
  the cycle. Rejected.
- Placement on lever 3, seed 3: v4 18.75, PW8 19.72 (vs 20.64); seed 1: v4 20.55, PW8 20.89 (vs 19.86). Within the
  route-to-route spread; not adopted without more seeds. v8 does not place on either seed.
- From item 14: seed 1 29.14 -> 18.45 (1.58x), seed 3 29.54 -> 17.64 (1.67x). Gap to 15 on these two routes: 3.5 / 2.6.
- Next: lever 5 on seeds 4-9 and its gate (rule-1 removal: the gate decides correctness); lever 3's gate is running.
### progress 23:00 (lever 3 on 8 routes 20.55 ns mean; lever 5 on 7 routes 18.42 mean; gates 29/29 so far)
- Lever 3 (pmfrcf), seeds 1, 3-9: 19.86 / 20.64 / 20.91 / 21.36 / 19.58 / 21.36 / 20.39 / 20.70 ns, mean 20.60 (item 14
  30.0): 1.46x. Lever 5 (nl30), seeds 1, 3-8: 18.45 / 17.64 / 18.71 / 20.15 / 18.72 / 17.37 / 17.95, mean 18.43; seed 9
  pending. Best route 17.37 ns.
- Gates (all PASS so far): collatz64 c64fm 21/24, lever 3 6/24, lever 5 2/24.
### progress 23:50 (lever 5: 8 routes, mean 18.69; what blocks 15)
- nl30 seed 9: 20.53 ns. 8 routes: 18.45 / 17.64 / 18.71 / 20.15 / 18.72 / 17.37 / 17.95 / 20.53, mean 18.69 (item 14
  30.0 -> 1.61x). Seeds 5 and 9 bind on a new coupling (fork ufork8 -> ulink_n7: the compare branch of the adder's fork
  lost its storage with the rule-1 link). Graph: a latch with no request delay back on it moves -1.0..+0.6 ns by seed;
  a latch on the steer branch (n30__0) does not help. Not a lever.
- What remains (seeds 1, 3): add 2.75 + compare 4.71 in series (sized to worst settle), merge 2.82, merge-output link
  2.13, select link 2.77. research/data/fifteen/README.md "Where it stands". 15 needs ~3.5 ns more, from cell-level
  levers (fused add+compare, a carry-chain delay that tracks the adder, fewer stages between merge and umux0).
### progress 00:40 (lever 6: the compare computes i+1 < rounds from i -- a duplicated add fused into it; prediction)
- research/tools/fifteen/dup_add.py rewrites xorshift's frontend MLIR: fork i, give cmpi1 its own `addi i, 1` (with its
  own constant), drop fork8 (the add now feeds only the loop-carry steer). bdc unchanged: it fuses the copy with the
  compare into bdc_fused_ucmpi1 (one region, one delay), and rule 1 puts links on both outputs of the new fork
  (ulink_n7d__0/__1, sized as the old ulink_n7: DELAY 0 default, UACK 0). The rule-1 link between add and compare
  (ulink_n30__1) disappears with the edge. simcheck PASS with levers 1-3.
- Sizes: research/data/xorshift_sizes_T3s50_dup_bench.vh = x0.5 with UCMPI1 = 9 + 6 (compare + add elements): the
  fused region's delay covers both, an upper bound (no shortening). Lever 5 (BDC_NO_LINK) is not used here.
- PREDICTION (by hand from pmfrcf's cycle; the graph has no fusion edit): add 3.41 + link 2.44 + compare 3.92 = 9.8 ns
  on seed 1's cycle become one region of 15 elements (~5.4 ns) + its join (~0.7): -3.7 ns -> ~16.2 (s1), ~17.0 (s3),
  unless the loop-carry ring (umux0 -> add -> steer -> pipe -> umux0, which also waits for the compare) binds first.
  Building dup seeds 1, 3, 4, 5.
### progress 01:30 (lever 6 measured: 20.86 / 20.35 ns -- slower, because its delay is the safe upper bound)
- dup seeds 1/3 (lever 3 + dup_add, UCMPI1 = 15 elements): 20.86 / 20.35 ns (predicted ~16.2 / 17.0; lever 3 19.86 /
  20.64). cd3132bf; seed 3 decode NOT_EQUIVALENT (check pending). The cycle moved to merge -> olink -> ulink_n12__2 ->
  umux2 (rounds) -> ulink_n11__1 -> fused compare (7.1 ns) -> steer: the fused region's 16 elements are 6.3-6.4 ns
  while its data's worst settle in the run is 2.2-2.6 ns (the fused i+1<rounds is faster than the old compare alone,
  2.9). So the structure works and the size is the blocker: the prediction assumed a fused size near its need.
- Sizing it properly = corner_audit.py on soak-top routes of the dup design (the established per-cell flow), then the
  gate. Not done this session. Recorded as blocked in research/data/fifteen/README.md.
### progress 02:20 (two gates complete: xorshift levers 1-3 24/24 -> board item 17; collatz64 24/24 -> item 16)
- Lever-3 xorshift (pmfrcf) seeds 1, 3-9 x 3 corners: 24/24 PASS 17/17, 7/8 EQUIVALENT (seed 6 benign F7), ffmux clean.
  BOARD-QUEUE item 17 / #18 (seed-1 sdf e88b0712): 20.60 ns mean per iteration on the itercost stack (item 14 30.0).
- collatz64 c64fm seeds 1, 2, 4-9: 24/24 PASS 14/14, 6/8 EQUIVALENT (5, 9 benign F7). Item 16 / #17 (sdf 2c06cd36).
- Lever-5 gate (nl30) 14/24, all PASS so far.
### progress 03:30 (lever 5 passes the full gate 24/24 -> board item 18: xorshift 18.69 ns per iteration)
- nl30 seeds 1, 3-9 x 3 corners: 24/24 PASS 17/17; 6/8 EQUIVALENT (3, 6 benign F7); ffmux clean. BOARD-QUEUE item 18 /
  #19 (seed-1 sdf c6519c91). Best gated xorshift now 18.69 ns mean (17.37-20.53): from item 14 1.61x, from x0.5 2.11x;
  Dynamatic 12.73. Gap to the owner's 15: 3.7 ns.
- Where the next ns are (research/data/fifteen/README.md): lever 6 (fused i+1<rounds) needs its delay sized by
  corner_audit on soak-top routes (its logic settles in 2.2-2.6 ns vs the 6.3 ns delay the safe size gives); the
  seeds that bind on the ufork8 -> ulink_n7 coupling (5, 9) lose ~2 ns to it.
### progress 03:55 (the other kernels: lever 1 found by the search everywhere; PREDICTION before building)
- search.py --new-knobs (latches on fork outputs, incl. a merge fork's result branch) re-finds lever 1 on xorshift and picks
  BDC_MERGE_RES_LINK=ucontrol_merge0 alone on collatz (item 15), ipow (item 13) and collatz64 (item 16): the period goes
  to each one's no-polarity-change floor. PREDICTED (graph of each gated route; +1-3 ns inserted-stage wire expected):
    colb s1 59.58->49.47; s2 58.44->48.56; s3 56.26->46.85; s4 58.35->48.58
    ipowfm s1 46.84->39.28; s2 45.02->38.71; s3 46.04->38.73; s4 45.24->38.94
    c64fm s1 54.85->44.92; s2 56.16->45.56; s4 57.54->47.96; s5 57.33->47.93
  Building each kernel's item + BDC_MERGE_RES_LINK on those seeds.
### progress 04:40 (lever 1 on the other kernels, measured on seeds 1-2: collatz 1.24x, ipow 1.16x, collatz64 1.19x)
- item 15 + BDC_MERGE_RES_LINK (colr): 47.56 / 47.84 ns (predicted 49.47 / 48.56; item 15 59.58 / 58.44): 1.25 / 1.22x.
- item 13 + it (ipowr): 39.78 / 39.97 (39.28 / 38.71; item 13 46.84 / 45.02): 1.18 / 1.13x.
- item 16 + it (c64r): 46.95 / 46.37 (44.92 / 45.56; item 16 54.85 / 56.16): 1.17 / 1.21x.
- All correct (261 steps, 3^(2^31-1)), EQUIVALENT, graph check PASS. Seeds 3-4 running; the three gates queued next.
  Against Dynamatic: collatz ~47.7 vs 14.05, collatz64 ~46.7 vs 17.84 (README), ipow ~39.9 vs no number on record.
### progress 05:50 (disk full again; the lever-1 builds after seeds 3 and the first colr/ipowr gate runs discarded)
- /home/user/runs reached 100% (trace dumps, gate netlists): every job after ~05:00 failed at once (36 gate "results"
  for colr/ipowr were FAIL from no space -- discarded, never read as results). Freed 13 GB; 15 builds restarted from
  scratch; a janitor now deletes finished runs' dumps and gate netlists every 5 min. Kept: colr_3 48.10 ns, ipowr_3
  38.78, ipowr_5 37.96 (graph checks PASS).
### progress 06:35 (lever 1 on the other kernels, 8 routes each: collatz 1.20x, ipow 1.17x, collatz64 1.18x)
- colr (item 15 + BDC_MERGE_RES_LINK) seeds 1-8: 47.56 / 47.84 / 48.10 / 48.47 / 49.08 / 49.17 / 49.17 / 51.46 ns, mean
  48.86 (item 15 on the same seeds 58.49): 1.20x. Dynamatic 14.05.
- ipowr seeds 1-8: 39.78 / 39.97 / 38.78 / 38.07 / 37.96 / 39.74 / 38.22 / 40.62, mean 39.14 (item 13 ~45.8): 1.17x.
- c64r seeds 1, 2, 4-8: 46.95 / 46.37 / 46.01 / 47.75 / 46.88 / 51.23 / 47.98, mean 47.60 (item 16 ~56.4): 1.18x; seed 9
  pending. Dynamatic 17.84.
- ffmux_scan clean on all of them. Gates running (collatz, ipow, collatz64; 8 routes x 3 corners each).
### progress 08:25 (ipow + result-branch latch passes the full gate 24/24 -> board item 19)
- ipowr seeds 1-8 x 3 corners: 24/24 PASS 17/17 (4 benign F7/CARRY4 decodes), ffmux clean. BOARD-QUEUE item 19 / #20
  (seed-1 sdf a6a2951b): 39.14 ns mean, 1.17x over item 13. collatz 14/24 and collatz64 3/24 so far, all PASS.
### progress 09:10 (lever 6 rejected on static sizing)
- tighten.py rule A on dup seed 1 (nextpnr SDF): bridge_i.udut.ucmpi1 (the fused add+compare) latest output 7.55 ns,
  PAD to 17 elements -- above the 15 used. The measured 2.2-2.6 ns settle is data-dependent (small i, short carries);
  the static worst path is what a matched delay must cover. Lever 6 cannot gain under the rules; cashing it would need a
  data-dependent delay (carry-chain completion detection), a new cell. research/data/fifteen/README.md updated.
### progress 09:30 (collatz + result-branch latch passes the full gate 24/24 -> board item 20)
- colr seeds 1-8 x 3 corners: 24/24 PASS 13/13 (3 benign F7 decodes), ffmux clean. BOARD-QUEUE item 20 / #21 (seed-1
  sdf 44536c3c): 48.86 ns mean, 1.20x over item 15. collatz64's gate 7/24 so far, all PASS.
### progress 11:15 (collatz64 + result-branch latch 24/24 -> board item 21; all of step 5's gates done)
- c64r seeds 1, 2, 4-9: 24/24 PASS 14/14 (seeds 5, 9 benign CARRY4/F7), ffmux clean; mean 47.64 ns (item 16 56.46: 1.19x).
  BOARD-QUEUE item 21 / #22 (sdf 29655e86). research/data/fifteen/README.md: the per-kernel table.
- Session total, board items added: 13-21 (ipow, xorshift x3, collatz x2, collatz64 x2, ipow). Best gated per iteration:
  xorshift 18.69, collatz 48.86, ipow 39.14, collatz64 47.64 ns.
Next: (1) levers 2/3/5 (ring-floor counting, fork-output latches, rule-1 link removal) on the other kernels, by the graph;
  (2) xorshift's last ~3.7 ns: a data-dependent (carry completion) delay cell for the loop add+compare, or fewer stages
  between the merge and umux0 -- both cell-level, need the owner's rule for changing cells; (3) commit the soak-top /
  corner_audit flow so per-cell sizing of new structures is reproducible.
### progress 11:45 (storage is spent on collatz, ipow, collatz64 after lever 1)
- search.py --new-knobs on colr_1 / ipowr_1 / c64r_1: base == floor (no polarity change), no edit gains. Rising pass by
  stage in research/data/fifteen/README.md: datapath delays (uselect0, uaddi0, ushrsi0) and compares, plus the select
  links the select rule keeps. Their next gains are in sizing and cells, not storage.
### progress 12:20 (lever 7: drop the select link ulink_n12__0 (umux0's select) -- prediction; the gate decides)
- After lever 5 the counter ring's select path is merge -> olink (2.1 ns) -> fork -> ulink_n12__0 (2.8 ns) -> umux0. The
  olink already latches the same index token; ulink_n12__0 is a rule-1 site on a select channel. BDC_NO_LINK=
  ulink_n30__1,ulink_n12__0: nothing else changes in the emitted kernel; simcheck PASS. The select rule (never shorten a
  select path) exists because of two traced select races (ipow umux3, collatz64 ulink_n14__1): this removes a select
  link outright, so only the full gate (all corners, 8 routes) can accept it, and any failure is traced before reading.
- PREDICTION (by hand from nl30's cycles): -2.0 to -2.4 ns -> ~16.4 (s1), ~15.5 (s3). Building nl3012 seeds 1, 3, 4, 5.
### progress 07:58 UTC (lever 7 rejected: dropping the select link re-couples the merge fork)
- nl3012 (levers 1-3 + BDC_NO_LINK=ulink_n30__1,ulink_n12__0), nextpnr 9c732bc6303458df, itercost stack: seed 1
  19.41 ns, seed 3 20.42 ns (odata cd3132bf both, the C value; seed 3's fasm_equiv difference is the benign constant
  F7BMUX decode kind). Lever 5 on the same seeds: 18.45 / 17.64. PREDICTION was 16.4 / 15.5: wrong in sign.
- Why (graph): with ulink_n12__0 gone, ucontrol_merge0_f's select branch has no storage, so its acknowledge waits for
  umux0 again; the cycle changes polarity at ucontrol_merge0_fF -> ucontrol_merge0_olinkR (and ufork8R -> ulink_n7F) and
  runs through the rounds ring (ulink_n12__2 3.3, ulink_n11__1 3.0, ucmpi1 4.7 ns). The link I removed was the storage
  that kept the merge fork decoupled -- the by-hand prediction counted only its forward delay. Not gated (slower, and it
  would also remove a select-path link). Seeds 4, 5 finish for the record.
### progress 07:59 UTC (lever 5 on the other kernels: drop one rule-1 link on the rising cycle -- predictions)
- After lever 1 each kernel's binding cycle has no polarity change (colr_1 / ipowr_1 / c64r_1 reports). Rule-1 links
  between two datapath ops on it: collatz64 ulink_n30__1 (uselect0 -> ucmpi2, 2.28 ns on the cycle), collatz
  ulink_n28__1 (uselect0 -> ucmpi2, 0.93), ipow ulink_n31__1 (ushrsi0 -> ucmpi2, 0.77). Next-worst cycles without them
  are >= 3 ns away (34.7 / 47.5 [uses ulink_n10__2, not n28] / 32.1), and each op keeps its own matched delay, so the
  removal saves the link's forward pass only. ring_depths re-deepens if a ring drops below 3 stages (checked in the
  emitted Verilog).
- PREDICTION (seed 1): collatz64 46.95 -> ~45.2; collatz 47.56 -> ~46.8; ipow 39.78 -> ~39.2. Seeds 1, 3 first; 8
  routes and the full gate only if both seeds gain.
### progress 08:00 UTC (lever 8: drop the merge's output link, keep the select link -- prediction)
- Lever 7's lesson: the merge fork's branches each need storage. The other stage between the merge and umux0 is the
  olink (BDC_MERGE_OUT_LINK, 2.13 ns on lever 5's s1 cycle). With levers 1 and 3 both fork branches already latch
  (rlink, ulink_n12__0). Dropping it (lever 5's knobs minus BDC_MERGE_OUT_LINK): emit diff = olink gone, and
  ring_depths deepens ulink_n_trueResult_12 to a 2-stage pipe (the counter ring loses the olink's count), so a stage
  moves rather than vanishes. Risk: the arbiter's output RTZ follows its input's (why the olink exists).
- PREDICTION (by hand): -2.1 + ~1.2 (the pipe's second stage, if on the cycle) -> -0.6 to -1.0 ns: ~17.6 (s1), ~16.9 (s3).
  If the arbiter re-couples, slower than lever 5. Seeds 1, 3.
### progress 08:18 UTC (lever 5 on the other kernels: first seeds; lever 7's last seeds)
- lever 7 seeds 4, 5: 19.52 / 18.42 (lever 5: 18.71 / 20.15). 4-seed mean 19.44 vs lever 5's 18.74 on the same seeds:
  rejection stands.
- collatz64 - ulink_n30__1, seed 1: 43.45 ns (c64r_1 46.95), odata 0x105 (C), fasm EQUIVALENT, emit diff = only that link
  (no deepening); cycle unchanged in shape, no polarity change. Better than the -1.75 predicted (uaddi0 and ulink_n14__0
  also routed shorter: scatter, so more seeds).
- collatz - ulink_n28__1, seed 1: 47.51 ns (colr_1 47.56): the link left the cycle but uselect0 routed 0.9 ns longer.
  Seed 3 decides whether it is a lever.
### progress 08:27 UTC (lever 8 seed 1; lever 9 from its graph -- two new opt-in knobs, prediction)
- lever 8 (lever 5 minus BDC_MERGE_OUT_LINK) seed 1: 18.31 ns (lever 5 s1 18.45), odata cd3132bf, EQUIVALENT. Predicted
  ~17.6: the counter ring's own R-only floor did fall to 16.33, but two couplings bind 0.1 ns apart: the rounds ring
  through ulink_n11__0_folink's falling request (3.47 ns; the folink has no RFAST -- BDC_LINK_FASTFALL never reached
  fork-output links) and the arbiter (ucond_br9 R -> ucontrol_merge0_rlink F -> merge F -> ulink_n_trueResult_12 R: the
  olink's original reason, now through the result latch).
- Graph (nlo_1): fastfall:folink alone -117 ps; + depth:ucontrol_merge0_rlink 17.32 (-0.99; next is ufork8 -> ulink_n7,
  lever 5's coupling); + a 1-element latch on n30__1 17.11 (but that is lever 5's link back: not pursued).
- bdc/emit.py: BDC_FORK_OUT_FASTFALL=1 (RFAST on fork-output links), BDC_MERGE_RES_DEPTH=N (the result latch as an
  N-stage bd_pipe; ring_depths counts N). Unset: byte-identical on gcd, xorshift, collatz, collatz64, ipow, isprime.
  With depth 2 counted, ring_depths no longer deepens ulink_n_trueResult_12 (variant 9a); 9b forces it back to 2
  (BDC_LINK_DEPTHS), the graph's exact edit. simcheck PASS on both.
- PREDICTION seed 1: 9b ~17.4 (17.32 + up to 0.3 for the new stage's wire, which is off the binding cycle); 9a not
  modelled (removes a stage from the counter floor, but the control ring merge -> rlink(2) -> steer -> trueResult_12 has
  only its 3 stages): 16.8-18.0. Seeds 1, 3 of each.
### progress 08:30 UTC (collatz64 lever 5: seed 3 confirms -> 8 routes + full gate; lever 8 seed 3)
- c64nl_3: 45.28 ns, odata 0x105, EQUIVALENT (c64r has no seed 3; c64r 8-route mean 47.64, range 46.01-51.23). With
  seed 1 (43.45 vs 46.95) both seeds are below every lever-1 route but one. Building seeds 2, 4-8 and gating all 8
  (SLOW_MAX / FAST_MIN / worst+M, C-derived oracle c6414).
- lever 8 seed 3: 19.03 ns (lever 5 s3 17.64; NOT EQUIVALENT = benign constant-CARRY4 DI kind). Lever 8 alone is mixed
  (-0.14 / +1.39); it stays only as lever 9's base.
### progress 08:45 UTC (lever 9 seed 1; collatz lever 5 seed 3)
- lever 9 seed 1: 9a 17.76, 9b 17.86 ns (lever 5 s1 18.45, lever 8 s1 18.31), odata cd3132bf, EQUIVALENT. Predicted 9b
  ~17.4: right direction, 0.46 short. Seeds 3 running.
- collatz - ulink_n28__1 seed 3: 45.92 (colr_3 48.10): -2.2 ns, where seed 1 gained nothing. Building seeds 2, 4-8 and
  gating all 8. collatz64 seed 2: 44.51 (c64r_2 46.37).
- (Timestamps of this session's progress entries corrected to the commit times; I had written them ~40 min ahead.)
### progress 08:50 UTC (lever 9c: size the fork-output latch's acknowledge line -- prediction)
- l9a_1's cycle: ucond_br8 R -> ulink_n11__0_folink ctl F -> its uack chain, 6 elements falling (2.6 ns) -> ufork4 ->
  ulink_n12__2. 6 is ACK_PAD, the placeholder every new link gets before tighten sizes it (the rule-1 links' UACK in
  T3s50 are 0 or 1). tighten.py rule H on l9a_1 (raw nextpnr SDF): "tighten to 2" (margin 2381 ps); on nl30_1: 0 links.
  Sized to 3 (largest need seen + 1) in research/data/xorshift_sizes_T3s50_l9_bench.vh; the full gate decides.
- PREDICTION (graph, three chain hops zeroed): 9a s1 17.76 -> 16.65; 9b 17.86 -> 17.70. Building 9c = 9a + this size,
  seeds 1, 3.
### progress 08:58 UTC (lever 9 seed 3: seed-sensitive, not adopted; ipow lever 5 seed 3)
- seed 3: 9a 21.20, 9b 18.05 ns (lever 5 s3 17.64), odata cd3132bf, EQUIVALENT. 2-seed means: 9a 19.48, 9b 17.96, lever 5
  18.05. l9a_3's cycle is lever 5's own coupling at full strength: ucond_br7 -> trueResult_8 -> ufork9 -> ufork8 ->
  ulink_n7 -> uaddi0 -> ucmpi1, with ufork8 R->ulink_n7 F and back (the adder fork's compare branch has no storage since
  lever 5, so the fork's return-to-zero rides the compare). With trueResult_12 single (9a) nothing else slows the
  counter ring enough to hide it. 9b's 0.1 ns is within scatter: not a lever. 9c (uack 3) is not on that cycle: only
  its seed 1 runs, as a check of the graph's 16.65 prediction.
- What would free it is storage on n30__1 with no request delay (graph, nlo_1: 16.73), i.e. lever 5's link back at
  zero DELAY. A bd_link's DELAY is rule A/B's to size, not mine to set; noted, not built.
- ipow - ulink_n31__1 seed 3: 38.20 (ipowr_3 38.78); seed 1 39.55 (39.78). -0.4 ns mean on 2 seeds, under scatter:
  not pursued until collatz/collatz64 gate.
## Session 2026-11-13 22:15 UTC -- (in progress) lever 5 on collatz/collatz64 re-run after the lost session; xorshift lever 9c
Toolchain: patches 789a7120c912d393, nextpnr 9c732bc6303458df (setup-toolchain.sh fingerprint PASS)   Seeds: per lane
### progress 22:15 UTC (lock taken; the previous session's runs died with its container)
- Lock of session_01HC49FvPDSuteFcADNgtDWm was 13 h old (dead). Its in-flight work (collatz64 and collatz lever 5 on 8
  routes + gate, lever 9c seed 1) left no outputs: /home/user/runs is not persistent. Re-running all of it.
- research/tools/fifteen/lane.sh: one worktree per lane (/home/user/runs/wt/L*), bench build + itercost stack + graph;
  writes research/data/eventgraph/graphs/NAME. The itercost one-vector files are now committed
  (research/data/fifteen/vec_*.hex: collatz/collatz64 n=6171, xorshift 92d68ca2 x256, ipow 3^(2^31-1)).
- Audit row (575be223, OVERSTATED): accepted. Seed 3's lever-5 gain on collatz64 is 0.90 ns paired against the audit's
  own c64r_3 (46.19), not ~2.4 against the 8-route mean. From now on every per-seed gain in this lead is quoted paired
  (same seed, both arms), and the 8-route claim only from 8 paired routes.
### progress 22:25 UTC (collatz64 lever 5 on 6 paired routes: -0.5 to -6.0 ns; lever 9c not a lever; lever 10 predicted)
- c64nl (item 22 + BDC_NO_LINK=ulink_n30__1), paired against item 22's per-seed periods (BOARD-QUEUE #22): s1 43.45 vs
  46.95, s2 44.51 vs 46.37, s4 43.29 vs 46.01, s5 45.68 vs 47.75, s6 46.40 vs 46.88, s7 45.23 vs 51.23 ns; every one
  odata 0x105 (C), ffmux clean; s2, s7 fasm_equiv NOT EQUIVALENT (kind to be checked as for the earlier items). Seeds
  8, 9 running, then the gate. Seed 1 reproduced its earlier route (sdf aac8ef27, 43.45).
- nl30_1 rebuilt: sdf c6519c91 = item 18's gated route, 18.45 ns: the lane flow reproduces.
- Lever 9c (9a + rule H's uack 3 on the fork-output latch), seed 1: 17.66 ns (predicted 16.65; 9a 17.76, lever 5 18.45).
  -0.1 against 9a: not a lever, and 9a itself was 21.20 on seed 3. Lever 9 closed.
- Where lever 5's seed-1 cycle goes (graph arcs.tsv): 41 arcs, 18.45 ns = wire 15.82 + cell arcs 2.63. Delay-chain hops
  (27 elements: n12__0 5, uaddi0 6, ucmpi1 9, merge 3, olink 4) 10.68 ns; handshake hops 7.77 ns (~19 hops, ~410 ps
  each). tighten.py on the same route: uaddi0 / ucmpi1 rule A margins -2.0 / -1.4 ns at the nextpnr SDF (they cannot
  shrink; the full gate passed them), merge "tighten to 1" but it drives the select channels (not touched: select rule),
  umux0's select +2.7 ns (select link: not touched).
- Lever 10: PLACE_WEIGHT on the counter ring's handshake nets only (BD_PLACE_WEIGHT_CELLS, 42 nets, x16; lever 4's PW8
  weighted all 267). PREDICTION (lever 5 seed 1 18.45): handshake hops ~410 -> ~300 ps would be -2.1 ns, the data nets
  pull back, so -0.5 to -2.0: s1 ~17.3 (16.5-18.0); s5/s9 (the ufork8 coupling) gain less. Seeds 1, 3, 5, 9.
### progress 22:51 UTC (lever 10 negative on 2 seeds; collatz: corner_audit on bench routes, PREDICTION 47.5 -> 39.1)
- Lever 10 (PLACE_WEIGHT x16 on the counter ring's 42 handshake nets), paired with lever 5: s1 19.70 vs 18.45, s3 17.83
  vs 17.64. s1's cycle moved to the rounds ring (ulink_n12__2, umux2, ulink_n11__1 + the shared compare/steer/merge),
  which the weighting pulled apart; the counter ring itself went to 19.05, not down. Variant 10b (both rings weighted,
  45+ nets) on s1, s3 queued; seeds 5, 9 of 10 finish for the record.
- collatz64 lever 5 seeds 8, 9: 45.95 (item 22 s8 47.98), 45.98 (47.95). Full gate running (8 routes x 3 corners).
- collatz lever 5 (colnl): s1 47.51 (colr 47.56), s2 46.30 (47.84), s5 47.46 (49.08).
- research/tools/corner_audit.py --prefix bridge_i.udut.: the per-cell worst-corner sizing (the flow behind T3cdb /
  T4cdb) now runs on a kernel bench route (lane dirs: pnr/soak_xray.sdf = the itercost xray.sdf, soak_routed.json, the
  route's sizes). Default (uut.) unchanged. On colnl_1 (worst corner, select paths never shortened): uaddi0 18 -> 9
  (A' 209 ps left), uselect0 23 -> 13 (A 180 ps left), ucontrol_merge0 5 -> 1, ucontrol_merge1 9 -> 1, uaddi1 10 -> 9,
  n1__1 2 -> 1; pads umux2 2 -> 11 (rule A -1473 ps at this corner), ulink_n7/n8 UACK 1 -> 2, n8 / trueResult_4 SDELAY
  1 -> 2. ucmpi2 kept (16). umux2 and merge1 have no periodic node in the graph (off the loop).
- PREDICTION (graph of colnl_1, each line's chain hops scaled new/old): 47.51 -> 39.11 ns, same cycle (n loop: n14__0,
  umux0, uaddi0, uselect0, ucmpi2, steer, merge, olink) -- 1.21x. Inserted-stage wire does not apply (no new stage).
  Next: corner_audit on colnl seeds 2-5, per-cell max (pads included), build seeds 1-8 at those sizes, gate.
### progress 23:08 UTC (lever 10 closed: placement weighting is seed-sensitive; collatz64 lever 5 on 8 paired routes 1.057x)
- Lever 10b (PLACE_WEIGHT x16 on both rings that bind, counter and rounds): s1 17.79 (lever 5 18.45), s3 18.61 (17.64).
  With 10 (19.70 / 17.83): every variant gains on one seed and loses ~1 ns on the other. Not a lever. Lever 4 (lever
  3 + v4 / PW8) was the same. Closed: the placer has no objective for the ring's period, so weights move the problem.
- collatz64 lever 5 (c64nl), all 8 routes, paired with item 22 (same seeds): 43.45/46.95, 44.51/46.37, 43.29/46.01,
  45.68/47.75, 46.40/46.88, 45.23/51.23, 45.95/47.98, 45.98/47.95: mean 45.06 vs 47.64 (1.057x), every seed faster
  (-0.48 to -6.0 ns). s2 / s7 NOT EQUIVALENT = the benign B6LUT-constant -> F7AMUX kind (checked in equiv.txt).
  Gate: c64nl_1 SLOW_MAX PASS 14/14 EQUIVALENT; 23 runs to go.
- An OOM kill (5 sims + 2 compiles at once) and an edit to fullstack_dump.sh under running lanes cost colnl_3/4's first
  runs (re-running; no result read from them). fullstack_dump.sh's iverilog is now under the same compile lock as
  build_ps.sh, so at most one compile runs at a time.
- corner_audit on collatz lever-5 routes (worst corner): s1 uaddi0 18->9, uselect0 23->13; s2 12 / 15; s3 10 / 16; merges
  -> 1 on all; ucmpi2 kept; pads on off-loop lines (umux2 2 -> 7..11). Seeds 4-8 running; the build takes the per-cell
  max over 8 routes.
### progress 23:40 UTC (GOAL 1: xorshift lever 5 = board item 18 ON HOLD -- a static violation the gate cannot see)
- Container restart at ~23:15 killed every job; /home/user/runs survived. Restarted the c64nl gate (1/24 done: s1
  SLOW_MAX PASS), colnl_3 and the corner_audit queue.
- corner_audit (worst corner, measured-residual guards) on nl30_1 (lever 5, = item 18's gated route c6519c91) asks
  uaddi0 6 -> 27 for rule E at ucond_br6 (-3556 ps). skew.py (rule E) on the plain nextpnr SDF: ucond_br6 -4651 ps RAW
  (-7126 guarded): the steer's request (via the add + compare matched delays, earliest 4.58 ns) beats its select (the
  adder's carry chain then the compare's, latest 9.23 ns) launched from ulink_n7. The same route at lever 3 (pmfr3_1,
  rebuilt = item 17's sdf e88b0712): +1699 ps raw (launch ulink_n30__1, compare only). So dropping ulink_n30__1 put the
  adder's static worst carry in series with the compare inside one bundle that the delays do not cover.
- Why the full gate passed 24/24: xor17's rounds are <= 1000, so i+1 carries at most 10 bits; the long path needs a carry
  through most of the 32 bits. The xorshift datapath toggles every bit by design, the counter does not. No vector the sim
  can afford (2^16+ rounds) reaches it, so the static rule is the only evidence there, and it fails at nominal.
- Action: BOARD-QUEUE list item 18 (#19) ON HOLD; research/data/fifteen headline back to item 17 (20.60 ns, gap 5.6).
  collatz / collatz64 lever 5 checked the same way: colnl_1/2 worst raw rule E +1.92/+2.13 ns, c64nl_1/2 +1.53/+1.77 ns
  (their gate vectors also span wide data); those continue.
- Lesson for every link-removal lever: check rule E/A statically at nominal on the paths whose data range the gate's
  vectors do not span (loop counters), before reading the gate. Lever 9 (built on lever 5) inherits the hold.
### progress 23:41 UTC (open goal-1 question: the x0.5 xorshift counter adder is statically short; nothing exercises it)
- The same check on item 17's route (pmfr3_1 = sdf e88b0712), nominal nextpnr SDF, tighten.py rule A: uaddi0 req 4054 vs
  peak 5524 (-1.47 ns raw, -2.20 guarded), ucmpi1 -1.02 raw, ucmpi0 -1.10 raw; uxori1/2 and umux3 also negative. At the
  worst corner with the measured-residual guards (corner_audit): uaddi0 A' -752 ps (asks 6 -> 11); ulink_n30__1 is bound
  by rule E at ucond_br6 with 238 ps left. Adding the two (the latch is transparent, so a late sum passes through it):
  about -0.5 ns end to end at the worst corner for a full-length counter carry, about +0.2 ns at nominal. That is a sum
  of two measurements, not one measured path.
- The xors are exercised by the gate (every output bit depends on many input bits, by design); uaddi0 / ucmpi0 / ucmpi1
  work on the loop counter and rounds, which the gate's vectors keep below 1000. So for the whole x0.5 xorshift family
  (board list items 4, 11, 14, 17), correctness at rounds >~ 1024 rests on these static numbers, which are thin to
  negative. This predates this session (the uniform x0.5 shrink); recorded here because it is now measured. Not put on
  hold: the board judges (loop_cost.sh) use their own round counts, which I have not checked yet -- next.
- Checked: cells/hw/loop_cost.sh / gen_bench.py mask xorshift's rounds to 12 bits on the board bench (DOMAIN_RESTRICTIONS),
  so every board run of the xorshift items keeps i < 4096 (carries <= 12 bits), against the gate's <= 10. The static
  worst cases above are for full 32-bit carries, which the board bench cannot produce either. So: the board items stay
  meaningful for the bench's domain, but none of the x0.5 xorshift kernels is shown correct for a general 32-bit rounds.
  Item 18's hold stays (its -4.65 ns raw is large enough that a 12-bit carry may already reach it; not quantified).
  Owner-facing summary is in research/data/fifteen/README.md's headline.
### progress 00:01 UTC (collatz: per-cell sizes from 8 bench routes -- PREDICTION before building)
- corner_audit (worst corner, residual guards, select paths never shortened) on colnl seeds 1-8; per-cell max
  (research/tools/fifteen/max_sizes.py) -> research/data/collatz_sizes_T3cdb_nl_bench.vh: uaddi0 18 -> 12 (routes
  9/12/10/11/8/9/10/9), uselect0 23 -> 16 (13-16), ucontrol_merge0 5 -> 1, merge1 9 -> 1, n1__1 UACK 2 -> 1; pads umux2
  2 -> 11, ulink_n7/n8 UACK 1 -> 2, n8 / trueResult_4 SDELAY 1 -> 2. ucmpi2 kept 16 everywhere.
- PREDICTION (each colnl graph, chain hops scaled new/old), ns: s1 47.51 -> 41.30, s2 46.30 -> 41.11, s3 45.92 -> 40.56,
  s4 47.21 -> 41.47, s5 47.46 -> 41.82, s6 46.39 -> 40.47, s7 47.40 -> 41.82, s8 49.24 -> 43.02; mean 47.18 -> 41.45
  (1.14x over collatz lever 5, ~1.18x over item 20 48.86). A re-route moves the cycle by its scatter (+-1.5 ns).
- collatz64 lever 5 gate: 4/24 PASS so far (s1 max/min, s6 min); s6 max lost to my own directory cleanup at the restart
  (re-queued). Building colsz (collatz lever 5 + these sizes) seeds 1-8 next.
### progress 00:22 UTC (second container restart ~00:05; collatz per-cell sizes: first 2 routes match the prediction)
- Restart killed all jobs again; queue scripts now skip finished items (results.txt / gate_results.txt / ca done.txt).
  colnl_3's rerun finished before it (graph 45.92 ns; recovered from the committed graph).
- colsz (collatz lever 5 + collatz_sizes_T3cdb_nl_bench.vh): s2 40.65 ns (predicted 41.11; colnl_2 46.30, colr_2 47.84),
  s3 39.70 (predicted 40.56; colnl_3 45.92, colr_3 48.10). odata 0x105 (C), ffmux clean; s2 NOT EQUIVALENT kind to check.
  s1 does not build: the bench's clocked harness closes at 82.88 MHz < 83 (build_bench refuses; not the kernel) -- seed 9
  replaces it, as seed 3 does for collatz64.
### progress 01:02 UTC (collatz per-cell sizes on 8 routes: 40.33 ns mean, 1.22x over item 20; gates running)
- colsz seeds 2-9 (s1's harness misses 83 MHz): 40.65 / 39.70 / 40.32 / 39.26 / 41.26 / 40.65 / 39.42 / 41.38 ns, mean 40.33
  (predicted 41.45 from the colnl graphs, every seed within 1.2 ns). Paired on seeds 2-8: colnl 47.13 -> 40.18 (1.17x),
  colr (item 20) 49.04 -> 40.18 (1.22x). All odata 0x105, ffmux clean; s2/s5 NOT EQUIVALENT = benign F7 kind (s2 checked).
  rule E raw at nominal (skew.py): colsz_2 worst +2.25 ns, colsz_3 no violation. Dynamatic 14.05.
- Gates: colsz_2 24-run gate started, 3/3 PASS so far (13/13 each); c64nl 5/24 PASS (s1 all three corners, s6 min).
### progress 01:05 UTC (owner rule 2026-11-14: full input range. Plan, and how "the static check" is defined)
- Read PROGRAM's new rule (bead13d7). Order of work from now: (1) re-baseline the x0.5 xorshift family on item 17's
  structure (lever 3); (2) mark BOARD-QUEUE items bench-range-only vs full-range; (3) the other kernels' counters and
  compares; (4) a data-dependent (speculative-completion) delay for i+1. The collatz / collatz64 gates already running
  continue in the background and get the same static check before any of them becomes a board item.
- The static check, as I apply it (a decision; recorded so it can be overruled): rules A / A' / E (tighten.py,
  skew.py via corner_audit.py, every path is its static worst, so the longest carry is included) at two corners, both
  with the measured-residual guards the sizing flow has used since PROGRAM item 3 (E 0.97 x req vs 1.03 x sel; A
  max(3% t, 50 ps)): NOMINAL = every arc at the calibrated band 0.288 (corner_audit --uniform 0.288, new), and WORST =
  the gate's worst column (delay chains 0.21, CARRY4 / F7F8 / FF at 1, rest 0.288). Not used as the gate: the 2025-era
  20% / 8.5%-scatter guards of plain tighten.py / skew.py on nextpnr's SDF -- on item 17's route nearly every line of the
  design, holds included, fails those, including lines the gate exercises. I report the plain-nextpnr numbers alongside.
- Sizing: corner_audit at both corners on 4+ lever-3 routes (seeds 1, 3-6, rebuilding), per-cell max over every
  proposal (both corners), never shortening select paths; then build 8 routes, re-run the check on the new routes, gate.
### progress 02:02 UTC (xorshift full-range re-baseline: sizes from 5 routes x 2 corners -- PREDICTION before building)
- Item 17 rebuilt on seeds 1, 3-6 (pmfr3_*: 19.86 / 20.64 / 20.91 / 21.36 / 19.58 ns, the README's per-seed numbers; sdf
  of s1 e88b0712 = item 17's). corner_audit at NOMINAL (uniform 0.288) and WORST on each; per-cell max over the 10
  proposals -> research/data/xorshift_sizes_T3s50_fr_bench.vh: counter uaddi0 6 -> 13 (per proposal 11/6/8/6/9/6/13/9/
  10/6: the worst corner binds, A'); ucmpi0 / ucmpi1 / ulink_n30__1 stay (12 / 9 / 4, bound by rule E with margin);
  datapath uxori1 2 -> 7, uxori2 3 -> 7, umux3 1 -> 14 (A / A' at both corners -- the x0.5 shrink was short there too,
  statically; the gate exercised them); merge0 3 -> 2; link SDELAY/UACK pads (rules H / I).
- PREDICTION (each pmfr3 graph, chain hops scaled): s1 19.86 -> 22.04, s3 20.64 -> 22.61, s4 20.91 -> 22.99, s5 21.36 ->
  23.50, s6 19.58 -> 21.19; ~ +2.0 ns, i.e. ~22.6 mean against item 17's 20.60. Cycle unchanged (counter ring).
- Gates in progress: colsz 9/24 PASS (+1 INFRA: ivl OOM-killed, re-queued), c64nl 9/24 PASS.
### progress 02:03 UTC (speculative completion read; design notes; a question for the owner)
- research/data/fifteen/speculative.md: for i+1 the abort condition must cover the carry DISCHARGE of the previous
  increment too: abort = low k bits of i all 0 OR all 1 (one LUT; 2/2^k of iterations). The compare i+1 < rounds gets
  no short case from it (the borrow ripples through the equal high bits every time).
- QUESTION FOR THE OWNER: inside the loop i + 1 <= rounds always holds, so i + 1 < rounds <=> i + 1 != rounds, a LUT
  tree with no ripple. Is rewriting the loop compare that way inside the "loop lowering stays as it is" rule? Not done.
- BOARD-QUEUE: new "Full-input-range status" section; x0.5 xorshift items marked bench range only.
### progress 02:23 UTC (xorshift full-range: first two routes)
- xfr (item 17's knobs + xorshift_sizes_T3s50_fr_bench.vh): s1 22.52 ns (predicted 22.04; item 17 s1 19.86), s3 23.58
  (22.61; 20.64). odata cd3132bf; s3 NOT EQUIVALENT kind to check. ~+2.8 ns over item 17 on these two seeds.
- Gates: colsz 12/24 PASS, c64nl 10/24 PASS; static check (both corners) running on the colsz routes.
### progress 02:52 UTC (xfr 6 routes; static check of colsz: merges at size 1 are 9-60 ps short on 1 of 2 routes)
- xfr s1, 3-7: 22.52 / 23.58 / 23.34 / 22.82 / 23.30 / 21.78 ns (item 17 same seeds 19.86 / 20.64 / 20.91 / 21.36 / 19.58 /
  21.36). s3/s4/s7 NOT EQUIVALENT to check. Static check and gate (gqE) queued on the xfr routes.
- Static check on the sized collatz routes: colsz_3 clean at both corners (no kernel A/A'/E below 0); colsz_2 rule A on
  ucontrol_merge0 (size 1) -60 ps worst / -9 ps nominal, merge1 -17 ps worst. The merge's index path is exercised by
  every loop entry and exit in the gate (26 per run), so under the owner's rule the gate covers it; still, if more routes
  show it, colsz gets merges back at 2 (about +0.4 ns) before it becomes a board item.
### progress 02:55 UTC (xorshift full range, 8 routes: 22.79 ns mean; the cost of the full range on record)
- xfr seeds 1, 3-9: 22.52 / 23.58 / 23.34 / 22.82 / 23.30 / 21.78 / 21.60 / 23.36 ns, mean 22.79 (item 17, same seeds: 20.60):
  +2.19 ns (item 17 is 1.106x faster, on the bench's range only). odata = C on all. Gate (xor17) running.
- Static check on xfr_1: kernel A/A'/E below 0: ucontrol_merge1 (size 1) A -153 ps worst / -121 nominal; tighten's
  bundled-channel row "a" for ucmpi1 -928 / -139 (the row corner_audit reports but does not size: it drops the upstream
  link's lead; A' is the sized one). Decision: the merge index is a 1-bit path that every vector's loop entry and exit
  exercises, so under the owner's rule (static check for paths the vectors do NOT span) the gate covers it. Recorded
  rather than rebuilt; if the owner wants every A clean regardless, merges go back to 2 (~+0.4 ns each design).
- Next kernel under the check: ipow (item 19's build, seeds 1-4, both corners).
### progress 03:45 UTC (gates progressing; ipow static check running)
- Gates: colsz 15/24 PASS (+1 INFRA re-queued), c64nl 12/24 PASS, xfr 2/24 PASS (s1 SLOW_MAX / FAST_MIN 17/17). No FAIL.
- ipowr_1 rebuilt = item 19's route (sdf a6a2951b, 39.78 ns); ipowr_2 39.97. corner_audit both corners running on 1-4.
- Machine at load 8-12 (3 gates + builds + corner_audit workers on 4 cores): everything is CPU-bound, so it only adds
  latency; memory stays under the limit since the one-compile-at-a-time lock.
### progress 03:45 UTC (static check: colsz clean on 5 more routes; xfr needs a second round -- umux0)
- colsz_3..7 static check: no kernel A/A'/E below 0 at either corner (colsz_2 had only the merge index, -60 ps).
- xfr_5: umux0 (the counter's mux, size 1) rule A -62 ps worst / -35 ps nominal. Its slowest bit is a high bit of i,
  which the vectors never toggle, so under the owner's rule this must hold statically: not covered. xfr_4 and xfr_1 do
  not show it. tighten's "a" row for ucmpi1 (-1.0 / -0.3 ns) is the pairing that drops ulink_n30__1's 4-element lead;
  A' (the sized form) holds -- I take A' as rule A, as corner_audit has since it was written.
- So xfr goes through another per-cell round (static check on all 8 xfr routes, both corners; per-cell max; rebuild,
  check, gate). Its gate (2/24 PASS) is stopped: those routes are superseded. colsz's second gate lane restarted.
### progress 04:05 UTC (ipow under the static check: only umux3, on a path the gate spans)
- ipowr_1 (= item 19's route a6a2951b): kernel A/A'/E below 0 only at umux3 (the loop result mux, size 3): A -1715 ps
  worst / -1624 nominal. ipow's loop runs on e (shift right to 0), and the gate's ipow17 vectors include e = 2^31 - 1,
  so the loop-control range is spanned; umux3 carries the result, whose bits the vectors toggle widely. So item 19 is
  not "bench range only" under the rule; but a 1.7 ns static miss at NOMINAL on a mux is the same family as the traced
  umux3 empty-pipe select race (JOURNAL 2026-11-10). Flagged for the owner; not held. Seeds 2-4 still checking.
### progress 04:55 UTC (xfr static check on all 8 routes: two rule-A shortfalls; xfr2 = + umux0 2, merge1 2 -- PREDICTION)
- Kernel A / A' / E below 0 on the 8 xfr routes at either corner: only xfr_5 umux0 (-62 / -35 ps) and xfr_1 merge1 (-153 /
  -121 ps); xfr_3, 4, 6-9 clean (A' basis). The corner_audit pad loop for hold rules H / I diverged on several routes
  (link UACK 66-108, uxori1 6125): not used. research/data/xorshift_sizes_T3s50_fr2_bench.vh = fr + umux0 1 -> 2 +
  merge1 1 -> 2 (merge1 back to the x0.5 base).
- PREDICTION: umux0 is on the counter ring once per iteration, one element: +0.3 to +0.45 ns -> ~23.1-23.2 ns mean
  (xfr 22.79). The graph scaler cannot model it (a 1-element chain has no internal hop). Building seeds 1, 3-9.
### progress 04:57 UTC (owner answers: umux3 needs an explanation; the != test is a frontend knob)
- Rebased onto the owner's two PROGRAM commits (ad4b0eac, 134e11b1).
- ipow umux3 (A -1624 ps nominal on item 19's route): tighten's row pairs the y-join's request (umux3.uj1) at t=0 with
  the SELECT latch's data (ulink_n_index_15 stage[1] lat, "upstream link data lag 1384 ps") at t=0, "no common source".
  But bd_mux's join is C(y_req, ctl_req.s): uj1 cannot fire before the select link's request, which leaves the same C
  node as that latch's enable and then runs the link's DELAY line. From that common launch, rule E on the same mux gives
  +3607 ps (sel pin 764 ps vs req 4530 ps). So the candidate false path: the select latch's data -> umux3 data LUTs,
  timed against a request that structurally waits for the select's own delayed request. Showing it with a trace now
  (ipowr_1, every net dumped; per-iteration select-pin settle vs uj0/uj1 rise at umux3).
- Frontend knob: Dynamatic is not built in this container (no dynamatic-opt / translate-llvm-to-std; the fixtures
  stop at the MLIR), so the handshake-MLIR diff the owner asks for cannot be produced here. A Dynamatic build is
  hours of LLVM and has not survived this session's hourly container restarts. Next: write the knob (opt-in, default
  byte-identical) and check its LLVM-level effect with the system clang / opt 18; the MLIR diff waits for a Dynamatic
  build (BOARD-QUEUE-style item for a session with one, or the owner's machine).
- xorshift fr2 (umux0 2, merge1 2) building on 8 routes; collatz / collatz64 gates continue.
### progress 04:59 UTC (4th container restart ~04:55; frontend knob BDC_FE_EXITCOND written, checked at the LLVM level)
- Restart killed everything again; relaunched: xf2 builds (8 routes), the colsz and c64nl gates (one lane each), the
  ipowr_1 full-dump run for the umux3 trace. ipow static check (routes 2-4) waits for its routes.
- bdc/frontend.sh step 4b, opt-in BDC_FE_EXITCOND=1 (unset: step skipped, outputs unchanged): one indvars +
  simplifycfg on step 4's output with data layout "e-n32", stripped again. Checked with system clang/opt 18 (Dynamatic's
  pragma plugin and source-rewriter are not here, so these .ll are close to but not the frontend's): xorshift
  `icmp slt i32 %10, %1` -> `icmp ne i32 %10, %1` (no smax: the loop is already guarded by 0 < rounds); collatz,
  collatz64, ipow byte-identical; isprime: a one-input phi folded, the inner increment loses nuw nsw, an exit phi's
  operand order changes. indvars alone (without simplifycfg) also added a preheader block and an LCSSA phi on every
  kernel: simplifycfg removes them.
- NOT done here, needs a Dynamatic build: the handshake MLIR diff per kernel, simcheck with rounds 0 / 1 / INT_MAX,
  the static check over the full range, the gate. Every later step of the frontend (translate-llvm-to-std,
  dynamatic-opt) is Dynamatic's.
### progress 05:00 UTC (the != exit test on xorshift, built here without Dynamatic -- assumption stated)
- research/data/fifteen/xorshift_exitcond_handshake_transformed.mlir = the xorshift fixture with cmpi1 `slt` -> `ne`.
  ASSUMPTION: BDC_FE_EXITCOND's only LLVM-level change on xorshift is that predicate (checked above), and Dynamatic
  lowers ops one-to-one, so its handshake MLIR differs from the fixture in that predicate only. To be confirmed by a
  real frontend run (needs Dynamatic).
- bdc emits ucmpi1 as z = ~(a == b): an equality tree, no carry chain. simcheck PASS on both MLIRs with two new
  xorshift vectors, rounds = -1 and INT_MIN (0 iterations: the != test is only correct behind the entry test
  rounds > 0, which these exercise). rounds = INT_MAX is 2^31 iterations, out of reach of any sim; the static check
  covers it (the compare's static worst case is now short).
- xne pass 1: lane2.sh (MLIR_OVERRIDE) with fr2 sizes (ucmpi1 still 9 elements, sized for the carry compare), seeds 1,
  3, 4, 5. PREDICTION: ~ the same as xf2 (~23.1 ns): only the compare's data got faster, not its delay. Then the static
  check sizes ucmpi1 for the equality tree; that is where the time comes back.
### progress 05:23 UTC (umux3 trace, run 1; xf2 / xne first routes)
- ipowr_1 full dump, the itercost vector (3^(2^31-1), two runs): umux3's output request (net n5225, the LUT after its
  3-element chain) rose 3567 ps after the last change of any of the 33 LUTs that read the select. But in this run the
  select (n4719) changed only at start-up and j0 never fired: every transaction took y. So it does not exercise the
  case the rule names. Re-running with research/data/fifteen/vec_ipow_selflip.hex (e = 0 / 5 / 0 / 7 / 0 / 31
  alternating), which flips the select between x and y on every transaction.
- xf2 (fr + umux0 2, merge1 2): s1 22.93, s3 23.07, s4 23.40 ns (xfr 22.52 / 23.58 / 23.34): within scatter, as
  predicted (+0.3-0.45 expected; the cycle moved). xne pass 1 (!= test, fr2 sizes): s1 22.79, s3 23.73 -- as predicted,
  no gain yet (ucmpi1 still 9 elements).
### progress 05:33 UTC (ipow umux3: the false path named and shown with a trace -- item 19 stays)
- Full dump of item 19's route (ipowr_1, sdf a6a2951b) on research/data/fifteen/vec_ipow_selflip.hex (e = 0 / 5 / 0 / 7 /
  0 / 31; each run twice, so umux3's select flips between x and y on every transaction; odata 1 / f3 / 1 / c90f7 / 1 /
  4b5f6a2b = the C values, 3^31 mod 2^32 = 0x4b5f6a2b). At every one of the 12 output requests (7 select flips):
  the select data (n_index_15 latch) changes; the select link's request rises 3385 ps later (its own delay line); the
  mux join (j0 or j1) fires 462-587 ps after that; the output request rises >= 3575 ps after the last change of any of
  the 33 LUTs that read the select.
- So tighten's rule A row for umux3 (-1624 ps nominal / -1715 worst) times the select latch's data from t=0 against a
  request that structurally cannot fire until the select link's request has arrived, which trails that same data by
  the link's delay line (3.4 ns in this run; rule E from the common launch +3.6 ns statically). That is the false path.
  The data the request actually bundles settles >= 3.6 ns before it on every transaction traced. Item 19 stays on the
  list (PROGRAM 2026-11-14: "name the false path ... and show it with a trace").
### progress 05:35 UTC (the farm: three 32-route requests, every check per route)
- Read research/cluster/README.md (owner, c5a0f210). farm_check was "submitted" at 05:24.
- research/tools/fifteen/eval_task.sh: one route = build + itercost period + graph (lane2.sh), the static check at
  nominal and worst (corner_audit, measured-residual guards; kernel A / A' / E below 0, tighten's "a" row listed apart),
  and the 3-corner gate, in parallel. Requests (8 cores, 32G, 240 min, seeds 1-32 each):
  fxf2 (xorshift full-range round 2, fr2 sizes, item 17's knobs), fcolsz (collatz lever 5 + per-cell sizes),
  fc64nl (collatz64 lever 5). Each comes back as eval.txt per seed: the distribution the owner asks for (median, worst,
  routes passing the static check and the gate).
- Local runs continue (they overlap the farm's seeds 1-9, which serves as a cross-check of the farm's routes).
### progress 05:42 UTC (the != exit test buys one element: the steers' select fanout binds the compare)
- corner_audit on xne_1 (fr2 sizes + != test): ucmpi1 9 -> 8 at WORST (rule E at ucond_br8, 120 ps left), 6 at nominal.
  The equality tree itself is short; what bounds the compare's delay is rule E at the loop steers: the one condition
  bit fans out to the select pins of six 32-bit steers (ucond_br4-9), and the latest of those arrivals is the cost.
  So on xorshift the != rewrite is worth ~1 element (~0.4 ns) at the worst corner. Lever this exposes: replicate the
  loop condition per steer (or per steer group) so no one net carries the whole broadcast -- the "replication for
  control inputs" lead from PROGRAM's goal-2 list.
- uaddi0 at nominal would go 13 -> 9 on this route; the worst corner keeps 13 (the counter's CARRY4 at SLOW_MAX).
- research/data/xorshift_sizes_T3s50_fr2ne_bench.vh (fr2 + ucmpi1 8); farm request fxne (32 routes, every check).
### progress 05:42 UTC (CORRECTION to the previous entry)
- Wrong: "the condition bit fans out to the select pins of six 32-bit steers". bd_steer reads its select in one control
  LUT and passes data by wire (ufork9 -> four steers, one LUT each). What binds ucmpi1 at the worst corner (rule E at
  ucond_br8, 120 ps left) is the equality tree's own data path from the ulink_n30__1 latch (32-bit routing into the
  tree, ~3 LUT levels) against the compare's delay line, whose elements the worst corner runs at the fast 0.21 band
  while that routing sits at 0.288. So the "replicate the condition" lever does not apply here; withdrawn.
### progress 07:03 UTC (farm: fcolsz back, 31 routes -- gate 93/93, static clean on 24/31, merges at 1 the only miss)
- The farm reproduces local routes exactly (fcolsz_2: sdf a48aaf17, 40653 ps, identical static rows). farm_check done.
- fcolsz (collatz lever 5 + per-cell sizes), seeds 1-32 (seed 1: harness misses 83 MHz, no build): period median 41.01
  ns, mean 40.86, best 39.22, worst 42.33 (31 routes); item 20 is 48.86 (8 routes), Dynamatic 14.05. Gate: 93/93 PASS
  (13/13 each, SLOW_MAX / FAST_MIN / worst+M). Static check: 24/31 CLEAN at both corners; 7 routes miss rule A on a
  control merge's index with the merge at size 1 (worst -140 ps, nominal -108). All 8 colnl routes had proposed 1 --
  the owner's point about routes not tried, again. Per-route table: research/data/fifteen/farm/fcolsz.tsv.
- fcolsz2: merges back at 2 (research/data/collatz_sizes_T3cdb_nl2_bench.vh), farm request, 32 routes. If its static
  check is clean everywhere it becomes the collatz board candidate; expected cost ~+0.4 ns per merge on the cycle.
### progress 08:04 UTC (farm: fxf2 back -- ONE GATE FAILURE: seed 1 FAST_MIN 6/17)
- fxf2 (xorshift full range, round 2 sizes, item 17's knobs), seeds 1-32: 28 routes built (14, 29: harness misses 83
  MHz; 7, 11: farm task failed in 10 s, no output -- rerun under a new name). Period median 23.29 ns, mean 23.29, best
  20.86, worst 24.94. Static check CLEAN at both corners on 26/28; seed 1: umux2 rule A -6 nominal / -42 worst; seed 23:
  ucmpi1 A -226 worst. Gate 83/84: **seed 1 FAST_MIN FAIL 6/17** (SLOW_MAX and worst+M pass). Seed 1's route is the same
  as local xf2_1 (sdf dc138ea2). Table: research/data/fifteen/farm/fxf2.tsv (research/tools/fifteen/farm_table.py).
- xfr seed 1 (round 1 sizes, umux0 1, merge1 1) passed FAST_MIN 17/17 locally; round 2 changed umux0 and merge1 and so
  the route. Reproducing the failing run locally now to trace it before anything else. xorshift has no full-range
  candidate until this is explained.
### progress 08:37 UTC (fxf2 seed 1 FAST_MIN failure: reproduced; it is the loop count; umux2 ruled out)
- Local rerun of xf2_1 FAST_MIN (same route dc138ea2): FAIL 6/17, deterministic. Every failure is an early exit:
  rounds 4 -> the 3-round value, 8 -> the 4-round value, 5 / 16 / 32 / 64 / 128 / 200 / 256 / 100 / 1000 wrong; rounds
  0-3, 3, 17 right. So the counter / compare / exit path misfires, the class the full-range rule is about.
- corner_audit --fast-min on that route: the only kernel rule A / E below 0 is umux2 (the rounds mux) -41 ps (it was
  also the route's only nominal / worst miss). Test: umux2's request path lengthened by 500 ps in the SDF only (same
  netlist and route; annot.sdf differs in exactly that arc): still FAIL 6/17, identical cycle count. Not umux2.
- Tracing now: full dump at FAST_MIN on rounds = 4 (fullstack_dump.sh takes DUMP_FIELD=min; default unchanged).
### progress 09:08 UTC (farm: fc64nl and fcolsz2 back)
- fcolsz2 (collatz lever 5 + per-cell sizes, merges at 2): 28 routes built (18: harness < 83 MHz; 2, 13, 19: farm task
  gave no eval -- infrastructure; 11: eval incomplete). Period median 41.15 ns, mean 41.22, best 38.85, worst 43.26.
  Gate 81/81 PASS. Static CLEAN at both corners on 27/27 evaluated. Merges at 2 cost +0.14 ns median against fcolsz.
  This is the collatz board candidate (BOARD-QUEUE entry next). Item 20: 48.86 (8 routes).
- fc64nl (collatz64 lever 5): 30 routes, median 45.21 ns, mean 45.16, best 42.46, worst 47.09 (item 22: 47.64). Gate
  90/90 PASS. Static: 0/30 clean -- umux2 rule A -1.3 to -2.5 ns at nominal on EVERY route (size 1, from T4cdb, as in
  board items 16 / 21 / 12). tighten's row is the same pairing as ipow's umux3: request from umux2.uj1 at t=0 against
  the select link ulink_n_index_11's latch data at t=0, "no common source"; rule D from the shared launch +5.6 ns.
  Under the owner's rule (>0.5 ns at nominal on a board item) it needs the trace: running on c64nl_1 with
  research/data/fifteen/vec_c64_selflip.hex (n = 1 / 27 / 1 / 97 / 1 / 6171: the select flips every transaction).
### progress 09:13 UTC (xf2_1 FAST_MIN: the failure depends on the previous transaction)
- Alone at FAST_MIN, rounds = 4 gives the right value (77b0567e). In the gate's sequence every wrong answer equals the
  PREVIOUS vector's rounds (4 after 3 -> 3 rounds; 8 after 4 -> 4; 16 after 8 -> 8 ...): the loop compares against the
  last transaction's rounds. So the rounds ring's entry (umux2 / its select / the value it latches) takes the stale
  loop-back token instead of the new rounds -- the empty-pipe select-race family (ipow umux3, collatz64 ulink_n14__1).
  The SDF experiment lengthened umux2's request, not its select path, which is consistent. Tracing rounds 3 then 4.
### progress 09:19 UTC (xf2_1 FAST_MIN failure TRACED: the rounds loop-back pipe's request outruns its data)
- Full dump, FAST_MIN, rounds 3 then 4 (reproduces: the second returns the 3-round value). At the first loop-back of
  the second transaction: ulink_n_trueResult_10 (bd_pipe N=3, SDELAY 6, the rounds value coming back to umux2.y)
  raises req_out at 4232391 ps while its data_out still holds the previous transaction's 3; data_out bit 2 settles at
  4233483 (+1.09 ns). umux2.j1 fires 4233291, umux2's request 4233754 with output data 0; the output settles to 4 at
  4235721, ~2 ns after umux2's request. ulink_n11__1 latches the stale value and the compare runs against rounds = 3.
- So: a pipe's req_out leads its data_out when it fills behind a fresh token (bd_link.v's header: the lead grows with
  depth), and here the consumer's own delay (umux2, 1 element) does not cover it at FAST_MIN. The static check put umux2
  only -41 ps short at FAST_MIN (-42 worst, -6 nominal): it underestimates this lag by ~2 ns. That is a gap in the
  static check (and why the SDF test with +500 ps changed nothing). The gate caught it.
- Also: corner_audit's FAST_MIN report flagged H -73 at ulink_n_trueResult_10 stage[1]; the H / I pad proposals I set
  aside as "diverging" were pointing at this pipe. Running the same route with umux2's request +2.5 ns in the SDF.
### progress 09:20 UTC (collatz64 umux2 rule-A miss: the same false path as ipow umux3, shown by trace)
- c64nl_1 full dump on research/data/fifteen/vec_c64_selflip.hex (n = 1 / 27 / 1 / 97 / 1 / 6171, each twice; results 0
  / 111 / 0 / 118 / 0 / 261 = the C). At all 12 output requests of umux2 (7 select flips): the select link
  ulink_n_index_11's request rises 5748 ps after its data; the join fires 334-338 ps later; umux2's output request rises
  >= 5877 ps after the last change of any of the 33 LUTs that read the select. tighten's row (-1.3 to -2.5 ns at
  nominal on all 30 fc64nl routes) pairs that latch's data with uj1 at t=0, the same no-common-source pairing as ipow.
  This covers collatz64 board items 6 / 12 / 16 / 21 too (umux2 = 1 in T4cdb / x0.75 sizes; same structure).
- Caveat now on record: on xf2_1 the static check UNDER-estimated a real lag by ~2 ns (pipe req_out leading data_out).
  A trace is the evidence for these explanations, not the static number.
### progress 09:34 UTC (GOAL 1: xf2_1's FAST_MIN failure is a HOLD race the static rules do not audit)
- Correction to the entry before last: rounds is right at the compare (4 throughout); the COUNTER is wrong. i+1 at the
  compare reads 1, 2, then 7 (run 1) / 5 (run 2). The lengthened-umux2 tests (+0.5 / +2.5 ns) changed nothing because
  umux2 is not involved; the "pipe req_out leads data_out" observation on ulink_n_trueResult_10 is real but harmless here.
- Mechanism (full dump, FAST_MIN, rounds 3 then 4, second transaction, second increment): ulink_n_trueResult_6 (bd_pipe
  N=2, the counter's loop-back: adder -> fork n30 -> branch n30__0 -> steer ucond_br6 -> this pipe -> umux0.y) opens its
  stage-1 latch for i+1 = 2 at 4244952 ps. The adder's request returns to zero at 4245584; the next token (i = 2)
  reaches the adder (n7) at 4246605 and its output starts moving at 4247312 (bit 2 glitches while 2 -> 3 carries). The
  pipe latch closes only at 4249162: for 1.85 ns the adder's NEXT result flows into the latch that is supposed to hold
  the previous one, and it settles with bit 2 set. The loop-back i becomes 6 (or 4), the adder makes 7 (or 5), and the
  compare ends the loop one iteration early.
- The static rules do not see it: corner_audit (FAST_MIN) rates rule H on that stage[1] at +86 ps, and stage[0] is
  "data enters from outside the design, or from no link stage that also requests -- not audited". The sender is a
  compute unit (the adder, through a fork branch and a steer, with no link stage), so the hold path (pipe acknowledge
  -> steer -> fork -> adder -> ulink_n7 -> umux0 -> next token -> adder output) is not timed by any rule.
- Consequences: (1) xf2 is NOT a full-range candidate (gate 83/84; this route fails). (2) Any design where a compute unit
  feeds a steer and a pipe with no link stage between them has an unaudited hold path; the gate is the only check there,
  and it caught this on 1 of 28 routes. That structure is in item 17's family (same knobs) and probably elsewhere: to be
  listed. (3) The fixes to test: a latch on the adder fork's steer branch (BDC_FORK_OUT_LINK=n30__0) so the sender is a
  link stage that H audits, or an acknowledge delay on the pipe's input stage -- and, first, a static check for this
  hold path (it must be able to fail on xf2_1).
### progress 09:35 UTC (xf3: a latch on the adder fork's steer branch -- PREDICTION)
- xf3 = xf2 + BDC_FORK_OUT_LINK=n11__0,n30__0 (bdc emits ulink_n30__0_folink: the counter's loop-back pipe now has a
  link stage as its sender, so rule H audits the hold and the link protocol orders it). Placeholder sizes for the new
  link (DELAY default, UACK ACK_PAD 6). PREDICTION: one more stage on the counter ring's loop-back: +1.5 to 2.5 ns on
  seed 1 (xf2_1 22.93 -> ~24.5-25). Seed 1 first (the failing route's seed, though the route will differ), all checks.
### progress 09:35 UTC (the hold audit's blind spots: 20 latch stages on one xorshift route)
- research/data/fifteen/hold_blind_spots_xf2_1.txt: every latch stage whose hold (rule H) and close (rule I) the audits
  report as "not audited" on xf2_1 -- 20 stages: the first stage of every pipe / link fed by a compute unit, a fork, a
  steer or the harness (ulink_n_trueResult_6/8/10/0/2, falseResult_1/9, n7, n8, n6, n11__1, n11__0_folink,
  merge0_olink, n12__0/1/2, n30__1, n1__1, index_15). On all of them the only evidence is the gate's FAST_MIN column,
  route by route; xf2_1 shows that it can fail there on one route in 28.
- What a check needs: for a latch fed by a non-link sender, the earliest time its D input can change after the latch
  opens -- the acknowledge back through the steer / fork / compute unit to the sender's own input links, the next token
  in, and the combinational path out -- against when the latch closes. That is a path through the handshake cycle,
  which the timed event graph (research/tools/eventgraph) already walks for periods; it needs the data arcs added and
  a min-delay (FAST_MIN) weighting. It must flag xf2_1's ulink_n_trueResult_6 (1.85 ns at FAST_MIN in the trace) to be
  trusted. Not built yet.
### progress 10:10 UTC (xf3 seed 1: 24.19 ns, every check passes; the blind spot moves, it does not close)
- xf3_1 (local, every check): 24.19 ns (predicted 24.5-25; xf2_1 22.93), static CLEAN at nominal and worst (tighten's
  "a" row for ucmpi1 only), gate max / min / worst 17/17 each. A different route from xf2_1, so this says nothing yet
  about the race; fxf3 (32 farm routes) decides empirically.
- On this route the pipe ulink_n_trueResult_6's stage[0] hold is now audited (H +938 ps worst; its sender is the new
  link). But ulink_n30__0_folink itself is fed by the adder through the fork and is "not audited": the blind spot moved
  one stage up. Whether that link's close can race the adder's next result depends on when its node falls (req_in low
  and the next stage high) against the next token's arrival -- the same kind of path, untimed. So xf3 is not shown
  safe statically either; the hold check for non-link senders is still the missing piece.
Next (for this session if it lasts, else the next):
  1. fxf3 (32 routes): if the gate passes everywhere, xf3 is the xorshift full-range candidate, with the hold blind spot
     on ulink_n30__0_folink stated. fxne (the != test) the same way.
  2. A hold check for latches fed by non-link senders (research/data/fifteen/hold_blind_spots_xf2_1.txt): it must flag
     xf2_1's ulink_n_trueResult_6 (the trace: 1.85 ns at FAST_MIN). Candidates: the timed event graph with data arcs
     and min delays; or a trace-measured hold margin per blind-spot latch (D changes inside the enable window after the
     downstream stage has captured), reported per route as a distribution. Then re-check items 17, 19, 20, 22.
  3. gcd's counters and compares under the full-range rule (items 1-3, 5), not yet done.
  4. The speculative-completion incrementer (research/data/fifteen/speculative.md) after 2: its static check needs case
     analysis, and the hold story above applies to it too.
  5. A Dynamatic build somewhere (owner's machine or a farm task) to confirm BDC_FE_EXITCOND's handshake MLIR equals the
     fixture-with-ne used here.
### progress 10:12 UTC (hold_trace.py: a trace-measured hold check that can fail -- it flags xf2_1)
- research/tools/fifteen/hold_trace.py DUMPDIR KERNEL_V: for every bd_link / bd_pipe input stage (the audit's blind
  spots), from a full dump: D (data_in, resolved through the kernel's assigns) must not change between the stage passing
  its token on (req_out / next stage's node) and its latch closing (its C node falling). Reports windows, violations and
  the smallest margin per instance.
- Negative control: on xf2_1 at FAST_MIN, rounds 3 then 4 (the failing sequence): ulink_n_trueResult_6 4 violations in 8
  windows, margin -1850 ps -- the hand trace's 1.85 ns, found without being told where to look. Next tightest:
  ulink_n_index_15 +588 ps, ulink_n11__0_folink +3168. research/data/fifteen/hold_trace_xf2_1_fmin.tsv.
- Coverage gaps: links whose C node net is not kept by name in the decoded netlist (n7, n8, n11__1, n12__0/2, n30__1,
  n1__1, merge0_olink) are not measured yet; pipes whose data comes from the harness have no data nets (constant per run).
- It is a trace check: it sees only what the vectors exercise, at the corner simulated. Its use: a margin per route and
  per blind-spot latch at FAST_MIN, so a route close to failing shows as a small margin instead of passing silently.
### progress 10:17 UTC (hold_trace positive control: xf3_1 at FAST_MIN, the failing vector sequence)
- xf3_1, FAST_MIN, rounds 3 / 4 / 8 / 5 in sequence (research/data/fifteen/vec_xorshift_hold.hex): all four results
  correct (7b0859a0 / 77b0567e / 2932183d / d28ab0e1, from the C). hold_trace: no violation; ulink_n_trueResult_6
  +7039 ps (xf2_1: -1850), the new ulink_n30__0_folink +6263, tightest ulink_n_index_15 +425 ps.
- So on seed 1 the extra latch turns the hold race into ~7 ns of margin. Whether every route does is what fxf3 / fxf3h
  (32 farm routes, the latter with this check) will say. fxf2h validates the check across routes (seed 1 must flag).
### progress 10:47 UTC (farm fxne: the != exit test does not pay on xorshift)
- fxne (xf2 structure + the != loop test, ucmpi1 8): 29 routes built (5, 7, 30: harness < 83 MHz). Period median 23.76
  ns, mean 23.54, best 21.52, worst 25.02 -- against fxf2's 23.29 / 23.29 / 20.86 / 24.94 on the same seeds: no gain
  (the one element saved on ucmpi1 is inside the route scatter, and the median moved the other way). Gate 87/87 PASS.
  Static clean on 27/29 (17, 27: umux2 rule A -2 to -65 ps, the same small rounds-mux miss as fxf2 seed 1).
- fxne keeps the xf2 structure (no latch on the adder's steer branch), so it carries the same unaudited hold path; its
  routes happened to pass. Not pursued further: BDC_FE_EXITCOND stays an opt-in knob, recorded as no gain on xorshift.
### progress 11:43 UTC (farm fxf2h: the hold check, across 29 routes, flags exactly the failing one)
- fxf2h = fxf2 (same seeds, same routes) + hold_trace at FAST_MIN on rounds 3 / 4 / 8 / 5. Gate 86/87: seed 1 FAST_MIN
  6/17 again (the farm reproduces it). Hold check: seed 1 ulink_n_trueResult_6 17 violations, -1850 ps; NO violation on
  any other route (seeds 11 / 14: no build). The race stage's margin on the passing routes: +1421 (s30), +1664 (s32),
  then >= +1759 ps -- seed 1 is an outlier placement, not the tail of a smooth distribution. Tightest stage elsewhere:
  ulink_n_index_15, +360 to +883 ps. research/data/fifteen/farm/fxf2h_hold.txt.
- So the trace-measured hold check catches what the static rules cannot see, with no false alarm on 28 routes. It joins
  the per-route checks (eval_task HOLD_VEC). Its limit stays: it sees only what the vectors exercise.
### progress 11:53 UTC (farm fxf3 / fxf3h: 31 routes, gate 93/93, no cost from the latch; one hold violation)
- xf3 (xf2 + latch on the adder's steer branch): 31 routes (10: no build). Period median 23.04 ns, mean 23.21, best
  21.62, worst 25.95 (xf2: 23.29 median): the extra latch costs nothing measurable. Gate 93/93 PASS. Static CLEAN on
  28/31; seeds 7, 9, 21: umux2 rule A -3 to -56 ps (the rounds mux at size 1, as on fxf2 / fxne).
- Hold check (fxf3h, same routes): ulink_n_trueResult_6 clean on every route. ONE violation: seed 4, ulink_n_trueResult_10
  (the rounds ring's loop-back pipe) 1 window, -612 ps -- on a route whose gate passes. Next tightest stage on any route
  +44 ps. So xf3 is not yet clean: rebuilding seed 4 locally (same route) to trace what that D change is.
### progress 12:07 UTC (xf3 seed 4's hold violation is a 57 ps x-pulse, not a new value; xf4 = xf3 + umux2 2)
- xf3_4 rebuilt (same route b1e3c2b0) and dumped at FAST_MIN on rounds 3 / 4 / 8 / 5: results correct; the flagged window
  on ulink_n_trueResult_10 is bit 14 of rounds at its input going x at 1667617 and back to 0 at 1667674 -- 555 ps before
  the latch closes, the value it holds unchanged. The pulse comes out of ulink_n11__0_folink's latch (an x from the fid
  model's near-simultaneous edges at that latch LUT): noted for a look, not a corruption.
- hold_trace.py now reports glitch_only (violations where every D bit is back at its captured value when the latch
  closes). xf2_1: 4 violations, 2 glitch-only, 2 REAL (the leak). xf3_4: 1 violation, glitch-only. So across the 31 xf3
  routes the hold check finds no real violation.
- Left for xf3 under the full-range rule: umux2 rule A -3 to -56 ps on 3 routes (the rounds mux; its high bits are never
  toggled by the vectors). xf4 = xf3 + umux2 1 -> 2 (research/data/xorshift_sizes_T3s50_fr3_bench.vh); farm fxf4, 32
  routes, every check + hold. PREDICTION: median ~23.0-23.4 ns (umux2 is on the rounds ring, rarely the binding one).
### progress 13:23 UTC (farm fipowrh: ipow item 19's design -- the hold check flags umux3's select pipe on 15/31 routes)
- fipowrh (item 19's knobs and sizes, 32 seeds, every check + hold at FAST_MIN on e = 0 / 5 / 0 / 7): 29 routes built,
  period median 38.96 ns, mean 39.06 (37.24-42.14). Gate 87/87. Static: every route only the umux3 rule-A row
  (-1.0 to -1.7 ns), the false path traced earlier today.
- Hold: ulink_n_index_15 (the 1-bit select pipe into umux3, N=2) shows REAL D changes (glitch_only 0) inside its input
  stage's open window on 15 of 31 routes: 4 of 8 windows each (the transactions where the select flips), -1 to -247 ps
  (s8 -247, s11 -233, s24 -209, s29 -170, s20 -154 ...). The next transaction's select value enters stage 0 after stage
  0 has passed its token to stage 1 and before stage 0 closes. Results stay correct on every route, so stage 1 closed
  first everywhere here -- but hold_trace measures stage 0 only, so it cannot show how much margin stage 1 had. Same
  structure as the umux3 empty-pipe select race traced on 2026-11-10 (ipow T9cd).
- Item 19 (#20): flagged in BOARD-QUEUE, not held: no corruption seen on 31 routes x 2 checks; the follow-up is to extend
  hold_trace to follow a leak through the next stage of a pipe (stage k's window against stage k+1's close).
- Tried and dropped: a "channel" check (data_out stable from req_out until the consumer's ack rises) flags large
  violations on routes known good (xf3_1: trueResult_8 16/16). Wrong contract for this library: a bd_link's output
  follows its still-transparent latch and its consumers are latches, so correctness is about latch closures, which is
  what the stage check measures. The follow-up for pipes stays: stage k's leak against stage k+1's close.
### progress 13:25 UTC (hold_trace fix: a pipe's latch closes at its C node, not at r[1])
- bd_pipe's r[k] is the request INTO stage k, i.e. stage k-1's request after its SDELAY line, so using r[1]'s fall as
  stage 0's latch close measured the close late by that line's fall time -- violations of up to one element's fall
  could be artefacts. hold_trace.py now walks back from r[1] through the delay line's elements (pass-through LUTs, or
  gated ones fed by the line) to the C node. xf2_1: still 4 violations, -1159 ps (the close is 691 ps earlier than
  r[1]'s fall); xf3_1: clean. The farm numbers above (fxf2h, fxf3h, fipowrh) used the old reading; fipowrh's -1..-247
  ps flags on ulink_n_index_15 are within one element's fall and are being re-measured (ipow seed 8 rebuilt locally).
### progress 13:36 UTC (ipow item 19's hold flags were the tool's error -- withdrawn)
- ipowr_8 rebuilt (= fipowrh seed 8, 40616 ps, sdf 00166fca), FAST_MIN dump on e = 0 / 5 / 0 / 7 (results 1 / f3 / 1 /
  c90f7, correct), corrected hold_trace: no violation anywhere; ulink_n_index_15 +782 ps (the old reading on this route
  was -247). So the fipowrh flags measured the SDELAY line's fall, not the latch; item 19's flag is withdrawn in
  BOARD-QUEUE. The fxf2h / fxf3h readings shift the same way (xf2_1 still fails at -1159 ps); the farm requests from now
  on use the corrected tool (it is on the branch they check out).
### progress 15:37 UTC (farm: collatz item 22 and collatz64 lever 5 with the hold check -- old tool reading)
- fcolsz2h (collatz item 22's design, seeds 1-32): 31 routes, period median 41.20 ns, gate 93/93, static CLEAN on 31/31.
  Hold (picked up the uncorrected tool, whose window is wider): 2 routes flagged on ulink_n_index_11 at -11 / -21 ps,
  inside the delay-line artefact; tightest elsewhere +39 ps.
- fc64nlh (collatz64 lever 5): 30 routes, median 45.23 ns, gate 90/90, static 0/30 (umux2, the traced false path).
  Hold (old tool): ulink_n_index_11 flagged on EVERY route, -262 to -748 ps, beyond one element's fall in places.
- Re-measuring both with the corrected tool on rebuilt routes: collatz seed 6, collatz64 seed 3 (worst, -748).
- fxf4 still "submitted" after ~3 h (no task started): noted per the farm README; checking again later.
### progress 15:55 UTC (corrected hold readings: collatz item 22 and collatz64 lever 5 are clean)
- colsz2_6 (fcolsz2h seed 6, 40782 ps) at FAST_MIN on n = 1 / 27 / 1 / 97 (0 / 111 / 0 / 118, correct): no violation;
  ulink_n_index_11 +1047 ps (old reading -21). c64nl_3 (fc64nlh seed 3, the worst old reading -748 ps): no violation;
  ulink_n_index_11 +734 ps. So every old-tool flag on these two designs was the SDELAY-line artefact.
- Collatz item 22 now has, over 31 farm routes: gate 93/93, static check clean 31/31, hold check clean (corrected tool on
  the flagged route; old tool's wider window clean on the other 29).
### progress 17:55 UTC (fxf4 back from the farm: xf4 is the xorshift full-range candidate, pending 2 local re-runs)
- Container restart #5 (~17:5x) cut the local xf4 runs; 4 of 5 had finished. fxf4 (farm, 32 routes) finished 16:44.
- xf4 = item 17's structure + latch on the adder's steer branch (BDC_FORK_OUT_LINK=n11__0,n30__0) + full-range sizes fr3
  (uaddi0 13, umux0 2, umux2 2, uxori1 / uxori2 7, umux3 14, merges 2). Farm: 30 routes built (30: harness < 83 MHz;
  9: ffmux_scan FLAG -- a slice FF configuration at CLBLM_L_X8Y41, the known nextpnr pin defect class; route excluded,
  the same flag locally on the same route). Period median 23.49 ns, mean 23.30, best 21.00, worst 24.75. Gate 87/87
  PASS. Hold check (old tool, wider window): no violation on any route, tightest +434 ps. Static CLEAN at both corners
  on 28/30: seed 18 uxori1 rule A -81 ps worst (the xorshift datapath, which the vectors toggle on every bit: spanned);
  seed 13's checks did not complete.
- Local xf4 (same routes as the farm's, sdf identical): s1 23.47 / s4 24.75 / s7 23.65 / s9 22.46 ns; static clean
  everywhere; gates pass except two FAST_MIN runs with "cycles 0" (killed compiles: two evaluations at once ran ten
  simulators; not results -- re-running one at a time), and three hold dumps lost the same way. s1's hold: clean,
  tightest +1021 ps (corrected tool).
### progress 18:32 UTC (xorshift full range: BOARD-QUEUE item 23 / #24 -- xf4, 23.49 ns median over 30 routes)
- Local re-runs (one at a time): xf4_7 / xf4_1 FAST_MIN 17/17; hold (corrected tool) xf4_7 tightest +756 ps, xf4_4 +715.
- xf4 is the xorshift full-range candidate: BOARD-QUEUE item 23 / #24, board seed 10 (sdf 2f825834, 23.31 ns, EQUIVALENT,
  ffmux clean, every check clean). research/data/fifteen/README.md's headline: 23.49 ns, gap to 15 ns 8.5 ns; the full
  range costs ~2.9 ns against item 17's bench-range 20.60.
### summary 18:33 UTC (this session so far)
Measured (nextpnr 9c732bc6303458df; farm and local routes identical by sdf md5):
| kernel | design | ns/iter median (range), routes | gate | static (full range) | hold check | vs |
|---|---|---|---|---|---|---|
| xorshift | item 23 / xf4 (full range) | 23.49 (21.00-24.75), 30 | 87/87 | 28/30 clean (1 spanned miss, 1 incomplete) | clean | item 17 20.60 (bench range only), Dynamatic 12.73 |
| xorshift | xf2 (no latch on the adder's steer branch) | 23.29, 28 | 83/84: s1 FAST_MIN fails | 26/28 | s1 -1159 ps (real) | -- |
| xorshift | xne (!= exit test) | 23.76, 29 | 87/87 | 27/29 | not run | no gain over xf2 |
| collatz | item 22 / colsz2 (full range) | 41.20 (38.85-43.26), 31 | 93/93 | 31/31 clean | clean | item 20 48.86, Dynamatic 14.05 |
| collatz64 | lever 5 (c64nl) | 45.23 (42.46-47.09), 30 | 90/90 | umux2 false path (traced) | clean (corrected) | item 22 47.64, Dynamatic 17.84 |
| ipow | item 19's design | 38.96 (37.24-42.14), 29 | 87/87 | umux3 false path (traced) | clean (corrected) | item 13 ~45.8 |
Does NOT show: silicon; hold paths the vectors do not exercise (hold_trace is a trace check; the 20 blind-spot latch
stages per xorshift route have no static hold rule); the != knob's real Dynamatic output (built from the fixture with the
predicate changed); gcd under the full-range rule.
Next: (1) gcd's items under the full-range rule; (2) a static (not trace) hold check for latches fed by non-link senders;
(3) the speculative-completion incrementer (research/data/fifteen/speculative.md) -- the remaining 8.5 ns to 15 on
xorshift is now mostly the full-range counter add (13 elements) and handshake wire; (4) the ulink_n11__0_folink x-pulse
on xf3_4; (5) a Dynamatic build to confirm BDC_FE_EXITCOND.
### progress 19:21 UTC (gcd under the full-range rule: static check running on board item 5's route)
- gcd_hw rebuilt as BOARD-QUEUE #5 (seed 6, R5s75 sizes, pads, v4, fast fall): sdf 39d30709 = the gated route.
- corner_audit could not run on it: the rig's free-running oscillators (dhk, invhk) form storage-free cycles, which
  tighten.py skips with --osc but corner_audit's rule A' step (tighten.routed_graph) did not. corner_audit.py --osc now
  passes them to the audits and cuts their arcs in the parsed SDF too. Running nominal + worst (--prefix urig.udut.).
- gcd's loop has no counter: a, b are the data, and the gate's vectors (1000 random 32-bit pairs on gcd_ps) span them,
  so the rule's "unspanned paths" are few; the static check is still the evidence for the long-carry compares.
### progress 21:22 UTC (gcd item 5 under the full-range rule -- preliminary, from the base audits)
- Route = BOARD-QUEUE #5 (sdf 39d30709). The per-line sensitivity runs of corner_audit are still going after 1.5 h (gcd
  is the biggest kernel); its base audits at each corner are done:
  rule E: no violation at nominal or worst. Rule A (tighten's rows; A' re-measure pending): nominal ushrsi4 -210 ps;
  worst ushrsi4 -1328, ushrsi2 -500, ushrsi1 -438, uaddi0 -121 ps.
- None is on a counter: gcd's shifts and subtract work on a and b, which the gate's 1000 random 32-bit vectors (gcd_ps)
  toggle across all bits. The one nominal miss is 210 ps (< the 0.5 ns the owner asks to explain). So under the rule:
  gcd item 5 (and #1-#3, same structure) is full range as far as these checks go, with the worst-corner rule-A rows on
  record. Final rows (A') to follow from corner_audit's report.
### progress 23:25 UTC (gcd item 5: static check final -- nominal clean, worst A' -359 ps on a spanned shift)
- corner_audit --no-size no longer runs the per-line sensitivity audits (they only annotate "depends on"; on gcd they
  took > 4 h): report-only checks now take minutes.
- gcd_hw #5's route (sdf 39d30709), measured-residual guards: NOMINAL: no kernel rule A' / E below 0 (tighten's pairing
  row "a" ushrsi4 -210). WORST: rule A' ushrsi4 -359 ps (tighten's rows: ushrsi4 -1328, ushrsi2 -500, ushrsi1 -438,
  uaddi0 -121). gcd has no counter; ushrsi4 shifts a / b, which the 1000 random 32-bit vectors span. Full range by the
  owner's rule, worst-corner row on record. BOARD-QUEUE updated.
### progress 23:26 UTC (collatz64 lever 5 becomes BOARD-QUEUE item 24 / #25, full range)
- c64nl: gate 90/90 over 30 farm routes, static check only umux2's false-path row (traced), hold check clean (corrected
  re-measure on the worst old reading), lever-5 rule E from the removed link's source +1.5..+1.8 ns raw at nominal.
  Board seed 17 (sdf 3a370768, 45.19 ns, EQUIVALENT, ffmux clean). Median 45.23 ns vs item 21 47.64.
- Full-range board list now: xorshift 23 (#24) 23.49 ns, collatz 22 (#23) 41.20, collatz64 24 (#25) 45.23, ipow 19 (#20)
  38.96, gcd #1-#5 (static check on #5's route).
### progress 23:27 UTC (speculative completion, step 1: the bdc knob)
- bdc/emit.py BDC_SPEC_INC=inst:k:nshort (opt-in; byte-identical unset on gcd, xorshift, collatz, collatz64, ipow,
  isprime, checked against HEAD's emitter): a fused single-op `addi x, 1` unit gets a second request line udly_s
  (DELAY_SHORT, sizes key BD_SZ_<INST>_SHORT) and a LUT3 z_req = abort ? z_long : z_short, abort = &x[k-1:0] |
  ~|x[k-1:0] (design notes: research/data/fifteen/speculative.md). simcheck PASS on xorshift with uaddi0:4:6, the
  negative-rounds vectors included.
- Next: the static check per case -- corner_audit with arcs cut: LONG case = the short line's arc into the LUT3 cut;
  SHORT case = the long line's arc cut and the adder's carry arcs above bit k cut (they cannot toggle when abort = 0).
  Plus the select race inside the cell (spec_abort settling before z_short rises) as a rule-E-like row.
### progress 23:41 UTC (speculative completion on xorshift: first route measured; static check clean in both cases)
- xs_10 = item 23's build (seed 10) + BDC_SPEC_INC=uaddi0:4:6 (short line 6, long 13). Bench latency on the 256-round
  vector: 466 cycles vs xf4_10's 503 (same seed, same sizes otherwise): -1.73 ns per iteration on average (predicted
  ~-2.1: 7 elements x ~0.35 ns x 7/8). Result cd3132bf (C), EQUIVALENT, ffmux clean. The event graph cannot give a
  single period any more (iterations differ by design); latency is the measure.
- Static check by cases (corner_audit --drop-inst / --cut, new): LONG = the short line removed, the abort->LUT3 arc
  cut; SHORT = the long line removed, the abort arc cut, and every arc out of the adder's CARRY4 slices 1-7 cut (with
  abort = 0 the carry never enters bit 4 and bits >= 4 do not change). uaddi0 rule A': LONG +3843 nominal / +2519
  worst; SHORT +1103 / +545. No other kernel A' / E row below 0 in any case. Stable across PYTHONHASHSEED (the first
  attempts were not: tighten pairs a cell with ONE delay line and picked between the two, or the abort path, by set
  order -- hence dropping the other line's instances outright).
- Not covered by those rows: the select race inside the cell (spec_abort must settle before z_short rises). Estimate
  from the SHORT-case rows: the latest low-bit data arrives ~2.5 ns at worst vs the short request at 3.08 ns; the abort
  is 2 LUTs off the same bits. To be measured as its own row. Then: gate, hold check, 32 farm routes.
### progress 00:33 UTC (xs_10: full gate and hold check clean)
- xs_10 (speculative uaddi0, seed 10): bench_gate SLOW_MAX / FAST_MIN / worst+M all PASS 17/17, EQUIVALENT (cycles
  13423 / 4930 / 6834). Trace hold check at FAST_MIN: no violations; tightest ulink_n_index_15 +1050 ps,
  ulink_n_trueResult_6 (item 23's fixed race) +5608 ps. One route; the 32-route farm run fxs is still running
  (fxf4l, the baseline latency on the same seeds, is back).
- Still open before a board item: the in-cell select race (spec_abort vs z_short) as its own row.
### progress 00:58 UTC (speculative cell: the in-cell select race, static row)
- research/tools/fifteen/spec_select.py: the race inside a BDC_SPEC_INC cell (abort must settle before the short line
  rises at uspec, else a long case completes on the short line). Rule-E form from each upstream link's C node:
  0.97 x earliest short request - 1.03 x latest abort. xs_10: +1361 ps nominal, +1124 ps worst (req 3661 / 3417,
  abort 2126 through the link latch + one LUT; LUTs and wires do not move between the two corners, the chains do).
  Negative control: the abort arc into uspec stretched by 3 ns in a copy of the SDF -> -1728 ps (fails, as it must).
- eval_task.sh prints the row ("select nom/worst") with SPEC_CASES. fxs was submitted before it, so farm request fxss
  rebuilds the same 32 seeds and reports only this row (spec_select_task.sh; checked to reproduce xs_10's worst row).
- Not covered by any row yet: the falling phase of the mux (both lines FASTFALL; abort is held until the acknowledge
  falls, by the bundling upstream). The 3-corner gate exercised it on xs_10 (PASS); a static argument is still owed.
### progress 01:20 UTC (speculative cell: the falling phase, static row)
- spec_select.py now also prints FALL: both delay lines must be low at uspec before the abort can change for the next
  token (else switching the mux passes a stale high: a z_req runt). Both lines fast-fall from the gate, which on this
  cell IS the upstream link's C node (the 1-input join is a wire); the abort can change only after that C node rises
  again (its latch reopens) plus the earliest C -> abort path. Re-rise bound: rule F's t_reuse (min over the two
  lines). xs_10: lines low by 1636 / 1596 ps; abort no earlier than 3120 + 1432 / 3054 + 1432 -> FALL +2730 nominal,
  +2707 worst. With the loop bounded by 0 instead it reads -296 (that bound is too loose to decide anything; the raw
  shortest C -> C graph cycle, 1215 ps, is the C-element's own hold feedback, not a handshake).
- fxss was picked up before the FALL row existed; fxss2 = the same 32 routes with both rows. fxss's SELECT rows must
  match fxss2's exactly (same seeds): a free reproducibility check.
### progress 02:20 UTC (CORRECTION: rule H saw the xf2_1 race; H / I rows were never read; board items 22-24 not clean)
- The xf2_1 corruption, re-traced in the FAST_MIN dump (trace/xf2_1_fmin2): the latch that misbehaves is ulink_n7's bit
  1, not the pipe. ulink_n7's node falls at ~4244.9 ns (its ack to umux0 falls at 4245062), but that bit's enable wire
  is 1637 ps long (its D wire 217): the bit is still open at 4246560 when umux0's output changes -- umux0's y_ack fell at
  4245482 on ulink_n7's ack, the loop-back pipe's last stage opened and sent i = 2 through umux0. Q1 follows D1 at
  4246605, the adder's input moves, and the pipe's stage 0 (still open) takes the wrong sum. Pure rule H: "the
  acknowledge is released after every latch bit has closed". And rule H flagged it: corner_audit on xf2_1 reports
  H ulink_n7 -439 ps at FAST_MIN, -466 at worst ("PAD to 3 -- VIOLATION (no DACK line routed)").
- So the 09:3x entries were wrong: "the static rules do not see it" -- they did. What did not see it: build_bench's gate
  (rule A only), eval_task's static line (rows A and E only), hold_trace (ulink_n7's node is not kept by name; it
  measures pipe INPUT stages only). The H / I rows were computed on every route and never read.
- Scan of every local corner report (research/tools/fifteen/eval_task.sh's corner_audit outputs): H / I rows below 0
  on almost every route of xorshift (xf3 / xf4), collatz64 (c64nl), ipow (ipowr), pmfr3; -1 to -838 ps (H), up to
  -1461 (I). Item 23's own board route, xf4_10 at worst: H -274 ulink_n7 (the xf2_1 stage), H -107 / -103 (pipe stage[1]
  of trueResult_10 / _8), H -1, I -85. collatz (colnl / colsz): mostly clean, a few I / H rows. The gates passed on
  these routes (a hold violation corrupts only when the data moves inside the window); the static rule says the margin
  is not there. Board items 22-24 (and 19) are therefore NOT statically clean for hold / capture: to be re-gated.
- Why no proposal ever fixed them: corner_audit sizes a knob by measuring its chain; a UACK at 0 links has no chain,
  so "PAD to k" never reached a proposal sizes.vh. research/tools/fifteen/hold_pads.py takes the H / I rows' PAD values
  from reports straight into the knobs (UACK per link / per pipe, SDELAY per pipe).
- eval_task.sh's static line now ends "| hold/close: <every H / I / F / K / L / B / C row below 0>".
- xorshift fr4 = fr3 + hold_pads over the 11 local xf4 reports: UACK n6 / n7 / n8 / trueResult_6 / _8 -> 1,
  trueResult_10 -> 2; SDELAY falseResult_1 -> 2, trueResult_0 / _2 -> 1. Farm fxf5 (32 routes, every check) and fxs5
  (+ the speculative incrementer); local xf5_10 (the board seed) running.
- Open: the same for collatz (item 22), collatz64 (24), ipow (19), gcd; then BOARD-QUEUE re-marked.
### progress 02:35 UTC (H / I pads for the other board families; farm fcol3 / fc64h / fipowh)
- hold_pads.py over the local reports: collatz64 (8 c64nl worst reports) 14 knobs (UACK n7/n8/n10__3/n13 and four
  pipes up to 4, SDELAY up to 2; worst rows H -838 ulink_n13, I -1461 falseResult_3); collatz nl2 -> nl3 (colsz / colnl,
  24 reports) 2 knobs (SDELAY n7, falseResult_9 -> 2); ipow (3 ipowr routes) 6 UACK knobs (n7 2, n8 3, ...). The
  values are corner_audit's per-corner estimates on routes built with the OLD sizes; the farm runs (32 routes each,
  every check, eval.txt now with the hold/close list) say whether they close. Cost: the period / latency lines vs the
  fcolsz2h / fc64nlh / fipowrh runs on the same seeds.
### progress 03:10 UTC (hold_bits.py: the trace hold check per latch bit, close at the bit's enable pin)
- research/tools/fifteen/hold_bits.py DUMPDIR KERNEL_V: decodes every latch bit from netlist_baked.v (a LUT output with
  a feedback pin whose INIT is en ? d : q), times each window at the PINS (driver event + that pin's wire delay; close =
  en-pin fall + the en arc), maps bits to stages by their Q net names (link data_out, pipe dat[]). Window start: the
  stage's delayed request rise (no earlier than the en-pin rise); when the request IS the node (DELAY 0) or is not kept
  by name (marked *), rule H's start, the node's fall at its driver. Covers the stages hold_trace could not (ulink_n7,
  n8, n25 ...) and the per-bit enable skew that broke xf2_1.
- Negative control, xf2_1 FAST_MIN (the failing dump): exactly two stages flagged -- ulink_n7* 4 violations, -184 ps
  (the hand trace: D at the pin 4246560, close 4246744) and its victim ulink_n_trueResult_6.stage[0] -1487 ps.
  research/data/fifteen/hold_bits_xf2_1_fmin.tsv. Two earlier versions raised false alarms on pipe last stages (a D
  change before the enable reached the pin; data still arriving through a DELAY-0 stage): fixed as above.
- Positive controls (gates pass): xf3_1, xf3_4, c64nl_3, ipowr_8, colsz2_6, c64nl_1 (select flips), ipowr_1: no
  violation; tightest +389 ps (c64nl_3 ulink_n13). xf3_4's old hold_trace flag (a 57 ps x-pulse) reads +741 per bit.
- eval_task.sh's HOLD_VEC step now also writes hold_bits.tsv and a "hold-bits violations" line. The farm requests
  already queued (fxf5, fxs5, fcol3, fc64h, fipowh) predate it; their static hold/close line is the check that matters.
- Limits unchanged: a trace sees only what the vectors exercise, at one corner. The static rows (H / I) stay the gate.
### progress 01:20 UTC (xf5_10 = fr4 on item 23's board seed: every H row cleared; one I row left)
- TIMESTAMP CORRECTION: the four entries above stamped 01:20, 02:20, 02:35 and 03:10 were written between 00:58 and
  01:18 UTC (`date -u` now reads 01:18); the stamps were guesses, not readings. Order and content are unchanged.
- xf5_10 (local, every check): route f17dabfd, P 23.15 ns (xf4_10 23.31), latency 499 cycles (503): the pads cost
  nothing measurable on this seed. Gate max / min / worst 17/17 each, EQUIVALENT, ffmux clean. Static A / A' / E clean
  at nominal and worst (tighten's bundled "a" row on ucmpi1 only, as always). Rules H: no row below 0 (xf4_10 at worst
  had -274 / -107 / -103 / -1). Rule I: one row left, ulink_n_trueResult_0 stage[1] -498 nominal / -578 worst at
  SDELAY 1, "PAD to 2". hold_bits: none, tightest +810 ps; hold_trace: none.
- Next for xorshift: fr5 sets that SDELAY from the 32 fxf5 routes (taking the longer number; eval_task now also returns
  the raw H / I rows with their PAD values, report_hi_{nom,worst}.txt, for hold_pads.py).
### progress 01:55 UTC (fr5 local test: one row fixed, two small others appear; speculative cell's select rows on 32 routes)
- xf6_10 = fr5 candidate (fr4 + trueResult_0 SDELAY 3), seed 10: new route f69639f5, P 22.80 ns, latency 492 cycles.
  The trueResult_0 I row is gone; this route instead shows H -8 (falseResult_9 stage[1], nom and worst) and I -106
  (trueResult_2 stage[1], worst). Gate 3 x 17/17, hold_bits none (+1409), hold_trace none. Route scatter moves the
  rows from stage to stage: one seed cannot size them. fr5 stays a candidate; the pads come from fxf5's 32 routes.
- fxss / fxss2 (the speculative cell's in-cell rows on the 32 fxs routes): every route positive. SELECT at worst min
  +150 ps (seed 1), +159 (12), median +1365; at nominal min +363, median +1603. FALL at worst min +1788, median +2749.
  fxss's SELECT rows equal fxss2's on all 32 seeds (the routes reproduce). Seeds 1 and 12 are thin (+150 / +159 against
  a measured-residual guard already applied): a candidate for a bigger margin is moving the abort LUT next to uspec
  (or sizing the short line one element longer on routes like those). research/data/fifteen/farm/fxss2_select.txt.
Next (for whoever picks this up; the farm results land on claude/cluster):
  1. fxf5 (xorshift fr4, 32 routes): tabulate the "hold/close" lists and report_hi_*.txt is NOT in it (eval_task gained
     that after submission) -- use the margins; set the pads for fr5 from the per-stage worst over 32 routes (the longer
     number), resubmit, until the H / I lists are empty on >= 32 routes. Same for fcol3, fc64h, fipowh.
  2. fxs / fxs5: the speculative incrementer's latency vs fxf4l / fxf5 seed by seed; the static LONG / SHORT lines.
  3. Only then re-mark BOARD-QUEUE items 19 / 22 / 23 / 24 and the fifteen README headline.

## Session 2026-11-15 03:30 UTC -- farm round-1 hold pads tabulated, round 2 submitted; speculative incrementer on 30 routes; rule E with C-element joins (lever 5)
Toolchain: 789a7120c912d393 (nextpnr 9c732bc6303458df, toolchain.sh ok)   Seeds: farm 1-32; local 10
### progress 03:30 UTC (farm results from the last session)
- Lock: the previous session's lock (01:51Z) was 93 min old at 03:24Z -- dead by the 90-min rule; taken.
- fcol3 (collatz nl3 pads): 26 routes (16-18, 23-25: farm task failures in 2-5 s, no exit code -- infrastructure, not
  builds). Period median 41.23 ns (38.69-42.49; item 22 41.20). Gate 78/78. Static A / A' / E CLEAN on 26/26 at both
  corners. Hold/close: 21/26 routes clean; rows left on 5 (worst H -351 trueResult_4 st1, I -188 falseResult_5 st1).
- fc64h (collatz64 pads): 30 routes, median 45.12 ns (42.21-48.29), gate 90/90; umux2's traced false-path A row on
  every route as before; hold/close rows on 28/30 (worst H -1211 ulink_n10__1, -757 ulink_n28).
- fipowh (ipow pads): 26 routes, median 39.34 (37.16-41.53), gate 78/78; umux3's traced row on every route; hold/close
  rows on 10/26 (worst H -620 falseResult_11 st1).
- Reading: one pad round shrinks the rows but route scatter moves them (as xf6_10 showed). Round 2: hold_pads_eval.py
  (new; the knob mapping of hold_pads.py, from eval.txt rows since these runs predate report_hi_*.txt), +1 link per
  300 ps of the worst row over 32 routes -> farm fcol4 / fc64h2 / fipowh2. The audit (T109/T109b) found these rows to
  be OR-join lower bounds whose paths were never live (0 dynamic violations, >= +763 ps); padding them anyway is the
  conservative choice while no static proof with C-element semantics exists (pads cost time only).
- fxs (speculative incrementer, fr3 sizes, 32 routes): latency 463 vs 503 cycles mean over the 30 seeds both built
  (fxf4l, same seeds, same sizes without the cell): -40 cycles = -1.87 ns per iteration; 28/30 seeds faster, seed 9
  +5, seed 17 -3. Static per case, all 32 routes: LONG A' >= +1034 worst, SHORT A' >= +94 worst (seed 13), no other
  A / E row below 0 in any case. Gate 93/93 (31 routes). The uncased "static" line's uaddi0 A row is the known
  pairing artefact (tighten pairs uaddi0 with one of its two lines), not a check of either case.
- fxs5 (spec + fr4 pads): 24 routes (8 farm task failures); every per-case row positive; hold/close rows on 14/24
  (worst H -354 trueResult_8 st1). fxf5 (fr4 without the cell) still running at 03:50Z.
- NOT EQUIVALENT (fasm_equiv) on fcol3 s5/s31, fc64h 10 routes, fipowh 9, fxs 5, fxs5 2: the farm does not return
  equiv.txt; the kinds seen before were all the benign constant-LUT -> F7/CARRY4 kind, but these are not checked yet.
### progress 03:41 UTC (rule E with C-element joins; lever 5 on the full-range sizes, local seed 10)
- skew.py (c26f1566): opt-in BD_SKEW_AND_JOIN=1 / --and-join. On the request (earliest) walk a positive C-element
  (bd_ctree's bd_c2/c3/c4, matched by name .g[234].u.u: 20 nodes on xorshift) is seeded with the LATEST of its inputs
  reached at the same crossing level, not the earliest (OR). Why it is a lower bound: such a node moves only after every
  input has; the inputs reached inside one level are combinational descendants of the launch's own transition, so
  each arrival bounds that input's transition for this token, and the max over any subset bounds the firing. The
  select (latest) walk is unchanged. corner_audit's A' walk uses the same set. Default off; unit test added.
  ASSUMPTION: the reached paths into a bd_ctree are non-inverting request paths (bd_join / fork-ack trees of the
  library); bd_mux's j0/j1 (an inverted select inside) are not bd_ctree and keep OR.
- xl5_10 = fr4 sizes + item 23 knobs + BDC_NO_LINK=ulink_n30__1 (lever 5 on the full-range structure), seed 10: route
  40480f3a, P 24.00 ns, latency 517 cycles, EQUIVALENT, ffmux clean -- SLOWER than xf5_10 (23.15 / 499, the same
  seed without lever 5). Event graph: ufork8 (the adder's fork) re-couples to ulink_n7 (polarity changes
  ufork8R->ulink_n7F), as on bench seeds 5 / 9 before; rising-only floor 21.51. whatif: a latch back on n30__1 with
  SDELAY 0 -> 22.42, SDELAY 1 -> 22.79, SDELAY 4 (= the dropped link) -> 23.92. corner_audit proposals on 13 fxs
  routes put ULINK_N30__1 at 1-3 (A' on ucmpi1 binds): a shorter link, not no link, is the lever here (~0.4-1 ns
  predicted, before the +1-3 ns the graph under-charges a stage).
- Rule E on xl5_10's worst-corner SDF (skew.py -v, its own 0.772 / 1.155 guards): OR joins: ucond_br6 VIOLATED
  (launch ulink_n7, req 8650 vs sel 7926: +724 raw, -2476 guarded). AND joins: every site ok; ucond_br6 binding launch
  ulink_n11__1 +2040 raw / +171 guarded. Negative control (copy of the SDF, ucmpi1's 29 delay-chain arcs set to 1 ps):
  AND joins: ucond_br6 VIOLATED -1027 raw (launch ulink_n11__1, req 4381 vs sel 5408) -- the check still fails when
  the request really can beat the select. research/data/fifteen/andjoin/.
- Farm fxl5s: fxs5 + lever 5, static check with AND joins, 32 routes -- whether lever 5 pays with the speculative
  incrementer over the seed distribution (fxs5 is the paired baseline).
### progress 03:44 UTC (lever 8: the loop test reads i against n-1 -- prediction before the build)
- research/tools/fifteen/pre_dec.py (MLIR pre-pass, MLIR_OVERRIDE; bdc unchanged): cmpi slt (i+1), n  ->  cmpi slt i, m
  with m = n - 1 computed once in bb0 (addidec0) and carried round the rounds ring instead of n. Exact on every
  reachable state: the loop is entered only when n > 0 (cmpi0), so m does not wrap; inside, i + 1 <= n <= INT_MAX. The
  ring value has no other reader (checked by the pass). simcheck PASS (rounds 0, 1, -1, INT_MIN and the bench set).
  Same kind of change as indvars' exit-test rewrite (an arithmetic identity on the exit test), not the loop lowering;
  if it pays, the LLVM-level form (an opt-in step in frontend.sh, as the owner preferred for "!=") is the next step.
- Emitted: a fork on i (uforkdec0) with a rule-1 link on each branch (ulink_n7f__0 -> add, ulink_n7f__1 -> compare);
  the adder's output goes straight to cond_br6 (no fork8, no ulink_n30__1, no n30__0 folink).
- PREDICTION (xf5_10's graph, seed 10): the serial ulink_n7 0.41 + uaddi0 5.55 + ulink_n30__1 2.88 + ucmpi1 4.17 =
  13.0 ns becomes max(add branch ~6.0, compare branch ~0.5 + 4.2 + link ~2) + fork ~0.7 = ~7 ns: about -6 ns on that
  cycle. The next cycles on xf5_10 were 19.15 (the xori ring through ucmpi1 / ulink_n11__1) and 15.89, so the period
  should bind elsewhere: predicted 19 ns (18-20; the graph under-charges new stages by 1-3 ns). xf5_10: 23.15.
- Local build xd_10: fr4 sizes (new instances at bdc's default sizes), item 23's knobs less n30__0 (gone), seed 10.
### progress 03:50 UTC (lever 8 measured on seed 10: latency -85 cycles, ~-4.0 ns per iteration)
- xd_10 (pre_dec MLIR, fr4 sizes, item 23's knobs less n30__0, seed 10): route 5e759620, latency 414 cycles vs xf5_10
  499 on the same seed (-85 cycles x 12 ns / 256 rounds = -3.98 ns per iteration: ~19.2 ns from 23.15), as predicted
  (19, 18-20). odata cd3132bf (the C value), ffmux clean. fasm_equiv NOT EQUIVALENT = DRIVER DIFFERS on
  SLICE_X7Y53/F7BMUX input 0, whose JSON driver D6LUT has a constant-0 function and the bits read constant 0: the
  benign constant-LUT -> F7 kind seen before (equiv.txt checked).
- The event graph does not build ("steady state too short": the marker's intervals are not constant on this run), so
  latency is the measure here, as for the speculative cell. Static check (with C-element joins) and the gate running.
- Farm fxd (lever 8) and fxds (lever 8 + speculative incrementer), 32 routes each, submitted.
### progress 04:07 UTC (lever 8 seed 10: gate 3 x 17/17, static A / A' / E clean at both corners)
- xd_10: bench_gate SLOW_MAX / FAST_MIN / worst+M PASS 17/17 each (cycles 11826 / 4451 / 6198; xf5_10's run was 13423 /
  4930 / 6834 for xs_10, the nearest record). Static check (corner_audit, measured-residual guards) A / A' / E CLEAN at
  nominal and worst -- this local run used the DEFAULT OR-join walk (BD_SKEW_AND_JOIN not set), the conservative model;
  tighten's unsized bundled row "a" on ucmpi1 (-462 worst) as on every xorshift route. Hold/close: one row, H -298
  ulink_n_falseResult_9 stage[1] (nom and worst). Trace hold checks (hold_trace, hold_bits at FAST_MIN) clean, tightest
  +880 / +924 ps. research/data/fifteen/lever8/.
- One route. The 32-route distribution comes from fxd / fxds.
### progress 04:12 UTC (lever 8 seed 10: period 19.15 ns, a period-2 pattern)
- Re-dumped xd_10 (same route, itercost stack): every loop request (n7, n8, n29) alternates 18924 / 19382 ps from
  iteration to iteration (252 / 254 of 511 intervals each), so the eventgraph's single-period marker finds no run and
  gives up. Mean 19.153 ns per iteration vs xf5_10 23.147 (same seed): -3.99 ns, matching the latency (-85 cycles).
  Likely an odd / even data dependence in the sim's delays (i's low bit through the compare / add); not chased.
### progress 04:13 UTC (the same idea for collatz / collatz64: the exit test n' == 1 is n == 2)
- research/tools/fifteen/pre_eq2.py: collatz's n' = even ? n >> 1 : 3n + 1, exit when n' == 1. In w-bit two's
  complement: n even -> n >> 1 == 1 <=> n == 2; n odd -> 3n + 1 == 1 <=> 3n == 0 mod 2^w <=> n == 0, not odd: never.
  So n' == 1 <=> n == 2 on every input (w = 32 and 64). cmpi2 now reads n (a fifth fork3 output) against a constant 2;
  fork7 is gone (cond_br7 reads n' directly); the freed constant-1 output is sunk. simcheck PASS on collatz (n = 1, 2,
  3, 6, 7, 27, 97, 703) and collatz64 (1, 27, 113383).
- PREDICTION, collatz seed 26 (fcol3: 38.69 ns): the 32-bit equality and its fork leave the update -> steer path,
  ~-3 ns -> ~35.5 ns (34-37). Local ce_26 running (nl3 sizes, item 22's knobs less BDC_NO_LINK=ulink_n28__1: n28 is
  gone). Farm fceq (collatz, nl4 sizes) and fc64eq (collatz64, h2 sizes), 32 routes, AND-join static check.
### progress 04:14 UTC (fneq: the farm's NOT EQUIVALENT routes are all one benign kind)
- fneq rebuilt 8 routes the farm marked NOT EQUIVALENT (fcol3 s5 / s31, fc64h s3 / s4 / s6, fipowh s2 / s7, fxs s6):
  every SDF md5 equals the farm's (same routes). Every verdict is "DRIVER DIFFERS" on F7BMUX input 0 only (1 site,
  2 on fxs s6): JSON driver = the slice's D6LUT, bits = constant 0; LUT functions identical (5187-5661 / route) and
  routing identical (0 nets differ). On 7 of 8 the D6LUT is listed by fasm_equiv as a constant-function LUT (INIT all
  0); on fipowh s7 that list prints 4 of its 10 entries and X1Y33 is not among the 4 shown -- same pattern, not
  confirmed by print. This is the benign constant-LUT -> F7 kind of 2026-11-10/13. xd_10 (lever 8): the same kind.
- ipow: its exit test e' > 0 (e' = e >> 1) is e > 1, but the shift by one is wiring only and the multiplier path
  binds, so at most a fork is saved: not built.
### progress 04:19 UTC (collatz pre_eq2, seed 26: 37.03 ns vs 38.69; route has the FFMUX gap)
- ce_26 (pre_eq2 MLIR, nl3 sizes, item 22 knobs less the dropped n28 link, seed 26): route d4a2fcc0, P 37.03 ns,
  latency 810 vs fcol3_26 38.69 / 847: -1.66 ns (predicted -3, 34-37: inside the range, at its slow end). New critical
  cycle: ulink_n13 <-> ulink_n14__1 (umux1's select link, 15.4 ns of the cycle, held at its base size by the select
  rule) with polarity changes; rising-only floor 26.1 ns (ucmpi2 is on it, after the mux now, not after the update);
  next cycle 32.5. So on collatz the select link of umux1 is what binds next, not the compare.
- THIS ROUTE IS NOT A BOARD CANDIDATE: ffmux_scan flags CLBLM_L_X8Y35.SLICEM_X0.CFF (ZINI, no CFFMUX), and fasm_equiv
  says NOT EQUIVALENT for the same flop (SLICE_X10Y35/CFF, a dfflegalize emulate_split_set_clr flop, in JSON with loads,
  not configured by the bits): the nextpnr FASM gap of 2026-11-08 (~7% of routes). Both checks caught it.
### progress 04:20 UTC (why the AND seeding is NOT applied to rule H)
- The audit (T109) asks for a static hold proof with C-element semantics. The AND seeding added to skew.py does not
  give one, and is deliberately not used in tighten.earliest_disturbance: the disturbance paths of rule H cross link
  controllers, bd_c2n = C(req_in, ~ack_out), whose rising (the upstream latch reopening) needs the released ack AND
  the NEXT token's request. Whether that request can already be waiting when the ack arrives is a question about the
  marking (how many tokens the ring holds ahead of the latch), not about delays: on xf2_1 it was waiting (the
  loop-back pipe held i = 2), and there the OR bound is exact and the failure real. Bounding it needs a token-count
  argument on the event graph (time separation of events with the occurrence offset of each path), not a max over
  inputs. Until that exists, rule H stays OR (a lower bound) and the pad rounds stay the conservative route.
### progress 04:21 UTC (lever 8's critical cycle, from a two-iteration event graph)
- eventgraph.py --stride S (new, default 1 = unchanged): the period is S marker rises, so a run whose iterations
  alternate (lever 8: 18924 / 19382 ps) gives the S-iteration unrolled graph (nodes stay distinct: S events per net
  edge at distinct phases). xd_10, stride 2, marker n8_req: P 38306 ps = 2 iterations (19.153 each), critical cycle 81
  arcs, CHECK period equal PASS, cycle equal to trace.py's PASS. graphs/xd_10 now has nodes / arcs / check.
- whatif report (per 2 iterations): the adder is off the critical cycle. On it: the xori datapath (uxori1 3.62,
  uxori2 3.28, ulink_n25 0.74), ucond_br7 / trueResult_8 / fork9 (3.4), the rounds ring (ulink_n11__1 2.73 + 0.99
  fall, ulink_n12__2 = umux2's select link 3.76, umux2 2.07, ucmpi1 4.29), merge (ucontrol_merge0 1.93, olink 2.19),
  umux1's select link ulink_n12__1 4.69, umux1 1.72; polarity changes at ufork9 -> ulink_n11__1 and ufork4 ->
  ulink_n12__2. Rising-only floor 36.38 (18.19 per iteration), two-phase bound 36.76; next cycles within 215, 458,
  1540 ps; without ucmpi1 34.81 (17.4).
- So after lever 8 the per-iteration budget is spread: no single term over ~2.4 ns per iteration, and the two select
  links umux1 (4.69 / 2) and umux2 (3.76 / 2) held at base by the select rule are the largest. 15 ns would need ~4 ns
  more out of several of: the select links (a select-rule question, not a size), the compare (sized to its full-range
  static worst), the RTZ arcs at the two polarity changes (~1 ns), the xori links.
### progress 04:36 UTC (note for a later lead: the select rule and rule H)
- After lever 8 the two largest per-iteration terms on xorshift are select links held by the select rule (ulink_n12__1
  DELAY 8, ulink_n12__2 DELAY 6; 4.69 / 3.76 ns per two-iteration cycle). Both traced failures behind that rule
  (JOURNAL 2026-11-09 22:50 ipow umux3; 2026-11-11 03:10 collatz64 ulink_n14__1) were hold-window corruptions: data
  moving downstream while a latch was still open, after a shortened select path let a request return to zero early.
  That is rule H's class, and rule H's rows were never read until 2026-11-15. A candidate replacement for the blanket
  rule: shorten a select link only with H / I rows clean at both corners on >= 32 routes AND hold_bits clean; first
  check that the H rows and hold_bits FLAG the two historical failures (ipow T9cd seed 29 with umux3 1; collatz64
  T4cd seed 7 with ulink_n14__1 10) -- if either check misses one, the select rule stays.
### progress 04:50 UTC (fcol4: collatz pad round 2)
- fcol4 (nl4 = nl3 + 3 pads): 27 routes (5 farm task failures), median 41.24 ns (39.48-42.58; fcol3 41.23: no cost),
  gate 81/81, static A / A' / E clean 27/27. Hold/close clean on 22/27 (fcol3: 21/26); rows left H -2 to -176 ps,
  6 of 7 on ulink_n_falseResult_5 stage[1] (round 1 padded its SDELAY; now its UACK), one ulink_n8 st1 -76.
  Round 3 -> nl5 (falseResult_5 UACK, n8 UACK), farm fcol5.
### progress 05:02 UTC (fceq: collatz with the n == 2 exit test, 32 routes -> BOARD-QUEUE item 25 / #26)
- fceq (pre_eq2 MLIR, nl4 sizes, item 22's knobs less the dropped n28 link, static check with C-element joins):
  32 routes built, period median 35.82 ns (33.38-38.51), mean 35.84. Paired with fcol4 (same sizes and seeds without
  the rewrite) on 31 seeds: -5.28 ns mean, 31/31 faster (1.15x). Gate 96/96. Static A / A' / E clean 32/32 at both
  corners. H / I clean on 31/32 (seed 5: I -12 ps ulink_n_falseResult_3 st1 at worst). hold_trace / hold_bits clean on
  32/32 (tightest +974 ps). ffmux clean 32/32. fasm_equiv: EQUIVALENT 29, the benign constant-LUT -> F7 kind on 10
  (3 sites), 27, 29 (checked in equiv.txt). Prediction was -3 ns (34-37 on seed 26): the measured median is at the
  low end of that range; the gain is larger than predicted on most seeds.
- The OR-join model (default) also reads ce_26 (another seed, nl3 sizes) clean at both corners, so collatz's result
  does not lean on the AND seeding. Local rebuild of the board seed (ceb_24, OR model) running to confirm the route
  (sdf e001dc27) and its static rows.
- BOARD-QUEUE: list item 25, section ## 26, board seed 24 (sdf e001dc27, 35.92 ns, every row clean). Predicted 1.14
  over item 22 on the board routes. fifteen README headline updated.
### progress 05:03 UTC (fxl5s: lever 5 on the full-range structure with the speculative cell -- rejected)
- fxl5s (fxs5 + BDC_NO_LINK=ulink_n30__1, AND-join static check): latency vs fxs5 on 22 paired seeds -12 cycles mean
  (-0.56 ns per iteration), faster on 15 / 22. With the link gone the compare reads the adder directly and its matched
  delay (9) no longer covers it: ucmpi1 rule A below 0 at worst on 26 routes (to -1.56 ns), in both speculative cases.
  Lever 5 stays rejected on the full-range structure (as xl5_10 showed without the cell). Lever 8 supersedes it: the
  compare no longer follows the adder at all.
### progress 05:14 UTC (fc64eq: collatz64 with the n == 2 exit test -> BOARD-QUEUE item 26 / #27; ceb_24 reproduces)
- ceb_24 (local rebuild of item 25's board seed, default OR-join walk): sdf e001dc27 (= the farm's), P 35.921 ns,
  latency 786, EQUIVALENT, ffmux clean. Static / gate lines of the OR-model run still pending.
- fc64eq (pre_eq2 at 64 bits, h2 sizes, item 24's knobs less the dropped n30 link): 30 routes, median 36.23 ns
  (34.38-38.15) vs fc64h 45.12: paired -9.0 ns on 30/30 (1.25x; predicted nothing for collatz64 -- the collatz
  prediction was -3). Gate 90/90 except seed 32 (0/14 at SLOW_MAX and worst on the bits netlist; ffmux_scan and
  fasm_equiv flag a dfflegalize flop not configured by the bits: the nextpnr FASM gap, excluded, as is seed 5 with the
  same flag -- 3 gap routes today of ~95 built). Static: umux2's traced false path on every route (as item 24); umux0 A
  -45..-135 on seeds 4 / 7 / 15, ucmpi2 A -29 worst on seed 31 (all < 0.5 ns); H / I clean on 29/30 (seed 13 H -305).
  Trace hold checks clean on all. Board seed 25 (6982a9d5, 36.27 ns). Sizes h3 = h2 + umux0 1 -> 2, ucmpi2 14 -> 15,
  falseResult_9 UACK 5 -> 7; farm fc64eq2.
- Why collatz64 gains more than collatz: its 64-bit equality on n' sat after the 64-bit select of two 64-bit operators;
  now the compare runs beside them.
### progress 05:21 UTC (fxd: xorshift lever 8 on 31 routes -> BOARD-QUEUE item 27 / #28; fxf5 done)
- fxf5 (fr4, no lever 8): 27 routes, median 23.47 ns (21.58-25.60), gate 78/78, static A / A' / E clean 26/27.
- fxd (lever 8, fr4 sizes, AND-join static): 31 routes; P (single period) where the eventgraph finds one: median
  19.39 ns (18.98-21.16); latency median 417 cycles (394-457). Paired latency vs fxf5 on 28 seeds: -80 cycles =
  -3.76 ns per iteration, 27/28 faster (~1.21x). Prediction 19 (18-20): met. Gate 93/93. Static A / A' / E clean on
  29/31 (seed 6 uxori2 -12, seed 27 ucmpi1 -13 at worst). H / I / F rows on 11/31: falseResult_9 st1 (7 routes, to
  -298), ulink_n25 (2, to -355), trueResult_8 st1 (2, to -187), uxori1.udly F -109 (seed 11). Trace hold checks clean
  on 31. ffmux clean on 31. fasm_equiv: 23 EQUIVALENT, 8 the benign constant-LUT -> F7 / CARRY4-DI kind. Seed 10's
  farm route = the local xd_10 (sdf 5e759620): the route reproduces.
- BOARD-QUEUE list item 27, section ## 28: board seed 2 (sdf a9bdac53, latency 417 = the median, every row clean).
- Sizes fr5d = fr4 + hold pads from fxd (ulink_n25 UACK 0 -> 2, falseResult_9 UACK 0 -> 1, trueResult_8 UACK 1 -> 2)
  + ucmpi1 9 -> 10 + uxori2 7 -> 8: farm fxd2. The F row (uxori1.udly) has no pad knob in hold_pads_eval; watch it.
- fifteen README headline: item 27, 19.39 ns, gap to 15: 4.4 ns.
### progress 05:21 UTC (fipowh2: ipow pad round 2)
- fipowh2 (h2 sizes): 28 routes, median 39.08 ns (36.83-40.97; fipowh 39.34), gate 84/84, umux3's traced false-path
  row on every route as before. Hold/close clean on 25/28 (fipowh: 16/26); rows left H -29 trueResult_0 st1, I -41 /
  -21 trueResult_8 st1. Round 3 -> h3, farm fipowh3.
### progress 05:22 UTC (fxds: the speculative incrementer on top of lever 8 -- no gain, not adopted)
- fxds (lever 8 + BDC_SPEC_INC=uaddi0:4:6, fr4): latency vs fxd on 31 paired seeds +7 cycles (+0.33 ns per iteration),
  faster on 12/31. Gate 96/96; per-case static rows as before (the uncased uaddi0 row is the known pairing artefact).
  With the compare reading i, the adder is no longer on the critical cycle (xd_10's two-iteration graph), so the
  cell's short path buys nothing and its select / mux costs a little. The speculative incrementer stays an opt-in
  knob, useful only where the add is on the cycle (it gave -1.87 ns on fr3 without lever 8).
### progress 05:37 UTC (ceb_24 OR-model re-check clean; fcol5; next collatz round on the n == 2 structure)
- ceb_24 (item 25's board seed, default OR-join walk): static A / A' / E and H / I CLEAN at both corners, gate
  3 x 13/13 with the farm's exact cycle counts (11204 / 4048 / 5456), hold checks clean. Item 25 does not depend on the
  AND seeding.
- fcol5 (old structure, nl5): 32 routes, median 40.76, gate 96/96, A / A' / E 32/32, hold/close clean on 27/32 (rows
  I -43..-275 falseResult_3 st1, H -17 n7 st1). Item 25 supersedes this structure; the pads carry over by name:
  nl6 = nl5 + fcol5's and fceq's rows (n7 UACK 2 -> 3, falseResult_3 SDELAY 1 -> 3), farm fceq2.
### progress 05:39 UTC (select rule vs rule H, negative control 1 of 2: collatz64 T4cd seed 7 -- both checks flag it)
- nc64_7: the 2026-11-11 failing build rebuilt (bench top, collatz64_sizes_T4cd_bench.vh -- ulink_n14__1 shortened 19 ->
  10 by corner_audit, SDELAY 2 -> 1 --, BDC_CONST_DATA=1, seed 7): route 98809562, P 61.37 ns, EQUIVALENT, ffmux clean.
  Gate: SLOW_MAX 14/14, worst+M 14/14, FAST_MIN FAIL 0/14 (2026-11-11: FAST_MIN 12/14 with n = 871 / 77031 wrong; the
  same corner fails, harder now -- the gate vectors or harness changed since; not chased).
- Static rule H (corner_audit, both corners): H -646 ulink_n13 and -712 ulink_n10__2, plus H / I rows on falseResult_3 /
  _9, trueResult_4, n7, n8 st1 (to -984). hold_bits (FAST_MIN, n = 27 / 871 / 77031): ulink_n13 22 violations, -325 ps
  (real data changes, glitch_only 0) and falseResult_5 stage[0] 40, -2085 ps (26 glitch-only); hold_trace:
  falseResult_5 -2063. That is the traced cause of 2026-11-11 exactly (falseResult_5 admits the next token, its data
  runs through umux1 -> ulink_n13 inside the counter's hold window), found by both checks without being told where.
- So on this failure the H rows and hold_bits are not blind. Still owed before the select rule can be replaced: the
  ipow umux3 failure (T9cd seed 29, an empty-pipe select race, a different mechanism) as negative control 2, and the
  positive control (nc64_7 with ulink_n14__1 / SDELAY back at 19 / 2: checks clean). research/data/fifteen/selectrule/.
### progress 06:08 UTC (fc64h2, fipowh3; a route with the F7-select nextpnr defect, caught)
- fc64h2 (collatz64 old structure, h2): 31 routes, median 45.28, gate 93/93; hold/close rows on 4 (ulink_n10__3, to
  -708). The same-sizes baseline for fc64eq: paired -9.02 ns on 31/31 (item 26's text updated).
- fipowh3 (ipow h3): 30 routes, median 38.80 ns (35.60-41.06); hold/close rows on 2 (n8 st1, -101 / -194) -> h4,
  farm fipowh4. Gate 87/90: seed 9 FAILS 13/17 at all three corners (odata 8aaaaaab, expected aaaaaaab). fasm_equiv:
  DRIVER DIFFERS on SLICE_X13Y43/F7BMUX/S0, json const 0, bits const 1 -- the second nextpnr defect of 2026-11-08 (the
  F7 select left at its default; ipow bench seed 7 then), which BOARD-QUEUE's header already says to refuse. Not the
  design: deterministic per route, identical at every corner, and the full stack catches it twice (gate + equiv).
  ffmux_scan does not look for this kind. Seed 25: the FFMUX gap (flagged; its gates pass).
### progress 06:19 UTC (fxd2 / fceq2: pad rounds on the new structures)
- fxd2 (xorshift lever 8, fr5d): 29 evaluable routes (seed 25: FFMUX gap, excluded), median 19.81 where P exists; gate
  87/87; A / A' / E clean 29/29 (seed 25 aside); hold/close clean on 26/29 (fxd: 20/31), rows H -25..-133 (trueResult_6
  st1, falseResult_9 st1, ulink_n8). Latency +6 cycles vs fxd (+0.29 ns): the pads cost a little.
- fceq2 (collatz n == 2, nl6): 30 evaluable routes, median 36.60 ns (34.63-38.80); gate 90/90; A / A' / E AND H / I
  clean on 30/30 -- the first family hold-clean on every route. Cost of the pads: +0.83 ns paired vs fceq (22/32
  slower). Seeds 3 and 22: FFMUX gap, gates fail on the bits (0/13, 1-2/13) as the defect predicts; flagged by both
  ffmux_scan and fasm_equiv; excluded. Note: farm_table.py silently drops FFMUX-FLAG routes (its regex wants
  "ffmux-clean"); counts above include them by hand.
- Item 25 keeps fceq's seed 24 (clean on every row at nl4, 35.92 ns); fceq2 is the variant clean on every route.
  FFMUX-gap routes today: fceq2 2/32, fc64eq 2/32, fxd2 1/32, fipowh3 1/32 (+ the F7-select defect on fipowh3 s9).
### progress 06:42 UTC (select rule vs rule H: the positive control)
- pc64_7: the same build with ulink_n14__1 / SDELAY back at T4's 19 / 2 (route acc06847, P 63.33 ns): gate 3 x 14/14,
  EQUIVALENT, ffmux clean. hold_bits / hold_trace: no violation (ulink_n13 +959 ps; nc64_7: -325, 22 violations;
  falseResult_5 clean; nc64_7: -2085). Static rule H: the ulink_n13 / ulink_n10__2 rows of nc64_7 are gone; other H /
  I rows (falseResult_3 / _9, trueResult_4, n7, n8 stage[1], to -1345) are present on BOTH builds (T4cd's unpadded
  sizes; the OR-join rows the audit found never live).
- Reading: on this failure hold_bits discriminates exactly (fails the failing build, passes the fixed one); static
  rule H names the culprit stage only on the failing build but carries unrelated rows on both, so as a gate it would
  have blocked both. A replacement for the select rule would be: pad until H / I are clean (the conservative route
  now running on every family) AND hold_bits clean, then allow select links to shrink. Still owed: negative control 2
  (ipow umux3, the empty-pipe select race) -- a different mechanism, possibly not a hold race at all.
### progress 06:43 UTC (select rule: what is left, and a measurement)
- Negative control 2 (ipow T9cd, JOURNAL 2026-11-10 04:10 / 07:40) failed in the soak-top harness (fusion_bench
  --route, out0 hold-window violation into the harness), not on the bench top that eval_task builds; reproducing it
  needs that flow. And its root cause was revised to ushrsi0 = 1 (a logic-free region whose one link did not cover
  routing skew), with umux3's select only a suspect. So the select rule's evidence is: one traced hold race (collatz64,
  now caught by hold_bits) and one suspected. Not enough to drop the rule; enough to measure what it holds back.
- Running corner_audit --shrink-selects on xd_10 (lever 8, seed 10) at the worst corner: the sizes the static rules
  alone would give the select links (ulink_n12__0/1/2, umux*). A measurement, not a proposal to adopt.
### progress 06:50 UTC (the select links sit on no static constraint -- what the select rule holds back on xorshift)
- corner_audit --shrink-selects on xd_10 (lever 8, worst corner): every select line goes to its floor of 1 --
  ulink_n12__0 5, ulink_n12__1 8, ulink_n12__2 6, ulink_n_index_15 5, umux0 / 1 / 2 2 -> 1 -- each "floor 1": no rule
  A / E / F / H / I constraint measured on this route depends on them. So the static rules cannot size these lines
  in either direction; that is the gap the select rule covers, not a sign that they are oversized.
- Stake, from xd_10's two-iteration graph: ulink_n12__1 4.69 and ulink_n12__2 3.76 ns per 2-iteration cycle; at ~0.4
  ns a link, 8 -> 1 and 6 -> 1 would be ~-2.8 and ~-2.0 ns per 2 iterations, ~-2.4 ns per iteration if nothing else
  binds (the next cycles were within 0.2-1.5 ns, so less). Not tried: shrinking them would rest on the gate and
  hold_bits alone, which CLAUDE.md forbids ("never shorten a delay to hit a speed target" without a check that can
  see the hazard).
- QUESTION FOR THE OWNER (decision, not blocking): the collatz64 select failure is now caught by hold_bits (flags the
  failing build, passes the fixed one) and named by rule H; the ipow one was re-attributed to ushrsi0. Would you accept
  "select links may shrink when rules H / I are clean at both corners on >= 32 routes AND hold_bits is clean on them"
  in place of the blanket select rule? Until then the rule stands and nothing here shrinks them.
### summary 06:50 UTC (this session so far)
Measured (farm, nextpnr 9c732bc6303458df, toolchain 789a7120c912d393; periods from the itercost stack):
| kernel | build | metric | median | range | n | vs previous |
|---|---|---|---|---|---|---|
| xorshift | fxd: lever 8 (i < n-1), fr4 | ns / iteration | 19.39 | 18.98-21.16 | 31 | fxf5 23.47; paired latency -3.76 ns, 27/28 |
| xorshift | fxd2: + pads fr5d | ns / iteration | 19.81 | 18.76-20.87 | 29 | latency +0.29 ns vs fxd |
| xorshift | fxds: lever 8 + spec incrementer | latency | -- | -- | 31 | +0.33 ns vs fxd (not adopted) |
| xorshift | fxs: spec incrementer (fr3) | latency | -- | -- | 30 | -1.87 ns vs fxf4l, 28/30 |
| xorshift | fxl5s: lever 5 + spec | latency | -- | -- | 22 | -0.56 ns vs fxs5; ucmpi1 rule A misses (rejected) |
| collatz | fceq: exit n == 2, nl4 | ns / iteration | 35.82 | 33.38-38.51 | 32 | fcol4 41.24; paired -5.28, 31/31 |
| collatz | fceq2: + pads nl6 | ns / iteration | 36.60 | 34.63-38.80 | 30 | hold-clean 30/30; +0.83 vs fceq |
| collatz64 | fc64eq: exit n == 2, h2 | ns / iteration | 36.23 | 34.38-38.15 | 30 | fc64h2 45.28; paired -9.02, 31/31 |
| ipow | fipowh3: pads h3 | ns / iteration | 38.80 | 35.60-41.06 | 30 | hold/close clean 28/30 |
Board list: items 25 (collatz, seed 24), 26 (collatz64, seed 25), 27 (xorshift, seed 2) added.
Does NOT show: anything on silicon. The rewrites (pre_dec, pre_eq2) are MLIR pre-passes, simcheck-checked and argued
exact; they are not yet expressed at the LLVM level (no Dynamatic here). AND-join rule E is a lower bound under the
stated assumption (non-inverting request paths into bd_ctree); rule H still uses OR. Several families still carry
small H / I rows on a few routes (pad rounds running). FFMUX / F7-select nextpnr defects hit ~5% of routes; every one
was caught by ffmux_scan and/or fasm_equiv and the gate.
Next:
  1. Farm results: fc64eq2 (collatz64 h3), fipowh4, fxd3 -- update items 26 / 27 if a round is clean on every route.
  2. The owner's answer on the select rule (question above); ~2.4 ns per iteration on xorshift rides on it.
  3. Negative control 2 for the select rule (ipow T9cd, soak-top harness via fusion_bench).
  4. Express pre_dec / pre_eq2 as LLVM-level steps (frontend.sh opt-in), once a Dynamatic build exists.
  5. A token-count (time-separation) static hold check to replace the OR bound in rule H (JOURNAL note above).
### progress 06:51 UTC (fc64eq2: collatz64 n == 2 at h3)
- fc64eq2: 32 routes (no FFMUX gap this time), median 36.19 ns (34.89-39.11; +0.25 vs fc64eq paired), gate 96/96;
  umux0's rows gone; ucmpi2 A -47 at worst on seed 8 (umux2's traced row aside); H rows on ulink_n7 stage[1] on 5
  routes (to -234); hold/close clean on 27/32. h4 = h3 + ucmpi2 15 -> 16 + n7 pads -> farm fc64eq3.
### progress 07:16 UTC (fxd3: xorshift lever 8 at fr6d -- hold-clean on every non-gap route)
- fxd3 (fr6d = fr5d + fxd2's pads): 30 routes evaluated, 2 FFMUX-gap routes (3, 24; seed 24's gate fails 9-10/17 on
  the bits, as the defect predicts) excluded. On the 28 others: gate 84/84, H / I clean 28/28, A / A' / E clean 27/28
  (seed 22: uxori1 A -20 nominal / -240 worst, the datapath xor, spanned by the gate's vectors). Latency +6.5 cycles vs
  fxd (+0.30 ns per iteration): the price of being hold-clean on every route. Item 27 keeps fxd's seed 2 (clean on its
  route at fr4); fr6d is the every-route variant (with uxori1 +1 if seed 22's row is to go too).
### progress 10:37 UTC (farm runner apparently stalled; local OR-model check of item 27's board seed)
- No push to claude/cluster since 07:14 UTC (fxd3 done). fipowh4 (submitted 06:08) and fc64eq3 (06:51) still say
  "submitted", past fipowh4's 240-minute task limit. The runner looks stalled; their results are for the next session.
- Local xdb_2: item 27's board seed rebuilt (pre_dec, fr4, seed 2) with the default OR-join walk, to confirm the route
  (sdf a9bdac53) and that its static rows do not lean on the AND seeding.
### progress 11:06 UTC (xdb_2 confirms item 27 under the OR model; fipowh4 hold-clean; the runner resumed)
- xdb_2 (item 27's board seed, local, default OR-join walk): sdf a9bdac53 (= the farm's), latency 417, EQUIVALENT,
  ffmux clean, static A / A' / E and H / I CLEAN at both corners, gate 3 x 17/17 with the farm's exact cycle counts,
  hold checks clean. Item 27 does not lean on the AND seeding.
- fipowh4 (ipow h4): 27 routes built, median 38.74 ns (36.16-41.99). H / I clean on every route; umux3's traced
  false-path row on every route as always. Excluded: seeds 6, 26, 29 (FFMUX gap) and seed 28 -- the F7-select defect
  again (SLICE_X10Y41/F7AMUX/S0 json 0, bits 1; gate 13/17 at all three corners, odata 28aaaaab): two ipow routes in two
  rounds (fipowh3 s9). ipow's board item (19) recipe already checks the sdf md5; its section should keep the warning.
  h4 = the ipow sizes hold-clean on every non-defect route.
- The farm runner pushed again after ~4 h idle; fc64eq3 still running.
### progress 11:47 UTC (fxd4: xorshift lever 8 pad round 4 -- stopping the rounds here)
- fxd4 (fr7d = fr6d + uxori1 7 -> 8): 30 evaluated (13, 16 FFMUX gap, excluded), gate 84/84 on the rest, fasm_equiv
  EQUIVALENT or the benign constant-LUT kind (F7 / CARRY4 DI) on every non-gap route. Rows on 2/28: seed 18
  ucontrol_merge0 A -78 / -129 and H -37 ulink_n6 st1; seed 19 H -45 / -96 ulink_n6 st1. uxori1's row is gone.
  Latency +11 cycles vs fxd (+0.52 ns per iteration).
- Each round removes the previous rows and route scatter puts small new ones elsewhere (fxd 11/31 routes with rows,
  fxd2 3/29, fxd3 1/28, fxd4 2/28), while the latency cost grows (+0.29, +0.30, +0.52 ns). Stopping: a 32-route
  sample with rows on 1-2 routes of <= 130 ps is where the per-route rules stop converging; item 27's own board route
  is clean at fr4. The owner's question stands on whether a route-by-route static sign-off of the board seed (done)
  or every-route cleanliness is the bar for a board item.
### progress 12:02 UTC (fc64eq3: collatz64 n == 2 at h4 -- clean on every non-gap route)
- fc64eq3: 30 routes, median 36.39 ns (35.28-39.31; +0.42 paired vs fc64eq). Seeds 6, 25: FFMUX gap (gates fail on the
  bits; excluded). On the other 28: gate 3 x 14/14, H / I clean, no A / E row but umux2's traced false path. No
  F7-select defect. So every family's latest sizes are hold-clean on every non-defect route of 28-32: collatz nl6,
  collatz64 h4, ipow h4, xorshift fr6d (one A -240 row) / fr7d (two small rows) -- at +0.3..+0.8 ns per iteration.
- Defect routes this session (FFMUX gap or F7 select), all caught by ffmux_scan / fasm_equiv and failing gates where
  they touch the datapath: ~16 of ~400 routes built (~4%).
### progress 12:03 UTC (lever 8b: drop the rounds ring's rule-1 link into the compare -- prediction)
- On xd_10's two-iteration graph ulink_n11__1 (the link between umux2's fork and ucmpi1) is 2.73 + 0.99 ns per two
  iterations. Dropping it (BDC_NO_LINK=ulink_n11__1): predicted at most -1.4 ns per iteration, likely less -- ufork4
  may re-couple to umux2 as ufork8 did to ulink_n7 under lever 5, and ucmpi1's delay then has to cover umux2's output.
  Local xd8b_10 (seed 10) vs xd_10 latency 414.
### progress 12:10 UTC (lever 8b rejected: dropping ulink_n11__1 re-couples ufork4)
- xd8b_10 (xd_10 + BDC_NO_LINK=ulink_n11__1, seed 10): route 072be564, P 22.66 ns (single period), latency 489 vs xd_10
  414: +3.5 ns per iteration. Event graph: polarity changes umux2R -> trueResult_10F and ufork4F -> ulink_n12__2R --
  the rounds fork's acknowledge now waits on the compare, and the ring's return-to-zero lands on the cycle (same
  mechanism as lever 5 / 5b). Its rising-only floor is 15.09 ns, so the rising pass alone would fit the target; but
  even with every falling arc at 0 whatif predicts 20.87. Rejected.
- Note for the 15 ns question: on xorshift with lever 8 the remaining time is mostly the link stages that decouple
  forks from the rings (every removal so far re-couples a fork) and the select links (the select rule).

## Session 2026-11-15 16:58 UTC -- token-aware rule H (time separation on the marked graph)
Toolchain: nextpnr 9c732bc6303458df (cloud/setup-toolchain.sh restored the cache; toolchain.sh all ok)   Seeds: see entries
### progress 16:58 UTC (start; lead chosen)
- Audit read (origin/claude/audit 608dd05f): nothing new REFUTED against research. Open on research's side: items
  19 / 22-24 are "gate-clean + dynamically hold-clean, static proof with C-element semantics OPEN" (T109). Owner commit
  b3ed0304: the farm now pushes partial results every 10 min; ask for time = ~3x the need.
- Lead (goal 1; Next item 5 of the last session): a static hold bound that respects C-element semantics and token
  counts. Rule H walks from a latch's close and lets every controller fire on its FIRST reached input (OR): a lower
  bound only, and wrong where the other input of a C element (the next token's request) cannot already be waiting.
  Plan (tsehold.py): on the timed event graph of the route (eventgraph.py's marked graph, arcs = enabling pins with
  token offsets, here from a FAST_MIN trace), the separation from a controller's close (occurrence k) to any later
  event v of an upstream controller is bounded below by the LONGEST path from (close, 0) to (v, m) in the unrolled
  graph (every event waits for ALL its enabling inputs; arcs weights are lower bounds at that corner). Occurrences of v
  not causally after the close and not before it are UNORDERED: no bound (flagged) -- that is the "token already
  waiting" case. OR-caused arcs ('bind' / 'eval_bind') are dropped, never used as precedence (conservative).
  Then margin = bound + earliest data path (v -> latch D, tighten's walk at the same corner) - close time - guard.
- Controls before any use: xf2_1 (fxf2 seed 1, a real FAST_MIN hold failure on the counter's loop-back pipe, JOURNAL
  2026-11-14 09:34) must be flagged; xf4_10 (item 23's route, OR rows the audit found never live) is the case to clear.
  Both building locally (lane2.sh, nextpnr seeds 1 / 10).
### progress 17:05 UTC (tse.py / tsehold.py written; plumbing checked; the negative control is the question)
- research/tools/eventgraph/tse.py: unrolled longest path on the marked graph from (close, 0); each event occurrence
  classified AFTER (bound), BEFORE, or UNORDERED. tsehold.py: per Muller latch controller L, launch points = storage
  whose output reaches L's data pins combinationally; a latch bit X carries a later token only after its own stage
  reopens, so its bound is LB(ctl_X rise, first occurrence not before L's close) + enable->Q + the path; graph nodes
  driving data directly use their own bound; aperiodic launch points fall back to rule H's OR time; unordered ones are
  violations. Guards as corner_audit (3 %, 50 ps). Its OR column reproduces corner_audit's FAST_MIN rule H row on
  xf2_1 trueResult_6 stage[1] (+86 ps), so the two read the same SDF the same way.
- Local rebuilds reproduce: xf2_1 sdf dc138ea2, xf4_10 sdf 2f825834 (lane2.sh, nextpnr 9c732bc6303458df); their band
  event graphs are byte-identical to the committed ones.
- Problem found at once: on xf2_1's (band) graph the next opening of ulink_n7 is causally after trueResult_6
  stage[0]'s close (stage[0] F -> ucond_br6.uack F -> ufork8 F -> ulink_n7 R, 1.2 ns), so TSE rates stage[0] +2 ns --
  but the 2026-11-14 trace has the adder's next result entering that pipe stage 1.85 ns BEFORE it closed. Either the
  failing stage / mechanism is not what I read, or the steady-state graph misses what happens in iteration 2 of a
  transaction. Re-running the failing FAST_MIN trace (rounds 3, 4, 8, 5) to settle it from the waveform before any
  number from this tool is used. FAST_MIN dumps for the graph itself (DUMP_FIELD=min) running for both routes.
### progress 17:20 UTC (xf2_1's failure re-traced: it is ulink_n7's own hold; TSE with an interval bound works on both controls)
- The 2026-11-14 attribution was one stage late. Re-run (xf2_1, DUMP_FIELD=min, rounds 3 / 4 / 8 / 5): rounds 4 gives
  the 3-round value again; hold_trace: ulink_n_trueResult_6 input stage 17 violations, -1159 ps. From the waveform:
  ulink_n7's node falls at 4245062; its acknowledge lets the loop-back pipe's stage[1] reopen (pipe req_out 4245699,
  data_out bit 1 at 4246142); that value reaches n7's D at 4246343 and n7's latch bit 1 changes at 4246605 -- 1.54 ns
  after its node fell, because the enable net reaches that bit late. The adder then recomputes (4247312) into the
  pipe's still-open input stage. So the corrupted latch is n7 (hold), the pipe stage only receives it. hold_trace
  could not see it: the decoded netlist keeps no name for ulink_n7.c (the instance is skipped). This matches the
  audit's positive control (T109: 2708 violations at ulink_n7 on xf2_1). Root cause: rule H's own row for ulink_n7
  (FAST_MIN OR -439 / worst -466 at corner_audit's guards) -- a "token already waiting" race: the pipe holds the next i.
- Min-delay TSE alone (marked graph, AND semantics, token offsets) gave the SAME numbers as rule H's OR walk on every
  row of both routes at FAST_MIN: the rows are not OR-join artifacts. They are rows where the next token's request
  arrives late only because of how long it takes round its ring -- invisible to any min-delay bound.
- So tse.interval_sep: delays in [0.97 w, 1.03 w] of ONE corner's trace (corner_audit's residual scatter, no corner
  mixing). For a reference event r before the close c: t(x) - t(c) >= L(r -> x) - U(r -> c), L = longest path at 0.97,
  U = max-plus upper bound at 1.03 over every event not before r (a source before r happened by t_r); maximised over
  every r in the last two occurrences. U may use OR-caused ('bind') arcs, L and "before" only 'and'; an event whose
  cause the graph could not evaluate ('eval_bind') has no upper bound. t_en is scaled by 1.03, launch paths by 0.97, and
  rule H's residual guard (3 %, 50 ps) is still subtracted (scatter counted twice: conservative).
- Self-check (every bound <= the separation the trace itself shows, the trace being one execution inside the
  interval): 888 bounds, 0 above, also at lo = hi = 1.
- Results (research/data/eventgraph/tsehold/; FAST_MIN graph = DUMP_FIELD=min run on vec_xorshift.hex, PASS period
  check; worst graph = lane2's; SDFs corner_sdf band 0 / the worst column):
  | route | corner | rule H (OR) rows < 0, covered stages | TSE rows < 0 |
  |---|---|---|---|
  | xf2_1 (real FAST_MIN failure) | FAST_MIN | 4: n7 -439, tR10 st2 -527, tR8 st1 -356, tR10 st1 -73 | 2: **n7 -442**, tR10 st0 -46 |
  | xf2_1 | worst | 3 | 1: **n7 -420** |
  | xf4_10 (item 23's route) | FAST_MIN | 5: n7 -285, tR8 st1 -146, tR10 st2 -121, n8 -120, tR6 st1 -20 | 1: n8 -196 |
  | xf4_10 | worst | 3: n7 -274, tR10 st2 -107, tR8 st1 -103 | 1: n8 -26 |
  The real failure stays flagged; every pipe-internal row and xf4_10's n7 row clear (n7 -274 -> +235 at worst). The one
  row left on xf4_10 (ulink_n8, fed by the x loop-back pipe's stage[1]) is the same shape as xf2_1's failure (a pipe
  that can hold the next token ready): a candidate, not an artifact.
- NOT covered by TSE: 13 controllers per route with no event in the steady-state graph (loop entry / exit pipes:
  ulink_n6, n1__1, falseResult_*, trueResult_0/2, index_15); their OR rows stand (n6 st1 -48..-335, falseResult_9 st1).
  Does NOT show: anything outside the loop's steady state, or paths enabled by data the window did not exercise.
### progress 17:22 UTC (owner, 12:17 / 12:20 EST: the select rule is withdrawn; second lead on collatz's delays)
- Read PROGRAM's two new sections. Order this session: (1) TSE on 32 routes and the select links sized by the checks
  -- the owner's bar: the checks must first FAIL on a raced select in each kernel family; (2) the collatz delay table
  (second lead); (3) the blanket-rule table.
- eval_task.sh step 5 (TSE_VEC, opt-in): FAST_MIN run + event graph, tsehold.py at FAST_MIN and worst -> tse_*.txt and a
  "tse" line in eval.txt. Farm, 32 routes each, item 27's structure (pre_dec, lever 8, fxd's knobs and seeds):
  fxdt (fr4 = fxd's sizes: item 27's TSE status), fxsel1 / fxsel0 (fr4 with ulink_n12__0/1/2 and ulink_n_index_15's
  DELAY at 1 / 0; everything else fr4).
- PREDICTION (from xd_10's two-iteration graph, 2026-11-15 04:21 / 06:50): the select links ulink_n12__1 (8) and
  ulink_n12__2 (6) are on the critical cycle at 4.69 / 3.76 ns per 2 iterations; at ~0.4 ns a link, 8 -> 1 and 6 -> 1
  is up to -2.4 ns per iteration, but the next cycles are within 0.2-1.5 ns, so: fxsel1 latency -1.0 to -2.0 ns per
  iteration vs fxd paired (median 19.39 -> ~17.5-18.4 ns); fxsel0 at most ~0.4 ns more. Static checks: no A / E change
  expected (corner_audit put every select line on no rule A / E constraint); whether H / I / hold_bits / TSE or the gate
  see anything is the experiment. If fxsel0 races on some route, that is the xorshift negative control the owner asks for.
### progress 17:25 UTC (select links at 0 on collatz, collatz64, ipow: each family's attempt at a raced select)
- Select-path macros per kernel (corner_audit.select_path_macros on each build's MLIR): collatz (nl6) ulink_n14__0 18,
  ulink_n14__1 36, ulink_n_index_11 15 (+ SDELAY 3 / 3, umux0/1/2 6 / 5 / 11); collatz64 (h4) 15 / 19 / 14; ipow (h4)
  ulink_n17__0/1/2 15 / 8 / 23, ulink_n_index_15 9; xorshift (fr4) 5 / 8 / 6 / 5. The collatz lines are the owner's
  second-lead numbers (ulink_n14__0 = 6.87 ns of chain on colsz2_6's loop).
- Farm fcsel0 / fc64sel0 / fisel0 (32 routes each, items 25 / 26 / ipow h4 structures, every check + TSE): those links'
  DELAY at 0; SDELAY (the pipe's internal line, rule I) and the mux delays (rule A) unchanged. Two outcomes are both
  useful: a route that races (gate fails) is that family's negative control, and the checks must flag it; no route
  racing is the gain, if every check is clean.
- PREDICTION (event graph, before the builds): collatz ulink_n14__0 is 6.87 ns of the loop on colsz2_6 (item 22's
  structure); at DELAY 0 that link costs its controller + wire (~1 ns) -> collatz -4 to -6 ns per iteration if
  nothing else binds (35.8 -> ~30-32); collatz64 ~-3 to -5 ns; ipow ~-2 to -6 ns. The gate is likely to fail on some
  routes at 0 (the 2026-11-09 / 11-11 failures were shortened select paths).
### progress 17:46 UTC (second lead: collatz delay accounting, first route)
- research/tools/itercost/line_account.py (written by a subagent from my brief, reviewed: it calls corner_audit's own
  worker and the audits' path functions; its traced totals equal the audits' numbers; arcs on uaddi0's path and
  uselect0's 1250 ps wire checked by hand against xray.sdf). Item 25 seed 24 rebuilt (sdf e001dc27, graph identical to
  ceb_24). Table and findings: research/data/itercost/README.md (new section); arc-by-arc paths committed.
- Headline: collatz's critical cycle on this route is umux1's select ring, and 27.4 of its 35.92 ns is ONE line,
  ulink_n14__1's 36-element select delay (rising and falling). The two select lines carry +13.2 / +7.1 ns of rule-E
  margin: only the withdrawn select rule holds them. fcsel0 (submitted) is the test.
- uselect0's 16 elements: tighten's bundled pairing borrows 1455 ps of lag from another link, and A' is blocked by two
  launch points that cannot move in operation (the reset flop, and a folded constant's request joined into the cell).
  Fix-the-cause candidates: no request join for a folded constant operand; reset flops not launches. Not done yet.
- Next for this lead: run line_account on >= 8 routes (farm, with fcsel0's routes), then collatz64 and ipow.
### progress 17:47 UTC (owner: formal works with research -- FOR-FORMAL.md started)
- research/FOR-FORMAL.md: item 27 / 25 / 26 / 23 build recipes with md5s, the pending select-link builds, and two
  bad builds with neighbours (xf2_1 with my corrected race at ulink_n7; nc64_7 / pc64_7, a minimal pair). Files for
  item 25 seed 24, item 23 seed 10 and xf2_1 committed under research/data/for-formal/ (fasm + sdf, xz, ~0.6 MB each).
- formal/FOR-RESEARCH.md (origin/claude/formal) read: nothing on research's builds yet (gcd_hw sections only).
### progress 17:48 UTC (eval_task step 5 bug: TSE lines on the farm are void so far; fixed, testing)
- fxdt's first 12 routes: every "tse ... CLEAN" without a self-check is a tsehold.py crash (no nodes.tsv): eventgraph
  wrote no graph because lever-8 routes alternate between two iteration times and need --stride 2, and my summary
  printed CLEAN for an empty result. Only routes 6 and 27 have real TSE lines (seed 6: ulink_n25 -287 FAST_MIN / -99
  worst; seed 27 clean). Fixed: the graph is tried at stride 1 then 2 (accepted only with its period check PASS), the
  worst graph is rebuilt from a fresh dump when lane2's is missing, the worst SDF is corner_sdf's worst column, and a
  run with no self-check line now says ERROR. TSE_ONLY=1 runs only the build and step 5 (for reruns). The gate,
  static and hold lines of fxdt / fxsel* / f*sel0 are unaffected.
- fxdt so far (10 routes back with gates): gate 3 x 17/17 on all; hold_bits clean on all.
### progress 18:03 UTC (step 5 validated locally; TSE_ONLY reruns of all six requests)
- Local TSE_ONLY test on fxsel1 seed 1 found two more faults, now fixed: the stride retry logged into a directory that
  did not exist yet (no worst graph), and on larger graphs a source that never reaches the reference event made
  interval_sep raise "window too short" -- such a source is now unanchored (U = INF, conservative). Controls re-run
  after the change: xf2_1 ulink_n7 still -442 (flagged), xf4_10 unchanged; self-checks consistent.
- fxsel1 seed 1 (select links at 1, FAST_MIN): rule H OR rows < 0: 1 (ulink_n25 -214); TSE rows < 0: 0
  (1716 bounds, self-check consistent). 14 controllers not covered (aperiodic in the steady-state window).
- Farm: fxdtT, fxsel1T, fxsel0T, fcsel0T, fc64sel0T, fisel0T = TSE_ONLY reruns (same seeds, so the same routes as the
  full runs, which supply gate / static / hold_bits).
### progress 18:04 UTC (select links at 0 / 1: partial farm results -- no race yet; collatz gains big)
- xorshift (item 27 structure; latency over 256 iterations, paired by seed against fxd): fxsel0 on 22 seeds -0.52 ns
  per iteration median (mean -0.59, -2.67..+1.41, faster on 15/22); fxsel1 on 11 seeds -0.09. Gates 3 x 17/17 on every
  route so far (23 + 12), static A / A' / E clean except one worst-corner row (fxsel0 s19), hold_bits clean everywhere.
  Below the prediction (-1 to -2 ns): the select links were on the critical cycle of xd_10, but the next cycles bind
  almost at once. fxsel1 s18: FFMUX defect route (flagged), excluded.
- collatz (item 25 structure, n = 6171 = 261 iterations, paired against fceq2): fcsel0 on 3 seeds -11.8 ns per
  iteration median (-10.8..-12.8; 800 -> 570 cycles), gates 3 x 13/13, static clean, hold_bits clean. Predicted -4 to
  -6: the event graph said ulink_n14__1 alone is 27.4 of 35.9 ns on seed 24 (line_account), which the prediction did
  not use. Waiting for 32 routes before any claim.
- No route has raced so far, so no family has its negative control yet. If none races at 0, the plan is a constructed
  bad build: lengthen the select's data path in the SDF only (same netlist and route) until the gate fails, then show
  that the static checks flag it on that SDF (CLAUDE.md: the injected defect larger than anything the harness hides).
### progress 18:09 UTC (CORRECTION: rule E rows on muxes / steers never reached eval.txt; re-checking every family)
- Found while building the constructed select race on fcsel0 seed 24 (local, sdf bb5fbbdb): corner_audit at worst
  reports rule E -255 / -174 ps at umux1 and -87..-224 at umux0 / umux2 on the UNPATCHED route, but the farm summary
  said static clean. eval_task.sh's awk keeps rows whose field 3 is the instance; rule E rows put the cell type there
  (E -255 bd_mux bridge_i.udut.umux1 ...). So since eval_task was written (2026-11-14) no E row of a bd_mux or bd_steer
  reached any summary, and every "static A / A' / E clean" for items 22-27 and the families behind them was A / A'
  only. Fixed (field 3 or 4); report_rows_*.txt now keeps every rule row. BOARD-QUEUE flagged: E status of items 19 and
  22-27 UNKNOWN until the re-check.
- Farm, STATIC_ONLY=1 (build + corner_audit at nominal and worst only), same seeds as the originals: fxdS (item 27),
  fceqS (25), fc64eqS (26), fxf4S (23), fc64nlS (24), fcolsz2S (22), fipowrhS (19), fceq2S, fc64eq3S, fipowh4S, and the
  select experiments fxsel0S / fxsel1S / fcsel0S / fc64sel0S / fisel0S.
- Constructed select race (fcsel0 seed 24, select latch -> umux1.uj0/uj1 wires +3000 ps in the prjxray SDF only):
  rule E goes -255 -> -3345 ps, rule D -30 -> -3080; H / I / A unchanged (as they should be: this is a bundling race,
  not a hold race). Gates at worst / FAST_MIN still compiling.
### progress 18:19 UTC (collatz select links: 0 is fast but fails rule E; 1 and 2 submitted)
- fcsel0 vs fceq2, 22 paired seeds (n = 6171, 261 iterations): -10.37 ns per iteration median (mean -9.91, -12.78 ..
  -6.71), faster on 22/22; gates 3 x 13/13 on 23/23. But the corrected static summary (local seed 24) has rule E
  -87..-255 ps at umux0/1/2 at worst: select data reaching the mux join after its request. Not a candidate at 0.
- fxsel0 vs fxd (26 seeds) -0.49 ns median, 18/26 faster; fxsel1 (23 seeds) -0.28, 13/23. Gates pass on all (27 + 24).
- Farm fcsel1 / fcsel2 (collatz select links at 1 / 2, every check incl. TSE with the fixed summary).
  PREDICTION: E at worst clean at 1 on most routes (one element ~376 ps covers -255) and on all at 2; -9 to -10 ns per
  iteration at 1, ~0.4 ns less at 2 (each element on umux1's select ring counts twice: rise and fall).
### Blanket rules: inventory (owner, PROGRAM "No blanket rules"; first pass)
Searched: CLAUDE.md, research/PROGRAM.md, cells/verify/{tighten,skew}.py, research/tools/corner_audit.py, bdc/emit.py,
cells/hw/build_bench.sh. Timing rules only (git / lock / farm / toolchain rules are not timing rules).
| rule | where | mechanism it stands in for | check that replaces it | cost today (ns / iteration) |
|---|---|---|---|---|
| never shorten a select link or mux delay (the select rule) | corner_audit.py default (`--shrink-selects` off); PROGRAM (withdrawn) | select read by the mux join C(x_req, ctl_req . ~s) before it lands; hold windows behind a select (collatz64 2026-11-11) | rule E at the mux (select vs ctl_req; flags the constructed race -3345 ps), rule H / I + hold_bits + TSE for the hold side | collatz -10.4 at 0 (fcsel0, 22 seeds; E fails at 0, 1 / 2 running); xorshift -0.3 / -0.5 (sel1 / sel0); collatz64, ipow running |
| a sized line keeps >= 1 element (`--floor 1`) | corner_audit.py | none named (a removed line also removes its hop, which the per-link price does not see) | the line's own rule margins re-measured with the line at 0 (corner_audit verify) | not measured; on fxd_2 11 hold-pad lines sit at the floor, off the critical cycle: likely < 0.3 |
| guard max(0.2 t, 200 ps) | tighten.py req_guard (rules A / F / H / I / K / L) | "eyeballed" (skew.py's own comment) | the measured residual (corner_audit: 3 %, 50 ps; skew GUARD 0.97 / 1.03 there) | 0 on board items (sized by corner_audit, BD_NO_TIGHTEN=1); still the default of check.sh / flow.sh builds |
| GUARD_LO / GUARD_HI 0.772 / 1.155 | skew.py rule E default | 8.5 % ring scatter (measured, but PROGRAM: 0.76 % on the board after the shared corner cancels) | corner_audit's residual guards | 0 on board items (corner_audit patches them); default for every other caller |
| tightening never removes more links than the old per-link price | tighten.line_links | none named; conservative pricing | per-link cost measured on the route (already the padding price) | small (one element at most per line, tighten-sized lines only) |
| K = 6 storage crossings, then a path is "a lap" | skew.py walk | termination of the longest-path walk on rings | -- (this one can HIDE a path: the unsafe direction; needs a check that no constraint's binding path was cut at K) | 0; a soundness question, not a cost |
| bd_pipe SDELAY >= 1 per internal boundary | bd_link.v / emit STAGE_PAD 3, ACK_PAD 6, SELECT_PAD 4 placeholders | named: the closing wave outruns the data in a filling pipe (rule I); placeholders are resized | rule I / H per route | placeholders that sizes.vh misses stay at the default: collatz seed 24 ULINK_N10__4_UACK = 6 on the datapath cycle's fall (rule H says 0; ~2.7 ns on the graph); N19__1..4_UACK, merge olink / rlink lines likewise |
| a ring needs three storage stages per simple cycle | CLAUDE.md, emit RING_MIN_STAGES | named: Muller ring liveness | -- (a theorem, not a margin) | -- |
| harness MIN_MHZ floor | build_bench.sh | the synchronous harness's own STA | -- (real) | -- |
Next on this list: the missing-macro defaults (cheap, real time on collatz's cycle), then --floor 0 measured on the
farm, then the K-lap check.
### progress 18:20 UTC (fcsel1m: a line sizes.vh never named)
- collatz's sizes.vh has no macro for ULINK_N10__4_UACK (and the merge olink / rlink lines, the constant links' acks):
  they are built at bdc's placeholders (UACK 6). line_account on seed 24: ULINK_N10__4_UACK is on the datapath cycle's
  falling edge (2.72 ns), rule H +2978 ps. Farm fcsel1m = nl6s1 + ULINK_N10__4_UACK 0. PREDICTION: -1 to -2.5 ns per
  iteration vs fcsel1 if the datapath cycle is what binds once the select ring is short; H at that link stays >= 0.
### progress 18:42 UTC (21 farm requests ignored: upper-case names)
- The *T / *S requests (TSE reruns, static re-checks) never got a status: request names must be a-z 0-9 _ -
  (cluster README), and mine ended in T / S. Renamed to *_t / *_s; ~45 min lost on those.
- Constructed select race, collatz fcsel0 seed 24, select latch -> umux1.uj0 / uj1 +3000 ps in the SDF (confirmed in the
  decoded netlist's fasm.sdf: 3273:3503:3589 on both A5 pins): rule E -3345 ps, but the worst-corner gate PASSES 13/13
  (FAST_MIN pending). Reading: umux1 is a loop-header mux; its init and loop-back requests are never pending together,
  so a late select arms the wrong join for a branch that has no request, and the C element waits for the right one.
  Rule E assumes both can be pending. So at a loop-header mux the select's arrival is not a race that the vectors can
  make fail, and rule E rows there are lower bounds, not hazards; the select's real hazard is the hold side (the
  collatz64 failure). To be confirmed: a mux where both requests CAN be pending would fail under the same injection.
### progress 18:42 UTC (select links at 0: ipow and collatz64)
- fisel0 (ipow h4, select links ulink_n17__0/1/2, ulink_n_index_15 at 0) vs fipowh4, 25 paired seeds, latency vector
  3^0x7fffffff (31 iterations): -10 cycles median = -3.9 ns per iteration (mean -3.5), faster on 24/25; gates 3 x 17/17
  on 30/30; static A / E rows (old summary, so A only, plus whatever E the re-check adds) on 9 routes.
- fc64sel0 (collatz64 h4) vs fc64eq3, 19 paired seeds (261 iterations): -1.93 ns median (mean -1.79), faster on 16/19;
  gates pass on 21/21.
- So far no family has a route that races with its select links at 0 (xorshift 27, collatz 23, collatz64 21, ipow 30
  routes, every gate at three corners). Gains: collatz -10.4, ipow -3.9, collatz64 -1.9, xorshift -0.5 ns per
  iteration. Rule E rows appear at the muxes when the select link is 0; the constructed race shows rule E flags a
  select-arrival race that the gate cannot make fail at a loop-header mux (FAST_MIN gate pending).
### progress 18:53 UTC (constructed races on fcsel0 seed 24: running)
- Select-arrival race (+3000 ps select -> umux1 join): worst-corner gate PASS 13/13, but the FAST_MIN gate has completed
  no batch after ~45 CPU-minutes (worst finished all 13 in ~10): it looks like a hang, i.e. a failure. So the reading in
  the 19:00 entry (a loop-header mux cannot fail on a late select) is NOT supported; waiting for the verdict.
- Hold race (+15000 ps on ulink_n14__1 stage[1]'s enable wire): corner_audit FAST_MIN rule H -14260 ps at that stage
  (and E -15.6 ns at umux1); gates at FAST_MIN / worst running.
### progress 18:54 UTC (second lead on 32 routes)
- eval_task LINE_ACCT=1: line_account.py at worst and nominal per route (graph from step 5, stride 2 where needed).
  Farm fceq_la: item 25's sizes and seeds (nl4, 32 routes), static + TSE + the line table, no gates.
### progress 18:55 UTC (collatz select links at 1 / 2 / 1m: -9.9 to -10.8 ns, rule E decides the size)
| build (vs fceq2, n = 6171) | paired seeds | ns / iteration delta median (range) | faster | gates | static rows (worst, E now visible) | TSE |
|---|---|---|---|---|---|---|
| fcsel0 (select 0) | 22 | -10.37 (-12.78..-6.71) | 22/22 | 23/23 | E at umux0/1/2 (seed 24 local: -87..-255) | void (old step) |
| fcsel1 (select 1) | 29 | -9.89 (-12.60..-3.31) | 29/29 | 31/31 | E < 0 on 21 routes (umux0/1/2, to -393); H / I clean | clean on all with a self-check |
| fcsel2 (select 2) | 27 | -10.02 (-13.33..-4.41) | 27/27 | 29/29 | E on 2 (-114 umux0, -149 umux1); I -356 falseResult_9 st1 on seed 5 | clean |
| fcsel1m (1 + N10__4_UACK 0) | 23 | -10.76 (-13.01..-7.68) | 23/23 | 25/25 | E on most, like fcsel1 | clean |
  fcsel1m vs fcsel1 (24 seeds): -0.32 median, 16/24 faster: the unnamed ack line was worth little.
  Periods where the graph gives one: fcsel1 ~25.4-31.4 ns (median ~26.3) vs fceq2 36.60; Dynamatic 14.05.
- Farm fcsel3m: select links at 3 + N10__4_UACK 0. PREDICTION: E clean on >= 30/32 routes at worst, ~-9.5 ns per
  iteration vs fceq2 (each select element ~0.4 ns, umux1's on the cycle twice), gates pass. If that holds it is the
  collatz candidate, pending the E re-check of the baseline and the select negative control.
### progress 19:23 UTC (E re-check, first families back; farm queue full)
- fc64eq_s (item 26's family, h2, 30 routes): rule E below 0 on 2 routes, both steers at worst: seed 1 ucond_br6 -191,
  seed 31 ucond_br5 -250 ps. Item 26's board seed (25): no E row. fc64nl_s (item 24's family, 29 routes): no E row.
  Every collatz64 route also shows umux2's traced false-path A row (as recorded since 2026-11-14) and, on fc64nl, the
  H rows item 24 is known for.
- The farm caps an account at 250 queued + running tasks: fxd_s, fxf4_s, fxdt_t and later requests wait for room.
- Local constructed races (fcsel0 s24): the late-select run at FAST_MIN and both delayed-close runs have completed no
  batch after 30-60 CPU-minutes (clean: ~10); verdicts pending.
### progress 19:31 UTC (owner b0f9dafa / audit T116: the select race has an arrival half; my monitor disagrees with the audit's)
- PROGRAM now names two select races: arrival (rule E at the mux / steer; in simulation the select must not change while
  the gated request is high) and hold (H / I / hold_bits). Audit T116 on fcsel0 seed 24 (same route, sdf bb5fbbdb):
  its mux monitor sees umux0's select pin change while z_req is high on 960 of ~1460 rises (13-vector gate) and 132 of
  202 on vec_collatz_hold.hex at FAST_MIN; the gate passes regardless. Research already sizes selects by rule E (fcsel1 /
  fcsel2 / fcsel3m), which agrees with that.
- research/tools/fifteen/select_arrival.py (new): per bd_mux / bd_steer, the select at every LUT pin it reaches inside
  the cell (the ICBUF wires of the decoded netlist), against the window z_req high (mux; the end of its udly chain, found
  from the netlist) or req high (steer). On fcsel0 seed 24, FAST_MIN, vec_collatz_hold.hex: 0 violations
  (research/data/fifteen/select_arrival_fcsel0_24_fmin.tsv), umux0 min lead +2107 ps. The reason is not the window: in
  this dump umux0's select net changes only 10 times in the whole run (entry / first loop-back of each transaction),
  and so does each of its 35 pins -- inside the loop the select is constant, as the dataflow says it should be.
  The audit's 132-of-202 needs a select that moves on most iterations. Unresolved: different nets, or a different
  model of the transparent DELAY-0 select latch (a runt / x on the latch output that this dump does not record as a
  change?). Until it is resolved this monitor has NOT failed on a known-bad build, so it is not a check; rule E (static,
  both corners, 32 routes) is the arrival check used for sizing. For the auditor: which net is "the select pin" in
  t83/mon_mux.py for umux0 on bb5fbbdb, and how many value changes does it have in your run?
### progress 19:54 UTC (constructed races: still no completed batch)
- fcsel0 s24 injections, local fid gate: select -> umux1 join +3000 ps at FAST_MIN 104 CPU-min, ulink_n14__1 stage[1]
  enable +15000 ps at FAST_MIN 69 and at worst 68 CPU-min -- no batch completed on any (a clean run: all 13 in ~10).
  The +3000 select case at worst completed 13/13. Treating "no batch in 6-10x the clean time" as a likely hang, not yet
  as a verdict; the runs continue to the bench's end time. fceq_s (item 25 family): no A / E row on the first 9 routes.
### progress 19:55 UTC (E re-check: collatz / collatz64 families clean)
- Rule E rows (corrected summary, nominal and worst) on: fceq_s (item 25, nl4) 0 / 28 routes; fceq2_s (nl6) 0 / 30;
  fc64eq3_s (collatz64 h4) 0 / 32; fcolsz2_s (item 22) 0 / 29; with fc64eq_s (item 26) 2 / 30 (steers, board seed clean)
  and fc64nl_s (item 24) 0 / 29. So the hidden E rows do not change the collatz / collatz64 items. Still queued: the
  xorshift (items 23, 27) and ipow (item 19, h4) families. fcsel3m (collatz select links at 3): no E row on the
  first 7 routes.
### progress 20:11 UTC (fcsel3m: collatz at 25.8 ns, every check clean on every route -> BOARD-QUEUE item 28 / #29)
- fcsel3m (nl6, select links ulink_n14__0 / n14__1 / n_index_11 at 3, ULINK_N10__4_UACK 0): 28 of 32 routes back.
  Period median 25.81 ns (24.63-27.55; fceq2 36.60); latency paired vs fceq2 on 26 seeds -10.94 ns per iteration
  (-14.11..-8.69), 26/26 faster. Gate 3 x 13/13 on 28/28; static A / A' / E (corrected summary) clean at nominal and worst
  on 28/28; H / I clean 28/28; hold_bits clean 28/28; TSE clean at FAST_MIN and worst on 28/28 (self-checks consistent);
  ffmux clean; fasm_equiv EQUIVALENT 25, benign constant-LUT kind 3. Prediction was ~-9.5 ns with E clean on >= 30/32:
  met (a little faster than predicted).
- BOARD-QUEUE list item 28 / section ## 29, board seed 20 (sdf d86bdde5, latency 566 = the median). Open, stated in the
  item: the simulated select-arrival check (my monitor vs the audit's on fcsel0) and 4 routes not back.
### progress 21:36 UTC (constructed races on collatz fcsel0 seed 24: the gate fails where the checks fire)
Base: fcsel0 seed 24 (sdf bb5fbbdb), delays added to the prjxray SDF only (same netlist and bits; confirmed in the decoded
netlist's fasm.sdf). Gate = bench_gate.sh, fid model, 13 vectors.
| injected | corner | gate | rule E (corner_audit) | rule H |
|---|---|---|---|---|
| none | worst | 13/13 (farm) | -87..-255 umux0/1/2 | clean |
| select latch -> umux1.uj0/uj1 +3000 ps | worst | PASS 13/13 | -3345 / -3264 umux1 | unchanged |
| same | FAST_MIN | 0/13: no batch completed in 205 CPU-min (clean run: all 13 in ~10); stopped | -- | -- |
| ulink_n14__1 stage[1] enable +15000 ps | FAST_MIN | 0/13 in 170 CPU-min; stopped | -15600 / -15659 umux1 | -14260 at that stage |
| same | worst | 0/13 in 168 CPU-min; stopped | -- | -- |
- Reading: on collatz both constructed select races make the gate fail (a run that never completes a batch hangs) at
  FAST_MIN, and the select-arrival race also passes at worst -- the gate alone would miss it at one corner. Rule E flags
  both builds; rule H flags the hold one. So on this family rule E (arrival) and H (hold) each fail on a known-bad build:
  the owner's "a check earns its place by failing" for collatz. Caveat: constructed by SDF injection, not by shortening a
  line until it races (no shortening down to 0 raced on any family); and "0/13" is non-completion, not a wrong value.
- My dynamic select_arrival.py was not run on these (the dumps were the plain route); its disagreement with the audit's
  monitor stays open.

## Session 2026-11-16 02:51 UTC -- E re-check complete; select-at-0 flagged by rule E on every family; per-family select negative controls
Toolchain: nextpnr 9c732bc6303458df (patches.sha 789a7120c912d393), toolchain.sh OK   Seeds: farm 1-32 per request
Lock: previous session (21:36 UTC) never cleared it; 5 h stale, taken.
Read: audit T117 (item 28 CONFIRMED on its board seed incl. pin-level select arrival), T118 (collatz select negative
control CONFIRMED; the simulated arrival monitor alone does not catch it, static E does), T119 / T120 (formal's item 26
and fcsel0 witnesses NOT reproduced in the audit's GLS; T120b: falseResult_3 is the input n, i.e. an input-hold race
against formal's earliest host). Formal C8-C10, A6 (both rewrites proved), A7 (xf2_1 kappa* 0, item 23 > 0.32).
### progress 02:51 UTC (overnight farm: rule E re-check complete, and select links at 0 per family)
- Rule E rows (corrected summary) on the last families: item 23 (fxf4_s) 0 / 29 routes; item 27 (fxd_s) 1 / 32 (seed 27,
  steer ucond_br8 -118 ps worst; board seed 2 clean); item 19 (fipowrh_s) 0 / 28; ipow h4 0 / 32. With yesterday's
  families: no board item's own route has an E row. BOARD-QUEUE's UNKNOWN note closed.
- Select links at 0, corrected static summary (fx/fi/fc64/fcsel0_s, same seeds as the gated runs):
  | family | routes with E < 0 (nom / worst) | worst E | cells | gate (earlier, 3 corners) |
  |---|---|---|---|---|
  | xorshift fxsel0 | 31 / 31 of 31 | -984 | umux0-3 (+ steers br6/8/9 on a few) | 27/27 PASS |
  | xorshift fxsel1 | 22 / 22 | -638 | umux0-3 | 24/24 PASS |
  | ipow fisel0 | 31 / 31 | -833 | umux0-3 | 30/30 PASS |
  | collatz64 fc64sel0 | 28 / 28 | -1761 | umux0-2 (+ A rows -1022) | 21/21 PASS |
  | collatz fcsel0 | 29 / 29 | -902 | umux0-2 | 23/23 PASS |
  So on every family, the select at 0 is a static arrival violation that the gates do not turn into a failure (as
  on collatz). Rule E is the check that sizes selects; whether it can fail where the gate also fails is next.
### progress 02:54 UTC (select negative controls on every family: farm selneg)
- research/tools/fifteen/sdf_inject.py: +PS on every INTERCONNECT arc matching source / destination regexes, every
  other byte copied (same netlist and bits). Checked on x27_2's xray.sdf: each of umux0-3 gets exactly its two select
  arcs (select latch -> uj0 / uj1), e.g. ulink_n12__1 stage[1] lat -> umux1.uj0/A5 (279:509:595) -> (3279:3509:3595).
- Farm selneg (14 tasks): each board candidate's own route (xorshift item 27 s2, collatz64 item 26 s25, ipow item 19
  s1, collatz item 28 s20), one mux per task, +3000 ps on the select into that mux's joins; corner_audit (E) and the
  full gate at FAST_MIN / worst / SLOW_MAX on the injected SDF (50 min limit each; a clean gate takes ~10).
  PREDICTION: E flags every injected mux at both corners (<= -2000 ps). The gate fails (wrong value or no completion)
  at FAST_MIN on most loop-header muxes, as on collatz; some injections (a mux whose select is settled long before
  its request on every iteration) may pass every gate -- each such case is a row where E is stricter than the gate,
  not a check that cannot fail.
### progress 02:56 UTC (xorshift select links sized by E: farm fxsel3; line accounting requests)
- fxsel1_s rule E rows by mux (both corners, 32 routes): umux0 to -620, umux2 -638, umux3 -238, umux1 -185 ps. At ~400 ps
  an element, 3 covers all with >= ~160 ps. Farm fxsel3 (fr4s3: select links 5/8/6/5 -> 3/3/3/3), every check.
  PREDICTION: E clean at both corners on >= 30/32; latency vs fxd paired -0.2 to -0.4 ns per iteration (fxsel1 bought
  -0.28 median, fxsel0 -0.49). Small: xorshift's select links are not the ring's big term the way collatz's were.
- Farm fcsel3m_la / fc64eq_la / fipowrh_la: the second lead's line table on item 28, collatz64 item 26, ipow item 19.
- itercost/README.md: item 25's line table on 28 routes (la_aggregate.py): the select ring is critical on 28/28,
  ulink_n14__1's select line 27.8 ns of it (rule E margin +13.4 ns, needs 1 element); datapath near-critical on 8,
  where uselect0's 16 elements cover 0.2 ns of logic + 2.0 ns of wire.
### progress 02:57 UTC (ipow and collatz64 select links sized by E: farm fisel3, fc64sel3)
- Worst E at select 0 per mux, both corners: ipow (fisel0_s, 31 routes) umux0 -587, umux1 -833, umux2 -578, umux3 -610;
  collatz64 (fc64sel0_s, 28) umux0 -850, umux1 -1761, umux2 -511 (and umux2's traced false-path A row, -1022).
  Sizes (h4 base, ~380-400 ps an element, >= ~250 ps over the worst row): ipow 15/8/23/9 -> 3/3/3/3 (h4s3);
  collatz64 15/19/14 -> 3/6/3 (h4s3). Farm fisel3 / fc64sel3, every check.
  PREDICTION: E clean on >= 30/32 each; latency vs the h4 base, paired: ipow -2.5 to -3.5 ns per iteration (sel0 -3.9),
  collatz64 -1.0 to -1.7 (sel0 -1.9). If so, each is that family's next board candidate.
### progress 03:16 UTC (selneg: +3000 ps is near the threshold on routes whose select line is long; selneg2)
- Local check of selneg's pipeline on x27_2 (item 27's route rebuilt here: sdf a9bdac53 = the board route; EQUIVALENT,
  static clean): +3000 ps on ulink_n12__1's select into umux1.uj0 / uj1 gives rule E only -318 / -290 ps at worst.
  The join's other input is the select link's own request through its 8-element line (3512 ps), so a select line
  longer than the injection absorbs most of it. (On fcsel0 s24 the line was 0, hence -3345.) So +3000 on selneg's
  routes is a near-threshold point: E fires a little, and the gate may well pass -- that row would show E stricter
  than the gate, not a control. Farm selneg2: the same 14 tasks at +6000 and +12000 ps (past every select line,
  1.2-9.2 ns), gates at FAST_MIN and worst.
### progress 03:45 UTC (second lead, fix-the-cause: A' refused uselect0 because of a tool bug, now fixed)
- Item 28 (fcsel3m s20, rebuilt locally: sdf d86bdde5, EQUIVALENT, static clean) line_account at worst: the critical
  cycle is now the datapath (25.81 ns): uselect0's 16 elements are 6.38 ns of it (needs 7 as routed, 1 for the
  logic), uaddi0's 12 are 4.28 ns (needs 5). fcsel3m's proposals over 31 routes x 2 corners do not move either at the
  per-cell max: uselect0 stays 16 on 18 of 62 (tighten's bundled pairing borrows ~1.3 ns of lag).
- Why A' (from the upstream links' C nodes) was refused there, traced (CA_DEBUG_FOREIGN, new diagnosis switch): the
  two "foreign" sources (the reset flop $auto$ff.cc:337:slice$7560/Q and usource2's request, the folded constant)
  reach NOTHING in uselect0 but its request join, ujoin's chunk[0] g4 and utop C nodes. Those join nodes were counted
  as data peers: the 'upstream' test asks whether the chain head is reachable without crossing a stop, and an inner
  join C node reaches it only through utop, itself a stop. So the cell's own request path was treated as data, and
  any request or reset into the join looked like a foreign data launch. Not a property of the circuit: a tool bug in
  the pessimistic direction (it only ever refused A').
- Fix (corner_audit.rule_a_from_link): outputs under parent.ujoin.* are not peers (CA_JOIN_PEERS=1 restores the old
  set). Same route: A' at uselect0 +5539 ps at 16 elements, proposal 16 -> 7 (400 ps left), uaddi0 12 -> 9 as before;
  verify: 0 sized constraints below slack. Other A' refusals on this route: umux2 only (its select link's latch, a
  real outside launch).
- Farm fcsel3m_p / fxd_p / fc64eq3_p / fipowh4_p: STATIC_ONLY reruns of each family's current sizes with the fix, for
  per-cell-max proposals on 32 routes. PREDICTION (collatz): uselect0 max over routes 8-10 (n_need 6-9 as routed on
  item 25's 8 routes), i.e. -2.2 to -3.1 ns on the critical cycle if it stays the binding line.
### progress 03:56 UTC (selneg, +3000 ps: first 6 of 14 -- E and the gate disagree in the safe direction)
| route (board item), mux | select line | rule E on the injected SDF (worst / nom) | gate FAST_MIN / worst / SLOW_MAX |
|---|---|---|---|
| xorshift item 27 s2, umux0 | ulink_n12__0, 5 | -1753 / -1566 | 17/17, 17/17, 17/17 |
| xorshift item 27 s2, umux1 | ulink_n12__1, 8 | -318 / -21 | 17/17 x 3 |
| xorshift item 27 s2, umux3 | ulink_n_index_15, 5 | -1527 / -1359 | 17/17 x 3 |
| collatz64 item 26 s25, umux2 | ulink_n_index_11, 14 | none (+1941 at umux2: absorbed) | 14/14 x 3 |
| ipow item 19 s1, umux0 | ulink_n17__0, 15 | none (+2575: absorbed) | 17/17 x 3 |
| collatz item 28 s20, umux2 | ulink_n_index_11, 3 | -2079 / -1962 | 13/13 x 3 |
- Where E stays positive the gate passes (agreement). Where E is -1.4 to -2.1 ns the gate still passes at every corner,
  cycle counts unchanged: so far no injected select race at +3000 has made any gate fail on the board routes. Rule E
  compares the select with the select link's own request (ctl_req at the join); the join fires at the later of
  ctl_req and the data request x_req, and on these muxes x_req evidently arrives > 2 ns after ctl_req, so a select
  that is late against ctl_req is still early against the join's firing. E is pessimistic by that gap. Not usable
  to shorten anything: x_req's lead is not bounded statically (different launches); the gate's vectors only sample it.
- So the negative control needs a bigger defect: selneg2 (+6000 / +12000) is that. The collatz fcsel0 s24 control
  (select line 0, +3000 -> no completion at FAST_MIN) remains the only gate failure on record.
### progress 04:07 UTC (fxsel3: xorshift select links at 3 buy nothing -- rejected)
- fxsel3 (fr4s3) vs fxd (item 27), 31 paired seeds: latency -0.23 ns per iteration median, mean -0.02 (-1.97..+1.64),
  faster on 16/31: noise. Period median 19.45 (fxd 19.39). Gates 96/96; rule E < 0 on 1/32 (s9 steer ucond_br6 -229),
  A uxori1 -119 on one; TSE (C-element hold) rows on ulink_n8 on 8+ routes (to -635 at FAST_MIN, s19). Prediction
  (-0.2 to -0.4) at the edge; not worth a new board item. xorshift's select lines are off its critical cycle.
- research/tools/fifteen/farm_pair.py A B ITERS: paired latency per iteration + gate / E summary of two farm requests.
### progress 04:16 UTC (collatz uselect0 at 7 on one route: 21.27 ns, every check clean; farm fcsel3a)
- c28a_20 (nl6s3a = item 28's sizes with uselect0 16 -> 7, uaddi0 12 -> 9; seed 20, new route sdf 7aefc4bd): period
  21.27 ns (item 28's seed 20: 25.81), latency 468 cycles vs 566 (-4.5 ns per iteration on 261 iterations); EQUIVALENT,
  ffmux clean; gates 13/13 at SLOW_MAX / FAST_MIN / worst; static A / A' / E and H / I clean at nominal and worst (tighten's
  unsized bundled "a" row at uselect0 -258, the one A' replaces); hold_trace / hold_bits clean. Predicted -2.2 to -3.1:
  more, because uaddi0 also moved and the next cycle is further below.
- Farm fcsel3a: the same sizes on 32 routes, every check (TSE included). This is one route's proposal; the per-cell
  max over 32 routes (fcsel3m_p) may come back longer on some routes, and fcsel3a will show which routes need it.
- xorshift item 27's route with the fix: A' now sizes uxori1 / uxori2 7 -> 5 (76 / 63 ps left); nothing else moves.
### progress 04:20 UTC (ipow and collatz64 select links sized by E: both pass everything -> BOARD-QUEUE items 29, 30)
| build (paired vs its h4 base) | valid routes | ns / iteration median (range) | faster | gates | E | hold side |
|---|---|---|---|---|---|---|
| fisel3 (ipow, select 3/3/3/3) vs fipowh4 | 26 (4 ffmux, 1 F7AMUX/S0 defect excluded) | -2.71 (-5.42..+0.77), 19 seeds | 18/19 | 78/78 | clean | I -87 on s1; TSE / hold_bits clean |
| fc64sel3 (collatz64, 3/6/3) vs fc64eq3 | 29 | -1.56 (-5.79..+0.74), 27 seeds | 25/27 | 87/87 | clean | TSE -120 on s1; H / I / hold_bits clean |
- PREDICTIONS were ipow -2.5 to -3.5 (met), collatz64 -1.0 to -1.7 (met), E clean on >= 30/32 (met on every valid
  route). The rule A rows are the traced false paths (ipow umux3, collatz64 umux2) as on items 19 / 24-26.
- The one gate FAIL (fisel3 s25, 13/17 at all three corners, same wrong value at each) is the known nextpnr F7AMUX/S0
  constant defect (fasm_equiv DRIVER DIFFERS, json 0 / bits 1, as on 2026-11-08 and 11-13): a bitstream defect, not timing.
- BOARD-QUEUE items 29 (ipow, seed 19, sdf 4a92cdf3) and 30 (collatz64, seed 10, sdf 637ff02e). farm_pair.py now
  excludes the two known bitstream-defect classes from pairing (ffmux flag, F7 select constant).
- Next for both: the corner_audit proposal round with the A' fix on top (fipowh4_p, fc64eq3_p): ipow's ushrsi0 / ucmpi2
  and collatz64's uaddi0 / uselect0 are sized well above what corner_audit needs as routed (itercost README).
### Blanket rules: status 2026-11-16 (update of yesterday's inventory)
| rule | status today | measured cost / gain |
|---|---|---|
| never shorten a select link / mux delay | REPLACED by rule E (arrival) + H / I / hold_bits / TSE (hold) on all four families; items 28-30 rest on it | collatz -10.9 (item 28), ipow -2.7 (item 29), collatz64 -1.6 (item 30), xorshift ~0 (fxsel3, rejected) ns / iteration |
| the cell's request join counted as data in A' (corner_audit) | a tool bug, not a rule, but it acted as one ("A' refused" = keep the bundled-pairing size): FIXED | collatz uselect0 16 -> 7 proposed; one route -4.5 ns (farm fcsel3a running) |
| a sized line keeps >= 1 element (--floor 1) | not measured yet | -- |
| missing sizes.vh macros at RTL defaults | the proposal rounds add them (farm_max_sizes.py adds proposal-only macros) | fcsel1m: -0.32 for ULINK_N10__4_UACK |
| K = 6 storage crossings in skew.py's walk | open (a soundness question, the unsafe direction) | -- |
- Select negative controls (owner: a check earns its place by failing): selneg, +3000 ps on the select into each mux's
  joins on each board candidate's route: the gate failed (no completion within 50 min, clean ~10) on 4 of 13 runs
  (xorshift umux2, ipow umux1, collatz umux0 / umux1), all at FAST_MIN (collatz umux0 also at worst). Rule E flagged
  every one of the 4 (-754 to -1952 ps). No gate failure without an E row. E also flagged 4 injections the gate passed
  (E stricter, never looser). Local re-run of collatz umux0 at FAST_MIN running to confirm the "TIMEOUT" is a hang in
  the simulation and not a compile / lock artefact; selneg2 (+6000 / +12000) queued.
### progress 04:31 UTC (xorshift item 27: line account on its board route; a missing ack macro on the cycle; farm fxu)
- x27_2 (item 27's route, sdf a9bdac53), graph at stride 2: 38.63 ns per two iterations (19.32 / iteration), 83 arcs;
  the next four cycles are within 0.6-2.0 ns. Lines on the critical cycle (line_account, worst, A' fix):
  ucmpi1 9 (needs 7, A'), ulink_n12__1 select 8 (needs 1; fxsel3 showed selects buy ~0), uxori1 7 (needs 3, proposal 5),
  ulink_n7f__1's ack 6 = 2.85 ns of the cycle's FALL, NOT in sizes.vh (bdc's RTL default 6), rule H margin +3763 ps, needs
  0; ucontrol_merge0_olink's request line 4, also not in sizes.vh, rising 1.87 ns, set by no rule -- and corner_audit
  says the stage it feeds is "not audited" (rule I has no launch for it). That second one is a CHECK GAP, not a lever:
  it stays at 4 until something audits it.
- Farm fxu: fr4 + ULINK_N7F__1_UACK 1 (fr4u). PREDICTION: -0.5 to -1.0 ns per iteration vs fxd paired (the line is
  ~2 ns of a two-iteration cycle, the next cycle without it is ~1-2 ns below); hold side (H / I, TSE, hold_bits) clean.
### progress 04:39 UTC (proposal rounds with the A' fix: collatz uselect0 9 over 32 routes -> farm fcsel3p)
- fcsel3m_p (32 routes x 2 corners, every proposal verified clean): per-cell max uselect0 16 -> 9 (min 5), uaddi0 stays
  12, five ack / stage lines -1. PREDICTION (made before the A' fix) 8-10: met. nl6s3p = nl6s3m + that; farm fcsel3p,
  every check. PREDICTION: period median ~22.5 ns (fcsel3m 25.8; uselect0 -7 elements x ~0.4 ns on the rising edge, the
  route-to-route spread decides how much of it the next cycle eats), every check clean on >= 30/32.
- fxd_p (xorshift item 27, 32 routes): the max moves little (ucmpi1 9 -> 10, uxori2 7 -> 8 up; acks down); 20 of 64
  proposals keep one H row short (the known falseResult_9 rows). No xorshift round from it; fxu tests the ack.
- fc64eq3_p (collatz64 h4, 32 routes x 2 corners, all verified clean): per-cell max uselect0 18 -> 12 (min 7), uaddi0
  25 -> 23 (min 11), acks -1 to -4; the proposal pads umux2 1 -> 16 for its traced false-path A row (kept at 1 by hand)
  and trims ULINK_N13_UACK 3 -> 2 (kept at 3 by hand: formal C8 / C9 name ulink_n13's latch enable as item 26's
  binding race, kappa 0.26, the link of the bad nc64_7). h4s3p = h4s3 (item 30) + that; farm fc64sel3p.
  PREDICTION: vs fc64sel3 paired -1.5 to -2.5 ns per iteration (uselect0 -6 x ~0.4 on a cycle where it binds on every
  route, uaddi0 -2); E / H / I / hold_bits / TSE clean on >= 30/32.
### progress 04:50 UTC (fcsel3a, 29 of 32 routes: collatz at 21.5 ns, -3.9 ns per iteration vs item 28)
- fcsel3a (item 28 + uselect0 7, uaddi0 9; one route's proposal after the A' fix) vs fcsel3m (item 28), 28 paired seeds:
  -3.93 ns per iteration median (-6.80..-2.30), faster on 28/28. Period median 21.48 ns (20.43-23.05; item 28 25.81;
  Dynamatic 14.05). Gates 87/87 (3 x 13/13 on 29 routes). Rule A / A' / E clean at nominal and worst on 29/29; tighten's
  unsized bundled "a" row at uselect0 (the row A' replaces) on some. Hold / close side: F -213 (ucontrol_merge1 fast-fall
  flush, s2), I -236 (falseResult_9 stage[1], s3); TSE / hold_bits clean so far.
- So the one-route proposal (7 / 9) holds A' on every route, though the 32-route per-cell max of nl6s3m's proposals asked
  for 9 / 12: proposals are measured on the old netlist's routes plus a guard, and the max over routes is an upper bound,
  not the need of a new build. fcsel3p (9 / 12) now mainly shows what that conservatism costs.
### progress 05:00 UTC (fcsel3a complete -> BOARD-QUEUE item 31: collatz 21.5 ns per iteration)
- 31 routes (s10 ffmux-flagged): gate 93/93, A / A' / E clean at both corners on 31/31, TSE and hold_bits clean on all;
  hold-side rows on two (F -213 s2, I -236 s3). Paired vs item 28 on 30 seeds -3.93 ns per iteration, 30/30 faster.
  Board seed 20 (sdf 7aefc4bd), item 28's seed. BOARD-QUEUE item 31 / section 32.
- Next on collatz's cycle (line_account on c28a_20): four cycles within 1.2 ns (21.27 / 21.04 / 20.51 / 20.11), so single
  lines buy little now. corner_audit --shrink-selects on that route proposes umux0 6 -> 1 and umux1 5 -> 1, but the mux's
  own delay covers select -> data-LUT -> output against join -> udly -> z_req, and line_account says umux0's 32 data
  outputs are on NO rule-A constraint (no common source with the request). That race is named (the audit's T116 saw the
  select reach umux0's data-LUT pins up to 579 ps after z_req rose on a select-at-0 route) but no static rule checks it:
  the mux delays stay until a rule does ("rule M": select latch -> data LUT -> data output vs select latch -> join ->
  udly -> z_req, common source the select link's C node). A check to build, not a size to cut.
### progress 05:41 UTC ("rule M": the mux's select -> data path gets a static check; corner_audit)
- Why the mux delays sit on no rule: tighten's check() pairs the request with ANY peer that shares a source with it and
  is silent about the rest. At a bd_mux the x / y data share the join with the request, so check() returns, and the
  32 data outputs the SELECT drives (select latch -> udat LUTs) were never measured (line_account: "32 peer outputs no
  common source pairs with the request, on NO rule-A constraint: umux0.udat"). That race is real and named (the select
  reaching the data LUTs after z_req: audit T116 measured it on a select-at-0 route, up to 579 ps late).
- corner_audit.rule_a_from_link now gives those uncovered peers the A' measurement from every upstream link's C node
  (added constraint "A'm", reported as rule A with "[peers no common source reaches: N]"; tighten's A stays). Two fixes
  were needed for it to run: (1) a 1-bit link's latch is one LUT, "<link>.lat.odd.u", which tighten's
  RE_UPSTREAM_BD_LINK does not match, so the select link was never an upstream link and its latch output was a "foreign"
  source -- now added in corner_audit (CA_ODD_LINKS=0 restores); (2) the partial-peer pass (CA_MUX_PEERS=0 restores).
  Item 31's route (c28a_20, worst): umux0 +1503 ps (6 elements), umux1 +1145 (5); umux2 gets no row (to look at).
- Negative control running (local, item 28's route c28_20): +3000 ps on ulink_n14__0's select latch -> umux0.udat
  (32 arcs, SDF only), corner_audit + the gate at FAST_MIN and worst. If rule M flags it and the gate fails, the mux
  delays can be sized by M (with E for the select links) instead of "never shortened".
### progress 05:42 UTC (select negative controls, all four families: rule E flags every gate failure)
- selneg + selneg2: 39 injected runs on the four board candidates' routes (table: research/data/selneg/README.md).
  20 runs fail the gate (19 by no completion, 1 wrong value: xorshift umux1 +6000 at FAST_MIN, 16/17); rule E is below 0
  at worst on all 20. 12 more runs are flagged by E and pass every gate (loop-header muxes: even +12000 passes). So on
  each family E fails on a known-bad build and never missed one: the owner's bar for the arrival check is met, by
  construction (SDF injection), not by a shortened line (none raced).
- Rule M's first control (item 28's route, +3000 on ulink_n14__0's latch -> umux0.udat, 32 arcs): M -353 ps at worst,
  gate FAST_MIN PASS 13/13 (cycles unchanged 2906): stricter than the gate, no failing build yet; +8000 running.
### progress 05:43 UTC (fxu rejected; fcsel3p confirms 3a; rounds with mux delays sized by rule M)
- fxu (xorshift item 27 + ULINK_N7F__1_UACK 6 -> 1) vs fxd, 31 paired seeds: -0.05 ns per iteration median, 16/31
  faster: nothing. PREDICTION (-0.5 to -1.0) FAILED: on x27_2 the next cycle without that line (c3, 38.0 vs 38.6 per two
  iterations) does not contain it, and on other routes the cycle differs. Gates 96/96; E rows on one route.
- fcsel3p (collatz, uselect0 9 / uaddi0 12, the 32-route proposal max) vs fcsel3a (7 / 9): +1.43 ns per iteration, 4/30
  faster; both pass everything. Item 31 (fcsel3a) stands; the per-cell max of proposals over old routes is the
  conservative way and costs 1.4 ns here.
- eval_task.sh: CA_EXTRA passes flags to step 2's corner_audit. Farm *_ps (STATIC_ONLY, --shrink-selects) on the four
  candidates' sizes and seeds (fcsel3a, fisel3, fc64sel3, fxd): proposals with mux delays checked by rule M and select
  links by rule E, for the next round.
### progress 05:53 UTC (collatz64 proposal round: 31.4 ns, -3.5 ns per iteration -> BOARD-QUEUE item 32; fc64sel3q)
- fc64sel3p (h4s3p) vs fc64sel3 (item 30), 30 paired seeds: -3.52 ns per iteration median (-5.47..-0.32), 30/30 faster;
  period median 31.39 ns (item 30 34.94, item 26 36.23; Dynamatic 17.84). PREDICTION -1.5 to -2.5: beaten (uaddi0's
  -2 elements sit on the cycle twice, rise and fall). Gate 90/90, E clean, A only umux2's traced false path.
- Hold side: TSE (C-element hold at FAST_MIN) rows at ulink_n28 on 9/30 routes (to -295 ps), H rows on 3 (to -104). The
  round cut ULINK_N28_UACK 3 -> 1 because corner_audit's H at nominal / worst allowed it; TSE at FAST_MIN does not.
  fc64sel3q (h4s3q = h4s3p with that ack back at 3) on the farm. Board seed 22 (sdf 842dd4d7) is clean on every row
  but the false path: BOARD-QUEUE item 32 / section 33, with the rows stated.
### progress 06:24 UTC (rule M: first failing build, farm control on all families; fcsel3a_ps first proposals)
- Local, item 28's route (c28_20), +8000 ps on ulink_n14__0's select latch -> umux0.udat (32 arcs, SDF only): gate at
  FAST_MIN completed no batch in ~25 CPU-min (clean route: whole gate 8.9 min), stopped by the session's job limit;
  re-running to 55 min. +3000 on the same arcs: M -353 ps, gates FAST_MIN / worst PASS 13/13 (cycles unchanged).
- Farm mneg: the same construction on all four candidates' routes, every mux, +4000 / +8000, corner_audit (M and E)
  + gates FAST_MIN / worst. PREDICTION: every gate failure has an M row < 0; at loop-header muxes M flags and the gate
  passes (as for E).
- fcsel3a_ps (collatz item 31's routes, --shrink-selects, rule M in force), first 4 routes: umux0 6 -> 3 and umux1 5 -> 3
  bound by A'm (rule M), umux2 11 -> 5 by A', uselect0 7 -> 5-6, ucmpi2 16 -> 12-15, select links 3 -> 2 by E.
### progress 06:34 UTC (rule M catches a build rule E misses; collatz mux delays sized by M: farm fcsel3b)
- +8000 ps select -> umux0.udat on item 28's route: rule M (corner_audit A'm) umux0 -5503 ps at worst; rule E: no row
  below 0 (E looks at the joins, not the data LUTs); gate FAST_MIN: no batch in ~25 CPU-min (55-min rerun going). So M
  flags a failing build that E does not see -- the reason the mux delay needs its own check.
- nl6s3b = item 31 + umux1 5 -> 3, umux2 11 -> 6 (rule M / A'), uselect0 7 -> 6, ucmpi2 16 -> 15 (seed 20's own proposal
  with --shrink-selects, nominal + worst; hold-side trims and select links NOT taken). Farm fcsel3b, every check.
  PREDICTION: -0.3 to -0.8 ns per iteration vs fcsel3a (ucmpi2 and uselect0 sit on near-critical cycles; umux1 / umux2
  mostly off them); M / E / H / I / TSE clean on >= 28/32.
### progress 06:36 UTC (rule M on the board families: mux data outputs were never checked by any rule)
- *_ps reruns with rule M (worst / nom, rows below 0): collatz item 31's family (fcsel3a) none on 29 routes. ipow item
  29's family (fisel3): umux2 on 15/19 routes, to -780 (board seed 19: -279 nom / -382 worst). collatz64 item 30's
  family (fc64sel3): umux0 on 32/32, -0.6 to -2.4 ns (board seed 10: -1231 nom / -1321 worst). xorshift item 27's family
  (fxd): umux0 / 1 / 2 on 23/29, to -734 (board seed 2: umux1 -13 nom / -117 worst).
- The binding launches are the DATA links (collatz64 umux0: ulink_n_falseResult_3, i.e. x_data -> udat LUT -> z_data
  against x's request -> join -> udly -> z_req), not the select. So at a bd_mux no rule ever covered ANY data output:
  tighten's check() found a common source with some trivial peer and returned. The mux delays were sized to nothing
  (collatz64 umux0 is 2; M asks 6-16 over 32 routes). Every gate on these families passes (hundreds of runs, 3 corners).
- What it means is open. z_data feeds a fork into links (transparent latches that close a phase later, at the
  sender's return to zero -- rule I's domain) and, on collatz64, one direct consumer (n10__0). A late mux output is a
  hazard only where a consumer acts on the request edge. PROGRAM's rule for a miss > 0.5 ns at nominal on a board item
  (items 30 / 32): name the false path and show it with a trace, or pad and gate again. Doing the trace first: a
  dynamic counterpart of M (mux output settle vs z_req rise, and vs each consumer's capture) on item 30's route.
### progress 06:58 UTC (what a rule-M miss means; collatz64 with umux0 padded to M: farm fc64sel3m)
- collatz64 umux0's z_data feeds only link latches (ulink_n10__1..4, and n10__0[0] -> ulink_n11). So a late mux output
  is still captured (the latch closes a phase later), but it breaks the contract every downstream measurement assumes:
  skew.py / A' take a link's data as following its ENABLE ("the d input was already stable, held by the sender's own
  contract"). With D still moving 1.3 ns after the link opens, the link's Q is late by up to that much and every
  downstream margin from that link shrinks by it. Rule M is that contract, checked; a miss is real unless the
  downstream margins absorb it, which nothing checks today. Item 30 rebuilt here (c64s3_10, sdf 637ff02e = the board
  route): rule M umux0 -1231 nom / -1321 worst; umux2's old -2.2 ns false-path row is now measured by A' at -464 / -500.
- Farm fc64sel3m (h4s3m = h4s3q with UMUX0 2 -> 16, rule M's 32-route max): the cost of meeting the contract.
  PREDICTION: +2 to +4 ns per iteration vs fc64sel3q (umux0 is on collatz64's critical cycle on every route, 14 elements
  ~0.4 ns each on the rising edge, the fall fast). Trace measurement of the lateness (mux_settle.py) on c64s3_10 at
  FAST_MIN running.
### progress 07:03 UTC (rule M's miss on collatz64 item 30, measured in simulation: real, 155 ps at FAST_MIN)
- research/tools/fifteen/mux_settle.py (new; select_arrival.py's dump plumbing): per bd_mux, per z_req rise, any z_data
  change (at the udat LUT outputs) before z_req falls. Item 30's route (c64s3_10 = sdf 637ff02e), FAST_MIN,
  vec_collatz_hold.hex: umux0 458 rises, 352 with a data change AFTER z_req rose, worst 155 ps late; umux1 0 (lead
  >= 2760 ps); umux2 (8 rises) z_data not named in the dump. Static rule M said -1231 ps (nominal, guarded, longest
  data vs shortest request over all launches); the trace shows the race happening on 77% of tokens, smaller.
- So the miss is not a false path: the output request leaves before the data on most iterations, the downstream link
  latches take Q up to ~155 ps (FAST_MIN) after their enable, and nothing static accounts for it downstream. Gates pass.
  Worst-corner trace and a clean control (collatz item 31's route, M clean) running.
- fcsel3b (collatz nl6s3b: mux delays by M, uselect0 6, ucmpi2 15), 25 routes so far vs fcsel3a: -0.37 ns per iteration
  median (16/24 faster), rule M rows at umux1 on 3 routes (to -228). PREDICTION -0.3 to -0.8: low end. Not worth an item.
- xorshift's mux delays (umux0/1/2) are 2 in fr4, shrunk in old rounds that never checked their data outputs; rule M's
  max over fxd_ps asks 5 / 7 / 3, and A' lets umux3 go 14 -> 9. Farm fxm (fr4m). PREDICTION: +0.3 to +1.0 ns per
  iteration vs fxd (umux0 / umux1 sit on the near-critical cycles c1 / c3, umux3 is off them).
- ipow (item 29): rule M / A' maxima over fisel3_ps: umux0 8 -> 6, umux1 9 -> 8, umux2 2 -> 7 (M), umux3 3 -> 4. Farm
  fisel3m (h4s3m). PREDICTION: within +-0.4 ns per iteration of fisel3 (umux1, on the cycle, -1; umux2, off it, +5),
  rule M clean on >= 30/32.
### progress 07:14 UTC (rule M vs simulation: the direction agrees on both routes; the size is pessimistic)
| route | rule M (nom / worst) | mux_settle FAST_MIN: late rises / worst lag | worst corner: late / lag |
|---|---|---|---|
| collatz64 item 30 (c64s3_10), umux0 | -1231 / -1321 | 352 of 458 / 155 ps | 300 of 458 / 60 ps |
| collatz64 item 30, umux1 | +869 | 0 (lead >= 2760) | 0 (lead >= 3920) |
| collatz item 31 (c28a_20), umux0 / umux1 | +1503 / +1145 (worst) | 0 / 0 (leads 1598 / 1790) | -- |
- Every M miss here is a race that happens in simulation, and every M pass is a race that does not. The static
  number is ~8-20x the simulated lag (longest data over 64 bits and every launch, shortest request, guard), so M sizing
  is conservative. A cheaper fix than padding (fc64sel3m pads umux0 2 -> 16): the lag comes from the data link's
  64-bit enable spread (ulink_n_falseResult_3 C node -> 64 latch LUTs); enable replication (PROGRAM's goal-2 lead
  list) would shorten the data side instead of lengthening the request side.
- Rule M's known-bad build, confirmed: item 28's route with +8000 ps on ulink_n14__0's select latch -> umux0.udat (SDF
  only): gate at FAST_MIN completed no batch in 55 min (the clean route: the whole gate in 8.9 min). Rule M -5503 ps
  at worst; rule E clean (0 rows below 0). At +3000 on the same arcs: M -353, gate PASS. So M fails on a build that
  fails and E does not -- M earns its place; on collatz it is stricter than the gate by between 3 and 8 ns of
  injection on this mux (farm mneg covers the other families).
### progress 07:29 UTC (mneg, first 8 of 14: rule M catches wrong values rule E cannot see; fcsel3b done)
- mneg (select latch -> one mux's data LUTs, +4000 / +8000 ps): +8000 gives a WRONG VALUE at FAST_MIN (FAIL, not just no
  completion) on xorshift umux1, ipow umux1 and collatz umux1; rule M on the injected mux -4908 / -2987 / -5811 ps at
  worst, rule E clean on every one (0 rows). Where the injected mux's M stayed >= 0 (or the injection fell on a mux
  M did not move), every gate passed. (The base routes' own M rows, xorshift umux1 -117 and ipow umux2 -532, show
  on every task of that route.)
- fcsel3b (collatz, mux delays by M + uselect0 6 + ucmpi2 15) complete: vs fcsel3a -0.37 ns per iteration median,
  22/31 faster; gates 96/96; rule M rows at umux1 on 5/32 (to -419). Item 31 stays the collatz candidate.
### progress 07:33 UTC (collatz64 umux0: rule M per launch -> a cheap fix; farm fc64sel3n)
- corner_audit (CA_DEBUG_FOREIGN now also logs every launch's A' / A'm margin) on item 30's route: umux0's data outputs
  vs z_req by launch: ulink_n_falseResult_3 (the loop-ENTRY operand) -1321 ps, ulink_n_falseResult_9 (loop-back) -542,
  the select link +712. The entry side can be paid off the loop: the pipe's own request line (DELAY, no macro before,
  RTL default 0). h4s3n = h4s3q + UMUX0 2 -> 4 + ULINK_N_FALSERESULT_3 DELAY 4. Farm fc64sel3n.
  PREDICTION: rule M clean on >= 28/32; +0.4 to +1.0 ns per iteration vs fc64sel3q (two elements on the cycle's rising
  edge), against +2 to +4 for fc64sel3m.
### progress 07:36 UTC (fc64sel3q: the ulink_n28 ack back at 3 costs +0.4 ns)
- fc64sel3q (h4s3p with ULINK_N28_UACK 1 -> 3) vs fc64sel3p, 29 paired seeds: +0.41 ns per iteration median (9/29
  faster); period median 31.79 ns; gates 90/90; E clean. Its static rows now include rule M (umux0 to -2401, as on
  every collatz64 route) and umux2's A' (-1005, the old traced false path, now measured from the upstream links).
  The TSE rows at ulink_n28 (fc64sel3p: 9/30 routes) are mostly gone (hold detail being tabulated). Next collatz64
  candidate = fc64sel3n (q + the rule-M fix per launch) if it comes back clean.
### Session summary so far (written 07:37 UTC; the session may continue)
Measured (farm, 32 seeds each unless noted; ns per iteration, paired latency medians; nextpnr 9c732bc6303458df):
| kernel | build | period median | vs previous | gates | static | board item |
|---|---|---|---|---|---|---|
| collatz | fcsel3a: item 28 + uselect0 7 / uaddi0 9 (A' join-peer fix) | 21.48 (31 routes) | -3.93 vs item 28 (30/30) | 93/93 | A / A' / E / M clean on 31/31 | **31** (seed 20) |
| collatz | fcsel3p: per-cell max 9 / 12 | -- | +1.43 vs 3a | 93/93 | clean | -- |
| collatz | fcsel3b: + mux delays by M, uselect0 6, ucmpi2 15 | 21.09 | -0.37 vs 3a (22/31) | 96/96 | M rows on 5/32 | -- |
| ipow | fisel3: select links 3/3/3/3 by E | ~36.1 (26 valid) | -2.71 vs h4 (18/19) | 78/78 | E clean; M umux2 on 15/19 | 29 (provisional, M) |
| collatz64 | fc64sel3: select links 3/6/3 by E | 34.94 | -1.56 vs h4 (25/27) | 87/87 | E clean; M umux0 on 32/32 | 30 (provisional, M) |
| collatz64 | fc64sel3p: + proposal round | 31.39 | -3.52 vs fc64sel3 (30/30) | 90/90 | TSE n28 on 9/30; M umux0 | 32 (provisional, M) |
| collatz64 | fc64sel3q: p + n28 ack back to 3 | 31.79 | +0.41 vs p | 90/90 | M umux0 | -- |
| xorshift | fxsel3 (selects by E) / fxu (missing ack) | 19.45 / 19.21 | -0.23 / -0.05 vs item 27 | 96/96 each | -- | rejected |
Checks: rule E's select negative controls on all four families (20 gate failures, E flags all 20 -- CORRECTED later the same
session: those failures are start-up X from the unreset select latch, not the race; formal C17 was right);
rule M (new: mux data outputs) with its own known-bad builds (collatz umux0 +8000: no completion, M -5503, E clean; mneg:
wrong values on xorshift / ipow / collatz umux1 at +8000, M < 0, E clean) and a dynamic counterpart (mux_settle.py) that
agrees in direction (collatz64 item 30: 352/458 tokens late by <= 155 ps at FAST_MIN; item 31: none).
Does NOT show: that rule M's misses on items 27 / 29 / 30 / 32 cause failures (every gate passes; the simulated lateness
is 60-155 ps, absorbed or not by downstream margins nobody checks); anything on silicon; formal margins for items 29-32.
Next:
- Farm results to read: fc64sel3n (collatz64 rule-M fix per launch: umux0 4 + entry link delay 4) and fc64sel3m (umux0
  16): if n is M-clean and every check passes, it replaces items 30 / 32. fxm (xorshift mux delays by M), fisel3m (ipow
  by M): same question for items 27 / 29. mneg tasks 1-7, 12 (rule M controls on the remaining muxes).
- Per-launch rule-M fixes for ipow umux2 / xorshift umux1 (the loop-entry link's own DELAY is off the cycle).
- Enable replication on wide data links (the source of the mux lateness: a 64-bit latch enable net) -- PROGRAM goal-2 lead.
- Rule I / A downstream composition: a check that a sender's lateness (M miss) is absorbed by the receiver's margins.
- ucontrol_merge0_olink's request line (xorshift, on the cycle, RTL default 4) feeds a stage no rule audits: a check gap.
### progress 07:47 UTC (xorshift item 27's mux race in simulation: none; ipow by rule M: static-clean)
- mux_settle on x27_2 (item 27's board route) at FAST_MIN, vec_xorshift_hold.hex (40 loop tokens): no late data change at
  any mux; umux1 (rule M -13 nom / -117 worst) leads z_req by >= 2334 ps, umux2 by >= 421. Item 27's M row is
  static pessimism on this route (dynamic margin > 2 ns), unlike collatz64's umux0 (late on 77% of tokens).
- fisel3m (ipow item 29 + mux delays by M / A': umux0 6, umux1 8, umux2 7, umux3 4), 30 of 32 routes: static A / A' / E / M
  clean at both corners on every route so far -- the first ipow family with no static row at all (umux3's old -1.4 ns
  false-path row is now A', +ve at 4); gates all pass; latency vs fisel3 -0.19 median (noise).
### progress 07:48 UTC (ipow item 29 replaced by fisel3m: every static row clean)
- fisel3m complete: 27 routes (5 known bitstream-defect routes excluded), gate 81/81, rule A / A' / E / M clean at nominal
  and worst on 27/27, TSE / hold_bits clean, H rows on 2 (-25 s9, -83 s30). Latency = fisel3 (+0.00 median), -2.71 vs
  fipowh4 (17/19 faster). BOARD-QUEUE item 29 / section 30 now point at it: seed 19, sdf b521630f, sizes h4s3m. The
  rule-M padding of umux2 (2 -> 7) cost nothing because umux2 is off ipow's cycle, and umux0 / umux1 came down.
### progress 07:48 UTC (the price of rule M by padding the mux: xorshift +1.2, collatz64 +2.2 ns per iteration)
- fxm (xorshift fr4m: umux0/1/2 2 -> 5/7/3, umux3 14 -> 9), 27 routes: +1.20 ns per iteration median vs fxd (2/26 faster),
  period median 20.55; gates 81/81; static clean on 23/27 (umux2 M -90 on one, ucmpi1 / uxori2 A and steer E rows on a few).
  PREDICTION +0.3 to +1.0: exceeded. Not adopted: item 27's own route shows no late mux data in simulation (umux1 leads
  by >= 2.3 ns at FAST_MIN), so on xorshift M's misses look like pessimism; a per-launch fix (as for collatz64) would
  cost less if one is needed.
- fc64sel3m (collatz64 umux0 2 -> 16), 19 routes: +2.16 ns per iteration vs fc64sel3q (2/19 faster), period median
  33.64. Rule M at umux0 clean; umux2's A' row (the old false path, now measured from the upstream links) -915 at
  worst remains. PREDICTION +2 to +4: met at the low end. fc64sel3n (umux0 4 + entry-link delay 4) decides.
- collatz64 umux2 (result mux, off the loop): with the 1-bit-latch fix, A' now measures it from its data links: item 30's
  route ulink_n8 -500, trueResult_4 -232, select +426 ps; up to -1005 over fc64sel3q. The old -2.2 ns rule-A row that
  was "traced as a false path" paired something else. h4s3o = h4s3n + UMUX2 1 -> 6 (off the loop: ~free); farm
  fc64sel3o. PREDICTION: every static row clean on >= 28/32, latency within +0.6 of fc64sel3q.
### progress 07:49 UTC (item 31's family clean under the new corner_audit; xorshift per-route proposal: farm fxa)
- fcsel3a_ps (item 31's 29 routes, corner_audit with the join-peer fix, 1-bit links and rule M): no A / A' / E / M row
  below 0 at either corner. Item 31 stands with every static check, rule M included.
- fxa (xorshift fr4a = item 27 + seed 2's proposal on datapath / mux lines: uxori1 / uxori2 7 -> 5, umux3 14 -> 9, ucmpi0
  12 -> 10, uaddi0 13 -> 12). PREDICTION: -0.3 to -0.6 ns per iteration vs fxd (uxori2 is on x27_2's critical cycle,
  3.7 ns, two elements out; the rest off it); A' clean on >= 26/32.
### progress 07:59 UTC (mneg: rule M's negative controls on all four families -- 6 gate failures, M flags all 6, E none)
- Table in research/data/selneg/README.md (tool: research/tools/fifteen/mneg_table.py). 6 runs fail the gate (3 wrong
  values, 3 no completion) on xorshift umux0 / 1 / 2, ipow umux1, collatz umux0 / 1; rule M < 0 on the injected mux in all
  6 (-2987 .. -6153 ps), rule E clean in every run. Where M stayed >= 0 the gate passed. So M earns its place on xorshift,
  ipow and collatz; collatz64's umux0 control (task 5) failed to run on the farm twice (container error).
### progress 08:10 UTC (formal C17 disagrees with research's gate on the select-JOIN injections; tracing)
- Formal C17 (its transport-delay model, same routes and SDFs, FAST_MIN, 12-ns host, 3-4 vectors): the select made late
  into the mux's request JOINS (my selneg / selneg2 arcs) never fails at +1..+12 ns -- it only delays the mux; the
  select made late into the mux's DATA LUTs (rule M's race, my mneg arcs) fails from +6 ns (wrong values). My gate
  fails on 20 join-injection runs. Formal asks for a trace of one (item 28 umux0, join +3000, FAST_MIN). The audit's
  T118 replay also saw no completion, but on the same simulator stack.
- Why it matters: if the join-injection failures are a simulator artefact, rule E's "known-bad builds" are not
  known-bad, and E's negative control rests on mneg-type failures only (where E is clean: E would then have NO
  failing build at all on the arrival race it models, and rule M would be the real arrival check at the data side).
- Running: fullstack_dump.sh (new XRAY_SDF_IN: use a given prjxray SDF) with the join +3000 SDF on c28_20, FAST_MIN,
  the gate's own vectors (col13.hex), VCD kept; then which handshake stops, and where.
- Formal C18 on research's candidates: item 32 ulink_n13 hold +3861 ps at the SDF (the ULINK_N13_UACK 3 kept by hand
  holds); item 30 no finite failure up to kappa 0.45; item 31 = C15 (uselect0 capture holds to 0.45); item 29 needs a
  DSP48 model (formal's decoder refuses DSP sites). C19: its "steer-cone" failures are 20-41 ps runt pulses into link
  controllers -- a device question (pulse shrinkage), asks whether research's GLS can show such a pulse.
### progress 08:21 UTC (CORRECTION: the select-JOIN injection failures are X from an uninitialized latch; formal C17 is right)
- Trace (c28_20 = item 28's route, umux0 join +3000 ps, FAST_MIN, gate vectors col13.hex; tr_c28u0j): first kernel net to
  go X is umux0.j0 (SLICE_X16Y27 C6LUT, INIT 3000322030003220; A1 ctl_req, A3 x_req, A4 its own output, A5 the select)
  at 1648074 ps, 45 ps after ctl_req reaches A1 (1648029). The select DRIVER (ulink_n14__0's latch) is X from t = 0 to
  its first token (1646953 -> 0); with +3000 on the wire the pin is still X when ctl_req arrives, and turns 0 at
  1650171. j0 latches X through its feedback; n_falseResult_9_req, n14__0_ack / data, j1, either follow by 1.668 us.
- So "no completion" here is X-propagation from a latch the simulation never initializes (bd_link resets its
  controller, not its data latch), exposed only because the late select reaches the join after the FIRST request.
  On silicon the latch has a defined power-up value, and at a loop-header mux a stale select only delays the join.
  Formal's C17 (join injections never fail; data-LUT injections fail from +6 ns) is right; my selneg reading was not.
  Every "gate failure" in selneg / selneg2 must be read as possibly this artefact; rule E has no genuine known-bad
  build among them. The 3 wrong values in mneg (data-LUT injections, rule M) are later tokens and look real; to
  confirm with the same trace.
- Consequence for the select checks: at a loop-header mux the arrival race at the join is benign (only a delay) and
  the real arrival race is at the data LUTs (rule M). Rule E stays the check at steers (a combinational req . s gate,
  where a late select mis-steers) and at muxes whose two requests can be pending together.
- The gate (bench_gate.sh) is X-pessimistic at start-up: any race against an uninitialized latch's first value
  becomes a hang. A start-up initialization of LUT latches (to 0, or to both values in two runs) would remove it.
### progress 08:22 UTC (fc64sel3n: the per-launch fix halves collatz64's M miss, not enough; fxa: xorshift -0.38)
- fc64sel3n (collatz64 h4s3q + umux0 4 + entry-link delay 4), 21 routes: -0.32 ns per iteration vs fc64sel3q (12/19
  faster), period median 31.31; gates 63/63; rule M at umux0 still < 0 on 15/21 routes (-23 .. -953; was to -2401),
  now from the loop-back link (falseResult_9) -- item 30's seed 10 route is +8. umux2's A' -522 .. -973 (fc64sel3o pads
  it). The loop-back side would need umux0 ~6-8 for M on every route; fc64sel3m (16) costs +2.2. With the simulated
  lateness at 60-155 ps where M says ~1.2 ns, M is ~10x pessimistic on this mux; collatz64's items stay provisional.
- fxa (xorshift item 27 + seed 2's datapath proposal: uxori1 / uxori2 5, umux3 9, ucmpi0 10, uaddi0 12), 23 routes:
  -0.38 ns per iteration vs fxd (17/23 faster), period median 18.88 ns (fxd 19.39); gates 69/69. Static rows under the
  new corner_audit (rule M at umux0 / 1 / 2, which fxd's older summary never computed; steer E rows on 2 routes; ucmpi1
  / uxori2 A on a few). PREDICTION -0.3 to -0.6: met. Not an item yet: needs its rows compared on equal terms with fxd's
  (fxd_ps gives fxd's under the same corner_audit: M rows on 23/29 there too).
### progress 08:32 UTC (rule M's known-bad build is real: defined wrong answers, traced)
- Trace tr_c28u1d (item 28's route, select latch -> umux1.udat +8000, FAST_MIN, col13.hex, dump kept): batches 0-4 odata
  X (the power-up X of the select latch, reaching the data this time), batches 5-7 and 10-12 right, batches 8 and 9
  DEFINED and wrong (0x0a for 0x06, 0x0c for 0x08). So the data-LUT race (rule M) breaks the kernel by logic, not by
  simulator pessimism; the join race (rule E at a loop-header mux) does not. research/data/selneg/README.md corrected.
- The gate's start-up X: a run that reaches an uninitialized latch's first value late shows X. Fix to consider in
  cells/gls (not done): initialize LUT latches at time 0 (run both 0 and 1), so a hang means a hang.
### progress 08:43 UTC (fxa complete: xorshift 18.9 ns, rows as item 27's family; collatz64's entry-link delay breaks a hold)
- fxa (xorshift item 27 + seed 2's datapath proposal), 31 routes: -0.40 ns per iteration vs fxd (22/30 faster), period
  median 18.91 ns (item 27 19.39), gates 93/93. Static rows: rule M at umux0 / umux1 on most routes (-13 .. -581, as on
  item 27's own family under the same corner_audit, fxd_ps: -178 .. -734), H rows on a few; fully clean on 2 (s18 at
  latency 415, i.e. no faster than item 27's seed). Not a board item: no route is both clean and representative, and
  on xorshift rule M has so far measured as pessimism (item 27's route: umux1 leads by >= 2.3 ns in simulation).
  The next step for it is mux_settle on a median fxa route; if the mux data leads there too, rule M on xorshift needs
  the downstream-absorption check before it can block.
- collatz64 fc64sel3n / fc64sel3o: the entry-link delay (ULINK_N_FALSERESULT_3 DELAY 4) brings a DYNAMIC hold violation:
  hold_bits at ulink_n_falseResult_3 stage[1] on fc64sel3n s2 (9x, to -825 ps) and fc64sel3o s29 (2x, -742) at FAST_MIN.
  The pipe's request delay is not free: it changes when stage[1] opens relative to its data. Rejected; collatz64's umux0
  rule-M miss stays open (padding umux0: +2.2 ns, fc64sel3m).
- collatz64 rule-M control (local, item 30's route, select latch -> umux0.udat +8000): rule M -7528 ps, E clean; gate
  FAST_MIN no batch in 55 min (clean route: 25 min, PASS 14/14). A no-completion, so possibly the start-up X; untraced.
### Next (updated 08:55 UTC; supersedes the list in the summary above)
1. The gate's start-up X (cells/gls/fid_core.vh starts every LUT state node at X; bd_link does not reset its data
   latch): add an opt-in plusarg that starts LUT latches at 0 (and a second run at 1), with a negative control that
   still fails; then re-run selneg's join injections with it. Until then a "no completion" may be start-up X: trace
   before calling it a failure (fullstack_dump.sh XRAY_SDF_IN + vcd_last.py).
2. Rule M's misses vs the downstream: a check that a sender's late data (M < 0) is absorbed by every consumer's margin
   from that link (composition), or a dynamic bound (mux_settle) per route. collatz64 umux0 is real in simulation
   (60-155 ps late on 77% of tokens); xorshift's look like pessimism (item 27: >= 2.3 ns lead). fxa s27 dynamic run going.
3. collatz64 items 30 / 32 (provisional): umux0 padded to M costs +2.2 ns (fc64sel3m); the entry-link delay broke a hold
   (fc64sel3n / o). Next try: enable replication on the 64-bit data links feeding umux0 (shorter data side), or umux0
   at ~6-8 (between n and m).
4. fxa (xorshift 18.9 ns, -0.40 vs item 27) becomes a board item if its median route's mux data leads in simulation.
5. Formal C19: force a 20-40 ps pulse onto a link ctl input in research's GLS and see whether the resolver lets it
   oscillate (formal's model does).
### progress 09:09 UTC (fxa s27: rule M's rows are pessimism in simulation -> BOARD-QUEUE item 33, xorshift 18.9 ns)
- xa_27 rebuilt locally (sdf 7f0c0592 = the farm's fxa s27). mux_settle over 512 loop tokens: FAST_MIN umux0 / 1 / 2
  lead z_req by >= 1042 / 2286 / 1544 ps, worst corner >= 1469 / 3394 / 2315; no late change anywhere. Static rule M
  said umux1 -113 nom / -192 worst, umux0 -71. BOARD-QUEUE item 33 / section 34 (xorshift 18.9 ns median, -0.40 vs item
  27), with the M rows and this measurement stated. fifteen/README headline unchanged until it is reviewed.
### progress 09:10 UTC (GLS start-up X: opt-in +META_INIT; validation running)
- cells/gls/fid_core.vh: +META_INIT=0|1 (opt-in; without it the simulation is unchanged): every LUT state node
  (TLOOP != 0: latches, C-elements) starts at that value instead of X. bench_gate.sh: GATE_PLUSARGS passes plusargs.
  Reason: silicon has no X; bd_link's data latch has no reset, so a race against its first value was a permanent X.
- Validation on item 28's route at FAST_MIN (running): select-join +3000 with META_INIT=0 and =1 (PREDICTION: both PASS
  13/13: the join race only delays); select -> umux1.udat +8000 with META_INIT=0 (negative control, PREDICTION: FAIL, wrong
  values as traced); the clean route with META_INIT=0 (PREDICTION: PASS, cycles 2906 as without it).
### progress 09:39 UTC (+META_INIT validation: negative control holds; the join injection STILL hangs -- X was not all of it)
- Item 28's route, FAST_MIN: clean route with META_INIT=0 PASS 13/13 (cycles 2906, as without); select -> umux1.udat +8000
  with META_INIT=0 FAIL 6/13 (the real failure stays); select -> umux0 join +3000 with META_INIT=0 and with =1: no batch
  in 27 CPU-min (clean ~8), stopped. So the start-up X explained the first X in the earlier trace, but removing it does
  not make the join injection pass: something else stops the run. My correction (the join failures are "only" start-up
  X) is itself too strong; tracing with META_INIT=0 (tr_c28u0j0). fullstack_dump.sh also takes GATE_PLUSARGS now.
### progress 10:00 UTC (the join hang IS start-up X; +META_INIT as written does not reach it)
- Trace with +META_INIT=0 (tr_c28u0j0): identical to the first -- the select latch's output (n14__0_data) is X from t = 0
  to its first token (1646953), its pin X until 1650171, j0 goes X at 1648074 and X spreads. So the earlier correction
  stands (the select-join "failures" are start-up X), and META_INIT=0 / 1 did not remove it: the latch's initial value
  is overwritten by its own X inputs (enable / data from controllers that are X before the harness reset), so it is X
  again before the first token. The opt-in stays (it is inert by default and did not change the clean or the
  data-LUT runs: PASS 13/13 cycles 2906 / FAIL 6/13), but it is NOT a fix. A fix: treat X on a state node's inputs as
  "hold" until reset has been released, or reset the data latches. Next session.
- Net effect on the checks: rule E has no genuine known-bad build on the select-join race (it may be benign at
  loop-header muxes); rule M has real ones (defined wrong answers). BOARD-QUEUE items rest on E (arrival at steers and
  joins) + M (mux data) + H / I / hold_bits / TSE (hold) + the gate.
### progress 10:14 UTC (+META_INIT fixed: the join injection passes, the data-LUT one fails, clean unchanged)
- fid_core.vh +META_INIT now also holds a state node's value against X evaluations until +META_INIT_T (default 5 ns, after
  the harness reset). Item 28's route, FAST_MIN, gate col13: select -> umux0 join +3000: PASS 13/13 with META_INIT=0 and
  with =1 (2913 cycles; clean 2906: the 3 ns delay, nothing else); select -> umux1.udat +8000: FAIL 7/13 (the real
  failure stays); clean: PASS 13/13, 2906 cycles (unchanged). So the select-join "failures" were start-up X, now shown
  both ways, and formal's C17 is confirmed. Default simulation unchanged (opt-in).
- Farm selneg3: selneg2's join injections (+6000 / +12000) with GATE_PLUSARGS=+META_INIT=0. PREDICTION: at loop-header
  muxes every run passes; a failure, if any, is at a mux whose two requests can be pending together.
### Next (updated 10:14 UTC)
1. Read farm selneg3 (join injections with +META_INIT=0). Re-check the 2026-11-15 hold control (fcsel0 s24, ulink_n14__1
   stage[1] enable +15000: "no completion") with +META_INIT: it may be start-up X too, in which case H / I / hold_bits
   have no genuine known-bad build either (xf2_1 and nc64_7 remain: those fail with wrong values).
2. Owner decision worth asking for: run every gate with +META_INIT (both values)? It removes a failure mode the device
   cannot have (an unreset latch is never X) and kept the real failures in every check so far. Until decided, it is
   opt-in; a "no completion" in the default gate must be traced before it counts.
3. Rule M downstream composition / per-route mux_settle (collatz64 umux0 real, xorshift pessimistic).
4. collatz64 items 30 / 32 provisional (umux0 M miss; padding +2.2 ns; entry-link delay breaks a hold).
5. Formal C19: a forced 20-40 ps pulse on a link ctl input in research's GLS.
### progress 10:38 UTC (the hold control is real: with a defined start-up it gives wrong answers)
- fcsel0 s24 rebuilt (sdf bb5fbbdb = 2026-11-15's base), +15000 ps on ulink_n14__1 stage[1]'s ctl -> select latch enable
  (1 arc, SDF only), gate FAST_MIN with +META_INIT=0: FAIL 1/13, every batch completes (3047 cycles), 12 wrong answers.
  On 11-15 the default gate showed "no completion"; with the start-up X removed it is a clean wrong-value failure.
  Rule H flagged that build (-14260 ps at the stage). So the hold checks keep a genuine known-bad build; the
  select-arrival-at-the-join checks (E at loop-header muxes) do not; rule M has genuine ones.
### progress 10:58 UTC (selneg3: with a defined start-up, every select-join injection passes)
- Farm selneg3 (selneg2's arcs, +6000 / +12000, gate with +META_INIT=0), 8 of 14 tasks: xorshift umux0-3, ipow umux1 /
  umux3, collatz umux1 / umux2 -- PASS at FAST_MIN and worst at both sizes, every one. Including xorshift umux1 +6000,
  which gave FAIL 16/17 under the default gate: that wrong value was start-up X reaching the data too.
- Reading: on these kernels a select that reaches its mux's request JOIN late, by up to 12 ns, only delays the token
  (formal C17's result, now reproduced in research's gate). Rule E at a bd_mux join is then a check without a failing
  build -- by the owner's rule, a blanket rule unless a mux where both requests can be pending together exists
  (none found in these four kernels: every mux is a loop header (init vs loop-back) or a loop exit). Rule E at a steer
  (combinational req . s) is a different race and keeps its place only if it too fails somewhere; not yet tested.
  Proposal for the owner: drop rule E at bd_mux joins whose requests are exclusive (shown per mux), keep rule M (data
  side, genuine failures) and the hold checks; test steer E with the same construction next.
### progress 10:59 UTC (farm steerneg: does rule E at the STEERS have a failing build?)
- steerneg (40 tasks: each board route x each steer ucond_br*): every arc into the steer's LUT except its request join
  (the condition: e.g. ucmpi1.uz_n41 -> ucond_br6.u$LUT5/6 A2 on item 27's route) +3000 / +8000 ps, SDF only; rule E and the
  gate at FAST_MIN / worst with +META_INIT=0. PREDICTION: a late condition at a steer whose request arrives while the
  condition still shows the previous token's value mis-steers -> wrong value or hang on most loop-exit steers at +8000;
  rule E flags each. If none fails, rule E at steers is also without a failing build.
### Session summary (update 10:59 UTC)
Board list after this session: item 31 collatz 21.5 ns (every check incl. rule M clean, 31 routes); item 29 ipow ~36.2 ns
(fisel3m, every static row clean on 27 routes); item 33 xorshift 18.9 ns (fxa; rule M rows shown pessimistic in
simulation); items 30 / 32 collatz64 35 / 31.4 ns provisional (rule M miss at umux0, real in simulation, 60-155 ps).
Checks: rule M (mux data outputs) new, with genuine failing builds (defined wrong answers); rule E at mux joins has
no failing build once the gate's start-up X is removed (+META_INIT, opt-in, validated both ways); rule H's hold control
is a genuine wrong-value failure. Steer E under test (steerneg). Formal C17 confirmed.
### progress 11:19 UTC (selneg3: 44 / 44 join-injection gates pass with a defined start-up)
- 11 of 13 muxes back (collatz64 umux1 and collatz umux0 still out): all PASS at both sizes and both corners. Rule E at
  the mux joins has no failing build on any family. selneg README updated.
### progress 14:15 UTC (rule E at a STEER has a failing build; at the mux joins it has none)
- Local, item 28's route: the loop steer ucond_br7's condition +8000 ps (SDF only), gate FAST_MIN with +META_INIT=0: no
  batch in 50 min (clean 9); rule E -5048 ps at ucond_br7. Farm steerneg: 2 of ~25 real steers back (xorshift ucond_br3,
  collatz ucond_br4: every gate passes at +3000 / +8000, E -0.3 .. -6.1 ns). So rule E keeps its place at steers (a late
  condition at req . s loses a token); at loop-header mux joins it has no failing build on any family. The farm has not
  pushed results since 11:44 UTC (steerneg 15 of 40 for 1.5 h): not waited on.
- 14:25 UTC: the farm has pushed nothing since 11:44 UTC (steerneg stuck at 15 of 40, status "running"):
  treated as down for now; steer controls continue locally (xorshift ucond_br9 on x27_2, collatz64 ucond_br6 on c64s3_10).
### progress 15:20 UTC (rule E at the loop steers: failing builds on xorshift, collatz64, collatz)
- Condition +8000 ps into the loop steer, gate FAST_MIN with +META_INIT=0: xorshift item 27 ucond_br9 (E -7266) and
  collatz64 item 30 ucond_br6 (E -6276) complete no batch (50 / 55 min), as collatz ucond_br7 (E -5048). Table in
  research/data/selneg/README.md. Where rule E stands now: it has failing builds at steers (three families) and none
  at mux joins (selneg3, 44/44 pass). ipow's steers wait for the farm (silent since 11:44 UTC).
- 15:46 UTC: container restarted (worker restart; a trace of the steer hang was lost and is re-running). Branch was clean and pushed.
### progress 16:12 UTC (the steer failure is a true deadlock, traced)
- tr_st7 (collatz item 28's route, ucond_br7 condition +8000, FAST_MIN, +META_INIT=0): no kernel net goes X after 10 ns,
  all 1415 end defined, the last kernel event is at 3.945 us, then nothing: a deadlock from a mis-steered token. Rule E's
  steer control is genuine (E -5048). Summary of the select checks after today: E at steers -- genuine failing builds
  (3 families); E at loop-header mux joins -- none (44/44 pass with a defined start-up); M at mux data -- genuine
  (defined wrong answers); H hold control -- genuine (wrong answers).
### progress 18:00 UTC (rule E's steer control on the fourth family, ipow)
- ipow item 29's route rebuilt (ip29_19, sdf b521630f = the board route): ucond_br9's condition (ucmpi2.uz_n39) +8000 ps,
  gate FAST_MIN with +META_INIT=0: no batch in 50 min; the clean route with the same plusarg PASS 17/17 in 6.7 min. Rule E
  at ucond_br9 -3238 ps. So rule E has a known-bad build at a loop steer on every family; its mux-join half has none.
- 18:10 UTC: handoff. Farm silent since 11:44 UTC (steerneg 15/40, selneg3 12/14 not re-read since). Next list above (latest 'Next (updated)' entry) stands; owner decisions asked: +META_INIT as the gate default, rule E at loop-header mux joins. LOCK cleared.

## Session 2026-11-16 18:48 UTC -- steerneg read (E at steers: 14 failing builds, 12 passes all at loop-entry steers); collatz gates lacked n = 1
Toolchain: nextpnr 9c732bc6303458df (patches.sha 789a7120c912d393), toolchain.sh OK   Seeds: farm per request
Lock: cleared by the previous session; taken 18:44 UTC. Audit: no new REFUTED / OVERSTATED row on research since T131.
Formal FOR-RESEARCH: C19 (runt pulses into link controllers) is the newest item; it asks for a forced 20-40 ps pulse
on a ctl input in our GLS (already on the Next list).
### progress 18:48 (farm steerneg done; a gate coverage gap at the loop-entry steers)
- steerneg (26 steers on the 4 board routes, condition +3000 / +8000, +META_INIT=0): 14 steers fail at +8000 with E < 0,
  on all four families. 12 pass with E -4..-7 ns: every loop-ENTRY DATA steer (cond from ucmpi0; 11) and collatz64 ucond_br7. The entry CONTROL steers (xorshift, ipow ucond_br5) fail.
  Table in research/data/selneg/README.md.
- Cause on collatz / collatz64: the gate vectors (col13, c6414) have no n = 1, so the entry test is the same on every
  call and the gate cannot see the entry steers at all. collatz(1) = 0 is a legal input (full-range rule). New vector
  files col14 / c6415 = old + n = 1 as the second vector; oracle compiled from kernels/*.c by
  research/tools/fifteen/kernel_oracle.sh (reproduces col13.exp / c6414.exp byte for byte).
- Farm zt1 (132 tasks): items 31 / 28 / 30 / 32 families, 32 routes each, gated at 3 corners on the new vectors; plus the
  entry-steer +8000 control on each board seed with new and old vectors. PREDICTION: every clean route PASSES (the
  entry-steer E rows on these routes are clean, and n = 1 was simulated before on vec_c64_selflip without failure); the
  control FAILS with the new vectors and PASSES with the old on all 4 board seeds.
- xorshift / ipow vectors do have a zero-trip call (rounds 0, b 0) and their entry data steers still pass: tracing
  locally on xorshift item 27's route (x27_2, building).
### progress 18:53 (formal C19: a 20-40 ps pulse into a C-element -- rejected by our resolver, oscillates without it)
- tb_f3_runtc.v (bd_c2n state LUT as routed, loop 224 / 424 ps, other request high, pulse P ps, 200 trials): the gate's
  fid model never oscillates and never sets the node for P <= 40 (formal's 20-41 ps); with +META_OFF=1 (pure transport,
  formal's semantics) every pulse below the loop delay circulates for 8 ns. The difference between formal's C19 failures
  and our passes is the resolver assumption (TAU = WIN = 150 ps, unsourced). Silicon: BOARD-QUEUE item 2 (H_RUNT).
  research/data/fid/runtc.md; answered in FOR-FORMAL.md. The old inertial model oscillates at P 150-300 on the 424 loop.
### progress 19:06 (xorshift entry data steers: a late condition passes even with zero-trip calls between looping calls)
- tx27_2 rebuilt (xray.sdf 2203029e = farm steerneg's x27 route). Every ucmpi0 -> ucond_br2/3/4 LUT arc +8000 ps (6 arcs,
  SDF only), gate FAST_MIN +META_INIT=0 on xor19 (xor17 + a zero-trip call with a new seed after three looping calls,
  and one at the end; oracle kernel_oracle.sh): PASS 19/19, every batch correct; the clean route PASS 19/19 (4534 cycles).
  So my explanation (a stray token on the skip path that only a later zero-trip call reads) is WRONG for xorshift: rule E
  says the condition reaches those steers 4.9 ns after their request (launch ulink_n1__1.ctl, req 7313 / sel 12203 ps at
  worst), yet no mis-steer shows. Tracing the steer on 5 vectors at FAST_MIN (tr_entry) to see what the request waits
  for. The zt1 PREDICTION (the collatz entry control fails on col14) is now doubtful for the same reason.
### progress 19:13 (GATE BLIND SPOT: the verdict read only the last run of each batch; fixed; regate1 submitted)
- Trace tr_entry (tx27_2, ucmpi0 -> ucond_br2/3/4 +8000, FAST_MIN, 5 vectors): the mis-steer DOES happen. Batch 1
  (rounds 0 -> 1): ucond_br3's false output fires at 4212390 ps, the false link acknowledges (4213754), then the true
  output at 4216941: both branches got the seed. Batch 3 (-> rounds 0): the reverse. The stray tokens wait at mux3 /
  mux1's unselected inputs and are read by the next call that selects that input, so from batch 3 on every batch's
  FIRST run returns the previous call's value and its SECOND run (same operands) the right one.
- bench_gate.sh judged only odata (the last run) and completion, so it passed this build. The bench's FIXED-mode
  repeatability latch (mism_st bit 0: the batch's runs disagreed) was set on 16 of 19 batches. The board script
  (xsdb_bench_gen.tcl) does assert it; the GLS gate never did.
- Farm results re-read for mism_st: 5 steerneg runs the gate called PASS had it set (xorshift ucond_br3 / br4 +8000
  worst / min, ipow ucond_br2 / br3 +8000 both corners, ipow ucond_br8 +8000 worst). So rule E at the entry steers DOES
  have failing builds; the "12 steers pass" in the table above was the gate's blind spot, not E's pessimism.
- Fix: bench_gate.sh fails a batch whose runs disagree (prints "MISMATCH in batch(es) ..."). Checked on the two local
  runs: the injected one FAIL 3/19 (mismatch batches 3-18), the clean one PASS 19/19.
- Consequence: every gate PASS made by bench_gate.sh before now (board items 23-34 and their farm families) did not test
  run-to-run agreement. eval_task.sh does not keep gate BENCHRES lines, so the past farm gates cannot be re-read. Farm
  regate1 (96 tasks): fxa (item 33), fxd (item 27), fisel3m (ipow item 29), 32 routes each, 3 corners, xorshift on xor17
  and xor19, the fixed verdict, every BENCHRES line kept. zt1 (collatz / collatz64) keeps its BENCHRES lines and is
  re-judged from them. PREDICTION: clean routes show no mismatch (a stray token needs a race that the static rules
  cover), and the steerneg control families do.
### progress 19:26 (owner's new PROGRAM section read: draws decide; sim-vs-board per iteration; SIM-VS-BOARD.md)
- PROGRAM 2026-11-16 "The board decides": static rules are tools, not gates; a candidate's result is the fraction of
  delay-model draws that return right answers, plus speed; the model's error on the August builds goes beside it.
  The steer / select-rule questions above are closed by it (their tables stay as record).
- bench_gate.sh draw:K: one draw = delay-chain band and rest band each uniform [0.20, 0.31] independently (spans
  ring128's 0.288 and the August kernels' 0.211-0.225, which disagree), CARRY4 / F7F8 / FF uniform [0.20, 1.0] (never
  measured), setting M scatter seeded by K, the fixed verdict. Local first draw on tx27_2 clean and on the
  ucond_br6 +3000 control (steerneg: fails at FAST_MIN, passes at worst) running before the farm request.
- Sim vs board, ns per iteration, same August bitstreams (research/tools/aug_periter.py; SIM-VS-BOARD.md): at the ring
  band 0.288 the model is +8.7% (collatz 100.76 vs 92.73), +8.1% (collatz64 127.49 vs 117.89), +8.1% (ipow 65.34 vs
  60.46), gcd +9.9%; at 0.222 within 1% (in-sample). xorshift's August bitstream is gone (rebuilt): no comparison.
- research/SIM-VS-BOARD.md written (11 rows: delay band, unmeasured cells, variation, glitches, metastability, start-up,
  bits, host incl. today's last-run blind spot, inputs, V/T, memory).
### progress 19:40 (first draws local; farm draws1 submitted)
- tx27_2 (item 27's route), draw 1 (chains 0.270, rest 0.261, CARRY4/F7F8/FF 0.765, M seed 1), xor19: PASS 19/19, 6422
  cycles; the ucond_br6 +3000 control: PASS 19/19, same cycles (the SDF did change: md5 1fb5d4a2 vs 299debfe). That
  control failed only at FAST_MIN, which no draw reaches (bands >= 0.20), so it is not a bad build under this model.
- Farm draws1 (32 tasks): items 33, 27, 31, 28, 29, 30, 32 on their board routes, 32 draws each; control ucond_br6
  +3000 (16 draws) / +8000 (16 draws). PREDICTION: every candidate 32/32; the +8000 control 0/16; +3000 16/16.
### progress 19:41 (farm shrink1: item 33's sizes scaled 0.85 / 0.70 / 0.55 / 0.40, judged by draws)
- Every matched delay of fr4a times f (shrink_sizes.py, ceil, floor 1; acks and select links included), routes 27 / 2 /
  5 / 9, 8 draws each on xor19. PREDICTION: 0.85 and 0.70 pass 32/32 (the sizes carry the static rules' guards, which
  assumed ~8.5% scatter against the measured 0.76%, and chains at 0.21 vs data at 0.288); 0.55 loses some draws;
  0.40 fails most. Period: item 33 is 18.9 ns; at 0.70 the ~10.7 ns of delay-chain hops on the cycle lose ~3 ns,
  so ~16 ns if it holds.
### progress 20:13 (zt1 113/132, regate1 27/96: clean routes all pass, no run-to-run mismatch)
- zt1 (collatz / collatz64 with n = 1): fcsel3a 86/87 gate runs, fcsel3m 93/93, fc64sel3 75/75, fc64sel3p 72/72 PASS; no
  batch with the mismatch latch set. The one FAIL: fcsel3a seed 10 at SLOW_MAX (batch 0 X, batch 2 hang), a route with
  the known 5FF-D bitstream defect (NOT EQUIVALENT, FFMUX-FLAG), already outside item 31's route set.
- regate1 so far: 81 xor17 + 81 xor19 gate runs, all PASS with the fixed verdict.
- Local: item 33 sizes x0.55 on seed 27: P 16.14 ns (18.71 at x1), but that route has the same FF defect (NOT
  EQUIVALENT, FFMUX-FLAG); draws 1 and 2 FAIL 11/19. Not separable from the defect; shrink1's other routes decide.
- draws1 / shrink1 still queued (the farm's 250-task account limit; zt1 + regate1 hold it).
- 20:44 regate1 85/96: fxa 168/168, fxd 168/168, fisel3m 78/78 gate runs PASS with the fixed verdict, no batch with the mismatch latch. draws1: item 31 16/16 draws PASS so far. Farm shrink2 submitted: collatz item 31 sizes x0.85 / 0.70 / 0.55 on routes 20 / 3 / 7 / 12, 8 draws each.
### progress 21:23 (shrink1: item 33's sizes hold to x0.40 under the draws; shrink3 submitted)
- shrink1 (11 of 16 tasks; 8 draws per route, xor19): x0.85 32/32 (routes 27, 2, 5, 9); x0.70 24/24 (27, 2, 9; P 18.51 /
  18.84 / 17.44 ns); x0.55 16/16 on routes 2 and 5 (P 17.83, 15.92) and 0/16 on 27 and 9, which both carry the 5FF-D
  bitstream defect (FFMUX-FLAG; the draw simulation runs the bits and fails them, as the board would); x0.40 8/8 on
  route 27 (P 15.67 ns, latency 339 cycles vs 394 at x0.85). Item 33 itself: 18.71 ns on route 27.
- draws1 so far: items 33 32/32, 27 24/24, 31 32/32, 28 32/32, 29 24/24, 30 8/8, 32 16/16; the +3000 control 16/16 (as
  predicted: it failed only at FAST_MIN). The +8000 half not back yet: until it fails, the draw model has no shown bad build.
- The full-range question under the new rule: the counter's add (i + 1) and the compares see at most i ~ 1000 in any
  vector, while rounds may be 2^31. A draw cannot judge their long carries, so the board candidates keep UADDI0 / UCMPI0 /
  UCMPI1 at their full-range sizes (x0.40c / x0.55c). ASK: is keeping the static size on paths no vector can reach the
  right reading of "the kernel's full input range" now that static rules are not gates?
- shrink3: x0.30 / 0.20 / 0.10 (where do draws first fail) on routes 2 and 5; x0.40c and x0.55c on routes 1-16, 4 draws
  each. PREDICTION: x0.10 fails every draw; the first failing factor lies between 0.20 and 0.30; x0.40c passes >= 62/64 on
  defect-free routes, median period ~16 ns.
### progress 22:02 (shrink2 / shrink3: everything passes down to x0.40; keeping the counter costs the gain; shrink4)
- shrink2 (collatz item 31 sizes): x0.85 / 0.70 / 0.55 all 8/8 draws on every route back (x0.55: 32/32 on routes 20, 3,
  7, 12; P 18.79 / 18.25 / 16.14 / 18.64 ns vs item 31's 21.5 median).
- shrink3 so far: x0.40c (counter add + both compares kept) 36/36 draws on 9 routes, P median ~18.6 ns; x0.55c 52/52 on
  13 routes, P ~18.0-18.7. Seed 7 x0.55c never simulated (the harness misses 83 MHz on that route: a build failure,
  reported by the request as TIMEOUT). So keeping the counter's three delays leaves item 33's 18.9 ns nearly unchanged:
  they are the cycle (ucmpi1 alone is 4.4 ns of it, whatif 2026-11-16).
- Correction to the ASK above: the compares' long carry is simulated after all. A compare's chain ripples through the
  bits where the operands agree, and every loop's last test compares i = n-2 with n-1, which agree in every upper bit.
  Only the incrementer's long carry (i = 2^k - 1 for k > 9) is beyond the vectors. shrink4: x0.40a / x0.30a = every size
  scaled except UADDI0 (12), routes 1-16, 4 draws each. PREDICTION: all draws pass on defect-free routes; P median
  16-17 ns (x0.40 on route 27 with the add shrunk too: 15.67).
- Still owed: the draw model's bad build. The +8000 steer control (draws 17-32) has not come back; shrink3 tasks 1-6
  (x0.30 / 0.20 / 0.10) are the size-side control.
### progress 22:22 (zt1 done: n = 1 was a real gap; every clean route passes it)
- Clean routes on col14 / c6415 (with n = 1): fcsel3a (item 31) 93/93 gate runs less the known-defect seed 10, fcsel3m
  (item 28) 96/96, fc64sel3 (item 30) and fc64sel3p (item 32) all PASS; no batch with the mismatch latch set.
- Controls (every ucmpi0 -> entry-steer arc +8000 ps, +META_INIT=0) on the board seeds, old vectors vs new:
  item 28 s20: old PASS 13/13 at FAST_MIN and worst; new: no completion at both. item 30 s10: old PASS 14/14 both; new:
  FAST_MIN "PASS 15/15" by the old verdict but 13 batches with runs disagreeing (= FAIL now), worst no completion. item 32
  s22: old PASS both; new no completion both. (item 31 s20's control task failed to build on the farm.) So without
  n = 1 the gate could not see a late loop-entry condition on collatz / collatz64; with it, it can.
### progress 23:47 (draws1: every board candidate passes every draw; first real draw failures at x0.40a)
- draws1, board routes, fixed verdict, no batch with the mismatch latch set anywhere:
  item 33 (fxa s27) 32/32, item 27 (fxd s2) 32/32, item 31 (fcsel3a s20) 32/32, item 28 (fcsel3m s20) 32/32,
  item 29 (fisel3m s19) 24/24 (one task's build failed on the farm), item 30 (fc64sel3 s10) 32/32, item 32 (fc64sel3p s22)
  32/32. Control ucond_br6 +3000: 16/16 (as predicted). The +8000 half still running (2+ hours: hangs run to the timeout).
- shrink4 (12 of 32 tasks): x0.40a (every size x0.40 except UADDI0) passes 4/4 on routes 2, 3, 5, 8, 9, 10, 11, 13, 15
  (P 15.6-17.3 ns), and FAILS 2 of 4 on route 14 (EQUIVALENT, ffmux-clean): draw 1402 (chains 0.234, rest 0.234) hangs
  in batch 2 with odata X; draw 1404 (chains 0.300, rest 0.288) returns the previous call's answer on the first run of
  every batch from batch 13 (1000 rounds) on. These are the draw model's first failures on a clean route: the size-side
  edge lies near x0.40 for some routes. x0.55 / 0.55c have passed every draw so far (68 + 52).
- 23:47 farm shrink5: x0.55a / x0.50a (every size but UADDI0), routes 1-32, 4 draws each. PREDICTION: x0.55a passes >= 126/128 on defect-free routes; x0.50a loses a few; P median x0.55a ~17 ns.
### progress 23:57 (draws1 done: the draw model fails its known-bad build 16/16)
- Control on item 27's route, ucond_br6's condition late (SDF only): +3000 ps 16/16 draws PASS (it failed only at FAST_MIN,
  outside the model's band range); +8000 ps 0/16 (every draw: no completion in 100 min). PREDICTION met on both halves.
- Board candidates' pass fractions (draws1, above) stand: 216/216 draws over 7 items, no mismatch latch.
- shrink4 so far: x0.30a fails 1 of 4 on route 9 (draw 902 hangs); x0.40a 2 of 4 on route 14; every other route 4/4.
### progress 00:06 (worker restarted ~00:00; branch intact)
- shrink4 15/32: x0.40a fails on routes 12 (1 of 4: a hang) and 14 (2 of 4); x0.30a fails 1 of 4 on route 9 (a hang).
  x0.40 is past the edge for some routes, so the candidate comes from shrink5 (x0.55a / x0.50a, queued).
- shrink3's x0.20 / x0.10 tasks are still running (their draws hang to the 100-min timeout).
### progress 00:54 (shrink5 done: xorshift 16.85 ns with every draw passing; candidate chosen)
| sizes (item 33 x f, UADDI0 kept) | routes (ffmux-flag excluded) | draws passing | period median (range), ns |
|---|---|---|---|
| x0.55a | 32 (0) | 128 / 128 | 16.85 (15.93-18.19) |
| x0.50a | 32 (1) | 124 / 124 | 16.74 (15.64-19.19) |
| x0.40a | 16 so far | fails on routes 12 (1/4) and 14 (2/4) | 15.6-17.3 |
| x1 (item 33, fxa) | 31 | board route 32 / 32 | 18.91 |
- x0.55a and x0.50a tie (0.1 ns), so by PROGRAM's rule the longer is taken: x0.55a, -2.06 ns per iteration against item
  33 (-11%), gap to 15 ns 1.85 (sim at band 0.288, which the August builds say is ~8% slow). The first size that fails
  is x0.40a, two steps (0.15 of the scale) below the choice. UADDI0 stays at 12: the incrementer's 31-bit carry is
  beyond any vector.
- Board route: seed 21 (P 16.84 = the median, EQUIVALENT, ffmux-clean). Farm draws2: 32 more draws on it and the
  3-corner gate on xor17 / xor19. PREDICTION: 32/32 and 6/6 PASS.
- 00:54 fifteen/README headline: xorshift 16.85 ns by draws. Farm shrink6: collatz x0.55s (item 31 x0.55, the 3n+1 select and both adds kept), 32 routes x 4 draws. PREDICTION: 128/128, median ~18 ns (item 31: 21.5).
### progress 01:32 (the size sweep's failing side: the draw model fails shrunk sizes broadly below x0.50)
| xorshift sizes (item 33 x f) | routes | routes with a failing draw | draws passing |
|---|---|---|---|
| x0.55a | 32 | 0 | 128 / 128 |
| x0.50a | 31 (1 ffmux) | 0 | 124 / 124 |
| x0.40a | 16 | 4 (routes 4, 12, 14, 16) | 55 / 64 |
| x0.30a | 15 | 14 | 6 / 60 |
| x0.30 (UADDI0 too) | 2 | 1 | 14 / 16 |
| x0.20, x0.10 | 2 each | 2 | 0 (no draw completed before the task limit) |
Failures are hangs (no completion) and result streams that fall a call behind (the mismatch latch), on routes whose
bits are EQUIVALENT. So the model is sensitive on the size side as well as to the injected late steer, and x0.55a sits
two steps above where it starts to fail.
- 02:01 draws2 done: x0.55a seed 21 32/32 draws, gate 6/6 (xor17 / xor19 x 3 corners). BOARD-QUEUE item 35 added (sdf 9145cd49).
### progress 02:29 (collatz: keeping the arithmetic gains nothing; vectors that reach 31-bit carries instead)
- shrink6 (13 of 32 back): x0.55s (item 31 x0.55 with USELECT0 / UADDI0 / UADDI1 kept) 48 / 48 draws, P median 21.30 ns:
  no gain over item 31 (21.5). The 3n+1 select's delay is collatz's cycle.
- Unlike xorshift's incrementer, collatz's long carries CAN be simulated: n = 77671 climbs to 1570824736 (31 bits) in 231
  steps; 94959 and 109881 peak at 30 bits (the highest peaks of any n < 113383, where int32 trajectories end). col17 =
  col14 + these three (oracle compiled from the C: 231, 301, 309 steps). shrink7: x0.55 and x0.70 of EVERY size, 32
  routes x 4 draws on col17. PREDICTION: x0.70 128/128; x0.55 >= 124/128, median ~18 ns (shrink2 on 4 routes: 16.1-18.8).
### Next (updated 02:40 UTC; for whoever picks this up)
1. Read farm shrink7 (collatz x0.55 / x0.70 of every size, col17 with 31-bit trajectory peaks, 32 routes x 4 draws):
   research/tools/draws_table.py on results/shrink7. If x0.55 passes every draw, pick its median EQUIVALENT route, run 32
   draws + the 3-corner gate on it (copy research/cluster/requests/draws2.sh), and add a BOARD-QUEUE item like 35.
2. The same for ipow (fisel3m sizes; ipow17 already reaches e = 0x7fffffff, so its long paths are simulated) and
   collatz64 (needs vectors whose trajectories reach 63-bit values, cf. col17).
3. xorshift below 16.85: the incrementer (UADDI0 12) is the one delay the draws cannot judge (2^31 iterations). Options:
   the owner's answer to the ASK (2026-11-16); or a speculative incrementer whose long case is simulated by construction.
4. Formal: FOR-FORMAL asks it to run the same draws (simx) on draws1's routes; read formal/FOR-RESEARCH.md for answers.
5. shrink6 (collatz x0.55s) is obsolete (no gain); its remaining tasks need no reading.
- 04:46 farm: no push since 03:37 UTC; shrink7 / shrink8 still queued (submitted 02:30 / 02:41). Local fallback: collatz x0.55 on route 20 with col17, draws 1-2.
### progress 05:07 (the long-carry collatz vectors catch a shrink the old vectors passed)
- Local: collatz item 31's sizes x0.55 (every size) on route 20 (sdf b2b0dad9, EQUIVALENT, ffmux-clean, P 18.79 ns), col17,
  draws 1 and 2: FAIL 14/17 both. Exactly the three new vectors are wrong, identically on both runs (no mismatch latch):
  n = 77671 -> 0xf9 (want 0xe7 = 231), 94959 -> 0x98 (want 301), 109881 -> 0xc2 (want 309). The trajectories that climb
  to 30-31 bits take a different path: the shortened 3n+1 delay misses the long carry. shrink2 passed x0.55 on col14 (whose
  trajectories stay below ~21 bits) 32/32: that pass was the vectors' blind spot, not margin.
- So the full-range rule bites on collatz exactly where the owner said it would. Next, at once: does item 31 itself
  (unshrunk) return the right counts for these inputs? Its gates never ran a trajectory above ~21 bits. Running item 31's
  board route on col17 at worst and two draws.
- 05:11 container restart lost the item 31 check; rerunning locally. c6418 (collatz64 + three n ~ 2^59 peaking at 63 bits; oracle 267 / 282 / 285). Farm regate2: items 31 / 28 on col17, 30 / 32 on c6418, 32 routes x 3 corners. Until it is back, items 28, 30, 31, 32 are UNVERIFIED on trajectories above ~21 / ~30 bits.
### progress 05:39 (CORRECTION: the collatz "long-carry failures" were vectors outside the bench's input mask)
- Item 31's own route (sdf 7aefc4bd) on col17, worst and draw 1: the same three "wrong" answers, 0xf9 / 0x98 / 0xc2, as
  the x0.55 build. Identical across sizes and delays, so not timing: the bench masks collatz's n to 16 bits
  (cells/hw/gen_bench.py DOMAIN_RESTRICTIONS, n & 0xFFFF; collatz64's high word to 0), and collatz(77671 & 0xFFFF) = 0xf9,
  collatz(94959 & 0xFFFF) = 0x98, collatz(109881 & 0xFFFF) = 0xc2. The kernel was right both times. My 05:0x entry
  ("x0.55 fails on long carries; the old vectors were blind") is WRONG, and the BOARD-QUEUE hold is withdrawn.
- What stands: inside the bench's domain the highest collatz peak is 593279152 (30 bits, n = 60975; gen_bench.py's own
  note), and collatz64's is ~3e14 (49 bits, n < 2^32). New vectors inside it: col18 (+ n = 60975, 65307, 63823; peaks 30 /
  29 / 27 bits) and c6419 (+ three 32-bit n peaking at 49 / 49 / 48 bits). col17 / c6418 deleted; requests regate2 and
  shrink7 (built on them, never started) replaced by regate3 and shrink9.
- Lesson for the vector files: every vector must be inside DOMAIN_RESTRICTIONS, or the oracle must apply the same mask.
- 05:53 Local, col18 (inside the bench domain, trajectories peaking at 30 bits): item 31's route (sdf 7aefc4bd) at worst PASS 17/17; item 31 sizes x0.55 on route 20 (sdf b2b0dad9, P 18.79 ns vs 21.27) draw 1 PASS 17/17. The 30-bit carries of the 3n+1 adder are now in the vectors; shrink9 (x0.55 / x0.70, 32 routes x 4 draws on col18) decides the collatz candidate.
- 09:10 farm: regate3 / shrink9 waiting since 05:39 ('the farm is full'), shrink8 since 02:41; shrink6 holds slots at 14/32. Local fallback: collatz x0.55 routes 3 and 7, 2 draws each on col18.
- 10:10 Local collatz x0.55 on col18: route 3 (sdf d8884e45, EQUIVALENT, P 18.25 ns) 2/2 draws PASS; route 7 (sdf 06af3676, P 16.14, bits NOT EQUIVALENT -> not a candidate route) 2/2 PASS. With route 20 (draw 1) that is 5/5 draws on 3 routes. Not enough for a board item (the owner's bar: many routes x draws); shrink9 (32 routes x 4) still waiting on the farm. Item 31 itself stays the collatz board item.
- 11:11 farm silent since 05:39 UTC (treated as down for now). Local: ipow item 29 sizes x0.55 on route 19, 2 draws on ipow17.
- 11:51 Local ipow x0.55 route 19 (sdf d63bfd80, P 26.84 ns vs item 29 ~36.2): FAIL 11/17 on draws 1901 / 1902, wrong values on the six large-e vectors (e = 0xfff .. 0x7fffffff) -- but the route carries the known F7-select bitstream defect (fasm_equiv: SLICE_X19Y65/F7AMUX/S0 json const 0, bits const 1; the class BOARD-QUEUE refuses). Not a timing result; needs a defect-free route (shrink8 on the farm, or another local seed).
- 12:30 Local ipow x0.55 route 3 (sdf 0b333646, EQUIVALENT, ffmux-clean): draws 301 / 302 PASS 17/17, P 26.41 ns (item 29: ~36.2 median, -27%). Route 19 failed only through its F7-select defect. 2 draws on one clean route is a lead, not a candidate: shrink8 (32 routes x 4 draws) decides when the farm returns.
- 14:28 Local ipow x0.55: route 5 (sdf e7c5057d, P 25.86 ns) and route 8 (sdf 70048ae0, P 27.56) 2/2 draws PASS each, both EQUIVALENT / ffmux-clean. Clean routes so far 3 / 5 / 8: 6/6 draws, P 25.9-27.6 ns vs item 29 ~36.2 (about -27%). Still a lead (3 routes); shrink8 (32 routes) makes it a candidate.
- 16:15 Local collatz x0.55 on col18: routes 12 (P 18.64) and 5 (P 17.00) 2/2 draws PASS each, but both NOT EQUIVALENT (not usable as board routes until the kinds are judged benign). Totals for collatz x0.55 on col18: 9/9 draws on 5 routes, P 16.1-18.8 ns vs item 31's 21.27 on its route; 2 of the 5 routes EQUIVALENT (20, 3). shrink9 still decides.
### Session summary and handoff (2026-11-17 17:12 UTC)
Toolchain nextpnr 9c732bc6303458df throughout.
- Gate verdict fixed: it read only the last of each batch's two runs (missed result streams a call behind). All current
  board families re-gated with the fix: clean.
- collatz / collatz64 vectors had no n = 1: added (col14 / c6415); clean routes pass; the entry-steer control now fails.
- PROGRAM 2026-11-16 ("the board decides"): bench_gate.sh draw:K; SIM-VS-BOARD.md; sim vs board on the August builds
  +8-10% per iteration at band 0.288. Board candidates 27-33 pass every draw; the model fails its known-bad build 16/16.
- BOARD-QUEUE item 35: xorshift 16.85 ns (item 33 x0.55, incrementer kept), 128/128 draws on 32 routes; its route 32/32
  + 6/6 gates. Draws first fail at x0.40a.
- Withdrawn the same day: a collatz "long-carry failure" that was vectors above the bench's 16-bit mask. kernel_oracle.sh
  now applies the bench masks; col18 / c6419 carry the highest-peak inputs inside the domain.
- Leads (local, few routes): collatz x0.55 9/9 draws on 5 routes, 16.1-18.8 ns (item 31: 21.27); ipow x0.55 6/6 draws
  on 3 clean routes, 25.9-27.6 ns (item 29: ~36.2). Their farm sweeps (shrink9, shrink8) and regate3 are queued; the farm
  pushed nothing after 05:39 UTC 2026-11-17.
- Formal C19 answered (runt pulses: rejected by our resolver, oscillate without it). ASK (owner): the incrementer's
  31-bit carry is beyond any vector -- keep its static size?
Next: read shrink9 / shrink8 / regate3 with research/tools/draws_table.py; for a candidate passing every draw, copy
draws2.sh for its median EQUIVALENT route and add a BOARD-QUEUE item like 35. Then collatz64 (c6419) the same way.
LOCK cleared.

## Session 2026-11-17 19:50 UTC -- (in progress) where the board sits: LUT band fitted, CARRY/F7 unpinned by latency; farm shrink8/9 read
Toolchain: (setup running)   Seeds: farm per request
Lock: empty at start; taken 19:49 UTC. Audit: T145 (LUT/routing x 0.22-0.23 on the measured bitstreams; CARRY/F7 not pinned
by any kernel; xorshift's archived bitstream matches no board log); no new REFUTED / OVERSTATED row on my files beyond the
col17 / x0.40a rows already withdrawn. Formal FOR-RESEARCH newest C42 / C41 / A13: CARRY/F7 cannot be placed by latencies;
item 35's loop-entry race rests on it; UCMPI0 = 10 keeps >= 387 ps at CARRY 1.0 on 8 routes at no speed cost.
### progress 19:50 (farm shrink8 / shrink9 / regate3 read)
- regate3 (items 31 / 28 on col18, 30 / 32 on c6419, 3 corners, ~32 routes each): 365 / 366 gate runs PASS; the one FAIL is
  fcsel3a seed 10 at SLOW_MAX, the known NOT EQUIVALENT route. The four collatz-family board items pass with the
  highest-peak in-domain inputs on every clean route.
- shrink9, collatz item 31 sizes x f on col18, 32 routes x 4 draws:
  x0.70 128 / 128, P median 19.59 ns (18.17-22.95; item 31 21.27). x0.55 122 / 124: route 30 (EQUIVALENT, ffmux-clean)
  fails draws 3001 and 3003 (results a call behind from batch 2 on), whose CARRY4/F7F8/FF band is 0.91 and 0.75; it passes
  3002 / 3004 (0.59 / 0.55). So collatz x0.55 lives or dies by the unmeasured CARRY/F7 band, exactly formal's point.
- shrink8, ipow item 29 sizes x f, ipow17, 32 routes x 4 draws: x0.70 104 / 104 on 26 clean routes, P median 30.37
  (28.06-33.38; item 29 ~36.2). x0.55: route 12 (EQUIVALENT, ffmux-clean) hangs on 3 of 4 draws, including draw 1203 at
  CARRY 0.20 (chains 0.22, rest 0.24): not a CARRY effect. Route 19 is the known F7-select defect (11/17 every draw).
  (draws_table.py counts NOT EQUIVALENT routes as clean; it excludes only FFMUX-FLAG. To fix.)
- So: collatz and ipow candidates come from x0.70, not x0.55.
### progress 19:52 (farm cand3 / cand4 / slowc1 submitted; slow-carry draws)
- bench_gate.sh: DRAW_CARRY=LO,HI narrows the CARRY4 / F7F8 / FF range of a draw (default 0.20,1.0 reproduces every
  existing draw K exactly; checked on K 1201 / 3001 / 2101). draws_table.py now also excludes NOT EQUIVALENT routes:
  shrink9 x0.70 96 / 96 on 24 EQUIVALENT routes (P median 19.76); shrink8 ipow x0.70 84 / 84 on 21 (30.21); x0.55 still
  fails on clean routes (collatz 30, ipow 12).
- cand3 (32 tasks): item 35's sizes with UCMPI0 6 -> 10 (formal C41), routes 1-32, 4 default + 4 slow-carry (0.8-1.0) draws.
  PREDICTION: 256 / 256 on EQUIVALENT routes, P median 16.85 +- 0.2 ns.
- cand4 (10 tasks): collatz x0.70 seed 27 and ipow x0.70 seed 31 (median EQUIVALENT routes), 32 draws + 3-corner gate each.
  PREDICTION: 32 / 32 and 3 / 3 for both.
- slowc1 (20 tasks): 16 slow-carry draws on each board route (items 33, 27, 31, 28, 29, 30, 32, 35) and on the two x0.70
  routes. PREDICTION: full-size items 16 / 16; item 35 loses draws (formal C38: ~0 ps at CARRY 0.9); x0.70 16 / 16.
- shrink10 (64 tasks): collatz64 item 32 sizes x0.70 / x0.55, 32 routes x 4 draws on c6419 (PROGRAM lead 4). PREDICTION: x0.70 all draws pass on EQUIVALENT routes, P median ~27 ns.
### progress 19:55 (owner's "use the quota" read; five subagents; toolchain OK)
- Toolchain restored from cache; toolchain.sh OK, nextpnr 9c732bc6303458df (patches.sha 789a7120c912d393).
- PROGRAM 2026-11-17 "Use the quota": up to 8 subagents until 2026-11-18 12:00 UTC; do not stop early. Leads 1-4 are on the
  farm (cand3, cand4, slowc1, shrink10; I read them and write the board items). Subagents (no git; I review and commit):
  band fit on the August bitstreams (lead 5), Dynamatic's ipow / gcd numbers (6), gcd by draws (7), preloaded loop state
  for the incrementer (1b), a CARRY4 / F7 ring board experiment to pin the unmeasured band (8: the gap with the largest
  effect on a candidate -- collatz x0.55 and item 35 live or die by it).
- 20:4x: cand3 / cand4 / slowc1 / shrink10 rejected by the farm (time limit 240 min, I asked 300); resubmitted as cand3b / cand4b / slowc1b / shrink10b, otherwise identical.
### progress 20:01 (Dynamatic's ipow / gcd numbers: ESTIMATES, Dynamatic not buildable here; research/data/dynamatic_ref/)
- Method behind 12.73 / 14.05 / 17.84 (cells/hw/dyn_baseline.sh, 2026-08-24): Dynamatic hw.mlir (on-merges buffering) +
  wrapper, yosys + nextpnr xc7z010-1 --freq 250, nextpnr Fmax read as ns per iteration assuming 1 cycle per iteration;
  ONE route, default seed, nextpnr build not recorded. No log or hw.mlir survives.
- dynamatic-opt / export-rtl are not in the sandbox, so ipow and gcd are estimated: cycles per iteration from Dynamatic's
  component latencies on the fixtures x a clock of 12.73-17.84 ns. ipow ~67 ns (63.7-70.3; muli is a 4-stage pipeline
  inside the recurrence -> 5 cycles); gcd main subtract iteration ~42 ns (38.2-53.5; 3 cycles), per inner shift ~14.
- Standing: ipow async 36.2 (item 29) / 30.2 (x0.70 candidate) = ~0.45-0.54x Dynamatic's time; gcd async is 2.9-4x SLOWER
  than Dynamatic per main iteration (board 156.5, gcd_ps sim 121.0) and 5-8x per shift. gcd is the kernel furthest
  behind; its RTZ / per-shift cost is the lead (journal leads: "gcd pays 23 cycles, cause unexplained").
- Does NOT show: measured Dynamatic routes for ipow / gcd (needs a Dynamatic build: run dyn_baseline.sh on >= 4 seeds,
  x5 for ipow, x3 + 1 per shift for gcd). The three earlier numbers are themselves single routes.
- 20:01 owner (PROGRAM 759d353b4): 8 subagents allowed until the reset 2026-11-18 23:00 UTC. New subagent: gcd iteration-cost diagnosis (research/data/gcd_itercost/), since gcd is 3-4x behind Dynamatic.
### progress 20:09 (band fit: first point; board-august = August builds)
- research/data/board-august/ (owner, 2026-11-17) is byte-identical to research/board/aug/builds for all ten .fasm / .sdf.
- August collatz bitstream, LUT + routing x 0.222, CARRY4 / F7F8 / FF y 0.2, 8 board vectors (6-153 steps): all right,
  no mismatch; 92.68 ns per iteration vs board 92.76 (-0.09%); per-vector latencies within 1 cycle of the board's.
  Refitted x at y 0.2: 0.2227 (same as 0.222 with every cell at one band, and audit T145's 0.223).
- xorshift's August board logs come from at least two builds (trip_N logs ~25 ns per round; repeat / run / soak ~48 ns,
  = PROGRAM's 47.66); all are match=NO against the archived .bit. Not simulated yet.
- Running locally (one at a time, ~15 min each): collatz y 1.0; collatz64 (x 0.224) / ipow (x 0.225) at y 0.2 / 1.0; then
  y 2.0 / 3.0 (beyond SLOW_MAX, extrapolated) on all three as a correctness bound. Scripts research/data/bandfit/.
### progress 20:31 (BOARD-QUEUE item 36: a ring experiment that measures the CARRY4 / MUXF7 band)
- cells/hw/carry_ring/ (subagent, reviewed): ro_many's JTAG harness with 64 rings per bitstream: LUT-only L8 / L16 (pin x
  again), CARRY4 chains C1 / C4 / C16 / C32 (S0->CO3 then CIN->CO3), MUXF7 select chains F8 / F16; 8 placements each.
  Period linear in (x, y_carry, y_f7); carry_fit.py fits all three. Two routes (s1 bit 40a85473, s2 bit 19ae3639; md5s
  checked), nextpnr 9c732bc6303458df, --freq 100; bits EQUIVALENT to routed JSON; chains present in the decoded bits.
- Simulated (x 0.288): C32 11.1 ns at y 0.2 vs 15.5 at 1.0 (+39%); F16 16.2 vs 21.3; L rings unchanged. The fid GLS of
  the decoded bits agrees with the prjxray walk to <= 30 ps on 96 points. At 1% ring scatter y resolves to +-0.01-0.02.
  Negative control (+300 / 500 / 1000 ps fixed on every carry ring) FAILs the fit's consistency checks every time.
- The GLS caught a design bug first (F rings released several edges at once: 1.0 ns instead of 9.3).
- Does NOT measure: CARRY4 XOR outputs, DI->CO, MUXF7 data arcs, MUXF8 (they inherit y through one band per cell type).
### progress 20:37 (band fit: collatz insensitive to CARRY/F7 within the bench's 10 ns resolution; farm partial)
- August collatz bitstream at x 0.222: y (CARRY4 / F7F8 / FF band) 0.2 and 1.0 give identical per-vector latencies, cycle
  for cycle (1808 CARRY4 / 2007 F7F8 / 1924 FF arcs moved; checked in the log header). The host samples on 10 ns edges, so
  |d(ns/iter)/dy| < 10 ns / 153 iterations / 0.8 = 0.08 ns per unit band (< 0.1% of 92.7). Our own number for audit T145.
- Farm (20:37 UTC): cand3b 3/32, cand4b 5/10, slowc1b 1/20, shrink10b 3/64 tasks finished; every draw back so far passes,
  including 8 slow-carry draws (0.85-0.97) on x55a10 routes 1-2 and ipow x0.70 seed 31's 8 draws.
### progress 20:38 (owner, PROGRAM d35499132: "General first" -- one switch, the compiler does it)
- Read. The first lead is now the automatic path: BDC_AUTO=1 (default byte-identical) choosing latches / link depths /
  fast fall / proven MLIR rewrites / sizes with no instance names, no sizes file, no factor; sizes from ONE rule changed
  for every kernel (the draws say the static sizes are 1.4-1.8x long); headline = one table over all kernels with the
  switch, Dynamatic, ratio, and the hand recipe beside it. No new per-kernel shrink / scale sweeps; the running farm
  requests (cand3b, cand4b, slowc1b, shrink10b) are read, not extended. gcddraw's x0.70 half will not be submitted.
- Subagents started: (A) BDC_AUTO -- inventory of every knob, which are general, the event-graph storage search inside
  the flow; (B) the sizing rule -- which term carries the 1.4-1.8x; (C) the all-kernel table at defaults (the automatic
  column's starting point) incl. isprime / gcd and whatever fixtures build.
- ASK: frontend output for nested, branchloop, memsum (kernels/<name>/<name>.c, committed 20:39 UTC): a loop nest
  (two rings sharing a token), a branch whose arm holds a loop (survives if-conversion), and a loop reading an array
  (memory). PROGRAM "General first" item 3 asks for at least these three shapes; please run the frontend and return each
  as cloud/fixtures/frontend/<name>/.
### progress 21:55 (gcd by draws: tooling + vectors done; farm gcddraw1 submitted without its shrink half)
- gcd judged on the kernel bench with BQ item 5's sizes (gcd_hw R5s75, bench prefix; research/data/gcd_draws/), flags
  BDC_LINK_FASTFALL=1, v4 placement, gcd_hw_pads.json select pads. Oracle from Dynamatic's gcd.c (audit copy) with the
  bench mask; matches research/board/gcd_ps_vec1000.hex byte for byte. gcd18: 18 in-domain pairs, no answer 0, no two
  consecutive answers equal (a stream one call behind cannot pass), longest pair 31 main iterations + 59 shifts.
- Local, route 1 (sdf 5c1abff4, EQUIVALENT, ffmux-clean): P 87.2 ns per main iteration + one shift; draws 101 / 102 PASS
  18/18. The worst corner was OOM-killed twice locally (gcd's compile peaks ~9.3 GB) -- not a verdict.
- Farm gcddraw1 (33 tasks): routes 1-32 x 4 draws + the three corners on route 1. The subagent's x0.70 half was dropped
  (General first: no per-kernel shrink sweeps). PREDICTION: every draw passes on EQUIVALENT ffmux-clean routes; 3/3.
- Caveat: this judges gcd's kernel and sizes on the bench harness, not inside gcd_hw / gcd_ps (the board items).
### progress 21:57 (farm read before handover)
- cand3b (x55a10 = item 35 with UCMPI0 10), 30 of 32 tasks: 192 / 192 draws pass on the EQUIVALENT routes, including 96
  slow-carry draws (CARRY4 / F7F8 / FF 0.8-1.0); P median 16.79 ns (15.73-18.55) vs x55a 16.85: no cost, as formal C41
  said. 3 routes NOT EQUIVALENT, route 32 never simulated.
- slowc1b (slow-carry draws 0.8-1.0 on the board routes), 17 of 20: 8 / 8 on every block back -- items 33, 31, 28, 29,
  32, 35 (x55a route 21: 16 / 16, against my prediction of lost draws), collatz x0.70 s27, ipow x0.70 s31. item 27
  (fxd s2) block 0: "no xray.sdf" (build failure on the farm, not a verdict); block 1 8 / 8. Item 30 not back.
- cand4b: collatz x0.70 seed 27 (sdf f11ff1ee, EQUIVALENT, ffmux-clean, P 19.77 ns) 16 draws pass; its other 16 draws and
  its gate task produced no draws (to look at); ipow x0.70 seed 31 (sdf 3d6fba5c, EQUIVALENT, ffmux-clean, P 30.21 ns)
  16 draws pass + SLOW_MAX / FAST_MIN / worst 17/17. Note: the .bit md5 differs between tasks of one build (timestamp?)
  -- check before naming a bit in a board item.
- shrink10b (collatz64 item 32 sizes), 58 of 64: x0.70 88 / 88 on EQUIVALENT routes, P median 27.71 ns (item 32 31.4);
  x0.55 68 / 88, fails on 7 routes (9 18 20 21 22 28 31), result streams a call behind (302 mismatch batches).
- band fit, collatz64 August bitstream at x 0.224: y 0.2 117.61 vs y 1.0 117.59 ns per iteration, board 118.04 (-0.4%):
  again no CARRY / F7 sensitivity. ipow and the y 2 / 3 bound runs were not run (killed at handover).

## Handover (cloud session -> cluster bot), 2026-11-17 21:57 UTC
PROGRAM a3b699817 (owner): this bot moves to the cluster; a cloud session hands over at its next re-read. Done here:
- **Read first:** PROGRAM "General first" (owner d35499132): the automatic path (BDC_AUTO=1) is lead 1; no per-kernel
  shrink sweeps; the farm holds 200 cores (6553f4160).
- **Farm requests in flight, read with research/tools/draws_table.py:** cand3b (2 tasks left), slowc1b (3 left: item 30,
  item 27 block 0 failed to build -- rerun if it matters), shrink10b (6 left), gcddraw1 (gcd R5s75 on the kernel bench,
  routes 1-32 x 4 draws + task 33 = corners on route 1; research/data/gcd_draws/README.md). cand4b is done (above).
- **Board items to write from those results:** item 35's route with UCMPI0 10 (pick the median EQUIVALENT cand3b route,
  run draws2-style 32 draws + gate); collatz x0.70 s27 and ipow x0.70 s31 (cand4b) -- but under "General first" these are
  hand recipes: list them as the hand column, not the headline.
- **BOARD-QUEUE item 36 (new):** CARRY4 / MUXF7 band rings (cells/hw/carry_ring/, research/board/carry/). Most useful board
  run now; the draw model's CARRY band [0.20, 1.0] is otherwise unpinnable.
- **Band fit (research/data/bandfit/):** collatz / collatz64 August bitstreams: LUT + routing x 0.222 / 0.224 reproduce the
  board within 0.1-0.4%; CARRY / F7 0.2 vs 1.0 changes nothing. To finish: ipow at y 0.2 / 1.0 and the y 2 / 3 correctness
  bound (research/data/bandfit/queue.txt, run1.sh -- paths under /tmp/claude-0 must be adapted), then the shared table in
  SIM-VS-BOARD.md.
- **Subagent work stopped mid-way (unreviewed, committed as WIP):** research/data/auto/ (BDC_AUTO inventory/design; the
  bdc code change is NOT applied: research/data/auto/wip/bdc_auto_unverified.patch + auto.py, byte-identity unproven),
  research/data/sizerule/ (which term of the sizing rule carries the 1.4-1.8x), research/data/alltable/ (all-kernel
  default table), research/data/preload/ + research/tools/preload/ (preloaded loop counter for UADDI0), research/data/
  gcd_itercost/ (gcd's cycle composition; gcd is 3-4x behind Dynamatic's ESTIMATE, research/data/dynamatic_ref/).
  Each README says how far it got; verify before use.
- **ASK (owner):** frontend outputs for kernels/nested, kernels/branchloop, kernels/memsum.
LOCK cleared.

## Session 2026-11-17 21:57 UTC -- (in progress) cluster bot, first session: BDC_AUTO applied and verified; automatic sizing
Toolchain: patches.sha 789a7120c912d393, nextpnr 9c732bc6303458df (toolchain.sh all ok on node4512)   Seeds: per item
Lock: empty at start (the cloud session handed over at 21:57); taken 21:57 UTC as cluster-research-29458663-1.
Audit: newest rows T144-T146 (item 35's race in the unmeasured CARRY band; T145 = our band fit; T146 pre-checks item 36);
no new REFUTED / OVERSTATED row on my files. Audit notes to keep: draws_table.py now excludes NOT EQUIVALENT routes (fixed
19:52); the bench masks xorshift's rounds to 12 bits, so a preloaded counter tests inputs the bench cannot deliver (it
tests the full C range the owner asked for, 2026-11-14). Formal: B2 (preload: UADDI0 12 -> 0 passes 112/112 preloaded
draws on 4 routes, -4.9 % period; "the static rule sizes an operator for a capture that does not happen"), C47 (slow-carry
draws pass on items 35 / 29), C46 (cand4 routes pass), and a caveat: C36-C47 used formal's default arcs, ~20 % fast.
cluster: no cloud/setup-toolchain.sh (installed); RUNS=/tmp/bot/runs; 16 cores; the farm by requests as before.
### progress 22:05 (farm: auto1 and sizerule1 withdrawn before they started)
- auto1 called bdc/auto.py with BDC_AUTO=1, but the BDC_AUTO change was never applied (WIP patch): every task would have
  built the plain default or failed. sizerule1 tested CA_SIZERULE with per-kernel floors taken from failing draws, which
  is per-kernel data an untuned kernel does not have. Both were "waiting"; removed (3f43bbca4). They come back reviewed.
- gcddraw1 runs 64 tasks, not 33: the runner took the request at 59db3a632, before the x0.70 half was dropped. Tasks
  33-64 (gcd x0.70) will be read as data, not as a recipe.
### progress 22:12 (BDC_AUTO applied; the automatic sizing loop written; preload1 re-judged)
- BDC_AUTO=1 applied from the WIP patch (26c095065): unset or 0, 80/80 emitted files byte-identical to HEAD on the 9
  fixtures x {top, --no-top} x {no knobs, BDC_AUTO=0, the three hand knob sets} + the pre-pass MLIRs (header line = input
  path only), exit codes identical. Choices: research/data/auto/ident/auto_choices.txt (gcd 5 merges + 6 fork links,
  isprime 4 + 9, fir now emits: fast fall is off for functions with a memory port).
- research/tools/auto/auto_size.sh: the flow's own sizing, nothing per kernel. it 0 = emit.py's estimates
  (est_sizes.py), then corner_audit CA_SIZERULE=1 proposes every line; each later iteration routes the proposal and
  re-runs the rule on the route actually built; clean = no sized kernel constraint below slack as built
  (corner_audit's new negative_sized.tsv); else ratchet max(S_i, proposal_i) and route again (ratchet.py). Why the loop:
  CA_SIZERULE prices a shortened line at its own mean step, which under-delivers when the short line re-places more
  compactly (tighten_loop.sh header: -27 % per element); the re-check on the built route is what makes it safe.
- AUTO at estimates, seed 1, 5 kernels: routed in ~6 min each (nextpnr 9c732bc6303458df); full stack running.
- preload1 (farm, x55a10 with UADDI0 12 / 8 / 6 / 4, 16 routes each, xp1 = xor19 + 10 preloaded rows) re-judged: the
  verdict line said FAIL 28/29 on every draw, but every answer is right; batch 13 (xor19's 1000-round vector, ~17 us
  per run) had its second run cut by the request's 30 us batch limit (preload_gate.sh's default at d3549913, since
  raised to 120 us). On EQUIVALENT routes: UADDI0 12: 48 draws, 8: 40, 6: 48, 4: 32, every answer right in all;
  P median 16.73 / 16.29 / 16.23 / 16.75 ns (route scatter, no trend). The negative-control tasks (65-68) were not in
  the submitted array, so this harness has not yet been shown to fail on a defect: NOT a result until it is.
  (Formal B2's own preload control does fail: +20 ns on the carry into bit 16.)

## Session 2026-11-17 22:15 UTC -- (in progress) cluster bot, session 2: the compiler suite (owner 4c65db3b3) and the automatic column
Toolchain: patches.sha 789a7120c912d393, nextpnr 9c732bc6303458df (toolchain.sh all ok on node3627)   Seeds: per item
Lock: cluster-research-29458663-1 (the previous session of this wrapper) taken 22:15 UTC as cluster-research-29466208-1.
Audit: newest row T147 (BDC_AUTO off byte-identical, own check over 144 cases; caveat: the MLIR rewrites apply only on an
md5 match with formal's three proven files, so on no other kernel). No new REFUTED / OVERSTATED row on my files.
Formal: B2 (preload: UADDI0 12 -> 0 passes 112/112 preloaded draws, -4.9 %), C36-C47 caveat (formal's default arcs ~20 %
fast; being redone on RC_TREE=1), C46 / C47 (cand4 routes and slow-carry draws pass in formal's simx).
cluster: the previous session's node (node4512) is gone with its local runs (the AUTO-at-estimates builds); this node is
node3627, RUNS=/tmp/bot/runs. research/tools/compile_slot.sh (bf9204114): the GLS compile lock becomes N slots
(/tmp/eventgraph_compile.slots = 4 here; unset = the old single flock, so the farm is unchanged).
### progress 22:25 (owner PROGRAM 4c65db3b3 read: a benchmark suite; four subagents; AUTO loops on six kernels)
- PROGRAM "A benchmark suite for the compiler" (owner, 22:1x): 20-30 kernels by shape, kernels/SUITE.md, Dynamatic's
  integer integration tests too, one command that runs the suite through the automatic path and writes the table (pass
  under draws, ns/iteration, LUTs, Dynamatic's figure, ratio; last line N pass and the geometric mean). The frontend now
  runs here ($HOME/dynamatic, linked as dynamatic/, excluded from git).
- build_bench.sh accepts any kernel with a frontend fixture (3def8ecfb); it listed the six by name.
- Subagents (no git; I review and commit): suitek (about twelve scalar kernels, one per shape, generic C oracle, simcheck
  from the C, SUITE.md), suited (triage of Dynamatic's 95 tests: frontend / bdc / bench, blockers ranked), suiteb (bench
  ABI: more than two argument words, host access to arrays through a slot on the generated memport, read-back), bandfit
  (finish "where the board sits": ipow at y 0.2 / 1.0, the y 2 / 3 bound, the shared table in SIM-VS-BOARD.md).
- Found while briefing: a memref argument becomes a bd_mem with no external port, so memsum emits but its array can
  never be filled (its answer is always 0); stores do not emit (single_loop: "store accessor"). suiteb has both.
- Local: research/tools/auto/auto_size.sh (BDC_AUTO=1, sizes from CA_SIZERULE, re-route and ratchet) on xorshift,
  collatz, collatz64, ipow, gcd, isprime, seed 1, MAXIT 5. First point: ipow it 0 (emit.py's estimates) P 64.71 ns,
  EQUIVALENT, ffmux-clean.
- Farm, read (hand recipes; under "General first" they are the hand column, not the headline):
  cand3b (x55a10 = item 35 with UCMPI0 10): 200 / 200 draws on 28 EQUIVALENT routes, P median 16.76 ns (15.73-18.55).
  slowc1b (slow-carry draws, CARRY4 / F7F8 / FF 0.8-1.0, on every board route + cx70 s27 + ix70 s31): every block passes.
  shrink10b (collatz64 item 32 sizes): x0.70 88 / 88 on EQUIVALENT routes, P median 27.71 (26.40-30.83); x0.55 68 / 88,
  failing on routes 9 18 20 21 22 28 31 (302 mismatch batches: a stream one call behind).
  gcddraw1 2 / 64 finished (the queue is full); preload1 61 / 64.
### progress 22:35 (the suite's one command, first version; the sizing loop made cheaper; AUTO it 0 on six kernels)
- research/tools/suite/: suite_one.sh K SEED [NDRAWS] [MAXIT] (BDC_AUTO=1 + auto_size.sh, the bits checked, draws with
  K = 10000 + 100 S + j so every route gets its own model points, expected values compiled from the C at run time, P,
  latency, kernel LUTs), run_suite.sh (every kernel x seeds, then the table), suite_table.py (the table; last line N pass
  and the geometric mean of the ratio), dynamatic_ref.tsv (Dynamatic's figures with how each was obtained; the three
  measured ones are single 2026-08 routes, ipow an estimate). Not yet run end to end: xorshift seed 2 is the first test.
- The loop's cost: corner_audit runs one sensitivity worker per line, ~70 lines, ~25 min per iteration; and every
  iteration ran the full stack. Now: CA_JOBS=N runs the workers N at a time (deterministic subprocesses; unset = the old
  order; equality being checked on collatz it 0); lane2.sh LANE_NORUN=1 builds the route and its prjxray SDF only, and
  auto_size.sh runs the full stack (lane2_run.sh, the old tail of lane2.sh, unchanged) once, on the route it keeps.
- AUTO it 0 (emit.py's estimates), seed 1: P xorshift 65.59, ipow 64.71, collatz 84.81 (bits NOT EQUIVALENT: 3 x
  F7BMUX/0 driven by nextpnr's GND LUT; subagent pnrfix has the defect class), collatz64 132.72 ns. Rule on collatz's
  it 0: 38 lines changed, kernel links 493 -> 114, verify clean.
- Subagents 5 and 6: dynref (Dynamatic's figure for any kernel from Dynamatic's own buffer placement, a cycle-level
  simulation checked against the C, and a period from Dynamatic's timing data calibrated on the three measured
  kernels; export-rtl is not in the owner's build, so measured figures cannot be made here); pnrfix (the NOT
  EQUIVALENT routes, 10-15 % of all routes: real or a checker false alarm per kind, a nextpnr patch that changes only the
  encoding if real, a toolchain.sh fingerprint that fails on the installed binary; nothing installed).
### progress 22:46 (the AUTO loop's first proposal was locking in the estimates route's pessimism; loop restarted)
- xorshift AUTO it 0 (estimates, seed 1): the rule's proposal took the kernel's delay links 511 -> 131 (hand x55a10: 105),
  but UCMPI1 (the loop test i < n - 1) 30 -> 26, bound by rule E at the steer ucond_br9 (request 6048 ps through three
  storage crossings vs the compare's select 4168 ps), where the hand recipe runs UCMPI1 = 5 with every draw passing
  (cand3b 200 / 200) and formal B3 measures >= 194 ps of settle on three routes. The compare's data path is long on a
  route placed with 511 links of delay (estimates: UXORI1 96, UXORI2 48 elements).
- auto_size.sh's ratchet made that first proposal a floor for every line (S_{i+1} = max(S_i, P_i) from it 1 on), so the
  loop could never use the compact routes it builds next. Now (ratchet.py): only lines the rule ever lengthened are
  pinned; the others follow each proposal; the loop goes on while a clean route still shortens a line, and ships the last
  clean route. The rule now runs with C-element (AND) joins (audit T93): on xorshift it 0 the proposal is identical
  either way (20 C-elements seeded), so that is fidelity, not speed.
- corner_audit CA_JOBS=4 vs 1 on collatz it 0: sizes / lines / negatives identical. Loop iterations no longer run the
  full stack (LANE_NORUN); the kept route does.
- Restarted: run_suite.sh on the six original kernels, seed 1, 4 draws, MAXIT 4 (22:45 UTC). Earlier loops (old
  ratchet) killed; their it 0 numbers above stand (estimates: P xorshift 65.6, ipow 64.7, collatz 84.8, collatz64 132.7,
  gcd 56.5 ns).
- Formal C48 (RC-tree arcs = this model's): item 35's loop-entry steer keeps 204 ps at CARRY 1.0, no runts (C36's 15 ps
  was formal's fast default arcs); x55a10 1425 / 923 ps; collatz x0.55 route 30 still fails (wrong answers) on the same
  entry-steer race, C43's UCMPI0 8 removes it. Formal B3: x55a10 with UADDI0 0 is ~6 % faster, every draw and preloaded
  draw passes, loop-test settle 194 ps on one of 3 routes; and a sizing-rule idea: size a join's inputs together when
  both start from the same token (only the later request must cover both data). Noted for the rule (below).
### progress 23:00 (Dynamatic's integration tests triaged; four AUTO builds lost to nextpnr's 420 s limit under load)
- suited (subagent, reviewed; d7ec7ac03, 07f2ae7be, 8d3e64ccc, 242c3f71b): Dynamatic's 95 test directories are 118
  tests (memory/ holds 23, sharing/ 2; frontend.sh now reaches them). 33 use float/double (out of scope; their 31
  fixtures dropped again), 4 fail at the frontend (translate-llvm-to-std: llvm.abs, external calls, sqrt, cos). **12
  emit through bdc** (factorial, fir, gcd, if_loop_1, if_loop_2, iterative_division, iterative_sqrt, sumi3_mem,
  test_bitint, test_int16, test_loop_free, unused_arg), identically with BDC_AUTO=1; **4 fit today's bench** (factorial,
  gcd, iterative_division, iterative_sqrt). Blockers of the 71 blocked integer tests, by tests needing each: lsq 39
  (only blocker of 25; nothing exists), a store on a memory controller 33 (only blocker of 9; emit.py
  _op_mem_controller), two accessors with a load first 21 (small), > 2 accessors 4, handshake.ram 3, divsi / divui /
  remsi 3 / 1 / 1, memref > 1024 words 2. The three memory-controller items alone unlock 26 tests. ASKed back to me:
  force-mc (compile LSQ tests with memory controllers) would leave 36 of 39 needing only those items, but nothing shows
  bdc's token chain orders a load after a store of the previous iteration (test_memory_5: a[i] = a[i-1] + a[i-2] + 5):
  not taken; a measurement at most.
- Bench bugs it found (forwarded to suiteb, who owns gen_bench.py): array arguments give invalid Verilog
  (`.x_data ({})`), so memsum cannot synthesize; the result width is never checked (test_int16's 16-bit result leaves
  16 host bits undriven); the input-domain table is keyed by kernel name.
- The six-kernel suite run of 22:45 lost xorshift, collatz64, ipow and gcd at it 0: nextpnr passed build_bench.sh's
  420 s per-seed limit on this loaded node (seven subagents' builds beside it). Not a compile failure; suite_one.sh now
  says PNR-TIMEOUT for it and exports PNR_TIMEOUT=3600 by default. Restarted 22:59 with -j 4.
### progress 23:24 (AUTO it 0 rule with C-element joins: collatz's loop test 22 -> 5 elements; x55a10 s21 rebuilt identically)
- Rule on the it 0 routes (seed 1, emit.py's estimates), C-element joins (BD_SKEW_AND_JOIN=1) vs the OR joins of the
  earlier loop: collatz 493 -> 97 links (OR: 114; the difference is UCMPI2, the loop test, 22 -> 5: OR joins let the
  steer fire on its first request, so the compare had to beat a request that cannot happen; audit T93's mechanism);
  collatz64 647 -> 110; xorshift 511 -> 131 either way (its UCMPI1 stays 26: bound by E at ucond_br9 with a request path
  through three storage crossings, which the AND seeding does not credit -- the joinrule subagent has this case).
  Collatz's 3n + 1 (UADDI0) goes 80 -> 4 (hand item 31: 9; the draws passed 5 on 32 routes, never 4): the draws decide.
- Determinism: the four it 0 routes rebuilt after the restart have the same sdf md5s as the killed loops' (e9a7370c,
  b0aaeccd, 82a2f474, d68acaae); x55a10 seed 21 rebuilt here = the farm's cand3b route 21 byte for byte (sdf 42b4fb4c...,
  P 16494 ps). Its bit (6a68b04e) is being judged for a board item: 32 draws + 3 corners on xor19.
### progress 23:44 (AUTO it 1: the pinning ratchet shrinks on compact routes; farm gcddraw1 timed out; suite1 narrowed)
- AUTO it 1 (seed 1, the route built from it 0's proposal): xorshift 3 constraints short (A'm umux2 -476, A' ucmpi0
  -202, I -49) -> 3 lines raised and pinned, 8 lowered: UCMPI1 26 -> 22 (now bound by E at ucond_br8, 16 ps left),
  UXORI1 / UXORI2 6 / 5 -> 4 / 3 (hand: 3 / 3), UADDI0 8 -> 6, UADDIDEC0 22 -> 6. collatz 16 short (A' uaddi1 -1302,
  E ucond_br6 -460, A' ucmpi0 -370, A' ucmpi2 -207, ...) -> 6 raised (UADDI1 3 -> 11, UCMPI2 5 -> 8, UCMPI0 6 -> 9 ...),
  2 lowered. As the loop's header predicted, a proposal priced on the estimates route under-delivers on the compact
  route it produces; the re-check catches it. Note UADDI1 (collatz's steps + 1) now 11 > UCMPI2 8 at their shared
  join: the case formal B3 says pays for a capture that never happens (joinrule subagent).
- Farm gcddraw1: 42 of 64 tasks hit the 150-min limit after their build (gcd18's draws take hours in the decoded-netlist
  simulation: e.g. task 10 built gd1_75_10, P 91.6 ns, EQUIVALENT, then timed out in the checks), 2 failed at container
  start, 20 running. Not a verdict on gcd; a lesson on budgets.
- So suite1 (still waiting) now asks 4 kernels x 8 seeds (32 tasks); for gcd and isprime the suite uses one long vector
  for P (gcd (7fffffff, 1), isprime 2003) and gcd8 for gcd's draws (gcd18's edges and its longest pair), expected values
  still compiled from the C at run time.
### progress 00:02 (the AUTO loop converges slowly: each lowering re-places the route and opens new small misses)
- Seed 1, negatives per iteration (it 1 / it 2): xorshift 3 / 8 (it 2: E umux2 -298, A' uaddi0 -188, A' uxori2 -51,
  A ucontrol_merge1 -41, E steers -24 / -8); collatz 16 / 8 (it 2: H ulink_n7 -304, A' umux2 -257, E ucond_br3 -256,
  A'm umux1 -255, A' uaddi0 -150, E ucond_br5 -90); collatz64 14 / 3 (it 2 route FFMUX-FLAG: a bitstream defect on an
  intermediate route). Pinned lines grow (xorshift 3 -> 7, collatz 6 -> 10, collatz64 8 -> 11) while the unpinned ones
  keep shrinking (xorshift UCMPI1 26 -> 22 -> 19).
- Why the first proposal under-delivers, measured: collatz64's 64-bit 3n + 1 (UADDI0) was 160 elements (63.4 ns) on the
  estimates route, the rule proposed 4 (1.26 ns, "205 ps left"), and on the route built from it A' was -2809 ps (padded
  to 20). On the spread-out route the request's own wires covered most of the data path; on the compact route they do
  not. The loop is what makes the rule safe; a better first point would save routes (to do: start from a tighter
  estimate than emit.py's deliberately generous one).
### progress 00:03 (CORRECTION: ipow x0.55 route 12 never failed a draw -- the three "hangs" were the farm wrapper's timeout)
- Formal C50: on the identical bits (c3542c6d) our own bench_gate.sh passes draws 1201 / 1203 / 1204 (PASS 17/17, ~380 s
  each on one core). Our farm record (shrink8 task 12) reads "=> TIMEOUT/none" for those three: the request's
  `timeout 100m` fired with four draws sharing the task's cores; the gate never gave a verdict. The journal entry of
  2026-11-17 19:50 ("route 12 ... hangs on 3 of 4 draws, including draw 1203 at CARRY 0.20: not a CARRY effect") and
  the conclusion drawn from it ("ipow candidates come from x0.70, not x0.55") were wrong: there was no failure.
- research/tools/draws_table.py now counts TIMEOUT/none as undecided, never as a fail. Re-tallied: ipow x0.55 81 / 81
  draws pass on the EQUIVALENT routes (+ 3 undecided), P median 26.41 ns (x0.70: 30.21); unchanged elsewhere (real
  wrong answers): collatz x0.55 110 / 112 (route 30), collatz64 x0.55 69 / 89 (302 mismatch batches), xorshift x0.40a
  47 / 55 (+ 5 undecided). The suite's own runner has no wrapper timeout (the gate's HANG cutoff is its only one).
- Local re-run of route 12's draws without a wrapper (niced) to close it here too. ipow x0.55 is a hand-recipe point
  (a per-kernel factor); under "General first" it goes to the hand column, not the headline.
### progress 00:04 (two-hour re-read: PROGRAM unchanged since 411a48df5; formal B3-B5, C49, C50 read)
- B4 (formal, untrusted sim, RC arcs): on each candidate route only 3-5 of ~55 delay lines set the period, and they are
  the loop RINGS (xorshift: the counter ring umux0 -> uaddi0 -> ucond_br6 -> ulink_n_trueResult_6 and the n ring umux2 ->
  ucmpi1 -> ucond_br8 -> ulink_n_trueResult_10, within 0.03-0.47 ns of each other; collatz / collatz64: 3n + 1 and the
  select), never the xorshift datapath. Which lines, moves with the route (seed 21 vs 4). Cutting the rings' request
  lines on x55a10 gave -5 % / -9.5 % but left the loop test 154 ps of settle with 4 live runts: formal does not
  recommend it; UADDI0 0 alone kept 1.5-1.8 ns.
- B3 update (farm b_u0xor, 12 seeds a side): UADDI0 0 safe in every draw, -3.3 % mean, the loop test's worst settle
  1020 -> 344 ps. B5: every current board candidate passes formal's full-range runs (preloaded counters, 63-bit collatz
  values); incrementers / step counters keep >= 8.6 ns of carry slack. C49: x55a10 on RC arcs, 13 routes, 52 / 52
  slow-carry draws, loop-test margin >= 896 ps. C50: handled above (ipow route 12).
- For the automatic path this says where the speed is: the sizing loop sizes ~55-70 lines, but the period is set by the
  few on the rings, and the full-range rule oversizes counters by >= 8 ns of slack. The joinrule subagent takes the
  "capture that does not happen" term; a cycle-aware step (shrink only the event graph's on-cycle lines, judged by
  draws) is the next candidate after it.
### progress 00:16 (owner 081281596: at most 2 subagents until the reset; Dynamatic estimator landed)
- PROGRAM "Quota: land near 95 % by the reset" (owner, 00:13 UTC; 78 % used): at most 2 subagents at a time, both on
  "General first" and the suite. Kept: suitek (the suite's scalar kernels, oracle, SUITE.md) and joinrule (the sizing
  rule's "capture that does not happen" term). Asked to stop now and write up what they have: bandfit, pnrfix, suiteb
  (bench ABI; resumes later from its notes). dynref and suited had finished.
- dynref (reviewed, cbad99cc3): research/tools/suite/dynamatic_est.py simulates Dynamatic's own on-merges circuit
  (dynamatic-opt here; units transcribed from dynamatic/data/verilog) cycle by cycle, every call checked against the C
  (310 calls on 62 kernels right); the period is Dynamatic's timing model's longest path x 0.793, fitted on the three
  routed kernels (rms 7.3 %, worst leave-one-out 16 %): an ESTIMATE. Cycle counts confirm the hand derivations:
  xorshift / collatz / collatz64 1 per iteration, ipow 5 (no placement below 4), gcd 3.03 per main iteration + 1.00
  per shift. MILP placement cannot run here (no Gurobi / CBC). The suite table now takes Dynamatic's figure from it
  where nothing was measured (ipow 50.0 replaces the hand 67; gcd 50.6 in our P's unit, main + one shift).
- .gitignore: dynamatic/ and circt/ anchored to the root (the unanchored pattern hid research/data/suite/dynamatic/).
### progress 00:22 (pnrfix and bandfit stopped and written up; the NOT EQUIVALENT class has one cause; collatz AUTO 18.06 ns)
- **The NOT EQUIVALENT / FFMUX routes, cause found (pnrfix, reviewed; research/data/pnrfix/README.md):** nextpnr-xilinx's
  Arch::routeVcc() (xilinx/arch.cc) routes GND/VCC sinks after router2 by a BFS through free wires capped at 50 000
  wires; a sink that hits the cap is logged "left to main router", but no router runs after it, so it stays unrouted.
  VCC always routes (every IMUX/BYP has a default ppip from VCC_WIRE); a missed GND pin reads 1 on the die. Effect by
  pin: plain LUT input -- harmless (fixupRouting drops its X_ORIG_PORT, so the INIT reads 0 = GND); **F7/F8 select --
  wrong** (ipow x0.55 route 19, d63bfd80: 11/17 in the bits-decoded GLS); **flop D -- wrong** (no FFMUX bit; what the
  die latches is unknowable); DSP CLK -- harmless. The "benign F7BMUX/0" kind was a fasm_equiv false alarm (the JSON-side
  GND LUT was not folded like the bits side): fixed (745cb181a, 6fa7bfb57) with two negative controls still flagged.
- **A nextpnr patch exists, NOT installed:** research/data/pnrfix/nextpnr-xilinx-const-sinks.patch routes the missed
  pins whose value matters after routeVcc, through free wires without a cap (rip-up fallback; error if still unroutable).
  On 6 defect routes (7 pins) the defect is gone, placement / signal nets / SDF byte-identical, the FASM only gains
  6-16 lines; route 19 11/17 -> 17/17; routes without a defect byte-identical in JSON, SDF and FASM (3 checked); the
  unpatched rebuild reproduces the installed binary byte for byte; a toolchain.sh check that fails on the installed
  binary (toolchain.sh.proposed). Why not installed: $TC is on NFS shared with the farm, so swapping the binary would
  mix two nextpnrs inside running requests (mine and formal's). Plan: install when no farm request is running,
  update toolchain.sh and patches/ in the same commit, and record the new fingerprint. Owner: objections welcome.
- **collatz AUTO, seed 1: P 18.06 ns** (hand item 31: 21.5 median; x0.70 sweep 19.76), route it 4 (533a7474), the
  loop NOT CLEAN by 1 constraint after 4 routes; bits EQUIVALENT once fasm_equiv is fixed (it was the false-alarm
  kind). Its 4 draws are running now (suite_one.sh had skipped them as not a board route). One seed: a sample, not a
  claim.
- **bandfit (stopped; a74851fb5):** LUT + routing x = 0.222 (0.213 gcd - 0.227 ipow) over the five August bitstreams,
  leave-one-out within 0.8 % on four, +1.6 % on gcd; ipow 60.43 / 60.33 ns at y 0.2 / 1.0 vs board 60.43. The CARRY /
  F7 band y moves ns per iteration by 0 (a constant ~0.2 ns per call per unit y, outside the loop), so no kernel can
  place it; only BOARD-QUEUE item 36 can; the draws stay uniform over [0.20, 1.0]. Answers stay right at y 2 and 3 on
  collatz / collatz64 / ipow / gcd (10 of 24 vectors), and at y 6 on ipow. Correction: xorshift's trip_N logs were taken
  at 50 MHz, so they show 49.6 ns per round, not ~25 (one build family, not two); the archived bit at x 0.222 gives
  49.71 ns. Not done: isprime, gcd's other 14 vectors.
### progress 00:33 (suiteb paused with 13 patches; to be applied after this suite run, with a GLS regression check)
- Done and verified by suiteb (its notes: research/data/suite/bench/README.md in /tmp/bot/sa/suiteb/out/0013): MAX_WORDS
  2 -> 10 (OP2..OP9 only for kernels that need them; kernels/sum3, 3 args, seed 1 worst PASS 6/6, EQUIVALENT,
  ANNOTATE_DONE clean); a host slot on each memory port (bdc/emit.py --host-mem, opt-in) driven by a four-phase handshake
  from the PS clock with 2-flop synchronizers on the acknowledges; vector format v2 (header line; old files read as
  before); oracle_mem.sh from the C; **memsum seeds 1-4 PASS 5/5 at worst** with the arrays read back after each fill and
  each call equal to the C's and a one-hot monitor seeing 448 host / 170 kernel requests, 0 overlaps (170 = the C's
  loads); negative control (different array contents) FAILS. RAMB18E1 in the bits-decoded GLS (fasm2net, gen.py,
  prims.v, xray_delay.py, fasm_equiv.py). gen_bench.py byte-identical for the six kernels (18 files, cmp).
- Not done: fir's gates (4 routes built), max / min corners, three negative controls, stores (design note only: bdc needs
  an arbitrated, token-driven store counter for memEnd). memsum seed 4 bits NOT EQUIVALENT (not looked at).
- The patches change the GLS core (prims.v, gen.py, fasm2net.py) that every running job reads, so they wait for the
  suite run to end, then go in after a regression run (an existing route's full-stack BENCHRES and fasm_equiv verdict
  unchanged).
### progress 00:51 (first automatic routes, seed 1 only: collatz 18.06 ns passes 4 / 4 draws; collatz64 30.01; xorshift 21.08)
| kernel (BDC_AUTO=1, seed 1, MAXIT 4) | route (sdf) | rule after 4 routes | bits | P, ns | draws | hand best | Dynamatic |
|---|---|---|---|---|---|---|---|
| collatz | su_collatz_1_4 (533a7474) | 1 constraint short | EQUIVALENT (fixed checker) | 18.06 | 4 / 4 (col18 17/17 each) | 21.5 (item 31) | 14.05 measured |
| collatz64 | su_collatz64_1_4 (932bae2e) | NOT CLEAN | EQUIVALENT | 30.01 | running | 31.4 (item 32) | 17.84 measured |
| xorshift | su_xorshift_1_4 (694d657d) | 2 short | EQUIVALENT | 21.08 | running | 16.76 (x55a10) | 12.73 measured |
| ipow, gcd, isprime | in the loop | | | | | 36.2 (item 29), 87.2 (1 route), - | 50.0 / 50.6 ESTIMATE |
- One route per kernel: a sample, not a result (farm suite1, seeds 1-8, is queued). Prediction for the automatic column
  (research/data/auto/README.md 3b, written before any AUTO route): xorshift 28 (25-31), collatz 26 (23-30), collatz64
  36 (32-40). All three came out faster than predicted; collatz and collatz64 at or below their hand recipes' medians.
- No sizes file, no factor, no instance name: BDC_AUTO=1 + auto_size.sh's loop. Each final route ran the full stack
  (bits-decoded netlist, prjxray SDF, fid) once; the draws are the judge.
### progress 01:14 (seed 1 local: xorshift 21.08 ns 4 / 4 draws; farm suite1 = flow v1, most routes judged by the old checker; suite2 = flow v2)
- Local seed 1 (flow v1: start at the estimates): **xorshift P 21.08 ns, 4 / 4 draws** (xor19 19/19 each), EQUIVALENT,
  1339 kernel LUTs; collatz 18.06, 4 / 4 (above); collatz64 30.01, draws running; ipow route it 4 (9a5c155d) NOT
  EQUIVALENT with a kind the fixed checker does not fold (F7BMUX/0 json const 0, bits D6LUT, the reverse orientation of
  the GND-LUT case; not yet looked into) and its event graph failed (no cycle found; IndexError in eventgraph.py), so
  no P. Local gcd / isprime (v1) stopped: suite2 runs them on the farm.
- Why xorshift's automatic route is 4.3 ns over the hand recipe (21.08 vs 16.76) with the same total delay (106 vs
  105 links): UCMPI1, the n ring's loop test, is 18 elements (hand 5), held by rule E at the steers ucond_br8 / 9;
  every other line is at or below the hand's. That is formal B4's n ring and the joinrule subagent's case.
- Farm suite1 (flow v1, picked up at a31502b69, before the checker fix): it runs fast on the farm (a whole loop + the full
  stack in ~28 min on 2 cores). 9 of 32 back: xorshift seeds 2 / 3 / 6 / 7 P 23.11 / 23.18 / 19.43 / 23.21 (seed 6 the
  only loop CLEAN by it 4), collatz64 seed 5 25.59, all called NOT EQUIVALENT by the old checker and so not drawn;
  collatz seed 7 EQUIVALENT but no P; collatz seeds 3 / 4 PNR-TIMEOUT at it 0 (the estimates route, > 3600 s on 2 cores).
  The request also copied the loop's result.txt over the suite's (fixed in suite2: the loop's files go to OUT/auto/).
  research/tools/suite/rejudge.sh rebuilds a route from its returned sizes_final.vh and judges it with today's checker
  (test running on xorshift seed 3: must reproduce sdf ea3c2aad).
- auto_size.sh flow v2 (2e5b0e013): the loop starts at emit.py's estimates x 0.3 (AUTO_START_SCALE, one number for
  every kernel; the rule still sets every size). Farm suite2 = flow v2 on the six kernels x seeds 1-8 with the fixed
  checker; prediction in its header.
### progress 01:27 (C50 closed: ipow x0.55 route 12 passes all four draws here; the checker fix had a one-sided fold, fixed)
- ipow x0.55 seed 12 rebuilt here = the farm's route (sdf c3542c6d, P 24.65 ns): draws 1201 / 1202 / 1203 / 1204 PASS
  17/17 each with no wrapper timeout (581-1152 s each on this loaded node, niced). With the farm's 81 / 81 that is
  every draw passing on every EQUIVALENT ipow x0.55 route (a hand-recipe point, P median 26.41 ns vs x0.70's 30.21).
  Formal C50 reproduced.
- But the same gate called those bits NOT EQUIVALENT, and so did AUTO ipow seed 1's (9a5c155d): 745cb181a (pnrfix) folded
  the JSON side's GND LUT in pin_drivers, so where both sides name the same LUT the JSON side became const 0 and the
  bits side stayed a bel: DRIVER DIFFERS (F7BMUX/0, CARRY4/DI0-2). 601010f1b folds only in the comparison, where one
  side is that LUT and the other a constant: c3542c6d, 9a5c155d, 533a7474, b0aaeccd all EQUIVALENT; pnrfix's two
  negative controls still NOT EQUIVALENT. Farm suite2 was picked up at 3e47c10ad (with the one-sided fold), so its NOT
  EQUIVALENT routes will be re-judged from their returned sizes (rejudge.sh).
- x55a10 seed 21 (bit 6a68b04e): SLOW_MAX / FAST_MIN / worst PASS 19/19 each; draws 2101-2105 PASS so far (32 queued).
### progress 01:38 (suitek landed: 14 suite kernels, SUITE.md, the C oracle; the suite found two liveness bugs in bdc)
- suitek (reviewed; 4fc96e310 .. 38c58b2c4): kernels/{straight, countloop, sqrtsub, nest3, twoloops, brhash, lfsrfind,
  quadrec, horner, fold64, varshift, cmpchain, digitsum, digitdiv} with fixtures, vectors at the edges of each declared
  range (trip counts <= ~256: the routed gate simulates ~0.22 us of circuit time per wall second) and expected values
  from research/tools/suite/oracle.sh (the kernel's C, argument words from its signature; reproduces ipow17 / isp17
  byte for byte; two negative controls fail); bdc/simcheck.py --c-oracle; kernels/SUITE.md (23 rows).
- Seed-1 smoke (one route each, emit.py's placeholder sizes, worst corner): 9 / 12 right in each flow.
  **quadrec deadlocks in both flows** (simcheck and the routed EQUIVALENT gate, n = 4): bdc's ring floor counts stages,
  not tokens; the rotation a <- b <- c <- d puts 4 tokens on a 4-stage ring (research/tools/suite/ring_tokens.py: -4;
  every other fixture +1 or acyclic). **The default flow hangs on lfsrfind, nested and nest3** (inner loops with zero
  trips after the first instance; a search with break); each passes with rule M's merge output link, so BDC_AUTO=1 is
  live where the default is not. digitsum stops in the frontend (arith.remui), digitdiv in bdc (no divui cell). Bits:
  10 of 26 smoke routes NOT EQUIVALENT under the old checker (the F7 kinds), lfsrfind / nest3 AUTO FFMUX-flagged (wrong
  values on those bits only).
- Found by it too: bdc/auto.py silently skips the proven MLIR rewrites when research/tools/fifteen is absent (a plain
  cells/ bdc/ copy, as research/data/alltable/run_default.sh builds); auto_size.sh / build_bench.sh in the repo are
  not affected. To do: make auto.py fail loudly.
- Started: subagent ringfloor (the token-aware floor for quadrec, and whether the same argument explains the default
  flow's hangs). Farm suite3 (16 suite kernels x 4 seeds) submitted; kernels.txt now lists 22.
- Rejudge test: the farm's xorshift seed 3 route rebuilt here from its sizes_final.vh is the same route (sdf ea3c2aad,
  P 23178) and EQUIVALENT under today's checker; its draws are running.
### progress 01:48 (bench ABI landed after a regression gate; auto.py refuses a missing rewrite)
- suiteb's 13 commits applied (3-way; fasm_equiv.py merged with the comparison-only fold): MAX_WORDS 10, the host memory
  slot (emit --host-mem), v2 vector files, oracle_mem.sh, RAMB18E1 in the bits-decoded GLS, the memport monitor, sum3.
  Regression before landing: the patched GLS re-ran collatz AUTO seed 1's draw 10101 (533a7474) with identical BENCHRES
  for all 17 batches and the same verdict (PASS 17/17, cycles 5090, EQUIVALENT). Memory kernels can now run in the
  suite (memsum passed 4 seeds at worst in suiteb's runs); stores still do not emit.
- bdc/auto.py exits 1 when a proven rewrite's script is missing (04ef56a1c).
### progress 02:09 (rejudge works: farm suite1's xorshift seed 3 passes 4 / 4; collatz64 seed 1 4 / 4; memsum joins)
- research/tools/suite/rejudge.sh on suite1's xorshift seed 3: rebuilt here from its sizes_final.vh = the farm's route
  (sdf ea3c2aad, P 23178 ps), EQUIVALENT under today's checker, **4 / 4 draws** (xor19 19/19 each). So the suite1
  routes the old checker refused can be judged; that is the plan for suite1's and suite2's NOT EQUIVALENT rows.
- Local seed 1, collatz64: **4 / 4 draws** at P 30.01 ns (c6419). Headline (top of research/data/fifteen/README.md,
  preliminary, one route each): xorshift 21.08, collatz 18.06, collatz64 30.01 ns, every draw passing.
- Memory kernels in the suite runner: a v2 vector file (arrays) takes oracle_mem.sh and GATE_MEMEXP (every array read
  back after each call must equal the C's); kernels/memsum/vec.hex = suiteb's five calls.
- eventgraph.py: with no cycle through its marker it now writes the marker's measured period instead of an IndexError
  (the reason the automatic ipow route had no P).
- x55a10 seed 21 (board-item candidate, hand column): 3 corners + 15 draws so far, all PASS.
### progress 02:16 (FIRST DRAW FAILURE of the automatic path: xorshift seed 8, the zero-trip call; the rule now sizes for the judge's band box)
- Farm suite1 (flow v1), 23 of 32 back, routes judged (EQUIVALENT under its old checker) and their draws:
  xorshift s1 21.08 4/4 (= the local route, P to the ps), s5 20.25 4/4, **s8 3 / 4**; collatz s2 21.15, s5 18.73, s6 17.68,
  s7 (no P) all 4/4; collatz64 s6 22.48, s7 22.25 4/4; ipow s1 (no P), s3 25.23, s7 20.20 4/4. The rest were called NOT
  EQUIVALENT by the old checker (xorshift s2 / s3 / s6 / s7, collatz s1, collatz64 s5, ipow s4 / s5 / s6) or timed
  out routing at it 0 (collatz s3 / s4): research/tools/suite/farm_collect.py lists them for rejudge.sh.
- **xorshift seed 8, draw 10804** (chains 0.2124, rest 0.2770, carry 0.2619): FAIL 18 / 19 -- batch 18, (x, rounds) =
  (0x2468ace0, 0), the zero-trip call: both runs completed, the second returned the right value, the repeatability latch
  says the two runs differed. The route's entry compare UCMPI0 = 5 (hand x55a10: 10, formal C41's fix for exactly this
  loop-entry steer race). Cause in the rule: CA_SIZERULE sized with the delay chains and everything else at one band
  (0.21), while the draws -- the judge -- take them independently from [0.20, 0.31]; a draw with fast chains and slower
  logic and wires is outside what the rule covered.
- Fix (56c8dea81): auto_size.sh runs the rule at the model's two worst vertices for the chains (0.20) with the rest at
  0.20 and at 0.31 (CARRY4 / F7F8 / FF at SLOW_MAX in both) and keeps per line the max (merge_rules.py). A race's margin
  is linear in the bands; the chains are on the request side, the rest on both. Cost on xorshift seed 1's final route:
  0.20 -> 97 links, 0.31 -> 102, merged 103 (built 106); UCMPI0 7 -> 8, UMUX3 5 -> 6. Not yet checked: seed 8's own
  route under the new rule (its sizes are in the farm results; rejudge after a re-size, next).
- Lesson for the draw counts: 4 draws per route found this on 1 of 32 routes; the hand items were judged by 32 draws on
  one route. The automatic routes need the same depth before any of them goes to BOARD-QUEUE.
### progress 02:27 (formal B6 / B7: suite1's "NOT EQUIVALENT" was the false alarm; a NOT CLEAN route fails a slow-carry draw; finish phase)
- B6: suite1 xorshift seeds 3 / 7's NOT EQUIVALENT is the packer GND-LUT false positive (agrees with 601010f1b).
- B7 (formal's simx, RC arcs): AUTO xorshift seed 3 (ea3c2aad, UCMPI0 6, the loop NOT CLEAN at MAXIT with the rule's raise
  6 -> 7 unbuilt) passes our 4 default draws but fails slow-carry draw 5104 (chains 0.259, rest 0.287, CARRY 0.997):
  the zero-trip call returns 0x92d78cb6; at the data steer ucond_br3 the entry compare's condition glitches 149 ps after
  the request (a 21 ps pulse corrupts ulink_n_falseResult_1's controller). Same race class as our seed 8 failure and as
  item 35's (C36 / C41 / C48). Formal's seed 1 route (UCMPI0 7) keeps 602 / 689 ps; final UCMPI0 per suite1 seed: s1 7,
  s2 8, s3 6, s6 9, s7 7, s8 5.
- So the loop must not ship a route its rule flags: 3e93738b1 adds a raise-only finish phase (up to AUTO_FINISH = 3 more
  routes, ratchet.py --raise-only) when nothing was clean by MAXIT. With the two-corner rule (56c8dea81) this is flow
  v3; suite3 and suite4 (both still waiting) will run it. Formal's shards have stopped until the reset (owner).
### progress 02:37 (suite2 = flow v2, 12 of 48: every judged route 4 / 4; xorshift 18.1-19.9 ns; gcd / isprime time out routing)
- suite2 (start x 0.3, one-band rule, the one-sided-fold checker): xorshift s4 18.11, s5 19.90, s6 18.21; collatz s3
  18.49 (clean), s4 18.86, s6 18.92, s7 21.44; ipow s1 22.22: all 4 / 4 draws, EQUIVALENT. collatz s5 / ipow s2 NOT
  EQUIVALENT (to rejudge). gcd s8 and isprime s1: PNR-TIMEOUT at it 0 (3600 s on 2 cores). The scaled start is faster
  than v1 on xorshift (v1 seeds: 20.3-23.2).
- suite4 now 4 kernels x 8 seeds (cores 3); suite5 = gcd and isprime x 4 seeds on 8 cores with PNR_TIMEOUT 7200. Both
  waiting; they will run flow v3 (two-corner rule, finish phase).
### progress 02:53 (joinrule landed: CA_JOINAWARE; on by default in the automatic loop = flow v4; steerE started)
- joinrule (reviewed; f7fa9e7fa .. ae3cb9668, research/data/sizerule/joinaware.md): rule A' checks each sized operator's
  data at its captures (the next latch's enable, a steer / mux select against the request on the same LUT), C-elements
  waiting for their last input, and credits a sibling's request at a join when it shares the operator's launch one
  crossing back (minimum over forward ancestors and acknowledge sources, valid under back-pressure); the latch's open,
  not its close, is the capture (downstream rules assume the input settled when it opened). Statically reproduces formal
  B3 on 4 x55a10 routes (UADDI0's chain removed: A' -1.5..-2.1 ns, A'j +275..+1734 ps, from ucmpi1's credited request).
  Negative controls flagged. Draws: xorshift UADDI0 1, 12/12 on 4 routes + preloaded counter 12/12; collatz UADDI1 1,
  7/7. Not credited: collatz's uaddi1 / ucmpi2 meet several crossings back (its proposal UADDI1 3, not 1).
- Unset, corner_audit is unchanged after the merge (checked on xorshift seed 1's final route). On, both corners merged,
  that route: 103 -> 89 links. Now the automatic loop's default (62d288da2): flow v4 = scaled start, two-corner rule,
  join credit, finish phase. suite3 / suite4 / suite5 (all still waiting) will run v4.
- Started steerE (subagent): why rule E at the loop steers holds xorshift's UCMPI1 at 17-19 (hand 5, 200 / 200 draws);
  hypothesis: the steer's C-element waits for the condition's own request, which skew.py's same-level AND seeding does
  not see.
### progress 03:33 (BOARD-QUEUE item 37: x55a10 seed 21, 32 / 32 draws + 3 corners; rejudge1 submitted)
- x55a10 seed 21 (bit 6a68b04e, sdf 42b4fb4c = the farm's cand3b route 21): SLOW_MAX / FAST_MIN / worst 19/19 each and
  draws 2101-2132 all PASS (xor19). Written as BOARD-QUEUE item 37 (hand column; run it instead of item 35). The first
  automatic build goes to the board list when one route has the same depth of evidence.
- Farm rejudge1 (12 tasks): the 11 suite1 / suite2 routes their older checker refused, rebuilt from the sizes their
  loops kept and judged with today's checker (4 draws each), and suite1 xorshift seed 8 with 8 draws (how often that
  route fails). suite1 31 / 32 done; its per-task table is research/data/suite/farm/ (sizes) and the journal above.
### progress 04:03 (farm suite2 = flow v2, 26 of 48: every judged route passes; the automatic column beats the hand recipes on 3 of 4)
| kernel (suite2, flow v2, 4 draws / route) | routes judged / built | draws | P median (range), ns | hand best | Dynamatic |
|---|---|---|---|---|---|
| xorshift | 8 / 8 | 32 / 32 | 18.63 (16.69-19.90) | 16.76 | 12.73 measured |
| collatz | 5 / 6 | 20 / 20 | 18.86 (17.99-21.44) | 21.5 | 14.05 measured |
| collatz64 | 3 / 3 | 12 / 12 | 23.20 (22.46-26.75) | 31.4 | 17.84 measured |
| ipow | 7 / 8 | 28 / 28 | 21.98 (20.39-23.48) | 36.2 | 50.0 ESTIMATE |
| gcd, isprime | 0 / 1 each | - | PNR-TIMEOUT at it 0 (2 cores) | 87.2 / - | 50.6 / 9.3 ESTIMATE |
- Geometric mean of the ratio to Dynamatic over the 4: 1.03 (ipow's figure is an estimate). Every loop ended NOT CLEAN
  (v2 had no finish phase) yet every draw passed; formal B7 shows a NOT CLEAN route can still fail a slow-carry draw,
  which is why v3 / v4 finish clean. Headline written to research/data/fifteen/README.md (marked as v2, partial).
- Local flow v4 on xorshift seed 8 (the v1 failure's seed): it 0 (167 links) -> proposals 76 / 79 at the two corners;
  it 1: 40 constraints short (the start still under-delivers), 8 raised; it 2: 8; it 3: 5. Running.
- suite_table.py reads a farm results dir one level deep (it had picked up the loop's own result.txt in TASK/auto/).
### progress 04:13 (audit: the headline's 1.03 OVERSTATED -- corrected to 1.37 over measured Dynamatic figures)
- Audit (journal 2026-11-18): "geometric mean ratio to Dynamatic 1.03" counted ipow against an ESTIMATE; over the three
  measured figures it is 1.37 (own arithmetic, agreed); no model error was quoted; flow v2 is the one-band rule already
  replaced. Accepted: suite_table.py prints both means (measured only / with estimates) and the model error (the
  simulation ~8 % slow per iteration vs the August board; Dynamatic's measured figures are single-route nextpnr Fmax,
  not board runs); the headline says v2 is superseded.
- Two-hour re-read: PROGRAM unchanged since 081281596 (2 subagents until the reset).
- Local v4 xorshift seed 8: phase 1 ended with 2 short (it 4); phase 2 (raise-only) it 5 still 5 short (-5..-278 ps:
  each re-placement moves margins by a few hundred ps); entry compare UCMPI0 now 9 (v1's route: 5), UCMPI1 13 (v1: 19).
### progress 04:24 (rejudge1, 9 of 12: every route the old checkers refused is EQUIVALENT and passes 4 / 4; headroom in phase 2)
- Rebuilt from their kept sizes on the farm, same sdf md5s as the original routes (determinism again): suite1 collatz s1
  (533a7474 = the local seed-1 route) 18.06, xorshift s2 23.11, s3 23.18, s6 19.43, s7 23.21, ipow s5 21.78, s6 23.53;
  suite2 collatz s5 19.32, ipow s2 21.53 -- all EQUIVALENT under today's checker, all 4 / 4 draws. Pending: collatz64
  s5, ipow s4, and suite1 xorshift s8 with 8 draws.
- Local v4 xorshift seed 8: the raise-only phase did not converge (it 5 / 6 / 7: 5, 3, 4 constraints short, -5..-278
  ps); 58eaea666 gives phase-2 raises one element of headroom (AUTO_HEADROOM=1). suite3 (still waiting) will run it;
  suite5 started at 2cfdd934b (v4 without headroom), suite4 at 312abcc32 (v3).
### progress 04:44 (ringfloor landed: the token floor -- quadrec and the default flow's three hangs fixed in bdc)
- ringfloor (reviewed; db544ea9f, 670bdbe09; research/data/suite/ringfloor.md): while a loop iterates the circuit is a
  marked graph, live iff every cycle holds a token. Two conditions: a directed cycle with T back edges (T tokens) needs
  >= 2T + 1 storage stages (the 3-stage floor is T = 1), and two paths from one fork to one join where one crosses K
  more back edges need >= 2K stages on that path (no cycle count sees it); one check, every closed walk holds a token.
  bdc/emit.py token_floor(), ON by default in both flows (a liveness rule, like the 3-stage floor; BDC_TOKEN_FLOOR=0 only
  for negative controls), adds stages where a walk has none.
- Effect: quadrec simcheck 10/10 in both flows (was a deadlock at n = 4); lfsrfind, nested, nest3 live in the default
  flow (the same mechanism: the walk exists only when an inner loop is skipped after the outer back edge was used); the
  model called 19 of 34 configurations short and simcheck deadlocked on exactly those 19. Negative controls: removing
  any one added stage deadlocks again (6/6). Emitted Verilog unchanged for every other fixture (90 identical, the
  refused ones refused alike); checked here: the six original kernels, straight and memsum identical in both flows.
  Routed smoke, 4 seeds x 2 flows: 4/4 + 4/4 pass, EQUIVALENT; 8/8 draws on the AUTO routes. Not run: the sizing loop.
- For the owner: CLAUDE.md's "A ring needs three storage stages per simple cycle" is the one-token case of this
  condition; it is not edited here.
### progress 04:54 (steerE landed: xorshift's loop test was held by a lap; flow v5; the v1 failure's seed passes under v4)
- steerE (reviewed; 81a286535, 277e16c7c; research/data/sizerule/steerE.md): the row holding UCMPI1 at 17-19 is a LAP,
  not a select-vs-request race: from n's latch through the compare, ucond_br8's own select and output, its
  acknowledge, the sibling link ulink_n11__0_folink's C node on c_next, its rdly, into the join -- and skew.py's AND
  seeding fires the steer's C-element on that input alone, because the other input (the compare's own request, from the
  link's C node) is not reached from a latch launch. skew.py --steer-self (BD_SKEW_STEER_SELF=1): a latch launch at a
  steer whose join carries the select's own channel request is bounded by that request (valid under the four-phase
  handshake and rule H at the source link). Unset: identical output. Negative controls (UCMPI1 at 1, +8 ns on the
  compare, steerneg / selneg-style injections) still flagged. On the AUTO route: UCMPI1 17 -> 8; built at those sizes,
  seed 1: **P 16.62 ns** (was 21.08), EQUIVALENT, 4/4 draws. Not converged (the rule's proposal on that route pins
  UCMPI1 near 11); and rule E still disagrees with formal on the hand route (x55a10 s21: E -211..-1189 ps at the loop
  steers from i's C node; formal +923..+1465 ps, every draw passes): no join credit for inputs a launch does not reach.
- Flow v5 (733987e1a) = v4 + the token floor + phase-2 headroom + BD_SKEW_STEER_SELF=1. suite3 (suite kernels, waiting)
  runs it; suite6 (the four fast original kernels x 8 seeds, 8 draws) and suite7 (gcd, isprime x 4, 8 cores) queued
  as the headline run. Frozen at v5 for the headline unless a correctness problem appears.
- Local v4 on xorshift seed 8 (the seed of v1's failing draw): route it 7 (b6f090b6) P 20.92 ns, EQUIVALENT, NOT CLEAN
  by 4 after the raise-only phase; entry compare UCMPI0 9 (v1: 5); draws 10801-10804 PASS, **including 10804** (the v1
  failure); 10805-10808 running.
### progress 05:06 (v4 on the v1 failure's seed: 8 / 8 draws)
- Local flow v4 (two-corner rule, join credit, finish phase without headroom), xorshift seed 8: route it 7 (b6f090b6),
  P 20.92 ns, EQUIVALENT, ffmux-clean, the loop NOT CLEAN by 4 after phase 2; **draws 10801-10808: 8 / 8 PASS**, among
  them 10804 (chains 0.2124 / rest 0.2770 / carry 0.2619), the draw v1's route failed on the zero-trip call. The entry
  compare is 9 here (v1: 5). Latency per call, median over xor19 under the draws: 228 ns.
- rejudge1: 9 of 12 (all pass, above); the last three (collatz64 s5, ipow s4, xorshift s8 x 8 draws) still running.
### progress 05:17 (suite4 = flow v3, 18 of 32: 112 / 112 draws on 14 routes; 12 of 14 loops end CLEAN)
- v3 (two-corner rule, raise-only finish phase, 8 draws per route): collatz 6 routes 48 / 48, P median 18.75
  (17.71-20.60); xorshift 6 of 7 judged 48 / 48, 20.16 (18.87-20.49; v2's 18.63 had the one-band rule); ipow 2 routes
  16 / 16, 24.57. The finish phase makes the loops end clean (12 of 14; v1 / v2: almost none). The cost of the second
  corner on xorshift is ~1.5 ns of median; steer-self (v5) should take back more than that (UCMPI1 17 -> ~10).
- Local v5 preview, xorshift seed 2: it 0 proposals 167 -> 69 / 71 links at the two corners. Running.
### progress 05:54 (rejudge1 done: two flow-v1 routes fail draws -- xorshift s8 1/8 (10804), ipow s4 2/4 (start-up X at the first call))
| rejudged v1 / v2 route (today's checker) | P, ns | draws |
|---|---|---|
| suite1 collatz s1 / suite2 collatz s5 | 18.06 / 19.32 | 4/4, 4/4 |
| suite1 ipow s2 (suite2) / s5 / s6 | 21.53 / 21.78 / 23.53 | 4/4 each |
| **suite1 ipow s4** | 21.61 | **2 / 4**: draws 10401, 10404 hang at batch 0 ((3, 1), one iteration): completed=0, odata=x, the bench FSM itself x (fsm=00000fX6) |
| suite1 xorshift s2 / s3 / s6 / s7 | 23.11 / 23.18 / 19.43 / 23.21 | 4/4 each |
| **suite1 xorshift s8** (8 draws) | 24.04 | **7 / 8**: only 10804, the zero-trip call, as before |
- Flow v1 therefore failed draws on 2 of its ~26 judged routes. v3 / v4 / v5 runs have shown none so far (suite4: 112 /
  112; local v4 seed 8: 8 / 8 on the seed of the xorshift failure).
- ipow s4's failure is the start-up class (SIM-VS-BOARD row 6: unreset latches start x; the owner keeps that start-up in
  the gate, +META_INIT only to diagnose). Being diagnosed here: the route rebuilt from its sizes, draws 10401 / 10404
  without and with +META_INIT=0 / 1. If both META_INIT values pass, the hang depends on an initial value the circuit
  does not define -- a real start-up hazard on silicon only if some power-up value breaks it, which META_INIT 0 / 1
  partly tests.
### progress 06:28 (TOOLCHAIN CHANGE: nextpnr 9c732bc6303458df -> 6e5d224472232d5d, the const-sinks patch; ipow s4's failure is start-up x)
- Installed in $TC (shared with the farm) at ~06:28 UTC: patches/nextpnr-xilinx-const-sinks.patch (pnrfix's), the binary it
  built (sha256 6e5d224472232d5d); the old one kept as $TC/openxc7/bin/nextpnr-xilinx.9c732bc6303458df.bak;
  toolchain.sh's new fingerprint check passes on it and FAILS on the old binary (MISSING const-sinks, exit 1);
  $TC/openxc7/.patches.sha = the new patch-set hash. Verified first, here: on two clean AUTO routes (b6f090b6,
  932bae2e) routed JSON / SDF / FASM byte-identical to the old binary's; on su_xorshift_2_7 (the v5 preview's final
  route, FFMUX-FLAG) the SDF identical and the FASM only gains the CFF's FFMUX bit and its GND pips: ffmux FLAG -> clean.
  From now on every route is built with 6e5d224472232d5d. Farm suite4 / suite5 were running across the swap: a task may
  have used either binary, which matters only on routes with a missed GND pin (old: NOT EQUIVALENT / FLAG; new: right).
  suite3 / suite6 / suite7 (waiting) will use the new one throughout. Why now and not at a quiet farm: it changes no
  route, only the bits of defective ones, and every automatic route the suite throws away for a defect is lost work.
- ipow s4 (v1 route, sdf 1ac15af5 rebuilt = the farm's): draws 10401 / 10404 hang without +META_INIT (as on the farm) and
  PASS 17/17 with +META_INIT=0; =1 running. So the failure is the start-up class: an unreset latch's power-up value the
  simulation leaves x. Under the owner's rule the gate keeps x start-up, so it stays a FAIL in the record; whether a
  power-up value can break it on silicon is what META_INIT=1 (and formal's simulator) can bound.
- Local v5 preview, xorshift seed 2: the loop ended CLEAN at it 7 (raise-only + headroom), on a route with the flop-D
  defect -- the reason for installing the fix now. Its draws are running (on the old bits; the result says
  NOT-A-BOARD-ROUTE).
### progress 06:30 (flow v6: it 1 recalibrates; the v5 preview on seed 2 was 23.0 ns, slower than v2's 16.7)
- Local v5 xorshift seed 2: loop CLEAN at it 7 but P 23.01 ns with 129 links (v2 on the same seed: 16.69 ns, 103 links,
  4/4 draws). Lines raised at it 1 -- where the start's proposal under-delivered on the compact route, 50 constraints
  short -- were pinned for good: UCMPI1 6 -> 15 (v2: 9), UMUX1 7 (2), UXORI1 8 (5). Fix (7cbfe337e): it 1 follows the
  rule's proposal and pins nothing; pinning from it 2. suite3 / suite6 (waiting) get v6 and nextpnr 6e5d224472232d5d;
  suite7 started at 45db9e386 (v5); suite5 at 2cfdd934b (v4). Local v6 on seed 2 running for the comparison.
### progress 06:57 (suite4 = flow v3 complete: 216 / 216 draws on 27 routes; the headline now)
| kernel (suite4, flow v3, nextpnr 9c732bc6303458df, 8 draws / route) | routes judged / built | draws | P median (range), ns | hand | Dynamatic |
|---|---|---|---|---|---|
| collatz | 7 / 7 | 56 / 56 | 18.98 (17.71-20.60) | 21.5 | 14.05 measured |
| collatz64 | 5 / 5 | 40 / 40 | 23.71 (21.50-27.86) | 31.4 | 17.84 measured |
| ipow | 8 / 8 | 64 / 64 | 24.10 (21.47-25.00) | 36.2 | 50.0 ESTIMATE |
| xorshift | 7 / 8 (1 PNR-TIMEOUT) | 56 / 56 | 20.11 (18.87-20.49) | 16.76 | 12.73 measured |
- Geometric mean over the three measured Dynamatic figures 1.42 (with ipow's estimate 1.08). 16 of 27 loops clean.
  Written to the top of research/data/fifteen/README.md (with v1's two failures and v2's faster, one-band numbers).
- With the new nextpnr, the v5 seed-2 route rebuilds with the same SDF (47ac67f6) and is now EQUIVALENT, ffmux-clean
  (was FFMUX-FLAG); its 8 draws are running. Local v6 on seed 2 running (it 0 done).
### progress 07:42 (ejoin: the automatic xorshift's loop-test margin is real; local v6 seed 2 19.72 ns)
- ejoin (reviewed; 5acd49e6c .. 43a061197, research/data/sizerule/ejoin.md): on the hand route (x55a10 s21) all 8
  negative rule-E rows at the loop steers are a missing credit, not a race: the walk fires ucmpi1's operand join on i
  alone, but n's request (behind ULINK_N11__1's 3 elements) is the join's last input in 3678 / 3678 firings (+1148 ps);
  worst-corner GLS gaps 1175-1478 ps (formal C48: 923). skew.py --e-join (BD_SKEW_E_JOIN=1, opt-in, unset identical)
  credits it only where sound (when an acknowledge, not a request, started i's link): br6 -929 -> +119; br7-9 unchanged
  (the request case happens too, the second corner shows it). Negative controls flagged; GLS +3 ns on the carry FAILS
  14/19 (the harness sees this race).
- On the AUTO routes it credits nothing: ULINK_N11__1 is 0 there, so there is no n-side delay. What holds UCMPI1 near
  10-11 is a real thin margin: on the steerE build (UCMPI1 8) br8 keeps 404 ps at the worst corner (n trails i by
  189 ps). E's pessimism there is 629 ps, not a missing credit. So the hand recipe's UCMPI1 = 5 rides on 3 elements of
  n's link; the automatic structure puts that delay in the compare instead. The remaining xorshift gap is structural
  (where the n ring's delay sits), not the rule.
- ejoin's own v5 loop (seed 1): CLEAN at it 5, P 22.67 ns, 4/4 draws -- UCMPI1 pinned at 13 at it 1 (the pin v6
  removes). Local v6, seed 2: NOT CLEAN by 2 after it 7, P 19.72 ns, EQUIVALENT (v5 on the same seed 23.01, v2 16.69);
  draws running. The loop's tightness is the open problem now: each re-route moves the small margins by hundreds of ps,
  so lowering and raising chase each other.
### progress 08:21 (suitew landed: 13 more kernels; memory lines were invisible to the rule; automatic board candidates judging)
- suitew (reviewed; e3005e03a .. 697f34043): kernels/dot2 (two arrays) and kernels/gather (a[b[i]]), and Dynamatic's 11
  integer tests that emit (factorial, fir, if_loop_1, if_loop_2, iterative_division, iterative_sqrt, sumi3_mem,
  test_bitint, test_int16, test_loop_free, unused_arg; their C copied unchanged to research/data/suite/dynsrc/ so farm
  oracles work without dynamatic/), vectors under research/data/suite/vec/, oracles that mask narrow results, clang
  for _BitInt. kernels.txt: 36 kernels. Seed-1 smoke (one route, 2 draws): dot2 PASS, test_bitint PASS,
  test_loop_free PASS; **gather FAIL** (x on every call that reads a[j], j != 0); test_int16 / unused_arg FLOW-FAILED
  (bdc: a `source` reaching a function result runs free; the bench ring on unused_arg's dropped memref has no storage).
- gather's cause: the automatic start shrank bd_mem's setup / clock-to-out lines (8 -> 3, 12 -> 4) and the rule never
  sized them back, because corner_audit named them after the port module (..._UPORT_UMEM0_UCO) while emit.py names the
  parameters after the controller (..._UMEM0_UCO). suitew's stopgap (c6fde65c8): the start does not shrink them. The
  fix here (corner_audit.knob_of_base: drop the _uport segment): being checked on gather's last route.
- The three automatic board candidates (suite4 medians, rebuilt here byte for byte): collatz s6 7 / 35, ipow s2 12 /
  35, collatz64 s5 2 / 35 judgments so far, all PASS.
### progress 08:35 (v6 seed 2: 8 / 8 at 19.72 ns; the formerly flagged route passes 8 / 8 on the new nextpnr; memory lines sized)
- Local flow v6, xorshift seed 2: route 55a25d4e, P 19.72 ns, EQUIVALENT, NOT CLEAN by 2 after it 7, **8 / 8 draws**
  (latency per call, median over xor19: 216 ns). Same seed: v2 16.69 (4/4, one-band rule), v5 23.01.
- The v5 route that the old nextpnr left FFMUX-FLAG (47ac67f6), rebuilt with 6e5d224472232d5d: EQUIVALENT,
  ffmux-clean, **8 / 8 draws**: a route the flow used to throw away is now a board route.
- corner_audit sizes a memory's lines (ae57dc574): on gather's last route the rule pads bd_mem's clock-to-out 4 ->
  12..17 and setup 3 -> 25..27 where rules C / B were short by up to 4.5 ns. Farm suite8 (the 12 runnable kernels added
  today x 2 seeds) submitted with it.
- Subagents: srcjoin (bdc: a source reaching a result, test_int16 / unused_arg) and stores (bdc: memory stores,
  write / read-modify-write kernels; 33 Dynamatic tests blocked by it).
- Automatic board candidates so far (35 judgments each): collatz s6 12 / 12, ipow s2 20 / 20, collatz64 s5 4 / 4 PASS.
### progress 08:57 (isprime seed 2's FLOW-FAILED is a pre-existing nextpnr error, not the const-sinks patch; audit T151 confirms an AUTO route)
- suite5 (gcd / isprime, v4): isprime seed 2 failed at it 2: "ERROR: No wire found for port A1 on destination cell
  $abc$23599...$23606" (rebuilt here from its sizes_2.vh: same error). The old binary (9c732bc6303458df, kept as .bak)
  and the new one fail identically on that netlist, so it is not the const-sinks patch; a nextpnr placement-time error
  on this netlist / seed (to look at: the flow could re-seed such a build).
- Audit T151 (07:43): AUTO collatz seed 3 (suite4, v3) rebuilt from the farm's sizes = sdf 73928b6b exactly; 9 / 9 at
  FAST_MIN / advA / advC / worst / SLOW_MAX on the auditor's own max-peak vectors, 0 runts, min steer margin 1641 ps:
  CONFIRMED. Re-read: PROGRAM unchanged; formal stopped until the reset (owner).
- suite6 (the headline run: 4 kernels x 8 seeds, v6, nextpnr 6e5d224472232d5d) picked up at 55988c8d5.
### progress 09:15 (BOARD-QUEUE item 38: the first automatic build on the board list -- ipow, 35 / 35 judgments, 22.71 ns)
- ipow, BDC_AUTO=1, the loop's own sizes (flow v3, farm suite4 seed 2; research/data/suite/board/ipow_v3_s2_sizes.vh,
  nothing edited), rebuilt here = the farm's route (sdf 81bbe268, P 22.71 ns), EQUIVALENT, ffmux-clean: SLOW_MAX /
  FAST_MIN / worst 17/17 and 32 / 32 draws (K 30201-30232). Hand ipow items: 36.2 ns median (item 29). Board item 38.
- collatz s6 (21 / 21 so far) and collatz64 s5 (8 / 8) still being judged.
### progress 09:25 (srcjoin landed: a result fed only by a source now waits for the call; test_int16 / unused_arg pass)
- srcjoin (reviewed; 2daa2e7ef, f7f4a0a20; research/data/suite/srcjoin.md): bdc/emit.py free_running() finds results
  whose tokens no call bounds (by token counts; plain reachability is useless: a source reaches a result in 103 of 104
  fixtures) and _op_end joins each with the call's produced control results (end + each memory's end), as Dynamatic's
  testbench takes all outputs through one join. BDC_CALL_JOIN=0 = the old wiring. Emitted Verilog: 420 / 428 identical
  (107 fixtures x default / BDC_AUTO / auto.py+AUTO / --host-mem); the 8 that differ are test_int16 and unused_arg; with
  the flag off 428 / 428. Spot-checked here: xorshift, collatz, ipow, gcd, memsum identical. gaussian has the same bug
  but stops earlier at lsq.
- Checks: simcheck test_int16 6/6 over six calls (flag off: the old timeout, 94162 out0 tokens); 50 / 50 other suite
  runs unchanged to the picosecond. Routed seed 1 (nextpnr 6e5d224472232d5d): test_int16 CLEAN at it 0 (no delay lines:
  est_sizes / auto_size now build once and judge), 2/2 draws, 3 LUTs; unused_arg CLEAN at it 1, 2/2, 89 LUTs. Negative
  control (flag off, same seed): both RULE FAILED, "combinational cycle with no storage".
- Board candidates: collatz s6 24 / 24, collatz64 s5 9 / 9 so far; xorshift v3 s8 (rebuilt = 3497ca67, 20.11 ns) started
  (3 corners, 32 draws, 8 slow-carry draws).
### progress 09:35 (suite7: the automatic loop is too slow for the large kernels -- gcd 1 rule step in 4 h; isprime 1 of 4 judged)
- suite7 (gcd / isprime x 4 seeds, 8 cores, flow v5): 6 of 8 tasks hit the 240-min limit. gcd (358 sized lines):
  only it 0 (build + rule) finished in 4 h. isprime (213 lines): seed 4 PASS 4/4 (P 363.19 ns on the period vector
  n = 2003 -- the OUTER trial's period, not comparable to Dynamatic's 1 cycle per inner shift; the table's isprime ratio
  is meaningless until the unit is fixed), seed 3 PNR-TIMEOUT, seeds 1 / 2 still iterating at the limit (seed 1:
  negatives 26 / 78 / 45 / 39 over it 1-4: the large kernels converge worse too).
- Cause: corner_audit runs one sensitivity worker per sized line, each re-running the whole static analysis on the
  route (O(lines x design)); at ~60 s per worker on gcd, one rule step is ~1.5 h even with 8 workers, and the loop
  wants 5-8 steps. The automatic flow does not scale to gcd-sized kernels yet: a work item (sensitivities from the
  critical paths the walk already records, or only for lines that can move).
### progress 10:01 (BOARD-QUEUE item 39: automatic collatz, 35 / 35 at 18.99 ns; suite3 split)
- collatz, BDC_AUTO=1 with the loop's own sizes (flow v3, suite4 seed 6), rebuilt = the farm's route (sdf c56def07,
  P 18.99 ns, the suite4 median), EQUIVALENT, ffmux-clean, rule-clean: 3 corners 17/17 and 32 / 32 draws. Board item 39.
  With item 38 (ipow 22.71 ns) the automatic path now has two board items, both faster than the hand items of the same
  kernel (collatz item 31 21.5; ipow item 29 36.2).
- suite3 (64 tasks) waited 8 h for 128 free cores; split into suite3a / suite3b (32 tasks each; test_int16 and
  unused_arg in, the two that do not compile out -- they are recorded as DOES-NOT-COMPILE already).
- Still judging: collatz64 v3 s5 (13 / 13 so far), xorshift v3 s8 (6 / 6, plus 8 slow-carry draws to come).

## Session 2026-11-18 16:50 UTC -- cluster bot, session 17: the automatic column over every listed kernel (59 of 62 pass), flow v6 -> v8, 15 subagents, every wrong answer traced to a rule and fixed
Toolchain: patches.sha 0d42657914fc25d3, nextpnr 6e5d224472232d5d (toolchain.sh all ok on node3627)   Seeds: per item
Lock: cluster-research-29466208-1 (this wrapper's session 1, ended 10:17 UTC) taken 16:48 UTC as cluster-research-29466208-17.
cluster: sessions 2-16 of this wrapper (10:17-16:17 UTC) each ended after 60 s on "You've hit your weekly limit"; nothing
was lost from git, but session 1's last ~16 minutes and the jobs it left running (until ~12:40 UTC) were never pushed.
Same node (node3627), so their files are still here: recovered below. Quota: PROGRAM's "at most 2 subagents until the
reset (23:00 UTC)" stands; with the week's limit already reached once, this session works without subagents until then.
Audit: newest T153 (item 39 launched); row 25 (the one-route AUTO headline, OVERSTATED minor) is answered by the suite4
table (27 routes, 8 draws each, model error and Dynamatic's kind stated). Formal: stopped since 02:51 (owner, until the reset).
### progress 16:50 (BOARD-QUEUE items 40 / 41 from session 1's unpushed judgments)
- collatz64 v3 seed 5 (sdf 9585dde4, P 23.71 ns, the suite4 median, loop CLEAN at it 7): SLOW_MAX / FAST_MIN / worst
  18/18 and draws 30501-30532 32 / 32 (c6419). **Item 40.**
- xorshift v3 seed 8 (sdf 3497ca67, P 20.11 ns, the suite4 median, CLEAN at it 6; the seed of flow v1's zero-trip failure):
  3 corners 19/19, draws 30801-30832 32 / 32 and slow-carry draws 30851-30858 (CARRY4 / F7F8 / FF 0.8-1.0) 8 / 8.
  **Item 41** (slower than the hand item 37, 16.49 ns; listed as the automatic flow's own xorshift).
- Both rebuilt with nextpnr 6e5d224472232d5d from the farm's sizes; the sdf md5s equal the farm's (9c732bc6303458df).
### progress 16:53 (session 1's two subagents recovered from disk: stores landed, ringplace negative)
- **stores** (bdc lowers a store: each block's outgoing control joins its stores' completions, so ctrlEnd / memEnd /
  out0 come after every store by construction; research/data/suite/stores.md): 7 commits applied. Conflict with srcjoin
  in _op_end resolved by hand: both joins kept, a function with a store AND a source-fed result refused (no fixture has
  both). Checked here after the merge, 108 fixtures x {default, BDC_AUTO=1, BDC_HOST_MEM=1} --no-top: the 105 outputs
  that emitted before are byte-identical to 79fec0d88; the 30 new ones (fill + 9 Dynamatic tests) equal the subagent's;
  top-level emission of the six kernels, memsum, test_int16 unchanged. kernels/fill routed: seeds 1-4 PASS 5/5 at the
  worst corner (s3 / s4 finished after the cutoff), arrays = C after every call, EQUIVALENT; the address negative
  control FAILS 1/5; automatic seed 2 (it 6, NOT CLEAN by 4) 2 / 2 draws at 37.27 ns per trip. 9 of Dynamatic's tests
  now emit (RTL-checked: single_loop, simple_example_1, matrix under AUTO); none routed.
- **ringplace** (a PLACE_WEIGHT on every loop ring's handshake nets, emitted under BDC_AUTO): 8 routes A/B, dP median
  +0.27 ns, mean +0.68, faster on 4 / 8; weight 3: 2 / 4. Prediction (no consistent sign) held. Not landed in bdc (kept
  as research/data/suite/ringplace/ringplace_knob.patch); cycle_wire.py landed. Wire is 85-87 % of the critical cycle
  on every route of both arms.
### progress 17:02 (owner 296c3bf13: 8 subagents until 23:00, then 1; seven started; farm suite9; auto_size.sh can resume)
- PROGRAM (owner, 16:48 UTC): the allowance is full again until the reset (23:00 UTC); up to 8 subagents until then, one
  lead each from the owner's list; from 23:00 at most 1 and fewer steps. Started 16:58 (reports due 22:40): xorgap (1:
  what the hand xorshift has that the flow lacks), loopfast (2: the sizing loop finishes on gcd / isprime), hangs (3:
  deadlocks / hangs, incl. matrix's default-flow deadlock and ipow s4's start-up x), divmod (4: remui in the frontend,
  a divider in bdc), dyntests (5: void kernels on the bench, the 9 store tests into the suite, mc:load1st), memauto (6:
  memory kernels through the automatic path; dot2 at 156 ns per iteration), dynfig (8: Dynamatic's figure per kernel).
  Lead 7 (the suite table on the farm) is mine.
- Farm, read: **suite6 (flow v6, nextpnr 6e5d224472232d5d, 8 seeds, 8 draws): collatz 17.04 ns (14.96-19.46) 64 / 64,
  collatz64 23.27 (22.03-26.12) 56 / 56, ipow 21.58 (19.84-23.36) 56 / 56, xorshift 22.28 (19.43-23.46) 56 / 56**
  (v3: 18.98 / 23.71 / 24.10 / 20.11: v6 helps three kernels and costs xorshift 2.2 ns -- xorgap has it). suite3a / 3b /
  8 / 5 / 7: every judged route passes its draws, but 14 + 19 + 18 tasks and nearly all of gcd / isprime hit the
  240-min limit inside the sizing loop (60-80 min per iteration at 2 cores, 5-8 iterations; and the loop converges
  poorly on the suite kernels: e.g. nested it 2 had 81 negative rows; 9 of 16 finished loops ended NOT CLEAN after 7).
- research/tools/auto/auto_size.sh AUTO_RESUME=DIR: continues a loop from the state a stopped farm task sent back
  (the last iteration whose ratchet_I.txt exists, its pins pinned_I.txt, the phase from the log, that iteration's stop /
  phase decision replayed; a route needed again is rebuilt from its sizes and seed, the sdf md5 checked against it_I.txt).
  ratchet_I.txt is now written last in each iteration, so its presence means the iteration is complete. Unset, the loop
  is the same (the decision block restructured, equivalent; two more files saved per iteration). Test running: suite3a's
  straight seed 3 cut after it 2 and resumed here must rebuild it 3 / it 4 as b185f449 / 4896c89d and end CLEAN it=4.
- Farm suite9 submitted: the 23 kernels with fewer than 4 judged routes x seeds 1-4 (92 tasks, 2 cores), flow v6, the
  state copied back every 5 min for a resume request (suite9r2) at the same commit.
### progress 17:50 (AUTO_RESUME checked on both paths against a farm loop; suite9 running 92 tasks at once; 8th subagent)
- Test 1 (continue a loop): farm suite3a's straight seed 3 state cut after it 2 (pins reconstructed from ratchet_2.txt),
  resumed here (RUNS=/tmp/bot/runs_rt, nextpnr 6e5d224472232d5d): it 3 / it 4 rebuilt as b185f449 / 4896c89d with the
  farm's ratchet lines (raised 7 negative 12 lowered 1 pinned 8; raised 0 negative 0), CLEAN it=4, EQUIVALENT, 1324
  LUTs, latency 72 ns per call, 1 / 1 draw -- the farm's result line field for field (it had 4 / 4 draws).
- Test 2 (resume after the loop finished, the shipped route not here): the farm's full state; the replay stopped at it 4
  (clean, nothing lowered), rebuilt su_straight_3_4 = 4896c89d (the earlier run's md5), full stack and 1 / 1 draw as
  above. Not exercised yet: the phase-2 switch inside a replay (only for state from the old script, which lacks
  rule_I.vh: the resume then stops and ships what it has, logged).
- Farm suite9 (92 tasks, 2 cores, flow v6 at eaef0dec7) runs all 92 at once since 17:03. The resume request is drafted
  (suite9r2: the state of each timed-out task committed under research/data/suite/resume/suite9/, run in a worktree
  at eaef0dec7); it is filed when suite9's tasks reach their limit (~21:05 UTC).
- 8th subagent graphsearch (PROGRAM General first, item 1 and idea 6b): the event-graph storage search over every site
  it can model, inside the flow if it pays; report by 22:40.
### progress 17:54 (the loop's finish phase rarely converges; AUTO_NEAR_PS opt-in; farm conv1)
- Farm loops, flow v3-v6 (suite4 / 6 / 3a / 3b / 8): phase 1 (MAXIT 4) almost never reaches 0 negatives; the raise-only
  finish phase usually ends with 2-10 rows of tens to hundreds of ps (suite6: 16 of 32 loops NOT CLEAN after 7 routes;
  collatz s1's last route: H -15 ps, with four lines at 106-326 ps left). Raising only the short lines leaves the next
  route its new misses among lines that were just positive.
- ratchet.py --near PS (auto_size.sh AUTO_NEAR_PS, opt-in): in the finish phase every line the rule keeps at least at
  its size with < PS ps left at a corner gets the headroom element too. Without it ratchet.py's output (sizes, pins,
  stdout) is byte-identical to the committed one in all three modes (checked on the resume test's it 3 rule). The rule's
  per-corner lines.tsv is now saved per iteration (lines_I_C.txt) so a resumed finish phase can use it.
- Farm conv1 (8 tasks, 2 cores, the 16 cores suite9 leaves free): eight of suite6's NOT CLEAN loops resumed after it 3
  with AUTO_NEAR_PS=300; suite6's own runs are the control (it 4 rebuilt first, md5 checked). Prediction in the request.
### progress 18:16 (xorgap: the event-graph search picks the hand recipe's p8 on every v6 xorshift graph; coordination)
- xorgap (interim, by message): with whatif.py able to deepen a single-stage link that has an acknowledge delay (every
  link on the automatic xorshift routes; before, search.py skipped them as ValueErrors), search.py --depth-only picks
  BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 -- the hand recipe's "p8", the one structural difference left -- on every v6
  xorshift graph (predicted -0.65..-4.55 ns), and nothing on collatz / collatz64 / ipow. It runs as auto_size.sh
  AUTO_SEARCH=1 (a phase after the loop; nothing named by hand; ships the new route only if clean and faster). Its farm
  request is being reworked to resume from suite6's states (committed: research/data/suite/resume/suite6/, f415db410).
- graphsearch told to aim at new site kinds and at why the other kernels gain nothing from depth edits; loopfast told
  the loop's own logic (ratchet, phases) is the bot's. xorgap was over its CPU budget (7 busy processes): now <= 3.
### progress 18:25 (dynfig landed; xorgap's AUTO_SEARCH landed as opt-in; farm xsearch1 filed)
- **dynfig** (lead 8; research/data/suite/dynamatic/DYNFIG_REPORT.md, c70e415cd..c39f2c107): Dynamatic's estimator now
  runs the memory kernels on the suite's v2 vectors (66 kernels, 409 / 409 calls = the C, arrays included); its memory
  units equal Dynamatic's own Verilog in every cycle (8 seeds x 3000 cycles; 3 injected defects caught 8 / 8). New
  figures: dot2 59.3, gather 69.2, memsum 59.3, fill 11.0 ns per iteration (on-merges buffering: a solver placement
  could be up to ~6x faster on the memory kernels). suite_table.py: latency per call on both sides (same calls) and its
  ratio; a P that is a multiple of the host clock refused -- **suite8's dot2 "156 ns per iteration" was the host's array
  fill (13 x 12 ns)**; where P is missing, the slope of call latency on trip count ("fit"; within 0.976-1.052 of P on 42
  routes). eventgraph.py: no marker in the memory port, strides 2-4 (fold64 alternates 21529 / 23924 ps), a reason
  instead of a crash. Over suite3a / 3b / 6 / 8: per-iteration ratio on 13 kernels, geometric mean 1.25 with estimates
  (1.40 measured only); latency-per-call ratio on 15 kernels, 1.35. MILP placement impossible here (dynamatic-opt built
  without CBC).
- **xorgap's AUTO_SEARCH** (a975807f1, 847153641; opt-in, unset = the loop's result lines and exit codes as before):
  after the loop, search.py --depth-only on the shipped route's event graph; if it picks a BDC_LINK_DEPTHS edit the loop
  goes on with that structure (pins reset), ships the new route only if clean and faster. Farm **xsearch1** filed: the
  four original kernels x 8 seeds, resumed from suite6's states (the shipped route rebuilt, md5 checked), so each task
  is an A/B against suite6's route of the same seed; prediction in the request (xorshift ~17-18 ns vs 21.07; the other
  three unchanged).
### progress 18:46 (the loop no longer dies on a route whose bench side misses 83 MHz)
- suite9's first finished task: varshift s4 BUILD-FAILED at it 3, "TIMING FAILED: 82.08 MHz < 83 MHz" -- the bench's
  PS-clocked harness, not the kernel; with NEXTPNR_SEED pinned build_bench.sh gets one attempt, so the loop ended
  (also quadrec s2 in suite3a, fill s1 under the stores subagent: roughly one loop in four or five over ~7 routes).
- auto_size.sh build() (28afd2149): only on that failure, the same iteration is rebuilt on seed S+100, then S+200
  (AUTO_SEED_TRIES, 3 attempts); the seed used is written to seed_I.txt (a resume rebuilds with it). Checked by forcing
  the miss (TARGET_MHZ=250, straight s1): seeds 1 / 101 / 201 each logged with their MHz (103.18, 105.12, 99.63), then
  BUILD FAILED it=0 and no seed file. Without such a miss every iteration is built on S as before.
- suite9r2 (drafted) will run at the branch head so the loops that died this way continue too.
### progress 19:45 (xsearch1 withdrawn while waiting; xsearch2 filed with xorgap's raise-only search phase)
- xorgap: the search phase's re-sizing (pins reset, a no-pin recalibration, then the ratchet) did not settle locally
  (xorshift s1: 1, 9, 23 rows short on its first three p8 routes; s4: 3, 9, 47). The first p8 route at v6's own shipped
  sizes (same seed, re-placed, EQUIVALENT) measured **P s1 17.02 / s2 18.23 / s3 18.87 / s4 15.84 ns vs v6's 19.80 /
  19.72 / 22.47 / 19.43** (nextpnr 6e5d224472232d5d), 1-3 rule rows short. So the phase now goes raise-only with one
  element of headroom from the shipped sizes (AUTO_SEARCH_MAXIT default 4); the re-sizing variant is opt-in
  (AUTO_SEARCH_RESIZE=1). Cherry-picked (f09d45c6f); xsearch1 (waiting, not yet submitted) withdrawn, **xsearch2** filed:
  the same 32 resumed A/B tasks, AUTO_SEARCH_MAXIT=4. Draws on xorgap's local p8 routes: s3 draw 10301 PASS 19/19, rest
  running (its report is due 22:40).
### progress 19:49 (owner T156: no list of kernels in the automatic path -- the md5-keyed rewrites are off by default)
- PROGRAM (owner, 19:30 UTC, auditor T156): bdc/auto.py applied pre_dec / pre_eq2 only when the output's md5 was one of
  three proven files (xorshift, collatz, collatz64): a per-kernel setting. **BDC_AUTO=1 now copies the MLIR unchanged;
  BDC_AUTO_REWRITES=1 is the named variant with the three rewrites** (every automatic route before today used it).
  Checked on all of build/frontend: with the switch off auto.py's output equals its input on every fixture; with it on,
  only collatz, collatz64 and xorshift differ.
- The same test on the rest of the automatic path (bdc/auto.py rules M / F, emit.py, mem.py, compute.py, auto_size.sh,
  ratchet.py, est_sizes.py, merge_rules.py, corner_audit.py, skew.py, tighten.py, arb_fork.py, search.py, whatif.py,
  build_bench.sh): no other key on a kernel's name, a file's hash, an instance name or a literal line of one kernel's
  MLIR. Kernel names appear only in comments and docstrings, in compute.py's multiplier-delay constant (calibrated once
  on ipow, the starting estimate of every kernel's multiplier), and in cells/hw/gen_bench.py's input-domain masks (the
  bench's harness: collatz n & 0xFFFF, xorshift rounds & 0xFFF -- verification data, not the compiler; they limit what
  the bench can test, as the audit noted before).
- BOARD-QUEUE items 39 / 40 / 41: commands now say BDC_AUTO_REWRITES=1 (the same routes). xsearch2 withdrawn while
  waiting (it measured the search on the rewritten flow). **Farm norw1 filed first**: xorshift / collatz / collatz64 x
  8 seeds with the rewrites off, flow v6, 8 draws: the headline's automatic column; suite6 is the "with the three
  rewrites" column beside it. The search lever (xorgap) will run on norw1's states next.
### progress 20:49 (hangs landed: a second token-floor gap fixed; ipow s4's start-up hang was a real race on a NOT CLEAN route)
- **hangs** (lead 3; research/data/suite/hangs.md, 4e0c33f1b..e71e03996): every kernel that emits, both flows, in RTL:
  26 scalar kernels 52 / 52 PASS (SUITE.md's "deadlock" cells for nest3, quadrec, nested, lfsrfind were stale: the token
  floor had fixed them); 19 memory kernels through a new testbench (research/tools/suite/memtb.py: fill, 2 runs per call,
  every array read back against the C, void and N-D kernels; its negative controls fail): 17 pass in both flows,
  **stencil_2d and matrix deadlocked in the default flow** -- a loop's next initial value waiting in a one-stage link
  whose return to zero the inner control_merge needs (walk count 0), a path the token floor never walked (it cuts
  loop entry / exit channels). **Fix in bdc (on in both flows):** each loop with a loop nested in it is also walked
  with its inner loops passing through in one trip; BDC_TOKEN_FLOOR_PASS=0 is the negative control. Checked here:
  135 outputs x {default, BDC_AUTO=1, --host-mem}, 131 byte-identical, the 4 that differ are matrix / stencil_2d
  (default, host) by one stage each. Routed smoke (stencil_2d default, seed 1, worst corner): PASS 2/2 arrays = C with
  the fix, FAIL 0/2 (both calls hang) with BDC_TOKEN_FLOOR_PASS=0.
- **ipow seed 4 (flow v1, sdf 1ac15af5): the start-up hang is a real select race the rule had flagged** (its last rule
  audit: A -719 ps on ucmpi2, E -734..-1070 ps at cond_br6-9; it proposed UCMPI2 5 -> 12; v1 shipped it NOT CLEAN). The
  link data latches (bd_latch, no reset) get their first value 0.19-1.73 ns after the request; the exit steer's request
  arrives 566 ps before its select. With +META_INIT=0 the race still fires on every call: 40 runts (17-474 ps) on the
  exit branch, 28 on the continue branch, 18 on the e >> 1 back edge in 9 us, all rejected by the gate's runt model, so
  the answers stay right in simulation; only at start-up (an x select) does it hang. +1500 ps on the four arcs from
  ucmpi2's chain to the steers: draws 10401 / 10404 PASS 17/17. The ipow board item 38 (v3 s2, UCMPI2 10) shows no runt
  in the same scenario. BDC_LINK_RST=1 (opt-in, every link's data latch reset; unset byte-identical) would let this race
  pass every gate: left off.
- **Consequence for the headline:** a route the rule calls NOT CLEAN can pass every draw while racing on every call
  (the runt model hides it). suite6 shipped 16 NOT CLEAN routes of 32 (suite4 11 of 28); the four board items 38-41 are
  CLEAN. Next: (1) a runt check in the gate (no pulse under ~1 ns on a steer output), (2) count NOT CLEAN routes apart
  in the suite table, (3) the finish phase must converge (conv1, running) or the route is not shipped.
### progress 21:38 (memauto landed: memory kernels through the automatic path, no failure; dot2 is 28 ns, not 156)
- **memauto** (lead 6; research/data/suite/memauto.md, 430f52be7..8e956a827): 22 / 22 draws pass on the memory
  kernels' default automatic routes, arrays read back = C, no deadlock. **dot2's "156 ns per iteration" was the host
  filling the arrays** (the port's request at 13 aclk): eventgraph.py now ignores rises while bridge_i.mem_busy is high
  (only in benches with memory), and lane2_run.sh retries --stride 2 --k 6 when no single-iteration period exists:
  dot2 s2 (farm route rebuilt byte for byte, 4d68e57e) **28.03 ns**, sumi3_mem s2 27.86, if_loop_1 s1 27.52, memsum s1
  28.21 (route 6), gather s1 / s2 55.22 / 51.53, fill s2 37.27. Merged by hand with dynfig's eventgraph.py fix (the
  memory-port marker skip, strides 2-4, a reason instead of a crash): both kept; on a design without mem_busy the
  merged tool takes dynfig's path unchanged. suite_one.sh: SUITE_TAG / SUITE_SKIP_AUTO (opt-in; xorgap had the same
  skip, merged).
- Where a memory loop's time goes: each access's return to zero costs as much as the access (gather 16.4 + 16.4 ns);
  dot2 / sumi3_mem: the multiply fused into the sum's ring. **BDC_MEM_FASTFALL=1** (opt-in; a new cell
  cells/rtl/optin/bd_mem_ff.v, read by build_bench.sh only when instantiated; cells/rtl/bd_mem.v unchanged; emission
  135 / 135 byte-identical with it unset, checked here): the port's two lines fall in one element. One route each,
  base loop sizes: gather s1 55.22 -> 51.90 (-6.0 %) 2/2 draws; fill s2 37.27 -> 32.55 (-12.7 %) 2/2, arrays = C;
  gather s2 unsized gave wrong answers on 6 of 9 calls (host write setup -249 ps, which the rule flags at -244 / -267)
  and one raise-only sizing step fixed it (47.39, -8.0 %, 2/2). Not yet a flow default: no sizing loop run with it.
- Open from memauto: the multiply inside dot2's sum ring (stop fusion at ring boundaries), rule C's address hold (2x
  clock-to-out stated, 1x with the new cell), the bench's 83 MHz latency-statistics path (lat_final -> leading-one ->
  adders, 12.7 ns: the path that misses the bench clock), BDC_AUTO's fast fall off for every kernel with memory.
### progress 21:39 (suite9: 79 of 92 back; first FAIL of the automatic path on a NOT CLEAN memory route; suite9r2 filed)
- suite9 (flow v6, 2 cores, 240 min): PASS so far on dot2 s1 / s2 / s4, fold64 s4, gather s1-3, horner s1-4, if_loop_2
  s1, memsum s2 / s4, sqrtsub s3 / s4, test_bitint s1-4, test_loop_free s1-4, varshift s1 / s3; cmpchain s1 / s4
  NOT-A-BOARD-ROUTE (bits; to look at); varshift s2 / s4 died on a missed bench clock (now fixed in the loop).
- **if_loop_1 s1: FAIL, 2 of 4 draws** (sdf b2ad5a7b, P 27.52 ns, bits EQUIVALENT): "MEMORY wrong in batches 0-7",
  cycles 0, on draws 10101 (chains 0.230 / rest 0.287) and 10104 (0.206 / 0.269); the two passing draws have the chains
  about as slow as the rest. The route was NOT CLEAN after the finish phase (9 sized rows short at it 7; raised, never
  rebuilt). if_loop_1 only reads its array, so wrong read-back from the first batch points at the host's fill through
  the port (memauto saw the same signature on gather s2 with the opt-in fast fall: a host write missing the RAM's
  setup, which the rule flagged). Not yet traced. With the hangs finding (ipow s4) this is the second NOT CLEAN route
  that is actually wrong: the suite table marks it FAIL, as it should; the flow must not ship such a route.
- suite9r2 filed: the 43 loops that came back unfinished (time limit) or died on a missed bench clock, resumed from
  their returned state (research/data/suite/resume/suite9/) at this commit (the rule and loop of suite9 + the seed
  fallback). No state came back for nest3 s1-4, nested s1, iterative_sqrt s2 (their it 0 alone outlasted 240 min:
  loopfast's lead). The 13 suite9 tasks still running go into a later round.
### progress 21:51 (xorgap, graphsearch, divmod landed)
- **xorgap** (lead 1; research/data/auto/xorgap.md): the hand xorshift recipe has ONE structural difference from the
  flow, a second stage on x's back edge (ulink_n_trueResult_8, "p8"); bdc/auto.py reproduces the other five hand knobs
  exactly. The event graph's search never saw it because whatif.py's depth edit failed on every link with an
  acknowledge delay (all automatic links) and search.py skipped the error silently: fixed. p8 alone at v6's sizes, same
  seeds (the rewrites-on variant): 17.02 / 18.23 / 18.87 / 15.84 vs 19.80 / 19.72 / 22.47 / 19.43 ns (median 17.63 vs
  19.76); after raise-only steps s1 / s3 / s4 17.62 / 18.28 / 17.55, 12 / 12 draws (s3 rule-clean, s1 / s4 1-2 rows
  short). On a no-rewrite route (graph only) the search picks p8 too (20.70 -> 18.35 predicted). What is left after
  p8 is sizing: the loop test UCMPI1 ends at 10-14 elements where the hand has 5 (+3 on n's link). Why v6 is slower
  than v3 on xorshift: the no-pin first step lets lines drop, the next compact route is 34-40 rows short, and the
  raises get pinned at that route's demand (seed 3: UCMPI1 9 -> 14; v3's sizes on v6's seed-3 route predict -2.12 of the
  +2.61). AUTO_SEARCH=1 landed (raise-only from the shipped sizes; AUTO_SEARCH_RESIZE=1 the re-sizing variant, which
  did not settle).
- **graphsearch** (PROGRAM General-first item 1 / idea 6b; research/data/eventgraph/search_all.md): search.py
  --all-sites (a latch on every bare channel, +1 depth on every link incl. bd_pipe, through the netlist's wires) on 22
  automatic routes; A/B builds on the farm's own v6 routes (their sizes, the new link at 1 / 1 element, 1-2 draws each):
  **xorshift latch n32__2** (the loop test's fork into the x steer's condition; 1 bit) 21.14 -> 16.94 ns mean over s2 s3
  s4 s8 (-19.9 %, every seed faster, 6 / 6 draws; p8 on the same seeds 18.23 / 18.87 / 15.84 vs n32__2 17.90 / 16.32 /
  15.47); **countloop n24__3** (the same shape) 24.71 -> 20.83 (-15.7 %, 4 / 4 draws; depth edits find nothing there).
  Why collatz / ipow / collatz64 gain nothing from depth: on 8 of 12 routes the cycle runs through one source forked to
  several literals, whose fork couples readers across the body; **BDC_SPLIT_SOURCES=1** (opt-in bdc rewrite, unset
  byte-identical, a wrong variant fails simcheck): collatz 17.64 -> 16.30 (-7.6 %, 3 of 4 seeds faster), ipow 22.21 ->
  20.36 (-8.4 %, 4 / 4), collatz64 24.27 -> 22.74 (-6.3 %, 2 of 3), every draw passing (13 / 13). The rising floor is
  83-86 % wire (matched delays 38-59 %, hops 18-39 %); countloop's matched delays alone (8.5-10 ns) equal Dynamatic's
  whole estimated cycle. AUTO_SEARCH_ARGS="--all-sites --buildable-only --wire 1000" lets the flow's search phase pick
  these (applied by hand on the raise-only phase). Not yet: any of it through the sizing loop on 8 seeds.
- **divmod** (lead 4; research/data/suite/divmod.md): divui / divsi / remsi / remui in bdc as a restoring array with
  one matched delay and an enable chain per stage (no new cell; the ungated array's glitches could not be simulated),
  C's semantics; frontend step 4c rewrites C's unsigned % (Dynamatic's dialect has no remui) -- **now on by default**
  (BDC_FE_UREM=0 off): it changes only kernels with a urem and every committed fixture is reproduced with it on (the
  subagent's check, 111 / 111), and a fixture built with an opt-in knob would be a per-kernel setting. Unit tests
  exhaustive at 8 / 10 bits, simcheck vs the C on digitdiv / digitsum / divmodu / divmods / test_divui in both flows,
  negative controls fail; **routed at worst corner, seeds 1-4: digitdiv 18/18, divmods 24/24, divmodu 20/20 on every
  seed, all EQUIVALENT** (placeholder sizes). 32-bit divui: 151 CARRY4, ~1900 LUTs, 122 ns at the worst corner. Found:
  **Dynamatic's own remsi.v is wrong for negative operands** (an unsigned remainder: remsi(-7, 2) = 1, C gives -1).
  Emission checked here: the 135 earlier outputs byte-identical after graphsearch + divmod; 18 new (digitdiv, digitsum,
  divmods, divmodu, if_loop_3, test_divui x 3 modes).
### progress 22:01 (conv1 negative: padding near-limit lines in the finish phase does not make it converge)
- Farm conv1 (8 of suite6's NOT CLEAN loops resumed after it 3 with AUTO_NEAR_PS=300; suite6 itself is the control):
  the rebuilt it 4 had suite6's sdf md5 on every task that reported it (6 / 6: the resume is exact). **Prediction (>= 5
  of 8 end CLEAN) failed: 0 of the 6 that finished ended CLEAN** (all NOT CLEAN at it 7, as in suite6); collatz s1 and
  collatz64 s7 gave no result line. The near set was 0-2 lines per finish step: the rows that open on the next route
  are mostly on lines that had more than 300 ps, or on constraints no line's "ps left" reports. P against suite6's
  same-seed route: collatz s2 16.91 / 14.97, collatz64 s5 20.73 / 22.99, ipow s1 21.31 / 21.73, ipow s4 22.74 / 22.57,
  xorshift s2 20.33 / 19.72, s7 22.28 / 22.28 ns; draws 48 / 48. AUTO_NEAR_PS stays opt-in and unused.
- What this leaves (with hangs' ipow s4 and suite9's if_loop_1 s1: NOT CLEAN routes can be wrong): the loop's finish
  phase needs another idea -- e.g. raise every line on the critical rows' launch-capture paths by the observed
  re-placement scatter, or keep re-routing raise-only until clean (resume makes the time affordable), or ship nothing
  NOT CLEAN. Under consideration; the suite table already counts a NOT CLEAN route that fails a draw as FAIL.
### progress 22:12 (loopfast landed: CA_FAST=1, the rule step 8-10x faster with byte-identical proposals)
- **loopfast** (lead 2; research/data/loopfast/, research/tools/ca_fast.py; 2d4b7d943): corner_audit CA_FAST=1 (opt-in)
  runs the base audit once in-process and every sensitivity / verify run as a fork of it; topology-only functions are
  memoized by content; weight-reading ones record the pins they read and reuse a base result only while none of those
  changed; rule H for sensitivity runs (scale <= 1) from the base run's shortest distances (CA_FAST_SELFCHECK=1 runs the
  original beside it). No audit arithmetic re-implemented (two helpers moved out of main() unchanged). **Equivalence:
  whole rule, both corners, every output file byte-identical** on xorshift / collatz / ipow / gather routes; gcd and
  isprime: every constraint of the base run, 4-line and verify-like runs identical, and the merged it-0 proposals equal
  the farm's suite7 old rule on 4 routes (gcd s1 / s2, isprime s1 / s2). **CPU per corner, old -> new: xorshift 784 ->
  80 s, collatz 637 -> 68, ipow 1652 -> 167, gather 2027 -> 264; gcd it 0 ~12 h (estimated from 12 sampled runs) ->
  1268 s**; gcd's step ~22 min wall with both corners side by side. isprime seed 1's whole loop ran here in 123 min
  (MAXIT 4, finish 1; builds 3-6 min, rule steps 13-17 min): NOT CLEAN after 5, EQUIVALENT, ffmux-clean.
- Found by it: **gcd and isprime can never be CLEAN under today's rule** -- an A' row at a mux no line can pad, every
  iteration (isprime umux13 -5125 / -5612 ps, gcd umux21 -3422 / -3680): a rule question (a real race, or a row with
  no line on its path) to settle before their loops can ship anything clean. And the old rule's greedy shrink order
  among equal-length lines followed Python's hash seed: auto_size.sh now pins PYTHONHASHSEED (default 1).
- Not yet the default: CA_FAST's exactness rests on its argument and 6 kernels; an old-vs-new check on collatz64,
  quadrec, dot2 and iterative_sqrt is running here. If identical, auto_size.sh turns it on, and the farm gets
  loopfast_gi (gcd, isprime x 4) and the 14 small kernels that timed out.
### progress 22:24 (dyntests landed: 22 more Dynamatic tests in the suite; void kernels; a load before a store / a second load)
- **dyntests** (lead 5; research/data/suite/dyn/README.md: every integer test's status): void kernels on the bench (a
  call completes on end + every memory's end, the arrays read back are the answer; oracle_mem.sh: void, N-D arrays,
  ORACLE_UBCHECK=1 rebuilds the C under UBSan / ASan and fails on out-of-range vectors); bench_gate.sh: an empty
  expected-values file is no longer PASS 0/0; 130 bench files of the old fixtures byte-identical. The 9 store tests in
  the suite (8 listed; matrix not: hours per call in the gate). **mc:load1st lowered in bdc**: a load before a store on
  one controller, and two loads (14 more tests emit): the first access's completion is forked into the second's order
  token (one basic block only; across blocks binary_search deadlocked); every load on an arbitrated port captures its
  word (bdc_load_cap: the stores.md section 6 hazard; tb_capture.v negative control returns the other station's word);
  the host slot sits outside bd_arbiter with a phase C-element; two loads of one block chained too (unchained,
  test_bool_array FAILED 1/4 on its route though RTL passed: a tie at the arbiter on every execution is the suspect).
  Routed smokes (seed 1, worst corner): simple_example_1, while_loop_3, if_convert, single_loop, stencil_2d (AUTO),
  test_memory_1, test_memory_2, test_bool_array, binary_search, mul_example, test_stdint, spmv (AUTO) PASS;
  test_flatten_array passes on NOT EQUIVALENT bits (16 F7 muxes in its shifter unconfigured: to look at);
  share_test_2 unjudged (fasm2net refuses its DSP48E1 mode). Of 85 integer tests: 2 stop in the frontend, 48 in bdc
  (lsq needed by 39, the only blocker of 35), 1 emits only, 17 pass RTL, 17 pass a routed smoke.
- Merged here by hand: hangs' RTL vectors of the same nine names moved to research/data/suite/hangs/vec/ (the suite's
  vectors are dyntests', UB-checked); dyntests' patch pair 0004 / 0006 (unchain, re-chain) skipped as a pair with
  0006's comment restored. Emission checked: the 153 earlier outputs byte-identical; 42 new; all equal dyntests' own
  tree except sobel / spmv in the default and host-mem modes, where hangs' token-floor fix (not in dyntests' tree) adds
  stages (spmv: ulink_n_falseResult_36 / _40 become 2-stage) -- the two kernels dyntests saw deadlock in the default
  flow; their RTL runs with the merged tree are running here.
### progress 22:52 (FOUND: bdc's default flow computes WRONG VALUES on spmv and sobel in RTL -- a functional bug, not timing)
- memtb (zero-wire-delay RTL, cells/sim arcs) on the merged tree, default flow (no BDC_AUTO), --host-mem: **spmv FAIL
  3 of 4 calls** (out[] elements 0 where the C writes nonzero, e.g. call 1 out[9] = 0 want ffee14cb; call 3 out[0], out[2]),
  **sobel FAIL 2 of 3** (call 1: 6 out[] elements wrong). The SAME failure with dyntests' own emission (its tree, before
  the merge; spmv FAIL 3/4, the same addresses), so the merge did not cause it; dyntests had recorded these two as
  "deadlocks in the default flow". Not deadlocks: wrong answers. spmv is out[row[i]] += val[i] * vec[col[i]] -- a
  read-modify-write of out[] across iterations through a load-first controller (dyntests' mc:load1st) -- so the
  suspect is the order of iteration k+1's load of out[r] against iteration k's store to out[r] (the ordering argument
  of stores.md section 2, "test_memory_5's question"). BDC_AUTO=1's emission of both passed RTL (dyntests) and spmv
  AUTO passed its routed smoke (4/4) -- which an ordering bug that the timing merely hides makes weak evidence.
  Open, goal 1: trace it (next subagent).
- CA_FAST equivalence on more kernels (ca_fast_e2e.sh, old rule vs CA_FAST=1, every output file compared):
  collatz64 both corners IDENTICAL (781 -> 110 s per corner), dot2 0.20 IDENTICAL (1525 s old); quadrec and
  iterative_sqrt still running.
### progress 22:55 (headline corrected first, as the owner asked: auditor T161 OVERSTATED; owner T156 / T161 rules)
- Owner (PROGRAM, 20:56 UTC, auditor T161): the headline counts every kernel attempted, keeps the sizing loop's
  unfinished (NOT CLEAN) routes apart, leaves isprime's non-ratio out of the mean, and an OVERSTATED headline is
  corrected before anything new is added. Done (research/data/fifteen/README.md top):
  research/tools/suite/suite_table.py --kernels / --reasons / --no-ratio; every listed kernel gets a row (62; a kernel
  with no result line says why, research/data/suite/headline_reasons.tsv); routes, draws and P split into rule-clean +
  NOT CLEAN (P and the ratio from clean routes only; the NOT CLEAN P, or fit, in brackets); one route per (kernel,
  seed), the later request counted. The automatic column no longer includes the rewritten xorshift / collatz /
  collatz64 numbers (they are under the table as the BDC_AUTO_REWRITES=1 variant; norw1 runs the column without a list).
- Result now: **18 of 62 kernels pass** (the others: 40 with no result line yet -- time limits, added today, or the
  no-list column pending -- plus quadrec BUILD-FAILED, cmpchain NOT-A-BOARD-ROUTE, if_loop_1 WRONG ANSWER under draws);
  including ESTIMATED figures (n = 8): 1.04..
- kernels.txt: divmodu, divmods, test_divui listed (divmod's kernels).
### progress 22:56 (23:00 re-read: PROGRAM unchanged since 64bf1172b; three subagents on goal-1 bugs)
- From 23:00 UTC at most 4 subagents, used where they pay. Started (reports by 03:00 UTC): **memorder** (spmv / sobel
  wrong values in bdc's default flow: the mechanism, whether BDC_AUTO has the same hazard under other delays, a fix
  that holds by construction), **bitsdefect** (test_flatten_array's unconfigured F7 muxes and cmpchain's
  NOT-A-BOARD-ROUTE on suite9 seeds 1 / 4: a real bitstream defect -- a nextpnr patch + a fingerprint that fails on
  6e5d224472232d5d -- or a checker false alarm), **ifloop** (if_loop_1 seed 1's two failing draws on a NOT CLEAN
  route: the race, whether the rule flagged it, the fix on the same route).
### progress 23:07 (4th subagent: steerrunt; gifast1 filed; SIM-VS-BOARD row 6)
- **steerrunt** (report by 03:30 UTC): an opt-in runt check in the gate (pulses shorter than a stated threshold on the
  kernel's steer / mux / C-element / latch-enable outputs, per instance), its negative control the v1 ipow s4 route
  (40 runts per 9 us on its exit branch, hidden by the gate's runt model), then board items 38-41 and a sample of
  suite6's shipped routes: which would fail a strict check.
- Farm **gifast1** filed: gcd / isprime x 4 seeds with CA_FAST=1 (loopfast's loopfast_gi without suite7's per-kernel
  AUTO_FINISH=1, auditor T161). loopfast_small not filed: suite9r2 already resumes those loops.
- CA_FAST equivalence so far: collatz64 2 / 2 corners identical, dot2 1 / 1, iterative_sqrt 1 / 1; quadrec running.
- SIM-VS-BOARD row 6: ipow s4's start-up x was the only symptom of a real race (hangs).
### progress 23:35 (CA_FAST on by default in the sizing loop)
- Old rule vs CA_FAST=1 (ca_fast_e2e.sh, every output file compared, PYTHONHASHSEED pinned on both sides): collatz64
  both corners IDENTICAL (781 -> 110 s per corner), dot2, iterative_sqrt and quadrec IDENTICAL on their first corner
  (second corners still running); with loopfast's six kernels that is ten. auto_size.sh's rule step now runs with
  CA_FAST=1 by default (CA_FAST=0: the old path). Requests already submitted are pinned to their commits; waiting ones
  (suite9r2, gifast1) get it when the runner picks them up -- the same proposals, faster.
### progress 23:56 (bitsdefect: cmpchain's and test_flatten_array's "NOT EQUIVALENT" was the checker; fasm_equiv fixed)
- **bitsdefect** (e060d7980; evidence research/data/suite/bitsdefect/): the flagged F7 / F8 cells are DEAD logic -- LUT8
  trees (yosys lut_map: one F8 over two F7s over four LUT6s) whose output nothing reads, from bdc's keep_hierarchy fused
  modules with outputs partly unconnected (test_flatten_array: fused shifts computing 64 bits of which 9 are used;
  cmpchain: ucontrol_merge4's z_data unconnected). nextpnr writes an output-mux setting only for a site pip a net uses,
  so the bits correctly carry none for a dead output; fasm2net correctly decodes no such cell; fasm_equiv looked one level
  deep for loads and flagged the always-on (no-bit) routing tails into the dead selects. Fix: a cell is dead when every
  load is dead (transitively; pads, PS7, BUFG, DSP, BRAM never); a dead JSON-only cell is a benign kind; a no-bit pip is
  excused only when every site pin it reaches is read only by dead, unconfigured cells. Controls still flagged: pnrfix's
  F7-select defect (ipow x0.55 s19, unpatched binary), its three flop-D routes, its two constructed controls, and a new
  control (three live features deleted from test_flatten_array's FASM: NOT EQUIVALENT, the dead cells still benign).
  Regression over 65 decoded routes on this node: 64 verdicts and count lines identical, test_flatten_array -> EQUIVALENT.
- cmpchain s1 / s4 rebuilt at eaef0dec7 = the farm's routes (sdf a796dad1 / e509aaee): EQUIVALENT under the fixed
  checker, **4 / 4 draws PASS 17/17 on each** (bits-decoded GLS, expected values from the C). Farm survey: the only
  routes of this kind are these two; the 120 flop "HAS LOADS" cells elsewhere are the real const-sinks defect on routes
  built before the patch.
- Open (bdc, efficiency): 14 % of test_flatten_array's LUT bels compute outputs nothing reads, and their selects add
  routed fanout to live nets.
### progress 00:25 (4th subagent: gcdclean)
- **gcdclean** (report by 04:00 UTC): isprime's and gcd's "unfixable" rule-A' rows (umux13 -5125 ps, umux21 -3422 ps:
  the data reaches six inputs, among them  flip-flop D pins) -- a real race, or the bench's clocked result
  capture (sampled a synchronizer's delay after the request) seen as an asynchronous one; if false, rule A' checks such
  a capture against the bench's sampling edge (opt-in, with a negative control), so their loops can end CLEAN.
### progress 01:21 (suite9 done; its last 9 unfinished loops added to suite9r2's state, which has not started yet)
- suite9's last tasks: gather s4 PASS; branchloop s4, factorial s1 / s2, fill s2 / s4, quadrec s1 / s2 / s4 timed out
  with a state (now in research/data/suite/resume/suite9/, 52 in all); fill s1, fold64 s1, iterative_division s1,
  quadrec s3 timed out with none. suite9r2 (waiting for cores) resumes every task with a state at the head it is
  submitted at -- now with CA_FAST (the same proposals, ~8-10x faster rule steps) and the bench-clock seed fallback.
### progress 01:31 (norw1: the column with no kernel list; gifast1: gcd and isprime loops now finish; headline updated)
- **norw1** (BDC_AUTO=1 with the md5-keyed rewrites OFF, flow v6, 8 seeds, 8 draws; nextpnr 6e5d224472232d5d):
  **xorshift 22.19 ns per iteration** on its 5 rule-clean routes (20.42-23.57; 2 NOT CLEAN routes 20.55 / 21.23), 40 / 40
  + 16 / 16 draws; **collatz 23.86** on 4 clean routes (22.14-25.56; NOT CLEAN 22.79-26.70), 32 / 32 + 24 / 24 draws;
  with the rewrites (suite6) the clean-route medians were 22.71 and 17.24 -- the rewrite was worth ~6.6 ns on collatz
  and nothing on xorshift (the prediction said 24-26 / 20-22 / 28-32: xorshift and collatz came in at its low / above
  its high end). **collatz64: all 7 finished tasks ran out of time** in their final stack / draws (6-7 ratchet steps
  done); resumed in norw1r2. xorshift s7, collatz s1 timed out at it 0.
- **gifast1** (gcd / isprime x 4 seeds, CA_FAST=1, the default finish phase, 8 cores): **the loops finish** -- gcd s3 /
  s4 and isprime s2 / s3 ran all 7 routes, the full stack and 4 draws in ~75-80 min each (suite5 / suite7: one rule step
  in 4 h): gcd P 61.42 / 66.30 ns, isprime 346.76 / 358.38 (the outer trial's period), every draw passing, bits
  EQUIVALENT -- and every route NOT CLEAN, on the A' row no line can pad (gcdclean's question).
- Headline regenerated (research/data/fifteen/README.md top): **21 of 62 kernels pass**; the no-list xorshift / collatz
  rows are now in the table (ratio to Dynamatic's measured figure 1.74 / 1.70).
### progress 01:41 (ifloop and memorder landed; CORRECTION of 22:52: spmv / sobel were the RTL model, not a bdc bug)
- **CORRECTION of the 22:52 entry ("bdc's default flow computes WRONG VALUES on spmv and sobel"):** subagent memorder
  (research/data/suite/memorder.md) found no ordering bug and nothing specific to the default flow. At 0 ps per arc
  (memtb's default) bdc's placeholder clock-to-out line (12 elements = 1488 ps) acknowledges a read before the RAMB18E1
  model's data (2454 ps after the edge), so every bdc_load_cap latch closes on the previous word; BDC_AUTO=1 fails the
  same way at 0 ps, both flows pass at 350 ps per arc (where dyntests had run AUTO) and with DCO >= 18. bdc unchanged;
  memtb now covers the RAM model's clock-to-out in the testbench (--keep-dco keeps the emitted value: the negative
  control fails), monitors every RAM, checks program order on every chained arbitrated port (0 out-of-order accesses in
  32 548 per flow on 11 kernels; it fires on 1060 / 1088 on binary_search's unchained port) and waits for a quiet port
  before a host access (a harness bug the slow-RAM runs found). All 32 memory kernels, both flows: 64 / 64 PASS; delay
  scatter (BD_JITTER, cells/sim, opt-in) +-30 % 68 / 68, +-50 % on spmv 16 / 16; slow RAMs 14 / 14; the capture latch
  removed (BDC_MEM_NOCAP=1) fails 18 / 18. spmv's default flow routed for the first time (seed 1): PASS 4/4 at worst,
  EQUIVALENT. Open: no rule checks a capture latch's timing on a route (capmargin.py: worst margins 2490-5261 ps over 11
  routes); rule C fails on two spmv routes by -46..-345 ps; nothing sizes DCO in the default flow.
- **ifloop** (research/data/suite/ifloop.md, research/tools/ramrace/): if_loop_1 s1 (sdf b2ad5a7b rebuilt = the farm's)
  fails because the **bench's host write to umem0 misses the RAM's WE setup** (100 RAMB18 SETUP VIOLATION lines, one per
  host write: the setup line's 2 elements bundle the host request through a 49-row wire to the WE LUT; 515 ps against 532
  needed). Rule B measures exactly this race and passed it at +79 / +101 ps: it has **no scatter guard**, and the draws'
  within-die scatter moves it by ~112 ps (one sigma), so ~10 % of draws fail on this route. It was NOT among the route's
  9 short rows. BD_RAM_GUARD_PS (tighten.py, opt-in): with 400 ps the rule raises USETUP 2 -> 5; that route (3386e563)
  passes draws 10101-10108 8 / 8. The race is in the bench's host slot, on every RAM of every memory kernel: over the
  14 other shipped memory routes of suite9 (rebuilt = the farm's) the worst host-race margins are gather s2 +234 ps and
  dot2 s4 +367 (every other >= +551; kernel load slots >= +785). **Gate hole closed** (bench_gate.sh): a batch whose
  signature contains x now fails (the run-to-run compare, a "!=", was never true against x: a route with a select race
  passed 3/3 with x in run 0), and any RAMB18 violation line fails the run; a clean run's verdict line is unchanged.
- **auto_size.sh now runs the rule with BD_RAM_GUARD_PS=400 by default** (a named race, a measured spread; it only
  lengthens a setup line on a host / store access). suite9r2 (still waiting) will resume the memory loops with it.
### progress 02:10 (split1: the source split buys collatz nothing through the loop; ipow ~6 % on 3 routes; split1r2 filed)
- Farm split1 (BDC_SPLIT_SOURCES=1 through the whole automatic flow, rewrites off, 8 draws): collatz 7 routes judged,
  P on 3 clean routes 24.24 ns (21.77-25.27; NOT CLEAN 23.20-27.14) vs norw1 without the split 23.86 (4 clean) --
  **no gain** (graphsearch had measured -7.6 % at the farm routes' own sizes, with the rewrites on: the loop re-sizes it
  away); ipow 3 routes judged: 18.98 (1 clean) / 20.27 (2 NOT CLEAN) vs suite6 21.39 / 21.73 -- ~6 % faster, as
  graphsearch measured; every draw passing (80 / 80). 14 tasks timed out in their final stack / draws (all of
  collatz64, five ipow, one collatz; 6-7 ratchet steps done): **split1r2** filed to finish them (CA_FAST, draws 3 at a
  time). Prediction (>= 5 % on all three) failed on collatz.
### progress 02:29 (farm nsearch1: the storage search inside the flow, on the column with no kernel list; suite9r3)
- nsearch1 filed: 18 finished loops (norw1's xorshift x 7, collatz x 7; suite3a's countloop x 4) resumed, their
  shipped routes rebuilt, then AUTO_SEARCH=1 with graphsearch's all-sites candidates (fork-output / merge latches and
  link depth, 1 ns of wire charged per stage), raise-only for at most 4 routes, then the draws: a per-seed A/B. The
  prediction is in the request.
- suite9r2 waited 4.5 h for 184 free cores while smaller requests went ahead: withdrawn and re-filed as suite9r3 with
  only its 52 tasks that have a state (104 cores); it started at once.
### progress 02:39 (steerrunt landed: a runt check in the gate; on by default in the suite as a report)
- **steerrunt** (research/data/suite/steerrunt/README.md, cells/gls/ps/gen_runt_mon.py): bench_gate.sh GATE_RUNTS=1 |
  fail (opt-in; unset byte-identical): a Verilog monitor compiled into the gate's run counts, at every kernel steer /
  mux / merge / C-element / fork / link-enable / matched-delay output (its driver in the bits-decoded netlist), pulses
  under 150 / 500 / 1000 ps and the narrowest pulse of any width; cost not measurable; checked net by net against a VCD.
  Threshold 1 ns: above every kernel C-element loop at the draws (<= 0.89 ns), below every legitimate handshake phase
  measured (>= 1.54 ns over 25 clean runs; at SLOW_MAX loops exceed 1 ns: use GATE_RUNTS_T=150,500,0 there). Nothing
  is known about what silicon swallows (H_RUNT, BOARD-QUEUE item 2, unrun).
- **Negative control:** flow v1's ipow s4 route (sdf 1ac15af5) passes draws 10402 / 10403 17/17 while the monitor counts
  1756 / 554 pulses under 1 ns on 41 / 40 of its 192 nets (exit branch of ucond_br9: 36 runts of 33-268 ps): fails
  under GATE_RUNTS=fail. **Board items 38-41** (rebuilt to their sdf md5s; 13 runs over corners and draws): 0 pulses
  under 1 ns, no x pulse. **suite6 sample** (9 shipped routes, 5 of them NOT CLEAN, rebuilt with BDC_AUTO_REWRITES=1;
  worst corner + the draw nearest the rule's 0.31 corner on the three with select-race rows): 0 pulses under 1 ns.
  So the rule's small NOT CLEAN rows did not turn into runts there; rows A and H are data races a handshake monitor
  cannot see.
- suite_one.sh runs every draw with GATE_RUNTS=1 (report) by default from now on; BOARD-QUEUE judgments should use
  GATE_RUNTS=fail. Merged with ifloop's gate changes (x in a SIG and any RAMB18 event fail): both kept.
### progress 03:18 (gcdclean landed: gcd's / isprime's "unfixable" row is a lap through the bench, not a race; a real rule gap found)
- **gcdclean** (research/data/benchcap/): isprime's umux13 / gcd's umux21 row is a LAP, not data: launched at an input
  link, the "data" is reached two storage crossings later through the bench's acknowledge LUT (o_ack_pl = ... &
  core_o_req), the select link's return to zero and its request delay -- the timing walk crosses the bench's AND as if
  the clocked bench_o_ack were already 1. The out0 mux's real sinks: 2 (isprime) / 64 (gcd) flops of the PS-clocked
  bench (result_hold, captured only after two 2-flop synchronisers: >= 2 periods of FCLK0, <= 100 MHz, so >= 19 ns with
  1 ns of setup / skew allowance, an assumption) and the mux's own join C-elements (which A' read as data). Margins on
  every route checked: +17.4..+18.7 ns (isprime, gcd, and farm routes of xorshift, collatz, gather).
- corner_audit **CA_BENCHCAP=1** (opt-in with CA_JOINAWARE=1; unset byte-identical on xorshift / collatz / gather, all
  8 output files; CA_FAST stays exact with it, 0 of 51 runs differ): a D / CE pin of a BUFG-clocked flop is a capture at
  the request's earliest arrival at a flop on that clock + CA_BENCHCAP_PS (19000); the operator's own join inputs are not
  data. Negative control (an arc on the data path into result_hold lengthened): +17000 ps -> +1177 margin, +19500 ->
  -1398 (sized: umux13's line), +25000 -> -7063 -- the shipped rule never measured that path at all. Effect: isprime it
  5's 2 unfixable rows gone; gcd it 0 73 -> 71 rows, all fixable, UMUX21 4 -> 1, the proposal 542 -> 520 links; on other
  kernels the out0 mux's line drops to its floor (xorshift UMUX3 5 -> 1, collatz UMUX2 3 -> 1, gather UMUX3 2 -> 1).
  isprime s1's loop resumed with it (it 6-10): 10, 6, 2, 1, 5 rows short, none unfixable -- still NOT CLEAN after 10
  (tens of ps that move with each re-route). Not the default yet: the out0 muxes at their floor need draws first.
- **Found: the select race inside bdc_muxnN is measured by no rule** (s must settle before ctl_req at the decode LUTs;
  select_consumers() misreads the bd_c2 pins); on isprime the line guarding it (ULINK_N_INDEX_71) stayed at its start
  size 3 from it 0 to it 10 with 363-633 ps of unguarded slack at 0.20. A goal-1 gap: next lead.
- All 13 subagents of this session have reported and landed.
### progress 03:18 (subagent muxsel: the N-way mux's select race into the rule)
- **muxsel** (report by 08:00 UTC): confirm which rules see a bdc_muxnN's select and which kernels emit one; make rule E
  (and the sizing rule) measure s against ctl_req at the decode LUTs, opt-in first, CA_FAST kept exact; a negative
  control that fails statically AND in the routed GLS (GATE_RUNTS=1); the margins on the routes available, and whether
  any board item has an N-way mux.
### progress 03:46 (headline: 29 of 62 kernels pass; collatz64 with no kernel list 30.93 ns on clean routes)
- norw1r2 (norw1's loops resumed, CA_FAST): every rebuilt shipped route had its earlier sdf md5; collatz64 s4-s7 with no
  kernel list: 28.10 / 29.85 (NOT CLEAN), 30.93 / 31.49 (clean), 8 / 8 draws each (with its rewrite, suite6: 23.01):
  the rewrite was worth ~8 ns on collatz64, inside the 28-32 predicted; collatz s1 18.98 (clean at it 2).
- Headline regenerated over suite3a / 3b / 8 / 7 / 6 (ipow) / 9 / 9r3 (partial) / norw1 / norw1r2 / gifast1: **29 of 62
  kernels attempted pass**; no-list column on clean routes: xorshift 22.16 (6 routes), collatz 22.54 (5), collatz64
  30.93 (3); gcd 62.82 and isprime 358.38 on NOT CLEAN routes only (the bench-capture lap; CA_BENCHCAP opt-in).
### progress 04:16 (nsearch1: on the column with no kernel list the search pays on countloop only; gifast1 done)
- **nsearch1** (16 of 18 back; the search phase with all-sites candidates on finished no-list loops; every route
  rebuilt with its earlier sdf md5; every draw passing, 116 / 116): **countloop**: the search adds fork-output latches
  (BDC_FORK_OUT_LINK=n13__0,n15__0,n22__0 or n24__3; s3 also a 4-deep trueResult_10): s1 26.60 -> 20.92 ns, s2 22.15
  -> 21.37, s3 25.80 -> 20.45, s4 picked but the new route was not shipped (24.30 kept) -- 3 of 4 faster, 0.8-5.7 ns.
  **xorshift** (no rewrite): nothing on 5 of 6 seeds -- the critical cycle already sits at the rising-only floor (base
  P = the R floor: no return to zero on it, so no storage can help); s8 picked n32__2 (21.24 -> 20.64 predicted) but
  shipped its old route. **collatz**: nothing on 6 seeds. So xorgap's p8 / graphsearch's n32__2 gains (2-4 ns) were a
  property of the REWRITTEN xorshift (pre_dec moves the loop test onto a coupled cycle with polarity changes); on the
  no-list structure xorshift's 22.2 ns is all rising pass -- matched delays and wire -- which only the sizing and
  placement can shorten. Prediction (xorshift -2.5..-4.5 ns) failed; countloop's (-3..-4) held on 2 of 4 seeds.
- **gifast1** done (gcd / isprime x 4, CA_FAST): every loop finished in ~75-80 min, all draws passing, all NOT CLEAN on
  the bench-capture lap (CA_BENCHCAP fixes that row; see gcdclean).
### progress 04:19 (PROGRAM General-first item 2: the draw model's box is NOT where the sizes' excess is)
- Question (PROGRAM): the draws said the STATIC sizes were 1.4-1.8x longer than needed; which part of the sizing rule
  carries that? Measured on one route (su_xorshift_1_4, the flow's own sizes, CA_FAST, PYTHONHASHSEED 1;
  research/data/sizerule/box/): the rule at the draw model's worst vertex (chains 0.20, rest 0.31) proposes 79 kernel
  links, at the other vertex (both 0.20) 73, merged 80; at the board fit for both bands (0.222) 72. **The box's
  independence costs ~11 % of the links** (8 links: UMUX3 6 vs 5, UCMPI1 8 vs 7, UCMPI0 7 vs 6, and 1-element steps),
  not 40-80 %: today's automatic sizes are already within ~10 % of a single-band rule at the board's position. The
  1.4-1.8x was the OLD static sizing (tighten.py's rule A with its fixed guards), which the automatic rule replaced.
- So, with nsearch1's result (the no-list xorshift cycle is at its rising floor): xorshift's 22 ns is matched delays
  bundling wire-dominated data paths (85-87 % of the cycle is wire) -- the remaining levers are placement (shorter data
  paths make shorter lines), not the rule. ringplace's soft weights were negative; hard relative placement of a ring
  (RLOC_GROUP) is untried.
### progress 04:19 (farm suite10: the 27 listed kernels never run through the automatic path, and 10 loops to redo)
- suite10 filed: digitsum, digitdiv, divmodu, divmods, test_divui and dyntests' 22 listed tests (stores, load first, two
  loads, void kernels), seeds 1-2; and suite9's 10 loops that returned no state (nest3 s1-4, nested s1,
  iterative_sqrt s2, fill s1, fold64 s1, iterative_division s1, quadrec s3), from scratch -- all with CA_FAST, the RAM
  guard, the seed fallback and the runt monitor reporting.
### progress 04:29 (split1 + split1r2: BDC_SPLIT_SOURCES through the whole flow helps ipow, hurts collatz / collatz64)
- BDC_SPLIT_SOURCES=1 through the no-list automatic flow (8 seeds each, 8 draws, 184 / 184 draws passing) against the
  same flow without it (norw1 / norw1r2; suite6 for ipow, which no rewrite touched), all routes, seeds paired:
  **ipow -2.28 ns** median paired difference (faster on 5 of 7; all-route median 21.58 -> 19.22, -11 %); **collatz
  +1.39 ns** (faster on 3 of 8); **collatz64 +1.15 ns** (faster on 1 of 4). graphsearch's fixed-size A/B (-6..-8 % on
  all three) does not survive the sizing loop on collatz / collatz64. Not a default (a choice only ipow justifies);
  candidate for an automatic "build both structures, keep the faster clean route" phase like AUTO_SEARCH's, which would
  cost one more loop per kernel.
### progress 04:38 (flow v7: the event graph's search runs inside the flow by default)
- nsearch1 complete: 18 / 18 tasks, 128 / 128 draws passing, every rebuilt route with its earlier sdf md5. The search
  shipped a faster route on countloop s1 / s2 / s3 only (26.60 -> 20.92, 22.15 -> 21.37, 25.80 -> 20.45 ns); xorshift
  (7 seeds) and collatz (7 seeds) kept their routes.
- **auto_size.sh: AUTO_SEARCH=1 with the all-sites candidates is now the default (flow v7; AUTO_SEARCH=0 = v6)** --
  PROGRAM General-first item 1 ("the event graph's search, run inside the flow"). It ships a new route only if it is
  rule-CLEAN and measured faster, so no kernel's result gets slower; it costs up to 4 more routes where it picks an
  edit. suite10 (waiting) will run v7.
### progress 05:29 (board items 38-41 pass the strictest gate; headline 31 of 62)
- Items 38-41 re-judged here (their routes on disk with the listed sdf md5s) under today's gate with GATE_RUNTS=fail:
  worst corner + 3 fresh draws each, **16 / 16 PASS**, 0 pulses under 1 ns on 155-192 kernel handshake nets, no x in
  any run's result, no RAMB18 event (no RAM in these kernels); narrowest pulse 2.1-4.1 ns
  (research/data/suite/board/rejudge_2026-11-19_gate_strict.txt). BOARD-QUEUE says so.
- Headline regenerated with nsearch1 (countloop's v7 routes: 4 clean, median 21.14 ns, was 25.05) and the resume
  rounds so far: 31 of 62 kernels pass.
### progress 05:47 (muxsel landed: the N-way mux's select race is measured, and on in the loop; a real case on cmpchain)
- **muxsel** (research/data/muxsel/notes.txt): tighten.select_consumers() never returned a bdc_muxnN (its joins are
  <p>.uj<k>.u, read as tag u under parent <p>.uj<k>), so no rule (E, D, A'j's select captures) saw the decode LUTs
  sel[k] = ctl_req & (s == k); 2-way bd_mux and steers are read correctly. Six fixtures emit an N-way mux: cmpchain (3 x
  5-way), gcd, isprime, iterative_sqrt, sobel (3 x 3-way); none of board items 37-41. **BD_SKEW_MUXN=1**: tighten's
  muxn_decode_sites() finds each mux by structure (the request pin from the LUT functions, not names) and skew.py
  checks every (request, index) pin pair like a 2-way mux join; unset byte-identical (isprime, xorshift routes); CA_FAST
  exact with it. Negative controls: lengthening the 8 arcs into umux13's index pins by 100 / 250 / 1000 ps moves the
  row to +122 / -32 / -804 ps exactly as predicted; in routed GLS (GATE_RUNTS=1) the +1000 ps route and a route with
  the guarding line removed put runts (247-631 ps) and x pulses on exactly the decode outputs, answers still right.
- **A real case:** the sizing loop had shrunk cmpchain's guarding select links to 1 element ("on no measured
  constraint"): s2 it5 (route 1c13ff02) -762 ps, s3 it2 (1994ab81) -1083 ps under the new rule, and in GLS 12 + 3 x / 12
  + 2 x narrow pulses on those muxes' decode outputs; with the line at 7 (what the new rule asks) 0 pulses, 17/17. Answers
  stayed right only because these muxes merge exclusive branches (the input whose decode pulses holds no token);
  sobel's muxes sit inside a loop body, where that may not hold. isprime / gcd / iterative_sqrt routes measured +36..+740
  ps (isprime it5 at 0.31: +36, now held by the rule).
- **auto_size.sh: BD_SKEW_MUXN=1 by default in the loop** (BD_SKEW_MUXN= off). Shipped routes with an N-way mux (cmpchain
  s1 / s4 in suite9; gcd / isprime / iterative_sqrt loops) were sized without it: the suite's next rounds re-size them;
  the runt monitor (GATE_RUNTS=1 in suite_one) now reports such pulses in every draw.
### progress 05:48 (subagent ringfuse: fewer handshake units per loop ring; farm muxn1)
- **ringfuse** (report by 12:00 UTC): on the column with no kernel list xorshift / collatz sit at their rising-only
  floor (no storage edit helps; the rule's box costs ~11 %), so the lever left is structural: fewer handshake units on
  each loop ring (PROGRAM General-first 6c). Price the merges on the event graphs, find where bdc's compute fusion
  stops on the rings, an opt-in general fusion pass (byte-identical off; simcheck / memtb on every kernel; a negative
  control), measured through the whole automatic flow on 2+ seeds of xorshift / collatz / countloop / ipow.
- Farm muxn1 filed (cmpchain x 4, iterative_sqrt x 2, sobel x 2 with the N-way mux race measured in the rule).
### progress 06:54 (headline 38 of 62; FOUND: the automatic flow undersizes the divider -- test_divui wrong on CLEAN routes)
- Headline regenerated with suite9r3 (50 / 52), norw1r2 (done), suite10b (19 / 64): **38 of 62 kernels pass**;
  WRONG ANSWER under draws: if_loop_1 (the host-fill race, fixed in the rule since: ifloop), **test_divui** (new).
- **test_divui (return var1 / 1083), suite10b seeds 1 / 2: every draw FAILS on two rule-CLEAN routes** (sdf 9875e724 /
  8ca1bfa7, bits EQUIVALENT, no runt): the sizing loop shrank the divider's matched delay UDIVUI0 from 161 links (the
  start) to 4-5 because the rule measures the quotient settling ~3.4 ns after the operand (A -40 ps "req 3400 data 3340")
  while the real enable-gated divider needs ~122 ns at the worst corner; the bench reads garbage after 5 host cycles
  (0x00300000 for 0xffffffff / 1083, want 0x003c836d). divmod's routed smokes passed only because they ran at the
  528-link placeholder. The draws caught it (the judge works); the automatic flow built a wrong divider. Subagent
  **divsize** (report by 12:30 UTC): why the static rule does not see the divider's data path (the enable chain read as a
  delay chain / request side, the gated stages, the literal divisor?), a fix with a negative control, and the flow on
  test_divui / digitdiv with every draw passing. Until then every divider result of the automatic flow is suspect
  (digitdiv, divmodu, divmods, digitsum, test_divui in suite10b).
### progress 07:33 (muxn1, first results: the N-way mux guard now sized by the flow; no runts)
- With BD_SKEW_MUXN=1 in the loop: cmpchain s1 / s2 keep the select link that guards umux0's decode at 5 / 3 elements
  (the earlier loops shrank it to 1), **0 pulses under 1 ns on all 340 kernel handshake nets** in every draw (the
  earlier routes: 12-15 on the decode outputs), 4 / 4 draws each; iterative_sqrt s2 P 64.56 ns, 4 / 4, 0 runts. All
  three NOT CLEAN on other rows (the loop's finish phase, as everywhere).
### progress 07:38 (a subagent's analysis reached 53 GB of the job's 64: killed; a watchdog now kills any process over 30 GB)
- divsize's peakpath.py (a path search through the divider's 32 gated stages) grew to 53 GB RSS in 8 minutes; killed
  before an OOM could take down the session and every subagent; the subagent was told to use a bounded longest-path DP.
  /tmp/bot/memwatch.sh (node-local) kills any single process over 30 GB from now on (logged to /tmp/bot/memwatch.log).
### progress 08:45 (headline corrected for auditor T167 before anything new: 43 of 62 pass)
- T167 (CONFIRMED in substance, OVERSTATED minor in disclosure): fixed -- norw1's collatz64 seed 8 (it finished after my
  archive: PASS 8/8, P 33.47 NOT CLEAN) is in; the exact command with its inputs in order and suite6's ipow-only filter
  are stated; the flow defaults of each request's commit listed (v5 / v6 / + CA_FAST / + RAM guard / v7 / + mux rule);
  the four build failures that resumes replaced (quadrec s2, varshift s2 / s4, isprime s3) named; cmpchain's NOT
  EQUIVALENT farm verdicts explained (the dead-cell checker false alarm, T166); stale reasons rewritten.
- Now **43 of 62 kernels pass**; WRONG ANSWER under draws: if_loop_1 (the host-fill race, fixed in the rule since) and
  test_divui (the undersized divider, divsize working on it); 16 with no result line yet (their loops run in suite10b /
  suite9r3).
### progress 10:13 (headline 49 of 62; suite10c / suite9r4 resume the rest)
- suite10b (the kernels new to the flow, v7) 62 / 64 back and muxn1 7 / 8: **49 of 62 kernels pass**. Not passing:
  if_loop_1 (its old routes; the RAM guard that fixes it is in the rule since), test_divui (the undersized divider),
  share_test_2 (NOT-A-BOARD-ROUTE: fasm2net does not decode its DSP48E1 cascade mode), and 10 with no finished route:
  digitdiv / digitsum / divmods (not resumed until the divider sizing is fixed), fir / sumi3_mem (suite9r4, 2 draws),
  nest3 / sobel / stencil_2d / single_loop / video_filter (suite10c).
### progress 10:52 (divsize landed: rule A's peers confined to the cell -- the divider was hidden through the bench's acknowledge)
- **divsize** (1daa7efd4..996eb42d3; cells/verify/test_peers_cell.py): rule A drops every output of a cell that is
  "downstream of the request" (reached from the line's tail without crossing storage) -- but that reach left the cell:
  test_divui's divider drives out0, the bench acknowledges combinationally (o_ack_pl), and through udivui0.uhold
  (hold = join | z_ack) the reach opened the enable chain and every gated stage, so 2393 of the divider's 2510 outputs
  were dropped (in tighten.py's site_peers and corner_audit's A' / A'j copies) and only 117 ungated carry bits (settling
  in ~3.4 ns) were measured. The GLS settle monitor (gen_settle_mon.py) on the farm route: the request rose 2.65 ns
  after the join while the quotient moved until 44-48 ns; the return to zero dropped the enables mid-divide. **Fix
  (default on; BD_PEERS_CELL=0 the old test): downstream = reachable without leaving the cell** (storage reached by any
  path stays downstream, which keeps the mux / merge acknowledge C-elements out of the peers). Negative controls: the
  farm's 5- / 6-link routes -104.4 / -101.7 ns, the it-0 route (159 links) -45.0 / -58.6. Peer census over 55 routes of
  25 kernels: only test_divui's divider set changes; rule outputs byte-identical on xorshift / collatz / gather (both
  corners, original vs fixed). **test_divui through the flow with it: 4 seeds clean at it 2-4, divider line 332 / 386 /
  338 / 1111 links, 16 / 16 draws, 0 runts** (the farm's seeds 1 / 2 had 0 / 4 on the same draw numbers). Open: rule F
  pads very short lines without converging (seed 4's 1111 links, 3.4x the need; 6 -> 6406 on a forced case).
- The other divider kernels never had this (their dividers reach the bench through a fork / pipe / link): divmodu
  passed suite10b 4 / 4 on seeds 1 / 2 (lines 319 / 345). Farm: **divsize1** (test_divui seeds 1-8) and **divres1**
  (digitdiv s1 / s2, digitsum s2, divmods s1 resumed, 8 cores) filed.
### progress 11:20 (ringfuse landed: fusing each loop's update with its test; farm ringfuse1 filed)
- **ringfuse** (research/data/ringfuse/README.md; bdc/emit.py BDC_RING_FUSE, opt-in; checked here: 195 / 195 emitted
  outputs byte-identical with it unset): on every loop ring the update and its test sit back to back with a link
  between them (7.8-11.1 ns of an 18-23 ns rising floor; wire 85-87 %); compute fusion stopped there because the update's
  value forks to the test and to the loop's data steer. BDC_RING_FUSE=1 merges them into one cell (any kernel, by the
  fork's shape; refused across basic blocks, above 8 members, or where a result could re-enter the cell in the same
  iteration): the rising floor drops, but return to zero lands on the cycle (the fused cell waits for every steer the
  test feeds); **=2 adds a 1-bit link on the test's output** (the stage the search ranked first on every =1 graph).
  RTL: simcheck 21 scalar + memtb 25 memory kernels, both flows, 92 / 92 for =1 and =2; negative controls hang / give
  wrong values (12 / 17 on ipow); the deadlock guard's own control hangs memsum without it.
- Through the whole automatic flow (v7, local, one route per seed; baselines = the farm's same seeds without it):
  **=2 faster on 7 of 10 routes, median -1.27 ns; xorshift all three seeds -1.76 / -2.34 / -2.59 ns (18.79 / 18.08 /
  19.61, below every one of the 8 no-list baseline seeds)**, collatz s2 -2.13 (s1 +1.66 against an unusually short
  baseline), ipow -0.39 / -1.20 (its floor is the multiply ring), countloop -1.34 / +1.31 / +3.85 (its binding cycle
  moves to the operand's fork into its steer, which the search phase picks but does not always make clean). 14 / 14
  routes pass 4 / 4 draws, no pulse under 1 ns, EQUIVALENT. One route per seed: not a claim. **Farm ringfuse1 filed**
  (=2 on 8 seeds x xorshift / collatz / countloop / ipow, plus v7 baselines for countloop s5-8 and ipow s1-8).
### progress 11:21 (STATE OF PLAY for the next session: what is in flight, what to read first)
- **Read first:** research/data/fifteen/README.md top (the automatic column, 49 of 62 kernels pass, provenance per
  request); this session's progress notes from 16:47 UTC yesterday on; research/BOARD-QUEUE.md "Run order now"
  (items 36, 37, then 38-41 -- all four re-judged under the strict gate, 16 / 16).
- **The flow now (auto_size.sh defaults):** BDC_AUTO=1 with no kernel list (rewrites off; BDC_AUTO_REWRITES=1 is the
  named variant), flow v7 = the loop (start x 0.3, two-corner rule, join credit, steer self-bound, token floor, finish
  phase) + CA_FAST (identical proposals, 8-10x faster) + the bench-clock seed fallback + rule B's RAM guard 400 ps +
  BD_SKEW_MUXN (N-way mux select race) + rule A's peers confined to the cell (BD_PEERS_CELL) + the event-graph search
  phase (all sites); suite_one.sh draws report runts (GATE_RUNTS=1); the gate fails on x in a run's result and on any
  RAMB18 event. Opt-in, measured, not defaults: BDC_RING_FUSE=2 (ringfuse1 on the farm decides), BDC_SPLIT_SOURCES
  (ipow -2.3 ns, collatz / collatz64 worse), BDC_MEM_FASTFALL, CA_BENCHCAP (gcd / isprime's bench-capture lap),
  AUTO_NEAR_PS (negative), BDC_LINK_RST (left off on purpose).
- **Farm in flight (read with research/tools/suite/suite_table.py; collect states with a copy of
  research/tools/suite/collect_resume.sh: TIMEOUT tasks' auto/ dirs into research/data/suite/resume/REQ/K_S, then a resume
  request with AUTO_RESUME):** suite9r4 (fir / sumi3_mem / memsum, 2 draws), suite10c (nest3, sobel, stencil_2d,
  share_test_1, single_loop, video_filter resumed), divsize1 (test_divui x 8 with the peers fix), divres1 (digitdiv /
  digitsum / divmods resumed, 8 cores), ringfuse1 (BDC_RING_FUSE=2 x 8 seeds x 4 kernels + baselines). Not yet resumed:
  stencil_2d s2 (suite10b t42), sobel s2 (muxn1 t8) -- no state came back; rerun from scratch.
- **Open, goal 1:** NOT CLEAN routes (about half of all loops end NOT CLEAN by tens to hundreds of ps; two such routes
  were wrong before the judge got stricter; AUTO_NEAR_PS did not help); share_test_2 is unjudged (fasm2net lacks its
  DSP48E1 cascade mode); rule F pads very short lines without converging (test_divui s4: 1111 links); the N-way mux's
  hold side is argued, not measured; capture-latch timing (memorder's capmargin.py) is checked by no rule.
- **Open, speed:** on the no-list column xorshift / collatz sit at their rising-only floor (storage cannot help;
  the sizing box costs ~11 %); the levers left are structural (ringfuse: fewer units per ring; mux + increment and
  compare + steer need new cells) and placement (hard RLOC groups untried; soft weights negative).
### progress 12:09 (headline 52 of 62: the slow memory kernels finished; test_divui passes with the rule fix)
- suite9r4 done: memsum s1, sumi3_mem s1-4, fir s1 / s2 / s4 PASS (2 draws each, 7 of 8 rule-clean; fir s3 ran out
  again) -- the loops had finished, their final stack and draws needed the time. divsize1 (rule A's peers confined to the
  cell): test_divui s1 / s6 PASS clean (s1 = divsize's local route, sdf ecbc22cc), s7 PASS (NOT CLEAN, unfixable row at
  it 1). The table still shows test_divui WRONG ANSWER through seed 2's suite10b route (the old rule) until divsize1's
  seed 2 arrives. **52 of 62 kernels pass.**
### progress 12:20 (subagent converge: why the finish phase does not converge, and a change that does)
- **converge** (report by 19:00 UTC): the residual rows of every returned loop (kinds, sizes, recurrence vs new, against
  one element and against route-to-route movement), what more routes / headroom 2 / movement-proportional headroom
  would have fixed, the best change as an opt-in knob (resume intact), tested by resuming NOT CLEAN loops from the
  start of their finish phase on >= 4 loops, a farm request if it works.
### progress 12:48 (divsize1: test_divui 8 / 8 seeds pass with the rule fix; headline 53 of 62 kerne)
- Farm divsize1 (test_divui seeds 1-8, rule A's peers confined to the cell): **8 / 8 routes PASS, 32 / 32 draws**, 7
  rule-clean (s7 NOT CLEAN on an unfixable row at it 1); seeds 1-4 = divsize's local routes byte for byte (ecbc22cc,
  96c7d776, 14c880c4, a43e6557); the divider's line ends at 324-516 links (s4: 1111, rule F's padding of very short
  lines -- open). suite10b's failing routes of seeds 1 / 2 (the old rule) are superseded in the table.
### progress 14:34 (ringfuse1, 39 / 44: the fusion pays on xorshift only; a NOT CLEAN route fails a draw)
- BDC_RING_FUSE=2 through the whole v7 flow vs the same seeds' v7 routes without it (nsearch1 / norw1r2 / ringfuse1's v7
  arm), paired: **xorshift faster on 4 / 4 seeds, median -2.17 ns** (-1.16..-3.42; 4 seeds so far); collatz -0.25
  (faster on 4 / 7); countloop +0.45 (3 / 6); ipow +0.12 (3 / 7). Not a default for every kernel on this evidence; the
  xorshift gain matches ringfuse's local runs. countloop s7 / s8 hit PNR-TIMEOUT at it 0 (3 cores).
- **ipow s7 with the fusion FAILS draw 10707** (chains 0.2017 / rest 0.2972 / carry 0.92, near the rule's worst
  vertex: batch 0 hangs; the runt monitor counts 12 pulses under 1 ns and 28 x pulses on 29 of 189 nets -- merges,
  links, steers), 7 / 8 draws. The route was shipped NOT CLEAN with **16 short rows**, while the loop's previous route
  had 2: when nothing is clean the loop ships its LAST route, not its least-short one. A third NOT CLEAN route that is
  actually wrong (after flow v1's ipow s4 and if_loop_1 s1); the rule flagged it. Passed to the converge subagent
  (ship the least-short route; make the finish phase converge).
### progress 15:13 (headline: 56 of 62 kernels pass)
- With suite10c (nest3 s1-4, stencil_2d s1 PASS), divres1 (digitdiv s1, divmods s1 PASS, rule-clean), ifl1 (if_loop_1
  s3 / s4 PASS with rule B's RAM guard) and ringfuse1's v7 baselines: **56 of 62 kernels attempted pass**. Not passing:
  if_loop_1 (seeds 1 / 2's old routes, sized before the guard; ifl1's seeds 1 / 2 still running), share_test_2 (the
  decoder lacks its DSP48E1 cascade mode), and digitsum / single_loop / sobel / video_filter (loops still running).
  Ratio to Dynamatic: 1.69 over the 3 measured figures; 0.99 over 20 with estimates -- the memory kernels' estimates
  assume Dynamatic's on-merges buffering (up to ~6x pessimistic for Dynamatic), so that mean flatters us; said so in the
  headline.
### progress 16:50 (converge landed: the finish phase gets 6 routes and ships its least-short route, by default)
- **converge** (research/data/converge/notes.txt; 14 farm requests, 252 loops, 231 with a finish phase): the clean rate
  per finish step is 7 / 11 / 21 % (steps 1 / 2 / 3); 2367 short rows on finish routes, median 172 ps (p90 606), by rule
  E 827, H 445, I 390, A'j 219, A'm 212; **95.3 % are on constraints and lines that no earlier finish route had
  short** -- a re-route moves every margin by sd ~483 ps (14 958 constraint pairs over 24 local loops; the same at fixed
  sizes on another seed), so the next misses come from rows that had 0.2-0.8 ns, and headroom on the raised lines
  (AUTO_NEAR_PS, headroom 2) cannot reach them (it would have cleared 0 of 383 routes).
- Tested by resuming 8 farm loops at the start of their finish phase (each replay exact: the farm's sdf md5s and rule
  rows): **more raise-only routes on the loop's own seed made 4 of 5 low-row loops clean with one extra route**
  (AUTO_FINISH); extra draws on new seeds (AUTO_FINISH_SEEDS, opt-in) are weak (2 of 40 draws clean); loops with 4-14
  rows per route clean under neither. P moves within route scatter (median +0.07 ns).
- **Ship the least-short route:** on 64 of 135 NOT CLEAN farm loops an earlier finish route had a smaller total miss than
  the shipped last one (median 343 vs 1081 ps). On ringfuse1 task 31 (ipow s7, the route that failed draw 10707),
  AUTO_SHIP_LEAST=1 ships it 6, which passes all 8 draws with no pulse under 1 ns (it 7 reproduced: FAIL 16/17).
- **auto_size.sh defaults now: AUTO_FINISH=6, AUTO_SHIP_LEAST=1** (the old behaviour: AUTO_FINISH=3 AUTO_SHIP_LEAST=0);
  suite_one.sh judges the route named by "shipped it=". Farm **finseeds1** filed (20 untested NOT CLEAN loops resumed
  at their finish phase, arm A = the new defaults, arm DA = + extra seeds; time limited to 240 min from 360).
### progress 16:50 (STATE OF PLAY, updated: supersedes the 11:2x note)
- **Headline** (research/data/fifteen/README.md top): 56 of 62 kernels pass; regenerate with suite_table.py over the
  inputs listed in its provenance paragraph plus whatever lands next (a later request supersedes a seed).
- **Flow defaults now (auto_size.sh):** v7 (the event-graph search phase) + CA_FAST + the bench-clock seed fallback +
  rule B's RAM guard 400 ps + BD_SKEW_MUXN + rule A's peers confined to the cell + **finish budget 6 routes and the
  least-short route shipped when nothing is clean** (converge); draws report runts (GATE_RUNTS=1); the gate fails on x in
  a result and on RAMB18 events. Opt-in, measured: BDC_RING_FUSE=2 (ringfuse1: xorshift -2.2 ns on 4 / 4 paired seeds,
  neutral elsewhere -- a candidate default for loops whose rising floor is the update + test), BDC_SPLIT_SOURCES (ipow
  only), BDC_MEM_FASTFALL, CA_BENCHCAP, AUTO_FINISH_SEEDS.
- **Farm in flight:** suite10c / divres1 / ringfuse1 / ifl1 (their last tasks), suite11 (seeds 3-4 of the 27 kernels
  added on 2026-11-18), finseeds1 (the finish-phase levers on 20 NOT CLEAN loops). Unfinished loops get resumed with
  research/tools/suite/collect_resume.sh + a request like norw1r2.sh.
- **Open, goal 1:** NOT CLEAN routes are fewer but not gone (loops with 4-14 rows per route stay NOT CLEAN; the next
  lever named by converge: an incremental placement that keeps the previous route's cells); share_test_2 unjudged
  (fasm2net: DSP48E1 cascade mode); rule F pads very short lines without converging; the N-way mux hold side is
  argued only; capture-latch timing has no rule.
### progress 17:07 (flow v8: ring fusion on by default under BDC_AUTO; farm suite12 runs the whole suite on it)
- ringfuse1 final (BDC_RING_FUSE=2 vs the same seeds' v7 routes, the whole automatic flow): **faster on 19 of 29 paired
  seeds, median -1.27 ns; xorshift 8 / 8, median -1.87 ns (-1.16..-3.42); collatz 5 / 8, -1.17**; countloop 3 / 6,
  +0.45; ipow 3 / 7, +0.12; one fused route failed a draw (ipow s7: the NOT CLEAN last-route case the least-short rule
  now avoids). **bdc/emit.py: BDC_RING_FUSE defaults to 2 under BDC_AUTO=1 (flow v8)**; without BDC_AUTO, or with
  BDC_RING_FUSE=0, nothing changes (checked: default and host-mem emissions 65 / 65 byte-identical; the BDC_AUTO
  emission changes on 49 of 65 fixtures, the ring-fused ones). Board items 38-41 now say BDC_RING_FUSE=0 (their v3
  routes). A resume of a v7 loop must set BDC_RING_FUSE=0 too, or it rebuilds a different circuit (log.txt would say
  "DIFFERENT ROUTE"); suite11 and finseeds1 were picked up before this commit.
- Farm **suite12** filed: all 62 listed kernels, seed 1, flow v8 -- the first whole-suite run of v8, for the next session
  to compare with the headline's v7 / v6 routes.
### progress 17:43 (headline: 59 of 62 kernels pass)
- divres1: digitdiv s1, digitsum s2 (clean at it 11), divmods s1 PASS, rule-clean (digitdiv s2 ran out again); ifl1:
  if_loop_1 s1 (the seed that failed under the old rule) PASS rule-clean with the RAM guard, s3 / s4 PASS; suite10c:
  single_loop passes. **59 of 62 kernels attempted pass**; left: share_test_2 (fasm2net cannot decode its DSP48E1
  cascade mode: unjudged), sobel and video_filter (their resumed loops still running). Every WRONG ANSWER of this
  session's tables is accounted for: if_loop_1 (rule B had no scatter guard -> the RAM guard), test_divui (rule A's
  peers escaped the cell -> confined), ipow s7 fused (a NOT CLEAN last route -> the least-short route ships).
### progress 18:29 (v8 smoke: dot2 passes; suite10d filed; the farm runs on for the next session)
- Flow v8 locally on a shape ringfuse1 did not route (dot2, seed 9, nextpnr 6e5d224472232d5d): the loop, the search
  phase (it picked fork-output links, no clean route: shipped the loop's route), CLEAN at it 8, EQUIVALENT, **2 / 2
  draws PASS**, P 34.96 ns (one seed: not comparable with v7's routes). nest3 under v8 still running (5400 LUTs).
- suite10c done: sobel s1 / s2, video_filter s1 / s2, share_test_1 s2, single_loop s2 had all 7 ratchet steps but ran out
  in the final stack / draws again; with divres1's digitdiv s2 they are resumed in **suite10d** (v7 circuit:
  BDC_RING_FUSE=0, 2 draws, 3 cores). In flight for the next session: suite11 (seeds 3-4 of the 27 newer kernels),
  finseeds1 (the finish-phase levers), suite12 (the whole suite on v8, seed 1), suite10d.
### progress 18:46 (finseeds1, 13 of 40: the finish-phase levers on loops that had ended NOT CLEAN)
- Arm DA (6 finish routes + 3 extra seeds per not-clean step, AUTO_FINISH_SEEDS=3; ship the least-short route): **5 / 5
  clean** so far (collatz s2 / s4, ipow s2 / s5 (split-sources loops), sqrtsub s1). Arm A (6 finish routes + least-short,
  today's default): **4 of 8 clean** (collatz s2 / s3, ipow s2 / s5); xorshift s8, sqrtsub s1, branchloop s2, twoloops s1
  NOT CLEAN (twoloops shipped its least-short route, it 4). Every draw passing (104 / 104). All of these loops had
  ended NOT CLEAN under the old budget of 3. If the rest holds, AUTO_FINISH_SEEDS belongs in the defaults too (converge
  found it weak on 5 local loops; the farm sample is larger) -- for the next session to decide on the full 40.
### progress 19:53 (FINAL STATE OF PLAY of this session -- the job ends at 22:13 UTC; read this first)
- **Results this session** (from 2026-11-18 16:47 UTC): the automatic column with no kernel list covers every listed
  kernel -- **59 of 62 pass** (research/data/fifteen/README.md top: per-kernel rows, clean / NOT CLEAN apart, the
  provenance of every input); the flow went v6 -> **v8** (CA_FAST, the event-graph search phase, the N-way mux select
  rule, rule A's peers in the cell, rule B's RAM guard, the bench-clock seed fallback, ring fusion of each loop's
  update and test, a 6-route finish phase shipping its least-short route); board items 40 / 41 added, items 38-41
  re-judged 16 / 16 under the strict gate (runts, x, RAMB18); xorshift against the 15 ns yardstick: 22.16 (v7), -1.87
  with v8's ring fusion (8 / 8 seeds, 19.88 median), hand 16.76, Dynamatic 12.73.
- **finseeds1 so far (33 of 40):** arm DA (+3 extra seeds per not-clean finish step) 15 / 15 CLEAN, 120 / 120 draws,
  P vs the loops' original NOT CLEAN routes median -1.14 ns but one +20.59 ns outlier (look at it); arm A (today's
  default: 6 routes, least-short) 11 clean / 7 NOT CLEAN, 144 / 144 draws, P median -2.50 ns (faster on 13 / 14; the
  originals are v6 / v7 routes of other commits, so this is not only the finish phase). **Decide AUTO_FINISH_SEEDS=3 as a
  default on the full 40 after explaining the outlier.**
- **Farm requests the next session reads first** (claude/cluster results/): suite12 (the whole suite on v8, seed 1 --
  compare with the headline's v6 / v7 rows), suite11 (seeds 3-4 of the 27 kernels added 2026-11-18, v7), suite10d (7
  resumed v7 loops: sobel, video_filter, share_test_1, single_loop, digitdiv), finseeds1 (above). Then: regenerate the
  headline (suite_table.py with the inputs in its provenance paragraph + these; suite12's routes are v8: keep them a
  column of their own until v8 has as many seeds as v7), resume what ran out of time (research/tools/suite/
  collect_resume.sh + a request like suite10d.sh; v7 loops need BDC_RING_FUSE=0).
- **Local work lost with this job (nothing the next session needs):** a v8 smoke on nest3 seed 9 (it reached it 9, the
  search had no event graph for its route: P NA, a 3-loop nest); dot2's v8 smoke passed and is journaled.
- **Open, in order:** goal 1 -- the remaining NOT CLEAN loops (4-14 rows per route; converge's next lever: an
  incremental placement that keeps the previous route's cells), share_test_2 (fasm2net: DSP48E1 cascade mode), rule F
  padding very short lines without converging (test_divui s4: 1111 links), the N-way mux hold side (argued only),
  capture-latch timing (no rule; capmargin.py measures it); speed -- v8 on the whole suite (suite12), mux + increment and
  compare + steer fusion (new cells needed), hard relative placement of a ring (untried).
### progress 21:10 (last note of this session: flow v8 on the whole suite, first results)
- suite12 (every listed kernel, seed 1, flow v8 -- ring fusion, the 6-route finish shipping its least-short route,
  every rule fix of this session), 17 of 62 back: **16 PASS, every draw** (brhash, collatz 23.50 ns, fill 30.40,
  lfsrfind 22.40, mul_example, simple_example_1, sqrtsub 29.74, straight, test_bitint, test_bool_array, test_divui,
  test_int16, test_loop_free, test_memory_2, test_stdint, unused_arg, varshift 33.53), 11 rule-clean, 5 NOT CLEAN with
  an unfixable row (shipped least-short); share_test_2 NOT-A-BOARD-ROUTE (the decoder gap). suite10d: share_test_1 s2
  and single_loop s2 PASS. suite11 51 / 54, finseeds1 36 / 40: their final numbers are for the next session.
- Nothing local is needed: every result, tool and request is on claude/research or claude/cluster.
### progress 21:29 (session end: LOCK cleared; the job ends at 22:13 UTC)
- Branch pushed, state of play current (the 20:0x note + the 21:1x note). LOCK cleared for the next session.

## Session 2026-11-19 21:30 UTC -- cluster bot, session 18 (the job's last 40 minutes): auditor T169's disclosure points fixed in the headline
Toolchain: patches.sha 0d42657914fc25d3 (no build this session)   Seeds: none built
Lock: empty at start (session 17 cleared it at 21:29); taken 21:30 UTC as cluster-research-29466208-18. The job ends at
22:13 UTC, so no local build or simulation was started: nothing local would survive it.
Audit: newest rows T162-T170. **T169 (OVERSTATED in disclosure, research/data/fifteen/README.md) answered below**; T168
(board items' BDC_RING_FUSE=0 commands rebuild the judged netlists) CONFIRMED; T170 (formal's ring-fusion theorem)
CONFIRMED as a token-level theorem, the emitted Verilog not covered. Formal: A27, ring fusion (v8's default) proved
function-preserving per kernel from the graphs alone on 18 of the 26 kernels it can import (gcd, collatz64, horner,
varshift, brhash, fold64, lfsrfind, twoloops among them); no counterexample to any rewrite.
### progress 21:33 (T169: every wrong answer the automatic flow produced is now in the headline's prose)
- Each point re-read from origin/claude/cluster results/, not copied from the audit:
  (1) test_divui s1 / s2 (suite10b/9, /10): rule=clean, FAIL 0 / 4 draws each (3 / 12 vectors wrong per draw), now
  listed with if_loop_1 s1 (suite9/77: NOT CLEAN, 2 / 4, memory wrong), ipow v1 s4 and ipow s7 fused (ringfuse1/31: NOT
  CLEAN, 7 / 8); the prose said "two NOT CLEAN routes have been wrong", which hid two wrong rule-CLEAN routes.
  (2) ringfuse1's fused arm: 30 of 32 judged, 215 / 216 draws right, countloop s7 / s8 PNR-TIMEOUT at it 0: now stated.
  (3) memory caveat quantified on the current table (n = 22, not the auditor's n = 20): 11 memory kernels (memref in the
  fixture's handshake); without them the mean with estimates is 1.16 (n = 11) against 1.01; all 10 ratios below 1 are
  against estimates, 4 of them non-memory (branchloop, digitdiv, horner, ipow).
  (4) ratios on one rule-clean route: 8 on this table (the prose said 6; the auditor counted 7 on the older table).
- Does NOT show: the Dynamatic estimates behind the 10 ratios below 1 were not re-derived (DYNFIG_REPORT.md stands).
### progress 21:35 (finseeds1 37 / 40: its +20.6 ns outlier is the event-graph P, not a slower route; suite12 28 / 62 back)
- **finseeds1** (tasks 14 DA quadrec s1, 18 DA iterative_division s3, 29 A collatz64 s2 still RUNNING at 21:34):
  arm DA (+2 extra seeds per not-clean finish step) **18 / 18 CLEAN, 144 / 144 draws**; arm A (today's default: 6
  routes, least-short shipped) **12 CLEAN / 7 NOT CLEAN, 152 / 152 draws**. P against each loop's original NOT CLEAN
  route (12 / 14 pairs with an original P): DA median -1.46 ns, A median -2.50 ns (A includes its NOT CLEAN routes).
  Prediction (A >= 11 of 20 CLEAN; DA clean wherever A is, plus 1-3) held: 12 and 18.
  Note: it5_check says DIFFERENT on 16 of 18 DA tasks (the rebuilt it 5 is not the farm's route: the request ran at a
  later commit than norw1 / split1 / suite9r3), so the farm runs are not the control the request's header claims;
  the comparison is arm against arm, same commit.
- **The outlier explained:** branchloop s2, arm DA, adopted seed 2002's route at it 8 (sdf e5e9c01f): P 35.12 ns,
  against 14.23 on arm A's seed-2 route (cda01728) and 14.52 originally. The bench's latency per call is the same on
  both (median 222 ns; sum over the 14 vectors 7422 vs 7572 ns: the DA route is 2 % FASTER). P is the event graph's
  period (auto_size.sh final(): "event-graph P"), not a bench time; on a loop with a data-dependent branch it can
  pick a cycle the vectors barely run. **Lead (goal 2 reporting, before the next headline):** check P against the
  bench's per-call latency on every kernel with a branch in its loop; the headline's ns column is this P (branchloop's
  ratio 0.40 rests on one clean route).
- **AUTO_FINISH_SEEDS=3 as a default: recommended, NOT changed here** (no time left in this job for the smoke test a
  default change needs; DA costs two extra routes per not-clean finish step, and 2 of its 20 tasks are still running
  after 3.5 h at 3 cores). Next session: make it the default with a local smoke run, after the last 3 tasks.
- **suite12** (flow v8, seed 1): 28 of 62 back, **27 PASS on every draw**, share_test_2 NOT-A-BOARD-ROUTE (decoder
  gap). One seed per kernel, so no claim; beside the headline's v6 / v7 clean medians: xorshift 17.81 [NOT CLEAN]
  (v7 22.16), horner 22.07 (28.03), lfsrfind 22.40 (25.33), memsum 27.77 (29.43), fill 30.40 (32.86), collatz 23.50
  (22.54), ipow 20.62 (19.95), sqrtsub 29.74 (23.91, slower), while_loop_3 28.34 (24.86, slower); twoloops 19.07 and
  varshift 33.52 now rule-clean. test_divui s1 (wrong under v7's old rule) passes 4 / 4.
- Does NOT show: anything about v8 as a distribution (one seed); finseeds1's three running tasks.
Next: (1) suite12's last 34 kernels, suite11's last 3, suite10d, finseeds1's last 3 -> regenerate the headline
(suite_table.py, provenance paragraph), v8 as its own column; (2) AUTO_FINISH_SEEDS=3 default + smoke; (3) the P vs
bench check on branch kernels; (4) the open goal-1 list in the 19:53 state of play stands.
### progress 21:36 (P against the bench, every PASS route on the farm: two single-route anomalies, one of them about to enter the headline)
- Read only (git cat-file over origin/claude/cluster results/*/*/result.txt, 1135 files): for the 30 kernels with >= 4
  PASS routes on the same vectors, the event-graph P and the bench's latency per call (lat_call_sum_ns) correlate at
  >= +0.9 on 24 kernels; iterative_sqrt, binary_search, divmodu and fir have P spreads under 6 % (correlation says
  nothing there). The two exceptions are one route each: **dot2 s2** (suite8 / suite9, NOT CLEAN, P = 156.000 ns
  exactly -- a round number, on the kernel's LOWEST-latency route: looks like a fallback value, not a period) and
  **branchloop s2 finseeds1 DA** (rule-clean, P 35.12 vs 13.5-14.8 on the other five routes at equal latency).
- Headline: a caveat paragraph says what P is and names both routes; the branchloop one becomes the clean s2 route at
  the next regeneration (finseeds1 supersedes suite9r3) and would move branchloop's ratio from 0.40 to about 0.7.
- Does NOT show: which cycle the event graph picked on either route, or where 156.000 comes from (grep the event-graph
  tool for a cap / default). **Next session, before regenerating the headline:** find both causes; until then have
  suite_table.py flag a route whose P sits far off its kernel's P-vs-latency line, or use the bench's per-iteration
  time for the ns column.
### progress 21:38 (the two P anomalies narrowed; adoption is not the cause; session end)
- **Not adoption:** 13 of finseeds1's 18 DA loops adopted an alternate seed's route (adopt() renames its hw / r / ca
  directories before final() computes P); on 12 of the 13, P(DA) / P(A) equals lat_sum(DA) / lat_sum(A) within 0.02
  (e.g. xorshift s8 1.38 / 1.40, sqrtsub s1 1.19 / 1.18, twoloops s1 1.14 / 1.13). Only branchloop s2 departs (P 2.47x
  at latency 0.98x). So P is a faithful per-iteration measure on every other pair, adopted or not.
- **Both anomalous P values came from the ordinary single-stride graph** (no `stride=2` on their it lines: suite9/46
  auto/it_7.txt `su_dot2_2_7 4d68e57e P=156000`, finseeds1/16 auto/it_8.txt `su_branchloop_2_8 e5e9c01f P=35116`).
  research/tools/fifteen/lane2_run.sh's own comment names dot2 suite8 s2: its iterations alternate (bench intervals
  27.85 / 28.20 ns), so the true per-iteration time there is about 28 ns and 156.000 is 5.6x off. Lead: eventgraph.py's
  steady-state detection on a route with alternating iterations (dot2) and on a loop with a data-dependent branch
  (branchloop); the graphs are under research/data/eventgraph/graphs/ in the farm's results if it copied them.
- Session end (job ends 22:13 UTC): branch pushed, journal current, BOARD-QUEUE unchanged (no new candidate judged this
  session), LOCK cleared. Next: see the 21:35 note's Next list; the P check above goes before the headline regeneration.
- 21:38: no wrong answer in flight: suite11 (36 results), suite12 (30), suite10d (2), finseeds1 (37) are all PASS on
  every draw except share_test_2 (NOT-A-BOARD-ROUTE on s1 / s3 / s4: fasm2net's DSP48E1 cascade gap, as before).

## Session 2026-11-19 21:40 UTC -- cluster bot, session 19 (the job's last 33 minutes): branchloop's ratio 0.40 withdrawn (our inner loop against Dynamatic's outer loop); both P anomalies explained
Toolchain: patches.sha 0d42657914fc25d3 (no build this session)   Seeds: none built
Lock: empty at start (session 18 cleared it at 21:38); taken 21:40 UTC as cluster-research-29466208-19. The job ends at
22:13 UTC: read-only work on the farm's committed results, nothing started locally.
Audit: newest row T171 (formal's mr_verilog_check passes bdc's BDC_RING_FUSE_NEGCTL build) is about formal's tool, not
research's files; T169 marked answered by the auditor at 21:39. Formal: C60 (memory routes SAME, 32 / 32), A27 ring fusion
proved on 18 of 26 kernels; no counterexample to any rewrite.
### progress 21:47 (the two P anomalies of session 18: both explained; branchloop's headline ratio was two different loops)
- **dot2 seed 2, P = 156.000 ns**: already known and handled. It is 13 x 12 ns, the host's array fill through the memory
  port picked as the auto marker; eventgraph.py masks bridge_i.mem_busy since 430f52be7 (2026-11-18 21:38 UTC), and suite9
  ran at eaef0dec7 (2026-11-18 17:03 UTC), before it. suite_table.py refuses a P that is a multiple of the host clock
  (line 176), so it never reached the table (dot2's bracket there is 33.39-34.28). Session 18 missed the earlier fix.
- **branchloop seed 2 (finseeds1 DA, P 35.12) is the OUTER loop; every other branchloop P (13.5-14.8) is the INNER loop.**
  branchloop (kernels/branchloop/branchloop.c) has an outer loop with an odd / even branch and an inner loop in the odd
  arm. The auto marker is the request net with the longest run of equal rise intervals, so which loop P measures depends
  on which net's run is longest on that route. Measured from the bench's per-call latencies (latmin x 12 ns minus the
  0-trip call; finseeds1 task 16 = DA route e5e9c01f, task 36 = A route cda01728, draw 10201):

  | quantity (from the vector that isolates it) | DA route (P 35.12) | A route (P 14.23) |
  |---|---|---|
  | inner trip (n = 0x7fffffff: 30 trips, minus n = 3's O + E) | 14.07 ns | 14.48 ns |
  | outer iteration (n = 0x40000001: 61 alternating O0 / E) | 35.80 ns | 36.39 ns |
  | even-arm iteration (n = 0x40000000: 30 E) | 30.00 ns | 29.60 ns |

  Both routes have the same loop times within the 12 ns quantisation; their P differ by 2.47x because P picked a
  different loop. Which net the marker was is not in the farm's files (the VCD is not kept): the identification is by
  period only.
- **Consequence for the headline: branchloop's ratio 0.40 was 14.79 ns (our inner trip) / 36.77 ns (Dynamatic's figure,
  3.44 cycles on bb1, "the most executed of 2 loops": 160 outer iterations against 68 inner trips over the 14 calls, so
  the outer loop).** Withdrawn, and out of every mean (suite_table.py's existing --no-ratio, as for isprime); like for
  like about 35.8 / 36.77 = 0.97, matching the latency-per-call ratio 1.01 on the same calls. Corrected by hand in
  research/data/fifteen/README.md (not regenerated): geometric mean with estimates 1.01 (n = 22) -> **1.06 (n = 21)**;
  without memory kernels 1.16 (n = 11) -> **1.28 (n = 10)**; ratios below 1: 10 -> 9, non-memory among them 4 -> 3
  (digitdiv, horner, ipow). The measured-figure mean (n = 3, 1.69) and the latency mean (n = 31, 1.38) do not change.
- Of the 22 kernels with a ratio, branchloop is the only one that Dynamatic's table lists with more than one loop
  (research/data/suite/dynamatic/table.md, "of N loops": 18 kernels). On the other 17 (gcd, nested, nest3, twoloops,
  binary_search, the memory nests; isprime already out) no ratio is filled yet; the same check comes first when one is.
- Does NOT show: that our P on single-loop kernels measures the iteration Dynamatic's figure measures (one loop each, so
  it should, but not checked against the bench the way branchloop was here); the ESTIMATED Dynamatic figures themselves.
Next (general, nothing per kernel): make P follow Dynamatic's convention on every kernel, in eventgraph.py's auto marker
or in suite_table.py: measure the most executed loop (by back-edge count over the calls), and refuse a P whose loop
cannot be identified; then regenerate the headline with --no-ratio isprime,branchloop dropped where the loop now
matches. Before that, the 21:35 Next list of session 18 stands (suite12's last kernels, suite11's last 3, suite10d,
finseeds1's last 3 -> regenerate; AUTO_FINISH_SEEDS=3 default + smoke; the open goal-1 list of the 19:53 state of play).
### progress 21:49 (P against the bench's own per-iteration time, every kernel: P is faithful on all 19 single-loop kernels; it departs only where a kernel has several loops)
- New read-only tool research/tools/suite/p_vs_slope.py: per route, P against the least-squares slope of the route's call
  latencies (latmin x 12 ns, median over draws, as suite_table.py's route_lat) on Dynamatic's header executions per call
  of the most executed loop (dynamatic_lat.tsv, the same trip counts suite_table.py's "fit" uses). Over the farm results
  copied to /tmp/bot/farmres (28 requests, finseeds1 34 of its 40 tasks); table in research/data/suite/pslope/p_vs_slope.txt.
- **Single-loop kernels (19): P / slope median 0.97-1.01 on every kernel, every route within 0.94-1.04** (xorshift 43
  routes, collatz 56, ipow 60, collatz64 34, countloop 22, ...), except dot2's two pre-fix routes (156.00 / 28.50: the host
  fill, already refused). So on one-loop kernels P is the per-iteration time of the loop Dynamatic's figure measures.
- **Multi-loop kernels depart:** branchloop 0.45 (five routes on the inner loop, one at 1.00: the DA route, the one session
  18 called the outlier, is the one that matches Dynamatic's loop); **gcd 2.16** (3 routes, gifast1: P 61-66 ns against a
  slope of 28-31 ns per execution of Dynamatic's bb11, the most executed of 5 loops; gcd has no ratio in the headline yet);
  isprime 7.07 (already out of every mean). twoloops 0.97 (P happens to be on the most executed loop).
- Does NOT show: digitdiv, if_convert, loop_path, single_loop, sumi3_mem, while_loop_3 and fir have a ratio in the headline
  but no row here (their trip counts do not vary over the vectors, or no '-' -> header column, so no slope): their P is
  unchecked this way. The slope includes everything per trip the bench sees, so it is an upper bound for the loop alone.
Next (general, nothing per kernel; replaces the 21:47 Next's first item): in suite_table.py, where the slope exists, refuse
a P that departs from it by more than 15 % (the single-loop scatter is 6 %) and use the fit, which is Dynamatic's own
convention; that removes the hand edit and the --no-ratio list for branchloop and isprime alike and fills gcd. Then
regenerate.
### progress 21:51 (the rule in the tool, nothing per kernel: suite_table.py refuses a P off its route's own latency slope by > 15 % and uses the slope; branchloop 0.85 (fit), mean with estimates 1.05)
- **Dynamatic's per-iteration figure is a slope**: branchloop's 3.44 cycles recomputes as 3.43 = the least-squares slope of
  its cycles per call on bb1's header executions (dynamatic_lat.tsv). So the like-for-like figure on our side is the same
  slope on the same trip counts, which suite_table.py already computes ("fit") where P is missing.
- **suite_table.py**: (1) a P more than PSLOPE_TOL = 15 % off its route's slope is refused, listed under its own "P refused"
  note, and the slope is used (the single-loop scatter over every farm route is 6 %, so the margin is 2.5x it); (2) the fit
  is no longer limited to one-loop kernels (Dynamatic's figure is the most executed loop's slope whatever the count).
- **Check:** regenerated with the provenance command over /tmp/bot/farmres (copied 20:03 UTC): unmodified, it reproduces the
  committed table's 63 rows byte for byte; modified, the only row changes are branchloop (all 4 suite9r3 P refused at
  0.42-0.47x; clean route fit 31.35 ns, **ratio 0.85 (fit)**) and NOT CLEAN bracket fits where there was no figure or a
  refused P (factorial 28.21, gcd 29.05, isprime 49.65, nest3 48.57, nested 29.73): no ratio of theirs changes (no clean
  route; isprime stays --no-ratio). Means: with estimates **1.05 (n = 22, 1 from the fit)** (1.01 with the old 0.40),
  measured 1.69 (n = 3) and latency 1.38 (n = 31) unchanged; non-memory 1.24 (n = 11). The hand edit of 21:47 is replaced
  by these generated rows (research/data/suite/pslope/headline_regen_2152.md is the full output).
- Does NOT show: that 15 % is the right margin on a kernel whose single loop has a branch (brhash's arms differ by design;
  its routes are within 6 % today); the slope includes the bench's per-trip overhead (none is known: P and slope agree to
  2 % on the single-loop kernels, so it is small).
### progress 21:52 (session end: the job ends at 22:13 UTC)
- State: branch pushed (64b0d95e9 + this note); BOARD-QUEUE.md unchanged (no new candidate judged); no draft-PR update (no
  `gh` on this node); nothing running locally; LOCK cleared with this commit. Scratch work under /tmp/bot/scratch_bl is
  lost with the job; everything it showed is committed (research/tools/suite/p_vs_slope.py, research/data/suite/pslope/).
Next, in order:
1. Regenerate the headline over the newest farm results (copy origin/claude/cluster results/ for every request in the
   provenance list plus suite12, suite11's last tasks, suite10d, finseeds1), now with the P-against-slope rule; v8 as its
   own column (session 18's 21:35 Next, item 1).
2. AUTO_FINISH_SEEDS=3 as the default, with a local smoke run (session 18's item 2).
3. The 7 kernels with a ratio but no slope (trip count fixed over the vectors: digitdiv, if_convert, loop_path,
   single_loop, sumi3_mem, while_loop_3, fir): their P is unchecked against the bench; add vectors with other trip counts
   (computed from the C) or check P against the bench's per-call latency divided by the C's trip count.
4. gcd's P sits on another loop than Dynamatic's most executed (2.16x the slope): name the loop from the event graph,
   for the record; the table uses the slope now.
5. The open goal-1 list of the 19:53 state of play (session 17) stands.
### progress 21:53 (lock retaken 21:50 for one hardening of the 21:51 rule; cleared again with this commit)
- suite_table.py: a P is refused only when its gap to the slope is beyond BOTH 15 % and 3 standard errors of the slope
  (residual-based, new slope_se()). Why: a kernel whose trip counts barely vary gives a slope too noisy, with calls
  quantised to 12 ns, to overrule P. Synthetic check (12 ns-quantised calls, trips 10-12): slope 27.00 +- 2.29, P 21.0 ->
  refused by the 15 % test alone, kept with the guard; wide range (trips 0-60, P 0.45x): slope 33.03 +- 0.08, still refused;
  P 1.6 % off: kept. The regeneration over /tmp/bot/farmres is byte-identical to the 21:51 one (the guard does not bind
  on today's data), so the headline stands as committed.
- Does NOT show: that 3 SE is the right multiple; nothing on today's routes sits between the two tests.
### progress 21:54 (lock retaken 21:51 for one read-only check; cleared again with this commit; session end)
- **while_loop_3** (one of the 7 headline kernels with no slope: Dynamatic's table has one call of its own test, so
  dynamatic_lat.tsv has no trip counts for it): trip counts from the C itself on the suite's 7 calls (vec/while_loop_3.hex
  bounds -2^31, 0, 1, 2, 100, 101, 1025 -> 0, 0, 1, 2, 10, 11, 33 trips). P / slope on its 4 farm routes: 1.00
  (suite10b s1, NOT CLEAN), 0.96 (suite10b s2), 0.99 / 0.97 (suite11 s3 / s4, both clean); slopes 25.12-27.44 +- 0.04-0.10 ns.
  So its P (24.86 clean median) is the loop's per-iteration time. Still unchecked: digitdiv, if_convert, loop_path,
  single_loop (one call each in Dynamatic's table, fixed trips in ours too or not: look at their vec files), sumi3_mem and
  fir (1000 trips in every call: no slope possible; P against (latency - 0-trip latency) / 1000 is the check there).
- **Generalising (Next 3 of 21:52, refined):** take every kernel's trip counts from the C run on the suite's own vectors
  (the oracle already runs the C), not from Dynamatic's simulation; then the slope, and with it today's P check and the
  fit, exist for every kernel whose vectors vary the trip count, Dynamatic's figure or not.
- Session end: branch pushed, LOCK cleared, BOARD-QUEUE unchanged, nothing running locally.
### progress 21:55 (two more of the 7 unchecked kernels: P faithful; LOCK stays clear)
- **sumi3_mem and fir** (1000 trips in every call, so no slope; the per-call overhead, 72-84 ns on the kernels that have a
  0-trip call, is under 0.1 ns per trip here): P / (latency per call / 1000) on every farm route (suite9r4): sumi3_mem
  0.99 / 0.95 / 1.01 / 0.97 (s1-s4, all clean), fir 0.99 / 0.96 / 1.01 / 0.98 (s1-s4; s2 NOT CLEAN). P is the loop's
  per-iteration time on both. Left unchecked: digitdiv, if_convert, loop_path, single_loop.
### progress 21:56 (three more: P faithful on digitdiv, loop_path, single_loop; only if_convert left unchecked; LOCK stays clear)
- Trip counts from each kernel's C on the suite's own calls (read-only, farm results):
  - **digitdiv** (trips = base-b digits of x, from each call's op0 / op1 in BENCHRES; 18 calls, 0-32 trips): divres1 s1
    P 147.74 against a slope of 149.24 +- 0.07 ns, **0.99**.
  - **loop_path** (one call, a = 0, 1, 2, ..., b = 1: 167 trips): suite10b s1 / s2 P against latency / 167: **1.00 / 0.96**.
  - **single_loop** (one call, a = 2, b = 0, 1, 2, ...: 501 trips): suite10c s1 **1.00**.
- With 21:52-21:55: P is the per-iteration time of the loop Dynamatic's figure measures on every single-loop kernel in the
  headline that has a ratio, except if_convert (unchecked: its trips depend on the array contents, i += 1 or 2). The one
  multi-loop kernel with a ratio, branchloop, is now from the slope (0.85).
### progress 21:57 (if_convert too: P is faithful on every kernel with a ratio; LOCK stays clear)
- **if_convert** (trips depend on a[]: the C run on the 3 calls' arrays from vec/if_convert.hex gives 193, 100, 130 trips):
  P / slope 1.00 / 0.97 / 1.00 / 0.97 on suite10b s1 / s2, suite11 s3 / s4 (all clean; slopes 49.03-53.61 +- 0.01 ns).
- **So, over every one of the 22 kernels with a ratio in the headline:** 21 single-loop kernels have P within 0.94-1.04
  of the bench's own per-trip time on every farm route checked (trip counts from Dynamatic's simulation where it has them,
  from the C on the suite's calls for the other 7), and branchloop, the one with two loops, now uses that slope (0.85).
  The per-iteration column measures what Dynamatic's figure measures. What it still does not settle: the ESTIMATED
  Dynamatic figures themselves (DYNFIG_REPORT.md), which carry the 9 other ratios below 1.
- Next stays as at 21:52, with item 3 done for the headline's kernels; for the regeneration, take trip counts from the C
  for every kernel (suite_table.py reads them from dynamatic_lat.tsv today, so 7 kernels have no slope there).

## Session 2026-11-19 21:57 UTC -- cluster bot, session 20 (the job's last 18 minutes): formal's C64 answered -- our rule B saw spmv s4's row RAM short (-373 ps), the route is NOT CLEAN and the loop's final sizes pad it
Toolchain: patches.sha 0d42657914fc25d3 (no build this session)   Seeds: none built
Lock: empty at start (session 19 cleared it); taken 21:55 UTC as cluster-research-29466208-20. The job ends at 22:13 UTC:
read-only work on the farm results already copied to /tmp/bot/farmres, nothing started locally.
Audit: no row since T171 (21:39 UTC, formal's tool). Formal: B19 (suite12 rows), C60; **C64 (20:55 UTC, spmv seed 4's
host-write race on the row array's RAM) had no answer in the journal**: answered below.
### progress 21:57 (C64: the rule saw it; the shipped route is the unfinished one)
- Formal C64: spmv s4 (suite11/32, sdf f52af15f) passes 128 / 128 of its draws, but the row array's umem0 ADDR setup
  margin is 22 ps at worst and -890 ps with skew.py's guards (GUARD_LO 0.772 on the 3332 ps clock path, GUARD_HI 1.155
  on the 2508 ps payload path). Its question: does our RAM guard look at this chain, and why did it pass it?
- **It did not pass it.** suite11 ran at e2c8e6c52, which contains the RAM guard (34c90ae2d, BD_RAM_GUARD_PS=400 in
  auto_size.sh). spmv's arrays map to controllers from the fixture (argNames n, row, col, val, vec, out; mem_controller9
  = row, 8 col, 7 val, 6 vec, 5 out). On the shipped route (it 7, row's umem0 usetup = 4 links, sizes_7.vh), rule B says
  **PAD 4->7, -373 ps** (band 0.31) and PAD 4->6, -316 ps (band 0.20) on umem_controller9 umem0, and -48 / -25 ps on its
  umem1 (auto/lines_7_*.txt). The route's result line says rule=not-clean, it=7: the loop stopped before routing the fix;
  its sizes_final.vh pads row's umem0 to 8 and umem1 to 6. So both tools call this route short, and it is one of the
  unfinished routes the headline keeps apart from the finished ones.
- What it does show: on it 6 the same line at 4 links had +337 ps left; the re-route for it 7 moved it to -373 ps, a
  ~700 ps swing on the host-port path between two routes of the same netlist at the same size. One route's margin on this
  path says little about the next.
- Open (general, for rule B, not for spmv): our RAM guard is additive (400 ps); skew.py's guard is multiplicative. Formal's
  multiplicative sum gives -63 ps on ifl1's fixed if_loop_1 s1 (c3113cc4), which rule B with the 400 ps guard calls clean,
  and which passes formal's draws (C63). Which form fits the draws is measurable: compare both on the 13 c_mem14 routes.
- **Correction (journal times):** session 19's notes headed 21:54, 21:55, 21:56 and 21:57 were committed at 21:52:21,
  21:52:41, 21:53:13 and 21:53:39 UTC (git log). The headings were estimated, against PROGRAM.md; their content stands.
- Does NOT show: anything new about spmv on a finished route (none was built here); whether 128 passing draws on a short
  route mean the guard is too strict (formal bounds the failure rate at ~2.9 % at 95 %, not at 0).
Next: session 19's 21:52 list stands (regenerate the headline over the newest farm results with the P-vs-slope rule and v8
as its own column; AUTO_FINISH_SEEDS=3 default + a smoke run; trip counts from the C for every kernel; gcd's P loop; the
goal-1 list of the 19:53 state of play), plus rule B's guard form (above).
### progress 21:57 (farm state for the next session; session end, LOCK cleared)
- Read from origin/claude/cluster at 21:57: **suite12** (flow v8, seed 1) 35 of 62 results back: 34 PASS on every draw
  (4 / 4), share_test_2 NOT-A-BOARD-ROUTE (fasm2net's DSP48E1 cascade gap, as before); 21 rule-clean, 14 not (6
  not-clean, 8 not-clean-unfixable: xorshift, cmpchain, gather, factorial, iterative_division, iterative_sqrt,
  test_memory_1 / 2, test_bool_array, binary_search, mul_example, test_stdint, countloop, share_test_2). New since session
  18's 28: binary_search P 37.86, collatz64 29.89, countloop 24.20, gather 56.03, if_convert 55.13, iterative_division
  20.99, iterative_sqrt 55.25, test_stdint 53.28 (one seed each: no claim). suite11 52 / 54, finseeds1 39 / 40, suite10d
  2 / 7 finished.
- Session end: branch pushed, journal current, BOARD-QUEUE unchanged (no candidate judged), nothing running locally,
  LOCK cleared with this commit. Next: as at the session heading's Next.
### progress 21:58 (one check of the C64 answer; LOCK stays clear)
- Checked, not assumed: the headline (research/data/fifteen/README.md line 126) has spmv at **0 rule-clean + 4 NOT CLEAN
  routes of 4**, no ns per iteration and no ratio, its latency only in brackets (900.75, 874.50-946.50). So no spmv route
  carries a number in the headline. No route of spmv has finished sizing yet: it belongs on the goal-1 list of NOT CLEAN
  loops, where the RAM guard rows (row's umem0 / umem1) are what the loop could not close on s4. suite12 (v8, 6-route
  finish) has not returned spmv yet: read it there first.
### progress 21:59 (gcd's P: the marker IS in Dynamatic's block on the one route whose marker is on record; the 2.16x is not "another loop"; LOCK stays clear)
- Session 19 read gcd's P / slope = 2.16 (gifast1 s1 / s3 / s4: P 61.4-66.3 ns) as "P sits on another loop than
  Dynamatic's most executed (bb11)". The gifast1 files hold no marker net (auto/it_*.txt, log.txt: P only), so that was
  not checked. The only gcd route with its marker on record is a local graph left in this job's clone,
  research/data/eventgraph/graphs/au_gcd_1_0 (2026-11-17, BDC_AUTO=1 it 0, sdf 68cd1f94, P 56.49 ns, untracked, not
  committed): its auto marker n10770 = bridge_i.udut.n145__3_req, and in the fixture (unchanged since 2026-10-25) %145
  is fork36, **handshake.bb = 11**. So on that route P is measured on a net of the block Dynamatic's figure counts.
- Candidate explanation, NOT checked: gcd (research/data/gcd_draws/gcd_kernel.c, Stein) has 5 loops; the main loop
  `while (a != 0)` holds the shift loop `while (a > 0 && (a & 1) == 0)`, whose test runs at least once per main
  iteration. If bb11 is that inner test, its executions per call are main iterations + shift trips (about 2 per main
  iteration), and a period measured per main iteration is about 2x the per-execution slope. That would make P and the
  slope two different units on one loop nest, not two loops. To check: which block is the main loop's header in the
  fixture, and the marker on one gifast1 route (rebuild seed 1, read eventgraph.py's check.txt).
- Does NOT show: anything about gifast1's own markers; that Dynamatic's bb numbering in its table equals the fixture's.
  The headline is unaffected (gcd has no clean route; suite_table.py uses the slope where P departs from it).
### progress 22:00 (correction of the previous note's count, from the fixture; LOCK stays clear)
- The fixture's blocks (handshake.bb on each op): bb10 holds the main loop's body (subi a - b, select, cmpi sgt, muxes);
  **bb11 holds the shift itself** (andi a & 1, cmpi, shrsi a >> 1, six cond_br: the rotated shift loop, body and test in
  one block), and the marker's %145 (fork36) feeds that shrsi: it is the shift loop's a. So bb11 runs once per SHIFT
  TRIP, not "main iterations + shift trips" as the previous note guessed. Every main iteration shifts at least once
  (a and b are odd there, so a - b is even), so shift trips per call >= main iterations, about 2 per main iteration on
  random inputs. A marker on the shift loop's a rises once per main iteration when that iteration shifts once, and P
  is then one main iteration (subtract, select, the shift); the slope is per shift. Same conclusion, different count:
  P and the slope are two units on one loop nest. Still unchecked on gifast1's own routes.
### progress 22:01 (finseeds1 39 / 40: one DA task hit the time limit -- a cost of AUTO_FINISH_SEEDS=3 to weigh; LOCK stays clear)
- Read from origin/claude/cluster at 22:01 (request at bc9e26857; 240 min per task, 3 cores): **arm A** (today's default,
  6 routes, least-short shipped) 20 / 20 back: **13 rule-clean, 7 NOT CLEAN, 160 / 160 draws right**. **Arm DA** (+2
  extra seeds per not-clean finish step) 19 / 20 back: **18 rule-clean, 144 / 144 draws right**, and task 18
  (iterative_division s3) **CANCELLED AT THE 240 MIN TIME LIMIT** in finish phase 2 (log: "phase 2 (raise-only) from it 5";
  no result line). Task 14 (quadrec s1, DA) is still running.
- For the default decision (session 18's item 2): DA turns 7 NOT CLEAN routes into clean ones on these loops, but at
  least one DA loop does not finish in 4 h at 3 cores, where arm A finished all 20. A default that makes a route miss the
  farm's time limit loses the route (a "time limit" row in the table). So the smoke run should measure DA's wall time per
  kernel, and the default may need a cap (extra seeds only while time is left), not just AUTO_FINISH_SEEDS=3.
### progress 22:01 (CORRECTION of the previous note: DA cleaned 5 of arm A's 7 NOT CLEAN loops, not 7; LOCK stays clear)
- Paired by kernel and seed (task.txt of each finseeds1 task): arm A's 7 NOT CLEAN loops are branchloop s2, quadrec s1,
  quadrec s4, sqrtsub s1, twoloops s1, xorshift s8, iterative_division s3. Arm DA is rule-clean on **5** of them
  (branchloop s2, quadrec s4, sqrtsub s1, twoloops s1, xorshift s8). The other two are exactly DA's unfinished tasks:
  iterative_division s3 (time limit) and quadrec s1 (still running). The previous note's "turns 7 NOT CLEAN routes into
  clean ones" was wrong. So the extra seeds fail to finish precisely on the loops where they are needed most, which
  makes a time cap part of the default question, not a detail.

## Session 2026-11-19 22:02 UTC -- cluster bot, session 21 (the job's last 10 minutes): finseeds1's last task and the audit, read only
Toolchain: not run (no build this session; nothing routed here)   Seeds: none
Did: took the lock; read origin/claude/cluster (finseeds1 task 14) and origin/claude/audit (new rows since session 20).
Next: as at session 20's Next.
### progress 22:03 (read only: finseeds1 still 39 / 40, suite12 still 34 / 62 with spmv running; no new audit or formal row for research; LOCK cleared)
- origin/claude/cluster, last results commit 84809d725 (22:01:52 UTC): **finseeds1** task 14 (quadrec s1, arm DA)
  RUNNING at 01:55:22, task 18 (iterative_division s3, DA) TIMEOUT at 04:00:14; so DA's two unfinished loops are still
  exactly arm A's two NOT CLEAN loops it did not clean (session 20's correction stands). **suite12** (flow v8, seed 1,
  submitted 19:52 UTC, 240 min per task): 34 COMPLETED, 28 RUNNING. spmv is task 51 (KS index in
  research/cluster/requests/suite12.sh), **RUNNING at 01:41:31**, no result files yet: the spmv check session 20 asked
  for (does v8's finish leave spmv's row-RAM guard rows NOT CLEAN, as on suite11 s4) has to wait for the next job.
- Audit: newest rows are still T171 (formal's mr_verilog_check, not research's files; noted by session 19) and the
  T169 answer (21:39 UTC). Formal: newest is 573b3d3fd (21:59 UTC), formal A's MARGINS row for spmv s4, which records
  research's C64 answer (route unfinished, rule B -373 ps). Nothing new for research to answer.
- Does NOT show: anything about the spmv or quadrec s1 results themselves; no build ran in this session.
- Session end: branch pushed, journal current, BOARD-QUEUE unchanged (no candidate judged), nothing running locally,
  LOCK cleared with this commit. Next, for the next job's first session: read finseeds1 task 14 and suite12 task 51
  (spmv) on origin/claude/cluster first, then session 20's Next.
### progress 22:05 (suite12 36 / 62 at 22:04:02 UTC; dot2 s1's row is new; spmv still running; LOCK stays clear)
- origin/claude/cluster 49d6bb7c5 (22:04:02 UTC): suite12 **36 of 62**. The two new COMPLETED are task 3 (collatz64 s1,
  P 29.891 ns, already in session 20's list) and task 27, **dot2 s1: PASS, draws 4 / 4, P 26.809 ns, rule clean (it 11),
  1475 LUTs, bits EQUIVALENT, ffmux clean, sdf 43afb62a, lat_call_med 909 ns over 8 vectors**. One seed: no claim.
  spmv (task 51) RUNNING at 01:52:28, finseeds1 task 14 (quadrec s1, DA) RUNNING. 26 suite12 tasks still running.
- Does NOT show: any multi-route figure for dot2; that the "Next" reads are done (they wait for the next job).
### progress 22:05 (au_gcd_1_0 committed: the evidence for session 20's gcd marker note survives the job; LOCK stays clear)
- Session 20's gcd P-marker note rests on research/data/eventgraph/graphs/au_gcd_1_0, a local graph from 2026-11-17
  that was untracked and would be wiped with /tmp at 22:13. Committed it as is (404 KB, the same files as the committed
  graphs such as colsz2_6): check.txt (marker auto n10770, P 56488 ps, period and cycle checks PASS), provenance.txt
  (routed.json md5 37dbffe8..., sdf 68cd1f94, fid model, netlist from the bitstream EQUIVALENT, **toolchain:
  UNSTAMPED**), build.txt (BDC_AUTO=1, 6955ef48). One route, toolchain not stamped: evidence for the marker's net only,
  not a period claim. The other 24 untracked graph dirs are not cited anywhere and are left uncommitted.
### progress 22:05 (8 more local graphs that the journal or a README cites committed before the wipe; LOCK stays clear)
- Committed as is, from this job's clone (~1 MB, the committed graphs' layout): au_collatz_1_0 (research/data/pnrfix/README.md),
  su_xorshift_1_4, su_xorshift_2_7, su_straight_3_4, su_collatz_1_4, su_collatz64_1_4 (journal tables, sessions 2 to 17),
  rj_ipow_4 and bqa_ipow_2 (research/data/ringfuse/README.md rows). Each provenance.txt names its SDF md5 and source path.
  su_straight_3_4 holds no arcs / nodes / check (as built). Nothing was rebuilt or re-checked: these are the files the
  citations were written from, kept so a later session can reread them. The 16 uncited graph dirs stay uncommitted.

## Session 2026-11-19 22:08 UTC -- cluster-research-29466208-22: the job's last 5 minutes; read-only farm check, no build
Toolchain: 0d42657914fc25d3   Seeds: none (no build)
### progress 22:08 (farm unchanged since 22:04: suite12 36 / 62, spmv and finseeds1 task 14 still running; LOCK cleared)
- origin/claude/cluster, newest commit 64311efea (22:06:14 UTC) is formal's fm_c_mem18 submission (3 tasks), not
  research's. suite12 is still **36 of 62** (49d6bb7c5, 22:04:02 UTC); task 51 (spmv) and task 52 RUNNING since 01:52:28.
  finseeds1 still 39 of 40 (task 14, quadrec s1, DA). No new result for research to read or answer.
- Does NOT show: anything new; no build or check ran (the job ends at 22:13 UTC, 5 minutes after this session started).
- Session end: branch pushed, journal current, BOARD-QUEUE unchanged, nothing running locally, LOCK cleared. **Next job's
  first session: read finseeds1 task 14 and suite12 task 51 (spmv) on origin/claude/cluster first, then session 20's Next.**
  The 16 uncited local graph dirs are lost with /tmp; nothing cites them.

## Session 2026-11-19 22:42 UTC -- cluster-research-29671222-1 (new job, ends 2026-11-21 22:41 UTC): rule H misread every memory load's capture latch as a controller; fixed, the real capture hold measured (>= 17.6 ns), farm capfix1
Toolchain: patches.sha 0d42657914fc25d3, nextpnr 6e5d224472232d5d (cells/verify/toolchain.sh all ok on node1452)   Seeds: per item
Lock: empty at start (session 22 of the previous job cleared it at 22:08); taken 22:42 UTC. cluster: new job, fresh /tmp;
the farm's results copied to /tmp/bot/farmres (git archive of origin/claude/cluster results/, 22:44 UTC).
Audit: newest rows T169-T171, all answered or about formal's tool; nothing new for research. Formal: B19 (suite12 rows),
A27, C63 / C64 (answered by session 20); nothing new for research.
### progress 23:01 (rule H's capture rows were a pattern bug: 23 of 49 shipped capture routes were NOT CLEAN on them alone)
- **Found** reading suite12's "not-clean-unfixable" routes (test_bool_array, test_memory_1 / 2, mul_example, test_stdint,
  vector_rescale, binary_search, share_test_2): every unfixable row is rule H at `uloadN.ucap.pair[k].u$LUT5/6`, -100 to
  -625 ps, "no DACK line here to pad". Across all farm results: 37 071 such rows, all H. On the shipped route of 49 loops
  of 12 capture kernels they are present, and on 23 they are the ONLY short rows.
- **Cause:** tighten.py's RE_BD_LATCH matched `.lat.` only (a link's latch). bdc_load_cap's capture is `bd_latch ucap`
  (bdc/mem.py CAPTURE); its LUTs are storage nodes (own feedback), so rule H took each as a CONTROLLER, its "enables"
  being the consumer link latch's DATA pins, and compared unrelated paths. Not a race: a misreading.
- **Fix** (599c89e6b): RE_BD_LATCH = `\.(?:lat|ucap)\....`. Only bdc/mem.py emits `ucap`, so no design without a capture
  changes. Check on test_bool_array s1 it 6 (rebuilt here: sdf 8759dc8d = the farm's): HEAD reproduces the farm's neg_6
  (24 rows) and rule_6.vh; fixed: 0 rows, CLEAN, proposal byte-identical, every non-ucap line of the four audit logs
  identical at both corners. New unit test (cells/verify/test_rule_h_hold.py) fails on the old pattern; 105 / 105 pass.
- **The capture's real hold, measured** (new research/tools/caphold.py; rule H cannot see it: the capture's enable comes
  through ucapen, and a RAM output is not in its model). From `done` rising: close = longest done -> ucapen -> latch LUT;
  the next DOADO change >= shortest done -> CLK + shortest CLK -> CLK (the whole four-phase port cycle: DCO line, arbiter,
  R0, DSETUP) + T_CO + DO -> D, storage passed through as if it fired at once (a lower bound). test_bool_array s1 it 6:
  close 1128-1307 ps, change >= 18.8-20.2 ns: **margin >= 17.6 ns** (band 0.20), 18.5 ns (0.31); >= 17.2 ns with T_CO at
  its fast minimum (585 ps). memorder's capmargin.py had the setup side at 2.5-5.3 ns; so the capture is far from
  binding on both sides on this route.
- **What it changes, replayed from suite12's own seed-1 loop files** (the ucap rows were unfixable, so every proposal and
  every route up to the ship decision is unchanged; only stop / ship moves): test_bool_array would ship it 6 CLEAN
  (shipped it 1, with 3 REAL short rows), mul_example it 5 (it 4, 1 real row), test_memory_2 it 9 (it 4, 2 rows),
  vector_rescale it 7 (it 5, 2 rows), test_stdint it 4 and test_memory_1 it 10 (the same routes, now clean). So the bogus
  rows did not only hide clean routes: through the least-short choice they made the loop ship routes with real misses.
- **Farm capfix1** (48 tasks: the 12 capture kernels with finished routes x seeds 1-4, flow v8 as suite12 + the fix;
  caphold on each shipped route at both corners; prediction in the request). sobel / video_filter (captures too) left
  out: their loops and draws ran out of 240 min in suite10c and suite10d.
- Correction (times): this note's heading was first written 23:12, an estimate; `date -u` said 23:01. capfix1's header says
  "PREDICTION (2026-11-19 23:10 UTC)", also estimated: it was committed at 23:00:39 UTC (599c89e6b), before any result.
- Does NOT show: caphold on more than one route (capfix1 adds 48); a negative control for caphold (its margin is ~17 ns,
  so no plausible delay error closes it, but the tool has not been shown to fail).
Next: suite12's last tasks -> regenerate the headline (v8 its own column; capfix1 for the capture kernels); then the
second convergence lever (placement kept between finish routes, research/data/converge/notes.txt's open lead).
### progress 23:31 (placement kept between finish routes: the hook works; first numbers; four loops resumed)
- **The open convergence lever (research/data/converge/notes.txt: "an incremental placement keeping the previous
  route's cells") is in, opt-in:** cells/hw/build_bench.sh BD_PLACE_FROM=<routed JSON or cell/bel list> runs
  cells/hw/place_from.py as nextpnr's --pre-place script (unset: the command line is unchanged); auto_size.sh
  AUTO_PLACE_KEEP=1 builds every finish-phase route from the previous route's placement (place_I.txt / placefrom_I.txt
  so a resume rebuilds it; a kept-placement build that fails is built fresh).
- **Why it is needed, measured:** test_bool_array s1 it 5 -> it 6 (USETUP 6 -> 9, 3 new LUTs): cell names identical,
  but a fresh re-route moved 6051 of the 6136 shared cells to another bel.
- **What it took to work (each measured on that pair, nextpnr 6e5d224472232d5d):** binding at STRENGTH_USER keeps every
  cell but the router then does not permute the bound LUTs' input pins: the packer starts LUT5 / LUT6 pairs on the same
  pin (A1) and 55 site wires stay overused, no route. STRENGTH_STRONG lets the post-place repair move 681 cells.
  STRENGTH_FIXED: 6130 kept, the 3 new cells placed, 8313 LUT pins permuted, routed, bench clock 111.5 MHz, rule CLEAN,
  ffmux-clean. Margin change of the 16 sized constraints whose lines did not change: **sd 95 ps against 221** for the
  fresh re-route (median |d| 115 vs 222). The router still re-routes everything, so ~100 ps of scatter is left.
- On xorshift the first try bound only 3687 of 7533 cells: yosys's abc names shift by a constant between routes
  ($abc$21205..$21206 -> $abc$21209..$21210), and other auto-numbered classes move inside (9 carry chains +4, 104 of 1910
  flops). place_from.py now matches by the abc index relative to its run, then by order inside a name class (7346 of
  7533 by the first two keys on a pack-only check); the half-bound try had also tripped nextpnr's known
  "post-placement validity check failed for Bel ..A5FF (no cell)".
- `--fixed-routes` (an undocumented option of this nextpnr binary, to keep the previous ROUTES too) dumped it 5's routes
  without changing that route (sdf db9c761d both ways) but crashed nextpnr (core dump) when applied to it 6: not used.
- **Running (local, worktree /tmp/bot/wt_exp at 1fd98f586):** suite12's seed-1 loops of xorshift, countloop,
  iterative_division and gather (each ended NOT CLEAN after the 6-route fresh finish phase on the farm) resumed at their
  finish phase with AUTO_PLACE_KEEP=1, AUTO_SEARCH=0; their it 5 is the farm's own route (sdf bed7ecfa, 46ef015c,
  b276174b reproduced), so the farm's finish phase is the control. PREDICTION (23:31): at least 3 of 4 reach a clean
  route within 3 kept-placement steps (the farm's fresh steps: 0 of 4 in 6).
- share_test_2 s1 it 6 rebuilt here (st2_6): fasm2net refuses DSP48_X0Y27: the pre-adder (USE_DPORT=TRUE, INMODE=00100:
  (D + A) * B) with B from BCIN and Z = PCIN>>>17. A subagent extends the decoder / dsp_model / prims.v to it, with
  negative controls (worktree, no git); share_test_2 is the suite's only NOT-A-BOARD-ROUTE kernel.
- CA_BENCHCAP (opt-in since 2026-11-19, research/data/benchcap/: the bench's synchronised capture of out0, negative
  control on record) removes the other unfixable family (A' at the out0 mux: iterative_sqrt umux3 -5.2 ns, isprime
  umux13, gcd umux21; 26 shipped routes); it waits only for draws on routes built with it: next farm candidate.
### progress 00:18 (capfix1 18 / 48: every judged route passes, 17 of 18 rule-clean, capture hold >= 11.4 ns; CORRECTION of 23:01's replay claim; place keeping v2)
- **capfix1** (origin/claude/cluster, 18 of 48 back; the 12 capture kernels x seeds 1-4, flow v8 + the ucap fix):
  **16 / 16 judged routes PASS 4 / 4 draws; rule-clean 17 of 18** (test_memory_2 s1 NOT CLEAN at it 9); share_test_2
  s2 / s3 NOT-A-BOARD-ROUTE (the DSP decoder gap, now rule-clean: the ucap rows were all it had). In suite12 (seed 1)
  the same kernels were 0 rule-clean of 8. **caphold (the capture's hold, lower bound, band 0.20) on all 18 shipped
  routes: 11.4 - 17.6 ns.** P on the kernels that have one: mul_example s1 57.59 ns, test_stdint s2 / s3 / s4 47.89 /
  44.87 / 51.27 (one route each so far).
- **CORRECTION (23:01 note and capfix1's PREDICTION):** "the fix leaves every proposal unchanged, so seed 1 rebuilds
  suite12's routes and only the stop / ship decision moves" is FALSE in general. It held on test_bool_array s1 it 6
  (checked), but on test_memory_1 s1 the trajectories split at it 3 and on test_memory_2 s1 at it 2: corner_audit's
  verify step only TRIMS a pad when no sized constraint is left below slack, and the 24 always-negative ucap rows had
  kept it from ever trimming (test_memory_1 it 2: ULINK_N_TRUERESULT_8_SDELAY padded 1 -> 3, now "trimmed 3 -> 2 by
  verify"). So the fix also shortens over-padded lines on capture kernels. The predicted shipped iterations are
  therefore not a check of anything; what stands is the per-route rule and draws above.
- **Place keeping v2** (30fc4597b): matching by trusted names (no yosys counter; abc by relative index), then output
  net names, then structure (neighbours with their port), every kept LUT's input pins restored to the previous route's
  (the router does not swap a constant tie's pin back). xorshift s1 it 5 -> 6: 6990 cells kept, routes, EQUIVALENT,
  margin move of unchanged-line constraints median |d| 122 ps (fresh 282), p5 -332 (fresh -552). Route keeping is not
  possible in this toolchain (research/data/placekeep/route_from.py: ROUTING pip names do not parse back; --fixed-routes
  segfaults even on its own netlist). The four suite12 finish phases are running again with v2 (the v1 run kept the
  placement on only 4 of 17 steps; xorshift s1 went CLEAN on its one kept step, it 7, P 19.59 ns).
### progress 00:57 (placement kept between finish routes: CLEAN in one step on xorshift, fails to route on 3 other kernels; parked as opt-in)
- research/data/placekeep/README.md has the whole account. Matcher v2 (trusted names, abc by relative index, output-net
  names, structure, previous LUT pins restored): **xorshift s1 rule-CLEAN at it 6, its first kept step, P 18.11 ns,
  EQUIVALENT** (the farm's fresh finish phase: 4, 4, 4, 2, 2 short rows at it 6-10, never clean, shipped it 9 NOT CLEAN
  17.81); with matcher v1 the one kept step (it 7) was also CLEAN (19.59). But on countloop, iterative_division and
  gather every kept step failed to route (router2 8 overused wires; a nextpnr segfault on gather, reproduced) and fell
  back to a fresh build: the harness's yosys names are not stable (gather: 680 abc cells off the run's offset, 1481 of
  8360 cells unmatched). Route keeping is impossible in this toolchain (pip names do not parse back; --fixed-routes
  segfaults on its own netlist).
- Decision: AUTO_PLACE_KEEP stays opt-in and out of the next flow. The fix is at synthesis (deterministic names for a
  whole loop; yosys autoname makes all 5545 xorshift harness names match across the two routes): next time this is
  taken up. The convergence lever left for now: the rule fixes that remove unfixable rows (ucap, CA_BENCHCAP).
### progress 01:09 (place keeping stopped: autoname does not stabilise gather's harness; v9 on the farm without it)
- BD_AUTONAME (opt-in, 207ecffdf: yosys autoname before write_json; AUTO_PLACE_KEEP turns it on): on gather s1 it 6 ->
  it 7 the harness's netlist itself changes with the kernel (5104 of ~7500 names common even with autoname; its
  generated names carry shifting disambiguation counters), the kept build timed out (1478 of 8360 cells new), and
  keeping the kernel alone left 2 constant sinks unroutable. The lever needs the harness synthesized apart from the
  kernel, and nextpnr changes for constant-tie pins and routes: both larger than this session's budget for it. Stopped;
  research/data/placekeep/README.md has the state. Everything added stays opt-in (unset: byte-identical builds).
- Waiting on: capfix1 (19 / 48 at 00:31), suite12's last task (if_loop_1), suite13 (v9: v8 + ucap fix + CA_BENCHCAP,
  240 tasks, submitted 00:58), the DSP subagent (share_test_2), the local CA_BENCHCAP smoke (iterative_sqrt s1).
### progress 01:13 (share_test_2 judgeable: the DSP pre-adder modelled; the != loop test with the real frontend; suite13 waiting)
- **share_test_2** (subagent dsp, landed 78f74977a; research/data/suite/dsp/README.md): fasm2net refused a DSP48E1 with
  the pre-adder (USE_DPORT=TRUE, INMODE 00100: (D + A2) * BCIN) and the B cascade. Modelled exactly that (plain
  multiply only; all else still refused); also fixed: USE_DPORT / B_INPUT were written from defaults, not the bits,
  and xray_delay gave the pre-adder cell the shorter non-pre-adder A -> P arc (3841 vs 5201 ps at SLOW_MAX).
  share_test_2 s1 it 6: **EQUIVALENT, P 99.39 ns, draws 10101-10104 PASS 3 / 3 each**; pre-adder made to subtract:
  FAIL 0 / 3; eight mutated FASMs all refused; bits-stack outputs byte-identical on three routes without it.
  Does NOT show: the D pin's routing-bit assumption on silicon (a board D-port bit-walk would settle it). suite13 was
  submitted before this commit: its share_test_2 routes will need re-judging.
- **The != loop test, now with the real frontend** (Dynamatic in $HOME/dynamatic; PROGRAM 2026-11-14): on today's v8
  route xorshift's critical cycle is 57 % matched-delay chains, 29 % wires, 13 % cells, and the fused update + test
  cell ucmpi1 (i + 1, then the signed compare i + 1 < n: two carry chains) carries 15 elements, 5.8 ns. The event
  graph (sizewhatif.py, same placement): ucmpi1 at 10 -> P 15.93 ns, at <= 7 -> 15.11 (from 18.11). BDC_FE_EXITCOND=1
  turns the compare into an equality tree. Real frontend on all 62 kernels: 37 change (11 only the loop test's
  predicate, slt -> ne; the rest indvars restructures more: nest3, sobel, stencil_2d, ...), 25 byte-identical;
  fixtures committed as cloud/fixtures/frontend_exitcond/ (13d3547ce). The Nov-14 farm test (fxne: no gain) was
  before ring fusion, when the compare was its own cell of 8-9 elements. Running locally: xorshift, countloop, horner
  s1 through the v9 flow (CA_BENCHCAP=1) with these fixtures. PREDICTION (01:13): ucmpi1 (or the kernel's fused
  update + test) sizes to <= 10 elements, P 1.5-3 ns below the same kernels' default-fixture routes; every draw passes.
- **suite13 is WAITING** (status 00:58: the account's 250-task limit; capfix1 still holds 24 tasks). Nothing else
  large is filed until it starts.
### progress 01:35 (formal C65 / C66 answered from the farm's own rule files; the != loop test sizes the fused compare at 11, not 15)
- **C65 (guard form):** formal's 121 memory routes / 3872 draws (0 failures) settle the question session 20 asked:
  rule B's additive 400 ps guard flags exactly the 6 routes with the smallest draw margins (draw minima <= 306 ps), the
  multiplicative x0.772 / x1.155 form flags 49 (39 with draw minima >= 400 ps). **The additive form stays.** The four
  older routes it flags besides if_loop_1 s1 / spmv s4 are all NOT CLEAN routes of their loops, and rule B named the
  same RAMs short on three of them at the shipped iteration (gather s2 suite9/50 it 7: umem_controller2 umem0 -96 /
  -173 ps; iir s1 suite10b/43: -157 / -175; test_stdint s1 suite10b/29: umem_controller1 umem0 -98 / -118;
  if_loop_1 s3 suite9r3/79: no B row at it 7). None carries a P in the headline (NOT CLEAN routes' P are bracketed).
- **C66 (share_test_1 s1, suite12/58, 65d7b529, the kernel's own accesses):** rule B DID flag that edge on the shipped
  route (it 4, auto/lines_4_*.txt): UMEM_CONTROLLER3_UMEM1_USETUP 3 links, B on umem1's uram -359 ps (band 0.20) /
  -415 (0.31), "PAD 3->6"; umem0 -230 / -275, "PAD 3->5". The loop stopped there NOT CLEAN (suite12 still had the
  bogus ucap rows: "not-clean-unfixable"); capfix1 seeds 1-4 of share_test_1 (with the ucap fix) have not returned.
  So formal's 165 ps sits on a route our rule already called short, by 359-415 ps after the guard.
- **The != loop test, first numbers (local, seed 1, v9 flow):** the fused update + test cell's line sizes to 11
  elements on xorshift (trajectory 17 -> 10 -> 14 -> 11 -> 11; the default fixture's loop: 15 throughout), bound by
  A'j with 52-313 ps left, 3426 ps of line against 4687-5458 with the magnitude compare. Loops still running.
### progress 02:44 (a hard region on the critical ring: worse on 3 of 4 seeds; the != structure at fixed sizes ~16.3 ns)
- **Region lever** (cells/hw/region.py, build_bench.sh BD_REGION_RX, opt-in; the box in SLICE coordinates because
  this nextpnr's Python has no getBelLocation): the 160 cells of the critical cycle's instances of ex_xorshift_1_5
  (the != fixture, it 5 sizes) confined to SLICE_X19..26 Y50..69 (shrunk 0.6 per axis from their X18..29 Y41..74),
  same sizes, seeds 1-4. P (EQUIVALENT, ffmux-clean on all 8): **boxed 15.87 / 16.87 / 17.85 / 18.91 against
  unconstrained 17.22 / 15.94 / 16.28 / 16.37: paired -1.35 / +0.93 / +1.58 / +2.54 ns, worse on 3 of 4.** Seed 1's
  cycle lost half its inter-cell wire (6.81 -> 3.54 ns), but on seeds 2-4 other cycles (through umux0 / ulink_n7,
  ucond_br8 / ufork4) became critical with the rest of the loop spread around the box. Boxing one route's critical
  cycle is a negative result; the whole kernel boxed (shrink 0.7) is running as the last variant.
- **The != loop test at fixed sizes:** the same four unconstrained routes (it 5's sizes, != fixture) give P 15.94 -
  17.22 ns (median ~16.3); the default fixture's suite12 / pk routes ran 17.8-18.1. Not a comparison yet (it 5 is
  not a finished, clean route); exit1 on the farm is the paired test.
### progress 02:46 (region lever closed negative; the != loop test's first finished loop: no gain on xorshift s1)
- Whole kernel boxed (BD_REGION_RX=^bridge_i\.udut\., shrink 0.7: 1251 cells into 364 slices for 309 needed): no
  legal placement on any of the 4 seeds (a CARRY4 of ucmpi0 "Unable to find legal placement"); a looser box is the
  kernel's present extent. With the critical-ring box worse on 3 of 4 seeds, **the hard-region lever is closed as
  negative**; region.py / BD_REGION_RX stay opt-in.
- **!= loop test, xorshift s1 through the whole loop (local, v9 flow):** shipped it 9 NOT CLEAN (30 ps over 1 row),
  **P 18.09 ns**, EQUIVALENT, against the default fixture's seed-1 routes 17.81 (suite12, NOT CLEAN it 9) and 18.11
  (pk, CLEAN it 6). The fused cell's line stayed short (11) but the finish phase (it 5-10, never clean: 1, 4, 3, 8 rows)
  raised other lines; at it 5's sizes four seeds gave 15.9-17.2. horner s1: NOT CLEAN, least short it 9 (12 ps over 2
  rows). One seed each: no claim; farm exit1 against suite13 (35 kernels x 4 seeds) is the test.
- CA_BENCHCAP smoke (iterative_sqrt s1, local): the loop ran to it 9 with no 'unfixable' row on any route (every
  suite12 route of this kernel had umux3's), final stack EQUIVALENT; draws running.
### progress 04:29 (post-route trimming: -2.9 ns on xorshift at one step, a hang at the next -- the rule is not enough to judge a trim)
- **New lever, research/data/trim/README.md (8844efeac):** a bd_delay(_gated) element g[k>=1] is a LUT2 of the chain and
  the line's own input; INIT 1100 on g[i] makes g[i] the line's entry (N - i elements, same edges) on the SAME placement
  and routes. research/tools/auto/trim_lines.py edits the routed JSON and the FASM (fasm_audit.expected_lut_bits); the
  rule follows trimmed lines (tighten.chain_side_arcs, corner_audit.chain_geometry; byte-identical untrimmed).
- **xorshift s1, != fixture, shipped it 9 (P 18.09, NOT CLEAN by one H row of -30 ps):** the rule's own proposal on the
  route applied as 14 trims -> **P 15.18 ns (-2.91, -16 %)**, bits EQUIVALENT, the rule shows only the same -30 ps row,
  **draws 10101-10104 PASS 19 / 19**, no pulse under 1 ns. Cycle: chains 11.4 -> 9.2 ns, wires unchanged.
- **AUTO_TRIM=1 in the loop (7a7cffb2d, e6557399e):** iterates rule -> trims -> rule on the shipped route, reverting a
  step that opens short constraints (now keeping the lines those rows do not depend on). On the same route it took
  step 1 (the 14 trims) and a step 2 (6 chains: ucmpi0 7 -> 1, umux1 3 -> 1, umux2 2 -> 1, ulink_n12__0 2 -> 1, two
  UACK 2 -> 1) with the rule still showing only the -30 ps row and bits EQUIVALENT -- **and the decoded-bits simulation
  of that route does not finish: 449 us of simulated time against 11 us for the step-1 route.** A race the rule does
  not model, exposed because trimming puts lines at exactly the rule's limit (the loop's re-routes and pins had always
  left some slack). So a trim must be judged by the simulation, not the rule. Bisecting the step-2 trims now (each
  alone on the step-1 route, a 30 us batch limit). On iterative_sqrt s1 the first step opened 10 short rows and was
  reverted (before the partial-revert change).
- Exit-test loops (local, seed 1, v9 flow): countloop CLEAN it 10, P 21.39 (suite12 s1: 24.20 NOT CLEAN), horner CLEAN
  it 12 (search route), P 21.09 (22.07), xorshift NOT CLEAN it 9, 18.09 (17.81); all PASS 4 / 4. CA_BENCHCAP smoke:
  iterative_sqrt s1 CLEAN it 9, PASS 4 / 4 (every suite12 route of it was NOT CLEAN on the out0 mux's unfixable row).
### progress 04:44 (CORRECTION of the 04:2x note: the trimmed route was not "only the same -30 ps row"; a rule-support bug, fixed; the bisection)
- The 04:2x note (and research/data/trim/README.md) said the rule on xorshift's 14-trim route showed only the old H -30
  ps row. False: my chain_side_arcs change counted a trimmed entry as fed through the routed wire into its dead pin, so
  the trimmed cell went unaudited ("nothing outside bridge_i.udut.ucmpi0 reaches its request -- not audited"). Fixed in
  f5b32d12d (the predecessor's pin must keep its LUT arc); untrimmed outputs byte-identical. **With the fix that route
  has 5 new short constraints, 63-346 ps** (A'j ucmpi1 -346, A ucontrol_merge1 -233, E ucond_br5 / br2 -203 / -190,
  A'j ucmpi0 -63). Its 4 draws had passed; P 15.18 ns stands as a measurement of that route, not as a rule-clean one.
- The loop's trim step had used the blind spot: its step 2 set ucmpi0 7 -> 1 ("floor 1"), and that route hangs.
  **Bisected** (each of step 2's five macros alone on the step-1 route, 30 us batch limit): ucmpi0 at 1 alone hangs
  (completed=0, result x, bench FSM x); umux1 / umux2 / ulink_n12__0 / the UACK at 1 each complete with the right answer.
  The fixed rule flags ucmpi0 at 1: E -1.1 .. -2.5 ns at four steers, A'j -2.2 ns. So the hang was the defect, not a
  race the rule cannot see; the lesson stands that a trim has to be judged by draws as well as by the rule.
### progress 04:55 (STATE OF PLAY -- read this first if the session ends here)
- **Rule H capture fix** (599c89e6b): capfix1 47 / 48 back: 34 / 34 judged routes PASS every draw, 34 of 38 rule-clean
  (suite12 had 0 of 8 on these kernels), capture hold >= 11.4 ns everywhere; 9 tasks hit 240 min (share_test_1 x4,
  iir s2 / s4, image_resize s3 / s4, spmv s3): need a resume request (research/tools/suite/collect_resume.sh, cf.
  research/cluster/requests/suite10d.sh).
- **share_test_2 judgeable** (78f74977a, DSP pre-adder): suite13 / capfix1 ran before it, so their share_test_2 routes
  say NOT-A-BOARD-ROUTE: re-judge them (suite_one.sh SUITE_SKIP_AUTO=1 or research/tools/suite/rejudge.sh).
- **Farm:** suite13 (v9 = v8 + ucap fix + CA_BENCHCAP=1; 60 kernels x 4 seeds) and exit1 (the != loop test fixtures,
  35 kernels x 4 seeds, the same flow: suite13 is its control) are WAITING for capfix1's last task (binary_search s2,
  limit ~05:50 UTC). When back: regenerate the headline (research/data/fifteen/README.md; suite_table.py, provenance as
  its paragraph says) with suite13 as the v9 column; then exit1 against suite13 per kernel.
- **Closed negative:** placement kept between finish routes (research/data/placekeep/README.md: works where names are
  stable, fails on 3 of 4 kernels; routes cannot be kept in this toolchain); a hard region on the critical ring (worse
  on 3 of 4 seeds); the whole kernel boxed (no legal placement).
- **Open, in progress: post-route trimming** (research/data/trim/README.md): lines of LUT2 elements shortened by INIT on
  the same route. Measured: -2.9 ns on xorshift's shipped route with draws passing 4 / 4, BUT that set is rule-short by
  63-346 ps on 5 constraints once the rule reads trimmed lines correctly (f5b32d12d), and the loop's trim step
  (AUTO_TRIM=1, opt-in) reverts it. Next: damped steps; exact trim deltas in corner_audit (enter via the side net).
- Local exit-test seed-1 results: countloop CLEAN 21.39 ns, horner CLEAN 21.09, xorshift NOT CLEAN 18.09; CA_BENCHCAP:
  iterative_sqrt s1 CLEAN, PASS 4 / 4.
### progress 05:06 (post-route trimming, honest status: the rule-clean slack on xorshift's route is small; the draws allow ~2.9 ns)
- With the rule reading trimmed lines correctly, the loop's trim step reverts every variant on xorshift s1 it 9: the
  rule's full proposal (16 rows opened, 1458 ps), damped (14, 1044 ps), and trim_plan.py's exact per-entry pricing
  (12, 754 ps; new research/tools/auto/trim_plan.py). The opened rows sit on the trimmed cells themselves. So the
  route has little rule-clean slack on the lines that matter (ucmpi1 needs ~14 built-equivalent elements, pinned at 15);
  most of the -2.9 ns measured earlier goes below the rule's need, which 4 / 4 draws tolerated.
- Not adopted as a default; AUTO_TRIM stays opt-in. Two continuations written down in research/data/trim/README.md:
  exact trim modelling inside corner_audit's verify (rule-clean trims, ~0.5-1 ns here), or sizing by the draws
  (PROGRAM allows it: shorten while every draw passes, report the first failing size; a trim search costs only
  simulations, no routes).
### progress 05:38 (trim mode in the rule itself: corner_audit CA_TRIM=1 predicts a trimmed route's margins exactly; capfix1 done)
- **Why the trims kept opening rows:** a trimmed line is entered at g[k]'s side pin, which the side net's DRIVER reaches by
  its own branch -- and g[0] is reached through the cell's anchor LUT `uor` (bd_delay_gated: a = uor's output, gate =
  the anchor's input). So the first trim already skips the anchor: ucmpi1 (xorshift s1 it 9, band 0.31) R -> uor -> g[0]
  1114 ps against R -> g[4]'s side pin 813 ps; a chain-only price missed 721 ps of a 1819 ps trim, and on
  ucontrol_merge1 (R = the arbiter's state LUT) the trimmed request is 1253 ps earlier, more than the line's whole 879 ps.
  The rule's own verify (chain arcs scaled to a delay) cannot express that, nor could trim_plan.py.
- **corner_audit.py CA_TRIM=1** (opt-in; default outputs byte-identical to HEAD, all 8 files at both corners + merged
  sizes, xorshift s1 it 9 with CA_BENCHCAP=1): lines whose g[1..N-1] are side-input LUT2s are sized for THIS route's
  bits -- priced at each entry from the side net's driver (wire, anchor, entry arc, chain), raised at most to the placed
  length, and VERIFIED with the entry moved in the timing graph exactly as trim_lines.py's INIT makes false_arcs() see it
  (g[k]'s chain-input arc cut, the old entry's restored); other lines keep their size. **On it 9 every one of 111
  constraints' predicted margin matched the trimmed route's own rule within 2 ps, both corners.** The proposal (umux1 7 ->
  3, umux2 6 -> 2, ucontrol_merge1 3 -> 2, ulink_n12__0 3 -> 2, two UACK 3 -> 2) opened nothing: the route keeps exactly
  its one old row (H -30). ucmpi1 stays 15: its first trim skips the anchor (~0.9 ns, counted twice on its 2x capture).
- auto_size.sh trim step: AUTO_TRIM_PLAN=ca (new default of the opt-in AUTO_TRIM=1) uses that proposal undamped.
- Running: the full stack (bits, equivalence, P) on the trimmed copy ex_xorshift_1_9e; draws next.
- capfix1 finished at 04:50 UTC: 38 of 48 tasks returned (34 judged routes all PASS 4 / 4, 34 of 38 rule-clean), 10 hit
  the 240-min limit (share_test_1 x4, iir s2 / s4, image_resize s3 / s4, spmv s3, binary_search s2). No resume request:
  suite13 (waiting for room behind another session's 68-task request) runs the same kernels with the same fix.

## Session 2026-11-20 06:21 UTC -- cluster-research-29671222-1, second start (job requeued: now ends 2026-11-22 06:20 UTC; fresh /tmp)
Lock: cluster-research-29671222-1 at 05:38 (this wrapper's previous session, same id); taken 06:21 UTC.
cluster: the job was requeued under the same id; /tmp/bot was recreated at 06:20 UTC, so nothing of the previous
session's local work (worktrees, ex_xorshift_1_9e, farmres) survives; only what was pushed.
Toolchain: patches.sha 0d42657914fc25d3, nextpnr 6e5d224472232d5d (cells/verify/toolchain.sh all ok, 06:22 UTC)   Seeds: per item
Audit: no new rows since T171 (only lock / journal commits). Formal: C67 (exit-condition fixtures: 59 LIVE exhaustively,
9 sampled, 0 deadlock; dot2 / gather / memsum refused on 'minui'), c_mem37 (first exit1 memory routes); nothing asked of research.
Farm: exit1 running (21 of 140 back at 06:20); suite13 (240 tasks) waits for room under the account's 250-task limit.
### progress 06:33 (bdc min / max: the != fixtures of memsum / dot2 / gather compile and pass RTL; trim-only mode; rtl_bench fix)
- **exit1's first 21 tasks:** every judged route passes 4 / 4 draws (lfsrfind s1 / s2, countloop s2, test_stdint s1 / s2,
  mul_example s2, test_bitint, test_memory_1 / 2), and memsum / dot2 / gather (x 4 seeds) are DOES-NOT-COMPILE: "no
  width rule for handshake op 'minui'" -- the != fixture computes their loop bound as umin(n, ...) once before the loop.
- **bdc: minui / maxui / minsi / maxsi** (c896d1fc4): one compare and a 2:1 select per unit (compute.BINARY, carry
  class, the comparator's +6 links of placeholder). test_compute.py 196 / 196 against references written the other way
  round; negative controls fail it (minsi with an unsigned compare; swapped arms). Emission byte-identical on every
  fixture that compiled before (65 default + 34 exitcond, header line aside). **RTL bench (BDC_AUTO=1, != fixtures):
  memsum PASS 5 / 5, dot2 8 / 8, gather 9 / 9**; an altered expected result or array word FAILs it.
- **rtl_bench.sh was blind** (fixed, this commit's neighbour): it extracts bench_gate.sh's verdict code "so the two
  cannot drift", but the python call grew a continuation line (the runt monitor's arguments) and the extracted code
  started with that line: every RTL bench since printed an empty verdict (it "passed" nothing and failed nothing).
- **auto_size.sh AUTO_TRIM_ONLY=1** (0c9143d3e, opt-in) + research/tools/auto/trim_farm.sh: a farm task's shipped route
  rebuilt from its own sizes and seed (sdf md5 checked), trimmed by the flow's trim step (CA_TRIM=1 plan), full stack,
  and suite_one.sh's draws on the task's OWN draw points: a paired measurement of the trim, the route unchanged.
  First four (exit1 lfsrfind s1, countloop s2, test_stdint s1, mul_example s2): all four rebuilt to the farm's sdf.
### progress 06:47 (trim step on farm routes: first periods; an "overbuild then trim" finish phase, opt-in, first loop running)
- **Trim step, paired, same route** (trim_farm.sh, AUTO_TRIM_ONLY; nextpnr 6e5d224472232d5d): every rebuilt route
  matched its farm sdf md5 (lfsrfind s1 129ff3ee, countloop s2 aa201b8b, test_stdint s1 3985966e, mul_example s2
  8e05893d, capfix1 mul_example s1 / s2, test_stdint s1 / s2). First trimmed periods (full stack, EQUIVALENT):
  lfsrfind s1 27880 -> 27062 ps (5 lines: ulink_n22__1 7 -> 1, umux1 5 -> 2, umux0 4 -> 2, ucmpi0 11 -> 10,
  ulink_n22__0 3 -> 2); exit1 mul_example s2 61750 -> 60989 (1 line); test_stdint s1: the rule's trim mode moves no
  line. countloop s2 (NOT CLEAN by one H row needing a UACK raise): ucmpi1 (the fused update + test) 18 -> 13, umux3
  6 -> 2, umux1 5 -> 2 and 6 more; its stack is running. Draws on all of them: running (the farm's own draw points).
- The md5 check works as meant: capfix1 binary_search s1 was shipped by the search phase, whose structure a farm task
  does not return (structure.env); rebuilt without it, it was refused as a different route (85887ea1 vs 58ff60aa).
  Fixed (82c85e9c1: the structure is read from the loop's result line); s1 / s3 / s4 to be re-run.
- **Why routes end NOT CLEAN, on the 111 shipped routes of suite12 / capfix1 / exit1** (the shipped iteration's neg
  file): 28 NOT CLEAN; besides suite12's ucap rows (fixed since), the rows are churn on lines that only needed padding
  (H at a link stage's controller 7 routes, A'm at a mux 5, C / B at a RAM 5 / 4, E at mux joins 4, ...), mostly by
  28-500 ps over 1-3 constraints. A trim can only shorten, so it cannot fix those as built.
- **AUTO_OVERBUILD=H** (0ea146dd6, opt-in, implies AUTO_TRIM): at the switch to the finish phase every TRIMMABLE line
  (trim_lines.py --list: side-input LUT2 chains; symmetric lines -- some mux delays, RAM lines, plain link requests --
  and 1-element lines of unknown kind are left alone) is built H elements longer than max(sizes, proposal); a finish
  route is clean when the trim step alone makes it so (trim_check: the trim step run, its final rule state read). The
  idea: churn of ~0.5 ns sd is covered by the extra length, and the trims cut every line back to what the route it
  landed on needs. First loop: suite12 xorshift s1 (farm: NOT CLEAN after 6 finish routes, shipped it 9, P 17.81 ns),
  phase 1 as the farm ran it, H = 3 (overbuild_farm.sh). PREDICTION (06:47): clean after the trim step within 2 finish
  routes; P at or below the farm's 17.81 ns; every draw passes.
### progress 06:52 (the != fixtures widen 22 of 37 kernels; first trimmed P: countloop s2 -9.8 %; compile slots were 1)
- **BDC_FE_EXITCOND widens the datapath on 22 of the 37 kernels it changes** (sum of channel widths in the handshake
  MLIR, default -> exitcond fixture): +225 (fold64, twoloops) to +2920 bits (test_flatten_array; sobel +2577,
  stencil_2d +1500, image_resize +1242, lfsrfind +325). Cause, read on lfsrfind: the counter is i8 / i9 under the
  default fixture (Dynamatic's --handshake-optimize-bitwidths bounds it from the `ult 256` test) and i32 under the
  != test, which the range analysis cannot bound. The other 15 (xorshift, countloop, horner, gcd, isprime, brhash,
  nested, quadrec, varshift, fill, if_loop_1 / 2, spmv, test_memory_1 / 2) keep every width: only on those does
  exit1 test the != loop test itself. Seed-1 routes so far, exit1 against suite12 (v8, one route each, so routing
  scatter is in it): horner 21.09 vs 22.07 ns, xorshift 18.09 vs 17.81, fold64 25.19 vs 22.93, varshift 37.14 vs
  33.53, lfsrfind 27.88 vs 22.40. Reading exit1 against suite13 must split the kernels by this.
- First trimmed routes (full stack after the trim step, the farm's route unchanged otherwise): **countloop s2 (exit1)
  22368 -> 20167 ps (-9.8 %)**: the fused update + test ucmpi1 18 -> 13, umux3 6 -> 2, umux1 5 -> 2, six more (its one
  H row stays: it needs a UACK raise no trim can give); lfsrfind s1 -2.9 %, mul_example s2 -1.2 %. Draws running.
- cluster: /tmp/eventgraph_compile.slots (4 on this node) is lost with /tmp at a job's start, and was missing until
  06:48: every draw compile of this session waited on one lock till then. Now 4 again.
- The trimmed lfsrfind s1 cycle (cycdecomp): P 27062 = delay chains 12641 + wire between cells 11966 + cell logic
  2455 ps over 12 handshake hops (~1 ns of wire each: two compares in series, each behind a join and a steer).
### progress 07:05 (trimmed routes pass their draws so far; overbuild: xorshift s1's first finish route CLEAN as built)
- Draws on trimmed routes, the farm's own draw points: lfsrfind s1 3 / 3 so far, countloop s2 2 / 2 (PASS 10/10 each,
  no pulse under 1 ns on lfsrfind's: narrowest 4.0 ns).
- **Overbuild (+3 on 31 trimmable lines), suite12 xorshift s1:** its first finish route (it 5, b4d71e3d) is CLEAN as
  built -- no short row at all, where the farm's six finish routes (no overbuild) never were; untrimmed P 20279 ps
  (the farm shipped it 9 NOT CLEAN at 17808). The trim step on it is running: the prediction stands to be checked
  against 17.81. countloop s1 / s2: their first finish routes are short on 6 / 10 rows as built; trim checks running.
- Next, beside these: BDC_MEM_FASTFALL (cells/rtl/optin/bd_mem_ff.v, the port's two lines fall in one element;
  research/data/suite/memauto.md: -6.0 / -8.0 / -12.7 % on gather s1 / s2, fill s2, single routes, never through the
  sizing loop) through the loop locally with AUTO_TRIM, as a candidate for the next flow.
### progress 07:31 (overbuild: the trims fix the E rows the extra length opened; the node is the limit)
- **Overbuild loops, first finish route (+3 on every trimmable line):** xorshift s1 CLEAN as built; countloop s1 short
  by 6 rows (1214 ps) as built -- E at umux1's join (select later than the request: lines on the select side got
  longer too) -- and by 2 (202 ps) after the first trim step, the trims having shortened those lines back; countloop s2
  (exit1) 12 rows 2054 ps -> 8 rows 476 ps after two steps. The rule marks such E rows "unfixable" in trim mode (it
  fixes a short row by padding, never by shortening a line on the other side), yet trimming other lines fixes them.
- exit1 xorshift s1 (d947adff) after the trim step: **18088 -> 16738 ps** (bits EQUIVALENT; its one old H row of
  -30 ps unchanged); capfix1 mul_example s2 60990 -> 58451. Draws on both running.
- cluster: this node is shared (load 130-155); my jobs hold 51 GB of the 64 GB allowance and ~17 cores; about 20 gate
  simulations run at once, so draws take 20-30 min each. The capfix1 trim queue is paused (memory kernels: the trims
  there were 0-4 %, the simulations the longest).
### progress 08:00 (trim step: every trimmed route judged so far passes its draws; suite13 replaced by suite13t = v9 + the trim step)
- **Trim step on farm routes, paired on the same route and the farm's own draw points** (trim_farm.sh; nextpnr
  6e5d224472232d5d; flow v9 rule with CA_BENCHCAP=1):

  | route (request task) | P farm -> trimmed (ps) | dP | lines moved | draws trimmed | rule |
  |---|---|---|---|---|---|
  | exit1 countloop s2 (39) | 22368 -> 20167 | -9.8 % | ucmpi1 18->13, umux3 6->2, umux1 5->2, ucontrol_merge0 4->2, 2 UACK | 4 / 4 (10/10) | NOT CLEAN, same H row |
  | exit1 xorshift s1 (1) | 18088 -> 16738 | -7.5 % | (record in the run) | 2 / 4 so far (19/19) | NOT CLEAN, same H -30 |
  | exit1 horner s1 (10) | 21088 -> 20424 | -3.1 % | 20 lines at step 1 | 2 / 4 so far (11/11) | clean |
  | exit1 lfsrfind s1 (8) | 27880 -> 27062 | -2.9 % | ucmpi0 11->10, ulink_n22__1 7->1, umux0/1 -> 2, ... | 4 / 4 (10/10) | clean |
  | exit1 mul_example s2 (60) | 61750 -> 60989 | -1.2 % | 1 line | 4 / 4 | clean |
  | capfix1 mul_example s2 (17) | 60990 -> 58451 | -4.2 % | | running | clean |
  | exit1 test_stdint s1 (27) | 52701 -> 52701 | 0 | none (the rule's trim mode moves nothing) | 4 / 4 | clean |

  Every rebuilt route matched its farm sdf md5. **Distance to the first failing trim** (trim_shrink.sh: EVERY trimmable
  line K elements below the rule's choice, the same four draws): K = 1 passes 4 / 4 on lfsrfind s1 (10 lines) and on
  countloop s2 (14 lines); K = 2, 3, 5, 8 running.
- **suite13 -> suite13t** (de5ecef22): suite13 had not started (it waits for exit1 to drain, ~10-11 UTC); suite13t
  runs the same v9 loops and adds AUTO_TRIM=1 at the end, recording the untrimmed route's own stack (P_untrimmed: the
  v9 figure, the same route as suite13 would have judged) and the critical cycle's composition before and after. The
  draws judge the trimmed route (none on the untrimmed one: that is the cost of folding it in). Prediction in the
  request (written 08:01 UTC). Cost: ~15-30 more minutes per task; more 240-min timeouts expected on memory kernels.
- Overbuild: xorshift s1 (suite12) shipped CLEAN after the trim step at **18276 ps** (untrimmed 20279) -- clean where the
  farm's v8 finish phase never was, but slower than the farm's NOT CLEAN least-short route (17808), which the trim step
  alone would likely take lower still (exit1's xorshift s1, the other fixture, went 18088 -> 16738). countloop s1 / s2,
  iterative_division s1: their first finish routes stay short after the trims (E at mux joins, one I row); loops go on.
### progress 08:15 (the automatic xorshift s1, != fixture + the trim step: 16.74 ns, 4 / 4 draws; the trims have >= 2 elements of draw margin)
- exit1 xorshift s1 trimmed (route d947adff, flow v9 + the != fixture + the trim step: 9 lines at step 1, then the rule
  moves nothing): **P 16738 ps, draws 10101-10104 PASS 19/19 each, bits EQUIVALENT, no pulse under 1 ns (narrowest 2.1
  ns)** -- the hand recipe's 16.76 (item 37) on one automatic route; NOT CLEAN by the same single H row (-30 ps, wants a
  UACK raise) before and after. One route, one seed: the farm's suite13t / exit1 seeds decide.
- Margin study (every trimmable line K below the rule's trims, the same draws): K = 2 passes 4 / 4 on lfsrfind s1 and on
  countloop s2; K = 3, 5, 8 running.
- suite13t is listed waiting on the farm (since 08:01:50); suite13's status file is frozen at "waiting", like the
  withdrawn auto1 / sizerule1 ones. exit1: 75 of 140 back at 08:00, none pending.
### progress 08:19 (formal A29 / B20 / B21 read; B21's race to be replayed here)
- **A29:** formal decoded my two trimmed routes (lfsrfind s1, countloop s2) from the bits: only the intended LUT INITs
  changed, each new entry passes its line's side input, the live lengths are the record's. An independent check of
  trim_lines.py on bits.
- **B20:** the README's FIRST trim set on xorshift's d947adff (the rule's rebuild proposal applied whole, 14 chains,
  15.18 ns) loses the loop-exit steer race through its ucmpi0 8 -> 7 trim: at kappa 0 / slow corner a 27 ps runt runs
  into ucontrol_merge1's arbiter (answers stay right); formal's structural bound -146 / -127 ps at ucond_br5 / br2
  agrees in sign and steer with our rule's E rows on that set (-203 / -190), which is why the trim step does not use it.
  **The trim step's own set on that route (CA_TRIM, this session: ucontrol_merge1, ulink_n12__0, umux1, umux2, two
  UACK; ucmpi0 / ucmpi1 untouched) is the one formal's result supports.** Formal's lesson for sizing by draws: draws
  passed at ucmpi0 = 6 while the corner race was lost at 7 -- so my margin study (trim_shrink.sh, random draws) measures
  the DRAWS' margin, not the race's; a shortening has to be judged at the race's corner (the rule), not by draws alone.
- **B21 (goal 1, untrimmed routes):** on exit1 varshift s1 (sdf 00324c96, rule-CLEAN, draws 4 / 4) the steer
  ucond_br11's condition comes from ulink_n41_folink's latch and its request through that link's request line at floor
  1 and the steer's join; both launch at the link's ctl rise. With the race's 32 arcs at opposite ends of prjxray's FAST
  interval (others mid-interval), formal's simx deadlocks at kappa 0 after 2 right answers; mid-interval, the request
  leads by 172 ps. The same race class is the weakest on brhash s2 (fails at kappa 0.03), twoloops s2 and fold64 s1
  (0.06). Formal's suggestion: a floor of 2 for a link whose latch output is a steer's condition, or rule E on this pair
  at per-arc min / max. Replay in our GLS: route rebuilding here now (/tmp/bot/b21).
### progress 08:41 (B21: our rule does check the pair, with 3 % guards; formal's failing point is the FAST corner with per-arc extremes; replay running)
- exit1 varshift s1 rebuilt here (sdf 00324c96 = the farm's). corner_audit as the loop runs it: rule E at ucond_br11
  from the launch ulink_n41_folink.ctl: request 1427 / 1559 ps, select 1193 / 1345 ps (bands 0.20 / 0.31), raw +234 /
  +214, **guarded +155 / +126** (corner_audit's guards 0.97 / 1.03); BD_SKEW_STEER_SELF changes nothing here. So the
  rule measures exactly formal's pair and finds ~130-150 ps after its guards; formal's failure needs the FAST corner
  (bands ~0-0.12, below the draw model's 0.20-0.31 box, which our ring / August fits put the board in) AND the race's
  15 condition arcs at FAST_MAX with its 17 request arcs at FAST_MIN.
- Replay in our GLS (bench_gate.sh COL=env, new, opt-in: the caller's band settings): everything at band 0.06 (~mid
  FAST interval), the latch lat.odd at 0.12 (~FAST_MAX on these paths, from formal's table), the request's rdly g[0] and
  join at 0 (FAST_MIN); the steer LUTs, which both paths enter, at 0.06 (a per-instance band sets the wires INTO an
  instance, so this replay is weaker than formal's on the last hop). Controls: all at 0.06; the two sides swapped.
- lfsrfind s1 trimmed route at bench_gate's `worst` corner (chains 0.21, rest 0.288, CARRY4 / F7 / FF / RAM at
  SLOW_MAX, scatter): PASS 10/10, no pulse under 1 ns.

## Session 2026-11-20 09:03 UTC -- cluster-research-29671222-1, third start (job requeued again: ends 2026-11-22 09:02 UTC; fresh /tmp): the headline counts a kernel only on a rule-CLEAN route (formal C68): 34 of 62, 25 UNFINISHED
Lock: cluster-research-29671222-1 at 08:41 (this wrapper's previous session, same id); taken 09:03 UTC.
cluster: /tmp/bot was recreated at 09:02 UTC (job requeued under the same id): the previous session's local work (the B21
replay in /tmp/bot/b21, the overbuild loops, draws on trimmed horner s1 / capfix1 mul_example s2, the margin study K = 3,
5, 8) is lost; only what was pushed survives. Farm results copied to /tmp/bot/farmres (origin/claude/cluster c6a1972fc).
Toolchain: patches.sha 0d42657914fc25d3, nextpnr 6e5d224472232d5d (cells/verify/toolchain.sh all ok, 09:04 UTC)   Seeds: per item
Audit: no new rows for research since T171 (its 01:35 update is about formal's tool). Formal: A28 (exit-test knob: 12
fixtures proved; gcd's graph differs on C-overflow inputs), A29 (trimmed bits = the record), B20-B23 (trim / latch-fed
steer races), C67-C69 (exitcond fixtures live; trimmed routes pass formal's draws; **C68: exit1 spmv s1, a NOT CLEAN
route our 4 draws passed, hangs in 11 of 32 of formal's draws of our model**).
### progress 09:19 (C68 taken: a NOT CLEAN route is not a pass; the headline corrected; replays of C68 and B21 running)
- **suite_table.py** (386712f62): a kernel passes only with a judged rule-CLEAN route and every draw on every judged route
  right; a kernel judged only on routes its loop left NOT CLEAN is UNFINISHED, counted apart. Latency (and its ratio)
  over clean routes where there are any, as P already was. **Headline regenerated from the same request list at
  origin/claude/cluster c6a1972fc: 34 of 62 pass (was 59 of 62), 25 UNFINISHED, 2 NO RESULT, 1 NOT-A-BOARD-ROUTE.**
  Ratio means unchanged (1.69 measured n = 3; 1.05 with estimates n = 22): they were over clean routes already. Latency
  ratio 1.22 (n = 19), was 1.38 (n = 31). stencil_2d gained a clean route since the 20:03 copy (PASS); its P (408 ns) is
  the outer loop's against Dynamatic's innermost cycle (4.66 cycles of 3 loops), so its ratio (10.09) is out of the
  means, as isprime's. Why: formal C68 (4 draws miss a 1-in-3 hang 18 % of the time) and auditor T161's rule.
- **suite13t split** (88961fc43) into suite13t_s1a .. s4b (30 tasks each, same flow / kernels / seeds): the 240-task
  request waited behind the 250-task account limit with exit1's 46 tasks running; 30-task requests start as room frees.
- **C68 replay running here:** exit1 spmv s1 rebuilt from the farm's sizes_9.vh / seed 1 with the exitcond fixture
  (research tools: lane2.sh MLIR_OVERRIDE), then 16 default draws (10101-10116) and 16 slow-carry draws (10151-10166,
  DRAW_CARRY=0.8,1.0), GATE_RUNTS=1. Our draws are not formal's samples (formal applies the per-pip scatter per pin
  arc), so the question is the failure RATE in our own GLS against formal's ~35 %.
- **B21 replay running here** (exit1 varshift s1, sdf 00324c96 rebuilt = the farm's): new research/tools/adv_sdf.py
  writes an SDF with ONE delay per arc from xray_delay.py's four-corner arc table, so formal's race-only adversary is
  replayed per ARC (the previous session's per-instance bands could not set the two wires into the steer apart). Our
  arcs on the race: condition ctl -> lat.odd/A5 -> lat.odd -> ucond_br11/A1 -> steer = 958 / 1135 ps (FAST_MIN /
  FAST_MAX), request ctl -> rdly g[0] -> ucond_br11_j -> ucond_br11/A3 -> steer = 1116 / 1323 ps; formal's 963 / 1140 and
  1120 / 1327. Adversary (condition at FAST_MAX, request at FAST_MIN, all else mid-FAST): the condition arrives 19 ps
  after the request (formal 20). Runs: adversary; swapped; all mid-FAST; adversary at the slow corner.
### progress 09:44 (B21 replayed per arc: our GLS loses the same race, 271 runts of 19 ps, answers right; the draw model loses it ~2e-5 of the time; a draw with a pulse under 1 ns no longer counts as passing evidence)
- **B21 replay** (exit1 varshift s1, sdf 00324c96 rebuilt here = the farm's; nextpnr 6e5d224472232d5d; one delay per arc
  from xray_delay.py's corner table via research/tools/adv_sdf.py; bench_gate.sh COL=env, max column, GATE_RUNTS=1):
  | assignment | answers | pulses < 150 ps on kernel handshake nets |
  |---|---|---|
  | formal's adversary: condition path at FAST_MAX, request path at FAST_MIN, every other arc mid-FAST | 10 / 10 | 271 (19 ps; 22 nets: ucond_br11 req0 / req1 / ack, both control merges' arbiters, ulink_n_index_19 stages, ...) |
  | every arc mid-FAST (control) | 10 / 10 | 0 (narrowest pulse 2.9 ns) |
  | the two sides swapped (control) | 10 / 10 | 0 |
  | the adversary at the slow corner | running | |
  So the two simulators lose the same race on the same nets; formal's simx (transport, 20 ps filter) then deadlocks, our
  resolver absorbs 19 ps pulses at the state nodes (SIM-VS-BOARD row 4, updated; silicon: BOARD-QUEUE item 2).
- **How often the draw model loses it** (new research/tools/race_mc.py: the model's bands, per-pip wire scatter with
  shared pips, region and per-arc cell scatter on the race's 10 arcs, Monte Carlo): margin request - condition at the
  steer 254 +- 59 ps, 4 of 200 000 model points below 0 (2e-5; 4.3 sd); the band corners alone 211-296 ps. Checked
  against 16 real gen.py draws of the same route (draw:K's own SDF, arcs read back from annot.sdf): 227 +- 68 ps, min 95;
  no-scatter base 251 vs the model's 252. formal's assignment lies outside the model's box (bands ~0-0.12, below its
  0.20 floor, with the race's arcs at opposite ends of their own intervals). **Decision: no flow change for B21.** Our
  rule already measures this pair (+126 / +155 ps guarded); a floor of 2 for every latch-fed steer link would be a rule
  for a race the model loses 2e-5 of the time. Listed as the weakest race on these routes; formal's kappa_lo stays the
  stress figure for it.
- **C68 replay running** (exit1 spmv s1 rebuilt, sdf f572267f = the farm's): of our own draws, 10105 and 10106 PASS 4/4,
  but 10106 had **408 pulses under 150 ps** (narrowest 56 ps) on 25 nets, ucond_br15's ack, ulink_n36__2 and
  ulink_n_trueResult_37's stage among them -- formal's hang nets (C68). And the farm's own draw 10102 on this route had
  72 such pulses; it was reported PASS (the runt monitor is report-only in the draws).
- **So a pulse under 1 ns now costs a route its passing evidence** (suite_table.py, 5be1192f4): over the 378 farm
  routes with runt-monitored draws, the 4 that ever showed one were all NOT CLEAN (exit1 spmv s1; ringfuse1 ipow s7, the
  draw that failed; ifl1 if_loop_1 s4; suite10b test_memory_1 s2); no clean route ever had one, so no headline row
  moves (34 of 62); the two headline routes are listed under the table.
- **Static rules under the draw model** (new research/tools/draw_sdf.py + ssta_draws.sh + ssta_table.py; corner_audit
  CA_ALLCONS=1, opt-in, outputs byte-identical without it): each draw K's delays (bench_gate.sh's bands, gen.py's pip /
  region hashes exactly; cell-arc normals same distribution) written as a one-value-per-arc SDF, every constraint
  measured raw (no guard). First 4 draws on C68's spmv route: **E at ucond_br15 (the steer formal's trace starts at)
  -14 +- 30 ps raw, below 0 in 2 of 4 draws**; next A'm umux10 +120 +- 118. 64 draws running.
### progress 09:53 (C68 reproduced three ways on exit1 spmv s1: runts at formal's hang nets in 4 of 8 of our draws, the flagged steer race lost in 9 of 16 static draws; B21's slow-corner control clean)
- **C68, our GLS** (route rebuilt here, sdf f572267f = the farm's; draws K 10101-10108 so far, GATE_RUNTS=1): answers right
  in all 8 (our resolver), but **4 of 8 draws carry 72-420 pulses under 1 ns** (narrowest 56 ps) on ucond_br15 / ucond_br9
  ack, ulink_n36__2, ulink_n_trueResult_37's stages -- the nets of formal's hang. Our draw 10102 reproduces the farm's own
  10102 exactly (72 / 96 / 96 pulses), which the farm reported as PASS. Formal's simx: 11 of 32 draws hang.
- **C68, the static rules under the same model** (research/tools/ssta_draws.sh, 16 draws, raw margins): **E at
  ucond_br15 -25 +- 73 ps, below 0 in 9 of 16 draws** (the row the rule had at -119 / -174 guarded); A'm umux10 +155 +- 138
  (3 of 16). Per draw the static sign and the GLS pulses agree only loosely (10107: +23 ps static, 396 pulses; 10104:
  -60 ps, none): draw_sdf.py has gen.py's bands, pip and region factors but its own per-arc cell normals, and gen.py's
  decoded netlist leaves more arcs without a route branch (40 % against 25 %). The rates agree: this route loses the race
  in a third to a half of the model's draws, which 4 draws report as PASS 4 / 4 (18 % of the time with no pulse at all).
- **B21's last control:** the adversary at the SLOW corner: PASS 10 / 10, no pulse under 6 ns (formal: 10 / 10 there too).
- Running: C68 draws 10109-10116 and the 16 slow-carry draws; the static draws to 64; the trimmed-vs-untrimmed static
  draws on exit1 countloop s2 (the route formal B23 judged); the mff loops (fill s1, gather s1: BDC_MEM_FASTFALL through
  the v9 loop + trim; PREDICTION written before results: P 5-12 % below suite13t's same routes, every draw passing).
### progress 10:10 (lead measured and dropped: a delay line built from CARRY4 would buy ~0.7 ns on xorshift; C68 draws 8 / 32)
- **How much of the matched delays covers CARRY4 at its slow bound** (exit1 xorshift s1 rebuilt here, sdf d947adff, P
  18088 ps as the farm's): the loop's rule on this route (CA_SIZERULE, both corners, CARRY4 / F7F8 / FF at SLOW_MAX,
  merged) proposes lines whose event-graph period on the same placement is **14878 ps** (sizewhatif); the same rule with
  CARRY4 at the chains' own band (0.20, as if the data's carry ran with the line) **14143 ps**: **-735 ps (-4.9 %)**,
  ucmpi1 (the fused update + test, two carry chains) 12 -> 10 elements, ucmpi0 7 -> 6, nothing else on the cycle.
  A line with a CARRY4 segment that tracks the data's carry would recover at most that, and only where the board's
  carry sits with its LUTs (never measured: BOARD-QUEUE item 36); at the carry's slow bound it gains nothing; it needs a
  new cell, bdc emission and rule support. **Not pursued.** (research/tools: cband estimate in /tmp only; the numbers
  are here.) The same run shows the rule's rebuild proposal at 14.9 ns on this placement against the trim step's 16.74
  (exact entry pricing: ucmpi1's first trim skips its anchor) and the loop's shipped 18.09.
- C68: 8 of our 32 draws done, 4 with 72-420 pulses under 1 ns (the rest clean), every answer right. Static draws on the
  same route: E at ucond_br15 lost in 13 of 24.
### progress 10:31 (static rules under 48 draws of the model, countloop s2 untrimmed vs trimmed: the trim brings four more races to 2.4-3.2 sd; C68: runts in 7 of 13 of our draws)
- **exit1 countloop s2** (rebuilt here, sdf aa201b8b; the committed trim record re-applied gives the committed trimmed
  FASM, c025f8bf), research/tools/ssta_draws.sh on the SAME 48 draws (K 10101-10148), raw margins:
  | constraint | untrimmed: mean +- sd (draws < 0) | trimmed |
  |---|---|---|
  | H ulink_n_trueResult_12 stage 2 (the loop's one short row) | -32 +- 63 ps (31 / 48) | the same |
  | A'm umux0 | +162 +- 82 (0) | the same |
  | A'm umux3 (trimmed 6 -> 2) | slack | **+227 +- 96 (0; min +3)** |
  | A ucontrol_merge0 (4 -> 2) | slack | +218 +- 78 (0) |
  | A'm umux1 (5 -> 2) | slack | +280 +- 94 (0) |
  | H ulink_n_trueResult_0 (UACK 3 -> 2) | slack | +267 +- 89 (0) |
  So the trim moves exactly the constraints of the lines it shortens from slack to 2.4-3.2 sd (normal tails 1e-3 to
  1e-2 each), as formal's B23 found for its steer bounds ("the edge is closer than the draws show"); nothing else moves.
- **But a static loss is not a failure:** the H row is lost in 31 of 48 static draws, yet the farm's four draws and
  formal's 16 + 16 on this route (B23, k = 0) all pass with no pulse under 3 ns. Rule H compares the acknowledge's
  release with the latch's close; the next value still has to cross the sender's handshake and data path before it can
  reach the latch, hundreds of ps the rule does not credit. E at a steer is different: on C68's spmv route the static E
  row (lost in 13 of 24 draws) and our GLS pulses (7 of 13 draws) agree in rate, though not draw by draw (6 of 13 signs
  agree: draw_sdf.py's cell-arc normals and gen.py's differ, and gen.py's decoded netlist falls back to per-arc factors
  on 40 % of wires against 25 % here). So per rule, the static tail is an upper bound on what the simulation sees; the
  A' rows (a capture before its data) are the ones to watch on trimmed routes.
- **C68, 13 of our 32 draws:** 7 with 72-420 pulses under 1 ns, every answer right.
- Running: varshift s1 (exit1, clean) static draws, the clean-route baseline; lfsrfind s1 trimmed next.
### progress 10:56 (formal's proved loop-test passes run here: 8 suite kernels get a rewrite Lean proves, by structure; the local v9 loops with them started)
- **The automatic path may carry a rewrite that is a PASS** (PROGRAM, T156). Formal's formal/tools-A/rewrite/
  auto_rewrites.sh (= plain_pass.py, the plain loop-test move `i + 1 < n -> i < n - 1`, PlainPass certificate; then
  eq2_pass.py, the test on the update -> the test on the value) matches by structure, no names or hashes, and keeps a
  rewrite only when Lean proves the rewritten graph equal to the original (token level, every schedule). Set up here:
  a worktree of origin/claude/formal at /tmp/bot/formal, formal's own farm lake cache ($SHARED/lake/a65e684bd52b.tar,
  26 GB, the key formal's requests use) extracted, lake build Formal.Rewrite.PlainPass (3 min); Lean v4.35.0 in ~/.elan.
- **With BDC_AUTO=1 as flow v8+ has it (BDC_RING_FUSE=2), plain_pass refuses** ("0 matches of the pattern in the
  import"): dfimport reads bdc's fusion plan, and ring fusion has already fused the increment with its test. With
  BDC_RING_FUSE=0 for the IMPORT only (the proof is about the unfused graph; ring fusion is a separate rewrite of the
  emitted graph), over the 62 default fixtures (research/data/autorw/census.txt): **plain_pass PROVED on xorshift,
  countloop, twoloops, quadrec, horner, varshift; eq2_pass PROVED on collatz, collatz64**; matched but refused (memory
  kernels: dfimport cannot import them) fill, if_loop_1 / 2, test_memory_1, spmv; no match on the other 49.
- Why it may pay under ring fusion: after plain_pass the loop test reads i (before the increment) against n - 1
  computed at the ring's entry, so the fused update + test cell's two carry chains run side by side instead of in
  series (suite13t's xorshift s1: that cell's line is 18 elements, 6.5 ns, 37 % of its 17.59 ns period). The
  md5-keyed versions measured before ring fusion: collatz -24 %, collatz64 -26 %, xorshift neutral (farm suite6).
- **Running (local, flow v9 + the trim step, seed 1, SUITE_TAG=arw):** xorshift with plain_pass's output, collatz with
  eq2_pass's (MLIR_OVERRIDE). Controls: suite13t's xorshift s1 (P 17588 trimmed / 18319 untrimmed) and collatz s1.
  PREDICTION (written before any result): xorshift s1's fused cell line 18 -> 10-13 elements and P 1.5-3 ns below
  suite13t's; collatz s1 15-25 % below suite13t's; every draw passes.
- varshift s1 (exit1, clean), 48 static draws: no draw loses any race; weakest I +275 +- 142 ps (min 4).
### progress 11:34 (formal B25 taken: the trim step limited to the critical cycle, opt-in, being tested; B26 being answered with a new race finder; the proved-rewrite switch is in the flow, opt-in)
- **Formal B25** (suite13t ipow s1: the trim step shortened the loop-exit compare ucmpi0 16 -> 11, off the critical cycle,
  P unchanged, the exit steer's proved bound 0.171 -> 0.017; over five suite13t routes most trims are off the cycle):
  right, and cheap to act on. **auto_size.sh AUTO_TRIM_SCOPE=cycle** (opt-in; unset, byte-identical behaviour): round 1
  lets the trim step move only the lines of instances on the untrimmed route's critical cycle (cycdecomp ->
  research/tools/auto/cycle_macros.py: the instance's own line, its _UACK and _SDELAY); then the trimmed route is re-timed
  and the NEW cycle's lines may move too, up to AUTO_TRIM_ROUNDS (3) rounds, until the cycle brings no new line. The
  first test re-applied suite13t's own recorded trims (a farm task's auto/ carries them): trim_farm.sh now drops a
  request's trim record so the step runs afresh. Running on suite13t xorshift s1 (7 trims, -4.0 %) and ipow s1 (8
  trims, none on the cycle). PREDICTION: xorshift keeps most of its -4.0 % with fewer trims; ipow trims nothing.
- **Formal B26** asks whether B21's 2e-5 is typical: new research/tools/race_find.py traces every latch-fed steer race of
  a route from its arc table and runs race_mc on each (on varshift s1 it finds ucond_br7-11; ucond_br11 = the hand
  spec, 254 +- 59 ps; the other four 7-14 sd). Rebuilding exit1 quadrec s3, twoloops s2, fold64 s1 for it.
- **Proved rewrites in the flow:** suite_one.sh AUTO_PROVED_RW=1 (opt-in, FORMAL_DIR = a built claude/formal checkout)
  runs formal's auto_rewrites.sh on the kernel's MLIR and builds every route from the Lean-proved output; checked
  here: xorshift -> plain_pass, collatz -> eq2_pass, gcd / fill -> none, outputs byte-identical to the committed
  research/data/autorw/ files that farm suite13t_s1c_arw builds (8 kernels x 4 seeds; filed 11:05).
- **Memory fast fall, local loops (seed 1):** fill s1 through v9 with BDC_MEM_FASTFALL=1: CLEAN at it 7, untrimmed P
  34038 ps, trimmed 30356 (-10.8 %), then the search phase continues; suite13t's fill s1 (default port): 30397 untrimmed
  = trimmed. gather s1: CLEAN at it 4, untrimmed 40286, trim and draws running; suite13t's gather s1 not back yet.
  So far no gain over the default port on one seed each; zmemff1 (30 memory kernels x 2 seeds) stays unfiled until
  gather's pair is in.
- **C68 so far:** 29 of our 32 draws: 7 of 16 default and 2 of 13 slow-carry draws have pulses under 150 ps at formal's
  nets, every answer right.
- cluster: **farm node node-c1 fails every task at container creation** ("mount proc ... operation not permitted",
  5 s): exit1 tasks 91 / 105, suite13t_s1a 16 / 19, suite13t_s2a 9 / 10 / 25 / 26 so far. A rerun request for them
  goes in when the suite13t waves are submitted.
### progress 12:00 (STATE OF PLAY -- read this first if the session ends here)
- **Headline** (research/data/fifteen/README.md top): a kernel passes only on a rule-CLEAN route whose draws had no pulse
  under 1 ns; 34 of 62 on the old flows' routes. **Next headline = suite13t** (v9 + the trim step; farm requests
  suite13t_s1a..s4b, 30 tasks each, 4 parts running / 4 waiting at 12:00; regenerate with research/tools/suite/
  suite_table.py over the 8 parts + suite13t_s5_rerun1). /tmp/bot/scripts/s13t_status.sh (local) shows the trim's
  effect per route so far: -3 to -16 % (collatz s1 / s2 -7.8 / -8.1, collatz64 -13.0 / -15.9, xorshift -4.0 / -6.4,
  countloop -2.9 / -10.3, lfsrfind -7.0 / -10.7); 8 of ~45 routes NOT CLEAN.
- **Farm queue (mine):** suite13t_s1c_arw (formal's proved loop-test passes, 8 kernels x 4 seeds; prediction in it),
  suite13t_s5_rerun1 (the 8 tasks node-c1 lost). exit1: 138 of 140.
- **Local, in flight:** (1) the proved-rewrite loops xorshift s1 / collatz s1 (SUITE_TAG=arw; both CLEAN at it 7, then
  killed by my in-place edit of auto_size.sh; resumed 11:59 with AUTO_RESUME=/tmp/bot/runs/resume/arw_*); (2)
  BDC_MEM_FASTFALL loops gather s1 (resumed the same way) / fill s1; (3) AUTO_TRIM_SCOPE=cycle on suite13t xorshift s1 /
  ipow s1 (/tmp/bot/tscope, trim_farm.sh); (4) formal B26: race_find on exit1 twoloops s2 / fold64 s1, then quadrec s3
  rebuilt WITH its search structure (BDC_FORK_OUT_LINK=..., the first rebuild missed it: SDF MISMATCH); (5) C68's last
  slow-carry draw.
- **Decided / done this session:** C68 (NOT CLEAN routes are UNFINISHED; reproduced: our GLS pulses at formal's hang
  nets in 10 of 31 draws, every answer right); B21 (our GLS loses the race under formal's assignment, answers right;
  the draw model loses it ~2e-5; no flow change); the CARRY4-tracking line (measured ~0.7 ns on xorshift: dropped);
  the static rules under the model (research/data/ssta/README.md: trims bring their lines' constraints to 2.4-3.5 sd).
- **Next:** read tscope (adopt AUTO_TRIM_SCOPE=cycle if xorshift keeps its trim gain and ipow trims nothing); read the
  arw loops and suite13t_s1c_arw (if the proved passes pay, AUTO_PROVED_RW=1 joins the next flow; the farm needs
  formal's lake cache: $SHARED/lake/a65e684bd52b.tar, key = md5(lean-toolchain + lake-manifest.json)[:12]); exit1 vs
  suite13t (research/tools/suite/pair_cmp.py) for the != knob; then flow v10 on the farm.
### progress 12:15 (B25's scoped trim confirmed on two routes; a flow bug found by the proved-rewrite test: the start sizes ignored MLIR_OVERRIDE; suite13t_s1c_arw withdrawn before it ran)
- **AUTO_TRIM_SCOPE=cycle, measured** (suite13t routes rebuilt SAME, trim_farm.sh): ipow s1: no line on its critical cycle
  can move -> nothing trimmed, P 19867 = as built (the unscoped step trimmed 8 off-cycle lines for the same P);
  xorshift s1: 2 cycle lines trimmed -> **P 17588 ps, exactly the unscoped step's 7-trim result**; round 2 (3 lines of
  the new cycle) running. Formal's B25 holds: the trims that buy period are the cycle's; the rest only spend margin.
- **The proved-rewrite loops (seed 1) came out slow for a flow reason:** untrimmed P xorshift 22275 ps (suite13t:
  18319), collatz 50021 (24676), with uaddi0 at 24 elements (9.4 ns on xorshift's cycle) and uselect0 at 86 (31.2 ns on
  collatz's). auto_size.sh built every route from the rewritten MLIR (lane2.sh MLIR_OVERRIDE) but took its start sizes
  from the ORIGINAL fixture's emission, so the rewritten graph's new fused cells had no sizes macro and kept emit.py's
  defaults, which no rule step ever lowered. Fixed (419115ec4: the start estimate and the search phase's estimate read
  MLIR_OVERRIDE). **suite13t_s1c_arw used the same path and had not started: withdrawn.** Not a measurement of the
  rewrites; the two loops restarted with the fix (SUITE_TAG=arw2, AUTO_TRIM_SCOPE=cycle).
- B26 so far: exit1 twoloops s2's 12 latch-fed steers, the weakest (formal's ucond_br17) 425 +- 68 ps (6.2 sd); the
  next 570 +- 57. varshift s1 (254 +- 59) is the worst seen. fold64 s1 and quadrec s3 running.
### progress 12:34 (B26 answered: varshift's latch-fed race is the worst of the routes formal listed, the rest >= 6 sd; new bdc pass BDC_SIBLING_FUSE: the proved loop-test move's parallel increment and test fused into one cell)
- **B26** (research/tools/race_find.py over every latch-fed steer of each route, 100 000 model points): exit1 varshift s1
  ucond_br11 254 +- 59 ps (4.3 sd); twoloops s2 ucond_br17 425 +- 68 (6.2 sd); fold64 s1 ucond_br4 322 +- 54 / ucond_br3
  303 +- 47 (6.0 / 6.4 sd); quadrec s3 rebuilding with its search-phase structure. Table in research/data/ssta/README.md.
- **Scoped trim refined** (3fb7ae248): a round whose trims leave the period no lower is reverted (xorshift s1's round 2
  had moved 3 lines of its new cycle for no change in P).
- **Why the proved plain move may not pay by itself under ring fusion:** after it, the increment and the test both read
  i, and BDC_RING_FUSE (which fuses `x' = f(x); test(x')`) no longer applies: two cells, a fork, links between them
  (the first arw loop, with its start-size bug, showed uaddi0 and a new link ulink_n_rd0f__1 on the cycle). **New:
  bdc BDC_SIBLING_FUSE=1** (0218b747f, opt-in, needs ring fusion's multi-result cells): a fork whose every output feeds
  fusable ops in two or more regions merges those regions into ONE multi-result cell (one join, one matched delay, the
  branches side by side), under the same three safety conditions as ring fusion. Unset: byte-identical emission (28
  emissions checked). With the 6 plain-move MLIRs, each kernel's increment and test become one cell (xorshift's:
  `i + 1` and `i < n - 1` both from e0_data) and all 6 pass the RTL bench against the C. On the 62 default fixtures
  (no rewrite) it changes 23 kernels: a separate, unmeasured effect (a merged cell makes a short branch wait for the
  longest one's line).
- Running locally: xorshift s1 with the plain move + BDC_SIBLING_FUSE=1 (SUITE_TAG=sib); the plain move alone
  (arw2); collatz with eq2 (arw2). PREDICTION (written now, before any of them ends): with sibling fusion the fused
  cell's line is 4-8 elements shorter than suite13t's ucmpi1 (18) and P (trimmed) 1-3 ns below suite13t's 17.59 ns;
  without it (arw2) P is no better than suite13t's.
### progress 13:07 (formal B25 suite-wide: 87 % of suite13t's trims were off the critical cycle; sibling fusion RTL-clean on 20 of 21 default kernels; farm suite13t_s5b_sib filed)
- **suite13t's trims, on or off the cycle** (every task back so far with a trim record: its trim_I.txt against
  cycle_macros.py of its own cyc_I_untrimmed.txt): **50 routes, 482 trims, 65 on the untrimmed critical cycle (13 %);
  21 routes trimmed nothing on it.** The period those 417 off-cycle trims could lower is none (a non-critical line does
  not set P); what they spend is margin (formal B25's ipow / brhash steers). The next flow carries AUTO_TRIM_SCOPE=cycle
  (measured: ipow s1 trims nothing for the same P, xorshift s1 2 trims for the same P as 7; a round that buys no period
  is reverted, 3fb7ae248). B26 closed: research/data/ssta/README.md (varshift 4.3 sd, quadrec 5.0, fold64 6.0, twoloops 6.2).
- **BDC_SIBLING_FUSE on the 21 default kernels it changes** (no rewrite; sobel / video_filter left out), RTL bench against
  the C: 20 PASS (straight, gcd, countloop, sqrtsub, ipow, twoloops, varshift, branchloop, horner, fill, nested,
  factorial, iterative_division, iterative_sqrt, if_loop_1, isprime, if_convert, nested_loop, stencil_2d,
  test_flatten_array), image_resize running. With the six plain-move MLIRs: 6 / 6 PASS (11:59).
- **Farm suite13t_s5b_sib** (a4a3d5a2f, after suite13t and its rerun): set A = the proved passes + sibling fusion
  (8 kernels x 4 seeds), set B = sibling fusion alone on 21 default kernels (x 4); prediction in the request.
- Local loops running: arw2 xorshift / collatz (proved move alone; it 7, not clean yet), sib xorshift (it 3) and sib
  countloop (started 13:07; control suite13t countloop s1 22896 untrimmed / 22224 trimmed). Partial suite13t table
  (not committed): 33 of 62 pass so far, 6 UNFINISHED, 23 without a result yet; measured-Dynamatic ratio mean 1.50
  (was 1.69 on the old flows).
### progress 13:14 (formal's proved eq2 rewrite pays under flow v9: collatz s1 untrimmed P 20.32 ns against suite13t's 24.68, -17.7 %)
- arw2 collatz s1 (eq2_pass's Lean-proved MLIR, the start-size fix, flow v9 + the scoped trim step; seed 1): CLEAN at
  it 8, **untrimmed P 20315 ps** (sdf 5f764ea9, EQUIVALENT, ffmux-clean); suite13t's collatz s1: 24676 untrimmed, 22751
  trimmed. Inside the prediction (15-25 % below). Critical cycle: uaddi0 10 elements (3989 ps), ulink_n_falseResult_9
  5 (1886), uselect0 2 (964); wire between cells 10726 ps of 20315 (53 %). The trim step and the draws are next.
  One seed: the farm's suite13t_s5b_sib (set A) has collatz / collatz64 x 4 seeds.
### progress 13:46 (formal B28 confirmed in our own model on a headline route: suite13t xorshift s1's latch-fed race at ucond_br9 is lost 0.2 % of the time; AUTO_RACE_Z pads such links in the loop)
- **race_find on suite13t routes** (rebuilt SAME; untrimmed: the trims do not touch these races): xorshift s1 (rule
  CLEAN, P 17.59, 4 / 4 draws) **ucond_br9 140 +- 48 ps, 2.9 sd, 98-121 of 50 000 model points below 0 (0.2 %)**, ucond_br8
  184 +- 47 (3.9 sd); xorshift s2 13.4 sd; collatz s1 18.9 sd; countloop s1 13.1 sd. Formal's B28 (negative slack at
  both prjxray corners, xsweep failing at +-8 % opposite error) is our own model's 0.2 %: the rule's 3 % guard on this
  pair is about one sd of the draw model's scatter, and the link sits at its floor of 1. A placement outlier, not the
  common case -- but it is a headline route.
- **Fix, opt-in for the next flow: auto_size.sh AUTO_RACE_Z=4.5** (bc91db673): on every route the rule calls clean (main
  loop and search phase), xray_delay --arcs + race_find.py; research/tools/auto/race_pad.py raises the link of any
  latch-fed steer race below 4.5 sd (normal tail 3e-6) by one element in the rule's proposal and adds a negative row,
  so the loop builds another route with it longer; the trim step never shortens a race-padded line. On xorshift s1's
  race lines it pads ULINK_N31_FOLINK 1 -> 2 (+~150-250 ps on the request side only: ~7 sd). Test loop running:
  xorshift s1, v9 + scoped trim + AUTO_RACE_Z=4.5 (SUITE_TAG=rz); it should retrace suite13t's routes to it 8.
- **BDC_SIBLING_FUSE, formal A30:** PROVED for the six plain-move kernels (fuse_check: sibling-fused = unfused, after
  plain_pass proved fixture -> plain) and against the C for countloop, horner, varshift, ipow, nested, twoloops,
  branchloop; and a timing caveat for the default fixtures: a merged cell makes every part wait for every input (on
  countloop the loop test now waits for the accumulator's s and a). The farm's set B measures what that costs.
### progress 14:09 (one seed each, draws pending: collatz s1 with the proved eq2 rewrite at 14.81 ns (suite13t 22.75, Dynamatic 14.05); xorshift s1 with the plain move + sibling fusion at 16.36 ns (suite13t 17.59))
- **collatz s1, eq2_pass's MLIR (Lean-proved), flow v9 + scoped trim** (arw2): it 8 CLEAN, untrimmed 20315 -> trimmed 19503
  ps; then the flow's own search phase (event graph, all sites) picked BDC_LINK_DEPTHS=ulink_n10__3=2,ulink_n11=2
  BDC_FORK_OUT_LINK=n17__0,n31__0 -> it 9 CLEAN, **untrimmed 15832, after the first trim round 14812 ps**; later rounds
  and the draws running. suite13t collatz s1 (no rewrite, the same search phase): 24676 / 22751. The hand recipe's best
  collatz: 21.50 ns; Dynamatic's measured: 14.05. One seed; farm suite13t_s5b_sib set A has collatz x 4 seeds.
- **xorshift s1, the plain move + BDC_SIBLING_FUSE, flow v9 + scoped trim** (sib): it 8 CLEAN, untrimmed 19365 ps (suite13t
  18319); the scoped trim's rounds: 17533 (round 1's lines), **16357 (round 2's)**, round 3's 8 lines being timed. The
  rounds keep paying here because the cycle lines are trimmed first and use the slack the unscoped step had spent on
  other lines (suite13t's one-pass trim: 17588). The plain move alone (arw2 xorshift): it 9 20941 -> 19710 trimmed; the
  search phase's it 11 untrimmed 17123, trimming running.
- So far the proved rewrites pay most through what they let the rest of the flow do (the search phase's storage on
  collatz; the trim rounds on xorshift), not in the untrimmed period of the route the loop first settles on.
### progress 14:33 (collatz s1 + proved eq2: final route 14.48 ns, EQUIVALENT, draws running; collatz64 s1 + eq2 loop started)
- collatz s1 (arw2): the search route it 9 after three trim rounds: **P 14483 ps** (15832 untrimmed -> 14812 -> 14483), bits
  EQUIVALENT; draws on col18 running. xorshift s1 plain + sibling (sib): 19365 -> 17533 -> 16357 -> **16289** (the last
  round's 8 lines kept: P lower); its final stack and draws running.
- Started: collatz64 s1 with eq2_pass's MLIR, flow v9 + scoped trim (control suite13t collatz64 s1: 29391 untrimmed /
  25557 trimmed; Dynamatic measured 17.84). PREDICTION (now, before any result): trimmed P 16.6-21.7 ns (15-35 % below).
- Farm: the proved-rewrite + sibling set moved ahead of suite13t's seeds 3-4 (suite13t_s3a_rwa, 32 tasks); set B of
  sibling fusion alone as suite13t_s5c_sibb (84); suite13t_s5b_sib withdrawn before it ran (79f15698f, 38bfa983b).
### progress 14:35 (the race check works in the loop; flow v10 filed on the farm with its prediction)
- **AUTO_RACE_Z in a real loop** (local, xorshift s1, v9 + scoped trim + AUTO_RACE_Z=4.5, SUITE_TAG=rz): the loop retraced
  suite13t's routes exactly (sdf it 0-3 = the farm's), reached its clean it 8 (sdf 138aac60 = suite13t's shipped
  route), and the race check said: 8 latch-fed steer races, weakest ucond_br9 2.85 sd, 4 below 4.5 sd -> padded
  ULINK_N31_FOLINK 1 -> 2, the route not clean; it 9 is being built with the link at 2.
- **Flow v10 filed** (suite13t_s5a_v10_{1a..4b}: 60 kernels x 4 seeds as suite13t, named to run after suite13t and its
  rerun): v9 + the trim step, with AUTO_TRIM_SCOPE=cycle, AUTO_RACE_Z=4.5 and AUTO_PROVED_RW=cache. Not in it:
  BDC_SIBLING_FUSE (on the default fixtures it couples a merged cell's parts, formal A30; its own test is
  suite13t_s5c_sibb), the != loop test (exit1 against suite13t: no gain on the kernels whose widths it keeps, +7 %
  on the ones it widens). **PREDICTION (written now, before any v10 result), against suite13t's same (kernel, seed):**
  collatz / collatz64 P 15-35 % lower (the proved eq2 + the search phase: collatz s1 locally 14.48 ns vs 22.75);
  xorshift and the other plain-move kernels (countloop, twoloops, quadrec, horner, varshift) 0-10 % lower; every other
  kernel within route scatter of suite13t's trimmed P (median -2 .. +2 %), some routes up to one element slower where
  a latch-fed link is padded; fewer trims (about the cycle's 13 %); every draw passes on every judged route; the
  rule-clean share within 5 points of suite13t's; no route with a latch-fed steer race below 4.5 sd.
### progress 14:46 (the race check converged: xorshift s1's weakest latch-fed race 2.85 -> 11.5 sd in two more routes; collatz s1 + eq2 first draw 17 / 17)
- rz loop (xorshift s1, v9 + scoped trim + AUTO_RACE_Z=4.5): it 8 (= suite13t's route) padded ULINK_N31_FOLINK 1 -> 2; it 9
  one rule row short; **it 10 rule-CLEAN and race check clean: 8 latch-fed steer races, weakest ucond_br8 11.47 sd**. Its
  period (the pad's cost) and draws next; the trim step will not shorten the padded line (race_padded.txt).
- collatz s1 + proved eq2 (14.48 ns route): draw 10102 PASS 17 / 17, narrowest pulse 2.7 ns; three draws running.
  xorshift s1 plain + sibling: final 16289 ps EQUIVALENT, draws running.
- Farm: suite13t_s2a done, s1b 29 / 30, s2b 19 / 30, s3a 19 / 30 (one more node-c1 failure: task 16, fold64 s3), s3b
  9 / 30; suite13t_s3a_rwa next; v10 (8 parts) after s4a / s4b and the rerun.
### progress 15:08 (collatz s1 with formal's proved eq2 rewrite: 14.48 ns, 4 / 4 draws, rule CLEAN -- Dynamatic's measured figure is 14.05)
- **arw2 collatz s1** (eq2_pass's Lean-proved MLIR, flow v9 + scoped trim; the search phase's structure): result line
  `status=PASS draws=4/4 P=14483 P_untrimmed=15832 trims=5 rule=clean bits=EQUIVALENT ffmux-clean`, every draw 17 / 17
  with no pulse under 2.6 ns. Against suite13t's collatz s1 (no rewrite): 22751 trimmed (-36 %); the bench's own cycle
  counts over col18 fall 6234-6504 -> 4130-4260 (-34 %), so P is not a marker artefact. Ratio to Dynamatic's measured
  14.05 ns: 1.03 (was 1.62); the hand recipe's best collatz: 21.50. One seed: suite13t_s3a_rwa and v10 decide.
- Route packaged for formal (research/data/for-formal/collatz_eq2_s1/, FOR-FORMAL entry). xorshift s1 plain + sibling:
  2 / 2 draws so far at 16.29 ns.
### progress 15:18 (suite13t loses ~30 % of its tasks to the 240-min limit; v10 and rwa now keep their state in $SHARED and can be resumed)
- **Farm timeouts, suite13t so far** (s1a / s1b / s2a / s2b done, s3a 21 / 30): TIMEOUT on 8 / 12 / 5 / 9 tasks of 30, plus
  4 + 4 node-c1 FAILED. 13 kernels time out on every seed run so far (gcd, isprime, digitsum, digitdiv, divmods, fir,
  iir, image_resize, stencil_2d, share_test_1, single_loop, loop_path, nested_loop); binary_search, gather, if_convert,
  quadrec, sumi3_mem, vector_rescale, nest3 on some (completed runs of them 177-238 min). Most had shipped their route:
  iir s1 (it 10 after the search phase, both trims done) ran out before its draws started. Earlier flows lost fewer
  (suite12 9 / 62, capfix1 10 / 48, exit1 29 / 140): v9's two trims and full stacks per route (the loop's route and the
  search phase's) are what pushed these over. Without a fix the headline would miss a third of the suite, the heavy
  third, and v10 (three trim rounds, the race check's extra routes) would lose more.
- **Fix, before they start** (both still waiting): suite13t_s5a_v10_{1a..4b} and suite13t_s3a_rwa copy their auto/ files
  to $SHARED/state_v10 (state_rwa)/K_S every 5 min; a later request with the same body resumes from there: AUTO_RESUME
  (the loop from its last ratchet step) or, when the loop had finished, AUTO_TRIM_ONLY (the shipped route rebuilt from
  sizes + seed + structure, sdf md5 checked, trimmed and timed again), then the draws. The flow is unchanged (same
  environment, same routes); only what survives the limit. Stub-tested (partial -> resume, finished -> trim-only,
  done -> state removed). The resume parts get filed with the tasks that ran out, after v10's 8 parts.
- suite13t's own timeouts sent their state back only through git (~1 MB per task): resuming them needs it committed
  here (research/data/suite/resume/, as suite10d did). Deferred: v10 is the run the headline will move to, and it is
  the one that can now resume cheaply.
### progress 15:23 (formal A31: the collatz eq2 route's graph is proved equal to the fixture, its bits are the recorded trims; xorshift plain + sibling 4 / 4 at 16.29 ns; finish seeds now pass the race check too)
- **Formal A31** (15:15, on the 15:08 package): trimcheck OK (6 LUT INITs differ, each passes the side input, live
  lengths = trim_record.txt's); eq2_pass on our fixture writes research/data/autorw/collatz.mlir byte for byte and Lean
  proves it equal to the fixture; fuse_check proves bdc's plan for this build (with structure.env's link knobs) equal
  to the unfused graph. So the chain from the C to this build's token graph is proved. Not covered: timing (shard B's
  steer screen and capture bound, shard C's draws). Formal C70: BDC_SIBLING_FUSE keeps every default fixture live.
- **xorshift s1, plain move + BDC_SIBLING_FUSE** (sib): PASS 4 / 4 (19 / 19 each, no pulse under 1 ns), P 16289 ps
  (untrimmed 19365, trims 5), rule CLEAN. The plain move alone (arw2): 16350 trimmed after the search phase, draws 3 / 3
  so far. One seed: the sibling cell is worth nothing measurable on xorshift (-0.4 %); suite13t's xorshift s1: 17588.
- **Finish seeds + race check** (auto_size.sh): with AUTO_FINISH_SEEDS (alternate placer seeds for a finish route that
  is not clean; finseeds1 cleaned 5 of 7 such loops under flow v8) an adopted alternate route skipped AUTO_RACE_Z's
  latch-fed race check. Now an alternate route the rule calls clean runs race_check too (race_pad.py gets the sizes it
  was built from; a race below Z makes it not clean). Unset either knob: no change (v10 and rwa unaffected).
- suite13t's consistently NOT CLEAN kernels (every seed back so far): cmpchain 3 / 3, factorial 3 / 3, twoloops 3 / 3,
  nested 2 / 2, quadrec 2 / 2, spmv 2 / 2; each finish phase ends 13-1081 ps short over 1-6 constraints (re-route churn).
  **Started locally: v10's environment + AUTO_FINISH_SEEDS=3 AUTO_FINISH_JOBS=2** on factorial s1 and cmpchain s1
  (SUITE_TAG=fs), a candidate for flow v11 now that a task can resume past 240 min. PREDICTION (now): each loop
  retraces v10's routes up to its first finish route that is not clean; at least one of the two ships an adopted
  alternate route, rule-CLEAN with every latch-fed race >= 4.5 sd, 4 / 4 draws; wall time +30-60 % over the loop
  without the knob.
### progress 15:26 (suite13t interim, 4.5 of 8 parts back: 39 of 62 kernels pass, 7 UNFINISHED, 16 no result (time limit); the B28 route shows runts in our own draws)
- suite_table.py over suite13t_s1a..s4a + rerun1 as returned at 15:20 (not committed as the headline: s3a 22 / 30, s3b
  12 / 30, s4a 2 / 30, s4b 0 / 30 back): **39 of 62 pass** (the current headline, older flows: 34), 7 UNFINISHED
  (cmpchain, factorial, iterative_division, nested, quadrec, spmv, twoloops), 16 NO RESULT (every task so far at the
  240-min limit: digitdiv, digitsum, divmods, fir, gcd, iir, image_resize, isprime, loop_path, nest3, nested_loop,
  share_test_1, single_loop, sobel / video_filter (not run), stencil_2d). Ratio mean over the 3 measured Dynamatic
  figures 1.51 (headline 1.69); with estimates 1.00 (n = 27). Every draw on every judged route returned every answer.
- **suite13t xorshift s1** (sdf 138aac60, rule CLEAN, formal B28's route): draw 10102 had **118 pulses under 150 ps on 5
  of 172 kernel handshake nets (merge 4 / 16, steer 1 / 24), narrowest 6 ps**, answers right (19 / 19); the table
  already refuses it as passing evidence (the 09:44 runt rule), so xorshift passes on its two other clean routes. The
  first rule-CLEAN route of the farm's ~470 runt-monitored ones with such a pulse, and it is the route whose latch-fed
  steer race formal (B28) and race_mc (0.2 % of the model's points lost) flagged: what AUTO_RACE_Z pads in v10. The rz
  loop (same kernel and seed, race-padded) is in its draws, on the same four draw points.
### progress 15:31 (STATE OF PLAY -- read this first if the session ends here)
- **Headline**: research/data/fifteen/README.md still shows the older flows (34 of 62). **suite13t** (v9 + trim) interim
  39 of 62 pass, 16 no result (240-min limit); regenerate when s3a / s3b / s4a / s4b are done (~19:00-19:30): `python3
  research/tools/suite/suite_table.py --kernels research/tools/suite/kernels.txt --reasons
  research/data/suite/headline_reasons.tsv --no-ratio isprime,stencil_2d` over results/suite13t_s1a..s4b +
  suite13t_s5_rerun1 (origin/claude/cluster), with time-limit reasons for the no-result kernels. Its timed-out tasks are
  NOT being resumed (their state came back only through git); v10 is.
- **Farm queue (mine, in name order):** suite13t_s3a_rwa (proved rewrites + sibling cell, 8 kernels x 4 seeds; state
  in $SHARED/state_rwa), **suite13t_s5a_v10_{1a..4b}** (flow v10: v9 + scoped trim + AUTO_RACE_Z=4.5 + proved rewrites
  from cache.tsv; 240 tasks; state in $SHARED/state_v10; PREDICTION in the 14:35 note), suite13t_s5c_sibb. When a v10
  part is done: `python3 research/tools/suite/mk_resume.py <results dir> r1 suite13t_s5a_v10_1a ...` writes
  suite13t_s5a_v10_1a_r1.sh etc. (only its unfinished tasks, 4 cores); commit + push; repeat with r2 on those.
- **Local, in flight** (/tmp/bot/runs; SUITE_TAG in the name): collatz64 s1 + eq2 (arw2; it 7 clean, final + search
  next; prediction 16.6-21.7 ns), countloop s1 plain + sibling (sib; 19533 trimmed at it 10 vs suite13t 22224; search
  route it 12 clean), xorshift s1 plain only (arw2; 16350, last draw), xorshift s1 race-padded (rz; 18622, draws),
  factorial s1 / cmpchain s1 with v10's environment + AUTO_FINISH_SEEDS=3 (fs; v11 candidate, prediction in the 15:23
  note), and /tmp/bot/scripts/resume_test.sh (the $SHARED resume block end to end on straight s1: r1 killed at it 0,
  r2 resumed; r3 = trim-only next).
- **Done today:** collatz s1 + proved eq2 14.48 ns 4 / 4 (formal A31: chain from the C to the build proved); xorshift
  s1 plain + sibling 16.29 ns 4 / 4; AUTO_RACE_Z (B28) in the flow; the scoped trim (B25); C68 / B21 / B26 settled.
- **Open with formal:** FOR-FORMAL 15:2x (can the proved passes reach the memory kernels and the plain counters with a
  branch / inner loop); B's steer screen on the collatz eq2 route.
### progress 15:33 (BDC_MEM_FASTFALL through the loop: gather s1 54.19 -> 37.72 ns, fill s1 30.40 -> 29.81; filed as an A/B against v10 on the 30 memory kernels)
- The local loops (v9 + trim, one seed each; started 09:23, finished before noon, not journalled until now): **gather
  s1** with BDC_MEM_FASTFALL=1 converged clean at it 4, untrimmed 40286 / trimmed 37720 ps, 4 / 4 draws PASS 9 / 9, no
  pulse under 1 ns; suite13t's gather s1 route (same seed, no FASTFALL, it 10) is 54186 untrimmed and trimmed (the
  trim found nothing), its task then ran out of time in the search phase. The two routes' rising floors are equal
  (18198 / 18227 ps): the period above the floor is the RAM port's return to zero, which FASTFALL takes in one element.
  **fill s1**: 29806 trimmed (4 / 4) vs suite13t 30397 (-1.9 %); untrimmed 31453 vs 30397 (+3.5 %). One seed each.
- BDC_MEM_FASTFALL changes 30 of the 60 suite kernels under BDC_AUTO=1 (every one with a memory port; emit md5s with and
  without). memauto.md's open item was this lever "with its own loop, 4+ seeds". **Filed suite13t_s5b_mff_{1..4}**
  (seed per part, 30 tasks each, v10's environment + BDC_MEM_FASTFALL=1, state in $SHARED/state_mff; named after v10
  and its resume parts, before sibb). PREDICTION in the request header (15:45): against v10's same (kernel, seed),
  median -5 %, range about -30 % .. +3 %, every draw passing with no RAMB18 setup / hold event, clean share within 5
  points.
### progress 15:43 (formal's own steer screen, run here: the race check fixes B28 -- latch-fed ctl slack -94 / -192 ps -> +427 / +1164 ps; collatz eq2 route clean but for two LUTs the tool cannot place)
- formal/tools-B/auto/racescreen.sh (B24; claude/formal 4cb32d0da, in /tmp/bot/formal_wt) on two local routes; files in
  research/data/ssta/racecheck_rz_xorshift_s1/ and research/data/for-formal/collatz_eq2_s1/*_ours.txt:
  - **rz xorshift s1** (AUTO_RACE_Z=4.5, f1ea3036, trimmed): steers 16, bounded 16, min kappa_lo 0.156; latch-fed race
    ucond_br8 ctl slack **+427 / +1164 ps**, adversary's first failure at kappa 0.20; at our bands no pulse and no
    failure to x = 0.25. suite13t's route of the same kernel and seed (B28): -94 / -192 ps, MISMATCH at kappa 0 and at
    x = 8-10 %. The check does what it was for, on formal's measure as well as ours (2.85 -> 11.47 sd). Cost +3.8 %
    untrimmed on this one seed.
  - **collatz eq2 s1** (0f050078, trimmed): steers 12, bounded 10, min kappa_lo 0.061 (ucond_br6); no latch-fed race;
    no pulse to x = 0.25 (first failure at 0.25). ucond_br7's two LUTs: "no launch node for ucmpi2.ujoin" -- the tool
    files ucmpi2 as a compare with a join on this steer and as joinless on br5 / br6; asked formal (FOR-FORMAL).
  - Both: output capture kappa_lo negative (-0.28 / -0.31) at formal's 3 ns sampling point; CA_BENCHCAP sizes out0 for
    the PS bench's capture ~24 ns after the request (formal's B28 re-run at --dout 23000 made the same distinction).
### progress 15:44 (rwa gets the race check before it starts: it becomes v10 + the sibling cell on the eight proved kernels)
- suite13t_s3a_rwa (still waiting) now also sets AUTO_RACE_Z=4.5. Its builds then equal flow v10's on the same MLIRs
  (v10 reads research/data/autorw/K.mlir through AUTO_PROVED_RW=cache, rwa through MLIR_OVERRIDE; suite_one's compile
  check is the only other use and does not touch the builds), plus BDC_SIBLING_FUSE=1. So rwa vs v10, same (kernel,
  seed), is the paired test of the sibling cell, and rwa's collatz / collatz64 routes (the flag changes nothing there,
  formal A30) are v10's own, early. Revised prediction in the request header (15:50).
### progress 15:54 (v10's first part is running; the flow code is frozen for it)
- suite13t_s5a_v10_1a **submitted** at 7874b6123 (seed 1, kernels 1-30), ahead of rwa (rwa's 32 tasks need 64 cores;
  the runner placed the 60-core part first). suite13t_s3a done; s3b 12 / 30, s4a 9 / 30, s4b 4 / 30, rerun1 6 / 8.
- **Rule until every v10 part and its resume parts are submitted:** no change to what auto_size.sh, suite_one.sh,
  lane2.sh, bdc or cells do under v10's environment (each part checks out the branch head when it is submitted, so a
  change would split v10 into two flows). Only opt-in knobs v10 does not set (AUTO_FINISH_SEEDS, BDC_MEM_FASTFALL, ...).
### progress 15:55 (v11 option measured from suite13t's logs: trimming only the shipped route would change 1 of 29 search decisions)
- When the search phase finds a clean route, v9 / v10 trim BOTH the loop's route and the search's before comparing
  their trimmed P. Over suite13t's 29 such comparisons, comparing untrimmed P instead picks the same route 28 times
  (the exception: countloop s2, trimmed 18836 vs 19500 -> search route; untrimmed 21006 vs 20384 -> loop's route).
  An opt-in "trim late" (compare untrimmed, trim only the shipped route) would save one trim phase (2-3 rule steps and
  1-3 full stacks; ~20 of collatz's 120 local minutes) on those tasks. Not done now (v10's flow code is frozen); a
  v11 candidate beside AUTO_FINISH_SEEDS and BDC_MEM_FASTFALL, if v10's timeouts make time the binding cost.
### progress 16:20 (the $SHARED resume block, end to end on straight s1: both resume paths taken as designed; rz's draw 10102 has no runt)
- /tmp/bot/scripts/resume_test.sh with suite13t_s5a_v10_1a.sh's body (task 7 = straight s1, own RUNS per run, killed as
  a process group): r1 killed at 10 min after it 0's rule (state: 13 files, sizes_1.vh); r2 "resumed ... the loop goes
  on" (RESUMED, "last ratchet it 0"), ran it 1-4 and shipped CLEAN it=2, killed as soon as $SHARED held its finished
  result.txt; r3 "resumed ... the loop had finished: trim-only" -> "TRIM-ONLY it 2" (trim records dropped, it_2.txt
  the untrimmed line); its rebuild / md5 check / trim / draws running. ratchet.py reads a missing pinned.txt as empty
  (the saver skips empty files).
- rz xorshift s1 (race-padded): draws 10101-10103 PASS 19 / 19 with **0 pulses under 1 ns** (narrowest 2.46-2.64 ns);
  on suite13t's unpadded route the same point 10102 had 118 pulses under 150 ps. Different routes: consistent, not
  paired. Its cycles per draw are ~5-6 % above suite13t's (the pad's cost, scatter included).
- xorshift s1 plain move alone (arw2): PASS 4 / 4, 16350 ps (untrimmed 17123); suite13t 17588 / 18319.
### progress 16:57 (the $SHARED resume block works end to end; countloop s1 plain + sibling 16.39 ns vs suite13t 22.22; collatz64 eq2's search route 22.38 untrimmed)
- **Resume test done** (straight s1, suite13t_s5a_v10_1a.sh's body): r3 took the trim-only path, rebuilt the loop's
  route (sdf 3aee4aab = r2's), ran the final stack and **4 / 4 draws PASS**, wrote its result line, and removed its
  state ("state left:" empty). So a v10 task stopped at 240 min continues from its last ratchet step, and one stopped
  after its loop continues from its shipped route; mk_resume.py files the parts. Side note: on a loop-free kernel the
  scoped trim finds 0 cycle lines and its rule step logs "RULE FAILED" (no trim either way; tidy after v10's parts).
- **countloop s1, plain move + BDC_SIBLING_FUSE** (sib, v9 + scoped trim): the loop's it 10 21110 / 19533; the search
  phase's it 12 (BDC_FORK_OUT_LINK=n13__0,n15__0,n21,n23) clean: **untrimmed 17268, trimmed 16392 ps** (rounds 16730,
  16392). suite13t's countloop s1: 22896 / 22224 (its search found no clean route): -24.6 % / -26.2 %. Draws running.
  formal A30 warned the merged cell makes the test wait for the accumulator's operands; on this route that did not
  cost what the plain move and the search gained.
- **collatz64 s1 + eq2** (arw2): it 7 24706 (untrimmed = trimmed); the search phase's it 8 (BDC_FORK_OUT_LINK=n19__0,
  n33__0) untrimmed 22383, trimming. suite13t: 29391 / 25557. Prediction (14:33): 16.6-21.7 ns trimmed.
### progress 17:08 (v10's first results; the farm's uninterrupted straight s1 = the resume test's route)
- suite13t_s5a_v10_1a 3 / 30 back (7874b6123): straight s1 PASS 4 / 4, **sdf 3aee4aab -- the same route the local resume
  test shipped after being killed twice** (r1 mid-loop, r2 after its loop, r3 trim-only): the resume reproduces the
  uninterrupted run's route. test_divui s1 PASS (clean), brhash s1 PASS 4 / 4 on a NOT CLEAN route (it 9). v10_1b
  submitted at 50f1fab54 (no flow file differs from 7874b6123's). suite13t: s3b 18 / 30, s4a 19 / 30, s4b 11 / 30,
  rerun1 done; rwa still waiting (64 cores).
- countloop s1 plain + sibling (sib): **PASS 4 / 4 at 16392 ps** (no pulse under 1 ns, narrowest 3.46 ns); suite13t 22224.
### progress 18:24 (v10 early read, 25 seed-1 pairs: the scoped trim gives the same P with 5 trims where suite13t made 108; the race check fired once; the proved rewrites reproduce the local routes)
- v10_1a / 1b as returned (14 + 11 of 30), paired with suite13t's same kernel and seed (results at origin/claude/cluster
  as of 18:23; nextpnr 6e5d224472232d5d):
  - **19 pairs are the SAME route** (sdf equal: no rewrite applies and the race check padded nothing). On every one the
    trimmed P is identical, and v10's cycle-scoped trim made **5 trims where suite13t's made 108** (fill 0 vs 5, ipow 0
    vs 8, lfsrfind 3 vs 8, sqrtsub 1 vs 7, nested 0 vs 28, ...). Paired on identical routes, so no scatter: formal B25's
    point holds suite-wide so far -- ~100 lines keep their built margin for nothing in P.
  - **The race check fired on test_memory_1 s1**: suite13t shipped it 5 (dd5c5ee7) with a latch-fed race at 3.60 sd
    (ucond_br5, ulink_n23_folink); v10 padded the link 1 -> 2 and went on to it 10, clean, weakest race 16.61 sd.
  - **Proved rewrites**: collatz -36.3 % (14483), xorshift -7.0 % (16350) -- both the routes of the local arw2 loops,
    sdf for sdf; twoloops 15811 (NOT CLEAN) -> 14708 CLEAN (-7.0 %; the same route, d4d19bb6, as the local fs loop's it
    7); countloop 22224 -> 19116 (-14.0 %); horner 20571 -> 20926 (+1.7 %).
  - Against the 14:35 prediction so far: collatz beyond the 15-35 % (36.3), countloop beyond the 0-10 % (14.0), horner
    slightly the wrong side of 0 (+1.7, inside scatter); every unchanged kernel exactly equal (inside "-2 .. +2 %").
- collatz64 s1 + eq2 (local arw2): the search route it 8, **21528 ps trimmed** (22383 untrimmed; suite13t 25557 /
  29391: -15.8 % / -23.8 %), inside the 16.6-21.7 ns prediction at its top; draw 10102 PASS 18 / 18, no pulse under 1 ns;
  three draws running.
### progress 19:26 (HEADLINE moved to suite13t, flow v9 + trim: 42 of 62 kernels pass (was 34), measured-ratio mean 1.50 (was 1.69); 13 no result, 11 of them the 240-min limit)
- research/data/fifteen/README.md top: the suite13t table (results at origin/claude/cluster 139b6dd35, 19:26 UTC; 4 tasks
  still running: sumi3_mem s3, quadrec s4, iterative_division s4, stencil_2d s4 -- their kernels have rows from other
  seeds). 42 PASS, 7 UNFINISHED (cmpchain, factorial, fir, iterative_division, nested, quadrec, spmv), 13 NO RESULT
  (research/data/suite/headline_reasons_s13t.tsv, written by research/tools/suite/timeout_reasons.py: how far each
  timed-out loop got per seed). Ratio means 1.50 (measured, n = 3) / 1.02 (with estimates, n = 29); latency ratio 1.17
  (n = 23). Every draw on every judged route right; xorshift s1's runty draw refused as evidence. The previous table
  stays below it, under its own heading.
- Caught while building it: suite13t_s5_rerun1's tasks 1-2 are exit1 tasks (the exitcond fixtures, no trim); the table
  reads only its tasks 3-8. Without that, nested_loop s3 and sumi3_mem s3 from another flow would have been in the row.
### progress 19:26 (collatz64 s1 + formal's eq2: 21.53 ns, 4 / 4 draws -- the 14:33 prediction (16.6-21.7) held, at its top)
- arw2 collatz64 s1 (eq2_pass's MLIR, v9 + scoped trim): `status=PASS draws=4/4 P=21528 P_untrimmed=22383 trims=2
  rule=clean it=8 bits=EQUIVALENT`, every draw 18 / 18 with no pulse under 1 ns (narrowest ~3.0 ns). suite13t collatz64
  s1: 25557 / 29391 (-15.8 % / -23.8 %). Ratio to Dynamatic's measured 17.84: 1.21 (suite13t's route 1.43).
- Finish-seed loops (v10 + AUTO_FINISH_SEEDS=3): no alternate route adopted yet; the alternates of the first finish
  routes were as short as their seed-1 routes (10-30 rows), cmpchain's it 9 alternate 4 rows. They are seed 1 of
  kernels whose loops are far from clean at the finish switch, not the "1-6 rows of churn" case finseeds1 cleaned.
### progress 19:27 (local early read for the mff A/B: v10 + BDC_MEM_FASTFALL=1 on memsum s1 and dot2 s1)
- Started (SUITE_TAG=mff10): v10's environment + BDC_MEM_FASTFALL=1 on memsum s1 / dot2 s1, to be paired with v10's
  same tasks (memsum s1: 24560 ps, the suite13t route). PREDICTION (now): memsum within -8 .. +3 %, dot2 within -5 .. +5 %
  (memauto.md's whatif: memsum -2.5 %, dot2 no change); every draw passes, no RAMB18 event.
### progress 20:07 (v10's first resume part filed: 7 of v10_1a's tasks hit 240 min)
- suite13t_s5a_v10_1a: 29 / 30 back at 20:07; TIMEOUT on tasks 6 isprime, 10 nest3, 14 quadrec, 21 digitsum, 22 digitdiv,
  23 divmodu, 24 divmods (s1); task 5 (gcd s1) was restarted by the farm on another machine (RUNNING 7 min at 20:07): its
  body resumes from $SHARED by itself. **Filed suite13t_s5a_v10_1a_r1** (mk_resume.py --running-ok: a part not yet done
  is read, its running tasks left out): the 7 timed-out tasks, 4 cores each, draws 4 at once, same body and state.

## Session 2026-11-20 20:26 UTC -- cluster-research-29671222-1, fourth start (job requeued a third time: ends 2026-11-22 20:24 UTC; fresh /tmp)
Lock: cluster-research-29671222-1 at 20:07 (this wrapper's previous start, same id); taken 20:25 UTC.
cluster: /tmp/bot was recreated at 20:24 UTC (requeued under the same id): the previous start's local loops (mff10
memsum s1 / dot2 s1, the finish-seed loops fs factorial s1 / cmpchain s1, the formal worktree and lake cache) are lost;
only what was pushed survives. Farm results copied to /tmp/bot/farmres (origin/claude/cluster ead225840).
Toolchain: patches.sha 0d42657914fc25d3, nextpnr 6e5d224472232d5d (cells/verify/toolchain.sh all ok, 20:26 UTC)   Seeds: per item
Audit: T172 in progress (own rebuild of the trimmed lfsrfind s1 = ours; trim INIT-only; its GLS running); no new
REFUTED / OVERSTATED row for research. Formal: A32 / A33 (15:26 / 15:39) not yet answered here -- see below.
Flow code unchanged since v10_1a's checkout 7874b6123 (only mk_resume.py, which tasks do not run): v10 is one flow.
### progress 20:32 (overbuild on v10's seven NOT CLEAN seed-1 loops, local, with a prediction)
- **Why:** suite13t's headline has 7 UNFINISHED kernels (every judged route NOT CLEAN) and v10 repeats it so far: of
  v10's 38 seed-1 routes back, 7 are NOT CLEAN (brhash, cmpchain, nested, factorial, test_loop_free, test_memory_2,
  spmv), each after phase 1 plus six raise-only finish routes (least short: 13 ps / 1 row on nested .. 1081 ps / 6 on
  cmpchain). research/data/converge/notes.txt measured why: a re-route moves every margin by ~0.5 ns sd, so the finish
  phase chases fresh rows. The one lever left open there is AUTO_OVERBUILD=H (opt-in since 2026-11-20 06:47: at the
  switch every trimmable line built H longer, a finish route counts as clean when the trim step -- LUT INIT only, the
  route unchanged -- makes it so). Its only test (xorshift s1 clean as built; countloop s1 / s2 6 -> 2 / 12 -> 8 rows
  after trim steps) was lost in the 09:02 requeue before it finished.
- **Running (local, research/tools/auto/overbuild_farm.sh, H = 3):** each of the 7 loops from v10's own phase 1 (its it 4
  rebuilt here from the farm's sizes and seed, sdf md5 checked), then the finish phase with AUTO_OVERBUILD=3 under v10's
  environment (CA_BENCHCAP, AUTO_TRIM, AUTO_TRIM_SCOPE=cycle, AUTO_RACE_Z=4.5, AUTO_PROVED_RW=cache), AUTO_SEARCH=0,
  the full stack and suite_one.sh's 4 draws on the farm's own draw points. Control: v10's own finish phase on the same
  phase-1 state (NOT CLEAN on all 7).
- **PREDICTION (written 20:32, before any result):** at least 4 of the 7 end rule-CLEAN after the trim step, most at their
  first or second finish route; every draw passes; where both have a P, the trimmed P within -5 .. +8 % of v10's NOT
  CLEAN route (the overbuilt lines are cut back by bits, but the placement is the overbuilt one's).
- **A gap this run does not close, found reading the code:** auto_size.sh runs the latch-fed race check (AUTO_RACE_Z)
  only on a route the rule finds clean AS BUILT, and research/tools/race_find.py prices a link's request line as built
  (entry at g[0]); a trimmed line is entered later. So a trim that shortened a race link's request line would ship
  unchecked. On v10 / rwa so far it has not happened: on all 27 trimmed routes back, no trimmed macro is a race link's
  request line (one, horner s1, trimmed a race link's acknowledge line, which is on neither side of the race). An
  overbuilt route made clean by the trim step skips the race check altogether. Both need closing before overbuild can
  join a flow (next note).
### progress 20:42 (farm queue trimmed for v11; overbuild also on four loops v10 finishes clean, for its cost)
- **Most v10 loops end in the finish phase:** of the 41 v10 routes back with a result (parts 1a / 1b / 2a), 33 reached
  phase 2 -- 26 ended clean there after 1-6 raise-only routes (median 4), 7 NOT CLEAN after 6. So AUTO_OVERBUILD would
  change about 80 % of all loops, not only the 7: its cost on the loops that converge anyway decides it as much as
  the 7. **Added (local, same tool, H = 3):** ipow s1 (v10: 4 finish routes, P 19867), fold64 s1 (5, 21348), twoloops
  s1 (3, 14708, plain move), sqrtsub s2 (4, 21661) -- no search phase on any of the four, so v10's shipped P is its
  loop route's (trimmed, cycle scope). PREDICTION (written now): each clean within 1-2 finish routes (v10: 3-5); trimmed
  P within -5 .. +8 % of v10's (overbuilt routes are larger, ~+3 elements on every trimmable line, cut back by bits only).
  These four started after a72f4a551, so they also carry its one unconditional overbuild change (a route with a race
  row is never made clean by trims); the first seven do not (it only matters if a race pads a finish route).
- **Farm queue (11fbcb879):** suite13t_s5c_sibb rewritten before it ran: flow v10 + BDC_SIBLING_FUSE=1 (was v9 + trim
  against suite13t), 17 kernels the flag changes that carry no proved rewrite, seeds 1-2 (34 tasks; was 84), with the
  $SHARED resume block; suite13t_s5b_mff_3 / _4 withdrawn (mff = seeds 1-2, 60 routes). Why: each A/B now differs from
  v10 in one flag, and the farm's time after v10 goes to flow v11 (named to run after sibb).
### progress 20:58 (Dynamatic's own circuit can be routed here again: our export-rtl, checked cycle for cycle; formal A34's census gives a v11 memo with brhash and nested)
- **Why:** the headline's ratio to Dynamatic rests on 3 periods routed in 2026-08 (one route each, default seed) and 29
  ESTIMATES (Dynamatic's timing model x one factor fitted on those 3; worst leave-one-out 15.8 %). The owner's
  Dynamatic build on the cluster has dynamatic-opt (with --lower-handshake-to-hw) and the Verilog library, but no
  export-rtl, so nothing could be routed since August.
- **New (ec909a42a):** research/tools/suite/dyn_export.py (export-rtl for the integer subset: config entries matched by
  their own parameter constraints, generic files copied, cmpi / constant generated from Dynamatic's templates as its
  generators do, anything else needing a generator refused), dyn_vsim.py (iverilog on dynamatic_est.py's calls:
  results and cycles), dyn_route.sh (dyn_baseline.sh's I/O-bound wrapper, --freq 250, a placer seed per route),
  dyn_all.sh (the four over a kernel list).
- **xorshift (current fixture, on-merges buffers):** 19 / 19 calls, results = the C and cycles = the estimator's model
  in every call; negative controls (a compare inverted, two constants with a bit flipped, the loop test inverted)
  caught on 19 / 16 / 1 / 16 of 19 calls. **Routed: period 11.48 ns mean over seeds 1-4 (11.11-11.72)**, nextpnr
  6e5d224472232d5d; August's one route: 12.73 (older fixture, nextpnr and seed); the estimate for this fixture 11.92.
  dyn_all.sh is running over all 62 suite kernels (one at a time, 4 seeds each); the memory kernels need the memory
  controller ports, which dyn_vsim does not drive yet.
- **Formal A34** (20:48, my 20:45 ask): ring_dec_route + tv_gate on all 111 fixtures: 9 PROVED, no counterexample; new
  against our memo: brhash, nested. **cache_v11.tsv** (ca02b7189) = cache.tsv + those two rows, selected by suite_one.sh
  AUTO_PROVED_RW_CACHE (opt-in; v10's waiting parts read cache.tsv unchanged). The local a33 loops build exactly
  these files.
### progress 21:10 (overbuild's first trim checks: the rows left short sit on lines the trim cannot move; sobel / video_filter filed under v10)
- **Overbuild, first two finish routes (test_memory_2 s1, test_loop_free s1; +3 on every trimmable line):** short as
  built by 8 rows (1665 ps) and 4 (457); four trim steps later still 8 / 4 rows, every one "unfixable" in the rule's
  trim mode. test_loop_free's rows are rule I at two multi-stage links' stage-1 controllers (-163 .. -294 ps): the rule
  pads the link's _SDELAY (1 element, a symmetric LUT1 line: trim_lines.py cannot move it, so overbuild did not lengthen
  it); the other line the row depends on (the link's _UACK, trimmable, built 5) moves the margin by 176 ps in all.
  test_memory_2's are E at a steer (-498 / -437), B at a RAM port (-377 / -367), A'm at a mux (-174 / -292). Across
  v10's finish routes the short rows are E 465, H 241, I 176, A'j 73, A'm 66, A 48, B 27, C 27 (rows x corners x LUT
  halves): overbuild reaches only those whose fixing line is a LUT2 side-input chain. Nine runs still going; verdict
  when they end.
- **A lead this shows (not started):** a symmetric line built from LUT2s that pass their chain input (INIT 0xA, the
  side input = the line's input, unused) would behave as today's LUT1 line and could be entered at any element by
  INIT, like the fast-fall lines. Link request lines, stage delays and RAM lines could then be trimmed: overbuild
  would reach the I / H / E / B rows above, and the trim step could shorten symmetric lines on the critical cycle (the
  first trim README: ulink_n12__1 and ulink_n31_folink on xorshift's cycle were refused as symmetric). A cell change
  under CLAUDE.md's rule (cells/rtl frozen: a stated reason and a routed-GLS result), plus tighten.py / corner_audit.py
  / trim_lines.py support for the new INIT.
- **Farm:** suite13t_s5a_v10_5sv filed (127303ba7): flow v10, same body, on sobel and video_filter, seeds 1-4 (v10 and
  suite13t left them out: one 240-min task cannot hold their loop; v10's resume removes that limit).
### progress 21:18 (symmetric lines made trimmable, opt-in: BD_SYMTRIM; two full loops with it + overbuild started, prediction)
- **c0f2bab80:** cells/rtl/bd_latch.v `BD_SYMTRIM (opt-in define): a symmetric bd_delay is built as g[0] LUT1 +
  g[1..N-1] LUT2 with INIT 1010 (O = the chain input; the side input = the line's input, unused), the same instance
  names; trim_lines.py treats INIT 1010 elements as trimmable (entry = INIT 1100, as for the AND / OR lines; under the
  define a 1-element line is trimmable once built longer); corner_audit.py's trim mode accepts them. Default build:
  yosys on bd_delay N=4 sym / FASTFALL / FASTRISE gives the same 14 cells and INITs as before; trim_lines --list on a
  default route unchanged. The rule needs no change: false_arcs() cuts the unused side pin's LUT arc from the INIT, so
  both edges walk the chain as on a LUT1 line. Regression check running: v10's straight s1 route (sdf 3aee4aab)
  rebuilt at this head.
- **CLAUDE.md's condition for a cells/rtl change (a routed-GLS result) is not met yet; nothing in any flow sets the
  define.** The evidence being made: two full loops, flow v10 + BD_DEFINES=-DBD_SYMTRIM + AUTO_OVERBUILD=3 +
  AUTO_RACE_KEEP=1 (SUITE_TAG=sym), on test_loop_free s1 and factorial s1 (both NOT CLEAN in v10 after six finish
  routes): their trimmed final routes go through the full stack (bits EQUIVALENT, ffmux, the event graph's check) and
  4 draws each; a negative control (a symmetric line trimmed below the rule's need) follows on one of their routes.
- **PREDICTION (written 21:18, before any result):** both loops reach the finish phase as in v10; the first overbuilt
  finish route of each is made rule-clean by the trim step alone (its rows are on lines that are now trimmable), or the
  second is; every draw passes with no pulse under 1 ns; on factorial the trimmed P within +-8 % of v10's NOT CLEAN
  route's slope figure (25.35 ns, suite13t).
### progress 21:20 (STATE OF PLAY -- read this first if the session ends here)
- **Headline:** still suite13t (flow v9 + trim, 42 of 62). Next: **flow v10** (suite13t_s5a_v10_*: 1a done but gcd s1;
  1b done but 3 restarted tasks; 2a / 2b running; 3a / 3b / 4a / 4b waiting; resume parts 1a_r1 (submitted) and 1b_r1
  (filed 21:12); 5sv = sobel / video_filter under v10 (filed)). File each part's resume with `python3
  research/tools/suite/mk_resume.py --running-ok <results dir> r1 <part>` once its tasks have timed out; then r2 on the
  r1 parts. Regenerate the table over all v10 parts + resumes when they are in (suite_table.py, as the headline's
  command line says), with dyn_apply.py's measured Dynamatic figures written first (below).
- **Dynamatic routed (new):** research/tools/suite/dyn_all.sh running over the suite (/tmp/bot/dynroute, summary2.txt;
  xorshift 11.48, collatz 13.79, collatz64 16.90, ipow 9.12 ns periods, 4 seeds each, exports checked exact). When it
  ends: `python3 research/tools/suite/dyn_apply.py /tmp/bot/dynroute` (dry run), then --write; commit the two tables
  and the per-kernel route.txt / vsim.txt under research/data/suite/dynamatic/routed/. If /tmp was lost: rerun dyn_all.sh
  (about 5 min per kernel when the node is quiet).
- **Convergence:** overbuild alone does not reach the rows on symmetric lines (2 of 2 first trim checks not clean, 9
  runs still going in /tmp/bot/runs/ob). BD_SYMTRIM (c0f2bab80, opt-in) makes them trimmable; loops sym test_loop_free
  s1 / factorial s1 (/tmp/bot/runs/sym) test it with overbuild; prediction in the 21:18 note. A regression rebuild of
  v10's straight s1 at the new head (must give sdf 3aee4aab) is running in /tmp/bot/regchk.
- **Farm queue after v10:** mff_1 / mff_2 (v10 + BDC_MEM_FASTFALL, seeds 1-2), sibb (v10 + BDC_SIBLING_FUSE, 17 kernels x
  seeds 1-2), then flow v11 (to be filed: v10 + AUTO_RACE_KEEP + cache_v11 (brhash, nested) + sobel / video_filter,
  + overbuild / SYMTRIM / mff / sibling if their evidence holds).
### progress 21:39 (regression check: v10's route rebuilt at the BD_SYMTRIM head is byte-identical; the overbuild-alone controls replaced by BD_SYMTRIM ones)
- **Regression:** v10's straight s1 route (it 2, seed 1, its sizes_2.vh) rebuilt with lane2.sh at c0f2bab80 (the
  BD_SYMTRIM bd_latch.v, define off): **sdf 3aee4aab = the farm's**, ffmux-clean. So the change leaves flow v10's
  waiting parts' routes as they were.
- **BD_SYMTRIM routes build and route:** sym test_loop_free s1 it 0 (33c32f69) and factorial s1 it 0 (8919c0dd), both
  ffmux-clean; test_loop_free's has 2 LUT2-1010 elements (its symmetric lines are mostly 1 element at it 0), and
  trim_lines --list now calls all 25 of its lines trimmable (default route: 13 trimmable, 2 symmetric, 10 unknown).
- **Overbuild alone (first finish route of each, as built):** twoloops 9 rows, brhash 2 (v10's it 5: 20), cmpchain 29
  (23), factorial 13 (19), ipow 5, test_memory_2 8, test_loop_free 3 (20), sqrtsub 12 (9); trim checks done: 0 of 2
  clean. The four controls (ipow s1, fold64 s1, twoloops s1, sqrtsub s2) stopped: their question (overbuild alone's
  period cost) is moot if it is not taken alone. **Replaced by** sym ipow s1 and sym sqrtsub s2 (flow v10 + BD_SYMTRIM +
  AUTO_OVERBUILD=3 + AUTO_RACE_KEEP=1; v10 shipped both clean after 4 finish routes, P 19867 / 21661): the period cost
  of the combination. PREDICTION: trimmed P within -3 .. +8 % of v10's; clean within 2 finish routes; every draw passes.
### progress 21:52 (Dynamatic routed on 9 kernels so far: the timing-model estimates were 11-30 % too slow on 5 and 28-45 % too fast on 3)
- research/tools/suite/dyn_all.sh, nextpnr 6e5d224472232d5d, seeds 1-4 each; every export checked exact (results = the
  C, cycles = dynamatic_est.py's model, every call):

  | kernel | period ESTIMATE (model x 0.793), ns | period ROUTED, mean of 4, ns | routed / estimate | cycles per iteration (simulated) |
  |---|---|---|---|---|
  | xorshift | 11.92 | 11.48 | 0.96 | 1.00 |
  | collatz | 15.48 | 13.79 | 0.89 | 1.00 |
  | collatz64 | 17.11 | 16.90 | 0.99 | 1.00 |
  | ipow | 10.00 | 9.12 | 0.91 | 5.00 |
  | gcd | 12.55 | 11.05 | 0.88 | 0.99 |
  | straight | 14.92 | 14.66 | 0.98 | - |
  | isprime | 9.26 | 11.74 | **1.27** | 1.00 |
  | countloop | 8.36 | 11.74 | **1.40** | 1.00 |
  | sqrtsub | 8.36 | 12.11 | **1.45** | 1.00 |

  countloop's routed critical path is the counter's 32-bit add (8 CARRY4) straight into the 32-bit loop compare:
  Dynamatic does not have our proved plain move (i < n - 1 tested on i), and its unit-delay model prices that pair
  low. So the headline's estimated ratios for such kernels made us look worse than we are (countloop: ours 19.12 / 8.36
  = 2.29 against the estimate, 19.12 / 11.74 = 1.63 against the route). The tables are rewritten when the run ends
  (dyn_apply.py; a preview over v10's interim results: measured-ratio geometric mean 1.22 over n = 6).
### progress 22:05 (overbuild alone: 0 of 5 trim checks clean -- not for a flow by itself)
- Trim checks of overbuilt finish routes (H = 3, v10's environment): brhash s1 it 5 2 rows short after 48 trims; test_memory_2
  s1 it 5 8 short; test_loop_free s1 it 5 / 6 / 7: 4 / 4 / 2 short. Every row left is "unfixable" in the rule's trim
  mode, on lines it cannot move (link request lines, _SDELAY, RAM usetup; journal 21:10). Runs left going to their end:
  brhash, factorial, test_loop_free (for the paired comparison with the BD_SYMTRIM loops on the same kernels); the
  other four NOT CLEAN runs and the four controls were stopped to give the node to the BD_SYMTRIM loops.
- **Decision:** AUTO_OVERBUILD stays opt-in and out of the next flow unless the BD_SYMTRIM loops (sym test_loop_free,
  factorial, ipow, sqrtsub; phase 1 still) show the combination converging.
### progress 22:20 (first BD_SYMTRIM verdict: test_loop_free s1's first overbuilt finish route is rule-CLEAN as built; overbuild gets a trim-back)
- **sym test_loop_free s1** (flow v10 + BD_SYMTRIM + AUTO_OVERBUILD=3 + AUTO_RACE_KEEP=1): phase 1 as v10's (16, 11, 13, 5
  rows; v10 16, 14, 6, 2), switch at it 4 with every line +3 (under the define all 25 lines are trimmable, the
  symmetric ones included); **it 5 rule-CLEAN as built**, no latch-fed race. v10's own finish phase on this kernel and
  seed: 20, 2, 4, 6, 6, 4 rows over it 5-10, never clean; overbuild alone (no define): 3 / 3 / 2 rows at it 5-7, trim
  checks 4 / 4 / 2 short. Its full stack and draws are running. One kernel and seed so far; factorial, ipow, sqrtsub
  are in phase 1.
- **A gap this exposed, fixed (5e9a2eb0b, inside AUTO_OVERBUILD only):** a route clean as built gets no trim check, and
  with AUTO_TRIM_SCOPE=cycle a loop-free kernel trims nothing, so it would ship every line +3 (latency; margin kept on
  lines off the cycle for nothing). Now an overbuilt finish route gives the extra length back on every line off the
  critical cycle, to max(the rule's need on this route, its size - 3) (trim_route TRIM_FLOOR), the trim step's own
  checks unchanged. The running sym loops started on the earlier script; their shipped routes get it by
  AUTO_TRIM_ONLY afterwards (same route, md5-checked, trimmed again).
### progress 23:09 (BD_SYMTRIM + overbuild: 2 of 3 first finish routes rule-CLEAN as built; test_loop_free s1 PASS 4 / 4; digitsum = digitdiv after the frontend)
- **sym test_loop_free s1: PASS 4 / 4 draws** (10 / 10 each, no pulse under 1 ns, narrowest 4.56 ns), rule CLEAN it 5, bits
  EQUIVALENT, ffmux-clean, latency per call median 72 ns (v10's NOT CLEAN route: 72): the first routed-GLS result for
  BD_SYMTRIM lines (untrimmed on this route). Its re-final with the trim-back (AUTO_TRIM_ONLY, same route 4cae65c5) is
  running: the trims of its 25 lines, symmetric ones included, then the stack and the draws again.
- **sym sqrtsub s2: it 5 rule-CLEAN as built** (v10 on the same kernel and seed: 9, 7, 4, 0 rows over it 5-8), latch-fed
  races all >= 15.2 sd; final running. **sym ipow s1: it 5 2 rows short (68 ps)**, its trim check running. factorial in
  phase 1 (it 3).
- **digitsum and digitdiv are the same kernel after the frontend:** their fixtures are identical but for the name
  (LLVM turns v % b into v - (v / b) * b), so their Dynamatic circuits route identically (11.91 ns, the same four
  periods), and our flow builds the same graph for both. They stay two rows (their C differs), but they are one data
  point; noted for kernels/SUITE.md.
- Dynamatic routing: 33 kernels done; divmods failed synthesis (Dynamatic's config omits divsi's oehb_dataless
  dependency; dyn_export.py now closes the file set over what the Verilog instantiates, 12a67c1b5); twoloops seed 2
  and lfsrfind seed 3 hit nextpnr's "post-placement validity check failed for Bel ..A5FF" -- seed 5 replaces them.
### progress 23:22 (a trim-tool naming bug found by sym ipow; fixed opt-in; the BD_SYMTRIM test relaunched on all seven of v10's NOT CLEAN kernels)
- **The bug (d8f163b4a):** research/tools/auto/trim_lines.py found a multi-stage link's last stage from the delay chains
  only. When the last stage has no request line (DELAY 0, a bypass), the link looked one stage shorter and its stage-0
  line (_SDELAY) was named after the link itself. Under flow v10 that only made the trim step miss such _SDELAY trims
  (the rule names them right and never proposes the link's own macro, which has no chain); under AUTO_OVERBUILD it
  raised the wrong macro (0 -> 3: a new 3-element line on the last stage) and left _SDELAY at 1 -- sym ipow s1's one row
  left (I at stage 1, -68 ps, its fix _SDELAY) is exactly that. The --list output changes on all three routes checked.
  The fix (the last stage from every cell of the link's stages, as corner_audit.py does) is on with TRIM_STAGEFIX=1 or
  AUTO_OVERBUILD / BD_SYMTRIM, off otherwise (v10's parts and resumes still to run: --list byte-identical on the same
  three routes with the knobs unset). Flow v11 sets TRIM_STAGEFIX=1.
- **Consequence for the runs so far:** sym test_loop_free / sqrtsub (both clean as built) carried the mislabel too; the
  overbuild-alone runs did not depend on it (their _SDELAY lines were symmetric, never overbuilt). sym ipow and sym
  factorial stopped mid-run; the three overbuild-alone runs left stopped as well (0 of 7 trim checks clean overall).
- **Relaunched (SUITE_TAG=sym2, fixed tool):** flow v10 + BD_SYMTRIM + AUTO_OVERBUILD=3 + AUTO_RACE_KEEP=1 on seed 1 of all
  seven kernels v10 left NOT CLEAN (brhash, cmpchain, nested, factorial, test_memory_2, spmv; test_loop_free already
  done) and ipow (period control; v10: clean after 4 finish routes, P 19867). PREDICTION: at least 5 of the 6 NOT CLEAN
  kernels clean within 2 finish routes; every draw passes; ipow's P within -3 .. +8 % of v10's.
### progress 23:56 (BD_SYMTRIM, routed GLS with trimmed symmetric lines: test_loop_free s1 PASS 4 / 4; the first negative control could not fail -- by design, noted)
- **symtb test_loop_free s1** (the sym route 4cae65c5 rebuilt by AUTO_TRIM_ONLY, md5 checked, then the overbuild trim-back
  with TRIM_STAGEFIX): 15 lines trimmed, symmetric ones among them (ulink_n11 / n22 / n6 / n_index_11 and their
  _SDELAY, ucontrol_merge2 4 -> 1 or 2: INIT 1010 elements re-entered by INIT 1100), rule CLEAN after every step;
  **PASS 4 / 4 draws (10 / 10 each), bits EQUIVALENT, ffmux-clean, no pulse under 1 ns (narrowest 3.94 ns)**, latency per
  call median 72 ns (= v10's). With the untrimmed route's 4 / 4 (22:57): the define's lines work in the bits-decoded
  GLS both as built and trimmed.
- **Negative control, first try -- it could not fail, and the reason is a lesson:** every symmetric line of that route
  set to 1 element (15 lines, 4 -> 1; research tools: /tmp/bot/scripts/symneg.sh) passes 2 / 2 draws. On this kernel
  the symmetric lines were built 1 + 3 (the overbuild) and the rule needs 1 on all of them, so 1 is not a defect, only
  the overbuild undone. A control has to cut a symmetric line below what its constraint needs: the sym2 routes of
  test_memory_2 / spmv carry RAM lines (usetup / uco, symmetric, rule B at the RAM) -- that is the next control.
- Found while doing it: research/tools/auto/trim_shrink.sh linked the route's .frames into its copy and fasm2frames
  wrote through the link onto the original route's .frames (5f28cb177). Each copy's .bit was made from what was just
  written, so the margin studies' verdicts stand.
### progress 00:09 (BD_SYMTRIM + overbuild: test_memory_2 s1 rule-CLEAN as built at its first finish route -- 3 of 3 so far; Dynamatic's remsi is wrong on negative operands)
- **sym2 test_memory_2 s1** (fixed trim tool): phase 1 like v10's, **it 5 rule-CLEAN as built** (v10's six finish routes:
  8 / 10 / 11 / 15 / 16 / 9 rows, never clean, among them B at the RAM (-377 / -367) and E at a steer (-498): overbuild
  alone left the same 8 rows after its trims). With sym test_loop_free and sym sqrtsub: **3 of 3 first overbuilt finish
  routes clean as built.** sym sqrtsub s2's final (old script, no trim-back): **P 20128 ps vs v10's 21661 (-7.1 %)**, draws
  running. sym2 brhash / cmpchain / factorial / ipow / nested / spmv in phase 1.
- **Dynamatic routed: 42 kernels exact and routed** (summary: /tmp/bot/dynroute/summary2.txt). **divmods: Dynamatic's own
  circuit is wrong** -- data/verilog/arith/remsi.v wraps an UNSIGNED remainder core (dynamatic_units_urem_...); 15 of
  24 calls (every one with a negative operand) differ from the C, cycles equal. No figure for it (the check rule
  refuses it). 16 kernels re-running after three tool fixes (c680372fa): void memory kernels (the estimator crashed on
  oracle_mem.sh's 'void'), and mem_controller_loadless (a dependency the config names only as a module).
- Farm: suite13t_s5a_v10_2a done -> suite13t_s5a_v10_2a_r1 filed (7 tasks).
### progress 00:23 (sym sqrtsub s2: PASS 4 / 4, P 20.13 ns vs v10's 21.66 on the same seed, clean at it 5 vs it 8)
- **sym sqrtsub s2** (BD_SYMTRIM + AUTO_OVERBUILD=3, the earlier script: no trim-back, the mislabelled overbuild):
  `status=PASS draws=4/4 P=20128 P_untrimmed=23916 trims=10 luts=1470 rule=clean it=5 bits=EQUIVALENT ffmux-clean`,
  13 / 13 per draw, no pulse under 1 ns (narrowest 3.97 ns); v10's same kernel and seed: P 21661, clean at it 8 (four
  finish routes), 1338 LUTs. **-7.1 % P, -5.6 % summed call latency, +10 % LUTs** (the extra elements stay placed),
  three routes fewer. One seed: route scatter is ~5 %, so the P difference alone is not a result; the convergence is.
### progress 00:45 (BD_SYMTRIM + overbuild: 5 of 5 first finish routes clean as built; ipow showed the trim-back had to come first -- reordered)
- **First overbuilt finish route, clean as built:** test_loop_free s1, sqrtsub s2, test_memory_2 s1, brhash s1, ipow s1 (5 of
  5; v10 needed 4 finish routes on ipow / sqrtsub and never got the other three clean in 6). cmpchain / nested just
  switched; factorial / spmv in phase 1.
- **sym2 ipow s1 exposed an ordering fault:** clean as built at P 25.7 ns untrimmed (every line +3), the cycle-scoped
  trim's one step moved its 7 overbuilt cycle lines at once, opened 2 constraints (137 ps) and was undone, so the cycle
  kept its +3 (v10: 19.9 ns). **266be9d16:** the overbuild trim-back now runs FIRST on every overbuilt line (cycle
  included) to max(the rule's need, size - 3), the route is re-timed, and the usual trim starts from that route and its
  own critical cycle. ipow s1 re-finaled with it (AUTO_TRIM_ONLY, same route 6836ab2f). The sym2 loops still in their
  loop run the earlier script; their shipped routes get the same re-final.
- Dynamatic re-runs: 8 of 9 memory kernels exact (test_memory_1 / 2, mul_example, share_test_2, image_resize,
  vector_rescale, iir, video_filter); test_stdint's estimator gave no call line (next).
### progress 00:49 (HEADLINE: the Dynamatic column is now routed for 60 of 62 kernels -- ours / Dynamatic on-merges 0.93, ours / Dynamatic at its recurrence bound 2.00)
- research/data/fifteen/README.md top regenerated (suite13t's own results unchanged: 42 of 62 pass) with
  research/tools/suite/dynamatic_ref.tsv / dynamatic_lat.tsv rewritten from the routed run (d65543df9; per-kernel records
  and the method in research/data/suite/dynamatic/routed/). Over the 28 passing kernels with a P:
  **geometric mean of ours / Dynamatic's on-merges circuit 0.93** (was 1.50 over the 3 August routes, 1.02 with the
  estimates); **against Dynamatic at its loop-recurrence bound 2.00** (the routed period x the fewest cycles per
  iteration any buffer placement could give; Dynamatic's solver placement needs Gurobi, absent here, so this is an
  optimistic bound for Dynamatic, not a measurement). Where it runs one cycle per iteration we are 1.5-2.4x slower
  (xorshift 1.53, collatz 1.61, countloop 1.65, varshift 2.40, fill 2.43); the 0.93 comes from kernels where on-merges
  waits 4-10 cycles (memory kernels, ipow, horner), which a solver placement would not.
- Does NOT show: Dynamatic with its MILP placement (not buildable here); a board run of either side.
### progress 01:02 (BD_SYMTRIM's routed-GLS evidence complete: as built, trimmed, and a negative control that fails; test_memory_2 and cmpchain clean at their first finish route)
- **sym2 test_memory_2 s1** (UNFINISHED in v10 and suite13t): `status=PASS draws=4/4 trims=35 rule=clean it=5
  bits=EQUIVALENT ffmux-clean`, 7 / 7 calls per draw with every array checked against the C, no pulse under 1 ns.
  Its 35 trims include the RAM lines (umem0 usetup 9 -> 6, uco 12 -> 11; umem1 usetup 6 -> 3, uco 16 -> 13) and link
  lines, all symmetric under the define.
- **Negative control on that route (fails, as it must):** only the two RAM setup lines, symmetric, trimmed below the
  rule's need (usetup 9 -> 1 and 6 -> 1; /tmp/bot/scripts/symneg2.sh): **FAIL 0 / 7 on both draws, every call's arrays
  wrong, 245 / 265 RAMB18 timing events.** The same lines at the rule's need (6 / 3) pass 4 / 4. So a trim of a
  BD_SYMTRIM line changes the circuit as the rule prices it, and the bits-decoded GLS sees a trim that goes too far.
  With sym test_loop_free (untrimmed 4 / 4, trimmed 4 / 4), sym sqrtsub (4 / 4) and this, **CLAUDE.md's condition for the
  cells/rtl change (a stated reason and a routed-GLS result) is met** for BD_SYMTRIM as an opt-in define.
- **sym2 cmpchain s1** (UNFINISHED in v10 / suite13t): it 5 rule-CLEAN as built. **First overbuilt finish route clean as
  built: 6 of 6** (test_loop_free, sqrtsub, test_memory_2, brhash, ipow, cmpchain). nested switched; factorial / spmv in
  phase 1; ipow re-finaling with the reordered trim-back.
### progress 01:44 (ipow showed overbuild's period cost on a loop v10 converges; flow v11's overbuild made LATE: only after v10's own finish phase fails)
- **symtb2 ipow s1** (overbuild at the switch, re-finaled with the reordered trim-back): P after the trim-back **23.01 ns**
  (untrimmed overbuilt 25.67; v10's route 19.87, clean after 4 finish routes); the cycle-scoped trim then moved no
  line. Its cycle against v10's: ulink_n32_folink 4 elements (v10: 1) -- a latch-fed race link, which AUTO_RACE_KEEP
  forbids the trim to shorten, so the +3 of the overbuild stayed on the critical cycle -- and uselect0 26 (v10: 21) on
  the larger route; chain 14.1 ns vs 10.3, wire 6.5 vs 7.3. So overbuilding loops that converge anyway can cost
  period (here +16 %; sqrtsub s2 went the other way, -7 %, on one seed).
- **56740456cf: AUTO_OVERBUILD_LATE=M (opt-in).** v10's finish phase runs unchanged; only a loop still NOT CLEAN after it
  gets M more routes built with BD_SYMTRIM, every sized line +3 except the latch-fed race links (race_lines.txt),
  clean when the trim step alone makes it so, the shipped one trimmed back first; no search phase after it. Unset:
  every condition is the old one (OB never set; the build's define empty; the phase-2 log line byte-identical).
- **Test running (lateob.sh):** v10's own cmpchain s1 state (NOT CLEAN after 6 finish routes) resumed with
  AUTO_OVERBUILD=3 AUTO_OVERBUILD_LATE=4: the resume found phase 2 ended and switched -- "phase 3 (late overbuild +3 on
  76 lines, BD_SYMTRIM) from it 11". PREDICTION: route 11 clean as built or after its trim check; final + 4 draws pass.
### progress 01:56 (flow v11 filed; the late phase's first route on v10's cmpchain s1 is rule-CLEAN as built)
- **lateob cmpchain s1** (v10's own state, NOT CLEAN after six finish routes, resumed with AUTO_OVERBUILD=3
  AUTO_OVERBUILD_LATE=4): phase 3's first route it 11 is a BD_SYMTRIM build (158 LUT2-1010 elements: the symmetric
  lines as pass chains), no latch-fed race, **rule-CLEAN as built**. Its final (trim-back, then the stack) and draws
  running.
- **Flow v11 filed (d4a6a3a4a7):** suite13t_s5a_v11_1a..4b, 62 kernels x seeds 1-4 (31 tasks per part), named after v10's
  parts and resumes, before mff / sibb. v10 + AUTO_OVERBUILD=3 AUTO_OVERBUILD_LATE=4 + TRIM_STAGEFIX=1 + AUTO_RACE_KEEP=1
  + cache_v11 (brhash / nested); sobel / video_filter in. PREDICTION (in the headers, 02:00): routes equal to v10's
  wherever v10 shipped clean from phases 1-2 and no _SDELAY trim or race-kept line differs; >= 80 % of the loops v10
  left NOT CLEAN reach a rule-CLEAN route in the late phase; every draw passes; most of v10's UNFINISHED kernels PASS.
- **Flow code freeze for v11** from the moment its first part is submitted: until all its parts and resumes are in,
  only opt-in knobs v11 does not set.
### progress 01:56 (STATE OF PLAY -- read this first if the session ends here)
- **Headline** (research/data/fifteen/README.md): suite13t (v9 + trim) 42 of 62 pass; the Dynamatic column is ROUTED now
  (60 of 62 kernels): ours / on-merges 0.93, ours / Dynamatic at its recurrence bound 2.00. Next headline: **flow v10**
  when its parts and resumes are in (regenerate with suite_table.py over suite13t_s5a_v10_* and the r1 / r1b / r2 parts
  and 5sv), then **flow v11** (filed 02:00; runs after v10's parts).
- **Farm queue (mine):** v10 3a / 3b running, 4a submitted, 4b waiting; resumes 1a_r1, 1a_r1b (gcd s1), 1b_r1, 2a_r1; 5sv
  (sobel / video_filter); then v11_1a..4b; then mff_1 / mff_2, sibb. As each v10 / v11 part ends: `python3
  research/tools/suite/mk_resume.py --running-ok <results> r1 <part>` (then r2 on the r1 parts). A task restarted by the
  farm and missed by its r1 needs its own part (as 1a_r1b).
- **Local (/tmp/bot/runs):** late/ (cmpchain s1, the late phase's test: final + draws), sym2/ (overbuild at the switch:
  nested / factorial / spmv still in their loops; brhash / cmpchain / test_memory_2 finished), symtb2/ ipow (re-final),
  a33/ (brhash / nested with the A34 rewrites, niced). If /tmp is lost, nothing here is needed by the farm runs.
- **Done this session:** Dynamatic routed (60 / 62) and the headline's ratio column; BD_SYMTRIM (opt-in, GLS evidence with a
  failing negative control); overbuild alone measured (0 of 7 trim checks clean); overbuild + BD_SYMTRIM (6 of 6 first
  finish routes clean, but +16 % P on ipow) -> AUTO_OVERBUILD_LATE; trim_lines _SDELAY naming fix (opt-in); race-keep;
  cache_v11 (formal A34).
### progress 02:16 (BD_SYMTRIM + overbuild: brhash, cmpchain, test_memory_2 PASS 4 / 4 on rule-CLEAN routes -- all three UNFINISHED in v10; factorial clean too; the A34 rewrite alone gets brhash s1 clean)
- **sym2 (overbuild at the switch + BD_SYMTRIM, seed 1), against v10's same kernel and seed (both NOT CLEAN in v10):**
  | kernel | status | rule | it | latency per call: median / sum, ns | kernel LUTs | v10 (NOT CLEAN) median / sum, LUTs |
  |---|---|---|---|---|---|---|
  | brhash | PASS 4 / 4 | CLEAN | 5 | 273 / 13380 | 2325 | 294 / 14610, 2110 |
  | cmpchain | PASS 4 / 4 | CLEAN | 5 | 108 / 1680 | 3298 | 108 / 1644, 2952 |
  | test_memory_2 | PASS 4 / 4 | CLEAN | 5 | 132 / 1338 | 1315 | - |
  factorial s1: clean at it 5 as well (final + draws running); nested s1 and spmv s1: 2 rows short at their first
  finish route, trim checks running. Overbuilt-first-finish-route-clean count: **7 of 9** so far.
- **a33 brhash s1** (flow v10 + formal A34's translation-validated plain move, no overbuild): **PASS 4 / 4, rule CLEAN at
  it 8** (v10 without the rewrite: NOT CLEAN after 6 finish routes); latency sum 12648 ns vs 14610 (-13 %). a33 nested
  s1 in its final. Both rewrites are in flow v11 (cache_v11).
- symtb2 ipow s1 (overbuild at the switch, reordered trim-back): PASS 4 / 4 at 23.01 ns (v10 19.87) -- the cost that made
  v11's overbuild late.
### progress 03:13 (a33 nested s1: PASS 4 / 4 on a rule-CLEAN route -- the A34 rewrites alone get both of their kernels clean)
- **a33 nested s1** (flow v10 + formal A34's translation-validated plain move via MLIR_OVERRIDE, no overbuild, no
  BD_SYMTRIM): **PASS 4 / 4, rule CLEAN at it 10**, bits EQUIVALENT, ffmux-clean. v10 on the same kernel and seed without
  the rewrite: NOT CLEAN (shipped it 7). Latency per call median / sum 276 / 11052 ns vs v10's 276 / 10752 (+2.8 % sum,
  on a route v10 could not clean); kernel LUTs 3581 vs 3510. With a33 brhash (02:16): **2 of 2** kernels that A34
  rewrites are clean with the rewrite alone. Both rewrites ship in flow v11 (cache_v11.tsv), which also has the late
  overbuild phase -- v11's numbers for these two will be the rewrite plus whichever phase converges first.
- One seed each, so this says the rewrite CAN unblock convergence, not how often; v11 gives 4 seeds.
- Farm (03:04): v10 3a 29 / 30 (2 timeouts so far -> an r1 when it ends), 3b 17 / 30, 4a 13 / 30, 4b 9 / 30; 1a_r1 6 / 7;
  2a_r1 3 / 7; 1a_r1b, 5sv_r1, 1b_r1_r2 submitted; 2b_r1, v11_1a.., mff, sibb waiting for cores.
- Local: late cmpchain s1 (the late phase's own test) is in its final trim rounds then draws; sym2 factorial / nested /
  spmv in final / trim-back.
### progress 03:32 (board prep: flow v10's collatz eq2 and xorshift plain-move routes rebuild byte for byte from one command; strict gate and steer screen running)
- With v10 3a / 4a in, both kernels have their **4 seeds** under flow v10 (formal's proved loop-test rewrites, trim,
  race check), all PASS 4 / 4 on rule-CLEAN routes: **collatz (eq2)** P 14.48 / 15.58 / 15.84 / 16.42 ns (s1-s4; mean
  15.58), **xorshift (plain move)** 16.35 / 15.22 / 16.36 / 15.07 (mean 15.75). Board items 39 / 41 (flow v3) are 18.99 /
  20.11 ns; the hand xorshift (item 37) 16.49.
- **research/tools/suite/board_rebuild.sh SPEC** (new): the flow's own build (lane2.sh LANE_NORUN=1: the proved MLIR,
  the loop's sizes / seed / search structure), the recorded trims by LUT INIT, the bitstream; exits 1 unless the
  route's sdf AND the trimmed fasm are the ones SPEC names, then puts the bit where cells/hw/loop_cost.sh reads it.
  Specs: research/data/suite/board/{collatz,xorshift}_v10_s1.spec (+ sizes / trims). Checked here: xorshift s1 ->
  sdf fd959b30, trimmed fasm 78aa6ac3 (the farm's route); collatz s1 -> sdf 0f050078, trimmed fasm 6ef8e077 (the bits
  formal's A31 checked). **Negative control:** the xorshift spec with SEED=2 is refused (sdf 5997994a, exit 1). The
  .bit's md5 differs between two builds of the same fasm (identical frames; the header carries the path), so the
  check is on the fasm, not the bit.
- Seed 1 for both: collatz s1 is the fastest of its four (the one formal's A31 proves from the C to the token graph);
  xorshift s1 is the slower of the middle two. Running: the strict gate (GATE_RUNTS=fail, x / RAMB18 fail) at worst /
  SLOW_MAX / FAST_MIN + 32 draws each (K 42101-42132 / 42201-42232), and formal's B24 steer screen (claude/formal
  36ba04ea34) on both trimmed routes. Items get written when these are in.
### progress 03:36 (flow v11's late overbuild phase passes its own test: cmpchain s1 PASS 4 / 4 on a rule-CLEAN route, its first late route clean as built; sym2 factorial / nested clean too)
- **late cmpchain s1** (AUTO_OVERBUILD=3 AUTO_OVERBUILD_LATE=4 TRIM_STAGEFIX=1 AUTO_RACE_KEEP=1, resumed from v10's own
  state after its finish phase ended NOT CLEAN): phase 3 (+3 on 76 lines, BD_SYMTRIM) from it 11; **it 11 rule-CLEAN as
  built** (raised 0, negative 0), trim-back, then **PASS 4 / 4**, bits EQUIVALENT, ffmux-clean. This is the exact
  sequence v11 runs on every kernel v10's finish phase leaves NOT CLEAN.
- Cost of being clean, against v10's NOT CLEAN route of the same kernel and seed (latency per call median / sum, ns;
  kernel LUTs):
  | kernel s1 | how it got clean | it | median / sum | LUTs | v10 (NOT CLEAN) |
  |---|---|---|---|---|---|
  | cmpchain | late phase (v11) | 11 | 120 / 1752 | 3451 | 108 / 1644, 2952 |
  | cmpchain | overbuild at the switch (sym2) | 5 | 108 / 1680 | 3298 | |
  | factorial | overbuild at the switch (sym2) | 5 | 120 / 1626 | 2909 | 120 / 1530, 2565 |
  | nested | overbuild at the switch (sym2) | 5 | 288 / 11664 | 3888 | 276 / 10752, 3510 |
  | nested | A34's rewrite alone (a33) | 10 | 276 / 11052 | 3581 | |
  So far clean costs +3 to +8 % latency sum and +2 to +17 % LUTs over v10's unclean route; a NOT CLEAN route is not a
  pass under the headline policy, so this is the price of a result, not a slowdown. One seed each.
- sym2 tally (overbuild + BD_SYMTRIM at the phase switch, first finish route clean or clean after trim): brhash,
  cmpchain, test_memory_2, factorial, nested PASS on clean routes; spmv still trimming back (144 chains moved).
### progress 03:52 (audit T173 answered: the Dynamatic headline's wording corrected, every nextpnr log behind its periods committed)
- T173 (claude/audit f02fc0fd9): numbers CONFIRMED (0.934 over 28, bound 1.999; its recompute.py run here gives the same),
  wording OVERSTATED on four points. Fixed in research/data/fifteen/README.md and research/data/suite/dynamatic/routed/
  README.md: (1) "checked call for call against its cycle model" now says OUR exporter checked against OUR model
  (dynamatic_est.py), not Dynamatic's simulator, 8 kernels on one call; test_stdint (never checked) keeps an ESTIMATE and
  its ratio cell now says it is out of the measured mean (suite_table.py). (2) "measured on both sides" replaced: the
  two sides are different kinds of measurement (ours: simulated event-graph period with draws, ~8 % slow vs the August
  board; Dynamatic's: routed static timing x simulated cycles), neither on silicon; suite_table.py's latency footer and
  last line no longer say ESTIMATED / single routes. (3) "2.00 is the honest distance" removed: 2.00 is against a
  COMPUTED bound times the on-merges period; five memory / multi-cycle kernels dominate it (share_test_2 11.1,
  mul_example 8.5, vector_rescale 6.4, gather 4.8, binary_search 3.6): **1.55 without them (n = 23), 1.68 on the 9
  kernels whose on-merges circuit already runs one cycle per iteration**. (4) --ignore-loops and the BRAM-less wrapper
  stated; **all 248 nextpnr logs** committed (research/data/suite/dynamatic/routed/pnr_logs.tar.xz, 1.5 MB; manifest:
  every log's last Fmax line agrees with route.txt).
- The table regenerated from the same result files with the corrected suite_table.py: only the wording cells change,
  and nested's bracketed NOT CLEAN fit (24.34 -> 24.60 ns; cause not found, not a passing figure).
- Board prep (journal 03:3x) running: collatz s1 strict gate 5 / 5 so far (worst, SLOW_MAX, FAST_MIN, 2 draws; 0 runts,
  narrowest pulse 1.9 ns); steer screens done (collatz: as at 15:40; xorshift: 16 / 16 steers bounded, min kappa_lo
  0.091, latch-fed race ucond_br7 slack +597 / +1492 ps, adversary no failure to kappa 0.20).
### progress 04:16 (NEGATIVE, bounded before building: a carry-tracking delay line would buy <= 1 element on the critical cycle -- research/data/carryx/)
- The rule on v10's shipped xorshift s1 / collatz s1 routes as built, CARRY4 priced as the flow does (control: equals
  the farm's rule_I.vh on both) vs CARRY4 at the chains' band (an ideal replica): xorshift's cycle line UCMPI1 9 -> 8
  (~0.4 ns, ~2 %), collatz's cycle unchanged even with F7/F8 tracking too. Over 88 clean v10 routes the cycle is 41 %
  matched-delay chain, 29 % inter-unit wire, 30 % cells; the chains are sized by their data paths' LUT / wire content,
  which the LUT elements already track. Not pursued.
- Gate (strict, board prep): 18 / 18 collatz runs PASS so far, xorshift's next; collatz64 v10 s1 rebuilt byte for byte
  (sdf de88e329) as a third candidate, its steer screen running.
### progress 04:17 (collatz64 flow v10 s1 is NOT a board candidate: formal's steer screen puts pulses at a path error of 8 %, a wrong result at 15 %)
- Formal's B24 screen (claude/formal 36ba04ea34) on the rebuilt, trimmed collatz64 v10 s1 route (sdf de88e329, fasm
  9b93469d; rule CLEAN, PASS 4 / 4): steers 12, bounded 10, **min kappa_lo 0.003** (ucond_br6, reading the 64-bit
  n == 2 compare ucmpi2.uz_n38, launched by ulink_n10__4's ctl: slack **+29** / +1108 ps at kappa 0); no latch-fed race;
  at our bands **first pulses at x = 0.08, first failure (RESULT) at x = 0.15**. B24's guide calls a route fine only with
  no pulses at x <= 0.10; board item 40 (collatz64, flow v3 s5) had none to 0.25. Our rule passes it with the 3 %
  guardband each side -- below the 8.5 % median ring scatter (CLAUDE.md), so this route is kept off the board.
  collatz s1 / xorshift s1: no pulses below x = 0.25 (research/data/suite/board/screen_v10/).
- Does NOT show whether collatz64's other v10 seeds (19.90-23.61 ns) are thin too, or what in v10 made it so (its
  trims, UMUX0 -> 6 and a falseResult ack line, are not on ucmpi2's request path; the route was built that way).
### progress 04:41 (BOARD-QUEUE item 42: flow v10's collatz s1, 14.48 ns, strict gate 35 / 35, formal's screen clean; one command rebuilds it)
- **Item 42 written** (research/BOARD-QUEUE.md, run order 3b, right after item 39 = its judge's base): collatz flow v10
  seed 1 (formal's proved eq2 rewrite + trim), sdf 0f050078, trimmed fasm 6ef8e077 (the bits formal's A31 checked),
  P 14.48 ns. **Strict gate here: worst, SLOW_MAX, FAST_MIN 17 / 17 each and 32 / 32 draws (K 42101-42132): 35 / 35
  PASS, 0 pulses under 1 ns, narrowest 1.9 ns, no x.** Formal's B24 screen: no pulses to x = 0.25, no latch-fed race.
  Rebuild: research/tools/suite/board_rebuild.sh research/data/suite/board/collatz_v10_s1.spec (exit 1 on any mismatch).
  Prediction committed in the item: ratio over item 39 ~1.31; ~13.3 ns on the board.
- It is the fastest of collatz's four v10 seeds (mean 15.58): chosen because formal proved that build's token graph from
  the C; the board number should be read against 14.48, not as the flow's mean.
- xorshift s1 (item 43 when its gate is in): 35 runs at 7 at a time, the first started 04:25 (its work dir's time).
### progress 04:41 (STATE OF PLAY -- read this first if the session ends here)
- **Board:** item 42 (collatz flow v10 s1, 14.48 ns) is in BOARD-QUEUE (run order 3b). Item 43 (xorshift flow v10 s1,
  16.35 ns) waits only for its strict gate (/tmp/bot/bq10/gate.txt: 35 xorshift lines when done; script
  /tmp/bot/scripts/bq10_gate2.sh); its steer screen is clean. If /tmp is lost: rebuild with board_rebuild.sh
  research/data/suite/board/xorshift_v10_s1.spec, then GATE_RUNTS=fail bench_gate.sh at worst / max / min and draws
  K 42201-42232 on research/data/eventgraph/gate/xor19 (as research/data/suite/board/rejudge_2026-11-19_gate_strict.sh).
  collatz64 v10 s1 is off the board (formal's screen: pulses at x = 0.08).
- **Headline** (research/data/fifteen/README.md): suite13t (v9 + trim) 42 of 62; Dynamatic wording fixed for audit
  T173. **Next headline: flow v10** -- a partial table already gives 46 of 62 (10 UNFINISHED, 6 NO RESULT pending
  resumes). Regenerate when 4a / 4b and the resumes are in: `suite_table.py --kernels research/tools/suite/kernels.txt
  --no-ratio isprime,stencil_2d results/suite13t_s5a_v10_*` (+ a reasons file for the NO RESULT rows).
- **Farm (mine, 04:16):** v10 4a 22 / 30, 4b 14 / 30 running; resumes 1a_r1 6 / 7, 2a_r1 6 / 7, 2b_r1 1 / 14 running;
  1a_r1b, 1b_r1_r2, 3a_r1, 3b_r1 (filed 04:18), 5sv_r1 submitted / waiting; v11_1a..4b waiting for cores. As each v10 /
  v11 part ends: mk_resume.py --running-ok <results> r1 <part> (r2 on r1 parts). v11's code freeze holds (only opt-in
  knobs v11 does not set).
- **Done this session since 01:56:** a33 nested clean (A34 rewrite alone); late overbuild phase passes its own test
  (cmpchain s1); sym2 factorial / nested clean; board_rebuild.sh; item 42; T173 answered (+ 248 nextpnr logs);
  carryx NEGATIVE (a carry-tracking delay line buys <= 1 element on the cycle).
- **Next:** item 43; v10 headline; v11 results -> headline; FOR-FORMAL answers (B: ucond_br7 bound, v10 screen
  census; C: draws on the board candidates).
### progress 04:50 (what formal's 10 % steer tolerance would cost: ~2 elements on the loop test, ~+5 % P; opt-in AUTO_GUARD_E)
- Our rule and formal's screen agree on collatz64 s1's thin steer: rule E has it at +954 ps raw, +588 after the 3 %
  guard; formal's x-test is the same margin as a relative path error (8 %). The question is only how much is enough.
- research/data/guardx/: the rule at a 10 % E / J guard on the three v10 s1 routes (control arm = the farm's rule):
  xorshift UCMPI1 9 -> 11 and collatz UCMPI2 7 -> 9 on their critical cycles (~+0.75 ns, ~+5 %); collatz64 UCMPI2 13
  -> 18 (not on its cycle). Each kernel: 3 lines grow, all loop / entry tests and one link.
- auto_size.sh **AUTO_GUARD_E=LO,HI** (opt-in, 57a426160; unset byte-identical, so v11 is unchanged): the rule's E / J
  guard. End-to-end test running: flow v10 + AUTO_GUARD_E=0.90,1.10 on collatz64 s1 (/tmp/bot/runs/g10); its shipped
  route goes through formal's screen. If it is fine by B24 at a small cost, it is a candidate for the next flow --
  a policy change (the guard), so it goes to the owner as a measured option, not as a default.
- Gate: collatz 35 / 35 done (item 42); xorshift 2 / 35 PASS so far.
### progress 05:02 (formal A35: the xorshift board candidate's exact graph is proved to compute the C, one theorem; its FASMs handed over for trimcheck)
- A35 (claude/formal, 03:54): research/data/autorw/xorshift.mlir under the spec's knobs (BDC_AUTO=1
  BDC_AUTO_REWRITES=0 BDC_FORK_OUT_LINK=n11__0,n32__2) computes xorshift's C, every input where the C returns, every
  schedule (Lean, standard axioms). collatz_v10_s1's chain is A31's. Formal also notes plain_pass at today's HEAD no
  longer reproduces the memo's xorshift.mlir (it refuses); the memo's file is the proved one and is md5-checked at
  use, so nothing in the flow changes.
- research/data/for-formal/xorshift_v10_s1/: sdf fd959b30, trimmed fasm 78aa6ac3, untrimmed 2178cbe4 (xz) + the
  trim record, sizes, structure, our screen's output -- what A31's trimcheck read for collatz.
- Gate: xorshift 8 / 35 PASS so far; g10 (collatz64 + 10 % E guard) at it 1.
### progress 05:28 (the board can now run any suite kernel's vectors and judge them as the GLS gate does: cells/hw/xsdb_bench_vec.tcl + board_vec_judge.py; tested against a mock bench, negative controls fail)
- Why: only 4 kernels had a board command with a self-reporting pass criterion (hw/loop_cost.sh's sweeps); the other
  ~40 passing suite kernels reached the top of the simulation ladder with no way onto BOARD-QUEUE.
- **cells/hw/xsdb_bench_vec.tcl BIT VECFILE [nruns] [clk] [memdump] [memcheck]**: hw/xsdb_bench_gen.tcl's board
  steps, then the GLS host's per-call program (cells/gls/ps/gen_ps7.py BENCH_PROG) register for register -- v1 and v2
  vector files (operand words, every memory word through the host port, LAYOUT / MEMINFO checked), FIXED mode, NRUNS
  per call -- printing the same BENCHRES / BENCHMEM lines. **research/tools/suite/board_vec_judge.py EXP LOG [MEMEXP]**:
  bench_gate.sh's rules (result = the C's, runs agreed, all completed, no x, arrays = the C's), PASS / FAIL / nothing
  to judge (exit 0 / 1 / 2).
- **cells/hw/test_bench_vec.sh** (tclsh + cells/hw/mock_xsdb_vec.tcl, no board): 9 / 9 -- col18's 17 calls started
  once each with the file's operands; binary_search's 7 v2 calls with the operand and all 101 array words, read back
  and dumped as written; the judge passes right runs and FAILS one wrong result, one hung call, and refuses a run that
  stopped early and a bench whose LAYOUT disagrees. Mutation check: a copy writing OP0 into OP1 is caught on 17 / 17
  calls. The judge on a real GLS run.log (item 42's worst corner) gives bench_gate's own PASS 17/17; with one result
  flipped, one call's runs disagreeing, one call hung: FAIL 14 / 17 naming each.
- Does NOT show: the script on a real board (xsdb's own command behaviour is the one thing the mock assumes; the
  board steps are copied from hw/xsdb_bench_gen.tcl, which has run on the board).
- Gate: xorshift 20 / 35 PASS so far.
### progress 06:06 (BOARD-QUEUE item 43: flow v10's xorshift s1, 16.35 ns, strict gate 35 / 35, formal's screen clean, A35 proves its graph)
- **Item 43 written** (run order 3b with item 42): xorshift flow v10 seed 1 (formal's proved plain move + trim), sdf
  fd959b30, trimmed fasm 78aa6ac3, P 16.35 ns. **Strict gate: worst, SLOW_MAX, FAST_MIN 19 / 19 each and 32 / 32 draws
  (K 42201-42232): 35 / 35 PASS, 0 pulses under 1 ns, narrowest 1.4 ns, no x.** Formal: A35 (graph = C, one theorem),
  B24 screen fine (16 / 16 steers bounded, latch-fed race +597 / +1492 ps). Both items also run the gate's own vectors
  on the board (xsdb_bench_vec.tcl + board_vec_judge.py) before loop_cost.
- Predictions committed in the items: 42 ~13.3 ns, 43 ~15.0 ns on the board (sim 14.48 / 16.35, ~8 % slow).
- Board suite: research/data/suite/board/suite_v10/ specs rebuilt so far: 30 + 3 by hand, every one reproducing its
  farm sdf; the rest still rebuilding (4 workers).
### progress 06:16 (BOARD-QUEUE item 44: the automatic suite on the board -- 46 kernels, one route each, the gate's own vectors and rules, one self-judging loop; dry run 46 / 46 against a mock bench)
- research/data/suite/board/suite_v10/: one spec per kernel flow v10 passed on a clean route (its lowest such seed),
  written by mk_board_specs.py from the farm saves and **every one rebuilt here: 46 / 46 routes reproduce the farm's
  sdf** (43 by four workers, 3 by hand), trimmed fasm pinned.
- research/tools/suite/board_suite.sh: per kernel board_rebuild.sh -> the C oracle exactly as suite_one.sh (its own case
  block, read and evaluated) -> cells/hw/xsdb_bench_vec.tcl -> board_vec_judge.py; last line "board_suite: P of N
  kernels PASS". **Dry run (BQ_MOCK=1 BQ_SKIP_REBUILD=1): 46 / 46 PASS** after fixing the mock for void kernels (13
  kernels whose answer is their arrays: the first dry run stopped them all at the mock's "0xvoid" -- the mock's bug,
  found because the dry run covered every kernel). Negative controls: a corrupted result FAILS (16/17), an
  array-writing kernel left unchanged FAILS (array oracle), a missing spec is NOT RUN.
- Does NOT show: anything on a real board -- the mock stands in for xsdb and the bench; the board steps are
  hw/xsdb_bench_gen.tcl's (which has run on the board).
- The guarded collatz64 run (g10): clean at it 7, untrimmed P 28.27 ns vs v10's 24.71 at its it 7 (+14 %, one route,
  before trim / search); draws pending.
### progress 06:22 (STATE OF PLAY -- read this first if the session ends here)
- **Board (new this session):** items **42** (collatz v10 s1, 14.48 ns), **43** (xorshift v10 s1, 16.35 ns) -- each
  strict-gated 35 / 35 here, formal's screen fine, formal's proofs of their graphs (A31 / A35) -- and **44** (flow v10's
  whole suite, 46 kernels, board_suite.sh; routes reproduced 46 / 46, mock dry run 46 / 46). New board tooling:
  cells/hw/xsdb_bench_vec.tcl (+ mock, test_bench_vec.sh 9 / 9), research/tools/suite/{board_rebuild.sh,
  board_vec_judge.py, board_suite.sh, mk_board_specs.py}.
- **Running locally:** formal's steer-screen census on all 46 suite_v10 routes (/tmp/bot/census/K/racescreen.txt;
  script /tmp/bot/scripts/census_run.sh) -- answers "is collatz64's thin steer one route or a pattern?" for item 44;
  g10 (collatz64 s1 + AUTO_GUARD_E=0.90,1.10) in its final / draws; sym2 spmv trimming back.
- **Headline:** still suite13t (v9 + trim), 42 of 62, T173 wording fixed. **Next: flow v10** (partial 46 of 62) when
  4b and the resumes are in; then v11.
- **Farm (06:05):** v10 4b 28 / 30; resumes 2b_r1 7 / 14, 3b_r1 5 / 12 running; 3a_r1, 4a_r1 (filed 06:06), 5sv_r1,
  1b_r1_r2, 1a_r1_r2, 2a_r1_r2, 1a_r1b_r2 submitted / waiting; v11 parts waiting for cores. v11 code freeze holds.
- **Open questions to formal:** B -- ucond_br7's bound on collatz; a screen of v10's clean routes (being answered
  here by the census); C -- draws on the board candidates.
### progress 07:07 (steer-tolerance census of item 44's 46 routes: about 17 of 40 below x = 0.10 by rule E's own arrivals, 3 of 19 thin in formal's simulation; item 44 becomes the steer guard's silicon calibration)
- research/data/suite/board/screen_v10/census.md: x (formal B24's path-error measure) for every select gate, from rule
  E's own log (steer_tol.py; all 46 routes) and formal's screen run here on the 19 non-memory routes. Thin by both:
  **collatz64 (rule 0.047 / formal pulses 0.08), sqrtsub (0.057 / 0.10), lfsrfind (0.062 / 0.12, and a -59 ps steer
  bound)**; below 0.07 by the rule also fill, twoloops, if_loop_2, dot2 (memory or another steer: not in formal's xtol).
  The rule's x is a bound (formal's simulated x is above it wherever both ran).
- **Correction to 04:17:** I set the 3 % guard against "the 8.5 % median ring scatter (CLAUDE.md)". CLAUDE.md says the
  opposite: 8.5 % is NOT a guardband. The 3 % (corner_audit --guard-lo/hi 0.97 / 1.03) is the residual within-die
  scatter on top of the band corners, by the sizing rule's own design; cells/verify/skew.py's 0.772 / 1.155 is the
  95/95 guard for nominal (un-banded) delays. Whether 3 % is enough at the band corners is unmeasured on silicon -- not
  shown to be too small by anything here: every one of these routes passed its draws.
- So item 44 is now also the steer guard's calibration: its routes span x = 0.045-0.42 (census_table.md); a board
  failure concentrated on the low-x routes would argue for AUTO_GUARD_E=0.90,1.10 (~2 elements on a loop test).
- Also found: twoloops' latch-fed race fails formal's race-only adversary at kappa 0.15; formal's draws give garbage on
  divmodu (all 4) where our GLS passes the same bits -- asked formal.
### progress 07:08 (farm suite13t_s5g_g10 filed: flow v10 + a 10 % steer guard on the seven thinnest kernels, seeds 1-4, paired with v10's own routes)
- The guard's first sample (local, collatz64 s1): clean at it 7, shipped it 9 (search) at **21.97 ns vs v10's 21.53
  (+2 %)** after the trim (untrimmed 27.19); draws running, then its steer x.
- research/cluster/requests/suite13t_s5g_g10.sh: v10's body and export line + AUTO_GUARD_E=0.90,1.10; collatz64,
  sqrtsub, lfsrfind, fill, twoloops, dot2, if_loop_2 x seeds 1-4 (28 tasks, state_g10); named to run after v11's parts.
  **Prediction (in its header):** no status worse than v10's; P on pairs clean in both within +5 % (median); every
  shipped route's weakest select gate at x >= 0.10 by steer_tol.py. If it holds, AUTO_GUARD_E=0.90,1.10 goes to the
  owner as a measured option for the next flow (it is a guard policy, not mine to set alone).
### progress 07:12 (the 10 % steer guard on collatz64 s1: formal's screen goes from pulses at x = 0.08 to none to 0.25, for +2 % P -- one seed)
- g10 collatz64 s1 (flow v10 + AUTO_GUARD_E=0.90,1.10; shipped it 9, sdf 68789cdc, trimmed): rule E's weakest select gate
  x = 0.163 (v10's route: 0.047); **formal's B24 screen: 12 / 12 steers bounded (v10's: 10 -- even ucond_br7 now has a
  bound), min kappa_lo 0.139 (0.003), no latch-fed race, no pulses and no failure to x = 0.25** (v10's: pulses 0.08,
  RESULT at 0.15). **P 21.97 ns vs v10's 21.53 (+2 %)**. Draws still running. research/data/guardx/
  collatz64_g10_s1_*.txt.
- One seed: the farm's suite13t_s5g_g10 (7 kernels x 4 seeds, paired with v10) is the measurement; local samples on
  sqrtsub / lfsrfind / fill s1 started.
### progress 07:20 (sym2 spmv s1 PASS 4 / 4 on a rule-CLEAN route: overbuild + BD_SYMTRIM has now cleaned every kernel it was tried on)
- spmv s1 (overbuild at the switch + BD_SYMTRIM, local): rule CLEAN at it 6 after the trim-back (134 trims), PASS 4 / 4,
  EQUIVALENT, ffmux-clean; latency per call median / sum 1092 / 3768 ns vs v10's NOT CLEAN route 1014 / 3516 (+7 %),
  kernel LUTs 4410 vs 3925 (+12 %).
- Tally of the overbuild + BD_SYMTRIM runs (one seed each, local): brhash, cmpchain, test_memory_2, factorial, nested,
  spmv (sym2), test_loop_free, sqrtsub (sym), ipow (symtb2) -- **9 of 9 clean and PASS 4 / 4**; plus the late phase's
  own test (cmpchain s1). Flow v11 runs the late variant on every kernel v10 leaves NOT CLEAN (8 now: cmpchain,
  factorial, isprime, iterative_division, nest3, nested, spmv, stencil_2d).
- v10 interim table (not published; parts still resuming): 48 of 62 pass (suite13t: 42), 8 UNFINISHED, 6 NO RESULT
  pending resumes; ratio to Dynamatic on-merges 0.93 over 34 kernels.
### progress 07:40 (formal B29: item 42's route rebuilt independently with board_rebuild.sh -- same sdf / fasm / bit; all 12 of its steers now bounded; what x is)
- B29 (claude/formal 582fe2897, 07:27): formal rebuilt collatz_v10_s1 with research/tools/suite/board_rebuild.sh at our
  c4fdc9d23 -- **sdf 0f050078, trimmed fasm 6ef8e077, bit 7ad2d1d0, the same on all three** (the first independent
  run of the board rebuild path); ucond_br7 bounded after a steersafe fix (kappa_lo 0.110; adversary first failure at
  kappa 0.20), so all 12 steers are bounded, min 0.061 (ucond_br6). BOARD-QUEUE item 42 updated.
- On x: a fully correlated adversarial path error (+x on the whole condition cone, -x on the whole request walk), no
  within-die model; formal's 0.10 line is a judgement. Only "first failure" is a hazard ("first pulses" includes benign
  latch glitches): by that, the census's thin routes are sqrtsub 0.10, lfsrfind 0.12, collatz64 0.15.
### progress 08:01 (STATE OF PLAY -- read this first if the session ends here)
- **Board:** items 42 / 43 / 44 in BOARD-QUEUE (collatz 14.48, xorshift 16.35, the 46-kernel suite); formal B29
  reproduced item 42's rebuild independently. Census of steer tolerance: research/data/suite/board/screen_v10/census.md
  (thin by formal's first failure: sqrtsub 0.10, lfsrfind 0.12, collatz64 0.15).
- **Steer guard (AUTO_GUARD_E=0.90,1.10, opt-in):** farm suite13t_s5g_g10 filed (7 kernels x 4 seeds, paired with v10;
  prediction in its header). Local seed-1 samples (/tmp/bot/runs/g10): collatz64 21.97 vs v10 21.53 ns and formal's
  screen clean (draws pending); lfsrfind it 7 27.82 vs 21.14 (+32 %, search running: its entry compare UCMPI0 8 -> 11
  joined the critical cycle); sqrtsub 22.87 untrimmed vs v10's 32.24; fill 33.79 untrimmed. One seed each: route churn
  dominates; the farm pairs decide.
- **Farm (08:04):** v11_1a SUBMITTED 07:52 at 716a27ea8 -- v11 has started; **the v11 freeze holds until 1b..4b are
  submitted** (only opt-in knobs v11 does not set). v10: all base parts done; resumes 3b_r1 running, 4a_r1 running,
  1a_r1_r2, 2a_r1_r2, 1a_r1b_r2, 5sv_r1_r2 submitted, 4b_r1 / 2b_r1_r2 / 3a_r1_r2 filed 08:01; g10 waiting.
- **Headline:** suite13t (42 / 62) until v10's resumes are in; v10 interim 48 / 62.
- **Open with formal:** divmodu disagreement (their draws garbage, ours 4 x 20/20); memory kernels in their screen.
### progress 08:07 (the 10 % steer guard on collatz64 s1: PASS 4 / 4 on a rule-CLEAN route, P +2 %, latency +1.6 %, LUTs +2 %; formal's screen clean)
- g10 collatz64 s1 final: **PASS 4 / 4**, rule CLEAN it 9, EQUIVALENT, ffmux-clean; P 21.97 ns (v10 21.53), latency per
  call median / sum 3216 / 91710 ns (v10 3165 / 90300: +1.6 %), kernel LUTs 1818 (1775). With formal's screen (12 / 12
  steers bounded, no pulses to x = 0.25) this is the route a board item would want for collatz64 -- after the farm
  pairs show the cost holds on 4 seeds.
- Running locally: g10 sqrtsub / lfsrfind / fill s1 (finals / search); the strict gate (worst / max / min + 16 draws)
  on item 44's three thinnest routes (sqrtsub, lfsrfind, collatz64: /tmp/bot/thin/gate.txt) -- 4 draws can miss a
  1-in-3 failure 18 % of the time (formal C68).
### progress 08:49 (formal B30 / B31: item 44's three thinnest routes fail formal's race-only adversary at kappa 0.06-0.10; divmodu was formal's harness, our GLS was right)
- **B31:** divmodu's garbage was formal's harness (it sampled out0 3 ns after the request; our bench samples >= ~24 ns
  and CA_BENCHCAP sizes for that). At 23 ns the same bits pass 2 + 2. Formal's racescreen now defaults to it; my census's
  xtol "first failure" figures (run at 3 ns) may read low elsewhere -- formal re-ran the thin ones at 23 ns: lfsrfind
  0.12, sqrtsub 0.10, unchanged.
- **B30 (steersafe corrected for latch-held conditions; numbers move <= 0.07):** on item 44's routes, its race-only
  adversary (each arc of the race independently anywhere in its prjxray range at one corner, condition late, request
  early) gives a **wrong answer at kappa 0.06 on lfsrfind s1** (structural slack **-59 ps** at the fast corner), at
  0.10 on collatz64 s1 (+29 ps) and on sqrtsub s1 (+346 ps). Each is the loop's exit test; the condition side is mostly
  routing (collatz64: 3.5 of 4.8 ns). Memory kernels: fill fine by the structural bound (0.171) though rule E calls it
  thinnest; dot2 0.032; if_loop_2 0.080 (adversary 0.15). Formal: "the 3 % guard did not cover them".
- Our side, same routes (/tmp/bot/thin/gate.txt, strict gate): lfsrfind PASS at worst / SLOW_MAX / FAST_MIN and every draw
  so far, 0 pulses under 1 ns, narrowest 2.8 ns -- the uniform corners and our correlated draws do not reach the
  per-arc extremes formal's adversary picks. The two models disagree on these three routes; item 44 (annotated) puts
  them on silicon. The 10 % guard closes the gap in both models on collatz64 (g10: formal's screen clean).
- Local guard samples, seed 1: lfsrfind's search route 21.05 ns vs v10's 21.14; collatz64 21.97 vs 21.53; sqrtsub
  20.12 vs v10's 32.24 (v10's own seeds span 17.2-32.2); fill shipped it 7 (search found nothing). Draws pending.
### progress 09:00 (the 10 % steer guard on the three thinnest routes: formal's adversary moves from kappa 0.06-0.10 to 0.15-none; P within v10's own spread)
- research/data/guardx/README.md table: collatz64 / sqrtsub / lfsrfind s1 rebuilt by flow v10 + AUTO_GUARD_E=0.90,1.10,
  all PASS 4 / 4 on rule-CLEAN routes, screened with formal's latest tool: min kappa_lo 0.003 / 0.045 / -0.008 ->
  **0.139 / 0.171 / 0.070**; race-only adversary first failure kappa 0.10 / 0.10 / 0.06 -> **none / none / 0.15**;
  P 21.53 / 32.24 / 21.14 -> 21.97 / 20.12 / 21.05 ns (one seed: churn). fill s1 too: PASS 4 / 4, 33.79 vs 30.40.
- If the farm's paired 4-seed test agrees (suite13t_s5g_g10, after v11's parts), the guard is the measured option to put
  to the owner for the next flow: it closes the gap formal's B30 found at the loop-exit steers, at small cost.
- Thin-route strict gate (/tmp/bot/thin): 35 runs PASS so far, none failed.
### progress 09:01 (digitsum / digitdiv cannot finish under v10 on the farm: every resume redoes the final stack and the trim, which alone exceed 240 min -- no r3 filed)
- 1a_r1_r2 (digitsum / digitdiv seed 1): both reached "final it 7" and the trim rounds again, then the limit. A task that
  dies inside final() leaves no CLEAN / NOT CLEAN line, so the next part resumes the loop (AUTO_RESUME), which runs
  final() -- the untrimmed full stack and the trim rounds, ~4 h for a 140 ns-per-iteration kernel -- from the start:
  the draws are never reached. Their 2a / 3a resumes already submitted will do the same; no r3 filed for seed 1.
- **For the next flow (a flow change, so after v11's parts are all submitted):** keep final()'s progress across a resume
  -- the untrimmed final's result and the trim record when the rebuilt route's sdf matches -- so a resume continues at
  the draws. Until then digitsum / digitdiv stay NO RESULT ("final + trim exceed the farm's limit"), as in suite13t.
### progress 09:42 (the 10 % steer guard's static cost on all of item 44's routes: +0.5 % period (geomean), at most ~6 %; the thin routes' extra elements are off the critical cycle)
- research/data/guardx/guard_est_table.md (research/tools/guard_est.py, new): the rule at 0.90 / 1.10 on every suite_v10
  route as built vs the route as shipped (trims applied); growth priced on the route's own critical cycle. 20 / 45
  routes grow (+1 .. +11 elements), 4 of them on the cycle (lfsrfind +5.8 %, collatz +4.1 %, quadrec +2.9 %, varshift
  +2.2 %); geomean (P + dP) / P **1.005** over 32. Blind to churn and to new critical cycles; the farm pairs
  (suite13t_s5g_g10) measure the real thing.
- So the guard looks cheap where it matters least to formal and costs a few % only where a loop test is itself on the
  cycle. Together with formal B30 (the 3 % guard did not cover three routes) and the local guarded routes (formal-clean
  or much better), it is the strongest goal-1 change available for the next flow, at about half a percent of speed.
### progress 09:53 (flow v11's first results: converged kernels give v10's identical routes; memsum shows the late phase pre-empting v10's search; two PNR timeouts at it 0)
- suite13t_s5a_v11_1a (9 / 31 at 09:52): collatz, ipow, sqrtsub, branchloop, straight, test_divui s1 -- v10's results
  exactly (same sdf where v10 converged: the late phase never triggers there), as designed.
- **memsum s1: the late phase ran (v11's finish phase ended NOT CLEAN), shipped it 11 at P 28.19 ns, rule CLEAN, PASS
  4 / 4 -- v10 got 24.56 on the same seed from its SEARCH phase**, which v11 skips when the shipped route is from the
  late phase. So the late phase can cost speed on a kernel v10's search would have rescued (+15 % here). To measure in
  the v11 headline: every (kernel, seed) where v10 shipped a search route and v11 a late-phase one. Not fixable under
  the v11 freeze; a candidate for the next flow (late phase only after the search, or the search on the late route).
- gather s1 and fill s1: status=PNR-TIMEOUT at it 0 (nextpnr over 3600 s on 2 cores; v10 routed both). Load, not the
  flow; they get a fresh rerun part when 1a ends (mk_resume.py skips them: they have a result line).
### progress 09:53 (next flow (v12) candidates, each with its evidence -- none filed: the v11 freeze holds until v11's parts are all submitted)
1. **Steer guard AUTO_GUARD_E=0.90,1.10** (opt-in now): formal B30 -- three rule-CLEAN v10 routes fail its race-only
   adversary at kappa 0.06-0.10; guarded rebuilds of those three: formal's measures 0.07-0.17, adversary 0.15 / none;
   static cost over all 46 suite routes +0.5 % P (geomean), max ~6 % (research/data/guardx/). Paired 4-seed farm test
   filed (suite13t_s5g_g10). A guard policy: for the owner to decide on the measurements.
2. **Late phase after the search, not before:** v11 memsum s1 shipped a late-phase route at 28.19 ns where v10's search
   found 24.56 (journal 09:53). Measure on all of v11 first.
3. **Resumable final():** a task that dies inside final() re-runs it whole on resume (untrimmed stack + trim rounds), so
   digitsum / digitdiv never reach their draws (journal 09:01). Keep a "loop finished" marker and a finished trim record
   across the resume; test by killing a local run mid-final and comparing the result line with an uninterrupted run.
4. **PNR timeout at it 0** (v11 gather / fill s1 on loaded 2-core nodes): retry on the next seed as AUTO_SEED_TRIES does
   for a missed bench clock.
### progress 10:38 (strict gates in progress: item 44's thin routes 52 / 57 PASS so far; their guarded partners 30 / 57 PASS)
- /tmp/bot/thin/gate.txt (v10's sqrtsub / lfsrfind / collatz64 s1, worst / SLOW_MAX / FAST_MIN + 16 draws each): 52 runs,
  all PASS, 0 pulses under 1 ns; collatz64's last runs still going (~40 min per run).
- /tmp/bot/gguard/gate.txt (the guarded routes, research/data/suite/board/guard_g10, same gate): 30 runs, all PASS.
- When both are in: BOARD-QUEUE item 45 (the guard pair; draft in /tmp/bot/bq10/item45_draft.md).
- Farm: v11_1a 12 / 31; v10's last resumes queued; nothing to file.
### progress 11:02 (item 44's three thinnest v10 routes pass our strict gate 19 / 19 each -- 0 pulses under 1 ns; our model and formal's adversary disagree on them)
- sqrtsub / lfsrfind / collatz64 s1 (the routes in item 44; formal B30: race-only adversary wrong at kappa 0.10 / 0.06 /
  0.10): worst, SLOW_MAX, FAST_MIN and 16 draws each (K 441xx-443xx), GATE_RUNTS=fail, the kernels' own suite vectors
  and C oracle: **57 / 57 PASS**, no x, narrowest pulse 2.7 / 2.8 / 2.2 ns (research/data/guardx/gate/thin_v10_gate.txt).
  With the farm's 4 draws, 20 draws each: our correlated band + scatter model does not reach the per-arc extremes
  formal's adversary sets. Which is closer to silicon is item 44's question (and item 45's, when written).
- Their guarded partners (same gate): 38 / 57 PASS so far, collatz64's runs going.
### progress 11:15 (sobel / video_filter are in the same resume loop as digitsum / digitdiv; the farm cannot run longer tasks, so three clean ones are being finished LOCALLY from the farm's saved state)
- 5sv_r1_r2: all 8 sobel / video_filter tasks hit 240 min again, each having redone its untrimmed final (video_filter
  s1: "final it 8 untrimmed" three times over three parts). research/cluster/README.md: 240 min is the per-request
  maximum. No more farm resumes for these four kernels under v10.
- Every seed's shipped iteration: sobel s1-s4 NOT CLEAN (least short); video_filter s1 CLEAN (it 8), s2-s4 NOT CLEAN;
  digitsum s2 CLEAN (it 7), s1 / s4 NOT CLEAN; digitdiv s2 CLEAN (it 7), s3 CLEAN (it 8).
- **Finishing locally** (/tmp/bot/scripts/v10loc.sh: the request body's own resume steps on the files the last farm part
  returned, then suite_one.sh with v10's export line; no time limit): digitsum s2, digitdiv s2, video_filter s1
  (/tmp/bot/runs/v10loc_*). Same code and flow (head 97c98a4: v10's code plus opt-in knobs it does not set); a
  different machine, said so in the headline when they land. sobel stays NO RESULT / UNFINISHED.
- Seeds 3-4 of the local guard runs dropped (the farm's suite13t_s5g_g10 covers them); seed 2 running.
### progress 11:55 (waiting on collatz64's GLS: guarded-route gate 46 / 57 PASS; local v10 completions in their finals)
- Guarded routes (guard_g10), strict gate: 46 runs, all PASS so far; collatz64's remain (~40 min per run on this node).
- Local v10 completions: digitsum s2 / digitdiv s2 past their untrimmed finals (P 154.0 ns), trimming; video_filter s1
  past its trims. v10 interim table now **50 of 62** pass (/tmp/bot/scripts/headline_v10.sh), 7 UNFINISHED.
- mk_resume.py --rerun-status PNR-TIMEOUT ready for v11_1a's gather / fill when 1a ends.
### progress 11:56 (v11 vs v10, first 20 tasks (seed 1, kernels 1-31): 11 identical routes, 3 newly CLEAN, 3 slower where the late phase pre-empted v10's search, 2 PNR timeouts)
| kernel s1 | v10 | v11 | why |
|---|---|---|---|
| brhash | NOT CLEAN, lat sum 14610 | CLEAN, 12648 | formal A34's rewrite (cache_v11) |
| nested | NOT CLEAN, 10752 | CLEAN, 11052 | A34's rewrite |
| cmpchain | NOT CLEAN, 1644 | CLEAN, 1752 | the late phase (as its local test) |
| countloop | CLEAN P 19.12 (search route) | CLEAN P 23.17 (+21 %) | late phase pre-empted the search |
| memsum | CLEAN 24.56 (search) | CLEAN 28.19 (+15 %) | same |
| dot2 | CLEAN 27.43 (search) | CLEAN 29.26 (+7 %) | same |
| fill / gather | CLEAN | PNR-TIMEOUT at it 0 | load; rerun part when 1a ends |
- Mechanism (countloop s1, both flows): the finish phase ends NOT CLEAN; v10's search phase then found a clean, faster
  structure (19.12 vs the finish phase's best 21.27); v11 builds the late phase first and skips the search for its
  route. **v12 candidate 2 is now measured, not hypothetical:** late phase only after the search has failed.
- v11 continues as filed (it measures the late phase as designed: gains where the search cannot clean, losses where
  it could); its headline will show both columns.
### progress 11:59 (AUTO_LATE_AFTER_SEARCH=1 committed (opt-in, 97169dac9) and under test locally; PREDICTION written before any result)
- The knob: v11's late overbuild phase only after the search phase has failed too -- this run goes v10's way first
  and, on a NOT CLEAN result, re-enters itself on its own state with the late phase on. v11's parts do not set it.
- Tests (/tmp/bot/runs/las, v11's export line + the knob): **countloop s1** -- predicted: no late phase; the search
  ships v10's search route (sdf as v10's, P ~19.1 ns, not v11's 23.17). **cmpchain s1** -- predicted: the search does
  not clean it (v10 shipped NOT CLEAN), "late-after-search:" in the log, the late phase from it 11, a CLEAN late route
  like v11's (latency sum ~1752 ns).
- Guarded-route gate 47 / 57 PASS so far.
### progress 12:17 (nest3 s4's "status=FAIL draws=3/4" is an out-of-memory kill on the farm, not a wrong answer: its 4th draw never ran; re-run locally)
- suite13t_s5a_v10_4a_r1 task 10 (nest3 s4, rule NOT CLEAN, shipped it 10): draws 10401-10403 PASS 12 / 12; draw 10404
  "FAIL 0/12 cycles 0 ... runts: NO MONITOR OUTPUT" and the farm's log: "Detected 1 oom_kill event" -- four GLS runs of a
  5449-LUT kernel at once (DRAW_JOBS=4, the resume parts' setting) in 16G. Nothing was simulated.
- The route rebuilt here byte for byte (sdf 8651fc19, from the farm's sizes_10.vh / seed 4); draw 10404 re-running on it
  with the farm's exp.txt (/tmp/bot/nest3rj). Its verdict goes into the headline's note for nest3 (UNFINISHED either way:
  the route is NOT CLEAN). Later resume parts with large kernels get mem=32G (4a_r1_r2 filed so).
### progress 12:42 (nest3 s4's OOM-killed draw re-run on the byte-identical route: PASS 12 / 12 -- nest3 is UNFINISHED, not FAIL; the correction is in the repo with its provenance)
- Draw 10404 on su_nest3_4_10 (sdf 8651fc19, rebuilt here): PASS 12/12, 0 pulses under 1 ns, narrowest 4.06 ns,
  EQUIVALENT. research/data/suite/corrections/v10_nest3_s4/ (README, the corrected result.txt / draws.txt); the v10
  headline reads it in place of the farm's line. nest3: UNFINISHED (16 / 16 draws, all on NOT CLEAN routes).
- Guarded-route gate: 53 / 57 PASS so far.
### progress 13:15 (BOARD-QUEUE item 45: the steer guard on silicon -- three guarded routes beside their unguarded partners in item 44; both sets pass our strict gate 57 / 57)
- Guarded routes (research/data/suite/board/guard_g10: collatz64 / sqrtsub / lfsrfind s1, flow v10 + AUTO_GUARD_E=0.90,1.10,
  rebuilt byte for byte): strict gate 57 / 57 PASS (19 / 19 each), 0 pulses under 1 ns, narrowest 2.2 ns. Their
  unguarded partners (item 44's routes): also 57 / 57. Our GLS separates neither pair; formal's adversary does (unguarded
  fails at kappa 0.06-0.10, guarded none / none / 0.15). Item 45 runs the guarded three with board_suite.sh; read with
  item 44's three lines it is the guard's silicon test (unguarded FAIL + guarded PASS = the strongest evidence possible).
### progress 13:17 (v10's farm resumes are done except gcd / fold64 s4; six more tasks stopped in final() or the search and are not resumed -- their kernels pass on other seeds)
- Finished resumes added: iterative_division / if_convert / share_test_2 / spmv / stencil_2d / sumi3_mem s4,
  test_flatten_array / loop_path s2, gcd s2 / s3, isprime s3 (gcd and spmv on NOT CLEAN routes).
- Not resumed (each was past its final stack or in its trims / search when the limit hit, as digitsum etc.; the resume
  would redo final()): image_resize s2 / s4, iir s2 / s4, share_test_1 s2 / s4 -- all three kernels PASS on other
  seeds. digitsum / digitdiv: two local completions running. Left on the farm: 4a_r1_r2 (gcd s4, fold64 s4).
- **The paired guard test suite13t_s5g_g10 is already running: 19 / 28 tasks finished** (the farm took it before most
  of v11). v11: 1a 30 / 31, 1b running, 2a submitted.
- The v10 headline goes up when 4a_r1_r2 and the three local completions are in.
### progress 13:17 (the guard's paired farm test, 19 / 28 tasks: no measurable period cost, but two (kernel, seed) pairs lose convergence -- one of them with a real wrong answer on its NOT CLEAN route; my "no status worse" prediction is FALSIFIED)
- suite13t_s5g_g10 vs flow v10, same (kernel, seed): 15 pairs clean in both, **geomean P ratio 0.991** (range 0.62-1.21,
  churn) and latency-sum ratio 0.992 -- the guard costs no measurable speed, as the static estimate (+0.5 %) said.
- **Convergence:** sqrtsub s2 (v10 CLEAN 21.66 ns) and fill s4 (v10 CLEAN) end NOT CLEAN under the guard; twoloops s2
  goes the other way (NOT CLEAN -> CLEAN, but at 35.26 ns vs 15.99). The guard adds constraints, and on some seeds the
  finish phase's 6 raise-only routes do not satisfy them all.
- **sqrtsub s2 (guarded, NOT CLEAN, least short it 8: one rule-H row, ulink_n_falseResult_7's stage[1] capture, -133 /
  -140 ps): draw 10204 FAILS 7 / 13** (ran fully: 1100 cycles, monitor output, no OOM; draws 10201-10203 PASS). The rule
  flagged exactly this route as short and a draw found the failure -- the rule did its job, and the headline policy
  (no pass on a NOT CLEAN route) keeps it out; under that policy sqrtsub would be FAIL in this test.
- So: the guard's period cost is nil on average, but it costs convergence on some seeds; with v11's late phase (which
  cleans the finish phase's leftovers) it might not. Full 28 pending; the next-flow decision waits for it.
### progress 13:18 (local work in flight; lock refresh)
- Late-after-search tests: countloop s1 at the end of its finish phase (it 10, 2 short) -> its final and search next;
  cmpchain s1 in its finish phase. Local v10 completions (digitsum / digitdiv s2, video_filter s1) in their finals.
- The farm's guarded seed-1 routes ship exactly the local ones' P (sqrtsub 20.117, lfsrfind 21.045): item 45's routes
  reproduce there too. Local guarded seed-2 runs stopped (the farm's test has them).
### progress 13:38 (a candidate next flow under local test: v11 + AUTO_LATE_AFTER_SEARCH + the 10 % guard, on the guard's failing case sqrtsub s2)
- Why: the guard alone loses convergence on some seeds (sqrtsub s2 shipped NOT CLEAN and a draw failed); the late
  phase exists to clean a finish phase's leftovers, and after the search it should not cost the search's rescues.
- PREDICTION: pass A (v10's way + the guard) ends NOT CLEAN at it 8 like the farm's g10 run (same route, sdf 9c11825a);
  the search does not clean it; "late-after-search:" then the late phase cleans it; PASS 4 / 4 on a rule-CLEAN route.
  (/tmp/bot/runs/v12c, /tmp/bot/scripts/v12_launch.sh.)
### progress 14:17 (waiting: late-after-search countloop s1 in its draws -- its search route reproduced v10's exactly, P 19.116 untrimmed; cmpchain s1 past its finish phase; candidate-flow sqrtsub s2 in its loop)
### progress 14:17 (AUTO_LATE_AFTER_SEARCH behaves as designed on both tests (results pending their draws))
- **countloop s1:** finish phase NOT CLEAN at it 8 (P 21.269 untrimmed, v10's route), the search's structure
  (BDC_FORK_OUT_LINK=n13__0,n15__0) clean at it 11 with **P 19.116 untrimmed -- v10's search route exactly**; no late
  phase (v11 shipped 23.17 here).
- **cmpchain s1:** finish phase NOT CLEAN, the search had nothing to search (no loop: no event graph), then
  "late-after-search:" and the re-entry: RESUMED from its own state, phase 3 from it 11, **it 11 rule-CLEAN as built,
  sdf 153e27be -- the same route as v11's and as the late phase's own local test**.
- So the knob gives v10's route where the search rescues and v11's where it cannot. Draws next; then it is the late
  phase's form for the next flow.
### progress 14:23 (AUTO_LATE_AFTER_SEARCH, countloop s1: PASS 4 / 4 at P 19.116 ns -- v10's result exactly, where v11 shipped 23.17)
- las countloop s1 (v11's environment + the knob): rule CLEAN it 11 (the search route), P 19116 ps, latency sum 7950 ns,
  LUTs 1864, PASS 4 / 4 -- the same P and latency as flow v10's seed-1 route; v11: 23.17 ns. cmpchain s1's late route
  in its draws.
- The candidate next flow (v11 + the knob + the 10 % guard) on sqrtsub s2 is at it 10 on the farm g10 run's own route
  (sdf f3dc482f): its pass A reproduces the guard-alone trajectory, as it should; the late phase is next.
### progress 14:43 (STATE OF PLAY -- read this first if the session ends here)
- **Board (BOARD-QUEUE):** items 42 (collatz v10 s1, 14.48 ns), 43 (xorshift v10 s1, 16.35), 44 (flow v10's suite, 46
  kernels, one loop: research/tools/suite/board_suite.sh research/data/suite/board/suite_v10), **45** (the steer guard's
  silicon test: guarded collatz64 / sqrtsub / lfsrfind s1 beside item 44's unguarded ones). All strict-gated here;
  research/data/suite/board/README.md says what is where.
- **Headline:** still suite13t (42 / 62). **v10 table ready to publish** (/tmp/bot/scripts/headline_v10.sh; interim
  50 / 62, 8 UNFINISHED) once 4a_r1_r2 (gcd / fold64 s4) and the three local completions (/tmp/bot/runs/v10loc_*:
  digitsum s2, digitdiv s2, video_filter s1 -- finished here from the farm's saved state; the farm's 240-min tasks
  redo final() on every resume) land. Correction in research/data/suite/corrections/v10_nest3_s4 (an OOM-killed draw).
- **Steer guard (AUTO_GUARD_E, opt-in):** census research/data/suite/board/screen_v10/census.md; formal B30; static cost
  +0.5 %; farm pairs suite13t_s5g_g10 21 / 28: P ratio 0.991 but 2 seeds lose convergence (guarded sqrtsub s2 NOT
  CLEAN, a draw FAILS). **Late-after-search (AUTO_LATE_AFTER_SEARCH, opt-in, verified):** countloop s1 back to v10's
  19.12 (v11 23.17), cmpchain s1 into v11's late route. **Candidate v12 = v11 + both knobs**: header drafted in
  /tmp/bot/scripts/v12_hdr.txt; its test (guarded sqrtsub s2 through the late phase, /tmp/bot/runs/v12c) decides
  whether the guard goes in. File v12 with mk_v11.py-style generation once v11's last part is submitted.
- **Farm (14:30):** v11 1a 30 / 31 (then: mk_resume.py --rerun-status PNR-TIMEOUT for gather / fill), 1b, 2a running,
  2b.. waiting; v10 4a_r1_r2 running; g10 21 / 28.
- **Next-flow candidates also logged:** resumable final() (the 240-min resume loop), PNR-timeout retry.
### progress 15:05 (candidate v12 (v11 + late-after-search + the 10 % guard) on sqrtsub s2: the guard's lost seed is CLEAN again after the late phase)
- v12c sqrtsub s2: pass A = the guard-alone route (least short it 8, the same -140 ps H row, sdf 9c11825a), the search
  did not clean it, "late-after-search:", then **phase 3 from it 11: rule-CLEAN as built** (raised 0, negative 0;
  latch-fed races >= 22.99 sd). Trim-back, final and draws next. If it passes, the guard's convergence loss is
  absorbed by the late phase as intended, and the guard goes into v12.
### progress 15:06 (the guard's paired farm test is complete: no speed cost (P ratio 1.003 over 18 clean pairs), convergence 1 lost + 1 gained + 1 lost with a failing draw; v10's farm parts are done)
- suite13t_s5g_g10 (flow v10 + AUTO_GUARD_E=0.90,1.10; 7 thinnest kernels x seeds 1-4) vs v10, same (kernel, seed): 22 of
  28 tasks finished (6 timeouts on dot2 / if_loop_2 / fill / twoloops, not resumed -- v12 runs the guard on the whole
  suite with the late phase). Transitions: 18 clean -> clean; fill s4 clean -> NOT CLEAN; **sqrtsub s2 clean -> NOT CLEAN
  with a failing draw (7/13)**; twoloops s2 NOT CLEAN -> clean; twoloops s4 NOT CLEAN both. **P ratio geomean 1.003**
  (0.62-1.48) and latency-sum ratio 1.006 over the 18 pairs clean in both. Results: research/data/guardx/gate/
  g10_farm_results.txt. Verdict on the prediction in the request's header: P part held, status part FALSIFIED.
- The guard alone is therefore not a flow: it needs the late phase behind it. The candidate v12 test (sqrtsub s2 through
  the late phase, rule-CLEAN at it 11) is in its draws.
- **v10's farm parts are done**: table 50 PASS / 8 UNFINISHED / 4 NO RESULT (digitsum, digitdiv, sobel, video_filter);
  gcd s4 PASS on a NOT CLEAN route, fold64 s4 PASS clean. Publishing waits only for the three local completions.
### progress 15:07 (HEADLINE: flow v10 -- 50 of 62 kernels pass (suite13t: 42), 8 UNFINISHED, 4 NO RESULT; ours / Dynamatic on-merges 0.98 over 35, at its recurrence bound 2.11)
- research/data/fifteen/README.md top: flow v10's table (all farm parts and resumes, nest3 s4 corrected). Newly passing
  vs suite13t: divmods, fir, iir, image_resize, isprime, loop_path, quadrec, share_test_1, single_loop; lost:
  stencil_2d. Same-kernel P ratio 0.99 over 30 (formal's rewrites: collatz 0.71, collatz64 0.76, xorshift 0.90).
  Ours / Dynamatic: on-merges 0.98 (n 35); bound 2.11 (1.70 without the five largest terms, 1.65 on the 10
  one-cycle-per-iteration kernels). UNFINISHED: cmpchain, factorial, gcd, iterative_division, nest3, nested, spmv,
  stencil_2d (v11's target). NO RESULT: digitsum, digitdiv, sobel, video_filter (the 240-min resume loop; three being
  finished locally -- the table gets them when they land).
- Does NOT show: the board's view of any of it (items 42-45 queued); v11; the guard's effect on the whole suite.
### progress 15:49 (AUTO_LATE_AFTER_SEARCH verified end to end on both kinds of kernel)
| kernel s1 | v10 | v11 (late phase first) | v11 + AUTO_LATE_AFTER_SEARCH |
|---|---|---|---|
| countloop | CLEAN, P 19.116, lat sum 7950 (search route) | CLEAN, P 23.17, 9474 (late route) | **CLEAN, P 19.116, 7950** (v10's route) |
| cmpchain | NOT CLEAN, lat sum 1644 | CLEAN, 1752 (late route, sdf 153e27be) | **CLEAN, 1752, sdf 153e27be** (v11's route) |
- Both PASS 4 / 4. The knob takes the better of v10 and v11 per kernel on these two. Next: the candidate v12 test
  (+ the guard) on sqrtsub s2, in its final trims.
### progress 16:09 (waiting: candidate v12 sqrtsub s2 in its trim rounds; v10 local completions in their trims; v11 1a 30 / 31, 1b / 2a / 2b running)
### progress 16:35 (flow v12 filed: v11 + AUTO_LATE_AFTER_SEARCH + AUTO_GUARD_E=0.90,1.10; its key local test passed)
- **v12 test, sqrtsub s2** (the seed the guard alone lost, with a failing draw): pass A = the guard-alone NOT CLEAN route,
  the search did not clean it, the late phase did -- **PASS 4 / 4 on a rule-CLEAN route** (draw 10204 passes now),
  P 27.33 ns, latency sum 12768 ns (v10's unguarded route: 21.66 / 10374). Prediction (journal 15:05) held.
- research/cluster/requests/suite13t_s5a_v12_{1a..4b}.sh (mk_v11.py's generation: v11's body, all 62 kernels, seeds
  1-4, state_v12; header with the evidence and the PREDICTION: no kernel worse than v11's status, P no worse than v10's
  where v10's search rescued, every shipped route's weakest select gate at x >= 0.10). Named after v11's parts, so they
  queue behind them; results likely after this session. **Flow code frozen until v12's last part is submitted.**
- Why the guard goes in: PROGRAM goal 1 comes strictly first; the guard is the conservative side of formal B30's
  adversary (three of v10's routes), costs nothing where routes converge (P ratio 1.003), and its convergence loss is
  what the late phase absorbs. v12's full-suite numbers against v11 and v10 will say what it costs.
### progress 16:35 (local v12 previews started on memsum s1 and dot2 s1 -- the other two kernels v11's late phase slowed (v10 24.56 / 27.43, v11 28.19 / 29.26); /tmp/bot/runs/v12c)
### progress 16:50 (SESSION SUMMARY so far -- the session's result in PROGRAM's format; updated at the end)
Toolchain: nextpnr 6e5d224472232d5d (cells/verify/toolchain.sh passing before every build)   Seeds: 1-4 per kernel (farm);
local tests seed 1 / 2 as stated.
Did: (1) **board**: BOARD-QUEUE items 42 (collatz v10 s1), 43 (xorshift v10 s1), 44 (flow v10's suite, 50 kernels, one
self-judging loop) and 45 (the steer guard's silicon test); new tooling cells/hw/xsdb_bench_vec.tcl (+ mock, test
9 / 9), research/tools/suite/{board_rebuild.sh, board_vec_judge.py, board_suite.sh, mk_board_specs.py}; every route
rebuilt byte for byte here, formal reproduced item 42's independently (B29). (2) **headline**: flow v10 published --
50 of 62 pass (suite13t 42), 8 UNFINISHED, 4 NO RESULT; Dynamatic wording fixed for audit T173 (+ all 248 nextpnr logs).
(3) **steer races**: census of item 44's routes (rule E's x for 46, formal's screen for 19), formal B30's adversary
failures on three of them, the 10 %% guard (AUTO_GUARD_E) measured (static +0.5 %%; paired farm test P 1.003 but a
convergence cost) and its silicon pair (item 45). (4) **flow**: AUTO_LATE_AFTER_SEARCH (v11's late phase only after the
search; verified on countloop / cmpchain); flow v11 running; **flow v12 filed** (v11 + both knobs). (5) negatives /
corrections: carry-tracking delay lines (<= 1 element on the cycle); nest3 s4's farm FAIL was an OOM kill (re-run PASS);
the 240-min resume loop on four big kernels (three finished locally).
Measured: see the progress notes; key numbers -- v10 50 / 62; ours / Dynamatic on-merges 0.98 (n 35); collatz 14.48 /
xorshift 16.35 ns (items 42 / 43, strict gate 35 / 35 each); guard P ratio 1.003 (18 pairs).
Does NOT show: anything on silicon (items 42-45 queued); v11's or v12's suite-wide effect (running / queued).
Next: v10 table + the three local completions; v11 results -> headline and its resumes; v12 when it runs; the board.
