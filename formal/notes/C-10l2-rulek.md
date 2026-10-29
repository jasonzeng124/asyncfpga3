# C-10l2: diagnosing rule K (10l's "X4 ctl_req fork" rows on gcd_hw)

Shard C, probe 10l2, 2026-10-29. Core Lean only; no sorry, axiom or native_decide.
STATUS: diagnosis done; Lean checked; counted routes (with --freq) being re-run (see Results).

## Verdict

**Front-end bug, not a race.** 10l's rule-K failures (16-24 of 42 rows per seed, down to
-5.9 ns) came from how the code that produced `results/summary10l.txt` built the late side,
not from the routes. Two things were wrong. (1) The max-node certificate let the control
sender's C-element "fire again" when its first handshake input (the upstream re-request)
arrived, even though it must wait for z_ack's fall as well. This alone reproduces the failure
pattern exactly on fresh routes. (2) Without the own-latch block, the sender's latch output
was a phase-0 shortcut around the ctl_req delay line. The rule now in `rules10l.py` already
has both fixes (the max-node arg-max is tried both ways, plus the latch max node and
H_LATCH_CLOSED). With them, rule K passes 42/42 rows on 4 fresh seeds in all six corner
models; the worst margin is +1.0 ns (fastG), and the per-pin LUT arcs B's form charges cost
<= 70 ps more. The multi-ns chain that 10l charged is bd_link's request delay line
(DELAY 8-14 LUT1, FASTFALL = 0). It belongs in the condition, because ctl_req's fall really
crosses it. But it also lies on the true causal path to the next `s` change, so it cancels.
Silicon risk of this race: negligible. The margin is a full control round trip, at least
10 ns on SDF, against the skew between two sinks of one routed net.
Also: rule K is mislabelled. It is B's X3 hold half `bd_mux.bundled_s_hold` (UNCHECKED in
B's JSON), not X4. B's X4 says that ctl_req fork needs no condition.

## 1. What the condition is (re-derived from B's Lean)

- B's X4 row (`bd_mux.isochronic_forks`, out/cell_constraints.json) says: "the ctl_req ->
  {uj0, uj1} fork needs no condition under FIFO branches (H_CTL_SEQ follows from
  causality)", backed by `OpsCounter.mux_ok_noskew`. `MergeMuxSI.mux_needs_iso_cr` is
  untimed: a wire branch there is a single variable that can drop an excitation (a runt). A
  FIFO/monotone routed wire cannot do that.
- What 10l's rule K checks ("the ctl pulse at a join has ended before s can change there") is
  B's **X3 hold half**, `bd_mux.bundled_s_hold` = `LibGapMux` H_HOLD_PIN, which is
  `MuxEnv.H_S_PIN0/1` in `OpsTimedMux`:
  `Cf + pc_k.hi <= S1 + ps_k.lo` per join k, EXACT over the delay box (`join_box_exact`).
  Here pc_k and ps_k include the join's own pin arcs I1->O6 and I2->O6, and S1 is "s held to
  ctl_ack fall = z_ack fall". B's JSON marks this row UNCHECKED (`rule: none`).
- New Lean (`Formal/Timing/RuleK.lean`) ties the launch-based check to B's exact form:
  - `sel_fall_after_ctl_fall` (from the REAL uj0/uj1 INITs through B's `LutEq`): the
    SELECTED join cannot fall before it reads ctl_req low, i.e. before `Cf + pc_sel.lo`.
  - `ruleK_hold`, `mux_joins_ruleK`: assume H_ROUND_TRIP (`tf + Rt <= S1`: the next `s`
    change at its driver comes at least `Rt` after the selected join's fall; that is
    selected join -> uor -> udly -> server -> z_ack fall -> sender C -> its latch -> s), plus
    B's setup halves and H_SEL_FIRED / H_SEL_FELL. Then the fork form
    `pc_k.hi <= pc_sel.lo + Rt + ps_k.lo` at each join gives B's hold, hence B's `JSpec` at
    both joins. So the deselected join never takes the other input's token, and the
    selected one obeys the C-element law.
  - `ruleK_exact`: at the minimum round trip (`S1 = Cf + pc_sel.lo + Rt`), the fork form is
    exact over join k's delay box (via B's `join_box_exact`).
  - `witness`, `witness_conclusion`: one constructed run (B's numbers, y request falling at
    2000 ps) meets every hypothesis of `mux_joins_ruleK`, and the theorem concludes that uj0
    stays 0 for ever.
  So rule K is a weak-isochrony condition: ctl_req fork skew < one control round trip
  (+ the s-pin read). On a route, a launch at the sender's C node evaluates exactly this
  when its late side runs through the SELECTED join.

## 2. Does the extraction pair the right nets and pins? (end-to-end rows)

Yes, checked on the routed netlist (seed 2, `umux20`, the worst row of 10l):
- launch C = `ulink_n166__1.many.stage[1].u.ctl.u.u/O6`. This is the control sender
  (bd_pipe N=2, stage[1]): `bd_mux umux20 (.ctl_req(n166__1_req), .s(n166__1_data[0]))`,
  `bd_pipe #(.W(1),.N(2),.DELAY(14)) ulink_n166__1` (build/gen/gcd_kernel.v).
- data side: C -> `rdly.chain.g[0..13]` (14 symmetric LUT1s: bd_pipe passes no RFAST, so
  FASTFALL = 0 and the fall crosses the whole line) -> `umux20.uj0/A1`, `uj1/A1` (ctl_req =
  LUT pin I1 after the placer's permutation). lD = 9115 ps (sdf).
- target: `umux20.uj{0,1}/A3` (s pin), rooted only in `ulink_n166__1.many.stage[1].u.lat.odd.u`,
  the latch enabled by C (the extractor's `lc[li][0] == C`).
- per-pin arcs (sdf / slowG): ctl pin->O6 hi 124 / ~120, s pin->O6 lo 124 / 77 ps.
The pairing is right. Shared prefix credited at X = `rdly.chain.g[0]/A4`.

## 3. Where -5.9 ns came from (ablation, same routes, same checker)

`K10L_ABLATE=1` (the old 10l2's hooks, run here for the first time) emits each row 5 ways.
Seed 2, sdf, row `umux20.uj1`; late path from `pathK` in build/out/k_2.json:

| tag | (C,1) max node | latch max node | own latch blocked in phase 0 | margin (sdf) | late path to the s pin |
|---|---|---|---|---|---|
| Knocmax | no | yes | yes | **-4265 FAIL** | C -> uack g[5] side tap (FASTRISE) -> stage[0] ctl -> SDELAY(3) -> C/A5 (req_in) -> phase 1 -> C -> latch -> s: 4.85 ns |
| Kold | yes | no | no | +2225 (fails under bands) | C -> own latch Q (the closing edge, no real change) -> uj1/A3 -> uj1 -> uor -> udly(12) -> n165 ctl -> uack -> C/A1 -> phase 1 -> latch -> s: 11.34 ns |
| K | yes | yes | yes | **+10518 uncredited, PASS credited** | C -> rdly(14) -> uj0/A1 (selected join) -> uj0 -> uor -> udly(12) -> n165 ctl -> uack -> C/A1 -> phase 1 -> C -> latch -> s: 19.63 ns |

Counts per seed (FAIL rows of 42; sdf/sdfband/fast/slow/fastG/slowG), 12 MHz-default routes:

| seed | K | Kold = Knoblk | Knocmax |
|---|---|---|---|
| d | 0/0/0/0/0/0 (min 7250/3304/3616/7283/1245/1938) | 0/2/0/1/6/6 | 6/22/14/18/24/24 |
| 2 | 0/0/0/0/0/0 (min 6300/3029/3367/6790/1010/1460) | 0/4/0/2/6/6 | 9/21/16/19/21/22 |
| 3 | 0/0/0/0/0/0 (min 6877/3017/3688/7388/1343/2173) | 0/6/0/0/6/6 | 10/20/16/17/21/22 |
| 4 | 0/0/0/0/0/0 (min 7056/4513/3681/7896/1496/2840) | 0/2/0/0/6/8 | 10/22/15/19/22/22 |
| 10l (old routes) | | | 16-20/22/19-20/20-22/23-24/24-26 |

- **Bug 1 (the 10l summary): the (C,1) max node was not effective.** The code committed
  at 3f8eed9 is the 10l rule K that made summary10l (08:57); its successor dfc8edc changed
  exactly this. Run verbatim (`tc_3f8/`) on the seed-d route, it gives EXACTLY Knocmax's
  numbers (6/22/14/18/24/24, min -3367/-5536/-2765/-6781/-4146/-9991). Cause: `emit_credited`
  fixed the max-node arc of potB to potA's arg-max. With X = the join's ctl pin, C's req_in
  pin is unreachable from X, so the arg-max fell back to an "unsettled source" (req_in), and
  potB then let C fire on req_in alone. That is a C-element firing on one input. The
  certificate stays sound (tcheck accepts it, and it is a valid lower bound), but it is
  loose by the whole round trip. Seed d, `umux20.uj0`, sdf, in the 3f8eed9 run: X =
  `umux20.uj0/A3`, the uncredited margin is **+3918** (it passes), but the credited
  certificate's potB is 4232 against lD 7599, i.e. **-3367 FAIL**. The credit step made the
  row worse than no credit at all. dfc8edc also tries potB's own arg-max, which fixes it. The
  same rows fail as in 10l: stage[1] of 2-stage pipes with DELAY 8-14 (n166__1, n166__0,
  n32__2, n53__*, n64__*, n90__*, n129__2). In these pipes the upstream stage re-requests
  within ~3 ns, while ctl_req's fall still crosses 8-14 LUTs.
- **Bug 2 (residual, G variants): the own-latch shortcut.** Kold has the C max node but lets
  the closing edge of C's own latch "change" s in phase 0. That makes uj1 "fire" off its s
  pin and skips the ctl_req delay line. It is sound but loose. Blocking it rests on
  **H_LATCH_CLOSED**: C's fall closes the latch with D = Q, so Q moves only after the enable
  reopens. That is what rule H checks. On these routes tighten.py's rule H gives the ctl
  links' latches >= 3.8 ns margin (e.g. `ulink_n166__1 ... stage[1]` enable 419 / data
  4493-4895 ps, sdf; build/tighten_*.log).
- **The multi-ns chain** is `rdly` (bd_link's req_out delay line). It is legitimately on the
  data side, but it is also the first segment of the true late path (through the selected
  join). The credited check counts the shared prefix once (`SharedPrefix.pot2_sound`,
  X = rdly g[0]). Nothing in it should be excluded.
- **Real race?** No. The worst K margin over 4 seeds x 6 models is +1010 ps (seed 2, fastG
  = fast corner with the 0.772/1.155 band). With B's per-pin arcs added (front-end
  arithmetic, `rows.py`), it is +979 ps. On SDF the margin is >= 6.3 ns: a control round trip
  through the mux's 12-LUT udly and the downstream ack line, minus the skew between two sinks
  of one routed net. A board failure would need the ctl_req net's branch to one join to lag
  the other by more than a full round trip. Likelihood: negligible.

## 4. What the PASS rests on (hypotheses)

Hypotheses on tcheck's side, each with its status:
- `xverdict_sound` (10l): H_CLEAN_EDGE(X) and H_ONE_SAMPLE_PER_WIRE at X = an rdly pin.
  Witness: none on routes (10b's toy only).
- H_ALL at max nodes: (C,1) via `MaxNode.cel_needs_pin` + H_FB_FIRST(C) (rule Rc); the
  select latch via its enable, i.e. H_LATCH_CLOSED (rule H, which passes on all 4 seeds).
- The prjxray front end at HEAD 16e798d: OUTMUX hop included, fallback arcs use the SDF band
  (H_FALLBACK_BAND), H_ONE_CORNER.
- Graph looseness, all on the safe side: storage crossed on any input in phase 0;
  FASTRISE side taps used for falling edges.
- The pin-arc correction (B's I1/I2->O6 terms) is front-end arithmetic, not tcheck.

In Lean (`mux_joins_ruleK`): B's H_PIN_READ, H_S_STABLE, H_CTL_PULSE, H_SEL_FIRED,
H_SEL_FELL, H_ROUND_TRIP. Witness: `RuleK.witness`, where all hold jointly on one
constructed run (constant delays). H_ROUND_TRIP is NOT proved from the netlist: the routed
late side bounds it, but the step from tcheck's potential to `tf + Rt <= S1` is not
mechanised (the same physical -> event-time gap as 8x).

NOT covered: more than one token; Kleene reads; the Kold/Knocmax losses as theorems (they are
measurements); whether the mux's own `udly` FASTFALL (opt-in, BDC_LINK_FASTFALL=1) would
shorten the round trip. With BDC_LINK_FASTFALL=1, udly and the request line fall in about
1 LUT. The round trip drops to roughly z_req -> downstream -> uack(6) -> C. The margin stays
positive on SDF by arithmetic from these paths, but this is UNMEASURED.

## Files (all mine)

| file | what |
|---|---|
| `formal/lean/Formal/Timing/RuleK.lean` | `jB_hold`, **`sel_fall_after_ctl_fall`**, `ruleK_hold`, **`mux_joins_ruleK`**, **`ruleK_exact`**, `witness`, `witness_conclusion` |
| `formal/lean/Wip/C10l2/Axioms.lean` | `#print axioms` of the headlines (propext, Classical.choice, Quot.sound) |
| `formal/tools/rulek/route.sh`, `routeall.sh` | copy of tcheck/route.sh (private trees build/tree_SEEDf, `NEXTPNR_FREQ` default 100) |
| `formal/tools/rulek/run.sh` | rule K + ablations on the routes with the private tcheck copy |
| `formal/tools/rulek/tc/` | tcheck from git HEAD 16e798d (Formal/* verbatim = formal/lean, cmp-checked). Only edit: `rules10l.py` (per-tag meta, which fixes the old 10l2 hooks sharing one `x` dict; per-pin LUT arcs in meta) |
| `formal/tools/rulek/tc_3f8/`, `tc_dfc/` | tcheck as of 3f8eed9 / dfc8edc (git archive), for the reproduction |
| `formal/tools/rulek/summ.py`, `rows.py` | fail counts per tag/variant; per-row table with the pin-arc correction (results/k_rows.tsv) |

## Reproduce

    cd formal && ./check.sh Formal/Timing/RuleK.lean            # [check] OK
    cd formal/tools/rulek && ./routeall.sh                     # 4 seeds, --freq 100 (cells/verify/toolchain.sh first)
    ./run.sh df 2f 3f 4f && python3 rows.py df 2f 3f 4f        # K + ablations, table
    # 10l's own code on a route:  (cd tc_3f8 && PYTHONPATH=../../fasm2lean:../../prjxdelay \
    #   python3 extract.py ../build/tree_d/cells/build/hw/gcd_hw gcd_hw --cells ../build/tree_d/cells \
    #   --osc dhk --osc invhk --no-hi --rules10l K --out X.tc --json X.json) && ../tc/.lake/build/bin/tcheck X.tc

## Progress log
- 07:4x: read B's Lean; mislabel found (above). No gcd_hw SDF on disk: re-routing.
- 08:2x: seed d: K passes, Knocmax = the 3f8eed9 code exactly.
- 09:1x: seeds 2, 3, 4 (12 MHz default target, i.e. WITHOUT --freq: route.sh copied from
  10e did not pass it): same picture. Re-routing all 4 seeds with --freq 100 for the counted
  numbers.
- 09:4x: --freq 100 routes: for seeds d and 2 the FASM (bitstream) is byte-identical to the
  12 MHz-default route (sha256 b73e1ba0.. / 1ee50d56..); the SDF differs only in arc order.
  The target only affects the clocked readback/lap logic, so the physical design rule K reads
  is the same. Per-pin-arc corrected minima on the 12 MHz routes (rows.py d 2 3 4):
  sdf 6300, sdfband 2968, fast 3356, slow 6766, fastG 979, slowG 1393 ps (correction <= 67 ps).
