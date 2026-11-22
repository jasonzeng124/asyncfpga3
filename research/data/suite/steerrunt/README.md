# Narrow pulses on the kernel's handshake outputs: an opt-in gate check (subagent steerrunt, 2026-11-19)

Brief: the gate (research/tools/eventgraph/bench_gate.sh: bits-decoded netlist, prjxray SDF, fid, delay-model draws)
passed flow v1's ipow seed 4 route although its loop-exit steer races its select on every call (research/data/suite/
hangs.md section 3; SIM-VS-BOARD rows 4 and 6): the gate's runt model rejects the pulses, so the answers stay right.
hangs proposed "no pulse under ~1 ns on any steer output". This directory: the check, its threshold and why, its
cost, its negative and positive controls, and a sample of the automatic flow's shipped routes.
Every routed number here: nextpnr `6e5d224472232d5d` (cells/verify/toolchain.sh all ok before the builds); every
route rebuilt and its sdf md5 checked against the one judged before; expected values from the kernels' C
(kernel_oracle.sh).

**Summary.**
- `GATE_RUNTS=1` (report) / `GATE_RUNTS=fail` (strict) in bench_gate.sh: a Verilog monitor generated per route
  (cells/gls/ps/gen_runt_mon.py, compiled into the gate's run by build_ps.sh PS_RUNTS=1) counts every pulse narrower
  than 150 / 500 / 1000 ps on 155-192 kernel handshake nets per kernel (every steer output, mux / merge / arbiter
  output, C-element, link controller = latch enable, matched-delay output). Unset, the gate is byte-identical. Cost:
  not measurable (190-197 s against 196 s, n = 1 each); checked against an independent VCD reading of the same run
  (1768 pulses, identical).
- Threshold, from the mechanism: a pulse longer than its reader's loop is captured (kernel loops <= 0.89 ns at the
  draws, 1.4 ns at SLOW_MAX); nothing is known to be swallowed on this die (no source; H_RUNT unrun), so every pulse
  counts from 1 ps; 1 ns sits above the loops at the draws and below every legitimate handshake phase measured
  (>= 1.54 ns anywhere, >= 2.64 ns in the brief's classes).
- **Negative control flagged**: ipow v1 seed 4 (sdf 1ac15af5) passes the gate 17/17 on draws 10402 and 10403 with
  1756 / 554 pulses under 1 ns on 41 / 40 of 192 nets (narrowest 33 / 16 ps), from the two loop steers the v1 rule
  flagged (ucond_br9, ucond_br7) into link enables, the arbiters and the loop's data links; GATE_RUNTS=fail fails both.
- **Positive controls clean**: BOARD-QUEUE items 38, 39, 40, 41 (sdfs 81bbe268, c56def07, 9585dde4, 3497ca67 rebuilt
  identical): 13 runs over max / min / worst / draws, **no pulse under 1 ns on any net** (narrowest 1.54-7.36 ns).
- **suite6 sample clean**: 9 shipped automatic routes (5 NOT CLEAN), 12 runs (`worst`; the rule's vertex draw on the
  three with select-race rows): **no pulse under 1 ns**. Their NOT CLEAN rows (E <= 208 ps, A, H) never became a
  pulse; only the route whose rows were large (v1 s4, E -1070 ps) races.
- **Which would fail a strict runt check: of everything run, only flow v1's ipow seed 4 route.** No board item
  (38-41) and no sampled suite6 route would.

## 1. The check (opt-in; unset, the gate is byte-identical)

`GATE_RUNTS=1 research/tools/eventgraph/bench_gate.sh ...` (or `GATE_RUNTS=fail`). bench_gate.sh exports
`PS_RUNTS=1`; cells/gls/ps/build_ps.sh then runs **cells/gls/ps/gen_runt_mon.py** after gen.py and compiles the
monitor module it writes (runt_mon.v) into run_baked.vvp, beside the bench (the same hook as PS_BUNDLE / PS_MON_GEN).

**What is watched** (the kernel only: cells under `bridge_i.udut.` in nextpnr's routed JSON, never the bench's
clocked side), each net at its DRIVER pin in the netlist decoded from the bitstream (nets.map, as gen_bundle_mon.py),
so a pulse is measured where it leaves the LUT; the interconnect is transport, so every reader sees it. A LUT output is
watched when it is
- (A) a state node: its output routed back into one of its own pins -- every C-element (bd_join / bd_fork trees, an
  operator's join, a mux's joins and acknowledges, an arbiter's state and acknowledges) and every link / pipe stage
  controller, which is also that stage's **latch enable** -- except latch storage (`.lat.`);
- (B) a steer output: both branches of every bd_steer (req0 = O5, req1 = O6) and its acknowledge OR;
- (C) the driver of a kernel channel net (`<name>_req` / `<name>_ack` at the kernel's top level): a matched delay's
  last element (a link's req_out / ack_in, a mux's, merge's or operator's z_req), a constant source's request;
- (D) any other non-datapath LUT that drives a pin of an (A) node (a muxn's select decode, a pipe stage's request line);
- (E) an arbiter's grants and state outputs (`.ugrant`, `.ustate`: g1, g2, q, R0) and every cell's request OR (`.uor`).
Never watched: latch bits, data muxes, an operator's datapath, a merge's index / data, the interior of a delay line.
Each net gets a class (steer, mux, merge, link = latch enable, join, op, chan, src) and its instance. ipow: 192 nets
(steer 24, link 37, chan 55, join 25, mux 23, merge 16, op 10, src 2); collatz 159, collatz64 155, xorshift 175.
The table (runt_nets.tsv, written beside run.log) also gives each state node's own loop (TLOOP = feedback wire + pin
arc, as gen.py bakes it for this run's corner) and the loops of each net's state-node readers.

**What is counted.** A pulse is a level bounded by the same 0/1 level on both sides (0-1-0 high, 1-0-1 low dip,
0-x-0 / 1-x-1 an x pulse); width = time between its two edges at the driver. Each net is sampled 1 ps after it changes
(fid_core.vh's FID_SAMPLE), so the changes of one time step count once (a state node's resolver can move its output
twice in one step; the first version counted such a zero-width excursion as the end of a pulse: 1 false pulse in 1757
on the negative control, found by the VCD check in section 3 and fixed). Per net: pulses narrower than 150 / 500 /
1000 ps (GATE_RUNTS_T; a third value of 0 = the loop threshold, section 2), of which high / low / x; the narrowest 0/1
pulse of ANY width (so a clean route reports its narrowest handshake phase); the time of the first. Output lines:
`RUNT` (the first 100 pulses < T3, each with time, width, level, net), and at every batch end (bench_busy falling)
`RUNTMON` per net hit, `RUNTCLS` per class (nets, nets hit, pulses, narrowest of any width), `RUNTSUM` (totals,
narrowest of any width, the longest kernel loop at this corner).

**The verdict.** bench_gate.sh appends one field, e.g. (the negative control):
`| runts <150/500/1000 ps 1525/1752/1756 x 12 on 41 of 192 nets (...), narrowest 33 ps, loops <= 886 ps: steer
ucond_br9.req1 64+1x (33 ps), ...`, and writes runts.txt (per net hit, cumulative; per class the narrowest pulse of any
width) beside run.log. GATE_RUNTS=1 reports only: PASS / FAIL are the gate's own. **GATE_RUNTS=fail** fails the run
when any watched net (or, with GATE_RUNTS_CLASSES=steer,mux,..., any net of those classes) has a pulse narrower than
the third threshold (1 ns by default); the field then ends `RUNTS FAIL (n net(s))`.

**Default unchanged.** Unset, bench_gate.sh passes no new plusarg, exports nothing new, and the verdict code takes
the path it took before: the verdict printed by HEAD's and by the new python on the same run.log is byte-identical
(checked on four runs' logs: the negative control, item 41 at FAST_MIN, suite6 collatz64 seed 2, and one cut short); build_ps.sh without PS_RUNTS runs exactly the commands it ran before.

## 2. The threshold: what a pulse must be to be swallowed or captured on this die

A pulse on a watched net matters where it meets a reader with memory: a C-element, a link controller, an arbiter, a
latch enable. What is known and what is not:

- **Certainly captured (known, in the transport picture): a pulse longer than the reader's own loop.** A LUT state
  node holds a value once its output has gone round its feedback wire back to its feedback pin (TLOOP = wire + pin
  arc). A pulse at an input whose other inputs already agree, lasting longer than TLOOP, has been fed back before it
  ends: the node holds it. fid does the same (fid_core.vh: delta = p - (TLOOP - WIN/2) + N(0, WIN/4) > 0 commits).
  The kernel loops, per run (RUNTSUM tloopmax, every watched state node): 195-886 ps on the ipow v1 route at draw 10402
  (median 284), longest 463 ps at FAST_MIN, 647-670 ps at `worst`, 1329 ps at SLOW_MAX (item 38); H_RUNT's cells
  211-633 ps at band 0.288 (research/board/runt/README.md). So a pulse wider than ~0.9 ns at the draws is captured by
  any kernel reader -- and then the gate sees what it does (a wrong token, a hang), because fid captures it too.
- **Certainly swallowed: nothing known.** No 7-series figure exists for the narrowest pulse a LUT input, a routing
  wire or a LUT loop rejects (research/data/fid/meta_sources.md: "LUT pulse rejection: none"). fid passes every pulse
  through a LUT (transport) and lets a state node reject one shorter than TLOOP - WIN/2 - noise, with TAU = WIN =
  150 ps unsourced; with its resolver off (pure transport, formal's model) a pulse shorter than the loop circulates
  (research/data/fid/runtc.md). BOARD-QUEUE item 2 (H_RUNT, research/board/runt/: 96 C-element loops forced by
  episodes of -427..+1542 ps against their own 211-633 ps loops) measures exactly where a LUT loop stops capturing;
  it is built, predicted and not yet run.
- **So the gate is blind between the two**: a pulse narrower than its reader's loop is rejected by the model (and is
  invisible in the answers) but may be captured, rejected or held metastable on silicon. No lower cutoff can be
  defended, so the check counts every pulse from 1 ps up; the upper threshold must be at least the longest loop a
  pulse may meet, plus the resolver's window (WIN/2 + 3 sigma = 75 + 111 ps), so that every pulse the model could
  hide is counted.
- **And a legitimate handshake phase is far wider.** A request (or acknowledge, or enable) on these nets stays at a
  level for at least a round trip through another cell. Measured on clean routes, the narrowest pulse of ANY width on
  ANY watched net, over the 25 runs of sections 5-6 (13 on the board items at max / min / worst / draws, 12 on the suite6 routes): per class steer 3.58 ns, join 3.58, link 3.05, chan 3.05, merge 2.71, mux 2.64, operator request lines ("op", not in the brief's list) 1.54 ns -- every minimum on item 41 (xorshift) at FAST_MIN; at the draws and `worst` every class is >= 1.86 ns, at SLOW_MAX >= 4.0 ns. The runts on the negative control are 16-828 ps.

Hence the thresholds reported: **150 ps** (= WIN: below it the model rejects the pulse at every reader whose loop is
above ~225 ps, i.e. nearly all of them -- the gate cannot see these at all), **500 ps** (the median kernel loop is
~280 ps at the draws: most readers reject below this in the model, some capture), **1000 ps** (above the longest
kernel loop + WIN/2 at the draws, `worst` and FAST_MIN; anything narrower is a pulse the model can still hide at some
reader). At SLOW_MAX the longest loop is 1.33 ns: there the loop threshold (`GATE_RUNTS_T=150,500,0`, the run's own
longest loop + 186 ps = 1515 ps on item 38) is the one that covers every reader; legitimate phases there are >= 4.0 ns (item 41; 7.3-7.4 ns on items 38, 39).
The fail threshold is the third (default 1 ns): above the longest loop + WIN/2 at the draws (<= 0.89 ns + 75 ps), and
below the narrowest legitimate phase of every class on every run (>= 1.54 ns, op lines at FAST_MIN; >= 2.64 ns in the
brief's classes). At FAST_MIN the loop threshold (0.5 ns + 186 ps = 684 ps on item 41) keeps a wider margin.

## 3. Cost, and a check of the monitor against an independent reading of the same run

research/data/suite/steerrunt/cost.sh, on the negative control's route (ipow v1 seed 4, sdf 1ac15af5) at draw 10402:
the decoded netlist built once (build_ps.sh PS_RUNTS=1), compiled four ways, each run with the gate's own plusargs
(17 batches x 2 runs, 50.8 us of circuit time). One run each (n = 1; the node was shared and loaded, ~40 runnable
processes), so differences below ~5 % are noise (cost_ipow4_d10402.txt):

| variant | run wall s | user s | max RSS MB | output |
|---|---|---|---|---|
| base (the gate's run_baked.vvp) | 195.7 | 188.4 | 2190 | 4 kB log |
| + runt monitor (192 nets; every pulse printed) | 190.0; 196.9 after the sampler fix | 187.0; 191.3 | 2191; 2192 | 0.3 MB log |
| + VCD of the 192 watched nets | 187.5 | 182.8 | 2190 | 1.1 MB VCD |
| + VCD of every net (`$dumpvars(1, tb_ps.dut)`, as hangs did) | 201.4 | 196.1 | 2190 | 114 MB VCD, compile 4x longer |

So the monitor costs nothing measurable (within the run-to-run noise), as does a VCD restricted to the same nets;
dumping every net costs ~3 % of the run, 110 MB per run and a slower compile, and still needs a parser. The monitor
was kept because it needs no post-processing and the gate reads its lines directly. Every variant's BENCHRES lines are
identical to base's: the monitor does not perturb the run.

**The check of the monitor** (vcd_pulses.py): the same run's watched-net VCD, read independently with the same pulse
definition, against the monitor's own list of every pulse < 1 ns (+RUNT_MAXLINES=1000000): **1768 pulses on 41 nets
in both, identical (net, start, width, level)**; the all-net VCD gives the same 1768. The first version of the
monitor had one pulse more (1769): a link controller's output (ucontrol_merge0_olink.c) moved 1 -> 0 -> 1 in one time
step 490 ps after a real edge, and the monitor closed a "pulse" at the first of the two changes. Fixed by sampling 1 ps
after a change (section 1); the runs below all use the fixed monitor except where said.

## 4. Negative control: flow v1's ipow seed 4 route is flagged on every draw the gate passes

Rebuilt from its sizes (research/data/suite/farm/suite1/ipow_4_sizes_final.vh, BDC_AUTO=1, seed 4, lane2.sh as
rejudge.sh does): **sdf 1ac15af5 = the farm's**; routed JSON 3270666c, FASM bd441fed and kernel Verilog 83723536
identical to subagent hangs' rebuild; the .bit (5f3d852e here, a41f1ae5 there) differs in 5 bytes at offset 123, the
.bit header's date / time field (the FASM, hence every configuration bit, is the same). Gate with GATE_RUNTS=1, ipow17
(17 vectors x 2 runs), expected values from kernels/ipow via kernel_oracle.sh, no +META_INIT:

| run | the gate's own verdict | pulses < 150 / 500 / 1000 ps (+ x) | nets hit of 192 | narrowest | steers hit |
|---|---|---|---|---|---|
| draw 10402 (chains 0.242, rest 0.261, carry 0.875) | PASS 17/17 | 1525 / 1752 / 1756 (+12 x) | 41 (steer 6, merge 10, link 8, chan 12, mux 3, join 2) | 33 ps | ucond_br9 req0 36 (33-268 ps), req1 64 + 1 x, ack 64; ucond_br7 req0 10, req1 8 + 1 x, ack 22 |
| draw 10403 (chains 0.302, rest 0.220, carry 0.961) | PASS 17/17 | 369 / 544 / 554 (+12 x) | 40 (steer 6, merge 9, link 8, chan 12, mux 3, join 2) | 16 ps | ucond_br9 req0 36 (41 ps ..), req1 20 + 1 x; ucond_br7 req0 10, req1 8 + 1 x, ack 28 |
| `worst` | no batch finished in 25 min: stopped. Batch 0 hangs at start-up as on draws 10401 / 10404 (hangs.md), with TBATCH = 1.2 ms of circuit time to simulate before the bench gives up; one x pulse (770 ps, ucond_br7 req1) before it | - | - | - | - |
| draws 10401, 10404 | FAIL (start-up hang, batch 0; hangs.md) | not run | | | |

With GATE_RUNTS=fail both PASS runs become FAIL (`RUNTS FAIL (41 net(s))` / 40; the verdict recomputed by the gate's
own code from the same run.log; GATE_RUNTS_CLASSES=steer alone fails them too, 6 nets). So the check flags this route on
every draw where the gate passed it, which is what it was asked to do. Where the pulses are (draw 10402, per net:
negctl_ipow_v1_s4_d10402.txt; every pulse: ipow_v1_s4_d10402_pulses.txt.gz):
- **At start-up (batch 0)**: x pulses on both steers' continue branches (ucond_br9 req1 581 ps, ucond_br7 req1 240 ps)
  and on what they feed -- the select is still x when the request arrives (hangs.md's start-up race; on this draw the
  x clears instead of sticking).
- **In every call with a loop (batches 2-14)**: the loop test races its steers. ucond_br9 (exit / continue of the main
  loop): 36 high runts on the exit branch (33-268 ps, median 99), 32 high + 32 low on the continue branch (a 74 ps
  rise, a 99 ps dip, then the real request); ucond_br7: 10 + 8 + 1 x. The runts then travel through everything they
  reach, because every LUT -- C-elements included -- passes a pulse (fid is transport; a state node that rejects a runt
  still emits it once, research/data/fid/runtc.md): the continue branch's link controller ulink_n_trueResult_12 (its
  latch enable) 64 + 1 x, merge0's grant / R0 / delay line / output link (62-65), the merge's acknowledge and the
  loop's data links ulink_n17__0/1/2 (56 each: their latch enables), the loop header mux umux1's join and request out
  (44), fork6 (44), and merge0's and merge1's arbiter state q (8 and 1, up to 496 ps). Every one of them was rejected
  at a state node by the model, so the answers stayed right: on silicon each is a pulse into a C-element, a latch
  enable or an arbiter, of 16-828 ps against loops of 0.2-0.9 ns -- exactly H_RUNT's unknown.
- These are the steers the rule flagged on this route when flow v1 shipped it (ca_4.txt: E -734..-1070 ps on
  ucond_br6..9 and A -719 on ucmpi2, the compare that drives their select). The runts appear at two of the four
  (br7, br9) on these draws; br6 and br8 none.

## 5. Positive controls: BOARD-QUEUE items 38-41 -- no pulse under 1 ns anywhere

Each rebuilt with its item's own command (BDC_AUTO=1, BDC_AUTO_REWRITES=1 for 39-41, its seed and sizes file) and
checked against the item's sdf md5: **38 81bbe268, 39 c56def07, 40 9585dde4, 41 3497ca67 -- all four identical**
(38 is subagent hangs' rebuild with this nextpnr, copied; 39-41 rebuilt here, lane2.sh LANE_NORUN=1). Gate with
GATE_RUNTS=1, each item's own gate vectors (ipow17, col18, c6419, xor19) and C oracle:

| route (sdf) | corner / draw | gate | pulses < 150 / 500 / 1000 ps, x | nets hit / watched | narrowest pulse of any width | longest kernel loop |
|---|---|---|---|---|---|---|
| 38 ipow v3 s2 (81bbe268) | draw:30201 | PASS 17/17 | 0 / 0 / 0, 0 | 0/192 | 4038 ps | - (first monitor version) |
| 38 ipow v3 s2 (81bbe268) | draw:88120 | PASS 17/17 | 0 / 0 / 0, 0 | 0/192 | 4138 ps | 737 ps |
| 38 ipow v3 s2 (81bbe268) | max | PASS 17/17 | 0 / 0 / 0, 0 | 0/192 | 7362 ps | 1329 ps |
| 38 ipow v3 s2 (81bbe268) | min | PASS 17/17 | 0 / 0 / 0, 0 | 0/192 | 2854 ps | 463 ps |
| 38 ipow v3 s2 (81bbe268) | worst | PASS 17/17 | 0 / 0 / 0, 0 | 0/192 | 3891 ps | - (first monitor version) |
| 39 collatz v3 s6 (c56def07) | draw:30601 | PASS 17/17 | 0 / 0 / 0, 0 | 0/159 | 4112 ps | 683 ps |
| 39 collatz v3 s6 (c56def07) | max | PASS 17/17 | 0 / 0 / 0, 0 | 0/159 | 7321 ps | 1202 ps |
| 39 collatz v3 s6 (c56def07) | worst | PASS 17/17 | 0 / 0 / 0, 0 | 0/159 | 3770 ps | 647 ps |
| 40 collatz64 v3 s5 (9585dde4) | worst | PASS 18/18 | 0 / 0 / 0, 0 | 0/155 | 4066 ps | 764 ps |
| 41 xorshift v3 s8 (3497ca67) | draw:30801 | PASS 19/19 | 0 / 0 / 0, 0 | 0/175 | 2262 ps | 751 ps |
| 41 xorshift v3 s8 (3497ca67) | max | PASS 19/19 | 0 / 0 / 0, 0 | 0/175 | 4024 ps | 1405 ps |
| 41 xorshift v3 s8 (3497ca67) | min | PASS 19/19 | 0 / 0 / 0, 0 | 0/175 | 1540 ps | 498 ps |
| 41 xorshift v3 s8 (3497ca67) | worst | PASS 19/19 | 0 / 0 / 0, 0 | 0/175 | 2118 ps | 748 ps |

Draws (chains / rest / CARRY4-F7F8-FF): 30201 0.288 / 0.248 / 0.830, 30601 0.287 / 0.306 / 0.984, 30801 0.231 /
0.233 / 0.320 (the first draw of each item's own judged set), 88120 0.2025 / 0.3097 / 0.992 (the rule's vertex,
section 6). "first monitor version": item 38's `worst` and draw 30201 ran before the 1 ps sampler fix and the loop
report (section 1); that version could only add pulses, so their zeros stand.

Every pulse found on these runs: **none narrower than 1 ns, on any watched net, on any run** (0 / 0 / 0, no x pulse).
The narrowest pulse of any width (a whole handshake phase) per class, over these runs (runts.txt `# class` lines):
steer >= 3.58 ns, join >= 3.58, link (latch enable) >= 3.05, chan >= 3.05, merge >= 2.71, mux >= 2.64 ns; the
operators' request lines ("op", not in the brief's list) >= 1.54 ns -- all of these minima on item 41 at FAST_MIN.
So on these four routes a strict check (GATE_RUNTS=fail, 1 ns) changes no verdict at any corner run, with a margin of
>= 1.5x (op lines at FAST_MIN; >= 2.6x in the brief's classes) between the fail threshold and the narrowest
legitimate phase. Not run for time: item 39 at FAST_MIN, item 40 at max / min / a draw (collatz64's gate takes ~25 min
here), item 41 needs no more. Items 38-41 would all pass a strict runt check on every run made.

## 6. A sample of the automatic flow's shipped routes (farm suite6, flow v6)

Rebuilt from research/data/suite/resume/suite6/<K>_<S>/sizes_final.vh (= the shipped iteration's sizes, checked), seed
S, BDC_AUTO=1 BDC_AUTO_REWRITES=1: **every rebuilt sdf equals the farm's** (column sdf). The rule re-run on each, as
auto_size.sh's rule() runs it (corner_audit CA_SIZERULE=1 at bands 0.20 and 0.31, merged; CA_FAST=1, byte-identical
on these kernels per research/data/loopfast): "rule rows" = its merged negative_sized.tsv, i.e. the NOT CLEAN rows
(report_<band>.txt and negative_sized.tsv per route in s6/). Gate at `worst` with GATE_RUNTS=1; and, on the three routes
whose rows include select races (rule E), at draw 88120 -- the gate's own draw nearest the rule's 0.31 vertex (chains
0.2025, rest 0.3097, CARRY4 / F7F8 / FF 0.9920; found by searching the draw generator, K 1-200000), where those rows
are most negative.

| route (sdf) | corner / draw | gate | pulses < 150 / 500 / 1000 ps, x | nets hit / watched | narrowest pulse of any width | longest kernel loop |
|---|---|---|---|---|---|---|
| collatz64_2 (d0e8210d, farm same) | worst | PASS 18/18 | 0 / 0 / 0, 0 | 0/155 | 4898 ps | 674 ps |
| collatz64_3 (5e15f4c3, farm same) | worst | PASS 18/18 | 0 / 0 / 0, 0 | 0/155 | 3905 ps | 636 ps |
| collatz_1 (f6c82582, farm same) | worst | PASS 17/17 | 0 / 0 / 0, 0 | 0/159 | 3615 ps | 670 ps |
| collatz_4 (d5a3f1f5, farm same) | worst | PASS 17/17 | 0 / 0 / 0, 0 | 0/159 | 3739 ps | 698 ps |
| ipow_1 (fcbfe8af, farm same) | draw:88120 | PASS 17/17 | 0 / 0 / 0, 0 | 0/192 | 3526 ps | 625 ps |
| ipow_1 (fcbfe8af, farm same) | worst | PASS 17/17 | 0 / 0 / 0, 0 | 0/192 | 3363 ps | 621 ps |
| ipow_2 (09da93d6, farm same) | worst | PASS 17/17 | 0 / 0 / 0, 0 | 0/192 | 3547 ps | 778 ps |
| xorshift_1 (e1415ef0, farm same) | worst | PASS 19/19 | 0 / 0 / 0, 0 | 0/175 | 2636 ps | 808 ps |
| xorshift_2 (55a25d4e, farm same) | draw:88120 | PASS 19/19 | 0 / 0 / 0, 0 | 0/175 | 2290 ps | 885 ps |
| xorshift_2 (55a25d4e, farm same) | worst | PASS 19/19 | 0 / 0 / 0, 0 | 0/175 | 2150 ps | 825 ps |
| xorshift_6 (290f3a44, farm same) | draw:88120 | PASS 19/19 | 0 / 0 / 0, 0 | 0/175 | 1860 ps | 646 ps |
| xorshift_6 (290f3a44, farm same) | worst | PASS 19/19 | 0 / 0 / 0, 0 | 0/175 | 1989 ps | 702 ps |

**Coincidence with the rule.** None of these routes has a pulse under 1 ns at `worst`, including the five NOT CLEAN
ones; the rule's rows there are 8 to 208 ps negative at its own corners (0.20 / 0.31) with its guards (E: 0.97 x
request vs 1.03 x select), against the negative control's -734..-1070 ps (rule E) and -719 ps (A) when v1 shipped it.
Per route (runs/s6_rows.txt; the rows themselves runs/s6_negative_sized.txt):
- ipow seed 1 (NOT CLEAN): rule E at the loop steers ucond_br8 -208, ucond_br9 -72, ucond_br6 -27 ps and A'j -46 at
  ucmpi2 (their select's compare), all at the 0.31 corner. The same kind of rows as the negative control's, ~5-40x
  smaller. No pulse at `worst`, none at draw 88120 (the rule's vertex): at the gate's delays the select still settles
  before the request reaches these steers.
- xorshift seed 2 (NOT CLEAN): rule E -143 / -200 ps at the loop mux's select (umux1). No pulse at `worst` or 88120.
- xorshift seed 6 (NOT CLEAN): rule E -18 / -85 at umux1.uj0 and H -155 / -172 at ulink_n_falseResult_1 (a latch's
  hold, not a select). No pulse at `worst` or 88120.
- collatz seed 1 (NOT CLEAN): H -15 / -27 at ulink_n7 (hold). collatz64 seed 2 (NOT CLEAN): A -8 / -45 at
  ucontrol_merge1 (a merge's data). No pulse at `worst`. Rules H and A are data races, not select races: a runt
  monitor on handshake nets cannot see them by construction (the data net is not watched; a late data bit at a latch
  makes a wrong value, not a pulse on a request).
- The four CLEAN routes (ipow 2, collatz 4, collatz64 3, xorshift 1): no pulse.

So on this sample the runt check and the rule's NOT CLEAN rows do not coincide: the rows are small (<= 208 ps) and at
the rule's own corner with its 3 % guards, and none became a pulse at the gate's corners; the one route where the rule's
rows were large (ipow v1 s4: E -734..-1070, A -719) is the one with runts on every passing draw. A NOT CLEAN route
is not a racing route on these runs, and the one route with runts was NOT CLEAN with rows 4-50x larger. Sample: 9 of suite6's 32 routes
(2-3 per kernel; seeds chosen to have both kinds), one corner each plus the vertex draw on three; ipow 5, collatz 2,
collatz64 5 were dropped for time (collatz64's gate takes ~25 min here).

## 7. What this does not show

- **Silicon.** The check measures pulses in the gate's model. Whether a 16-600 ps pulse into a LUT C-element, a latch
  enable or an arbiter is captured on this die is H_RUNT's question (BOARD-QUEUE item 2, not yet run). The check makes
  the gate say where such pulses are; it does not say they are harmful, and no lower cutoff is claimed safe.
- **Coverage of the delay space.** Positive controls: one run per corner (max / min / worst) and one or two draws per
  item; suite6 routes: the `worst` corner (and one draw at the rule's own vertex where said). A race whose margin is
  positive at these corners and negative at another draw is not excluded (ipow v1 s4's runts appear on every draw it
  was run at, but its start-up hang only on some).
- **Which nets.** Only the kernel's handshake outputs (classes in section 1). Data nets are not watched: a glitch on
  a select's DATA bit (the compare output on ipow v1 s4) is seen only through the steer it feeds. The bench's clocked
  side is not watched.
- **The x pulses** count as pulses; at start-up they come from the X model of unreset latches (SIM-VS-BOARD row 6),
  where silicon has a defined (unknown) value.
- **The pulse is measured at its driver.** Each reader sees it after its own wire, rise and fall arcs differ by tens
  of ps, so the width at a reader's pin may differ from the driver's by that much.
- **n.** One route per item; one draw (or corner) per route for most cells of the tables; one negative control route
  (two draws where the gate passes). The monitor's own correctness: one VCD cross-check (1768 pulses, identical).

## 8. Files

- `cells/gls/ps/gen_runt_mon.py` (new): the monitor generator (ROUTED_JSON NETS_MAP OUT.v; writes runt_mon.v and
  runt_nets.tsv). `cells/gls/ps/build_ps.sh`: `PS_RUNTS=1` (opt-in) compiles it in.
- `research/tools/eventgraph/bench_gate.sh`: `GATE_RUNTS=1|fail`, `GATE_RUNTS_T` (default 150,500,1000; third 0 = loop
  threshold), `GATE_RUNTS_CLASSES`; the verdict field; runts.txt. Unset: byte-identical (checked on four logs).
- This directory: README.md; cost.sh (the four-way cost run) and cost_ipow4_d10402.txt; vcd_pulses.py (the monitor
  against a VCD); s6_route.sh (a suite6 route rebuilt, re-ruled and gated); collect.py (the tables); runs/runs.tsv
  (every run), runs/s6_rows.txt and runs/s6_negative_sized.txt (the rule's rows per suite6 route), runs/runts_*.txt
  (per net, every run with a pulse); negctl_ipow_v1_s4_d10402.txt (the negative control per net, draw 10402),
  ipow_v1_s4_d10402_pulses.txt.gz (its 1768 pulses), runt_nets_ipow_v1_s4.tsv (the 192 watched nets of ipow with
  their loops and readers' loops).

To rerun a cell of the tables: `GATE_RUNTS=1 research/tools/eventgraph/bench_gate.sh HW DESIGN WORK VEC EXP COL` on the
route rebuilt with its item's command (BOARD-QUEUE 38-41) or `RUNS=... research/data/suite/steerrunt/s6_route.sh K S
worst draw:88120`. Not run (for time): item 39 at min, item 40 at max / min / a draw, suite6 ipow 5 / collatz 2 /
collatz64 5, and the negative control at `worst` beyond batch 0.

