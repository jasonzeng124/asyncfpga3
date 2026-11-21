# BDC_AUTO=1: one switch, no instance named (PROGRAM "General first", owner 2026-11-17)

Subagent A, 2026-11-17. Code: `bdc/auto.py` (rules + the proven-rewrite step), `bdc/emit.py` (`_auto_apply`, read only
when `BDC_AUTO=1`), `cells/hw/build_bench.sh` (the MLIR rewrite step, only when `BDC_AUTO=1`),
`research/tools/fifteen/lane2.sh` + `eval_task.sh` (SIZES_VH `default` = the flow's own sizing; any other value is
unchanged). Sizing is NOT touched here (subagent B). AUTO builds use BD_SIZES=none (every matched delay at emit.py's
estimate), the sizing of the all-kernel default table (subagent C, `research/data/alltable/run_default.sh`), because
build_bench.sh's own MODE=tighten does not finish: its rule-E converge loop stopped "NOT CONVERGING" on xorshift seed 1
(at the new ucontrol_merge0_rlink / ulink_n11__0_folink select margins) and on collatz seed 1 (at ulink_n14__1, a link
the knob-free build has too), 20:47-20:57 UTC.

## 1. Every knob, and what it is

G = general (no instance named, a rule for every kernel); I = names an instance (one kernel's recipe); P = a
parameter / measurement knob. "Check" = what shows it is safe beyond the gate on the builds that used it.

| knob | what it does | G/I | check / proof | what it bought (board-queue item) | in AUTO |
|---|---|---|---|---|---|
| BDC_LINK_FASTFALL=1 | RFAST on every single-stage bd_link request, FASTFALL on 2-input mux delays | G | tighten.py rule F (drain); refuses memory kernels | xorshift / ipow / collatz +7-12% (items 13-15) | **on** (off where the func has a memory port) |
| BDC_CONST_DATA=1 | a fused region reads a forked constant as a literal (channel kept) | G | same function by construction; test_const_data.py | collatz 14.6-16.3 ns of barrel shifter per iteration (item 9-10); ipow 1.26x soak (item 10, withdrawn for its sizes, not the knob) | **on** |
| BDC_RING_COUNT_OLINKS=1 | ring floor (3 stages per simple cycle) counts the merge olink / rlink storage | G | the floor still holds (it only counts real storage) | xorshift lever 2, ~-1 ns (counter pipe 3 -> 1) | **on** |
| BDC_MERGE_OUT_LINK=ucontrol_merge0 | bd_link between an arbitrated merge and its output fork | I | gate 24/24 (items 13-21), rules A/E/H | xorshift 1.34x with p8+FF (item 14), ipow 1.18x, collatz 1.13x | **rule M** |
| BDC_MERGE_RES_LINK=ucontrol_merge0 | bd_link on that fork's result branch | I | gate (items 17-21) | xorshift 30.0 -> 23.4, collatz 1.20x, ipow 1.17x, collatz64 1.19x (items 18-21) | **rule M** |
| BDC_FORK_OUT_LINK=n11__0 | bd_link on one fork output | I | gate (item 17) | xorshift lever 3: 21.7 -> 20.6 | **rule F** |
| BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 | one link a bd_pipe of N | I | gate (items 11, 14) | xorshift x0.5: mo 38.1 -> p8mo 31.8 (second_latch) | **left out** (below) |
| BDC_NO_LINK=ulink_... | drop a rule-1 (measurability) link | I | static rule E failed on xorshift (lever 5 ON HOLD); collatz item 22 / c64 item 24 | xorshift -1.9 ns (held), collatz/c64 items 22/24 | left out (static check fails on xorshift; pre_eq2 makes the collatz one moot) |
| BDC_MERGE_RES_DEPTH, BDC_FORK_OUT_FASTFALL | rlink as a pipe / RFAST on fork links | P | lever 9 tests | nothing adopted | off |
| BDC_SPEC_INC=inst:k:n | speculative short line on an addi | I | spec_select.py | xorshift +0.33 ns (fxds): no | off |
| BDC_SELECT_PAD / ACK_PAD / STAGE_PAD / RING_PAD / SLACK_STAGES / SELECT_PADS | placeholder delays, depth sweeps, per-route select pads | P | sizes rules replace them | - | defaults |
| BDC_OP_FUSION / FORK_FUSION / MAX_FUSE_NODES / FASTFALL(compute) | region fusion, compute fast fall | G | default ON already | - | defaults |
| BDC_PROBE, BDC_MEM_NAIVE_ACK | probe ports / a negative control | P | - | - | off |
| pre_dec.py (MLIR) | xorshift: `i+1 < n` -> `i < n-1` | I (string-matches xorshift's SSA names) | **formal A6** (Lean, every input) | xorshift ~-3.5 ns latency, item 27 | **applied when its output is a proven file** |
| pre_eq2.py (MLIR) | collatz/64: `n' == 1` -> `n == 2` | I (collatz shape; false at w = 2) | **formal A6** (every 32/64-bit n) | collatz 41.2 -> 35.8 (item 25), c64 45.2 -> 36.2 (item 26) | **same** |
| BDC_FE_EXITCOND=1 (frontend.sh) | LLVM indvars rewrites `i+1 < n` to `!=` | G | LLVM's own proof | xorshift only changes (journal 2026-11-14); never built | not here: the frontend runs on the owner's machine |
| BD_DSP=1 | multiplies on DSP48 | G | - | every recipe | on (lane) |
| BD_SIZES=<file> x0.5 / x0.55 / x0.70 / x0.75, select links at 3, hold pads | per-kernel sizes | I | draws / rules | most of 2026-11-12..17's gains | **not here** (subagent B); default flow |
| BD_RLOC / BD_PLACE_WEIGHT(_CELLS) | placement | P/I | - | mixed by seed (levers 4, 10) | off |
| BD_SKEW_AND_JOIN=1 | static check with C-element joins (an audit option, not a design knob) | G | - | - | audit side |

## 2. The rules (what the event-graph search actually found)

The search (`research/tools/eventgraph/search.py --new-knobs`) was free to put a latch on any fork output, any merge
output and +1 depth on any link. On the four kernels it chose:

- **Rule M -- every loop-header arbitrated control_merge gets an output link and a result link.** ucontrol_merge0 is,
  on all four kernels, the 2-input control_merge on a cycle of the node graph (entry + loop-back). The arbiter's
  output cannot return to zero before its granted input, and its output fork's acknowledge waits for the loop steer,
  which waits for the loop test. Implemented: `loop_header_merges` = every control_merge with 2+ inputs inside a
  non-trivial SCC. gcd gets 5, isprime 4 (nested loops; nobody tuned these).
- **Rule F -- latch a fork output that is read directly as a loop steer's data while a sibling output computes that
  steer's condition** (inside one iteration: forward, not through mux / merge / control_merge / cond_br). The fork's
  acknowledge otherwise waits for the steer's join, i.e. for the test computed from its own other branch. Finds
  exactly n11__0 on xorshift; nothing on collatz / collatz64 (pre_eq2 compares fork3 directly but the steer reads
  the update); **n31__0 on ipow** (e>>1 to its steer and to `e > 0`, the same shape), which the hand recipe lacks:
  the graph of item 29's route (ip29_19) predicts +0 ps for it (ipow is at its no-polarity-change floor; it removes the
  polarity changes of the next cycles at 33.1 ns) -- a wire cost is the risk (p12).
- **Ring floor counting** follows from M (it is storage). On collatz and ipow it turns the control ring's back-edge
  bd_pipe N=3 (ulink_n_falseResult_7 / ulink_n_trueResult_12, 2.8 ns on ipow's critical cycle) into one RFAST link:
  the same change as xorshift's lever 2, never applied to them by hand.
- **CONST_DATA** on ipow turns `e >>> e1_data` (a 32-bit barrel shifter, ushrsi0 = 10.3 ns of ip29_19's 35.5 ns
  cycle) into `>>> 32'h1`; the hand recipe after item 10 did not carry it.
- **Left out: BDC_LINK_DEPTHS=ulink_n_trueResult_8=2.** Structurally it is "2 stages on the back edge of a loop value
  that does not feed the loop test" (xorshift's x). The same rule would hit collatz's ulink_n_falseResult_7 and the
  graph of item 31's route (c28a_20) says +675 ps there (+0 on collatz64's c64s3_10; ipow's not periodic). One kernel
  justifies it, so per PROGRAM it stays out; the cost on xorshift is measured below, not assumed.
- **Proven MLIR rewrites:** `bdc/auto.py` runs pre_dec.py and pre_eq2.py on every kernel and keeps an output only if
  its md5 is one of formal A6's proven files. Honest scope: each matcher fits one kernel, so this is "every rewrite
  with a proof is applied where it applies", not a general pass. A general one: LLVM's `!=` exit test
  (BDC_FE_EXITCOND, owner side) for `i+1 < n`; the n == 2 kind needs a preimage proof per update function.
- **Not done: the search inside the flow.** `storage_pass.sh` already does build -> graph -> search -> rebuild; making
  it AUTO's second stage (BDC_AUTO=2) costs 2 routes + 1 full-stack run per kernel and would find kernel-specific
  depths like p8 by measurement instead of by rule.

Unset, every emitted file is byte-identical: `cmp` of `bdc/emit.py` output (with and without top) before and after,
on all 9 fixtures (single_loop fails identically before and after: store accessor not implemented), plus the four
hand recipes' knob sets on their MLIR (xorshift_predec, collatz/64_preeq2, ipow): 36 / 36 identical.

## 3. Prediction (written before any AUTO build), event-graph P, itercost stack

**3a. With BD_SIZES=none (what was built; written 20:59 UTC, after the tighten flow failed and before any route).**
At emit.py's estimates the delay lines dominate, and the estimate does not shrink for a constant operand (ushrsi0 stays
32 elements with CONST_DATA), so CONST_DATA buys nothing here. Gains over the knob-free default at the same sizes:
storage + fast fall (1.13-1.6x at hand sizes, less here where the chains are longer) and the rewrites taking the
update off the loop test (xorshift: uaddi0's 24-element estimate leaves the counter ring; collatz/64: the select +
update leave the exit test). Predicted default / AUTO period ratio: xorshift 1.30 (1.15-1.5), collatz 1.30 (1.1-1.5),
collatz64 1.25 (1.1-1.4), ipow 1.10 (1.0-1.25). Against the hand recipes AUTO is far slower here: sizes, not structure.

**3c. Structure only: AUTO at the hand recipe's own sizes file and board seed (written 21:28 UTC, before those
builds).** Same seed, same sizes, so the difference is the rules vs the hand knobs (plus the re-placement the changed
netlist causes; new instances take emit.py's placeholder, ipow's ushrsi0 keeps its barrel-shifter size, so CONST_DATA
shows nothing there). Hand route (graph): xorshift s27 18.71, collatz s20 21.27, ipow s19 35.54, collatz64 s22 31.32.
Predicted AUTO: xorshift 19.7 (+1: no 2-stage x back edge), collatz 20.5 (-0.8: control back-edge pipe 3 -> 1),
ipow 34.0 (-1.5 the same; rule F 0), collatz64 30.5 (-0.8). Seed scatter is ~1 ns, so only xorshift's sign and ipow's
are expected to be readable from one route.

**3b. Had the default tighten flow run (written 20:45, kept for the farm's tighten half if sizing is fixed):**

The hand recipes ran on hand sizes (x0.5-x0.75 of the static rules); AUTO runs on the default flow's sizes, which are
~1.3-2x longer on the matched delays of the cycle. So the AUTO-vs-hand gap below is mostly sizing (B's work).

| kernel | hand recipe (item, P) | AUTO structure vs hand | AUTO predicted (range) |
|---|---:|---|---:|
| xorshift | 33: 18.9 (fxa_27 18.7) | - p8, + CONST_DATA (bb0 only); sizes ~x2 on ~10 ns of chain on the cycle | 28 (25-31) |
| collatz | 31: 21.5 (c28a_20 21.3) | + control back-edge pipe 3 -> 1 (-0.5..-1.5) | 26 (23-30) |
| ipow | 29: 36.2 (ip29_19 35.5) | + CONST_DATA shift (-6..-8), pipe 3 -> 1 (-1.5), rule F (0, wire risk) | 30 (26-34) |
| collatz64 | 32: 31.4 (c64s3_10 34.9) | + pipe 3 -> 1 | 36 (32-40) |
