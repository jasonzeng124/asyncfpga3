# The token floor: how much storage a loop needs to move (ringfloor, 2026-11-18)

**Status.** bdc/emit.py has a new correctness rule, on by default in both flows (`token_floor()`, after
`ring_depths()`; `BDC_TOKEN_FLOOR=0` turns it off, for negative controls only). It fixes the four deadlocks the suite
found (kernels/SUITE.md findings 1 and 2): quadrec in both flows, and lfsrfind, nested and nest3 in the default flow.
Every other fixture emits byte-identical Verilog. Routed: quadrec on 4 seeds x 2 flows, the suite's smoke check (bdc's
generous delay estimates, gate at the worst corner on the bits-decoded netlist): 8 / 8 PASS 10/10 on EQUIVALENT
bitstreams, plus 8 / 8 model draws on the BDC_AUTO routes. The brief's full automatic path (suite_one.sh, with the
sizing loop) did NOT fit the time box and was stopped unjudged (see "Routed").

## The condition

Every cycle of the loop's handshake marked graph has to hold a token. In terms of the dataflow graph, with *stages*
counted on channels (a bd_link is 1, a bd_pipe N, a merge olink / rlink and a fork output link 1 each) and *tokens*
counted as back edges (a data input of a mux, or an input of a merge / control_merge, fed from the same or a later basic
block, on a cycle):

1. **a directed cycle that threads T back edges needs at least 2T + 1 stages** (two per token, plus one to move
   into). T = 1 is the existing `RING_MIN_STAGES = 3`;
2. **two paths from one fork to one join, where one (Q) crosses K more back edges than the other, need at least 2K
   stages on Q** between the fork and the join (the stage after the join is the free one).

Both are instances of one condition: every closed walk that goes forward along some channels and backward along
others, turning back at joins and forks, holds a token, where a channel walked forward contributes
`stages - 2 x tokens`, a channel walked backward `2 x tokens`, and each turn at a join `+1`; the walk is short when the
sum is <= 0. Condition 1 is the all-forward walk; condition 2 is forward along Q, back along P.

The suite subagent's proposal ("a cycle that threads k back edges needs 2k + 1 stages") is condition 1 alone. **It is
necessary and not sufficient**: quadrec with trueResult_14 at 7 stages and nothing else changed meets 2k + 1 on every
cycle (ring_tokens.py +1) and still deadlocks at vector 2 in simcheck. Condition 2 is what it violates, and condition 2
is also the whole mechanism of finding 2 (lfsrfind, nested, nest3), which no cycle count sees (ring_tokens.py read +1
on all three).

## Derivation

**Cells.** A storage stage is a Muller half buffer, `c = C(req_in, ~c_next)` (cells/rtl/bd_link.v; a bd_pipe is N of
them; the merge olink / rlink and the fork output link are bd_links). Nothing else on a ring stores a token: a join
(bd_join, a cond_br's condition with its data, a mux's select with its selected data -- bd_mux.v
`j1 = C(y_req, ctl_req . s)` -- and a compute cell's operands) is a C-element on the requests with the acknowledge
broadcast back; a fork (bd_fork) is a C-element on the acknowledges; a steer is two AND gates; the arbitrated merge
passes its granted input. So a stage t rises when every stage feeding it (through those cells) has risen and every stage
it feeds has fallen, and falls in the dual case. (The C-element joins and forks hold state, but in every reachable state
"all inputs agree" is exactly when they switch, so they add arcs, not tokens.)

**Marked graph.** While a loop iterates (every header mux takes its back edge, every loop steer continues), that is a
marked graph on the stage transitions. For each stage edge s -> t (t fed from s through rendezvous cells only) there are
four arcs: `s+ -> t+`, `s- -> t-` (data forward) and `t+ -> s-`, `t- -> s+` (the acknowledge back). In any state
exactly one of the four holds a token: (c_s, c_t) = (1, 0), (0, 1), (1, 1), (0, 0) respectively. A marked graph is live
iff every cycle holds a token, and a cycle's token count never changes, so it can be read off one state.

**Counting.** Read the marking at an iteration boundary: each loop-carried value resting in a stage of its back edge
(that stage high, its neighbours low), every other stage low. Per stage edge exactly one arc holds a token: an
acknowledge arc where the two stages agree, a data arc where they differ, and a resting value makes exactly the two
stage edges around it differ. A marked-graph cycle is a closed walk over stage edges, each taken with the data (the
cycle then uses that edge's acknowledge arcs: one token per stage, minus two per value resting there) or against it
(its data arcs: two per resting value), taken twice round where the polarity requires. With d = the back edges a stage
edge crosses (0 or 1) its token count is

    sum over stage edges walked with the data of (1 - 2d)  +  sum over stage edges walked against it of 2d .

- A directed cycle of S stages with T back edges, walked with the data: `S - 2T >= 1`, i.e. S >= 2T + 1; against
  it: `2T >= 1` (it has a token at all). For a ring of N Muller stages this is the textbook result: W = 2T wavefronts on
  N boundaries move iff 0 < W < N.
- Fork F, join J, paths P and Q between them, Q crossing K more back edges. At stage level the walk turns at u (the
  last stage before F, shared) and v (the first stage after J, shared): forward along Q from u to v is
  `(L_Q + 1) - 2 T_Q`, backward along P from v to u is `2 T_P`; so `L_Q + 1 - 2K >= 1`, i.e. **L_Q >= 2K** stages
  strictly between F and J. The shared piece u -> F contributes 0 (walked both ways), the shared piece J -> v
  contributes exactly the one stage v: that is the `+1` at a join turn in the node-level walk.

**Modes.** The cells that choose (a mux's data inputs, a merge's or control_merge's inputs, a cond_br's two branches)
belong to different marked graphs in different modes. The walk never turns between two of them (a turn is only between
inputs that are joined, or outputs that leave together: a fork's, a control_merge's result and index), and never walks
a loop's entry channels (the non-back-edge inputs of its header muxes / merges / control_merges) or its exit channels
(the other branch of every steer on the loop's condition; the condition is found from the steer that feeds a back edge,
traced back through forks). So each loop is seen iterating, and an inner loop either iterating or skipped (its guard's
other branch), never passed through in one trip; and a back edge only counts on a cycle (cmpchain, loop-free, has a mux
fed from its own basic block). Memory ops are walked through but never turned at (not modelled).

**Worked example: quadrec** (`d <- t(a, b, c, d); c <- d; b <- c; a <- b`, one basic block). The loop-condition fork
(fork9) feeds all seven steers. d -> c is cond_br13 -> trueResult_20 -> mux4 -> fork5 -> cond_br12, and cond_br12's
condition comes straight from fork9: a fork-join pair with K = 1, so trueResult_20 needs 2 stages. Same for c -> b
(trueResult_18), b -> a (trueResult_16) and t -> d (trueResult_14, already 2 from the old floor). With those, the
four-token ring has 2 + 2 + 2 + 2 + 1 (the link in front of the adder) = 9 = 2 x 4 + 1 stages: on quadrec condition 2
implies condition 1. Before the change it had 6 stages for 4 tokens (the simple cycle is -2; the -4 ring_tokens.py
printed is Floyd-Warshall's d[i][i] around a negative cycle, which can go round twice).

**Trace of the d -> c deadlock** (config C below: trueResult_14 = 3, _16 = 2, _18 = 2, _20 = 1; every directed cycle
at 2T + 1; `deadlock_traces.txt`): fork9 is in its return to zero (its request n39 low, acknowledge still high) because
cond_br13's acknowledge (n40__2) is still high; that is because trueResult_20's one stage holds c_{j+1} (request high,
not acknowledged) and cannot empty until mux4's output is taken; mux4 has fired (n24 req high) but fork5 cannot
complete, because cond_br12 (n25__0 req high) waits for the next condition token (n40__3 req low), which fork9 cannot
send until its return to zero completes.

## The change

`bdc/emit.py`:
- `token_graph(func, linked, depth, exclude)`: the walk graph. A state is (channel, direction); forward costs
  `stages - 2 x tokens`, backward `2 x tokens`, a join turn `+1`, a fork turn 0, passing forward through a
  control_merge with a merge olink `+1` (the olink is one stage between the arbiter and its result/index fork, shared
  by both). Stages are read the way emit lowers them: the link depth, plus a fork output link, plus a merge result link
  (MERGE_RES_DEPTH), always counted (they are physical storage whatever BDC_RING_COUNT_OLINKS says).
- `short_walk(chans, out)`: queue Bellman-Ford on `weight x (states + 1) - 1`, under which a simple cycle is negative
  iff its count is <= 0; returns the walk.
- `token_floor(func, linked, depth, exclude, forbid)`: while a short walk exists, add one stage to a link it walks
  forward (a back edge first, then the link with the fewest stages, then by name); if it walks no link forward, put a
  new 1-stage link on one of its forward channels (same order; never on a fused-away, memory-absorbed or BDC_NO_LINK
  channel). Runs in `Emitter.__init__` right after `ring_depths()`, before the ring pad, slack stages and
  BDC_LINK_DEPTHS (which may still only raise depth; its floor now includes this one). Prints one stderr line per stage
  added (`emit: token floor: ...`).
- `BDC_TOKEN_FLOOR=0` turns it off (negative controls only).

`research/tools/suite/ring_tokens.py`: a second view, the walk condition above, on the design bdc emits (with
`BDC_TOKEN_FLOOR=0`, on the design without the floor); exit 1 when either view finds a short cycle or walk.

**Why the default flow too.** It is a liveness rule of the same kind as RING_MIN_STAGES, not a speed choice: without
it the default flow deadlocks on quadrec, lfsrfind, nested and nest3 in simulation, and the suite's routes hang the same
way. It adds nothing where every walk already holds a token, so it changes no other fixture's output. Where it acts it
costs latency (quadrec: 3 more stages on its ring; lfsrfind: one link on its control back edge).

## Checks

**1. Output unchanged where the floor already holds** (`ringfloor/fixtures_cmp.txt`). Every fixture in
build/frontend (104), emitted before (start ecc62e17e) and after, `--no-top`, default / BDC_AUTO=1 /
BDC_AUTO=1 after auto.py's proven rewrites: 90 byte-identical, 216 refused by bdc before and after with the same error
(memory, lsq, divui ...), **6 changed**: quadrec (all three; trueResult_16/18/20 -> 2 stages), and in the default flow
only lfsrfind (new 1-stage link on trueResult_14, cond_br9 -> control_merge0), nested (falseResult_17 -> 2) and
nest3 (falseResult_17 and falseResult_33 -> 2). In BDC_AUTO lfsrfind / nested / nest3 are unchanged: rule M's merge
olink already gives their walks a token.

**2. quadrec simcheck** (`--c-oracle`, kernels/quadrec/vec.hex, 10 vectors, expected values from the C):
PASS 10/10 default and BDC_AUTO (was: deadlock at vector 2, n = 4, in both).
**Negative controls** (BDC_TOKEN_FLOOR=0, BDC_LINK_DEPTHS = the floor minus one stage): removing the added stage from
trueResult_16, _18 or _20, one at a time, deadlocks at vector 2: **6 / 6** (3 links x 2 flows). With BDC_TOKEN_FLOOR=0
and BDC_LINK_DEPTHS = exactly the floor's depths the Verilog is byte-identical to the floor's (both flows), so the
controls differ from the shipped design by that one stage only.

**3. The condition against simulation** (`ringfloor/validation.txt`): 34 configurations of quadrec, lfsrfind,
nested, nest3 (hand depths, the floor, floor minus one, rule M's olink alone, its result link alone, rule F alone,
BDC_AUTO). The walk view says short on 19 and live on 15; simcheck deadlocks on exactly the 19 and passes the 15
(28 simcheck results from this work; 6 rows rely on the suite's recorded runs only: rule M's olink alone on lfsrfind,
nested, nest3, rule F alone on lfsrfind and nest3, the suite's all-four-at-3 fix of quadrec). The directed-cycle view
alone (ring_tokens' first view, the suite's proposal) calls 11 of the 19 deadlocks live. Two of the 34 were
predictions made before running them: rule M's result link alone fixes nested (PASS 11/11) and nest3 (PASS 12/12);
a third reproduces the suite's record (it does not fix lfsrfind: deadlock at vector 1).

**4. No regression** (`ringfloor/simcheck_regress.txt`): simcheck --c-oracle on all 14 suite kernels with a vec.hex,
both flows: 28 / 28 PASS. The 24 (kernel, flow) pairs whose Verilog did not change reproduce the suite's recorded
verdict and `$finish` time to the picosecond; the 4 that were deadlocks pass every vector (quadrec 10/10 x 2,
lfsrfind 10/10, nest3 12/12, nested 11/11, default flow). The six REFS-path kernels (gcd, ipow, collatz, collatz64,
isprime, xorshift) emit byte-identical Verilog in all three flows (check 1), so their simcheck is unchanged by
construction (not re-run).

**5. Finding 2 (default flow: lfsrfind, nested, nest3) is the same argument.** Each has a short walk (count 0) that
runs through a loop-header control_merge and a back edge with 0 stages, against a fork-join pair:
- nested: fork6 (the inner loop's guard) -> cond_br13 -> **the skip branch falseResult_17 (1 stage)** -> mux12, joined
  with mux12's select from control_merge2's index; control_merge2's result -> cond_br25 -> the outer back edge
  trueResult_44 (0 stages) -> control_merge0 -> fork5 -> constant3 -> cmpi1 -> fork6. It exists only when the inner
  loop is skipped (0 trips) after the outer back edge has been used once -- exactly the suite's hang condition
  ((2, 0) and (5, 0) hang, (1, 0) and (2, 1) pass). The VCD of (5, 0) (`deadlock_traces.txt`) shows that walk stuck:
  cond_br13 offers the next value (falseResult_17_u req high) into the skip link, whose stage is still returning to
  zero at mux12 (req low, ack high); mux12 waits for its select's return to zero (n49__3 req and ack high), which
  waits for control_merge2's fork, whose result (n_result_34) waits for cond_br25, whose back edge into control_merge0
  (n_trueResult_44 req high, not acknowledged) waits for control_merge0's output (n_result) to be taken by fork5,
  which waits for constant3 -> cmpi1 -> fork6 -> cond_br13: the start.
- nest3: the same walk one level down (falseResult_33, then falseResult_17); each of the two stages the floor adds is
  needed (without falseResult_17's: deadlock at vector 6; without falseResult_33's: vector 1).
- lfsrfind: fork3 (the key) -> cond_br4 -> merge0 -> cond_br8, joined with the loop test's fork11 -> cond_br9 -> the
  back edge trueResult_14 (0 stages, unlinked) -> control_merge0 -> result -> cond_br3, joined with fork5 (x == k)
  <- cmpi0 <- the link n21 (walked backward) <- extui2 <- fork3. The walk walks no link forward, so the floor adds one
  (1 stage on trueResult_14). Without it: deadlock at vector 1.
Why rule M fixed all three: its olink is a stage inside the header control_merge, on the forward part of every one of
these walks. Why the result link alone fixes nested / nest3 but not lfsrfind, and why rule F alone fixes neither
lfsrfind nor nest3: the walk view predicts each of these (validation.txt).

**6. Routed** -- see "Routed": 8 / 8 routes PASS 10/10 (4 seeds x 2 flows, EQUIVALENT), 8 / 8 draws PASS.

**How the walk graph was got right (development record).** The first version confined walks to one strongly connected
component of the node graph (to keep loops' entry and exit modes apart). Config C (trueResult_14 = 3, _16 = 2, _18 = 2,
_20 = 1) passed that check and deadlocked in simcheck: quadrec's rotation and its loop-control ring are separate SCCs,
joined one way by fork9, and the d -> c walk crosses between them. The floor had still added trueResult_20's stage, for
the cycle count. Replaced by "no loop entry or exit channels"; that first flagged cmpchain (a mux fed from its own basic
block counted as a back edge) and isprime (a walk taking cond_br34's continue branch and cond_br33's exit branch, both
on fork30's condition), both false: hence back edges only on cycles, and exits found by the condition's root. The two
versions emit the same Verilog on every fixture (checked). The stopped full-path routes below were built from the
first commit, the smoke routes from the final code.

## Routed

**The brief's path did not fit the time box.** `suite_one.sh quadrec S 2 4` (BDC_AUTO, the auto_size sizing loop,
MAXIT 4, then the bits checks and 2 draws) was started on seeds 1 and 2 (PNR_TIMEOUT=3600, CA_JOBS=2): one sizing
iteration took ~30 min on this node (corner_audit's per-line sensitivity: 151 lines x ~17 s on 2 workers), so a seed
needs ~3 h; at 03:34 UTC seed 1 was building iteration 3 and seed 2 was in iteration 2's audit, and both were stopped
(`ringfloor/fullpath_partial.txt`: each had built 3 routes, all ffmux-clean where logged; none judged: no draw ran).
Seeds 3 and 4 were never started.

**Instead: the suite's routed smoke check, 4 seeds x 2 flows** (`ringfloor/routed_smoke.txt`; the check the suite's
routed column used, `research/tools/suite/smoke.sh`): build_bench.sh at bdc's own generous delay estimates
(BD_SIZES=none, no sizing loop), `--freq 83`, then bench_gate.sh at the worst corner on the netlist decoded from the
bitstream, 2 runs per vector, expected values from the C. Routes built from the final bdc in private trees; each
route's kernel has the floor's 2-stage pipes on trueResult_14/16/18/20.

| flow | seed 1 | seed 2 | seed 3 | seed 4 |
|---|---|---|---|---|
| default | PASS 10/10, EQ | PASS 10/10, EQ | PASS 10/10, EQ | PASS 10/10, EQ |
| BDC_AUTO | PASS 10/10, EQ | PASS 10/10, EQ | PASS 10/10, EQ | PASS 10/10, EQ |

8 / 8 routes return every right answer at the worst corner, both runs of each vector agreeing; all 8 bitstreams
EQUIVALENT (fasm_equiv), ffmux_scan clean on all 8. Before the change the suite's seed-1 routes hung at vector 2 in
both flows (default on an EQUIVALENT bitstream). nextpnr 9c732bc6303458df, toolchain.sh ok before both batches of
builds.

**Plus 2 draws of the delay model on each BDC_AUTO route** (`ringfloor/routed_draws.txt`; bench_gate.sh draw:K,
K = 10000 + 100 x seed + j as suite_one numbers them, prjxray SDF reused from the route's gate): **8 / 8 PASS 10/10**,
all on the EQUIVALENT bitstreams; the draws' bands span chains 0.205-0.303, rest 0.205-0.287, CARRY4 / F7F8 / FF
0.375-0.984. So on 4 seeds the BDC_AUTO routes pass suite_one.sh's steps 2 and 3 (bits checks, draws), on routes built
at bdc's generous estimates rather than at the sizing loop's sizes.

## What this does NOT show

- **Not a proof of liveness.** It is a model: half-buffer stages and C-element rendezvous cells (as the cells are
  written), the arbitrated merge as a pass-through of its granted input, memory ops not modelled (walked through, never
  turned at; no memory kernel here can be simulated: the bench has no array ABI). Modes: each loop iterating, inner
  loops iterating or skipped; NOT an inner loop passed through in one trip, and not the transients of entering and
  leaving a loop. A walk can still mix the two branches of an if-then-else inside a loop body (no rule ties two steers
  on the same non-loop condition); that can only over-ask (add stages), and no fixture showed it.
- **Minimality** is not proven (greedy, one stage at a time). On quadrec, nested, nest3 and lfsrfind every stage it
  adds is necessary (each minus-one control deadlocks), so there it is minimal.
- Condition 1 for T >= 2 was never the binding one in these kernels (on quadrec the fork-join pairs imply it); it is
  derived, not separately measured. Condition 2's boundary was measured on both sides (K = 1: 2 stages pass, 1
  deadlocks).
- simcheck is pre-route Verilog with sim/bd_prims_sim.v arc timing; liveness in the model does not depend on delays,
  but right answers on silicon also need the matched delays sized (the routed gate).
- Routed: the 8 routes are built at bdc's generous estimates (BD_SIZES=none), not at the sizes the automatic path
  (auto_size.sh) would choose; whether quadrec stays right at those tighter sizes is untested (suite_one.sh was stopped
  unjudged). One corner (worst) per route plus 8 model draws on the BDC_AUTO routes; no board run.
- Nothing about speed: the stages added cost latency per iteration (not measured here; the gate's `cycles` field is the
  bench's host-cycle total, not a kernel speed).
- CLAUDE.md still says "A ring needs three storage stages per simple cycle"; that is the one-token case of condition
  1. Updating it is the owner's call (not edited here).
