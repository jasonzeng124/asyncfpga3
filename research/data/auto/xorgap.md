# xorgap: what the hand xorshift recipe has that the automatic flow does not (PROGRAM 2026-11-18, lead 1)

Subagent xorgap, 2026-11-18 16:57-22:40 UTC. Every routed number: nextpnr 6e5d224472232d5d. Hand = BOARD-QUEUE item 37
(x55a10: pre_dec MLIR + six knobs + research/data/xorshift_sizes_T3s50_fr4a_x55a10_bench.vh), farm cand3b (28 routes,
P median 16.76). Automatic = BDC_AUTO=1 + research/tools/auto/auto_size.sh: flow v3 = farm suite4, flow v6 = farm
suite6 (the current default). P = the timed event graph's period on the period vector (lane2_run.sh), ns per iteration.

**Summary.** The hand recipe (16.76 ns, farm median) differs from the automatic flow in ONE storage decision: x's back
edge (`ulink_n_trueResult_8`) has 2 stages in the hand recipe, 1 in the flow. Without it the automatic routes' critical
cycle couples x's ring, the loop test's 4-way fork and the control ring (2 polarity changes); the event graph's search
names exactly that link when it can see it -- it could not before: whatif's depth edit failed on every link with an
acknowledge delay, which every automatic link has, and search.py skipped the failure silently. With that fixed, the
search runs inside the flow (auto_size.sh AUTO_SEARCH=1, opt-in) on the route the loop ships, and picks the hand's link
on every automatic xorshift route checked (6 routes, and a no-rewrite one) and nothing on collatz, collatz64, ipow.
Measured on four seeds at v6's own sizes: 17.02 / 18.23 / 18.87 / 15.84 ns against v6's 19.80 / 19.72 / 22.47 / 19.43
(median -2.1 ns); through the phase's raise-only steps (two of them fitted) 17.62 / 18.28 / 17.55 on seeds 1 / 3 / 4
(one clean, two 1-2 rows short). The rest of the gap to 16.6-16.8 is sizing: the loop test's delay UCMPI1 sits on
every ring and the rule ends at 10-14 elements where the hand has 5 (+3 on n's link); v6 is slower than v3 on xorshift
because its loop pins the cycle's lines at the worst route it visits (UCMPI1 9 -> 14 on seed 3).

## 1. Hand vs automatic, same seeds

**P per seed** (farm, nextpnr as each request ran; every route EQUIVALENT except where marked):

| seed | hand (cand3b) | flow v3 (suite4) | flow v6 (suite6) |
|---|---|---|---|
| 1 | 16.65 | 20.39 | 19.80 |
| 2 | 16.66 | 18.87 | 19.72 |
| 3 | 16.62 | 19.86 | 22.47 |
| 4 | 16.79 | 20.20 | 19.43 |
| 5 | 17.14 | 20.03 | 23.46 |
| 6 | 16.51 | 20.49 | 19.86 |
| 7 | NA | BUILD FAILED | 22.28 |
| 8 | 16.99 (NOT EQUIV., old nextpnr) | 20.11 | 22.96 |

**Structure.** The kernel Verilog of the hand route (bq_x55a10_21) and of the automatic routes differ in ONE place:
`ulink_n_trueResult_8` (x's back edge, cond_br7 -> mux1) is a 2-stage `bd_pipe` in the hand recipe
(`BDC_LINK_DEPTHS=ulink_n_trueResult_8=2`, "p8") and a 1-stage `bd_link` (RFAST) in the automatic one. Every other
instance and link depth is the same: BDC_AUTO's rules M / F, fast fall, ring counting and the pre_dec rewrite reproduce
the other five hand knobs exactly (research/data/auto/ident/auto_choices.txt). bdc/auto.py leaves p8 out on purpose
("one kernel justifies it": a static rule for it would also hit collatz).

**Sizes** (elements; the lines on the loop rings; hand = the x55a10 file, lines it does not set take emit.py's
default, marked d):

| line | hand | v3 s1-s8 | v6 s1-s8 | ring(s) |
|---|---|---|---|---|
| UCMPI1 (loop test i < n-1) | 5 | 9-13 | 10-14 | every ring (counter, n, x via fork9, control) |
| ULINK_N11__1 (n's link into the test) | 3 | 0 | 0 | n ring, control ring (mux2 branch) |
| UADDI0 (i + 1) | 12 | 8-12 | 1 (join credit, v4) | counter ring |
| ULINK_N7F__0/1_UACK (i's links' ack) | 6 d | 1 | 1 | counter ring |
| UMUX0 / UMUX1 / UMUX2 | 2 / 2 / 2 | 3-6 / 4-7 / 3-5 | 3-6 / 5-6 / 3-8 | counter / x / n |
| UXORI1 / UXORI2 | 3 / 3 | 5-9 / 4-8 | 5-9 / 1-5 | x ring |
| UCONTROL_MERGE0 / _OLINK / ULINK_N12__1 | 2 / 4 d / 5 | 1-3 / 2 / 1-3 | 2-4 / 1-2 / 1-3 | control ring |
| sum of all sized lines | 105 | 119-136 | 111-133 | |

**Critical cycles** (eventgraph, research/data/eventgraph/graphs; chain = arcs into matched-delay elements, wire = the
routed interconnect between kernel instances, other = cells and wire inside an instance):

| route | P | arcs | chain | inter-instance wire | other | the cycle |
|---|---|---|---|---|---|---|
| hand s21 (bq_x55a10_21) | 16.49 | 36 | 10.01 | 5.42 | 1.07 | the counter ring: umux0, uaddi0 (12 el, 4.83 ns), cond_br6, trueResult_6, fork9, ulink_n7f__1's ack (6 el, 2.48 ns), forkdec0, ulink_n12__0 |
| v3 s8 (board item 41) | 20.11 | 44 | 9.92 | 6.89 | 3.31 | umux1 (x) -> x's back-edge ack (fall) -> cond_br7 -> fork9 (fall) -> ucmpi1 (11 el, 4.0 ns) -> cond_br9 -> control_merge0 -> olink -> n12__1 -> umux1: 2 polarity changes |
| v6 s1 / s2 / s4 | 19.80 / 19.72 / 19.43 | 44 / 41 / 42 | 9.95 / 9.38 / 9.40 | 6.55 / 7.30 / 6.67 | 3.30 / 3.03 / 3.37 | the same shape as v3 s8 |
| v6 s3 / s8 | 22.47 / 22.96 | 47 / 48 | 12.05 / 12.45 | 7.15 / 7.30 | 3.27 / 3.21 | the same shape; UCMPI1 14 (6.0 ns) on s3; UCMPI1 12, merge0 4, n12__1 4, umux1 6 on s8 |

The automatic cycle is not the hand's cycle with longer delays: its matched delay on the cycle is the same (9.4-10.0 ns
on the four fast v6 routes vs 10.0) but it is 6-12 arcs longer, through the x mux, x's back-edge acknowledge (a
falling edge), the loop-test fork and the whole control ring: +1.1-1.9 ns of wire between units and +2.0-2.3 ns of
cells. That cycle exists because x's back edge has one stage: cond_br7 cannot hand x over until mux1 has taken the
previous x, which waits for the select the control ring produces, and fork9 (the loop test's 4-way fork) cannot
acknowledge the compare until every steer, cond_br7 included, has. The hand's second stage absorbs x at once.

**What each difference costs** (research/tools/eventgraph/whatif.py and sizewhatif.py on the route's own graph, same placement, an edit
predicted by the max-plus recursion; sizewhatif.py sets matched delays to another sizes file's lengths at the measured
element weights of that chain; cycdecomp.py splits a critical cycle into chain / wire / cells per instance):

| edit on the automatic route's graph | v3 s8 | v6 s1 | v6 s2 | v6 s3 | v6 s4 | v6 s8 |
|---|---|---|---|---|---|---|
| base P | 20.11 | 19.80 | 19.72 | 22.47 | 19.43 | 22.96 |
| + p8 (x's back edge 2 stages) | 16.78 | 17.36 | 19.06 | 17.92 | 15.90 | 18.57 |
| + p8 + every hand size | 15.06 | | | | | |
| + p8 + hand UCMPI1 5 / ULINK_N11__1 3 only | 16.09 | | | | | |
| + p8 + hand UMUX0/1/2 only | 15.81 | | | | | |
| + p8 + hand UXORI1/2 only | 15.94 | | | | | |

And the other way round, the hand route (which has p8) with each automatic flow's sizes: v6 s1 17.70, s2 19.22, s3
18.48, s4 17.53, s8 18.63, v3 s8 17.95 (hand 16.49): with p8 in place the automatic sizes cost +1.0..+2.7 ns, almost
all on the n ring through the loop test (UCMPI1 10-14 against the hand's 5, the critical cycle becomes ucmpi1 ->
cond_br8 -> trueResult_10 -> mux2 -> fork4 -> ulink_n11__1). The automatic flow is better than the hand on two lines:
the hand route with the automatic UADDI0 = 1 and ULINK_N7F__0/1_UACK = 1 would be 15.75 ns (-0.74).

So the gap (20.1 -> 16.8) has two parts: **(1) structure, p8: -0.65..-4.55 ns** on the six automatic routes (median
-3.4); **(2) sizes on the n ring: UCMPI1** -- the rule wants 10-14 elements in the compare that every ring shares; the
hand has 5 there and 3 on n's link, and its sizes are x0.55 of an older rule's, validated by draws, not by a rule.

## 2. Why v6 is slower than v3 on xorshift

Same seeds, the same structure (BDC_AUTO's choices did not change), so the difference is the sizes the loop ends at.
v6 is bimodal: four seeds faster than v3 (s1 -0.59, s4 -0.77, s6 -0.63; s2 +0.85) and three much slower (s3 +2.61,
s5 +3.43, s8 +2.85; s7 has no v3 route). On the slow seeds the lines ON the critical cycle ended longer:

| seed | v3 -> v6 P | lines on the cycle, v3 -> v6 | where v6 raised them |
|---|---|---|---|
| 3 | 19.86 -> 22.47 | UCMPI1 9 -> 14 | it 3 -> 4 (phase 1): UCMPI1 lowered 12 -> 7 at it 2 -> 3, the it-3 route then 40 rows short, raised 7 -> 14 and pinned |
| 5 | 20.03 -> 23.46 | UCMPI1 12 -> 13, UCONTROL_MERGE0 1 -> 3, ULINK_N12__1 2 -> 3, ULINK_N8_UACK 1 -> 5 | it 4 -> 5 and 6 -> 7 (phase 2, +1 headroom per raise) |
| 8 | 20.11 -> 22.96 | UCMPI1 11 -> 12, UCONTROL_MERGE0 3 -> 4, UMUX1 5 -> 6, UMUX0 4 -> 6, ULINK_N12__1 2 -> 3, ULINK_N12__2 2 -> 4 | it 6 -> 7 (phase 2: 14 rows short, 7 lines raised with +1 headroom) |

Same-placement check (v3's sizes of the same seed on v6's route graph): s3 22.47 -> 20.35 (-2.12 of the measured
+2.61), s4 19.43 -> 21.16 (+1.73), s2 19.72 -> 20.01, s1 19.80 -> 19.79. So the per-seed differences are the cycle's
line lengths, not placement. Mechanism: the ratchet pins a line at the demand of the worst route it met; v6's it-1
recalibration (no pins) lets the lines drop further at it 2-3 (UCMPI1 7, UMUX1 2-3, UXORI2 1), the compact route built
there is short on 34-40 rows, and the raises are pinned at that route's demand (+1 headroom in phase 2). The final
UCMPI1 is 9-14 in both flows and it decides P (~360 ps per element on every ring): which seeds land high is a draw of
the routes the loop visits. v4's join credit (UADDI0 8-12 -> 1) is not the cause (UADDI0 is not on these cycles).

## 3. The change: the event graph's search inside the flow (AUTO_SEARCH=1, opt-in)

What the hand recipe has that the flow lacks is one storage decision (p8), and the tool that found it by hand -- the
event graph's search (research/tools/eventgraph/search.py) -- was never run inside the flow (research/data/auto/README.md:
"Not done: the search inside the flow"). It also could not have found it on an automatic route: whatif.py's `depth`
edit raised "no acknowledge users" for every single-stage link whose acknowledge has a delay (DACK >= 1, every link of
an automatic route after the rule), and search.py skips an edit that raises, silently. Fixed here:

- `whatif.py` depth(): a single-stage link with an ack chain is deepened as a stage on its input channel (bd_pipe's new
  stage 0 sits there with its own DACK) -- the same edit as `stage:REQ_IN:ACK_IN`.
- `maxplus.py` mcr(lenient=True) for whatif's predictions: when the argmax back-walk closes a lower-ratio loop (a node
  shared with a 2-token critical cycle; v6 s1 with p8: walk 17297.0 ps, growth 17356.5 ps at K = 600 and 2400), return
  the growth rate (the period) instead of raising; eventgraph.py's own check is unchanged (lenient defaults off).
- `search.py --depth-only`: only BDC_LINK_DEPTHS candidates, and not rule-F fork-output links (not nameable by
  BDC_LINK_DEPTHS); the automatic structure already has fast fall and rule M, and an env knob naming a merge would
  replace rule M's set (emit.py reads the env first), fast fall would override the memory-kernel refusal.
- `auto_size.sh` AUTO_SEARCH=1: after the loop ships its route (final() has already built that route's event graph),
  search.py --depth-only on it; if it picks an edit, the loop goes on with that structure (BDC_LINK_DEPTHS passed to
  every build), from the shipped sizes, the new line (the deepened link's SDELAY) at emit.py's estimate x 0.3,
  raise-only with one element of headroom (phase 2's step), at most AUTO_SEARCH_MAXIT = 4 routes, and the full stack on
  its last clean route. The flow ships the new route if it is clean and its measured P is lower than the first route's
  (or the first was not clean); else the first route, exactly as without the search. log.txt says both;
  structure.env holds the knob of the shipped route. AUTO_SEARCH_RESIZE=1 (opt-in) re-sizes the new structure as the
  loop does instead (pins emptied, a no-pin recalibration, the pinning ratchet, raise-only at the end, 6 routes): on
  seed 3 the rule proposed 121 -> 78 links on the first p8 route (UCMPI1 14 -> 8), but the routes that followed were
  short on more rows each time (seed 1: 1, 9, 23; seed 4: 3, 9, 47) -- the loop's own oscillation (section 2) -- so it
  is not the default.
- `suite_one.sh` SUITE_SKIP_AUTO=1 judges what an earlier (resumed) auto_size.sh left (used for the measurement below).

Nothing is named by hand: the search names the link from the measured graph of the kernel's own route, and a kernel
whose graph shows no >= 300 ps gain ships its route unchanged. On every graph checked, it picks
ulink_n_trueResult_8 = 2 (the hand's p8) on xorshift (v6 s1, s2, s3, s4, s8, v3 s8) and nothing on collatz (v6 s1, v3
s6, an older s1), collatz64 (v3 s5, an older s1) and ipow (v6 s1, v3 s2, an older s12): there the best depth edit
gains 0-11 ps. That is the "kernel-specific" decision bdc/auto.py left out, taken by measurement for every kernel.

Unset (AUTO_SEARCH empty), the script runs the same commands as before: `${XENV:-}` is empty in build() / final(), and
the tail prints the same result line with the same exit code. bdc/ is not touched: emitted Verilog with BDC_AUTO=1 and
default for xorshift, collatz, collatz64, ipow, gcd, isprime, cmp-identical to the bot's eaef0dec7 (12 / 12).

## 5. What the flow still lacks after p8 (with numbers)

On the hand route (it has p8), the automatic sizes of each seed cost +1.0..+2.7 ns (v6 s1 17.70, s2 19.22, s3 18.48,
s4 17.53, s8 18.63 vs 16.49; same placement). Its critical cycle then is the n ring through the loop test: ucmpi1 ->
cond_br8 -> trueResult_10 -> mux2 -> fork4 -> ulink_n11__1 -> ucmpi1. Two things hold it:

1. **UCMPI1, the loop test's matched delay, is on every ring** (the counter ring through cond_br6's condition, x's
   through fork9 / cond_br7, n's, the control ring), at ~360 ps per element. The rule asks 10-14; the hand has 5 and
   puts 3 elements on n's link (ULINK_N11__1) instead. The rule's binding rows for UCMPI1 come from n's launch (v6 s3
   it 3: "a ucmpi1 from ulink_n11__1.ctl: req 3381 data 3934", plain A peak 4300 vs req 2920), and the rule always pads
   the operator's own delay. A delay on n's link covers the same n-launch rows but sits on 2 rings, not 4; the i-launch
   rows then need the join credit (BD_SKEW_E_JOIN, ejoin.md: sound where an acknowledge started i's link). Graph
   estimate on the automatic routes, beyond p8: -0.7 (v3 s8), -1.3 (v4 s8), -3.9 ns (an older s1 route). Not built here:
   it is a change to corner_audit's choice of WHICH line to pad (by the number of rings a line sits on, from the same
   graph), and the hand's split is also below what the rule accepts at all (next item).
2. **The rule's margin.** The hand sizes are x0.55 of an older static proposal, accepted by draws (200 / 200), not by
   the rule; on the same route the rule's own proposal is 1.4-1.8x longer (PROGRAM "General first" 2). After p8,
   the mux lines (UMUX0/1/2 2 vs 3-8) and x's xor lines (UXORI1/2 3 vs 5-9) are worth another -0.8..-1.0 ns each on
   v3 s8's graph. This is the sizing rule's guard / corner question, not a structural one.
The automatic flow is ahead of the hand on two lines (UADDI0 = 1 by the join credit, ULINK_N7F__0/1_UACK = 1 where the
hand left emit.py's 6): the hand route at those values predicts 15.75 ns (-0.74).

## 4. Measured (nextpnr 6e5d224472232d5d; the full stack: bits-decoded netlist, prjxray SDF, fid, event-graph P)

All on suite6's loop states, i.e. **BDC_AUTO with the three md5-keyed MLIR rewrites (pre_dec on xorshift)** -- since
f7573b807 that is the named variant BDC_AUTO_REWRITES=1, not the default. Each v6 route was rebuilt here from the
farm's sizes with the same seed and came out byte-identical (sdf md5 and P equal: s1 e1415ef0 19804, s3 34ed8d5a 22465,
s4 81893ce1 19429, s8 8599c579 22961, collatz s1 f6c82582 16971, ipow s1 fcbfe8af 21727; s2 55a25d4e 19715 is the
bot's local v6 route = suite6's).

**p8 alone, at v6's own shipped sizes** (the search phase's first route: same sizes, same seed, the route re-placed;
every one EQUIVALENT and ffmux-clean):

| seed | v6 route P | + p8, same sizes | delta | graph prediction | rule on the p8 route |
|---|---|---|---|---|---|
| 1 | 19.80 | 17.02 (dbdca879; iterations alternate, eventgraph stride 2) | -2.78 | 17.36 | 1 row short |
| 2 | 19.72 | 18.23 (c53f5832) | -1.49 | 19.06 | (not run) |
| 3 | 22.47 | 18.87 (08173e0e) | -3.60 | 17.92 | 2 rows short |
| 4 | 19.43 | 15.84 (5609da7a) | -3.59 | 15.90 | 3 rows short |
| median | 19.76 | 17.63 | -2.13 (mean -2.87) | | |

The hand recipe on the same four seeds: 16.65 / 16.66 / 16.62 / 16.79 (cand3b). Draw 10301 (chains 0.26, rest 0.27,
CARRY4 / F7F8 / FF 0.87) on seed 3's p8 route: PASS 19/19.

**Without the rewrites** (the new default, f7573b807): one xorshift route, seed 1, sizes = v6 s1's for the 60 lines
that keep their names + emit.py's estimate x 0.3 for the 6 new ones (not a flow route), sdf 448b2581, P 20.70 ns,
EQUIVALENT: the same coupling cycle (umux1 -> x's back-edge acknowledge -> cond_br7 -> fork9 -> ucmpi1 -> the control
ring, 2 polarity changes), and search.py --depth-only picks ulink_n_trueResult_8 = 2 again, predicting 18.35 ns
(-2.36) = the cycle floor (the counter ring umux0 -> ulink_n7 -> uaddi0 -> ulink_n30__1 -> ucmpi1). So p8 does not
depend on the rewrite.

**The search phase's raise-only default, continued from those routes** (the subagent's p3_raise.sh, not in the repo:
the phase's raise-only steps from the first p8 route's own rule output, the same ratchet / rule / build commands as
auto_size.sh; the node was at load 50-70 on 16 cores and a rule step took 30-40 min under a 3-process budget, so at most
two raise steps fitted before 22:00):

| seed | v6 P | first p8 route (v6 sizes) | raise step 1 | raise step 2 (judged) | rule on the judged route | P judged | delta vs v6 | hand, same seed |
|---|---|---|---|---|---|---|---|---|
| 1 | 19.80 | 17.02, 1 row short | f75dc424, 2 short (ULINK_N_INDEX_15 1 -> 3) | f1498e93 (UCONTROL_MERGE1 1 -> 4) | 2 rows short (wants ULINK_N_TRUERESULT_10_UACK 1 -> 3) | 17.62 | -2.18 | 16.65 |
| 3 | 22.47 | 18.87, 2 short | 4f4710f7, 4 short (ULINK_N12__2 1 -> 3) | 8e072bbf (UADDIDEC0 4 -> 7, ULINK_N_TRUERESULT_8_SDELAY 1 -> 3) | CLEAN | 18.28 | -4.19 | 16.62 |
| 4 | 19.43 | 15.84, 3 short | c8080748, 2 short (UMUX3 5 -> 7, ULINK_N12__2 1 -> 3) | db331900 (ULINK_N_TRUERESULT_8_UACK 1 -> 4) | 1 row short (wants ULINK_N_TRUERESULT_0_SDELAY 1 -> 3, x's entry link) | 17.55 | -1.88 | 16.79 |

Draws on the judged routes (K = 10000 + 100 x SEED + j, suite6's first four draw points of each seed, xor19, the C's
expected values): **12 / 12 PASS** (s1 10101-10104, s3 10301-10304, s4 10401-10404; CARRY4 / F7F8 / FF drawn 0.38-1.00, every
run 19 / 19, EQUIVALENT); plus 10301 on s3's first p8 route (v6 sizes): PASS 19 / 19.

On s4 the raises cost 1.7 ns of the structural gain: step 1 put 4 elements on the new pipe's acknowledge
(ULINK_N_TRUERESULT_8_UACK), and the critical cycle of the judged route runs through it (ucmpi1 -> cond_br7 ->
ulink_n_trueResult_8, ack 2.5 ns -> fork9 -> ulink_n7f__1). On s3 the judged route keeps v6's UCMPI1 = 14 (raise-only
never lowers): ucmpi1 is 7.2 ns of its 18.28 ns cycle. On s1 the counter ring is critical (ulink_n12__0 5 and ucmpi1 11,
v6's values).

## 6. What this does not show, and what is open

- The measured routes are the "with the three md5-keyed rewrites" variant (suite6's states: pre_dec on xorshift);
  without the rewrites (the default since f7573b807) only one route was checked, by the graph (the search picks p8
  there too; not built with p8).
- One-route numbers per seed, four seeds (s2's loop was stopped before any raise step; s1 / s4's judged routes are 2 / 1
  rule rows short: the phase would have built one more route). The farm request xsearch1 / its successor on norw1's
  states measures the phase as written, 8 seeds per kernel.
- The ship decision (P_new < P_old) chooses between two measured routes of the same seed: a flow that builds two
  candidates ships the better one. The deltas above compare the p8 route with v6's route, not the minimum.
- Not closed: the loop test's delay. After p8 the cycle is the n ring through ucmpi1 (UCMPI1 10-14 against the hand's 5
  + 3 on n's link). A rule that pads the input link whose launch binds an operator (fewer rings) instead of the operator
  (every ring), with the join credit for the other input (BD_SKEW_E_JOIN), is what the hand split would need; the graph
  prices it at -0.7..-3.9 ns beyond p8. Not built.
- The loop itself (section 2): pinning at the worst route visited is what makes v6 bimodal on xorshift; the re-sizing
  variant of the search phase (AUTO_SEARCH_RESIZE=1) shows the same instability on the new structure.
- No board run. The draws use the delay model (bench_gate.sh draw:K); the simulation runs ~8 % slow per iteration
  against the August board (SIM-VS-BOARD.md).
