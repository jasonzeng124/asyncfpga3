# A placement weight on every loop ring, emitted by the compiler (PROGRAM "General first", idea 6a): NEGATIVE

Subagent `ringplace` (2026-11-18 04:30-10:55 UTC; stopped by the week's usage limit, read and written up by the main
session). PROGRAM: "wires were about 5 ns of the cycle on lever 3's route ... a constraint the compiler emits for every
ring has not been tried as a rule."

**The lever (arm B).** `BDC_RING_PLACE=1` under `BDC_AUTO=1`: bdc finds every loop ring from the token-floor walk graph
(strongly connected components holding a back edge; rings sharing a node are one group, so xorshift's rounds ring and
counter ring are one group), and puts one attribute on the kernel module; `cells/hw/rloc_stamp.py` turns it into
`PLACE_WEIGHT 8` (patches/nextpnr-xilinx-place-weight.patch) on every handshake net inside one group. A matched delay's
own links stay at weight 1 (weighting them would shorten the delay the rules sized). Arm C: weight 3. Arm B0: an
earlier B (attribute on another line), the same routes where both exist. Arm A: the same sizes and seed without it =
the suite4 routes (sdf md5s equal the farm's). Sizes: each route's own suite4 `sizes_final.vh`
(research/data/suite/farm/suite4/), identical in both arms, so only placement differs. nextpnr 6e5d224472232d5d.

**Prediction (written 09:42 UTC, before any B result):** B vs A within +-1 ns of P with no consistent sign;
inter-unit wire on the critical cycle 0-2 ns lower on B; chain wire unchanged.

**Measured** (P from the itercost stack; the cycle's wire split from `research/tools/eventgraph/cycle_wire.py`;
ab_table.txt has every row):

| kernel s | A: P (ps) | B: P | dP B-A | C (w 3): dP | d inter-unit wire on the cycle (B) |
|---|---|---|---|---|---|
| xorshift 1 | 20388 | 20104 | -284 | -731 | -221 |
| xorshift 8 | 20112 | 19285 | -827 | +581 | -724 |
| collatz 3 | 17707 | 20076 | +2369 | +1400 | +1160 |
| collatz 6 | 18993 | 20103 | +1110 | -675 | -84 |
| collatz64 3 | 21501 | 24931 | +3430 | | +4541 |
| collatz64 5 | 23713 | 23651 | -62 | | -1036 |
| ipow 2 | 22711 | 21825 | -886 | | -1151 |
| ipow 5 | 21474 | 22067 | +593 | | +3425 |

**B: 8 routes, dP median +266 ps, mean +680, range -886..+3430, faster on 4 / 8. C: 4 routes, median -47, mean +144,
faster on 2 / 4.** Every route EQUIVALENT and ffmux-clean. The prediction held on the sign (none) and failed on the
inter-unit wire: it went up on 3 of 8 routes, by up to 4.5 ns, because a weight on some nets re-places everything, and the
cycle that binds afterwards is a different one. Wire is 85-87 % of the critical cycle on every route of both arms
(chain + intra + inter); the critical cycle's composition moves with the placement, not with the weights.

**Verdict: not a rule for the automatic path.** A soft placer weight on the ring's nets does not shorten the cycle
consistently; on two routes in eight it costs more than 2 ns. Not pursued further: the farm request prepared for a
32-route A/B (ringplace1) was not submitted, since 8 routes already show a mean loss and no route gained more than
0.9 ns. What might still work is a hard constraint (relative placement of a ring's cells, RLOC_GROUP), which this does not
test.

**Not landed in bdc** (a negative lever stays out of the compiler): the knob is kept as a patch,
`ringplace_knob.patch` (bdc/emit.py `ring_place_groups`, cells/hw/rloc_stamp.py, build_bench.sh, the A/B script and the
unsubmitted farm request), against 5cea12356. Landed: `research/tools/eventgraph/cycle_wire.py` (the wire split of a
timed event graph's critical cycle: chain / intra-instance / inter-instance hops) and suite4's per-route sizes.
