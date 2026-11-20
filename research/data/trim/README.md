# trim: shortening matched delay lines after routing, by LUT INIT alone (2026-11-20)

Research bot, session cluster-research-29671222-1; nextpnr 6e5d224472232d5d (toolchain.sh all ok).

## The mechanism
A bd_delay / bd_delay_gated line (cells/rtl/bd_latch.v) is a chain g[0] = LUT1(s[0]), g[k>=1] = LUT2(s[k], side) where
`side` is the line's own input (FASTFALL: AND, INIT 1000; FASTRISE: OR, 1110; gated: AND with `gate`). Setting one
element g[i]'s INIT to 1100 (O = the side input) makes g[i] the line's entry: the line is then N - i elements, with the
same edge behaviour, on the SAME placement and routes. So a routed line of LUT2s can be shortened to any length 1..N
by bits alone; lengthening still needs a route. Symmetric lines (LUT1 elements) cannot be trimmed.
- research/tools/auto/trim_lines.py ROUTED_JSON FASM_IN OUT_JSON OUT_FASM [--partial] MACRO=LEN ...: the INIT edit in
  the routed JSON and the FASM (each touched LUT site's 64-bit INIT recomputed with cells/verify/fasm_audit.py's
  expected_lut_bits, X_ORIG_PORT pins included); then the bitstream from the FASM as build_bench.sh makes it.
- The rule reads trimmed lines: cells/verify/tighten.py chain_side_arcs() no longer treats an entry's side arc as a
  fast-fall side tap (an entry has no live arc from the stage before it: false_arcs() cuts it from the INIT), and
  research/tools/corner_audit.py chain_geometry() starts a trimmed chain at its entry. Untrimmed, both are byte-
  identical (xorshift s1 it 5: neg, rule.vh, report / tighten / skew logs, lines.tsv at both corners).

## First measurement: xorshift s1, the != fixture, the loop's shipped route (ex_xorshift_1_9, sdf d947adff)
- Untrimmed: P 18.09 ns, NOT CLEAN by one row (H -30 ps on ulink_n_falseResult_9 stage 1: the rule wanted its UACK
  raised 1 -> 2). Its finish phase had pinned ucmpi1 back at 15 (11 at it 5).
- The rule's own proposal on that route shortens 15 lines; 10 macros (14 chains) are trimmable (ucmpi0 8 -> 7, ucmpi1
  15 -> 12, ucontrol_merge1 3 -> 1, ulink_n12__0 3 -> 2, three UACK lines, umux1 7 -> 3, umux2 6 -> 2, uxori2 3 -> 1);
  ulink_n12__1 and ulink_n31_folink are symmetric lines (refused); two _SDELAY macros had no chain.
- Trimmed (14 LUT INITs, nothing re-placed or re-routed): **P 15.18 ns (-2.91 ns, -16 %)**, event-graph checks PASS
  (xs_ex9_trimmed_check.txt); bits-decoded netlist **EQUIVALENT**; **draws 10101-10104: PASS 19 / 19 each**, no pulse
  under 1 ns on 172 kernel handshake nets, narrowest 2.1 ns.
- **CORRECTION (2026-11-20 05:00 UTC):** this README first said the rule on the trimmed route showed "the same single row
  as before trimming, nothing new" (xs_ex9_trimmed_neg.txt). That was a defect of the rule support, not a property of
  the route: tighten.chain_side_arcs counted a trimmed line's entry as fed by its predecessor (the routed wire into the
  dead pin stays in the graph; only the LUT arc is cut), so the entry's side arc stayed excluded, the request walk never
  reached the line, and the cell was "not audited" (ucmpi0: "nothing outside ... reaches its request"). Fixed (the
  predecessor's pin must still have its LUT arc). **With the fix, the same trimmed route has 5 new short constraints:
  A'j ucmpi1 -346 ps (0.31), A ucontrol_merge1 -145 / -233, E at ucond_br5 / ucond_br2 -203 / -190 (0.31), A'j
  ucmpi0 -63 (0.31)**, beside the old H -30 (xs_ex9_trimmed_neg_fixed.txt). The rule's proposal, priced on the untrimmed
  route, under-delivered on the trimmed one. The four draws above still passed.
- What the defect cost: the loop's AUTO_TRIM step (7a7cffb2d) took a second step on top of these 14 trims, including
  ucmpi0 7 -> 1 (the rule, blind to it, called it "floor 1"); that route does not finish in simulation (449 us of
  simulated time against 11 us). Bisected (each step-2 trim alone on the step-1 route, 30 us batch limit): ucmpi0 at 1
  alone hangs (result x, the bench FSM in x), the other four alone complete with the right answer. The fixed rule flags
  ucmpi0 at 1 with E rows of -1.1 .. -2.5 ns at four steers and A'j -2.2 ns.
- Critical cycle (cycdecomp): chains 11410 -> 9212 ps, wires 3833 -> 3833 (the same routes), cells 2845 -> 2138.

## Does NOT show
One route of one kernel; the draws' four points; that a trimmed line's entry (the side net, a fanout wire) is as well
modelled as a chain hop (the rule and the GLS both read it from the same SDF); anything about symmetric lines.

## The loop's trim step with the corrected rule (2026-11-20 04:45-05:05 UTC; AUTO_TRIM=1)
- Full proposal (step 1 = the 14 trims): 16 short constraints opened (1458 ps) -> reverted. Damped (half the gap): 14
  (1044 ps) -> reverted. trim_plan.py (each entry priced exactly from the corner SDFs, charged to the constraints that
  list the line in "depends on"): ucmpi1 15 -> 13, ucontrol_merge1 3 -> 1, umux1 7 -> 2, umux2 6 -> 1, uxori2 and
  three UACK lines -> 1: 12 opened (754 ps) -> reverted. The opened rows are on the trimmed cells themselves (A'j
  ucmpi1 -165, A ucontrol_merge1 -145 / -233, A'm umux1 / umux2 -14 .. -112, H trueResult_0 stage 1 -106): the linear
  charge (delta x sensitivity / line delay) under-estimates, and an A'j / A'm row may not list its own line's macro.
- What it says about this route: little rule-clean slack is left on the lines that matter. The finish phase pinned
  ucmpi1 at 15 where this route needs ~14 built-equivalent elements; the 2.9 ns of the first measurement came mostly
  from going BELOW the rule's need (the four draws tolerated it; the rule's guards sit beyond the draw model).
- Two ways on, not taken yet: (1) model a trim exactly inside corner_audit (its verify step re-times the route with the
  trim applied: cut the dead chain input, the side arc becomes the entry) so the rule proposes rule-clean trims
  directly -- expected gain here ~0.5-1 ns; (2) size by the draws (PROGRAM "Sizes may be chosen by this simulation":
  shorten while every draw passes, report the distance to the first trim that fails, take the longer on a tie) -- the
  xorshift route above is such a point (15.18 ns, 4 / 4), and ucmpi0 at 1 is a failing one (hang). Either way the
  route stays the same and only bits change, which is what makes a search over trims cheap.

## The trim step on routes the farm shipped (2026-11-20, session cluster-research-29671222-1)

**Method.** `research/tools/auto/trim_farm.sh REQ TASK OUT [ENV]` (auto_size.sh AUTO_TRIM_ONLY=1): a farm task's
shipped route is rebuilt from its own sizes, seed and structure (the sdf md5 must equal the farm's, else the run stops:
it did once, on a search-phase route whose structure the farm does not return -- fixed), the flow's trim step runs on
it (the rule's trim mode, CA_TRIM=1, as AUTO_TRIM=1 runs it in the loop), the full stack, and suite_one.sh's draws on
the farm's OWN draw points (K = 10000 + 100 x seed + j). The comparison is paired on one route: only LUT INITs differ.
`research/tools/auto/trim_table.py OUTROOT...` tabulates. nextpnr 6e5d224472232d5d; rule as flow v9 (CA_BENCHCAP=1).

| route (request task) | P farm -> trimmed (ps) | dP | trimmed lines | draws on the trimmed bits | rule before / after |
|---|---|---|---|---|---|
| exit1 countloop s2 (39) | 22368 -> 20167 | -9.8 % | ucmpi1 18->13, ucontrol_merge0 4->2, umux1 5->2, umux3 6->2, two UACK | 4 / 4 PASS (10/10) | NOT CLEAN by one H row (-111 ps), unchanged |
| exit1 xorshift s1 (1) | 18088 -> 16738 | -7.5 % | | 2 / 4 PASS so far (19/19) | NOT CLEAN by one H row (-30 ps), unchanged |
| exit1 horner s1 (10) | 21088 -> 20424 | -3.1 % | 20 lines at step 1 | 2 / 4 PASS so far (11/11) | clean / clean |
| exit1 lfsrfind s1 (8) | 27880 -> 27062 | -2.9 % | ucmpi0 11->10, ulink_n22__0 3->2, ulink_n22__1 7->1, umux0 4->2, umux1 5->2 | 4 / 4 PASS (10/10) | clean / clean |
| exit1 mul_example s2 (60) | 61750 -> 60989 | -1.2 % | 1 line | 4 / 4 PASS | clean / clean |
| capfix1 mul_example s2 (17) | 60990 -> 58451 | -4.2 % | | running | clean / clean |
| exit1 test_stdint s1 (27) | 52701 -> 52701 | 0 | none: the trim mode moves no line | 4 / 4 PASS | clean / clean |

The trimmed xorshift s1 route is the README's first measurement route (d947adff): there the 14-trim set reached
15.18 ns but was rule-short by 63-346 ps; the rule's own trim mode reaches 16.74 ns with no new short row.

**How far the trims sit from the first trim that fails** (`research/tools/auto/trim_shrink.sh`: EVERY trimmable line
K elements below its current length -- the trim mode's choice, or as built where it trimmed nothing -- on a copy of the
route, the same four draws). K = 1: lfsrfind s1 (10 lines) 4 / 4 PASS, countloop s2 (14 lines) 4 / 4 PASS. K = 2, 3, 5, 8:
running.

**Cycle composition after the trim** (cycdecomp): xorshift s1 16738 = chains 10060 + wire between cells 3833 + cells
2845 (7 cells on the cycle; the fused update + test ucmpi1, 15 elements, 5.6 ns, is the largest item: its first trim
step would skip the anchor LUT, more than the rule allows); lfsrfind s1 27062 = 12641 + 11966 + 2455 (12 cells, ~1 ns
of wire each); countloop s2 20167 = 8987 + 8023 + 3157 (the trim moved the critical cycle from the counter ring to s).

**In the flow.** AUTO_TRIM=1 (opt-in) runs the same step on the route the loop ships, recording the untrimmed route's own
stack first (it_I_untrimmed.txt, P_untrimmed on suite_one.sh's line) and the cycle composition before and after
(cyc_I_untrimmed.txt, cyc_I.txt). Farm suite13t (filed 2026-11-20 08:00 UTC, prediction in the request) runs flow v9 on
every suite kernel x 4 seeds with it: the paired measurement over the whole suite.
