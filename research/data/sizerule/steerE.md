# steerE: rule E at a steer whose join carries the select's own request (`BD_SKEW_STEER_SELF=1`)

Subagent `steerE` of research, 2026-11-17 21:20 - 23:55 EST. nextpnr 9c732bc6303458df (patch set as printed by
`cells/verify/toolchain.sh`, OK at 22:16 EST before the build). Changed: `cells/verify/skew.py` (additions behind the
flag), `cells/verify/test_skew_walk.py` (one test), `research/tools/corner_audit.py` (one report line, only when the
flag is set). Added: this file and `xorshift_sizes_auto_ss5_bench.vh` (the sizes built in section 5). cells/rtl, bdc, dynamatic,
circt untouched.

**Headline.** The row that sizes xorshift's loop compare UCMPI1 at 17-19 in the automatic flow is not a race of one
token. Its launch is a latch output of the n link (`ulink_n11__1.lat.*`); its "request" reaches the loop steer by going
through that steer's OWN LUT (select pin -> req0/req1 output), out to its acknowledge, into a SIBLING input link's
controller on that link's acknowledge pin (`c_next`: the sibling's next token), and into the steer's join, which the
AND seeding then lets fire on that input alone -- the join's other input, the compare's own request, starts at the
link's C node and is never reached from a latch output. Its margin is the lap's delay minus the select's own skew;
UCMPI1 is not in it, and the sizer charges UCMPI1 against it only through its linear model. `BD_SKEW_STEER_SELF=1`
bounds such a launch's request by the select channel's own request (the join cannot fire before it). On the AUTO route
su_xorshift_1_4, at both corners of the auto flow, the only line the flag changes is UCMPI1: 17 / 16 -> 7 / 8 (merged
17 -> 8; kernel links 103 -> 94), now bound by A' at ucmpi1 (the compare's own bundling); with `CA_JOINAWARE=1` as
well, 89 -> 80 links, UCMPI1 8 bound by rule E's C-node row (CA_JOINAWARE alone leaves UCMPI1 at 17). collatz and
collatz64: no change (the bound is computed at all 12 steer gates and never the later). Built (seed 1, the auto
loop's next sizes with the flag, UCMPI1 8): P 16620 ps against the AUTO route's 21084 (hand recipe ~16.8 ns),
EQUIVALENT, 4 / 4 xor19 draws PASS. Unset, rule E's output is byte-identical (skew.py cmp; corner_audit reproduces the
bot's run). Every negative control larger than the route's real margin stays flagged, with identical rows where the
flag moves nothing; the one control whose verdict changes (+3 ns on the compare's carry at UCMPI1 18) could not be
decided in GLS (that carry never toggles for xorshift's inputs; +8 ns passes too). What remains: the new route is NOT
clean under the rule (E's C-node row at ucond_br8 -267 / -527, A' ucmpi1 -207; the loop would pin UCMPI1 at 11 next),
and rule E, with or without the flag, still flags the hand recipe's own route at its loop steers (-0.2 .. -1.2 ns, C
nodes) where formal measures +0.9 .. +1.5 ns of settle: E credits no join input its launch does not reach (section 6).

## 1. The race the binding row stands for

Route su_xorshift_1_4 (auto loop it 4, seed 1, sdf 694d657d, UCMPI1 18), corner_audit as `auto_size.sh` rule()
(`BD_SKEW_AND_JOIN=1 CA_SIZERULE=1`, `--band 0.20` / `0.31`, chains 0.20, CARRY4 / F7F8 / FF 1.0, guards 0.97 / 1.03).
Traced with skew.py's own walk() and path_to(), replaying main()'s launch selection at the gate, corner 0.20:

| | path (storage crossings in brackets) | arrival |
|---|---|---|
| launch | `ulink_n11__1.lat.pair[0].u$LUT5/O5` (n, bit 0: one of the compare's operands) | 0 |
| select (latest) | -> ucmpi1's CARRY4 compare -> `ucmpi1.uz_n41` -> `ucond_br8.u$LUT5/A4` | 3220 ps |
| request (earliest) | -> ucmpi1's LUTs -> `uz_n41` -> **ucond_br8's own select pin A4 -> its LUT5 output (req . ~s) -> `ucond_br8.uack`** -> `ulink_n11__0_folink.ctl.u.u/A2` (c_next) [1: the sibling's C node, on its acknowledge] -> its rdly -> `ucond_br8_j/A5` [2: the join, seeded with A5 alone] -> `ucond_br8.u$LUT5/A1` | 4098 ps |
| margin | raw +878, divergence 676 ps in, guarded **+699** (t2_0.20; +875 at 0.31) | |

The join `ucond_br8_j` is a bd_ctree C-element with inputs A2 (`ucmpi1.udly.chain.g[17]`: the compare's request,
n32__1_req) and A5 (`ulink_n11__0_folink`'s request, the n token being steered). From the latch output the walk
reaches A5 at level 1 only through the lap above and never reaches A2 at all (A2 descends from the link's C node,
upstream of its latch output), so `BD_SKEW_AND_JOIN`'s seeding -- "only inputs reached at THIS level count" -- fires
the join on A5 alone. ucond_br9 is the same with one more crossing: its select -> its LUT6 output (req1) ->
`ulink_n_trueResult_12`'s C node [1] -> its ack -> `ucond_br9.uack` -> `ucontrol_merge0_rlink`'s C node on c_next [2]
-> rdly -> `ucond_br9_j/A3` (n_result) [3] -> request pin: 4373 ps (3 x) vs select 3012, guarded +1180 (on the it-0
route au_xorshift_1_0 the same path is the 6048 ps (3 x) row of the brief, +1611).

What the row stands for is therefore: "the select changes, the steer fires on the change (the mis-steer itself), the
steered token is acknowledged, the sibling input link takes its NEXT token, and that token's request completes the
join". It is not the request this select is bundled with. In one transaction: when the n link's C node rises (the latch
opens, the select can move), the steer's join has already returned to zero -- the C node needs c_next low, i.e.
ucmpi1's z_ack low, i.e. ufork9's acknowledge C-tree low, i.e. every loop steer's acknowledge low, which follows its
join's fall -- and the join's next rise needs the compare's next request, which needs this C node's request through
ucmpi1's operand join and its matched delay. The C-node launches that measure exactly that are evaluated at the same
gate and are far from binding:

| gate (0.20) | binding launch (flag unset) | guarded | C node of n (`ulink_n11__1`) | C node of i (`ulink_n7f__1`) |
|---|---|---|---|---|
| ucond_br8 | n latch, 2 x lap | +699 | +4573 (req 9149, sel 4176) | +4442 (req 9107, sel 4263) |
| ucond_br9 (it 0, au_xorshift_1_0, 0.21) | n latch, 3 x lap | +1611 | +7722 | +7749 |

Why the line moves by only 1-2 elements: corner_audit charges a shortened line on a constraint at slope
max(0.97, dM / D) against that constraint's CURRENT margin. Here the row is the min over launches; zeroing UCMPI1 drops
it by dM 2536 (the C-node launches overtake the lap), so each ps of UCMPI1 is charged 0.97 ps against the lap's +699,
although the lap row itself does not move with UCMPI1 at all. UCMPI1 18 -> 17 (0.20, 333 ps left) / 16 (0.31, 143 ps
left); at it 0, 30 -> 26 (205 ps left).

The hypothesis of the brief holds, with one refinement: the request path is not "through other storage" in the
forward sense; it is a lap through the gate being checked and a sibling's acknowledge (2 crossings at ucond_br8, 3 at
ucond_br9), and the binding row's dependence on UCMPI1 is an artefact of the sizer's linear charge, not of the row.

## 2. The change (`BD_SKEW_STEER_SELF=1` or `--steer-self`; unset = byte-identical)

`cells/verify/skew.py` (5) and `self_request_floor()`. At a select gate whose request pin is driven by a positive
C-element J (a bd_ctree node), and whose select comes from a producer P with a request of its own (a request site,
`<P>.uor`, whose `.uor` has ONE input -- a compute cell's operand join; a bd_merge's two-input OR is excluded because
either request raises it) or straight from a link's latch: for a launch X that is a latch output of link L, with L's
C node C,

    J >= s(C -> ip) + arc(ip -> J) - l(C -> X)          (relative to X)

for an input ip of J that C's EARLIEST walk reaches along the channel's own request path -- every pin inside L's or
P's instances, every storage node crossed a C-tree of P's operand join (`P.ujoin.*`), passing P's request output (the
chain tail). l(C -> X) is X's arrival on C's LATEST walk at level 0 (enable net + EN -> Q). Any other chain (another
link's controller, a merge, a steer, the gate itself) gives no bound. The request from X becomes max(walk, bound);
where the bound is the later, the row is the race from C (request through the channel's request, select through X),
with the divergence point C, l(C -> X) BEFORE the launch, so both legs are guarded from C (`divergence point -N ps`,
and a `request bound (--steer-self)` line in the verbose block; corner_audit's parser ignores the extra line). Every
other launch, every other gate (mux joins: their request pin is the select link's own request, not a C-tree) is
untouched; C's own launch (added by (3)) keeps its row.

Why it is a lower bound: the latch is transparent while C is high and its data is held by the sender until it closes
(rule H), so X moves only when C rises: X <= C + l(C -> X). The compare's request rises only after C's request passes
P's operand join (a positive C-element) and P's gated delay; J fires after every input. And X's change cannot fall
inside an earlier firing of J: C rises only with c_next low, which (ufork9's acknowledge C-tree, every steer's ack)
follows J's return to zero. So the bound holds under the 4-phase discipline of the cells and rule H at L; rule E does not
check either (rule H and the cells' own verification do), and neither is changed.

## 3. Checks

**Byte-identical when unset.** `skew.py -v` on su_xorshift_1_4's 0.20 corner SDF, before and after the change: `cmp`
identical. corner_audit (unset) at HEAD + the change, su_xorshift_1_4 0.20, against the bot's earlier t2_0.20 run:
sizes.vh, negative_sized.tsv, tighten.log identical; report.txt identical below its 3-line header (paths); skew.log,
arb_fork.log, verify.txt identical but for the SDF path line; lines.tsv the same rows (rows with equal delay come out
in another order: corner_audit's chain dict is built from a set, so tie order follows Python's hash seed -- not new).

**Unit test.** `cells/verify/test_skew_walk.py::test_steer_self_floor_counts_the_channel_request_not_a_lap`: a minimal
graph with the lap; the bound is 160 ps from the channel input only; no bound through an outside instance, without the
producer's request output on the chain, through a join that is not the producer's, or for a launch C does not open.
All four tests of the file pass; with test_rule_a_links.py and test_resize.py, 33 / 33 under pytest.

**What the flag moves on the AUTO route (0.20, corner_audit guards).** Loop steers only:

| steer | flag unset: launch, guarded | flag set: launch, guarded |
|---|---|---|
| ucond_br6 | n latch (lap), +4071 | C of i, +4117 |
| ucond_br7 | n latch (lap), +3443 | C of i, +4596 |
| ucond_br8 | n latch (lap), **+699** | C of i, +4442 |
| ucond_br9 | n latch (lap), +1180 | C of i, +4463 |

Entry steers ucond_br2-5 and umux0-3 identical (16 gates qualify: the 8 steers' two LUTs each; 0 muxes).

**Negative controls** (corner_audit's worker, guards 0.97 / 1.03, BD_SKEW_AND_JOIN=1; "rows < 0 / min" over all 24 E
rows; loop steers br6 / br7 / br8 / br9):

| route, defect | flag unset | flag set |
|---|---|---|
| su_xorshift_1_4 (UCMPI1 18), 0.20, none | 0 < 0; +4071 / +3443 / +699 / +1180 | 0 < 0; +4117 / +4596 / +4442 / +4463 |
| ditto, UCMPI1 at 1 (its chain arcs x 1/18) | 8 < 0; -1818 / -1339 / -1493 / -1473 | 8 < 0; identical rows (C of i) |
| ditto, +3 ns on ucmpi1's carry (slice[0] CO3 -> slice[1] CIN) | 4 < 0; +981 / +353 / **-2390 / -1909** (laps) | 0 < 0; +1027 / +1506 / +1352 / +1373 (C of i) |
| ditto, +8 ns on ucmpi1's carry | 8 < 0; -4168 / -4796 / -7540 / -7059 | 8 < 0; -4122 / -3643 / -3797 / -3776 |
| ditto, +3 ns on uz_n41 -> ucond_br8/9 LUTs (steerneg) | 0 < 0; br8 +519, br9 +1000 | 0 < 0; br8 +1352, br9 +1373 |
| ditto, +8 ns on uz_n41 -> ucond_br8/9 LUTs (steerneg) | 4 < 0; br8 -3797, br9 -3776 | 4 < 0; identical |
| ditto, +8 ns on the compare's output (uz_n41's input) | 8 < 0; -4122 / -3643 / -3797 / -3776 | 8 < 0; identical |
| ditto, +3 ns on every mux select arc into uj0 / uj1 (selneg) | 8 < 0; umux0-3 -2907 / -2993 / -1957 / -3012 | identical |
| se_xorshift_ss_5 (new route, UCMPI1 8), 0.20, none | 5 < 0; br8 **-267** (C of i) | identical |
| ditto, +3 ns on ucmpi1's carry | 11 < 0; -2774 / -2024 / -3357 / -2653 | identical |
| bq_x55a10_21 (hand recipe, UCMPI1 5), 0.20 / 0.31, none | 8 < 0; br6-9 -929 .. -211 / -1189 .. -382 (C of i) | identical |

Every defect larger than the route's real margin at the loop steers is flagged with the flag set, and where the flag
moves nothing the rows are identical. The one control that changes verdict is +3 ns on the compare's carry at
UCMPI1 = 18: flagged without the flag only through the lap rows, while the request the select is bundled with is still
1.0-1.4 ns (guarded) behind the late select. Section 5: the GLS cannot decide it on this route. The mux controls (select links at 0 by
scaling: +18 .. +158, not a failing control on this compact route; +3 ns injected: flagged) are untouched by
construction. The select-at-0 builds of 2026-11-16 (farm routes, not local) were flagged at the mux joins, which the
flag does not touch; their "steers br6/8/9 on a few" rows could not be re-checked here.

## 4. Effect on the automatic flow (corner_audit on the AUTO routes, both corners, merged as auto_size.sh)

Routes: the last iteration of each auto run (`/tmp/bot/runs/ca/su_<k>_1_4`, seed 1), corner_audit exactly as
`auto_size.sh` rule() (`BD_SKEW_AND_JOIN=1 CA_SIZERULE=1`, `--band 0.20` and `--band 0.31`, chains 0.20), merged per
line by the max (`merge_rules.py`). "base" = flag unset (xorshift 0.31: the bot's t2_0.31 run of the same command,
whose 0.20 twin this code reproduces, section 3); "ss" = `BD_SKEW_STEER_SELF=1`; "ja" / "ssja" = with `CA_JOINAWARE=1`.
Only lines some configuration moves; kernel links = the sum over the kernel's lines.

**xorshift** (su_xorshift_1_4, sdf 694d657d, P 21084 ps):

| line | route | base | ss | ja | ssja |
|---|---|---|---|---|---|
| UADDI0 | 8 | 7 | 7 | 1 | 1 |
| UADDIDEC0 | 5 | 7 | 7 | 3 | 3 |
| UCMPI0 | 7 | 8 | 8 | 7 | 7 |
| **UCMPI1** | 18 | **17** | **8** | **17** | **8** |
| UCONTROL_MERGE0 | 1 | 2 | 2 | 2 | 2 |
| UCONTROL_MERGE1 | 2 | 1 | 1 | 1 | 1 |
| ULINK_N12__2 | 3 | 1 | 1 | 1 | 1 |
| ULINK_N_TRUERESULT_10_SDELAY | 2 | 1 | 1 | 1 | 1 |
| UMUX1 | 3 | 2 | 2 | 2 | 2 |
| UMUX2 | 5 | 3 | 3 | 3 | 3 |
| UMUX3 | 2 | 6 | 6 | 6 | 6 |
| UXORI1 | 6 | 4 | 4 | 3 | 3 |
| UXORI2 | 4 | 4 | 4 | 2 | 2 |
| kernel links | 106 | 103 | 94 | 89 | 80 |

UCMPI1's binding row per corner (0.20 / 0.31): base and ja "E ucond_br8.u$LUT5/A1" (the lap; 333 / 143 ps left) ->
17 / 16; ss "A' ucmpi1" (47 / 143 ps left) -> 7 / 8; ssja "E ucond_br6.u$LUT5/A3" (the C-node row of i, the same race
as A'j ucmpi1's worst capture: data 4441 / capture 8961 ps at 0.20; 91 / 205 ps left) -> 7 / 8. CA_JOINAWARE alone does
not move UCMPI1 (the lap binds); the flag alone or with it gives 8.

Every other line is the same in base and ss at both corners (and in ja and ssja), so the merged proposals differ in
UCMPI1 alone, and so do the ratcheted next sizes (`ratchet.py` with the run's pinned.txt; UADDI0 is pinned at 8 by an
earlier raise, so it does not shrink in either).

**collatz** (su_collatz_1_4) and **collatz64** (su_collatz64_1_4): the flag changes nothing. At both corners sizes.vh
and report.txt are identical with and without it (lines.tsv the same rows). The bound is computed at all 12 steer
gates (6 steers x 2 LUTs) but is the later at none: their latch launches' own request walks are LATER than it
(collatz ucond_br7, 0.20: the operand latch `ulink_n10__4.lat.pair[0]`'s walk reaches the request at 9198 ps, 3 x; the
bound from `ulink_n10__4`'s C node through ucmpi2 -- a one-operand compare, no join crossed -- is 4439 ps), and their
binding steer rows are C-node launches already (0.20: collatz UCMPI2 9 -> 8 "bound by E ucond_br7" from
`ulink_n10__4.ctl`; collatz64 UCMPI2 16 -> 12, the same; collatz64's entry steers ucond_br2-4 are -754 .. -986 from
`ulink_n1__1.ctl`, also C-node rows, in both configurations).

| collatz line | route | base = ss | | collatz64 line | route | base = ss |
|---|---|---|---|---|---|---|
| UADDI1 | 11 | 6 | | UADDI0 | 20 | 10 |
| UCMPI0 | 11 | 10 | | UADDI1 | 7 | 10 |
| ULINK_N14__0 | 2 | 3 | | UCMPI0 | 8 | 16 |
| ULINK_N14__1 | 1 | 3 | | UCMPI2 | 16 | 13 |
| ULINK_N7_UACK | 3 | 1 | | UCONTROL_MERGE1 | 2 | 1 |
| ULINK_N_FALSERESULT_9_SDELAY | 1 | 2 | | ULINK_N10__4_UACK | 1 | 2 |
| ULINK_N_INDEX_11 | 2 | 1 | | ULINK_N14__0 | 9 | 1 |
| ULINK_N_TRUERESULT_4_UACK | 2 | 1 | | ULINK_N_FALSERESULT_3_SDELAY | 3 | 1 |
| UMUX0 | 5 | 4 | | ULINK_N_FALSERESULT_3_UACK | 3 | 1 |
| UMUX1 | 4 | 2 | | ULINK_N_FALSERESULT_9_UACK | 5 | 4 |
| UMUX2 | 4 | 3 | | UMUX0 | 9 | 6 |
| USELECT0 | 6 | 4 | | UMUX1 | 6 | 2 |
| kernel links | 124 | 112 | | UMUX2 | 4 | 3 |
| | | | | USELECT0 | 9 | 5 |
| | | | | kernel links | 153 | 126 |

collatz / collatz64 with `CA_JOINAWARE=1`: not run here (time). The flag bounds no launch on these routes at either
corner, and CA_JOINAWARE does not change rule E's input, so ssja = ja is expected there; not measured.

## 5. Build and draws

**The build.** The auto loop's next sizes with the flag: `ratchet.py(sizes_4.vh, merged ss proposal, its negatives,
pinned.txt)` = sizes_4 with UCMPI1 18 -> 8, UCMPI0 7 -> 8, UADDIDEC0 5 -> 7, UCONTROL_MERGE0 1 -> 2, UMUX3 2 -> 6,
UMUX1 3 -> 2 (the same as without the flag except UCMPI1, which would be 17; the file is
`xorshift_sizes_auto_ss5_bench.vh` in this directory). Built as `auto_size.sh` build() / final()
(`LANE_NORUN=1 lane2.sh ... BDC_AUTO=1`, seed 1, then `lane2_run.sh`), RUNS under this subagent's directory:

| route | UCMPI1 | sdf | bit | P (event graph) | full stack |
|---|---|---|---|---|---|
| su_xorshift_1_4 (auto it 4, the bot's) | 18 | 694d657d | | 21084 ps | EQUIVALENT, ffmux-clean |
| **se_xorshift_ss_5** (this, seed 1) | 8 | 24f4dfb4 | 8fe0aba6 | **16620 ps** (35-arc cycle; trace.py agrees) | EQUIVALENT, ffmux-clean |
| hand recipe x55a10 (cand3b, 28 routes; brief / BOARD-QUEUE) | 5 (+ ULINK_N11__1 3) | | | ~16.8 ns | |

Draws (`bench_gate.sh draw:K`, xor19 + xor19.exp, the fixed verdict: every batch 2/2, runs agree, odata = the C's):

| route | draw | chains / rest / CARRY-F7-FF | verdict |
|---|---|---|---|
| se_xorshift_ss_5 | 10101 | 0.2299 / 0.2874 / 0.5261 | PASS 19/19, 5494 cycles |
| se_xorshift_ss_5 | 10102 | 0.2466 / 0.2342 / 0.3752 | PASS 19/19, 5494 cycles |
| se_xorshift_ss_5 | 10103 | 0.2079 / 0.2226 / 0.7103 | PASS 19/19, 5345 cycles |
| se_xorshift_ss_5 | 10104 | 0.2061 / 0.2688 / 0.4837 | PASS 19/19, 5384 cycles |
| su_xorshift_1_4 + 3 ns on ucmpi1's carry (slice[0] -> [1]; xray.sdf, `sdf_inject.py`) | 10101 | as above | PASS 19/19, 6780 cycles |
| su_xorshift_1_4, clean | 10101 | as above | PASS 19/19, 6780 cycles |
| su_xorshift_1_4 + 8 ns on ucmpi1's carry (slice[0] -> [1]) | 10101 | as above | PASS 19/19, 6780 cycles |
| su_xorshift_1_4 + 8 ns on ucmpi1's carry-out (slice[2] CO2 -> its LUT; reached the GLS SDF: ICBUF 8413 ps) | 10101 | as above | PASS 19/19, 6780 cycles |

The injected rows were meant as the GLS answer to the one control whose static verdict the flag changes (section 3:
+3 ns on the compare's carry, flagged by the base rule's laps at ucond_br8 / br9, -2390 / -1909, not by the flag).
PREDICTION written before they ran: +3 ns PASS. It passed -- but so did +8 ns, which both versions of the rule flag,
at either carry arc, with the cycle count of the clean route (6780) to the cycle. The reason is functional, not
timing: the carry chain computes g = (i > n), which is 0 on every iteration of every call (the loop runs while i < n
and exits at i == n, through the equality LUTs). Its arcs are on rule E's static longest select path and never toggle.
**So these draws do not discriminate and are not evidence for or against the flag.** A discriminating injection does not
exist on this route: every select arc that does toggle (the equality tree, uz_n41, the wires into the steers) is also on
the lap row's own request path -- the lap runs through the gate's own select pin -- so delaying it delays both sides of
the lap row. The lap row's margin is (lap loop: gate -> uack -> sibling C -> rdly -> join -> pin, 1984 ps at ucond_br8)
minus the select's own skew from the launch (latest 3220 - earliest 2114 = 1106 ps); UCMPI1 does not appear in it.

UADDI0 did not shrink (pinned at 8), so the preloaded counter (research/tools/preload) was not run.

**The rule on the new route** (both corners, report and full proposal, flag set and unset): NOT clean, and the
flag changes none of its negative rows (identical sets). 0.20 / 0.31: E ucond_br8 (both LUTs) -267 / -527 from
`ulink_n7f__1.ctl` (a C-node row: req 4709, sel 4694, raw +15 at 0.20), A' ucmpi1 - / -207, A'm umux1 -503 / -646
(UMUX1 3 -> 2 at it 4, in both configurations), E umux0 / umux3 joins -117 .. -215, A' uxori2 - / -157, H / I rows -9 ..
-152. The flagged rule's proposal on it pads UCMPI1 8 -> 10 (0.20) / 11 (0.31) for that E row; the ratchet's next
sizes would pin UCMPI1 at 11 (and raise UMUX1 2 -> 6, UXORI2 4 -> 5, ULINK_N12__0 1 -> 3, three 1 -> 2). Not built.
So with the flag the loop's UCMPI1 lands near 10-11 on this seed, not at 8, and not at the hand's 5.

## 6. What this does NOT show

- **It does not make rule E agree with the draws or with formal at the loop steers.** On the hand recipe's own route
  (bq_x55a10_21, UCMPI1 5, ULINK_N11__1 3) rule E is negative at all four loop steers with and without the flag
  (0.20: -929 / -211 / -421 / -483; 0.31: -1189 / -382 / -580 / -691; launch `ulink_n7f__1.ctl`, the compare's other
  operand), where formal C48 measures 923 ps (CARRY 1.0) / 1465 ps (CARRY 0.20) of settle at chains 0.20 / rest 0.31 on
  the same seed-21 route and 200 / 200 draws pass on 28 routes; on this subagent's route (UCMPI1 8) E is -267 / -527
  at ucond_br8 and 4 / 4 draws pass. What E still cannot credit, structurally, is a join's OTHER input from a launch
  that does not reach it: from i's C node, ucmpi1's operand join is seeded with i's request alone (n's request, 3
  elements later in the hand recipe, is not reached), and the steer's join with the compare's request alone (the
  steered token's request, e.g. uaddi0's 12-element chain into ucond_br6 in the hand recipe, is not reached). Which of
  these makes the real firing later on these routes is not measured here; formal's settle numbers say something does.
  That is formal B3's "the later request covers every input's data", which `CA_JOINAWARE=1`'s sibling credit models
  for A'j only. Rule E's C-node rows are what bind UCMPI1 at 10-11 on the new route.
- One route per kernel for the proposals (static), one build (seed 1), 4 draws on it, and 4 draws (1 clean, 3
  injected) on the AUTO route: no routed claim over seeds (CLAUDE.md asks >= 4); P 16620 is one route's number, though the change (-4.5 ns)
  is an order above routing scatter.
- The bound assumes what it cannot see: the 4-phase discipline of the cells (the select source's C node rises only
  after every loop steer's join has returned to zero, through ucmpi1's acknowledge C-tree) and rule H at the select's
  source link (its latch data held while open). Those are checked by other rules (H, the cells' formal checks), not
  by E.
- Only the lap that starts at the select source link's latch output and ends in the steer's join is removed; laps
  from other launches, and every mux join, are as before. The chain test (pins inside the link and the producer, the
  producer's own operand join, its request output) is structural and was exercised on xorshift (the bound is the later
  at 32 / 28 latch launches of the 16 steer gates on su_xorshift_1_4 at 0.20 / 0.31, 2 on the new route), collatz and
  collatz64 (computed at 12 gates, never the later);
  a select fed straight from a link's latch (the producer-less branch) occurs in none of these kernels' steers, so
  that branch is covered by the unit test only.
- No GLS run separates the two rules (section 5: the injection points that separate them never toggle with xor19 /
  any xorshift input, since i never exceeds n). The case for the flag rests on the 4-phase argument of section 2 and on
  the structure of the row (section 1), not on a simulation that failed under one rule and passed under the other.
- No board run. Simulation is not silicon (CLAUDE.md).
- CPU note: for ~10 min the first injected draw ran beside the 4-draw series and two audit queues (a wait loop matched
  nothing), i.e. 4 processes on the 3 cores of the brief; results unaffected (deterministic simulations).

## Commands

```
# rule E alone, verbose (the flag: env or --steer-self)
BD_SKEW_AND_JOIN=1 BD_SKEW_STEER_SELF=1 python3 cells/verify/skew.py CA/rule_0.20/soak.sdf -v
# the rule as auto_size.sh, plus the flag
BD_SKEW_AND_JOIN=1 CA_SIZERULE=1 BD_SKEW_STEER_SELF=1 CA_JOBS=3 python3 research/tools/corner_audit.py CA/seed1 \
  --prefix bridge_i.udut. --band 0.20 --inst-rx '\.chain\.g\[\d+\]\.u$:0.20' --out CA/ss_0.20      # and --band 0.31
python3 research/tools/auto/merge_rules.py CA/ss_merged CA/ss_0.20 CA/ss_0.31
python3 research/tools/auto/ratchet.py sizes_4.vh CA/ss_merged/sizes.vh CA/ss_merged/negative_sized.tsv sizes_5.vh pinned.txt
# the build (as auto_size.sh build() / final())
LANE_NORUN=1 research/tools/fifteen/lane2.sh se1 se_xorshift_ss_5 xorshift /abs/sizes_5.vh 1 /abs/vec_xorshift.hex BDC_AUTO=1
research/tools/fifteen/lane2_run.sh se_xorshift_ss_5 xorshift /abs/vec_xorshift.hex BDC_AUTO=1
research/tools/eventgraph/bench_gate.sh HW xorshift_bench_gen W research/data/eventgraph/gate/xor19.hex .../xor19.exp draw:K
# controls: a line at 1 (worker, chain arcs scaled), an injected arc
python3 research/tools/corner_audit.py --_worker SDF '{"a_frac": 0.03, "a_min": 50, "glo": 0.97, "ghi": 1.03,
  "drop_const": true, "rule_a_link": false, "osc": [], "cut": [], "drop": [], "scale": {"bridge_i.udut.ucmpi1.udly": 0.0556}}'
python3 research/tools/fifteen/sdf_inject.py IN.sdf OUT.sdf 'ucmpi1\..*slice\[0\]\.genblk1\.carry4/CO3$' \
  'ucmpi1\..*slice\[1\]\.genblk1\.carry4/CIN$' 3000
```
