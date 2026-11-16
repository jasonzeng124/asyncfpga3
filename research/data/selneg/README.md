# Select negative controls, every kernel family (2026-11-16)

**CORRECTION (2026-11-16, later): the request-JOIN injections below do not fail for the reason they seemed to.** Traced on
collatz item 28's route, umux0, +3000, FAST_MIN (`fullstack_dump.sh` with XRAY_SDF_IN, `vcd_last.py`): the select link's
latch has no reset, so in simulation its output is X from time 0 until the first token. The first ctl_req reaches the
join pin at 1.648 us while the late select pin still carries that power-up X (it turns 0 at 1.650 us); the join's
C-element LUT (j0) outputs X, holds it through its own feedback, and X spreads through the handshakes: "no
completion". On silicon the latch powers up 0 or 1, and at a loop-header mux a stale select only delays the join (the
other request is never pending). Formal's C17 (no failure for any join injection, transport model from a defined
state) agrees. So the 20 join-injection failures are X-propagation from an uninitialized latch, not the select race:
**rule E has no genuine known-bad build here.** Confirmed with a defined start-up (GLS +META_INIT=0 and =1, cells/gls/
fid_core.vh): the same collatz umux0 join +3000 run PASSES 13/13 (2913 cycles vs 2906 clean); the data-LUT +8000 run still
FAILS (7/13); the clean route is unchanged. Farm selneg3 re-runs the join injections that way. The 2026-11-15 HOLD control
(fcsel0 s24, +15000 on ulink_n14__1 stage[1]'s enable) with +META_INIT=0: FAIL 1/13 with every batch complete -- a real
wrong-value failure, flagged by rule H (-14260 ps). The data-LUT injections (rule M, second table) fail as real logic
(three wrong values) and are not affected the same way: traced on collatz umux1, +8000, FAST_MIN (tr_c28u1d), batches 0-4
give X (the same power-up X, now in the data), but batches 8 and 9 give DEFINED wrong answers (0x0a for 0x06, 0x0c for
0x08) while 5-7 and 10-12 are right: the late select lets the mux's data output change after its request, and the
downstream latch keeps the wrong input's value. Rule M's known-bad builds are real.


PROGRAM "A check earns its place by failing": before a result rests on the select checks, show them fail on a raced
select in each kernel family. No select link shortened to 0 ever made a gate fail (2026-11-15, 4 families x ~30 routes),
so the race is constructed: on each family's board-candidate route, the select latch's output arcs into ONE mux's
request joins (umuxN.uj0 / uj1) are made late by +3000 / +6000 / +12000 ps in the prjxray SDF only (same netlist and bits;
`research/tools/fifteen/sdf_inject.py`). Then rule E (corner_audit, worst and nominal) and the full gate (bench_gate.sh,
50 min limit; a clean run takes ~9-10). Farm requests `selneg` (+3000, three corners) and `selneg2` (+6000 / +12000,
FAST_MIN and worst), `research/cluster/requests/`. "no completion": no batch finished in the limit (the clean route
finishes all in ~9 min; locally checked on collatz umux0 +3000: no batch in 71 CPU-min, killed).

| route, mux | inj | rule E worst / nom (ps; '-' = no row < 0) | gate FAST_MIN | gate worst | gate SLOW_MAX |
|---|---|---|---|---|---|
| xorshift item 27 s2, umux0 | +3000 | -1753 / -1566 | PASS 17/17 | PASS 17/17 | PASS 17/17 |
| xorshift item 27 s2, umux0 | +6000 | -4843 / -4656 | no completion | no completion | -- |
| xorshift item 27 s2, umux0 | +12000 | -11023 / -10836 | no completion | no completion | -- |
| xorshift item 27 s2, umux1 | +3000 | -318 / -21 | PASS 17/17 | PASS 17/17 | PASS 17/17 |
| xorshift item 27 s2, umux1 | +6000 | -3408 / -3111 | FAIL 16/17 | no completion | -- |
| xorshift item 27 s2, umux1 | +12000 | -9588 / -9291 | no completion | no completion | -- |
| xorshift item 27 s2, umux2 | +3000 | -1333 / -1129 | no completion | PASS 17/17 | PASS 17/17 |
| xorshift item 27 s2, umux2 | +6000 | -4423 / -4219 | no completion | no completion | -- |
| xorshift item 27 s2, umux2 | +12000 | -10603 / -10399 | no completion | no completion | -- |
| xorshift item 27 s2, umux3 | +3000 | -1527 / -1359 | PASS 17/17 | PASS 17/17 | PASS 17/17 |
| xorshift item 27 s2, umux3 | +6000 | -4617 / -4449 | PASS 17/17 | PASS 17/17 | -- |
| xorshift item 27 s2, umux3 | +12000 | -10797 / -10629 | PASS 17/17 | PASS 17/17 | -- |
| collatz64 item 26 s25, umux0 | +6000 | -826 / -210 | no completion | PASS 14/14 | -- |
| collatz64 item 26 s25, umux0 | +12000 | -7006 / -6390 | no completion | no completion | -- |
| collatz64 item 26 s25, umux1 | +3000 | - / - | PASS 14/14 | PASS 14/14 | PASS 14/14 |
| collatz64 item 26 s25, umux1 | +6000 | - / - | PASS 14/14 | PASS 14/14 | -- |
| collatz64 item 26 s25, umux1 | +12000 | -5778 / -5079 | no completion | no completion | -- |
| collatz64 item 26 s25, umux2 | +3000 | - / - | PASS 14/14 | PASS 14/14 | PASS 14/14 |
| collatz64 item 26 s25, umux2 | +6000 | -1148 / -603 | PASS 14/14 | PASS 14/14 | -- |
| collatz64 item 26 s25, umux2 | +12000 | -7328 / -6783 | PASS 14/14 | PASS 14/14 | -- |
| ipow item 19 s1, umux0 | +3000 | - / - | PASS 17/17 | PASS 17/17 | PASS 17/17 |
| ipow item 19 s1, umux0 | +6000 | -514 / - | no completion | PASS 17/17 | -- |
| ipow item 19 s1, umux0 | +12000 | -6694 / -6069 | no completion | no completion | -- |
| ipow item 19 s1, umux1 | +3000 | -754 / -484 | no completion | PASS 17/17 | PASS 17/17 |
| ipow item 19 s1, umux2 | +3000 | - / - | PASS 17/17 | PASS 17/17 | PASS 17/17 |
| ipow item 19 s1, umux2 | +6000 | - / - | PASS 17/17 | PASS 17/17 | -- |
| ipow item 19 s1, umux2 | +12000 | -3805 / -2820 | no completion | PASS 17/17 | -- |
| ipow item 19 s1, umux3 | +3000 | - / - | PASS 17/17 | PASS 17/17 | PASS 17/17 |
| ipow item 19 s1, umux3 | +6000 | -2948 / -2572 | PASS 17/17 | PASS 17/17 | -- |
| ipow item 19 s1, umux3 | +12000 | -9128 / -8752 | PASS 17/17 | PASS 17/17 | -- |
| collatz item 28 s20, umux0 | +3000 | -1952 / -1845 | no completion | no completion | PASS 13/13 |
| collatz item 28 s20, umux0 | +6000 | -5042 / -4935 | no completion | no completion | -- |
| collatz item 28 s20, umux0 | +12000 | -11222 / -11115 | no completion | no completion | -- |
| collatz item 28 s20, umux1 | +3000 | -1951 / -1824 | no completion | PASS 13/13 | PASS 13/13 |
| collatz item 28 s20, umux1 | +6000 | -5041 / -4914 | no completion | no completion | -- |
| collatz item 28 s20, umux1 | +12000 | -11221 / -11094 | no completion | no completion | -- |
| collatz item 28 s20, umux2 | +3000 | -2079 / -1962 | PASS 13/13 | PASS 13/13 | PASS 13/13 |
| collatz item 28 s20, umux2 | +6000 | -5169 / -5052 | PASS 13/13 | PASS 13/13 | -- |
| collatz item 28 s20, umux2 | +12000 | -11349 / -11232 | PASS 13/13 | PASS 13/13 | -- |

runs with a gate failure: 20; E flagged 20, E clean 0; E flagged but every gate passed: 12

Reading:
- Every one of the 20 runs whose gate failed (no completion, or a wrong value: xorshift umux1 +6000, 16/17) had a rule E
  row below 0 at the worst corner. Rule E fails on every known-bad build here, on all four families.
- E is conservative: 12 runs flagged by E passed every gate. At loop-header muxes (xorshift umux3, collatz umux2,
  collatz64 umux2, ipow umux3) even +12000 ps passes: the select changes only at loop entry / exit, and only one of the
  two requests is ever pending, so a late select arms a join that has no request yet. E compares the select with the
  select link's own request and cannot see that.
- Missing: collatz64 umux0 +3000 (farm container error), ipow umux1 +6000 / +12000 (selneg2 task 9 not back).
- Not covered by these runs: the hold half of the select race (rules H / I, hold_bits, TSE; collatz's +15000 ps
  enable injection on 2026-11-15 is the only hold control), and the select's path to the mux's DATA LUTs (rule M,
  corner_audit 2026-11-16; its own control is in the journal).

## Rule M (the mux data outputs), the same construction (farm mneg, 2026-11-16)
Late arcs: the select latch ('<select link>.lat.odd.u') into ONE mux's DATA LUTs (umuxN.udat.*), +4000 / +8000 ps, SDF
only. Rule M = corner_audit's A rows marked "peers no common source reaches" (the mux's data outputs against z_req,
measured from every upstream link's C node). The injected mux's M value is shown; "-" = no M row for that mux.

| route, mux | inj | rule M on that mux, worst / nom | rule E rows < 0 | gate FAST_MIN | gate worst |
|---|---|---|---|---|---|
| xorshift item 27 s2, umux0 | +4000 | -1643 / -1343 | 0 | PASS 17/17 | PASS 17/17 |
| xorshift item 27 s2, umux0 | +8000 | -5763 / -5463 | 0 | no completion | no completion |
| xorshift item 27 s2, umux1 | +4000 | -788 / -377 | 0 | PASS 17/17 | PASS 17/17 |
| xorshift item 27 s2, umux1 | +8000 | -4908 / -4497 | 0 | FAIL 2/17 | PASS 17/17 |
| xorshift item 27 s2, umux2 | +4000 | -2033 / -1738 | 0 | PASS 17/17 | PASS 17/17 |
| xorshift item 27 s2, umux2 | +8000 | -6153 / -5858 | 0 | no completion | no completion |
| xorshift item 27 s2, umux3 | +4000 | - / - | 0 | PASS 17/17 | PASS 17/17 |
| xorshift item 27 s2, umux3 | +8000 | - / - | 0 | PASS 17/17 | PASS 17/17 |
| collatz64 item 26 s25, umux1 | +4000 | 942 / 1180 | 0 | PASS 14/14 | PASS 14/14 |
| collatz64 item 26 s25, umux1 | +8000 | 942 / 1180 | 0 | PASS 14/14 | PASS 14/14 |
| collatz64 item 26 s25, umux2 | +4000 | - / - | 0 | PASS 14/14 | PASS 14/14 |
| collatz64 item 26 s25, umux2 | +8000 | - / - | 0 | PASS 14/14 | PASS 14/14 |
| ipow item 19 s1, umux0 | +4000 | 1604 / 1911 | 0 | PASS 17/17 | PASS 17/17 |
| ipow item 19 s1, umux0 | +8000 | 73 / 1024 | 0 | PASS 17/17 | PASS 17/17 |
| ipow item 19 s1, umux1 | +4000 | 1133 / 1831 | 0 | PASS 17/17 | PASS 17/17 |
| ipow item 19 s1, umux1 | +8000 | -2987 / -2289 | 0 | FAIL 14/17 | PASS 17/17 |
| ipow item 19 s1, umux2 | +4000 | -532 / -448 | 0 | PASS 17/17 | PASS 17/17 |
| ipow item 19 s1, umux2 | +8000 | -532 / -448 | 0 | PASS 17/17 | PASS 17/17 |
| ipow item 19 s1, umux3 | +4000 | - / - | 0 | PASS 17/17 | PASS 17/17 |
| ipow item 19 s1, umux3 | +8000 | - / - | 0 | PASS 17/17 | PASS 17/17 |
| collatz item 28 s20, umux0 | +4000 | -1383 / -1043 | 0 | PASS 13/13 | PASS 13/13 |
| collatz item 28 s20, umux0 | +8000 | -5503 / -5163 | 0 | no completion | PASS 13/13 |
| collatz item 28 s20, umux1 | +4000 | -1691 / -1380 | 0 | PASS 13/13 | PASS 13/13 |
| collatz item 28 s20, umux1 | +8000 | -5811 / -5500 | 0 | FAIL 6/13 | PASS 13/13 |
| collatz item 28 s20, umux2 | +4000 | - / - | 0 | PASS 13/13 | PASS 13/13 |
| collatz item 28 s20, umux2 | +8000 | - / - | 0 | PASS 13/13 | PASS 13/13 |

runs with a gate failure: 6; rule M below 0 on the injected mux in 6 of them; M below 0 but every gate passed: 7

Reading: all 6 gate failures (3 wrong values: xorshift umux1 2/17, ipow umux1 14/17, collatz umux1 6/13; 3 no
completion) have rule M below 0 on the injected mux, and rule E has no row below 0 in ANY of these runs: the select's
path to the data LUTs is a race E does not model. M is stricter than the gate on 7 runs (all at +4000, or on muxes the
vectors exercise only at loop entry). Where M stayed >= 0 (the injection absorbed by a long mux delay: collatz64 umux1,
ipow umux0, umux1 at +4000) every gate passed. collatz64 umux0 (task 5 failed on the farm twice, container error) run locally on item 30's route (c64s3_10), +8000 on the
select latch -> umux0.udat (64 arcs): rule M -7528 ps at worst, rule E clean, gate FAST_MIN no batch in 55 min (the clean
route: PASS 14/14 in 25 min). As a no-completion it may carry the start-up X (see the correction above); not traced.

## The join injections again, with a defined start-up (farm selneg3, 2026-11-16)
selneg2's arcs (select latch -> umuxN.uj0 / uj1), +6000 and +12000 ps, gate at FAST_MIN and worst with +META_INIT=0
(cells/gls/fid_core.vh). 11 muxes back (xorshift item 27 umux0-3, collatz64 item 26 umux0 / umux2, ipow item 19 umux1-3,
collatz item 28 umux1 / umux2): **44 gate runs, 44 PASS**. Every "failure" of selneg / selneg2 on these muxes was the
start-up X. On these kernels a select late at the request join, by up to 12 ns, only delays the token.

## Rule E at a steer (local, 2026-11-16; farm steerneg partly back)
Item 28's route, the loop steer ucond_br7: its condition (ucmpi2.uz_n36 -> ucond_br7.u$LUT5 / $LUT6 A3) +8000 ps, SDF
only, gate FAST_MIN with +META_INIT=0 (no start-up X): no batch completed in 50 min (clean route: 9 min). Rule E at
ucond_br7: -5048 ps at worst. A condition that arrives after the request at a combinational steer loses the token: rule E
has a failing build here, unlike at the mux joins. Not traced (the hang may still contain a non-start-up X). Farm
steerneg (every steer, +3000 / +8000): the first two back, xorshift ucond_br3 and collatz ucond_br4, passed every gate
at both sizes with E -0.3 .. -6.1 ns (steers whose condition is settled long before the next request).
Two more loop steers, local, same construction (condition +8000 ps, gate FAST_MIN with +META_INIT=0):
| route, steer | rule E at the steer (worst) | gate FAST_MIN |
|---|---|---|
| xorshift item 27 (x27_2), ucond_br9 | -7266 | no batch in 50 min |
| collatz64 item 30 (c64s3_10), ucond_br6 | -6276 | no batch in 55 min (clean route: 25 min) |
| collatz item 28 (c28_20), ucond_br7 | -5048 | no batch in 50 min (clean: 9 min) |
| ipow item 29 (ip29_19, sdf b521630f), ucond_br9 | -3238 | no batch in 50 min (clean route: PASS 17/17 in 6.7 min) |
So rule E fails on a known-bad build at the steers of all four families.
Traced (collatz ucond_br7, +8000, +META_INIT=0, tr_st7): no kernel net is X at any time after 10 ns, all 1415 kernel nets
end defined, and kernel activity stops at 3.945 us: a true deadlock (the token steered the wrong way), not an artefact.

## Farm steerneg complete (2026-11-16 18:44 UTC push): every steer of the four board routes
Every arc into ONE steer's own LUTs (ucond_brK.u$LUT5 / $LUT6; not its join) +3000 / +8000 ps, SDF only; gate with
+META_INIT=0, 50-min limit ("none" = no batch in the limit). Rule E at that steer, worst corner. "entry" = condition from
ucmpi0 (the loop-entry test, evaluated once per call); "loop" = from the loop's compare.

| route | steer | kind | E +3000 / +8000 | gate +3000 min / worst | gate +8000 min / worst |
|---|---|---|---|---|---|
| xorshift item 27 s2 | ucond_br2 / 3 / 4 | entry (data) | -776..-325 / -5926..-5475 | PASS / PASS | PASS / PASS |
| xorshift item 27 s2 | ucond_br5 | entry (control) | -826 / -5976 | PASS / PASS | none / none |
| xorshift item 27 s2 | ucond_br6 | loop (ucmpi1) | -2051 / -7201 | none / PASS | FAIL 3/17 / none |
| xorshift item 27 s2 | ucond_br7 | loop | -1689 / -6839 | none / PASS | FAIL 2/17 / none |
| xorshift item 27 s2 | ucond_br8 / 9 | loop | -1867, -2116 / -7017, -7266 | none / PASS | none / none |
| collatz64 item 26 s25 | ucond_br2 / 3 / 4 | entry | -228..-40 / -5378..-5190 | PASS / PASS | PASS / PASS |
| collatz64 item 26 s25 | ucond_br5 | loop | -1130 / -6280 | none / PASS | none / none |
| collatz64 item 26 s25 | ucond_br6 | loop | -1711 / -6861 | none / none | none / none |
| collatz64 item 26 s25 | ucond_br7 | loop | -1679 / -6829 | PASS / PASS | PASS / PASS |
| ipow item 19 s1 | ucond_br2 / 3 / 4 | entry | - / -4749..-4154 | PASS / PASS | PASS / PASS |
| ipow item 19 s1 | ucond_br5 | entry (control) | - / -4534 | PASS / PASS | none / PASS |
| ipow item 19 s1 | ucond_br7 | loop | - / -2653 | PASS / PASS | FAIL 3/17 / none |
| ipow item 19 s1 | ucond_br8 / 9 | loop | - / -2488, -2679 | PASS / PASS | none / PASS |
| collatz item 28 s20 | ucond_br2 / 3 / 4 | entry | -1807..-968 / -6957..-6118 | PASS / PASS | PASS / PASS |
| collatz item 28 s20 | ucond_br5 / 6 | loop | - / -5103, -4818 | none / PASS | none / none |
| collatz item 28 s20 | ucond_br7 | loop | - / -5048 | PASS / PASS | none / PASS |
(ipow ucond_br6 task did not run; collatz64 / xorshift / ipow / collatz tasks past the last steer had no steer.)

Reading: of 26 steers, 14 (every loop steer but collatz64's ucond_br7, plus xorshift's entry control steer) fail the
gate at +8000 with E < 0: rule E at steers has failing builds on all four families. The 12 that pass at +8000 with E at
-4 to -7 ns are the entry DATA steers (12/12) and collatz64 ucond_br7. For collatz and collatz64 the reason is the vectors:
col13 / c6414 have no n = 1, so the entry condition is true on every call and a late condition shows the same value. That
is a full-range coverage gap in the gate (collatz(1) = 0 is a legal input): farm zt1 re-gates items 28 / 31 / 30 / 32 with
n = 1 added (col14, c6415) and repeats the entry-steer injection on both vector sets. xorshift (rounds = 0) and ipow
(b = 0) vectors do include a zero-trip call, and their entry data steers still pass: not yet explained (traced next).

**CORRECTION (2026-11-16, later): the 12 "passes" at the entry steers were the gate's blind spot.** bench_gate.sh read
only the last of each batch's two runs. Traced on xorshift item 27 (ucond_br2/3/4 +8000, FAST_MIN): the steer does
mis-steer, both branches get the token, and from then on every batch's first run returns the previous call's answer
(the run-to-run mismatch latch was set on 16 of 19 batches). Five of steerneg's PASS runs had that latch set. The gate
now fails such batches. PROGRAM (owner, 2026-11-16) closes the question of which static rule earns its place; these
tables stay as record.
