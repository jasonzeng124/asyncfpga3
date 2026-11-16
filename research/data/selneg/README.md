# Select negative controls, every kernel family (2026-11-16)

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
