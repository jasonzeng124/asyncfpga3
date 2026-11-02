# R5 vs R5 x1.25 (gcd_hw, BQ#2 flags): speed and log-normal scatter margin (2026-11-02)

`research/data/gcd_hw_sizes_R5x125.vh` = every R5 size x1.25 rounded up (lengthening only). Full stack (bit-decoded
netlist, prjxray SDF, fid). Laps on vectors 6/12/13 per 150 us window; seeds_fid results rows in the two .tsv files.
R5x1.25 seed 6 did not place (nextpnr post-placement validity check); seed 9 has a rule A -32 ps flag; seeds 7, 8, 10
every audit clean. R5 seeds 7-10: every audit clean (BOARD-QUEUE #2).

| seed | R5 SLOW_MAX | R5x1.25 SLOW_MAX | vec 6 | R5 logn 2x d1 | R5x1.25 logn 2x d1 | R5 logn 3x d1 | R5x1.25 logn 3x d1 |
|---|---|---|---|---|---|---|---|
| 6 | 33/27/39 | (no placement) | - | FAIL errs 3 | - | - | - |
| 7 | 31/25/36 | 28/22/33 | -10% | PASS 51/39/58 | PASS 50/40/58 | PASS 47/36/53 | PASS 44/34/50 |
| 8 | 31/25/37 | 29/23/34 | -6% | PASS 41/32/48 | PASS 35/28/42 | PASS 34/26/39 | PASS 28/22/34 |
| 9 | 31/25/36 | 28/23/33 | -10% | PASS 45/36/53 | PASS 33/26/39 | PASS 39/31/46 | PASS 26/20/31 |
| 10 | 31/25/36 | 26/21/31 | -16% | PASS 44/35/53 | PASS 38/29/46 | **FAIL errs 4** (vec 2,3,9,15) | PASS 32/25/39 |

Mean SLOW_MAX vec 6 on seeds 7-10: R5 31.0, R5x1.25 27.75 (-10.5%). On seeds 7-10: log-normal 2x draw 1, both 4/4;
3x draw 1, R5 3/4 (seed 10 fails on vectors 2, 3, 9, 15, the uori2 signature of BQ#3 seed 9) and R5x1.25 4/4.
Reading: x1.25 removed the one scatter failure seen on these routes, for 10.5% of SLOW_MAX speed. One failure in
eight scatter runs per arm is thin evidence; it says "failures are rare and route-specific, and a uniform 25% pad
covered the one seen", not a failure rate.
