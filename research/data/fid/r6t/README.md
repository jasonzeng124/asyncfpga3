# R6t: R5 with only uori2/uori3 x1.25 (gcd_hw, BQ#2 flags), 2026-11-02/03

`research/data/gcd_hw_sizes_R6t.vh`: uori2 19 -> 24, uori3 20 -> 25 links; everything else R5. Full stack (bit-decoded
netlist, prjxray SDF, fid). Laps on vectors 6/12/13 per 150 us window.

| seed | audits | SLOW_MAX | log-normal 3x draw 1 |
|---|---|---|---|
| 6 | clean | 30/24/35 | PASS 40/32/47 |
| 7 | clean | 30/24/35 | PASS 44/33/53 |
| 8 | clean | 32/26/37 | PASS 24/19/29 |
| 9 | clean | 30/24/35 | PASS 44/34/50 |
| 10 | clean | 32/26/37 | FAIL errs 7 (vectors 1,2,3,9,11,13,15) |

Compared with R5 (seeds 7-10: SLOW_MAX vec 6 mean 31.0; 3x draw 1 3/4, seed 10 fails) and R5x1.25 (27.75; 3x draw 1
4/4): R6t costs ~nothing at SLOW_MAX (mean 30.8 over 5 seeds) and places and audits clean on all 5, but fails 3x on 1
of 5 like R5. Rule A on the failing draw's scaled SDF lists 10 short bundles (`seed10_3x_scaled_ruleA_violations.txt`):
at 3x the shortfall is broad, so a targeted pad on the two chains seen failing at 2x does not remove it.
