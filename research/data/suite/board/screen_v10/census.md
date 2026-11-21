# Steer-tolerance census of flow v10's suite routes (research/data/suite/board/suite_v10, item 44's routes; 2026-11-21)

Two measures of how much path error each route's select gates (steers, mux selects) tolerate before a request can beat
its select -- formal B24's "x": the request walk -x against the select's cone +x, at research's bands.

1. **Rule E's own arrivals** (research/tools/steer_tol.py on corner_audit's skew.log, flow v10's environment, bands 0.20
   and 0.31, every route as built): x = (req - sel) / (req + sel - 2 div) per gate, the weakest over both bands. A
   bound: the earliest request against the latest select over every path and launch. All 46 routes (6 have no select
   gate). census_table.md.
2. **Formal's B24 screen** (racescreen.sh at claude/formal 36ba04ea34: steersafe bounds, the latch-fed race adversary,
   xtol.sh = a simulation of the weakest steer by formal's kappa with the path error applied): 19 non-memory routes
   (formal's bench boundary does not take memory vectors yet). census_racescreen.txt.

The flow sizes rule E with 0.97 / 1.03 at the band corners (x = 0.03: corner_audit's residual guard, "the measured
within-die scatter, not the band"); formal's guide calls a route fine with no pulses at x <= 0.10.

| x by rule E (weakest gate) | routes | formal's screen on those it can run |
|---|---|---|
| < 0.07 | fill 0.045, collatz64 0.047, twoloops 0.047, if_loop_2 0.054, dot2 0.055, sqrtsub 0.057, lfsrfind 0.062 | collatz64 pulses 0.08 / fail 0.15; sqrtsub pulses and fail 0.10; lfsrfind pulses and fail 0.12 (and a negative steer bound, -59 ps); twoloops none to 0.25 (its xtol ran another steer) |
| 0.07 - 0.10 | varshift 0.069 (a mux), nested_loop, single_loop, memsum, test_memory_2, fold64 0.088, branchloop 0.089, vector_rescale (a mux), quadrec 0.094, horner 0.097 | fold64 0.20, branchloop 0.15 / 0.20, quadrec none, horner 0.20, varshift none |
| >= 0.10 | 22 routes incl. collatz 0.108, xorshift 0.131, ipow 0.180, countloop 0.183 | none below 0.15 |

Reading: the rule's x is a conservative bound (formal's simulated tolerance sits above it on every route where both
ran), and the three routes formal calls thin are the rule's 0.047-0.062. About 17 of the 40 routes with a select gate
are below x = 0.10 by the rule; 3 of 19 screened are below formal's 0.10-0.12 in simulation. Every one of these routes
passed its draws (4 / 4) and the rule's own 3 % guard. Whether 3 % is enough on silicon is what item 44 can show: its
46 routes span x = 0.045-0.42, so a failure concentrated on the low-x routes would say the steers need a wider guard
(research/tools/auto/auto_size.sh AUTO_GUARD_E=0.90,1.10, cost ~2 elements on a loop test: research/data/guardx/).
Other findings: twoloops' latch-fed race (ucond_br17, +222 / +577 ps) fails formal's race-only adversary at kappa 0.15;
divmodu: formal's own draws give wrong results on all 4 (garbage, not near misses) where our GLS passes the same bits
-- most likely its divider in formal's model; asked (FOR-FORMAL); test_int16 crashed the screen (no steers).

**Formal B29 (2026-11-21, on this census's x):** xtol puts +x on every arc of the condition cone and -x on every arc of
the request walk -- a fully correlated, adversarial path error, with no within-die model in it; formal's 0.10 line is
a judgement. "First pulses" counts benign transparent-latch glitches; only "first failure" measures a hazard. By first
failure the thin routes are sqrtsub (x = 0.10), lfsrfind (0.12), collatz64 (0.15); then branchloop (0.20), collatz
(0.25); divmodu's 0.00 is formal's model of its divider (asked). B29 also bounds collatz's ucond_br7 (0.110).
