# C-12d: the track-12 tool results redone at one consistent corner (and with the corner model)

Shard C, probe 12d, 2026-10-29. Files (mine): `formal/tools/smt/run_onecorner.py`,
`formal/tools/smt/arb.py` (tx monitor, separate O5 arc), `formal/tools/async/onecorner.py`,
`formal/tools/zone/{onecorner,celem1c,witness1c}.py`, `formal/tools/grantfork/kappa.py`,
this note, and dated correction sections in C-12a-smt.md, C-12b-async-tools.md,
C-12c-zone.md and C-10i-grantfork.md. No Lean (see "Lean" below for why).

STATUS: DRAFT, runs still in progress (sections marked PENDING).

## The problem

12a (z3), 12b (Storm) and 12c (TChecker) took the LUT arcs from `cells/sim/bd_prims_sim.v`
as "O6 rise 56 / fall 124, O5 rise 52 / fall 150 (or 28)". prjxray SDF triples are
`(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)` (`prjxray/utils/makesdf.py:63`): 56 and 124 are
the FAST_MAX and SLOW_MAX of ONE arc. prjxray-db has no rise/fall split. The O5 "fall 28 ps"
of 12b/12c has no prjxray source at all (it came from the header's zero-routing trace).
So every arbiter threshold those probes derived from the asymmetry is suspect.

## Corners used here (every arc, both edges, ps)

prjxray `CLBLL_L.sdf` (the table in B-arb-corners.md):

| arc | FAST_MIN | FAST_MAX | SLOW_MIN | SLOW_MAX |
|---|---|---|---|---|
| A6LUT -> O6 (flat over pins): q, g2, A1, A2 | 45 | 56 | 100 | 124 |
| A5LUT -> O5 (union over I0..I2): R0, g1 | 42 | 55 | 121 | 152 |

Readings, all with rise = fall (one interval per output, drawn independently per
transition, so an interval row also allows rise != fall INSIDE one corner's band -- a
superset of the auditor's rise = fall points):
- **FAST** = every arc in [FAST_MIN, FAST_MAX]; **SLOW** = every arc in [SLOW_MIN, SLOW_MAX].
- **points**: FASTp (FAST_MAX: O6 56, O5 52 = the q pin), SLOWp (SLOW_MAX: 124/150),
  FMINp (FAST_MIN: 45/42). Exactly rise = fall.
- **corner model** (A's `Formal/Core/Delay/Corner.lean`: shared corner c in [0,1], local
  scatter kappa, `Scat`), in B-arb-kappa's two readings:
  - `lit`: F = FAST_MIN, S = SLOW_MAX, d in [(1-k) D(c), (1+k) D(c)], D(c) = lerp(F, S, c);
  - `cons`: d in [(1-k) lerp(FMIN, SMIN, c), (1+k) lerp(FMAX, SMAX, c)] (k = 0 gives FAST/SLOW).
  - kappa: rule A's 1/11 and rule E's 383/1927 = 0.1988 (the 0.772/1.155 guardband). A has
    no measured kappa (A-kappa.md correction); these are the two limits the shipped rules are
    proved sound for. c in {0, 0.5, 1}.
  - Name scheme in the logs: `cons0k11` = cons, c = 0, k = 1/11; `lit1kE` = lit, c = 1, k = 0.1988.

## Results per tool per corner

PENDING (filled below as runs land).
