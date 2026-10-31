# C-12d: the track-12 tool results redone at one consistent corner (and with the corner model)

Shard C, probe 12d, 2026-10-29. Files (mine):
- `formal/tools/smt/run_onecorner.py`, `formal/tools/smt/arb.py` (adds the 12b `tx`
  monitor and a separate O5 arc to `arbiter()`), results in `formal/tools/smt/results/onecorner_*.txt`;
- `formal/tools/async/onecorner.py` (Storm);
- `formal/tools/zone/onecorner.py`, `celem1c.py`, `witness1c.py`, `tpquick.py` (TChecker);
- `formal/tools/grantfork/kappa.py` (10i under the corner model);
- logs: `formal/tools/zone/results/*`, `formal/tools/async/results/onecorner.log`,
  `formal/tools/grantfork/results/kappa.log`. The stale `smt/results/onecorner_arbiter{2,3}.txt`
  from a lost earlier 12d run (`owner`-monitor artefacts) were removed;
- this note, and dated correction sections at the top of C-12a-smt.md,
  C-12b-async-tools.md, C-12c-zone.md and C-10i-grantfork.md.
- No Lean (see "Lean" at the end). `formal/lean/Wip/C12d/` is not created.

## Verdict

**Most of the old arbiter thresholds were corner-mix artefacts; the structural ones keep
their form with corner-dependent numbers; 10i was already corner-consistent.**

- **Artefacts** (they vanish at every consistent corner, κ = 0):
  - the "16 ps" bare-cell / UNHELD handover race (12a tb, 12b, 12c);
  - "server latency >= ~60 ps (exactly 56 ps)" for held ack exclusion (12b, 12c);
  - 12a's "early ack needs k >= 10" number;
  - UNHELD "ho/tx iff server >= 60-80 ps";
  - 12a's transport-route numbers: the aperture of 152 ps is 72 ps at FAST (bounded), SLOW
    needs none at 48 ps, and route 0 is clean to depth 60.
- **Same form, numbers per corner:**
  - A0-rise fork: breaks iff wa >= 2·O6lo + c_lo, i.e. 94 ps FAST, 204 ps SLOW; the old
    116 = FAST_MAX points;
  - q->ugrant route: mutex iff wq_g < 42 ps FAST, 100 ps SLOW; 56 at FAST_MAX points;
  - A0-fall fork: early ack iff late >= early + ua2 arc, i.e. k >= 8 units FAST, 14 SLOW
    (25 ps units);
  - C-element: e_lo vs feedback (never mixed corners).
- **New under the corner model** (scatter κ on top of one corner): a small held-arbiter
  ack-exclusion condition on the server latency, 2s >= max(2 h6, h5 + h6) - 2 l5 - l6. At
  s = 0 it holds iff κ <= 0.069-0.107 (cons reading) or 0.176-0.215 (lit reading).
- **H_GRANT_FORK (10i)** stays open on >= 57/80 routed instance-clients at κ = 0, and on
  73/80 at κ = 1/11.
- **Not re-established:** 12c's pure-delay "holds" rows (`*_nr`, ovf_nr = 0). At rise =
  fall their explorations no longer finish. The failing side (mutex_nr for any wq_g > 0;
  the A0-rise fork bound) is reproduced.
- **Effort:** about 3 h of work.
  - Tool time: TChecker plus Storm about 9 CPU-minutes for every arbiter question at 15 + 6
    corner settings; z3 about 2 CPU-hours (coarse BMC of the full arbiter, the aperture).
  - B's Lean redo of the same instances (ArbCorners) was a full probe.
- **Track 12:** the tools are good bound-finders and corner sweepers, but they carried the
  corner misreading silently because the delays are inputs to them.

## The problem

12a (z3), 12b (Storm) and 12c (TChecker) took the LUT arcs from
`cells/sim/bd_prims_sim.v` as one of:
- "O6 rise 56 / fall 124, O5 rise 52 / fall 150" (12a);
- "O6 rise 56 / fall 124, O5 rise 52 / fall 28" (12b, 12c).

prjxray SDF triples are `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`
(`prjxray/utils/makesdf.py:63`):
- 56 and 124 are the FAST_MAX and SLOW_MAX of ONE arc;
- prjxray-db has no rise/fall split;
- the O5 "fall 28 ps" has no prjxray source at all. It is the header's zero-routing trace.

## Corners used here (every arc, both edges, ps)

prjxray `CLBLL_L.sdf`, as tabulated in B-arb-corners.md:

| arc | FAST_MIN | FAST_MAX | SLOW_MIN | SLOW_MAX |
|---|---|---|---|---|
| A6LUT -> O6 (flat over pins): q, g2, A1, A2 | 45 | 56 | 100 | 124 |
| A5LUT -> O5 (union over I0..I2): R0, g1 | 42 | 55 | 121 | 152 |

Every reading uses one interval per LUT output for both edges. An interval row draws each
transition's delay independently, so it also allows rise != fall inside one corner's band.
That makes it a superset of the auditor's rise = fall points.

| name in logs | reading |
|---|---|
| **FAST** / **SLOW** | every arc in [FAST_MIN, FAST_MAX] / [SLOW_MIN, SLOW_MAX] |
| **FASTp** / **SLOWp** / **FMINp** | points: FAST_MAX (O6 56, O5 52 = the q pin), SLOW_MAX (124/150), FAST_MIN (45/42). Exactly rise = fall |
| **corner model** `lit<c><k>` | A's model (`Formal/Core/Delay/Corner.lean`: shared corner c in [0,1], local scatter κ, `Scat`), B-arb-kappa's literal reading: F = FAST_MIN, S = SLOW_MAX, d in [(1-κ)D(c), (1+κ)D(c)], D(c) = lerp(F, S, c) |
| **corner model** `cons<c><k>` | B-arb-kappa's side-pessimistic reading: d in [(1-κ) lerp(FMIN, SMIN, c), (1+κ) lerp(FMAX, SMAX, c)]. κ = 0 gives FAST / SLOW |

- `k11` is κ = 1/11 (rule A's limit).
- `kE` is κ = 383/1927 = 0.1988 (rule E's limit, the 0.772/1.155 guardband).
- A has no measured κ (A-kappa.md correction), so these are the two limits the shipped
  rules are proved sound for.
- c is in {0, 0.5, 1}.

Corner-model rows still fix c per run, so they are a sweep over c, not a statement for
every c. For the conditions below, which are linear in the arcs, the c = 0 and c = 1 ends
bind. That was checked numerically, not proved.

## Results: TChecker (dense time, 12c's model), the authoritative numbers

Commands (from `formal/tools/zone`; tck-reach rebuilt from the same commit as 12c,
d711ace9, into `build/tchecker`; logs in `formal/tools/zone/results/`: `onecorner_inertial.log`,
`celem1c.log`, `witnesses_onecorner.txt`, `tpquick.log`). `$VENV` below is a venv with
`pip install z3-solver stormpy==2.0.0` (z3 5.3.2, stormpy 2.0.0):

    python3 -I onecorner.py all inertial FAST,SLOW,FASTp,SLOWp,FMINp,cons0k11,cons1k11,lit0k11,lit1k11,cons0kE,cons1kE,lit0kE,lit1kE,cons0.5k11,lit0.5k11
    python3 -I celem1c.py
    python3 -I witness1c.py FAST inertial tx wa=94,94        # (and the other witnesses below)
    ROWS=7,0 TMO=200 python3 -I tpquick.py SLOWp,FASTp,FMINp  # transport, targeted

Cost: 15 corners x 3 sections (server, A0 fork, q->ugrant route, HELD and UNHELD, each
bisected to 0.1 ps) took **264 s** in total. Each exploration took 0.1-0.3 s and at most
~750 zones. The model is 12c's `arb.py` nodes, INITs, monitors and environment, unchanged:
- clients fall [4, 24] ps after their A;
- the server follows R0 after [s_lo, s_lo + 20] ps;
- zero routing except the swept wire.

Inertial channel, HELD (shipped) bd_arbiter:

| question | old (12b/12c, corner mix) | FAST | SLOW | FASTp | SLOWp | FMINp | corner model (c = 0 / 1) | closed form (fits every row) |
|---|---|---|---|---|---|---|---|---|
| server latency for ack exclusion (amutex) | s_lo > 56 ps | **any s >= 0** | **any** | any | any | any | k11: cons 2.5 / any; lit any / any. kE: cons 15.6 / 28.5; lit 2.4 / any | 2s >= max(2h6, h5+h6) - 2l5 - l6 |
| A0-rise fork (A0 into ustate.I4 late by wa) | wa < 116 ps (c_lo = 4) | **wa < 94** | **< 204** | < 116 | < 252 | < 94 | k11: cons 85.8 / 185.8; lit 85.8 / 229.4. kE: cons 76 / 164.2; lit 76 / 202.6 | wa < 2·l6 + c_lo |
| same, slow client c_lo = 40 | (152) | < 130 | < 240 | < 152 | < 288 | < 130 | (all +36) | wa < 2·l6 + c_lo |
| q->ugrant route (mutex) | wq_g < 56 ps | **< 42** | **< 100** | < 56 | < 150 | < 45 | k11: cons 38.1 / 90.9; lit 38.1 / 138.1. kE: cons 33.6 / 80.1; lit 33.6 / 99.3 | wq_g < min{ l5 if h5 > l6 ; l6 if h6 > l5 } |
| mutex, ho, tx at zero routing, any server latency | hold | hold | hold | hold | hold | hold | hold (amutex: row 1; cons1kE also loses amutex/tx at wq_g >= 154.7) | -- |

Notation: l6/h6 and l5/h5 are the lo/hi of the O6 and O5 arc at that corner, and c_lo is
the client's minimum r-fall response. "any" means no violation at any s_lo in {0, 4, 20, ...,
320}. Every edge is closed at the failing side: for example, FAST mutex holds at 41.9 and
fails at 42.0. The corner-model numbers agree with the closed forms to within the 0.1 ps
rounding of the arcs. The κ crossing of the server condition was bisected separately at
srv [0, 20]:

| reading | holds up to κ | fails from κ | formula predicts |
|---|---|---|---|
| cons, c = 0 | 0.0688 | 0.0695 | 0.0705 |
| lit, c = 0 | 0.1758 | 0.1766 | 0.1781 |
| cons, c = 1 | 0.1063 | 0.1070 | 0.1068 |
| lit, c = 1 | 0.2148 | 0.2156 | 0.2159 |

UNHELD (not shipped):
- mutex holds at zero routing at every corner except cons1kE (box-like scatter, the
  O5-fall vs q + O6-rise race; it agrees with B's `box_r1_to_r2_le`).
- The old "16 ps" does not appear at any consistent corner.
- amutex/ho/tx fail at every server latency in every band.
- At points, ho/tx fail iff s_lo >= 36 ps (FASTp), >= 25 (FMINp), or always (SLOWp).

### Witnesses (TChecker symbolic, event order; `witness1c.py`, log `formal/tools/zone/results/witnesses_onecorner.txt`)

**A0-rise fork, FAST, wa = 94** (the scenario of 12b's 116 ps witness):
1. r2 and r1 rise; g2, R0, A0 rise and A2 rises; the token is used.
2. r2 falls 4 ps later, then g2 and R0 fall.
3. q rises for the waiting r1 BEFORE A0s (the late copy of A0 at ustate.I4) arrives, because
   the hold is not yet active.
4. Then A0s arrives, qg/qs, g1 rises with A0 still high (`bad_ho`), R0, and A1 rises with no
   new A0 transaction (`bad_tx`).

The path is A2 rise (l6) + c_lo + q rise (l6) = 45 + 4 + 45 = 94.

**q->ugrant route, FAST, wq_g = 42** (12c's grant-LUT runt, mirror direction):
1. Client 2 is served, then client 1.
2. r1 falls; R0 and A0 fall; q falls for r2.
3. r1 rises again while the old q = 1 is still on qg.
4. g1 = r1·qg fires (O5, l5 = 42), then qg falls and g2 rises while g1 is still in its fall
   arc, so `mutex` is violated.

**Server, cons0kE, s ∈ [0, 20]** (the corner-model condition):
1. Client 2 holds the grant; r2 falls.
2. R0 falls fast (O5 lo), and the server drops A0 at once.
3. q flips for r1; R0 and g1 rise; the server raises A0 again.
4. Meanwhile g2 falls slowly (O6 hi), so ua2 = C(g2, A0) sees both inputs low only for
   2s + 2l5 + l6 - h6, which is shorter than its own fall arc.
5. The inertial ua2 swallows the fall: A2 never drops, and A1 rises. So A1 & A2.

With rise = fall and no scatter (κ = 0), that window is always longer than h6, which is why
the condition is vacuous at every consistent corner.

### C-element (`celem1c.py`): 12b/12c's bounds hold at one corner

| corner (dl = O6 arc; dw = assumed feedback route band) | inertial spec | inertial hazard-free | transport spec |
|---|---|---|---|
| FAST dl [45,56] dw [60,80] | e_lo >= 36 | >= 81 | >= 80 |
| SLOW dl [100,124] dw [150,200] | >= 101 | >= 201 | >= 200 |
| lit c=0 k11 dl [40,50] dw [54,66] | >= 27 | >= 67 | >= 66 |
| cons c=0 k11 dl [40,62] dw [54,88] | >= 49 | >= 89 | >= 88 |
| lit c=1 k11 dl [112,136] dw [181,219] | >= 108 | >= 220 | >= 219 |
| cons c=1 k11 dl [90,136] dw [136,219] | >= 130 | >= 220 | >= 219 |

These are exactly 12c's forms in integer ps: inertial spec e_lo > dw_hi - dl_lo, hazard-free
e_lo > dw_hi, transport e_lo >= dw_hi. They never depended on rise vs fall, so the old
C-element results are not artefacts.

Bug found and fixed in my own WIP from the lost earlier 12d run: `celem1c.py` used an
environment window [e_lo, e_lo + 30]. With dl_lo > 30 ps the two inputs could never be skewed
by a LUT delay, so "spec holds for every e_lo" came out, which was an artefact. The fix is
the window [e_lo, inf).

### Transport (pure delay) at one corner

- **12c's "mutex_nr fails for every wq_g > 0" stands at one corner.** It is reachable at
  wq_g = 0.1 ps at FASTp (2.4 s), SLOWp (6 s) and FMINp.
  - With rise = fall the runt on the grant is not stretched.
  - But the other grant's rise and this one's fall come from the same qg edge through O5
    vs O6. Whichever arc is slower overlaps by |O6 - O5|: 4 ps at FAST_MAX, 26 ps at
    SLOW_MAX. This is B's `grant_cap`.
- The "holds" side of 12c's transport rows (`*_nr` server and A0-fork rows) could NOT be
  re-established at one corner. Every unreachable query timed out at 200-300 s, at more
  than 550 MB, under a load average of 20-29.
  - At 12c's corner-mixed arcs the same explorations took 0.7-5 s.
  - Likely reason (not verified): with rise = fall, pure delay never shrinks a pulse, so
    runts circulate. In 12b's model a pulse "shrinks by the rise/fall asymmetry". The queue
    shapes then multiply. This matches B's "pure transport shows runts circulating forever".
  - So 12c's transport exactness monitors (ovf_nr = 0) are corner-mix results too.
- The full banded sweep (`onecorner.py tp transport FAST,...`) was started and stopped: its
  first exploration was still running after 20 min.
- The A0-rise fork's failing side is the same under pure delay: tx_nr is REACHABLE at
  wa = 2·O6 + c_lo exactly at FASTp (116 ps), SLOWp (252) and FMINp (94), in about 3 s each.
  The holding side just below could not be explored (timeouts, as above).

## Results: Storm (12b's model, digital clocks, 4 ps ticks, bounds rounded outward)

    cd formal/tools/async && $VENV/bin/python -I onecorner.py FAST,SLOW,cons0k11,cons1k11,lit0k11,lit1k11

This was 384 checks in 245 s, with 1-275 k states per check. Log:
`formal/tools/async/results/onecorner.log`.

| question | FAST | SLOW | cons0k11 | cons1k11 | lit0k11 | lit1k11 |
|---|---|---|---|---|---|---|
| HELD amutex vs server latency (ticks) | holds from 0 | holds from 0 | fails 0-2, holds >= 5 | fails 0, holds >= 1 | holds from 0 | holds from 0 |
| HELD A0-rise fork: first failing wa on the grid | 23 (92 ps) | 52 (50 holds) | 22 | 48 | 22 | 58 |
| q->ugrant: mutex first fails at wq_g (grid) | 10 (8 holds) | 26 (20 holds) | 10 | 26 | 10 | 30 |

All of these agree with TChecker after outward rounding. For example, FAST O6 lo rounds to
11 ticks, and 11 + 1 + 11 = 23 ticks for the A0-rise fork. Storm's sweep grid is coarse,
and TChecker's dense-time edges are the exact ones.

## Results: z3 / SMT (12a's model)

### (a) Bare bd_arbcell under tb semantics (route lumped into the inertial arc), route 0

    $VENV/bin/python run_onecorner.py tb      -> results/onecorner_tb.txt

12a found a counterexample at route 0 with a 16 ps overlap.

| corner | arcs | mutex | k-induction, time |
|---|---|---|---|
| FAST | max, and interval | **PROVED unbounded** | k = 15, 1.3 s |
| SLOW | max, and interval | **PROVED unbounded** | k = 19, 3-3.5 s |
| every lit / cons setting at c ∈ {0, 0.5, 1} with κ = 1/11; lit with κ = 0.1988 | max, and interval | **PROVED unbounded** | k = 14-23 |
| cons, κ = 0.1988, c = 0.5 and c = 1 | max | **PROVED unbounded** | |
| cons, κ = 0.1988, c = 0.5 and c = 1 | interval | **CEX** at depth 15 / 21 | |

(Interval rows allow rise != fall inside the band.)
- So the 16 ps race is an artefact at every consistent corner. This agrees with B's
  `ArbCorners.corner_no_overlap`.
- It comes back only when the scatter is box-like: O6 hi exceeds q (O6 lo) + g1 (O5 lo),
  with 8 ps outward rounding on top. That is B's box overlap (`box_overlap_le`); TChecker's
  cons1kE UNHELD row also shows it.

### (b) Shipped bd_arbiter, four-phase clients and server

Setup:
- 1 unit = 25 ps, rounded to nearest. This is coarse; dense-time numbers are above.
- FAST = (2,2) on O6 and O5; SLOW = O6 (4,5), O5 (5,6).
- Route 1 unit on every net.
- Results: `results/onecorner_arbiter.txt`, `onecorner_fork.txt`, `onecorner_fork2.txt`.

Server latency, fork 0:
- mutex, ackmutex and tx: no violation to depth 60 at FAST, SLOW and 12a's mix, for
  Ls = 1, 2, 4.
- The earlier (lost) 12d run's "owner CEX at fork 0, SLOW, Ls = 1" is a **monitor
  artefact**. 12a's `owner` monitor flags an A0 rise while the grant has not yet risen.
  With R0 faster than g2 inside one band, a 1-unit server answers before g2 is up. That is
  not a protocol error: ua2 waits for g2. 12b's `tx` token monitor (added to `arb.py`)
  finds nothing.

A0-fall fork (12a 2d, B ArbA0Fork): the smallest extra delay k on the A0 branch into ua2
that gives an early acknowledge (tx).
- **FAST: k >= 8** (k = 7 none to depth 60; k = 8 counterexample at depth 40).
- Trace:
  1. Client 1 is served; r1 falls; A0 falls at t = 31.
  2. q flips at 34; g2 rises at 37.
  3. ua2 = C(g2, A0b) fires at 40 on the stale high A0b; there is no token.
- In general the condition is late >= early + ua2 arc, i.e. 1 + k >= (route + q + route +
  g2 + route) + ua2, so k >= 3·lut + 2·route. This is the same form as 12a and B (rule J).
- 12a's k >= 10 was this form with q's corner-mixed fall arc (4) instead of its rise arc (2).
- **SLOW: k >= 14**, exactly the predicted 3·4 + 2·1. At depth 60 there was no
  counterexample for any k <= 24, because depth 60 is too shallow (one SLOW transaction is
  about 30 ticks). The depth-90 run (`results/onecorner_fork2.txt`) gives a counterexample
  for k = 14 at depth 63 (178 s), and none to depth 90 for k = 13 (1200 s; bounded, not a
  proof).
- Caveat: with a fork of 24 units the FAST run gave a counterexample at depth 20. That is
  shorter than reset (11) plus the wire (25), so it is a power-up wire-history artefact. The
  threshold rows (k = 7, 8, 9, 12) have counterexamples at depth 40, after every history
  is flushed.

### (c) Bare arbcell, transport routes, free requests, and the aperture

    REAL_CORNERS=FAST $VENV/bin/python run_onecorner.py real            -> results/onecorner_real.txt
    SFX=_slow REAL_CORNERS=SLOW $VENV/bin/python run_onecorner.py real  -> results/onecorner_real_slow.txt
    $VENV/bin/python run_onecorner.py real_slow_routes                  -> results/onecorner_real_slow_routes.txt

Setup: 8 ps ticks, arcs rounded outward, one band for both edges, the same transport route
on q and on r1/r2 into both LUTs, and free requests with a minimum level time of 400 ps.

12a (corner mix) found mutex violated at routes 0, 48 and 100 ps, and an aperture of
152 ps at 48 ps.

| corner | route 0 | route 48 ps | aperture at 48 ps | other routes |
|---|---|---|---|---|
| FAST | none to depth 60 | CEX at depth 23 | **72 ps** (9 ticks; bounded, depth 50). k-induction at 9 ticks did not finish in about 60 min under load | -- |
| SLOW | none to depth 60 | none to depth 60 | not needed (no violation) | 96 ps: CEX at depth 52; 104 ps: CEX at 54; 160 ps: none to 60 (depth probably too shallow; inconclusive) |

- **The FAST route-48 counterexample is the grant-fork runt** (12c's wq_g / 10i's
  H_GRANT_FORK):
  1. r1 rises; r2 rises 48 ps later.
  2. q rises at ustate before r2 arrives there.
  3. r2 reaches ugrant while ugrant still reads the old q, so g2 fires (O6).
  4. g1 rises when the new q arrives, and the two overlap.
- This happens because the q route (48 ps) is longer than the arc that would swallow the
  runt (O5 lo 42 at FAST, rounded down to 40 ps). At SLOW the arcs are 96-120 ps, so the
  route must be about 96 ps or more. That matches TChecker's closed form (wq_g < 42 FAST,
  100 SLOW) in the tick rounding.
- **Corrections to 12a:**
  - At one corner, route 0 shows no violation to depth 60 (bounded only). 12a's route-0
    near-tie needed the mixed asymmetry.
  - The aperture at 48 ps is 72 ps at FAST, not 152. At SLOW none is needed at 48 ps.
  - 12a's 152 ps was a box-like mixed reading (rise 45-56 with fall 100-124 on the same
    arc).

## H_GRANT_FORK (10i) under the corner model

    cd formal/tools/grantfork && python3 -I kappa.py     # reads the committed GrantForkInst.lean

- 10i already priced every element per prjxray column with no rise/fall split, so its
  corner verdicts stand and its Lean needs no restating.
- The transport window W is a signed sum of the 8 per-pin delays. Its box maximum at corner
  c is a sum of endpoints that are affine in c, so its maximum over c ∈ [0,1] is at c = 0
  or c = 1. That is exact on rationals and is arithmetic, not Lean.
- The inertial checker is evaluated at c ∈ {0, 1/4, 1/2, 3/4, 1}.

Instance-clients (of 80) passing:

| checker | reading | κ = 0 | κ = 1/11 | κ = 0.1988 |
|---|---|---|---|---|
| okT (transport) | lit (F = FMIN, S = SMAX) | 23 | 7 | 4 |
| okT (transport) | cons (scatter on the corner windows) | 7 | 4 | 1 |
| okI (inertial) | lit | 23 | 11 | 4 |
| okI (inertial) | cons | 7 | 5 | 1 |

- At κ = 0, lit reproduces 10i's "23 of 80 at SLOW_MAX" and cons its "7 of 80 in the
  per-corner boxes".
- The largest κ* (the scatter up to which the race stays closed, transport) is
  g2_merge3.uarb1 c2: 0.317 (lit) / 0.221 (cons). After it come gd_merge9.uarb1 c1 at
  0.231 / 0.118 and g3_merge9.uarb1 c2 at 0.201 / 0.102.
- So only the near-isochronic merge3/merge9/merge12 forks survive rule E's κ. The
  conclusion "the race is live on shipped routes" is strengthened.
- Per-instance table: `python3 -I kappa.py` (log `formal/tools/grantfork/results/kappa.log`).

## Which old numbers were artefacts

| old claim | source | status |
|---|---|---|
| bare-cell handover overlap 16 ps at route 0; exclusion needs route >= 16 ps (tb semantics) | 12a 2a, 12b, 12c UNHELD | **ARTEFACT**: no overlap at any consistent corner. SMT proved it unbounded at FAST, SLOW and every corner-model setting except cons κ = 0.1988 (box-like scatter); TChecker agrees |
| HELD ack exclusion needs server latency >= ~60 ps (56 ps exact) | 12b, 12c | **ARTEFACT**: it came from the sourceless 28 ps R0 fall. It holds for every latency at one corner. Under the corner model there is a NEW small condition (above) |
| A0-rise fork breaks at wa >= 116 ps (= 56 + 4 + 56) | 12b, 12c | **form stands** (2·O6lo + c_lo). 116 is the FAST_MAX point value, since both arcs in it were rise arcs = FAST_MAX. FAST band 94, SLOW 204, SLOW_MAX 252 |
| HELD mutex needs q->ugrant route wq_g < 56 ps (inertial) | 12c | **form changes**: min{l5 if h5 > l6, l6 if h6 > l5}. 56 is the FAST_MAX point value; FAST band 42, SLOW 100 |
| pure delay: mutex_nr fails for every wq_g > 0 | 12c | **stands** at one corner (overlap = arc difference, not asymmetry stretching) |
| transport `*_nr` rows exact (ovf_nr = 0), server/fork bounds equal to inertial | 12b, 12c | **not re-established**: explorations do not finish at one corner (runts no longer shrink) |
| early ack (A0-fall fork) needs k >= 10 units | 12a 2d | **number artefact, form stands**: k >= 3·lut + 2·route; 8 at FAST, 14 at SLOW (25 ps units) |
| UNHELD ho/tx iff server >= 60 ps / 80 ps | 12b, 12c | **ARTEFACT** (corner dependent; always fails in a band) |
| C-element E >= dw_hi (FIFO), e_lo > dw_hi - dl_lo (inertial spec) | 12a/12b/12c | **not affected** (symmetric arcs); numbers per corner above |
| aperture 152 ps at 48 ps routing; mutex fails at every routing (transport routes) | 12a 2b | **ARTEFACT as numbers**: FAST aperture 72 ps (bounded); SLOW needs none at 48 ps; route 0 clean to depth 60 at both. The failures that remain are the grant-fork runt (route >= O-arc lo) |
| H_GRANT_FORK open on 32/40 instances | 10i | **not affected** (already per corner); stronger under κ |
| 12b DTMC resolution law | 12b | not affected (no arcs) |

## Tool acquisition (2026-10-29)

| tool | route | result |
|---|---|---|
| z3 5.3.2, stormpy 2.0.0 | `python3 -m venv $S/venv && pip install z3-solver stormpy==2.0.0` | works, about 1 min. The earlier venv was lost with the session |
| TChecker | `git clone --depth 1` into `$S/ext` (commit d711ace9, same as 12c), cmake + `make -j2 install` | works, about 10 min under load |
| UPPAAL | uppaal.org, download.uppaal.org | CONNECT 403 (unchanged) |
| Workcraft | workcraft.org 403; github releases / API 403; **`git ls-remote` works** (master 5ebe0838) | the source is clonable, but its backends (Petrify, MPSat, punf) come from workcraft.org, which is blocked. Not built |
| PRISM | prismmodelchecker.org | 403 |
| IMITATOR (parametric TA: the "for all delays" tool track 12 lacks) | source via git (ls-remote works), but its OCaml deps need opam (opam.ocaml.org 403) and PPL's OCaml interface (not in Ubuntu's libppl-dev). **The Docker Hub registry is reachable**: the v3.4.1 image's layers were fetched with the registry API (`imitator/imitator`, static binary `/usr/local/bin/imitator`) into `$S/ext/imitator-img/` | **not run**: the permission system refused to execute the downloaded binary. No docker daemon. Left for the owner to decide; it is the one tool that could give thresholds symbolic in the arcs |

`$S` = `/tmp/claude-0/-home-user-asyncfpga3/c76940ed-8cbb-5e65-894f-a2480ae0f52d/scratchpad`.

## Effort and coverage vs Lean (track-12 verdict update)

| | tools (this redo) | Lean (B's ArbCorners redo of the same instances) |
|---|---|---|
| cost of the corner redo | about 3 h total. CPU: TChecker 264 s for 15 corners x 3 questions; Storm 245 s; z3 tb 1 min, arbiter 40 min (BMC, coarse) | a full probe (Bc, about 1370 lines). Every instance became a theorem, with the mix proved to BE the mix (`prj_is_mix`, `rfl`) |
| what it gives | thresholds at 0.1 ps per corner, witnesses, and **closed forms guessed by sweeping corners** (3 new ones here: server, A0-rise fork, wq_g) | parametric statements for every arc value, so the corner choice is an instantiation, not a re-run |
| corner model | a sweep over c and κ (finite). Endpoint sufficiency argued, not checked | `Corner.lean`: endpoints suffice, proved (`bundle_ratio_affine`) |
| how the misreading propagated | silently. Delays are inputs, the tools checked exactly what they were given, and the counterexample-one-below-threshold check cannot catch a wrong input | equally silently in the numeric instances (B's 7e/7h/7j used the same numbers), but the parametric theorems stood and only instances changed |
| failure modes found in this redo | an environment-window artefact in my own WIP (`celem1c.py`); a monitor artefact (12a's `owner`); a power-up wire-history artefact (SMT, fork 24); an explicit-state blow-up of pure delay at rise = fall | none of these classes (but no Lean was written here) |

**Updated track-12 verdict:** works as a bound-finder and corner sweeper, not as a prover.
- In minutes per corner, the dense-time checker re-derives every arbiter threshold exactly
  and suggests closed forms. B can then prove those forms parametrically.
- It inherits whatever delay reading it is fed. Every numeric input needs a provenance check
  (prjxray column, rise = fall).
- Pure delay at a consistent corner is out of reach for explicit zones on the full arbiter.
- Parametric tools (IMITATOR) are the obvious next step: obtainable, but not executed here.

## Lean

None written.
- 10i's GrantFork.lean is corner-consistent already.
- The new closed forms (server condition, wa < 2·l6 + c_lo, the wq_g form) are tool fits,
  not theorems. Proving them would mean stating 12c's inertial TA semantics in Lean, which
  B's ArbHeldTimed/ArbCorners model differently (transport `Dl` relations).
- **Hypotheses:** none claimed as proved.
- **Non-vacuity:** every failing edge above has a tool witness; every holding row has
  `reach1 = reach2 = 1`, i.e. both clients are served.

## Fidelity (unchanged from 12a/12b/12c unless noted)

- **LUTs:** real INITs. One arc per output, not per pin (O5 is the union over pins I0..I2;
  B's per-pin values differ by up to 3 ps at one corner).
- **Channels:** inertial (optimistic: it swallows sub-arc pulses), or transport
  (pessimistic).
- **Environment:** free clients with a 4 ps minimum response; the server is a pure delay of
  R0.
- **Feedback route:** assumed bands for the C-element (60-80 ps fast, 150-200 ps slow).
- **Corner model:** the κ values are the rules' limits, not measurements.
