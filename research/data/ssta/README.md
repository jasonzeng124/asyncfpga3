# The static rules under many draws of the delay model (2026-11-20)

Four simulated draws per route (suite_one.sh) cannot see a race that the model loses one time in three: formal's C68
found exactly that on exit1 spmv s1 (11 of 32 of its draws hang; our 4 passed). A gate-level draw costs 10-30 minutes.
The rules (`research/tools/corner_audit.py`: tighten / skew / arb_fork, the races the sizing loop sizes on) cost about one
minute per corner. So: time the route as ONE draw of the model would, measure every rule constraint on that timing with
no guard, and repeat over many draws.

## Tools

- `research/tools/draw_sdf.py ROUTED_JSON XRAY_SDF K OUT_SDF`: the route's prjxray SDF (FAST_MIN : SLOW_MIN : SLOW_MAX
  per arc, cells/gls/fid/xray_delay.py) timed as `bench_gate.sh draw:K` times it in the GLS -- bands XC (delay chains),
  XR (the rest), XK (CARRY4 / F7F8 / FF / RAM) from random.Random(7919 K + 17); per-pip wire scatter 0.126 (each
  INTERCONNECT arc times the mean factor of its route branch's pips, md5("K:pip"), shared pips shared), region scatter
  0.02 per 10 x 10 slice block (md5("region:K:x:y")), per-arc cell scatter 0.126 -- written with ONE delay per arc.
  The bands, the pip and the region factors are gen.py's own (same hashes); the per-arc cell normals are drawn here in
  this file's order, so they are the same distribution, not the same numbers.
- `research/tools/ssta_draws.sh ROUTED_JSON XRAY_SDF SIZES_VH OUT "KEYS" [JOBS]`: for each K, draw_sdf.py, then
  corner_audit.py `--uniform 0.5 --no-size --guard-lo 1 --guard-hi 1 --a-frac 0 --a-min 0` with the sizing loop's rule
  switches (auto_size.sh rule(); BD_RAM_GUARD_PS=0) and `CA_ALLCONS=1` (new, opt-in: all sized constraints with their
  margins; unset, every corner_audit output is byte-identical -- checked).
- `research/tools/ssta_table.py OUT [TOP]`: per constraint the raw margin over the draws (mean, sd, minimum, draws below
  0, the normal tail at mean / sd), worst first; how many draws lose at least one race.
- `research/tools/race_mc.py ROUTED_JSON ARCS_TSV SPEC [N]`: the same model on ONE named race (two paths, their arcs
  listed), by Monte Carlo over 200 000 points, for tails no number of runs reaches.
- `research/tools/adv_sdf.py SDF ARCS_TSV OUT SPEC`: a fixed delay per arc (e.g. formal's race-only adversary: one
  path at FAST_MAX, the other at FAST_MIN) for `bench_gate.sh COL=env` with `GLS_SDF_FIELD=max`.

## Checks

- race_mc on formal B21's race (exit1 varshift s1, steer ucond_br11): base margin without scatter 252 ps at bands
  0.25 / 0.25; gen.py's own SDF for the same bands (no scatter), arcs read back from annot.sdf: 251. Spread: 16 real
  gen.py draws 227 +- 68 ps (min 95) against the model's 254 +- 59.
- adv_sdf on the same race: the adversary loses it in our GLS too (271 pulses of 19 ps on 22 nets, 10 / 10 answers);
  every arc mid-FAST, the two sides swapped, and the adversary at the slow corner: no pulse under 2.9 ns (journal
  2026-11-20 09:44 / 09:53).
- ssta on C68's route (exit1 spmv s1, NOT CLEAN by E at ucond_br15): E at ucond_br15 lost in 34 of 64 draws (-11 +- 74
  ps); our GLS draws on the same route show 72-420 pulses under 1 ns at formal's hang nets in 7 of 13; formal's
  simulator hangs in 11 of 32. The rates agree; draw by draw the signs agree only 6 times in 13 (the cell normals
  differ, and gen.py's decoded netlist falls back to per-arc wire factors on 40 % of arcs against 25 % here).

## What it says so far

| route | rule verdict | static draws | draws losing any race | weakest constraints (raw mean +- sd) |
|---|---|---|---|---|
| exit1 spmv s1 (C68) | NOT CLEAN | 64 | (E at ucond_br15 alone: 34) | E ucond_br15 -11 +- 74; A'm umux10 +142 +- 123 |
| exit1 countloop s2, untrimmed | NOT CLEAN (one H row) | 48 | 31 (all the H row) | H ulink_n_trueResult_12 stage 2 -32 +- 63; A'm umux0 +162 +- 82 |
| exit1 countloop s2, trimmed (the committed record) | NOT CLEAN (the same row) | 48 | 31 (the same) | + A'm umux3 +227 +- 96 (min +3), A ucontrol_merge0 +218 +- 78, A'm umux1 +280 +- 94, H trueResult_0 +267 +- 89 |
| exit1 varshift s1 | CLEAN | 48 | 0 | I +275 +- 142 (min +4), I +284 +- 113, E umux0 +217 +- 70, H +211 +- 68 |
| exit1 lfsrfind s1, untrimmed | CLEAN | 48 | 0 | A ucontrol_merge2 +152 +- 44, A'j uselect0 +350 +- 92, A ucontrol_merge0 +193 +- 51 |
| exit1 lfsrfind s1, trimmed (the committed record) | CLEAN | 48 | 0 | + A'm umux1 +318 +- 104 (3.1 sd), A'm umux0 +222 +- 63 (3.5 sd); ucmpi0's A'j 2239 -> 1444 |

- A static loss is an upper bound on a failure, by rule. countloop s2's H row is lost in 31 of 48 static draws, and
  every simulated draw on that route passes with no pulse under 3 ns (the farm's 4, formal's 16 + 16): rule H compares
  the acknowledge's release with the latch's close and does not credit the sender's handshake and data path that the
  next value must still cross. E at a steer (C68) is the kind that shows in the simulation as pulses.
- The trim step moves the constraints of the lines it shortens from slack to the rule's own guard, 2.4-3.5 sd in the
  model, and nothing else (countloop s2, lfsrfind s1); the loop's own sized lines sit at the same distance (A'm umux0 untrimmed, 2.0
  sd). Formal's B23 says the same of its steer bounds.

## Formal's latch-fed steer races (B21 / B26) in the draw model

`research/tools/race_find.py` traces every steer whose condition comes from a link latch and whose request crosses that
link's request line and the steer's join (both launched by the link's controller rising), and runs race_mc.py on each.
Per route, the weakest such race (mean +- sd of request minus condition at the steer's output, over 100 000 points of
the model; the band corners alone in brackets):

| exit1 route | latch-fed steers | weakest | margin | sd from 0 | formal's ctl slack at kappa 0 (corner 0 / 1) |
|---|---|---|---|---|---|
| varshift s1 | 10 (5 steers x 2 halves) | ucond_br11 | 254 +- 59 ps (211-296) | 4.3 | -21 / +25 ps |
| twoloops s2 | 24 | ucond_br17 | 425 +- 68 (370-479) | 6.2 | +42 / +115 |
| fold64 s1 | 20 | ucond_br4 / br3 | 322 +- 54 / 303 +- 47 | 6.0 / 6.4 | +66 / +202 |
| quadrec s3 (built with its search structure) | 22 | ucond_br11 | 325 +- 65 (259-391) | 5.0 | +5 / +10 |

varshift's race is the weakest found; the model loses it about 2e-5 of the time; quadrec's is at 5.0 sd (normal tail
~3e-7), fold64's and twoloops' beyond 6 sd.
formal's ranking (its fast-corner slack) and the model's agree on varshift being worst, but the model puts the
other three much further from it than formal's corner does: formal's adversary sits outside the model's band box.
