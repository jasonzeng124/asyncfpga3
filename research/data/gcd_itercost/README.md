# Where gcd's iteration goes (PROGRAM.md "Second lead" method, applied to gcd; subagent 2026-11-17)

Diagnosis. Nothing here changes a design or a size. Simulation, not silicon: the itercost stack (netlist decoded from
the .bit, prjxray SDF, `GLS_MODEL=fid`, chains 0.21 / CARRY4-F7F8-FF 1 / rest 0.288, no scatter, +FCLK_PS=12000), which
reads ~8% slow against the August board on gcd (`../aug_gcd/`, x = 0.21).

## The build

The gcd board candidate the draws agent is judging (`../gcd_draws/`): `gcd_bench_gen` with
`gcd_bench_sizes_R5s75.vh` (BQ#5's R5 x0.75 sizes, bench prefix), `BDC_SELECT_PADS=hw/gcd_hw_pads.json`,
`BDC_LINK_FASTFALL=1`, BD_RLOC v2 (the bench default; v4 aborts on the bench), `BD_SIZES_GATE=0` (no gate read),
NEXTPNR_SEED=2, --freq 83 (closes 112.2 MHz). nextpnr 9c732bc6303458df (toolchain.sh PASS, all patches ok).
sdf 3df14ec9, bit a6024bc0, decode EQUIVALENT (benign kinds). Built in a scratch copy of cells/ + bdc/ (no repo file
touched). ONE route only: the gcd full-stack compile peaks at 9.4 GB RSS (`/usr/bin/time`), and on this shared 15 GB
machine it was OOM-killed three times before a window opened; a second seed was not affordable in the time box.

Vector (a, b) = (2^31-1, 1): every main iteration is |a-b| = 2^k-2, one shift, then the exit test of the ctz loop, so
one period of the steady state = **one main iteration + one inner shift**. Returned gcd = 1 (C: 1).
Tools: `research/tools/eventgraph/eventgraph.py` (CHECK: graph period == trace period, cycle == trace.py's, both PASS),
`whatif.py`, `search.py --new-knobs`, `research/tools/itercost/analyze.py` (categories, per-delay settle),
plus two scratch helpers kept here: `split.py` (per stage-visit split of the critical cycle) and `lever.py`
(whatif + `shrink:INST:N[:kind]`, a line cut to its first N elements at the route's own element cost).

## Result: 81.03 ns per (main + 1 shift); the datapath is not on the critical cycle

The critical cycle (160 hops, all exact) is the **control-token ring of the two nested loops**, not the gcd
arithmetic: none of |a-b| (uselect1), min (uselect0), the shift (ushrsi4) is on it. Per period it runs the ctz loop's
ring (ucontrol_merge10 -> ulink_n151__0 (umux15's select) -> umux15 -> ulink_n145__3 -> uori4 (ctz test) -> ucond_br45 ->
ulink_n_falseResult_91 -> ucontrol_merge10) twice, rising and falling (the shift test, then the exit test), and the
outer ring once (uori4's exit -> ucond_br41 -> ulink_n112__1 -> ucmpi10 (`a == 0`) -> ucond_br39 -> ucontrol_merge9 ->
ulink_n129__1 -> ufork34 -> ucontrol_merge8 -> ucond_br45 -> ucontrol_merge10). 4 polarity changes, all at
ucontrol_merge10 (the ctz loop's arbitrated merge).

| ns per (main + 1 shift), seed 2 | ns | % |
|---|---:|---:|
| logic (part of each delay its data really used, analyze.py) | 12.67 | 15.6 |
| excess delay (matched delay beyond its data) | 21.36 | 26.4 |
| handshake cell arcs | 2.20 | 2.7 |
| req/ack wires (rising) | 16.85 | 20.8 |
| return to zero (every falling hop) | 27.95 | 34.5 |
| of RTZ: delay chains / handshake cells | 9.50 / 18.45 | |
| sum - period | 0 ps | |

Split by loop (`split_s2_b1.txt`, rows in cycle order): **one inner shift = 29.8 ns** (ctz ring rising 19.9 + falling
9.9); **the main iteration = 51.2 ns** (exit-test rise of the ctz ring 16.0, outer ring rise 17.7, the falls after the
exit 17.5). Against the task's figures: gcd_ps P1's 121 / 77 ns were pad-only (RTL default) sizes, uori4 84 elements,
uselect1 94; this candidate is 51 / 30 ns (sim at 0.288, ~8% slow vs board), against Dynamatic's estimated ~42 / ~14:
**1.2x behind per main iteration, 2.2x per shift** (not 3-8x).
Check by a second vector on the same route: (2^31-1, 3) has two shifts per main iteration (a = 2^k-1 -> 2^(k-2)-1;
returned 1, C: 1); its steady period is 112.01 ns (14 equal intervals, too few for eventgraph's window, so no graph).
112.01 - 81.03 = **31.0 ns per extra shift**, hence **main = 50.0 ns** (the cycle split above says 29.8 / 51.2).

The old P1 graph (`../eventgraph/graphs/gcd_2`, 186.9 ns) shows why the old number was so large: its cycle crossed
min -> b's header mux -> |a-b| -> ctz test, 79% rising delay chains (uselect1 37.4 ns, uori4 33.8 ns x 2, uselect0
20.3 ns). With R5s75 sizes those lines fell below the control ring (the graph, cut to R5s75 sizes + fast fall,
predicted 91.7 ns and the control ring; the rebuilt route measures 81.0 with that ring).

## Every stage on the cycle (seed 2; stages.tsv of analyze.py, both visits summed)

| stage | on cycle | logic | excess | handshake | wire | RTZ |
|---|---:|---:|---:|---:|---:|---:|
| uori4 (ctz test, x2) | 17.48 | 2.21 | **10.75** | 0.14 | 0.93 | 3.44 |
| ucontrol_merge10 (ctz merge) | 8.86 | 2.24 | 1.47 | 0.35 | 2.38 | 2.42 |
| ulink_n145__3 (a into the test) | 6.72 | 2.06 | 0.31 | 0.14 | 1.33 | 2.88 |
| umux15 (a's ctz mux) | 6.63 | 0 | 2.87 | 0.14 | 0.93 | 2.69 |
| ulink_n151__0 (umux15 select) | 6.41 | 3.19 | 0 | 0.14 | 1.14 | 1.95 |
| ucmpi10 (`a == 0`) | 5.68 | 0 | **5.01** | 0 | 0 | 0.67 |
| ucontrol_merge9 (outer merge) | 4.51 | 1.67 | 0.45 | 0.14 | 0.74 | 1.52 |
| ulink_n112__1 (a into ucmpi10) | 2.99 | 1.29 | 0 | 0.07 | 0.53 | 1.11 |
| ulink_n129__1 (uack 1) | 2.63 | 0 | 0.49 | 0.07 | 0.76 | 1.32 |
| 12 handshake-only stages (steers ucond_br39/41/45 + joins, forks, merge8, _f forks, n143, n_falseResult_91) | 19.12 | 0 | 0 | 0.98 | 9.14 | 9.00 |
| total | 81.03 | 12.67 | 21.36 | 2.20 | 16.85 | 27.95 |

## Every delay line on the cycle

"Set by": the R5 round (tighten rule A, measured on 8 gcd_hw routes, + skew.py --slack 500 pads), then x0.75
(shrink_sizes.py). corner_audit / line_account were not run (they need a fusion_bench route directory and ~one audit
run per line; out of the time box). "Data needs" is analyze.py's settle - entry of the line's bundled data on this
vector, and its worst over the whole run (both calls, entry and exit iterations); n for that = ceil(1.2 x worst / ps
per element as routed). This is ONE vector: a static check would give the full-range need.

| line | n | ps rise per visit (visits) | data it bundles | settle steady / worst over run | n for the data (as routed) | false / impossible path? |
|---|---:|---|---|---|---:|---|
| uori4.udly | 15 | 6484 (2) | `a < 1` (32-bit signed compare) or `(a & 1) != 0` | 1.11 / 2.91 ns | ~8 | **yes**: the compare's second operand is the constant 1, delivered through a 32-bit latch bank (ulink_n155__1, D = 32'h1, from usource13 -> ufork38 -> constant -> ufork39), so yosys builds a variable-vs-variable carry-chain compare and the line is sized for it. With the literal it is a sign bit + zero detect, 2 LUT levels: ~3-4 elements |
| ucmpi10.udly | 9 | 5013 (1) | `a == 0` (folded constant) | 0 / 2.02 ns | ~5 | no (real zero detect; the steady value never changes: a != 0 until exit) |
| umux15.udly | 3 | 1383-1483 (2) | mux data (a) | data not on the cycle | 1? (rule M) | the mux's request waits on its select here, not on a |
| ulink_n151__0.rdly | 4 | 1594 (2) | merge10's index (umux15's select) | 1.81 / 1.81 ns | 4 (data arrives 0.2 ns after the line) | no |
| ulink_n145__3.rdly | 3 | 1189 (2) | a, 32 bits | 0.88-1.21 / 1.59 | 3 | no |
| ulink_n112__1.rdly | 3 | 1285 (1) | a, 32 bits | 1.29 / 1.82 | 3-4 | no |
| ucontrol_merge10.udly | 3 | 1858 (2) | index | 0.81-1.43 / 1.43 | 3 | no |
| ucontrol_merge9.udly | 3 | 2123 (1) | index | 1.67 / 1.67 | 3 | no |
| ulink_n129__1.uack | 1 | 493 (1) | ack delay | -- | 0-1 (rule H) | -- |

Off the cycle but next once RTZ goes (graph, every falling arc 0: 61.5 ns): the datapath ring umux13 -> uselect1 (|a-b|,
20 el., 10.5 ns) -> umux15 -> ushrsi4 (17 el., 8.4 ns). **ushrsi4 is a 32-bit barrel shifter for `a >>> 1`**: its shift
amount is the same forked constant 1 through a latch bank (ulink_n155__0). The constant's request (usource13 ->
ufork38 -> ufork40 -> ulink_n155__1) is on 3 of the 5 next cycles (0.6-4.3 ns below the critical one): it is joined in
uori4 and ushrsi4 every ctz iteration although its data never changes.

## Levers that exist in bdc (predicted on the seed-2 graph; the graph's error on a rebuild is ~1.4 ns mean, 3 ns max)

| lever | knob | predicted (main + 1 shift) | per main / per shift |
|---|---|---:|---|
| today | -- | 81.0 | 50.0 / 31.0 (two vectors) |
| 1. uori4 to its data (15 -> 8, as routed) | sizes only | 76.7 (-4.4) | the test is on both visits |
| 1'. uori4 with the literal (BDC_CONST_DATA=1, then 15 -> 4) | BDC_CONST_DATA + a sizing round | 75.1 (-5.9) | the next cycle (constant's request path, ushrsi4) binds |
| 2. ucmpi10 to its data (9 -> 5) | sizes only | 79.3 (-1.8) | main only |
| 1' + 2 | BDC_CONST_DATA + sizing | **73.3 (-7.7, 1.11x)** | (1 + 2 with uori4 at 8: 74.9) |
| 3. the merge10 polarity changes (every falling arc 0 = two-phase bound) | none in bdc for this merge (see below) | 61.5 bound (-19.5) | |
| storage search (search.py --new-knobs) | BDC_MERGE_OUT_LINK=ucontrol_merge9 | 80.5 (-0.6) | |
| BDC_MERGE_OUT_LINK=ucontrol_merge10 | built, see below | not predictable by the graph (reasoned 77, 72-81) | **measured 81.73 (+0.69)** |

- **RTZ is the largest term (28 ns, 34.5%) and it sits at one cell, ucontrol_merge10** (all 4 polarity changes). The
  ctz loop's ring is entered twice per main iteration, so its rising and falling passes are both paid on each shift.
  whatif.stage() cannot evaluate a stage on merge10's channels: their nets have two phases per period (the ring runs
  twice) and it refuses (`node_of`), and search.py skips such candidates silently -- so "storage buys nothing" (search:
  -0.6 ns) is a statement about the channels the tool could edit, not about merge10.
- With BDC_CONST_DATA + a sizing round, ushrsi4 (17 -> ~1) comes off the datapath bound too: every falling arc 0 with
  uori4 8 / ucmpi10 5 gives 56.5 ns (ushrsi4's 8.4 ns on that cycle); with ushrsi4 at 1 as well, 54.9 ns, where |a-b|
  (uselect1, 10.5 ns) and the constant's request path bind.
- Not a bdc knob, structural: Dynamatic/LLVM sank `b = min(a, b)` (select0) into bb9, after the ctz loop, so a and b
  ride the ctz loop's steers every shift (ucond_br43/44) and min is in series after the loop exit. On the P1 route it
  was on the critical cycle (uselect0, 21 ns); on this route it is not, but it is what the datapath ring crosses.

## Build of one lever (prediction written first: PREDICTION_mo10.txt)

Same recipe + `BDC_MERGE_OUT_LINK=ucontrol_merge10`, NEXTPNR_SEED=2 (sdf bb53adbe, bit 000546a3, decode EQUIVALENT,
returned 1). Predicted 77 ns (72-81), with the stated reading "at or above 81 means the merge10 polarity changes are
not the arbiter-output coupling".

**Measured 81.73 ns (base 81.03, +0.69): no gain.** Graph CHECK PASS (period and cycle equal the trace's). The cycle is
the same control ring; its 4 polarity changes moved from ucontrol_merge10 to the new link
(`ucontrol_merge10_f R -> ucontrol_merge10_olink F`, `ucontrol_merge10_f F -> ucontrol_merge10_olink R`, twice): the
coupling is the output fork waiting for its consumers on the ctz ring to return to zero, not the arbiter holding its
granted input. The olink's own request line (DELAY = SELECT_PAD 4; BDC_LINK_FASTFALL does not cover the merge-output
link) falls slowly on the cycle twice; with it falling fast the graph gives 80.09, still the base's 81.0 within scatter. Rising-only floor 62.3, two-phase bound 62.3 (base 60.2 / 61.5). `split_mo10_s2_b1.txt`.

Reading: on the ctz ring a token comes round twice per main iteration, and every stage between merge10 and the next
latch must finish its 4-phase return before the second lap: the ring is too short (in storage that decouples the
RTZ) for its own lap time. The bdc knobs that add such storage on the ring (BDC_LINK_DEPTHS on ulink_n151__0 /
ulink_n145__3 / ulink_n_falseResult_91, BDC_FORK_OUT_LINK on merge10_f's outputs) could not be predicted (multi-phase
nets, above) and were not built.

## Does NOT show

- One route, one vector. The draws agent judges correctness; nothing here does. The size cuts are what the data on
  this vector used, not what a static full-range check allows.
- Silicon (sim at the 0.288 band, ~8% slow on gcd's August build).
- The Dynamatic numbers are estimates (`../dynamatic_ref/`).
