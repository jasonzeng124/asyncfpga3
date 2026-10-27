# C-10c: is the SDF the reason silicon disagrees? (prjxray model vs the rings)

Track 10, probe c. Shard C. 2026-10-27. Python only, no Lean.

## Verdict

**Works, with one big surprise. Most of the silicon residual the repo quotes
is a known SDF bug, not missing physics.** All the ring measurements
(`ro_top` 2026-08-03 and 2026-08-18, `ro_many_top` 2026-08-23) were compared
against SDFs written **before** `patches/nextpnr-xilinx-lut-perm-sink.patch`
(committed 2026-09-20). In those SDFs every LUT input reached through a
non-identity pin permutation carried the placer's estimate: **0 ps within
the same slice and LUT pair, and 150 ps within the same tile**, where the routed
hop costs 295 ps. Here that applies to 85% of chain hops (only A1 is identity
for a LUT1). `cells/hw/README.md` still compares silicon with those SDFs and does
not mention the patch. When the pre-patch SDF is emulated on fresh routes:

- **Ring 0 (+35%):** its SDF of 4674 ps is exactly a value the emulation gives
  for a compact 7-link ring: the corrected SDF is 6704 ps for the same
  placement. Against comparable rings (n=47), the corrected SDF predicts the
  measured 6293 ps to within 6.7%, the prjxray model (median) to within 1.1%,
  and the pre-patch SDF misses by 36%.
- **The "+988 ps per loop" offset and the short-ring excess:** reproduced
  mostly by the patch alone, with the prjxray model adding a little more
  (table below).
- **The prjxray model proper** (physical-pin site delays plus Elmore RC) changes
  the per-route prediction by up to about ±25% against the current SDF on 7-link
  rings. Its within-length scatter is about the size of silicon's scatter. That
  is consistent with explaining the per-route residual, **but it is not
  demonstrated ring by ring**: the per-ring silicon data and the measured
  bitstreams are not in the tree, and the measured routes cannot be rebuilt
  (different nextpnr binary). Every comparison here is population against
  population.

## What checks (run it)

    cells/verify/toolchain.sh                  # 9/9 ok; nextpnr sha256 9c732bc6303458df
    formal/tools/prjxdelay/run.sh              # routes 2 designs x 4 seeds (~10 min first time), then ~45 s

Files (all mine; large outputs go to `formal/tools/prjxdelay/build/`, which is gitignored):
- `route.sh TOP SEED [FREQ]`: the same yosys and nextpnr invocation as
  `cells/hw/build_hw.sh`, written to `build/`. Settings: BD_RLOC=none (as the
  measured builds were), no bitstream, and `fasm_audit.py` on every route (all
  PASS). It records the toolchain stamp per route.
- `ringdelay.py BUILD TOP`: per ring, (a) the repo's own SDF prediction,
  computed by **importing** `ro_many_measure.ring_loop_ps` / `ro_measure.ring_loop_ps`
  + `tighten.parse_sdf`. The tool asserts that the per-stage arcs sum to it.
  (b) The emulated pre-patch SDF. (c) The prjxray model at 4 corners.
- `analyze.py`: the comparisons. Outputs are in `build/analysis.txt`,
  `build/analysis_prepatch.txt` and `build/analysis_extra.txt`.

Routes: `ro_many_top` and `ro_top`, seeds default (no `--seed`: how the
measured bitstreams were built), 1, 2 and 3. All are nextpnr **9c732bc6303458df**,
with toolchain.sh 9/9. FASM sha256 prefixes: ro_many default 564f2945611a0e7b,
s1 f68cfdb54c08facc, s2 ae05d644d64b1fba, s3 0defd420a897edbd; ro_top default
d580bb3155c29301, s1 0c21608c480d1d12, s2 10c7999939b7cda4, s3 3a23d1ad15e8eac0.
`--freq 100` on ro_many default gave a **byte-identical FASM** (sha
564f2945611a0e7b), so the router is not timing-driven here, and omitting
`--freq` (as build_hw.sh does) does not change the route. That gives 512
`ro_many` rings and 20 `ro_top` rings.

## The model (`ringdelay.py`) and its fidelity

- **Stage** = predecessor LUT site output pin -> routed net -> **physical** input
  pin -> LUT arc. The physical pin comes from the routed JSON (ports are
  renamed to physical pins). It is **cross-checked against the bits**: fasm2lean's
  `Extract.walk` goes backwards over the FASM's active pips from that pin and
  must arrive at the predecessor's site output pin (A..D or ?MUX via
  ?OUTMUX). Any mismatch exits 1; there were none on 8 routes.
- **Net** = an RC tree built from **prjxray/prjxray/timing.py's own classes**
  (Outpin, Wire with pi-model, Buffer, PassTransistor, Inpin). It covers the whole
  routed net: every ON pip (FASM features, plus ppips `always`/`default` only on
  a node with no explicit driver; 0-54 such pips per route) and every site input
  pin on every node, so fanout loads are included (the slot-mux leg in ro_many,
  the BUFG tap in ro_top). Units are as in prjxray tile.py (R/1e3, C/1e3, ns).
  Per sink, the intrinsic sum at each of fast_min/fast_max/slow_min/slow_max is
  added to the Elmore sum (R and C have one value, not one per corner).
- **LUT arc** = prjxray-db `timings/slicel|slicem.sdf` IOPATH for the physical
  pin and O6/O5: (45, 56, 100, 124) ps for every pin.
- **Period** = 2 x loop. prjxray has no rise/fall split, so this is
  H_RISE_EQ_FALL. To test it, measure duty cycle, or compare an inverting ring
  with a non-inverting two-token ring.
- **Pre-patch SDF emulation**: a stage whose net ends with a non-identity
  permutation pip (`CLB.._<L><x> -> SITEWIRE/<site>/<L><y>`, x != y, read from
  the net's ROUTING) gets predictDelay as patches/README.md states it: 0 ps for
  the same site and LUT letter, 150 ps for the same tile, otherwise
  450 + 90|dy| + 45|dx| ps on the tile grid. The tile-grid units are my reading
  of that text (no nextpnr source in the tree). Evidence that it matches the old
  binary: the measured ring 0's 4674 ps is a value the emulation produces
  18 times among the 132 7-link rings: 2 x (8 x 124 + 295 + 7 x 150), a
  compact ring with one identity-pin hop (routed, 295 ps) and seven permuted
  hops in the same tile estimated at 150 ps. The corrected SDF of those
  placements is 6704 = 2 x 8 x (124 + 295). The 08-03 ring 0's 8290 is not produced
  exactly (values are spaced by 290/580 ps steps; 8290 is within the range).
  The old binary placed differently from this one, so this is a distribution
  of what that SDF said, not the measured routes.
- Not modelled: rise/fall, per-corner RC, within-die variation, temperature,
  speed grade (prjxray-db does not state it; the board is -1), and LUT internal
  pin-to-pin differences beyond prjxray's site-pin delays.
- Upstream bug found: prjxray `math_models.py` declares
  `def PythonMathModel(object):`, a function and not a class, so it cannot be
  instantiated. `ringdelay.py` carries the 4 methods verbatim as a class.

Hand check of one stage (ro_many default, ring (0,0), C6LUT -> A6LUT A2,
4 pips): prjxray slow_max net = 806 ps, of which 507 ps is the A2 site pin and
24 ps is RC. nextpnr's SDF charges 436 ps for that hop. The 3-pip in-slice hop into A5
costs 264 ps in prjxray against nextpnr's 295 ps. So the model moves away from the
SDF in both directions, depending on the physical pin.

## Numbers

Physical pins used by ring stages (15360 stages over 4 routes x 128 rings): A1 2348, A2 3690, A3 3579, A4 1984, A5 3759,
**A6 0**. nextpnr never puts a chain input on the fast pin (prjxray A6: 5 ps
slow max; A1/A2: about 510 ps).

**1. Model / current SDF (ro_many, 512 rings), median per length:**

| links | fast_min | fast_max | slow_min | slow_max |
|---|---|---|---|---|
| 7 | 0.495 | 0.612 | 1.185 | 1.465 |
| 15 | 0.489 | 0.603 | 1.165 | 1.449 |
| 31 | 0.492 | 0.604 | 1.171 | 1.446 |
| 63 | 0.489 | 0.599 | 1.159 | 1.437 |

The ratio is flat in length. The difference is almost all site pins: with
25 ps/pin removed, the site-pin excess is 5.2 ns of the 3.4 ns model-minus-SDF
difference on a 7-link ring (the SDF's pips are dearer than prjxray's), and
the RC is 0.31 ns. Within a length, Spearman(site-pin excess/SDF, model/SDF) is
+0.96 to +0.98. **So against the current SDF, the prjxray model predicts no
short-ring excess.** Silicon sits at **0.61-0.68 x slow_max**, between fast_max
and slow_min, for the population as a whole.

**2. Against the pre-patch SDF (what silicon was actually compared with).**
One global scale is fitted per model so that its pooled median equals silicon's
0.989. Median per length, p90/median, and the README's two-parameter intercept b/a:

| predictor of silicon | 7 | 15 | 31 | 63 | p90/med 7 / 15 / 31 / 63 | intercept b/a |
|---|---|---|---|---|---|---|
| current SDF (the patch alone) | 1.060 | 0.983 | 0.983 | 0.968 | 1.27 / 1.11 / 1.08 / 1.06 | +948 ps |
| prjxray slow_max | 1.075 | 0.988 | 0.985 | 0.972 | 1.33 / 1.15 / 1.10 / 1.08 | +1170 ps |
| prjxray fast_max | 1.070 | 0.974 | 0.987 | 0.971 | 1.31 / 1.16 / 1.11 / 1.07 | +1134 ps |
| **silicon (README)** | **1.176** | **0.987** | **0.959** | **0.969** | **1.22 / 1.13 / 1.13 / 1.09** | **+1053 ps** |

- The **offset** (+988 ps, i.e. b/a = +1053 ps) is reproduced: +948 ps by the patch
  alone and +1170 ps with prjxray.
- The **short-ring excess** (7-link vs 63-link, silicon x1.214) is about half
  reproduced: x1.095 by the patch alone and x1.106 with prjxray. **The remaining 7-link
  median excess of about 9% is unexplained.**
- The **spread** within a length is the same size as silicon's (p90/med
  1.10-1.33 against 1.09-1.22). It is larger than silicon's at 7 links. That
  is expected: two different binaries' placements are mixed, so the
  emulated distribution is not the measured one.

**3. Ring 0** (ro_top 2026-08-18: SDF 4674, measured 6293 ps, "+35%"). The 47
7-link rings here whose emulated pre-patch SDF is within 700 ps of 4674 have a
corrected SDF of 6704 ps (one has 7130). Scaled by each predictor's population
scale:

| predictor | predicted ring-0 period | measured / predicted |
|---|---|---|
| pre-patch SDF (what the repo used) | 4623 (4336..5196) | **1.361** |
| current SDF | 5896 (5896..6271) | 1.067 |
| prjxray slow_max | 6360 (4489..7341) | 0.989 |

So ring 0's +35% is the lut-perm-sink bug first and site pins second.
prjxray's range of 4.5-7.3 ns is the physical-pin lottery that the SDF cannot
see. Taking the longer number, as CLAUDE.md asks when a result is ambiguous,
silicon could be up to 7341/6293 = 17% faster than the worst comparable route
and is 6.7% slower than the corrected SDF predicts.

**4. ro_top re-routed** (4 seeds x 5 rings): slow_max/current-SDF ranges
1.35-1.72. The 7-link ring always has the highest ratio within a route
(1.50-1.72), because its fanout to the BUFG and its few pips leave the
site pins as a larger share.

## What does not work, and why

- **No per-ring pairing.** `build/hw/ro_many_top/raw/gNN.log` (the per-ring
  silicon) and the measured `.bit`/`.sdf` are not in the tree. The measured
  routes came from a pre-2026-08-21 binary, and placement is not stable across
  binaries (build_hw.sh says so), so "the shipped seed" does not reproduce them.
  So the brief's "correlation of residual with predicted pin-delay difference"
  cannot be computed per ring. What I can show: (a) within the model, the
  per-ring deviation from the SDF is the site-pin term (rho ≈ 0.97); (b) at
  the population level, the shapes match as in the table above.
- **Silicon vs slow_max as a bound**: not testable without pairing. The
  population median is at about 0.61 x slow_max. But silicon's 7-link max/median
  (1.25) and the model's min/median (0.58) could pair to above slow_max for an
  unlucky ring. Unknown.
- **research's board-fidelity GLS delay calculator** (JOURNAL 2026-10-2x,
  workstream F1) is **not in this tree**: research/tools holds only `rtz/`,
  cells/gls has no prjxray code, and nothing outside formal/ imports
  `prjxray.timing`. So there was nothing to compare against. `ringdelay.py`'s
  `Net` class is a candidate core for it (it already gives min:max per corner
  per sink).

## Effort to finish

- **Pair per ring (the decisive test): about 1 day**, given the board host's
  `build/hw/ro_many_top/{ro_many_top.bit, raw/gNN.log}` (or a fresh measurement
  of a bitstream built here, about 30 min of board time). Read the bit back with
  bit2fasm. The ring topology from the FASM alone needs fasm2lean's LUT netlist
  plus a cycle finder; ringdelay currently takes cell->site from the routed JSON.
  Then compute the per-ring residual against prjxray and Spearman against the
  site-pin excess.
- **Re-measure the 128 rings against a current-binary build**: 1 build plus 1
  board session (ro_many_measure.py as is). This replaces every number in
  cells/hw/README.md's ring sections, which today are relative to a superseded
  SDF.
- **Emit a min:typ:max SDF from `Net`** for cells/gls/gen.py (PROGRAM.md F1):
  2-3 days. The tree walker and corners already exist. Remaining: map every sink
  pin to SDF instance/pin names, and add FF/carry/BUFG site arcs.

## What it buys the project

1. **The 8.5% → 34.6% guardband story needs a re-measurement.** Its inputs
   (the 128 ratios, the +988 ps intercept, ring 0) are relative to a pre-patch SDF.
   On fresh routes that SDF misses by about 30% on compact 7-link rings for a
   reason that is now fixed. tighten.py's guard was sized from that population.
   With the current SDF, the remaining 7-link excess is about 9% (median), and
   the spread may be smaller or larger; that is unmeasured. This does **not**
   license a smaller guard (CLAUDE.md: take the longer number). It says the
   measured number is about an obsolete predictor.
2. **The current SDF still misses a first-order term**: the physical LUT pin.
   prjxray puts it at 5 ps (A6) to about 516 ps (A1) at slow max, while nextpnr
   charges 25 ps for every pin. A1-A5 are what chains use (A6 is never used),
   and the model's per-route deviation from the SDF is ±20-25% on short chains
   (7-link 0.75-1.23 after scaling). That is the same order as the scatter that
   rules E/A spend guardband on. A rule that read per-pin delays (C-10b's fix)
   would no longer need to cover this part.
3. Silicon sits at about 0.6 of prjxray's slow_max (between fast_max and slow_min),
   which is the expected place for a room-temperature typical die. The
   population gives no sign that prjxray's corners fail to bound this board;
   the per-ring check (above) is what would show it.

## Decisions taken (no one to ask)

- Routed with BD_RLOC=none and no `--freq`, as the measured bitstreams were.
  CLAUDE.md wants `--freq`, so I checked that `--freq 100` gives a
  byte-identical FASM. Default seed plus seeds 1-3 (n=4 routes).
- Built in `formal/tools/prjxdelay/build/` with my own route.sh rather than
  calling build_hw.sh, which writes into cells/build (cells/ is read-only for
  this probe). The yosys script is copied verbatim.
- Silicon numbers are taken from cells/hw/README.md (per-length median, p90,
  max; 2-param fit; the two ro_top tables), not re-derived; the raw logs are absent.
- Did not modify fasm2lean (I import it). Did not run git.
