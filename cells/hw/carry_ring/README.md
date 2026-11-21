# carry_ring: where this die sits in prjxray's CARRY4 and MUXF7 band

Written 2026-11-17 for research (PROGRAM "First: where does the board sit"; formal A13 / C36-C42). Untrusted
until a board run: everything below is simulation and construction checks.

## Why
The 128 August rings pin LUT + wire arcs at x = 0.288 of [FAST_MIN, SLOW_MAX] (research/data/fid/ring128). CARRY4
and F7/F8 (`SELMUX2_1`) arcs have never been measured, and no kernel latency can pin them (formal A13: CARRY/F7
over 0.2-1.0 changes collatz per-iteration time by 0.00 ns). The draws therefore spread them over [0.20, 1.0], and
the weakest races of the fastest candidates (xorshift item 35's loop-entry compare -> steer, ~0 ps at CARRY ~0.9;
collatz x0.55 failing draws only at CARRY/F7 0.75-0.91) live in exactly that range. This design measures it.

## Design (`carry_ro_top.v`)
`hw/ro_many_top.v`'s instrument, unchanged where the host depends on it (BSCANE2 USER1, 48-bit DR, TAG 0xA5,
constants 8/9/10, sampler 12, group echo 13, control [3:0] addr [4] run [5] clear [9:6] group; 8 slots = 8 BUFG +
8 32-bit counters), with **G = 8 groups x 8 slots = 64 rings**. Ring (g, b) has kind `KIND[(g+b)%8]` =
{L8, C1, C4, F8, C16, L16, C32, F16}: each kind once in every slot and once in every group (8 placements per kind
per route), and **group 0 holds one ring of every kind**. Every ring closes through ro_many's NAND
(`fb = ~(z & en)`, the node the slot mux taps).

| kind | loop | what it adds over the L rings |
|---|---|---|
| L8, L16 | fb -> 8 / 16 LUT1 buffers -> NAND (ro_many's ring) | reference: pins x on this bitstream |
| C1, C4, C16, C32 | fb -> 5 LUT1 -> CARRY4[0].S0 -> CO3 -> CIN of CARRY4[1] -> CO3 ... CARRY4[N-1].CO3 -> NAND | S0->CO3 once, CIN->CO3 N-1 times (CYINIT 1, DI 0, S = 1 via one LUT1 of `en` per S pin) |
| F8, F16 | fb -> 8 / 16 MUXF7 stages (I0 = 0, I1 = 1 constants, S = previous stage) -> NAND | MUXF7 S0->OUT per stage (the bd_mux select arc) |

The 5 lead-in LUTs keep C1's period (~6.6 ns at x = 0.288) inside what a BUFG + counter follows (slowest slot
counter: nextpnr Fmax 215 MHz at its own slow numbers; fastest ring at FAST_MIN 3.3 ns, ~5.6 ns at x = 0.29).

A first version drove the MUXF7 data inputs from `en` (I1 = en, I0 = ~en): parked, every stage was an inverter,
and selecting the group injected several edges at once. The GLS caught it (F8 ran at 1.04 ns instead of 9.3 ns);
silicon would keep such a multi-edge mode too. Now I0/I1 are constants (every stage a buffer whether or not
selected) and each ring releases exactly one edge; carry rings are clean by construction (header).

**Measured quantity.** Per ring the full-stack period is linear: `P = LO + x R + yc C + yf F` (LO = FAST_MIN period,
R / C / F = SLOW_MAX-FAST_MIN span of LUT+wire+site-pip / CARRY4 IOPATH / SELMUX2_1 IOPATH arcs), which is exactly
what `cells/gls/gen.py` annotates under `GLS_SDF_FIELD=band GLS_SDF_BAND=x GLS_SDF_BAND_CELL=CARRY4=yc,SELMUX2_1=yf`.
`carry_fit.py` fits x, yc, yf to the 64 measured periods.

## Files
| file | what |
|---|---|
| `carry_ro_top.v` | the design |
| `build.sh OUTDIR SEED [FREQ]` | build_hw.sh's recipe (BD_NO_TIGHTEN / BD_RLOC=none path), toolchain.sh first, `--seed`, `--freq` |
| `fullstack.sh BUILDDIR` | xray_delay -> fasm2net --bit -> fasm_equiv -> check_chains -> carry_predict --check-gen; `GLS=1` adds the event GLS |
| `check_chains.py` | on the netlist DECODED FROM THE BITS: carry chain lengths and sites, S pins, carry-in, MUXF7 stages |
| `carry_predict.py` | ring walk on the prjxray SDF -> per-ring LO/R/C/F (`predicted.tsv`); `--check-gen` vs gen.py's reader; `--summary`; `--compare-gls` |
| `carry_gls.sh`, `tb_carry.v` | event GLS (GLS_MODEL=fid) of group 0 on the decoded netlist at one band point |
| `carry_measure.py` | board run: imports `hw/ro_many_measure.py` (its xsdb TCL, hw_server bring-up, decode), readback checks, `measured.tsv`, then the fit |
| `carry_fit.py` | the fit and the self-judging verdict; `--selftest x yc yf sigma [c_offset_ps]` on synthetic rings |

Board copies (bits + predictions committed before any run): `research/board/carry/s1/`, `research/board/carry/s2/`.

## Builds
`source /root/dev2/lib/fpgatoolchain/openxc7/export.sh; cells/hw/carry_ring/build.sh OUT SEED 100` then
`cells/hw/carry_ring/fullstack.sh OUT` (GLS=1 for the event GLS). nextpnr 9c732bc6303458df, toolchain.sh all ok
(toolchain.txt in each dir), source md5 f8ddaca8. 3140 LUT sites, 488 CARRY4 (424 ring + 64 counter), 9 BUFG.

| route | seed / --freq | .bit md5 | predicted.tsv md5 | fasm_audit | bits vs routed JSON | check_chains | nonxray rings |
|---|---|---|---|---|---|---|---|
| s1 | 1 / 100 MHz | 40a8547393641d3dec64d584cb3c9acc | ad2b96767f6ee35db32d28bfb0a66ff1 | PASS | EQUIVALENT | ALL CHAINS OK | none |
| s2 | 2 / 100 MHz | 19ae3639d163b6d229ab7f88ac7b7cfd | cabff6263152808d379ef42f4cb08331 | PASS | EQUIVALENT | ALL CHAINS OK | none |

The carry arcs are really in the loops: in the decoded bits the chains are exactly 8 x {1, 4, 16, 32} (+ 8 x 8 counter
chains) on the same site sequences nextpnr placed, first CARRY4 PRECYINIT = 1, every S pin LUT-driven; the walk
finds one cycle per ring with N CARRY4 arcs (ncarry column) and 8/16 SELMUX2_1 arcs; and the GLS period moves with
y exactly as the walk predicts (below). Known model gap: a CO3->CIN link across the Y49/Y50 clock-region boundary
has no prjxray node (xray_delay keeps nextpnr's 110 ps; seen on an earlier seed-1 build); `carry_predict` flags such
a ring `nonxray` and the fit leaves it out. Neither committed route has one.

## Simulation: period vs y (x = 0.288; median over the 8 placements, ns)
Walk of the prjxray SDF (`carry_predict.py`; `--check-gen`: gen.py's own reader agrees to <= 1 ps/arc).

Route s1:

| kind | n | FAST_MIN | y=0.0 | y=0.2 | y=0.4 | y=0.6 | y=0.8 | y=1.0 | SLOW_MAX | y 0.2 -> 1.0 |
|---|---|---|---|---|---|---|---|---|---|---|
| L8 | 8 | 5.08 | 7.88 | 7.88 | 7.88 | 7.88 | 7.88 | 7.88 | 14.81 | +0.0% |
| L16 | 8 | 9.73 | 15.12 | 15.12 | 15.12 | 15.12 | 15.12 | 15.12 | 28.42 | +0.0% |
| C1 | 8 | 4.42 | 6.50 | 6.65 | 6.79 | 6.93 | 7.08 | 7.22 | 12.37 | +8.7% |
| C4 | 8 | 4.51 | 6.54 | 6.78 | 7.01 | 7.25 | 7.48 | 7.72 | 12.95 | +13.9% |
| C16 | 8 | 6.54 | 9.00 | 9.59 | 10.19 | 10.78 | 11.38 | 11.98 | 18.00 | +24.9% |
| C32 | 8 | 7.53 | 9.99 | 11.09 | 12.18 | 13.28 | 14.38 | 15.47 | 21.55 | +39.6% |
| F8 | 8 | 5.64 | 7.85 | 8.48 | 9.11 | 9.75 | 10.38 | 11.01 | 16.56 | +29.9% |
| F16 | 8 | 10.74 | 14.93 | 16.19 | 17.45 | 18.71 | 19.97 | 21.23 | 31.59 | +31.2% |

Route s2:

| kind | n | FAST_MIN | y=0.0 | y=0.2 | y=0.4 | y=0.6 | y=0.8 | y=1.0 | SLOW_MAX | y 0.2 -> 1.0 |
|---|---|---|---|---|---|---|---|---|---|---|
| L8 | 8 | 4.98 | 7.70 | 7.70 | 7.70 | 7.70 | 7.70 | 7.70 | 14.46 | +0.0% |
| L16 | 8 | 9.82 | 15.22 | 15.22 | 15.22 | 15.22 | 15.22 | 15.22 | 28.60 | +0.0% |
| C1 | 8 | 4.32 | 6.55 | 6.69 | 6.83 | 6.98 | 7.12 | 7.26 | 12.77 | +8.5% |
| C4 | 8 | 4.91 | 7.14 | 7.37 | 7.61 | 7.84 | 8.08 | 8.31 | 13.81 | +12.8% |
| C16 | 8 | 5.96 | 8.29 | 8.90 | 9.50 | 10.10 | 10.71 | 11.31 | 17.19 | +27.1% |
| C32 | 8 | 7.66 | 10.08 | 11.17 | 12.27 | 13.36 | 14.46 | 15.56 | 21.53 | +39.3% |
| F8 | 8 | 5.72 | 7.93 | 8.58 | 9.22 | 9.86 | 10.50 | 11.14 | 16.61 | +30.0% |
| F16 | 8 | 10.84 | 14.97 | 16.24 | 17.52 | 18.79 | 20.06 | 21.33 | 31.61 | +31.3% |

**Event GLS of the decoded bitstream** (group 0, GLS_MODEL=fid, `carry_gls.sh`; period in ps; walk = same ring's
linear terms):

Route s1 (from the run log; its gls.tsv was not kept):

| point | L8 | C1 | C4 | F8 | C16 | L16 | C32 | F16 |
|---|---|---|---|---|---|---|---|---|
| FAST_MIN | 5190 (+0) | 3706 (+0) | 4468 (+0) | 5856 (+0) | 5728 (+0) | 9872 (+0) | 7072 (+0) | 10970 (+0) |
| SLOW_MAX | 14938 (+0) | 10902 (+0) | 13030 (+0) | 17026 (+0) | 16542 (+0) | 28240 (+0) | 20100 (+0) | 32222 (+0) |
| x 0.288, y 0.2 | 8000 (+3) | 5718 (+2) | 6834 (+4) | 8796 (+5) | 8566 (-11) | 15174 (+12) | 10354 (+4) | 16542 (+6) |
| x 0.288, y 0.6 | 8000 (+3) | 6000 (+1) | 7308 (+5) | 10076 (+5) | 9778 (-6) | 15174 (+12) | 12508 (+5) | 19070 (+13) |
| x 0.288, y 1.0 | 8000 (+3) | 6284 (+1) | 7780 (+5) | 11352 (+1) | 10992 (+1) | 15174 (+12) | 14660 (+4) | 21582 (+3) |
| x 0.22, y 0.2 | 7328 (-7) | 5272 (-3) | 6324 (-4) | 8252 (+3) | 8032 (-15) | 13902 (-11) | 9826 (-5) | 15522 (+3) |

Route s2 (`research/board/carry/s2/gls.tsv`):

| point | L8 | C1 | C4 | F8 | C16 | L16 | C32 | F16 |
|---|---|---|---|---|---|---|---|---|
| FAST_MIN | 4778 (+0) | 3280 (+0) | 4740 (+0) | 5188 (+0) | 5928 (+0) | 9856 (+0) | 7728 (+0) | 10272 (+0) |
| SLOW_MAX | 14154 (+0) | 9756 (+0) | 13144 (+0) | 15224 (+0) | 16850 (+0) | 28692 (+0) | 21934 (+0) | 29826 (+0) |
| x 0.288, y 0.2 | 7484 (+6) | 5082 (+1) | 7058 (+1) | 7802 (+5) | 8798 (-10) | 15290 (+9) | 11314 (-23) | 15336 (-2) |
| x 0.288, y 0.6 | 7484 (+6) | 5376 (+3) | 7526 (+1) | 9082 (+5) | 10010 (-5) | 15290 (+9) | 13518 (-12) | 17916 (+6) |
| x 0.288, y 1.0 | 7484 (+6) | 5668 (+2) | 7996 (+3) | 10358 (+1) | 11224 (+2) | 15290 (+9) | 15724 (+1) | 20484 (+1) |
| x 0.22, y 0.2 | 6834 (-7) | 4684 (-6) | 6560 (-5) | 7336 (+4) | 8254 (-16) | 13984 (-16) | 10714 (-30) | 14438 (-7) |

All 96 points: |GLS - walk| <= 30 ps (per-arc rounding), `compare-gls` AGREE on both routes. The L rings do not move with y; every C and F ring moves by its predicted amount.

**Can it tell y = 0.2 from y = 1.0?** C32 moves +39%, C16 +25-27%, F8/F16 +30-31% between y = 0.2 and 1.0; the L
rings move 0. Ring scatter on the board was 0.76% median (sd 1.08%) per ring (ring128). `carry_fit.py --selftest`
(synthetic rings from each route's terms, Gaussian per-ring scatter):

| route | synthetic truth (x, yc, yf, scatter) | fitted yc [slope] | fitted yf [slope] | verdict |
|---|---|---|---|---|
| s1 | 0.288, 0.31, 0.31, 1% | 0.30 +-0.01 [0.30 +-0.01] | 0.30 +-0.01 [0.27 +-0.02] | PASS |
| s1 | 0.288, 0.20, 0.20, 1% | 0.19 +-0.01 | 0.19 +-0.01 | PASS |
| s1 | 0.288, 1.00, 1.00, 1% | 0.99 +-0.01 | 0.99 +-0.01 | PASS |
| s1 | 0.288, 0.50, 0.80, 2% | 0.48 +-0.01 | 0.78 +-0.02 | PASS |
| s2 | 0.288, 0.20, 0.20, 1% | 0.19 +-0.01 [0.19 +-0.01] | 0.19 +-0.01 [0.16 +-0.02] | PASS |
| s2 | 0.288, 1.00, 1.00, 1% | 0.99 +-0.01 [0.99 +-0.01] | 0.99 +-0.01 [0.95 +-0.02] | PASS |
| s2 | 0.22, 0.31, 0.85, 2% | 0.29 +-0.01 [0.30 +-0.02] | 0.83 +-0.02 [0.77 +-0.04] | PASS |
| s1 | 0.288, 0.31, 0.31, 1% + 300 ps on every C ring | 0.36 [0.30] | | FAIL (slope vs absolute) |
| s1 / s2 | ... + 500 ps | 0.41 [0.30] | | FAIL (slope vs absolute) |
| s1 | ... + 1000 ps | 0.52 [0.30] | | FAIL (slope, C16 vs C32, residual 3.8%) |

(The synthetic noise draw is the same seed in every row, which is why the F slope fit errs the same way, ~1.5 sigma.)

So at 1% per-ring scatter yc is resolved to +-0.01 (slope fit +-0.01) and yf to +-0.01 (+-0.02): y = 0.2 and 1.0 are
~80 sigma apart. The negative control (an unmodelled 500 ps fixed cost on every carry ring) biases the absolute fit
to 0.41 and is caught by the slope-vs-absolute check; 300 ps is caught too.

## Pass criterion (carry_fit.py; carry_measure.py exits 2 before it if the readback is not a measurement)
PASS needs: >= 6 rings of every kind; median |residual| <= 3% (one x, one yc, one yf explain every ring); yc from C16
alone vs C32 alone, and yf from F8 vs F16, agree within 3 sigma + 0.05; the slope fit (free fixed cost per C and per
F ring, so y comes from differences between lengths only) agrees with the absolute fit within 3 sigma + 0.03;
sigma(y) <= 0.10. Uncertainty = max(normal-equation sigma, jackknife over the 8 groups). Output ends with

    CARRY_BAND y=0.30 +-0.01 [slope fit 0.30 +-0.01] (sim, x=0.290: C32 median 11.11 ns at y=0.2, 15.49 ns at y=1.0; measured 11.60 ns)
    F7_BAND    y=0.83 +-0.01 [slope fit 0.87 +-0.02] (sim, ...)
    LUT_BAND   x=0.290 +-0.002 (ring128, August route: 0.288)
    === PASS === ...

(those numbers are the offline end-to-end test: fake xsdb logs at x 0.288 / yc 0.31 / yf 0.85 through
`RO_OFFLINE=1 carry_measure.py`.)

## Drafted BOARD-QUEUE item (paste)

N. **The CARRY4 / MUXF7 band (carry_ro_top): the one number no kernel can give** -- research/board/carry/ (two routes,
   s1 bit 40a85473, s2 bit 19ae3639; predictions committed before any run; cells/hw/carry_ring/README.md). 64 ring
   oscillators per bitstream on ro_many's JTAG harness: LUT-only rings (pin the LUT/wire band x again), rings through
   1 / 4 / 16 / 32 chained CARRY4 (CIN->CO3) and through 8 / 16 MUXF7 selects (S0->OUT), 8 placements of each. About
   2-3 minutes per bitstream (8 groups x 2 windows x 4 s). From cells/:

       for s in s1 s2; do
         hw/board.sh python3 hw/carry_ring/carry_measure.py ../research/board/carry/$s/carry_ro_top.bit \
           ../research/board/carry/$s/predicted.tsv build/hw/carry_ro_top_$s; echo "measure $s exit $?"
       done

   (xsdb / hw_server from VIVADO_LAB as for item 5; the script programs the device itself on the first group.)
   Pass: exit 0 and `=== PASS ===` on both routes. Exit 2 = the readback failed its own checks (constants, group
   echo, liveness, poison, overflow) or a ring is not the ring asked for: nothing is a measurement. Exit 1 = the
   band model does not explain these arcs (residual > 3%, C16 vs C32 or F8 vs F16 disagree, or the slope fit
   disagrees with the absolute fit); the line says which. The answer is the three lines before the verdict:
   `CARRY_BAND y=... +-...`, `F7_BAND y=... +-...`, `LUT_BAND x=...`; please paste them (and build/hw/carry_ro_top_s*/
   measured.tsv + raw/) back. Simulated: C32 is 11.1 ns at y = 0.2 and 15.5 ns at y = 1.0 (x 0.288), F16 16.2 / 21.3
   ns; at 1% ring scatter the fit resolves y to +-0.01-0.02. The two routes must agree with each other within their
   sigmas; if they do not, that is the finding.

## What this does not measure
- Which CARRY4 arcs: the loop is CIN->CO3 (N-1 times) plus S0->CO3 once. CIN->CO0..2, S->O / CIN->O (the XOR
  outputs) and DI->CO are not in any loop; the band model gives all CARRY4 arcs one y, and that assumption is what
  the result would carry over to them. Compare chains in the kernels (ucmpi) leave through CO3, so their arcs are
  mostly these. MUXF7: only S0->OUT (select); the I0/I1->OUT data arcs and MUXF8 are not in a loop.
- The CO3->CIN link itself is 0 ps in prjxray (9 ps across the HCLK row) and is charged to x, not y; anything the
  silicon spends there shows up in yc (it scales with N), as it would in a kernel.
- One die, one temperature, one supply, like ring128. The fit also gives this run's x, so a temperature shift
  between August and the run shows up as x != 0.288 rather than in y.
