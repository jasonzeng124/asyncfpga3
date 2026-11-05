# Board queue

Experiments that have passed every check possible without the board, most
valuable first. Each one: branch/commit, exact commands, pass criterion
(self-reporting, never "read the scope"), and what a failure would mean.

## Board list, in order (owner, 2026-11-04: best first; each item judges itself)
1. **gcd_ps with the 1000 vectors** (item #4 below): `hw/board.sh xsdb hw/xsdb_gcd.tcl ../research/board/gcd_ps_e6bb4aec.bit
   ../research/board/gcd_ps_vec1000.hex; echo "exit $?"`. Pass: `=== PASS 1000/1000 ===` and exit 0. Also gives
   per-call latency directly comparable with the full stack's (research/data/gcd_ps/cost_model_vs_board.tsv).
2. **The short-pulse C-element test (H_RUNT)**: research/board/runt/ (runt_top, bit 08529a39; predictions committed
   before any run; README there). 96 C-element loops forced by episodes of routed width -427..+1542 ps against their own
   211-633 ps loops, plus NEG/LONG/PULSE controls. From cells/:

       mkdir -p build/hw/runt_top && cp ../research/board/runt/runt_top.bit ../research/board/runt/instances.tsv build/hw/runt_top/ && \
         xz -dc ../research/board/runt/runt_top_routed.json.xz > build/hw/runt_top/runt_top_routed.json && \
         python3 hw/runt_measure.py; echo "measure exit $?"
       python3 ../research/tools/runt_judge.py build/hw/runt_top/runt_measured.tsv ../research/board/runt/predicted.tsv; echo "judge exit $?"

   Pass: measure prints `=== RIG OK ===` and exits 0 (every control in every trial: NEG never captures, LONG always,
   PULSE k=3 counts an edge every trial), and the judge prints `=== PASS: ... ===`, exit 0 (a capture threshold w* can
   be named). The answer is in the lines after: `=== RUNT CIRCULATES ===` (any TEST cell with >= 2 rising edges in a
   trial) or not, and w* - loop. RIG FAIL means the rig, not the fabric, and nothing else is read.
3. **The fastest design the sim accepts**: currently #2 below (gcd_hw R5 sizes): it passes the combined worst-case gate
   (matched-delay chains 0.21, CARRY4/F7F8/FF SLOW_MAX, the rest 0.288, + the measured residual as scatter) on 8/8 routes
   (research/data/fid/bq2_worstcase.tsv), and the cell check (slow uncalibrated cells) 8/8. #3 (R5 + fast fall, ~6%
   faster) has passed the cell check 8/8; its worst-case gate is running. Commands and criteria under #2/#3.
4. **A ring set on a second route (band transfer)**: research/board/ro_many_2/ (today's ro_many_top, bit 8dc4f1ac,
   predictions committed before any run). From cells/:

       mkdir -p build/hw/ro_many_top && cp ../research/board/ro_many_2/ro_many_top.bit build/hw/ro_many_top/ && \
         for f in ro_many_top_routed.json ro_many_top.sdf; do xz -dc ../research/board/ro_many_2/$f.xz > build/hw/ro_many_top/$f; done && \
         RO_MEAS_TSV=build/hw/ro_many_top/measured.tsv python3 hw/ro_many_measure.py; echo "measure exit $?"
       python3 ../research/tools/ring2_judge.py build/hw/ro_many_top/measured.tsv ../research/board/ro_many_2/predicted.tsv; echo "judge exit $?"

   Pass: measure exit 0 (the readback's own checks) and the judge's `=== PASS ===`, exit 0 (median and per-length
   median error of the 0.288 prediction within +/-5%, every ring inside its FAST_MIN..SLOW_MAX). The judge was
   checked on the first route's data: 0.288 PASS, 0.38 FAIL. A FAIL with every ring inside the corners means the band
   does not transfer between routes (the judge prints this route's own x).

## 1. gcd_hw, fusion on, cloud toolchain, v4 placement, converged select pads -- 16/16 in routed GLS on 8 seeds
**Rule J (verify/arb_fork.py, added 2026-10-26) on this route: pass, worst guarded +463 ps**
(8 seeds: worst +272, raw >= +718). That counts the part of A0's route its branches share as
common, and that part is an ESTIMATE (pip-count fraction; the routed JSON has no per-pip delays).
Without that credit, 3 of 8 routes came out short. See JOURNAL 2026-10-25 "rule J".

Branch claude/research. Bitstream: `research/board/gcd_hw_03e82630.bit`
(sha256 03e82630dcf5c453b40121cdaf86eae0cc79c6c65a69ba1bfa0c83e402141196; the route with
build_hw.sh's default seed; sdf md5 6f8b99e6 (routed.json 1c6a1fb9 on the original build only: it embeds
absolute paths and does not reproduce, audit bq1-repro.md -- compare the sdf); toolchain in the
`.toolchain.txt` beside it: nextpnr 9c732bc6303458df, patches 789a7120c912d393, yosys v0.62,
fasm via prjxray's textX parser).

Use the committed bitstream, not a local rebuild: the local yosys may map a different netlist
(it did for soak_top, see JOURNAL 2026-10-25 19:21), and this bitstream is the one that was
GLS'd. To rebuild the same route in the cloud: `cd cells && BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json
BD_RLOC=v4 ./hw/build_hw.sh gcd_hw`.

    cd cells
    mkdir -p ../build/hw/gcd_hw && cp ../research/board/gcd_hw_03e82630.bit ../build/hw/gcd_hw/gcd_hw.bit
    hw/board.sh python3 hw/gcd_measure.py --program
    sleep 60
    hw/board.sh python3 hw/gcd_measure.py; echo "exit $?"

Pass (self-reporting): the second command prints `PASS -- all vectors correct,
err_sticky=0x0000, ok_sticky=0xFFFF.` and exits 0. Anything else is a FAIL. It also refuses to
judge a die that is not running gcd_hw (scan-alignment check).

What it would mean:
- PASS: the first compiled kernel built entirely in the cloud (fusion on) is correct on silicon,
  including vectors 5/6/7/8/11/12/13 that the August builds failed. It also validates the cloud
  bitstream path end to end (yosys 0.62 + textX fasm parser), which nothing has checked yet.
- FAIL with err bits set: a wrong answer that routed GLS on 4 routes did not show. Send
  `gcd_measure.py`'s full output (errv/absn/abss); GLS of this exact route is reproducible from
  the md5s above.
- FAIL "never checked" on some vectors: a livelock or deadlock on silicon, the August failure
  shape. Compare the mask with 5, 6, 7, 8, 11, 12, 13.
- Refused / scan misaligned: a bitstream generation problem (the fasm or frames path), not the
  design.

Evidence update 2026-10-26: same pads on seeds d and 2-8, rules A/E/H/I/J clean and routed GLS
16/16 errs=0 on all 8; x0.9 and x1.1 corners 16/16 on seeds d, 5, 6, 7, 8 (JOURNAL 2026-10-26 04:13).

Evidence (all in JOURNAL 2026-10-25 19:21): rule E 0/118 violated on all 4 routes; tighten rules
A/H/I 0 violations (rule D 38 = the documented screen); GLS gate ANNOTATE_DONE with 0 SDF
warnings/errors on each; 16/16 vectors, errs=0, laps 19-2719 per 150 us window on each.

Board-fidelity full stack, 8 seeds x 2 corners (2026-10-31, resolver 055edd7; research/data/fid/bq1_fullstack_8seed.tsv;
default-seed sdf 6f8b99e6 reproduced): 16/16 errs=0 and bits EQUIVALENT on all 16 runs; laps vec 6 SLOW_MAX mean
15.9 (15-16), FAST_MIN 45.9 (44-48). #2 on the same stack: SLOW_MAX ~32, FAST_MIN ~88 (the ~1.9-2x of the
nominal GLS holds at both corners). Within-die scatter 1x (band 0.38 + region 0.16 + wire 0.126, draw 1): 8/8 seeds
PASS (vec 6 laps 23-29).
Log-normal (bounded) within-die scatter 1.5x (region 0.24 + wire 0.189), draw 2: 8/8 seeds PASS (vec 6 laps 24-32).
Log-normal 3x (region 0.48 + wire 0.378), draw 2, all 8 seeds: 8/8 PASS 16/16 errs 0 (vec 6 laps 20-32;
research/data/fid/bq1_logn3x_draw2.tsv); draw 3, all 8 seeds: 8/8 PASS 16/16 errs 0 (vec 6 laps 20-30;
research/data/fid/bq1_logn3x_draw3.tsv). The default lengths carry far more scatter margin than R5 (#2/#3 fail at 1.5-2x).

## 2. gcd_hw with route-measured matched-delay sizes (R5) -- ~1.9x laps in routed GLS; every audit and routed GLS (nominal + corners) clean on 8 routes
Same rig, pads and placement as #1, plus per-cell matched-delay sizes `research/data/gcd_hw_sizes_R5.vh`
(220 sizes). History: R2 passed every audit on 8 seeds until rule E learned to launch from the select's
feeding-link C node (69ee32b), which flagged R2 on 2 seeds; R3/R4 padded the asks route by route; R5 adds
`skew.py --slack 500` asks over R4's 8 routes, i.e. every select link with less than +500 ps guarded on any
route was padded to reach it.
Branch claude/research. No bitstream is committed (owner, 2026-10-25); build it in the cloud toolchain
(nextpnr 9c732bc6303458df, patches 789a7120c912d393, yosys v0.62). The default-seed build's sdf md5 is
a9c4e265; check yours with md5sum before trusting the run. Compare the SDF only: the .bit md5 is not reproducible
(header date bytes), and the routed.json md5 recorded earlier (7be3c1cf) was not reproduced by the independent
audit's clean rebuild (b398103e, same sdf) -- a different routed.json md5 is NOT a reason to distrust the build:

    cd cells
    BD_SIZES=../research/data/gcd_hw_sizes_R5.vh BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw
    md5sum build/hw/gcd_hw/gcd_hw.bit build/hw/gcd_hw/gcd_hw_routed.json build/hw/gcd_hw/gcd_hw.sdf
    hw/board.sh python3 hw/gcd_measure.py --program
    sleep 60
    hw/board.sh python3 hw/gcd_measure.py; echo "exit $?"

Pass (self-reporting): `PASS -- all vectors correct, err_sticky=0x0000, ok_sticky=0xFFFF.` and exit 0.
Speed (secondary, only meaningful after a PASS): gcd_measure.py's per-vector latency in housekeeping
cycles per completed gcd; run #1's bitstream the same way and compare. Routed GLS predicts R5 at about
0.5x of #1's latency on the loop vectors (6, 12, 13). The housekeeping ring is placed per route, so
compare ratios across vectors, not absolute cycles.

What it would mean:
- PASS and ~2x: route-measured sizing of a compiled kernel's matched delays is safe and pays on silicon.
- PASS with no speedup: the matched delays are not on silicon's critical cycle; still safe.
- FAIL while #1 passes: a too-short delay that rules A/E/H/I/J and corner GLS did not see -- the most
  important possible result; send the full gcd_measure.py output.

Evidence (JOURNAL 2026-10-26 04:13 session): rules E (with C-node launches)/A/H/I/J 0 violations on
seeds d, 3, 4, 5, 6, 7, 8, 9 (seed 2 did not place: nextpnr post-placement validity check); routed GLS
16/16 errs=0 at nominal, x0.9 and x1.1 on ALL 8 placed routes d, 3-9 (vec 6 nominal: 47 / 42 / 45 / 49 /
50 / 48 / 49 / 48 laps, mean 47.3, vs 24-26 unsized), gate clean on each. Per-arc scatter on R5 seeds 3 and 4: 8.5%
(seed 4), 17%, 25% x2 all 16/16. Its predecessor R2 (same compute sizes, fewer select pads) passed
nominal/corner GLS on 8 seeds and per-arc scatter to 25% (wire mode to 35%) on two routes.

Board-fidelity full stack (bits-decoded netlist + prjxray SDF + fid primitives), 8 seeds x 2 corners: seeds
d,3,4,5 (2026-10-29 early session, old resolver) and 6,7,8,9 (2026-10-29 14:41 session, resolver 055edd7;
research/data/fid/bq2_fullstack_s6-9.tsv): 16/16 errs=0 and bits EQUIVALENT on all 16 runs. Laps vec 6 SLOW_MAX
28-33 (6-9: 31-33), FAST_MIN 77-93 (6-9: 86-93). The resolver change reproduced seed 6 SLOW_MAX exactly (33/27/39).
Arbiter near-tie round trips (research/data/fid/arbtie.md): 0 of 18 ack C-elements below the model's requirement on
seeds 6-9, worst margin 878 ps.
Within-die scatter (band 0.38, draw 1, 2026-10-30/31): 1x (region 0.16 + wire 0.126) PASS on seeds 6, 7, 8, 9; 2x
(0.32 + 0.252) PASS on seeds 7, 8, 9 and FAILS on seed 6 (vectors 7, 8, 12: one lap with an x compare, then stall).
Cause, confirmed by intervention: uori3's matched delay (chain X12-13 Y53-55, region factor 0.49 in this draw)
tracks a datapath at X0-5 Y56-76 (factors 1.56/1.54); with only that chain's arcs and wires scaled back x2.03,
all three vectors pass (39/175/146 laps, errs 0). Same mechanism as #3's seed-9 uori2 failure, beyond what the
ring data supports, so #2 stays queued; if the board fails vectors 7, 8, 12 with the rest passing, suspect uori3.
Log-normal within-die scatter (GLS_SCATTER_LOGN=1, bounded speed-ups, 2026-11-01): 1.5x (region 0.24 + wire 0.189),
draw 2: PASS on seeds 6, 7, 8, 9 (the routes on disk). Seed 6's failing scale on draw 1: between 1.5x and 1.75x.
Fresh seeds (2026-11-03): R5 on seeds 10, 11, 14 every audit clean; seed 13 rule E 6 violations, all one link
(ulink_n106__1 feeding ucond_br34/35/36: raw +3837 ps, guarded -119 ps, fix +1 element); seed 12 does not place (nextpnr
"post-placement validity check failed ... A5FF (no cell)", third time seen). So build #2 with the default seed as
written (that route is the one audited and simulated); another seed can come out rule-E short by one element.

## 3. gcd_hw R5 sizes + link fast fall (BDC_LINK_FASTFALL=1) -- ~6% more laps than #2 (same 8 routes), every audit and routed GLS clean on 8 routes
Run only after #2 passes: it is #2 plus one opt-in change (bd_link's request delay and bd_mux's output delay fall
in one hop; cells/rtl/bd_link.v RFAST, bd_mux.v FASTFALL, committed fdfe098 with tighten.py rule F, which audits
that a fast-fall line drains before its input can rise again). Same rig, pads, placement, sizes.
Toolchain as #2. Default-seed md5s: sdf 61e14755 (compare this one), routed.json f9c4597d (reproduced by the audit, but routed.json
md5s are not portable in general), bit f9fb4b19 (not reproducible):

    cd cells
    BD_SIZES=../research/data/gcd_hw_sizes_R5.vh BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 BDC_LINK_FASTFALL=1 ./hw/build_hw.sh gcd_hw
    md5sum build/hw/gcd_hw/gcd_hw_routed.json build/hw/gcd_hw/gcd_hw.sdf
    hw/board.sh python3 hw/gcd_measure.py --program
    sleep 60
    hw/board.sh python3 hw/gcd_measure.py; echo "exit $?"

Pass: the same PASS line and exit 0 as #1/#2. Speed: compare gcd_measure.py's per-vector latency with #2's; routed
GLS predicts ~0.92x of #2 on the loop vectors.
What it would mean: PASS = the fast request fall is safe on silicon; FAIL while #2 passes = a fall-path hazard that
rules A/E/F/H/I/J and corner/scatter GLS did not see (send the full output).
Evidence (JOURNAL 2026-10-26/27): seeds d, 3-9: rules A/E/F/H/I/J 0, fasm_audit PASS, gate clean, routed GLS 16/16
errs=0 at nominal on all 8 and at x0.9/x1.1 on d, 3, 6, 7, 8, 9; 17% scatter on d and 3. Laps vec 6 mean 50.0
(46-52, 8 routes) vs #2's 47.25 on the same 8 routes (+5.8%; vec 12 +6.0%, vec 13 +5.8%; the earlier "~9%" compared
8 routes with #2's 4, corrected per audit research-stats.md); vec 12 40.4, vec 13 58.6. Rule F worst +888 ps (an existing line).
Reproduction (2026-10-27): an independent rebuild of the default-seed route gives the same routed.json
(f9c4597d) and sdf (61e14755) md5s; on it rules A/E/H/I/J 0, gate clean, GLS 16/16 at nominal, x0.9, x1.1 and
wire scatter 25% (1 draw) and 35% (2 draws).
Board-fidelity full stack (2026-10-27 session 10:12; research/data/fid/fullstack.md): this route, simulated from the
netlist decoded from its own .bit, with prjxray RC-tree delays and the fid primitives: 16/16 errs=0 at FAST_MIN,
SLOW_MAX and band 0.38 (laps vec 6 91 / 33 / 55). At band 0.38 (where the five measured rings sit) the stack predicts
vec 6 ~55 laps per 150 us window. The same stack fails the unpatched lut-pinmap bitstream on an August-shaped route
(vectors 5-8, 11-13 never complete), so it can fail. 
8 seeds (2026-10-29, research/data/fid/bq3_fullstack_8seed.tsv): seeds d,3-9, each simulated from its own .bit
(fid model 78de9c2 + decoder fix 54f2ce6): 16/16 errs=0 at FAST_MIN on 8/8 (laps vec 6 mean 89.6, 83-94) and at
SLOW_MAX on 8/8 (vec 6 mean 32.8, worst seed 4: 31); band 0.38 with region 0.16 + wire 0.126 scatter (the measured
8.5% median ring scatter): 8/8 seeds pass, vec 6 47-54; with 2x that: 7/8 pass, and seed 9 FAILS (draw 1: six
vectors give one lap with an X in the result compare, then stall). Root cause (JOURNAL 2026-10-29): uori2's matched
delay sits ~30 slice rows from the comparator it tracks; the failing draw makes their regions differ ~2.8x in
speed at its threshold (~1.33x the calibrated scatter). Beyond what the ring data supports, so #3 stays queued;
if the board fails vectors 2,3,9,11,13,15 with the rest passing, suspect this bundle first.
Re-run on the 055edd7 resolver (2026-10-30, research/data/fid/bq3_fullstack_newresolver.tsv; audit r16's
follow-pulse fix): all 16 corner runs PASS 16/16, EQUIVALENT, every laps triple identical to the old-resolver
table (vec 6 SLOW_MAX mean 32.75, FAST_MIN 89.6); the seed-9 2x-scatter failure reproduces exactly (same six
vectors). Arbiter near-tie round trips (research/data/fid/arbtie.md): 0 of 18 ack C-elements below the model's
requirement on all 8 routes, worst margin 691 ps (seed d).
Log-normal within-die scatter (GLS_SCATTER_LOGN=1, bounded speed-ups, 2026-11-01): 1.5x the calibrated scatter
(region 0.24 + wire 0.189), draw 2: PASS on all 8 seeds (vec 6 laps 44-56). Seed 9's failing scale on draw 1:
between 1.75x and 2x (linear factors: ~1.33x).
The board's vec 6 should land between the FAST_MIN and SLOW_MAX numbers; ~50-55 laps per 150 us is the band
prediction.

## 4. gcd_ps: the same kernel, 32-bit operands from the PS (no vector table), P1 pad-only sizes -- every audit and the full-stack fid GLS (24/24, both corners) clean on 8 seeds
The owner's lead of 690f156. The kernel, bdc flags, pads (`gcd_hw_pads.json`) and placement (v4) are BQ#1's; the
harness is `cells/hw/gcd_ps.v` (AXI3 register slave on M_AXI_GP0, operands from the host, no vector table). With
full-width operands one bundle needs more delay than BQ#1's: `bridge_i.udut.umux21` violated rule A on 3 of 4 unsized
seeds (-1567/-154/-464 ps), so P1 lengthens it alone, 12 -> 16 links (`research/data/gcd_ps/gcd_ps_sizes_P1.vh`,
research/tools/pad_sizes.py: only rule-A violators lengthened, nothing shortened).

**Formal target**: seed `d` (build_hw.sh's default seed) of this build.
- `research/board/gcd_ps_e6bb4aec.bit`: md5 aa83c8b7a5e6b68e69729131e984c0f4,
  sha256 e6bb4aec70f31fa7579a482d94ec168162656dabf74e833ed57d1a516b809798
- `research/board/gcd_ps_e6bb4aec.fasm.gz`: the .fasm, gzip -n; md5 of the uncompressed .fasm
  2dbf962dbcf01dcd9bd6ad6f7870ca27
- `research/board/gcd_ps_e6bb4aec.boundary.tsv`: the kernel's boundary in this route (the kernel has no pins in
  the bitstream; its ports are internal nets), from research/tools/boundary_map.py on the routed JSON: in =
  a_data[31:0] (bridge_i.a_data_reg FF Q), b_data[31:0] (b_data_reg), rst (SLICE_X2Y29/DFF/Q, ctrl_rst), the ONE
  request net a_req = b_req = start_req (SLICE_X3Y30/C5FF/Q, the req_core FDCE; yosys named it bridge_i.p_end_req),
  out0_ack (SLICE_X4Y34/A6LUT/O6 = ctrl_o_ack & o_req, named n_index_97_ack), p_end_ack; out = a_ack, b_ack,
  start_ack, out0_req (SLICE_X5Y31/C6LUT/O6, core_o_req), out0_data[31:0] (o_data_pl).
- same route: sdf md5 cbdbea3a7416b56010e8ef0aec0331d4, prjxray SDF (xray_delay.py) 8afd5cce25bbc4187cb11808fae1d5a4;
  toolchain in `gcd_ps_e6bb4aec.toolchain.txt` (nextpnr 9c732bc6303458df, all patches ok, yosys 0.62, textX fasm
  parser). Branch claude/research.
Use the committed bitstream (as for #1). To rebuild the same route in the cloud:

    cd cells && BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 \
        BD_SIZES=../research/data/gcd_ps/gcd_ps_sizes_P1.vh ./hw/build_hw.sh gcd_ps

Board run (from cells/; the first is the 16 golden vectors, the second 1000 vectors outside them):

    hw/board.sh xsdb hw/xsdb_gcd.tcl ../research/board/gcd_ps_e6bb4aec.bit; echo "exit $?"
    hw/board.sh xsdb hw/xsdb_gcd.tcl ../research/board/gcd_ps_e6bb4aec.bit ../research/board/gcd_ps_vec1000.hex; echo "exit $?"

`gcd_ps_vec1000.hex` comes from `cells/gls/ps/gen_vectors.py --n 1000 --seed 1`: operands in [0, 2^31), none of
gcd_rig's 16 pairs, expected from bdc/simcheck.py's `ref_gcd` (the transcription of gcd.c) and asserted equal to
math.gcd; none is 0. Its first 24 lines are the vectors the GLS below ran.

Pass (self-reporting): each run prints `liveness pre-check PASS`, then `=== PASS 16/16 ===` (first) and
`=== PASS 1000/1000 ===` (second), and exits 0. Any `MISMATCH`, `TIMEOUT`, a `FAIL:` line or a non-zero exit is a
FAIL. The script programs the PL and re-runs the SLCR bring-up itself (FCLK0 100 MHz).
The script's verdict was checked offline (`tclsh cells/hw/mock_xsdb_gcd.tcl FAULT -- <bit> [vecfile]`, a fake
board with gcd_ps's register map and an independent Euclid gcd): clean, PASS 16/16 and 1000/1000, exit 0 (so the
vector file's ref_gcd answers agree with Euclid on all 1000); one wrong answer or one missing o_req, `PASS 999/1000`
plus `FAIL: 1/1000`, exit 1; A_DATA reading back 0, the liveness pre-check refuses, exit 1. Note `=== PASS k/n ===`
is printed on a failing run too: only `n/n` with exit 0 is a pass.

What it would mean:
- PASS: the compiled kernel computes gcd on full 32-bit operands from outside the die, on 1000 vectors nobody
  chose to suit the route, on silicon. That is the claim the formal work's target is about.
- MISMATCH on some vectors: a wrong answer the full-stack GLS did not show. Send the full output (a, b, got).
- TIMEOUT "o_req rise": a missing answer (livelock or deadlock), the August shape. Note which vectors.
- `A_DATA readback FAILED` or a TIMEOUT on "i_ack rise" for every vector: the AXI bridge or the PS bring-up, not
  the kernel.
- The harness is sequential on purpose (one call completes before the next is offered). formal/FOR-RESEARCH.md
  section 2: the kernel reorders overlapped calls, so a host that overlaps them is not testing this.

Evidence (JOURNAL 2026-11-01 17:31-19:57):
- Audits, P1 seeds d,3-9 (`research/data/gcd_ps/p1_audit_8seed.tsv`): rule A 0 on all 8 (umux21 margin mean 1456 ps,
  range 358-1889, guardband applied), rule D 38 (the screen, as on #1), E 0, J ok, build_hw PASS incl. fasm_audit.
  nextpnr's fclk0 estimate 343-447 MHz against the 100 MHz FCLK0 (build_hw.sh passes no --freq for gcd_ps, so its
  "PASS at 12.00 MHz" line means nothing; the estimate is the number).
- Full stack (`research/data/gcd_ps/p1_fullstack.tsv`): each seed's netlist decoded from its own .bit with the PS7
  (fasm2net --ps7), prjxray SDF, fid primitives, a behavioural PS7 running the host sequence above over the 24
  vectors: seeds d,3-9 x SLOW_MAX/FAST_MIN: 24/24 ok, 0 err, 0 hang, fasm_equiv EQUIVALENT on all 16 runs; gate
  ANNOTATE_DONE with 0 SDF warnings on all 16. (0x7fffffff, 0x7ffffffe), the longest vector: 15.0 us mean
  (14.6-15.4) from i_ack to o_req at SLOW_MAX, 5.3 us (5.2-5.45) at FAST_MIN.
- Within-die scatter 1x (band 0.38 + region 0.16 + wire 0.126, the measured 8.5% median ring scatter; draw 1):
  8/8 seeds 24/24, EQUIVALENT (`research/data/gcd_ps/p1_scatter1x.tsv`; out0 margin on 6-9 +5.96..+7.41 ns).
  Log-normal 1.5x (region 0.24 + wire 0.189, draw 2), all 8 seeds: 24/24, EQUIVALENT, out0 margin +5.93..+9.07
  ns, no late change (`research/data/gcd_ps/p1_logn15.tsv`); draw 3, all 8 seeds: 24/24, out0 margin +6.19..+9.95 ns
  (`p1_logn15_draw3.tsv`). BQ#4 now has BQ#1's scatter coverage. Beyond it (draw 2): log-normal 2x 8/8 and 3x 8/8
  seeds 24/24 (out0 margin >= +5.07 ns), 5x on seed d 24/24 (`p1_logn2x.tsv`, `p1_logn3x.tsv`): no scatter level tried
  breaks this design (P1 keeps default lengths; the tightened R5 of #2/#3 fails at 1.5-2x).
- **Every vector the board run uses, pre-simulated on the formal target itself**: all 1000 of gcd_ps_vec1000.hex on
  the netlist decoded from gcd_ps_e6bb4aec.bit, full stack, SLOW_MAX and FAST_MIN: 1000/1000 ok, 0 err, 0 hang at
  both corners, out0 margin >= +12.0 / +4.1 ns, no late change; and at band 0.38 + 1x within-die scatter (the
  board-like point) 1000/1000, margin >= +7.3 ns (`research/data/gcd_ps/p1_vec1000_target.tsv`).
  So a board MISMATCH or TIMEOUT on any of them is a disagreement with this model, vector by vector.
- The harness can fail: the same netlist with two expected values corrupted gives ok=1 err=2.
- umux21 drives out0, and the PS reads O_DATA >= 2 synchronizer clocks after out0_req, so this harness cannot see
  an out0 bundling violation (umux21 cut to 1 link: still 24/24). Measured instead at the kernel boundary with an
  out0 bundling monitor (`research/data/gcd_ps/p1_out0_bundle_8seed.tsv`): P1 on all 8 seeds, SLOW_MAX mean +12.3 ns
  (worst +11.3, seed 5), FAST_MIN mean +4.2 ns (worst +3.98, seed 5) between the last out0_data change and out0_req,
  no late change; seed d with 64 vectors 64/64 at both corners, same margins; the monitor's negative control
  (umux21's data LUTs 20x slower) shows 23-24 late changes up to 10 ns after the request while the harness still
  says 24/24. On this bundle rule A over-charges: even 1 link measures +0.57 ns at FAST_MIN where rule A asks
  for 13. P1 is kept (a delay that is too long only costs time; this one is on the exit path, once per call).
- CDC (read in gcd_ps.v): STATUS.i_ack and STATUS.o_req reach the PS clock through 2-flop synchronizers; the
  kernel-facing request is a flop cleared asynchronously by the kernel's own i_ack (the pulse adapter), so a host
  holding CTRL.i_req for milliseconds over JTAG cannot wedge the kernel; A/B are written before the CTRL write that
  raises the request and stay unchanged until the result is read.

## Owner-side check, not a board experiment (cheap, still useful)
ANSWERED in the cloud on 2026-10-25: the failure was the netlist, not the patch or the chipdb.
yosys 0.62 maps soak_top's two 8-input functions to MUXF7/MUXF8, and rloc_stamp gave their LUTs
slots no placement can honour (fixed in 77b20a8). The check below still tells whether the local
yosys makes MUXF7/F8 here (`grep -c MUXF build/pnr/synth.log`); if it does not, the two
toolchains produce different netlists from the same source, which is worth knowing.
On the owner's machine, with the local toolchain rebuilt from this branch's
patches/ (the local one has only main's patches, see the first journal entry):

    cd cells && BD_NO_TIGHTEN=1 ./flow.sh; echo "exit $?"

Pass: `flow.sh PASS`, exit 0. If it passes there and fails in the cloud
(`Unable to find legal placement ... rdly_chain`), the difference is the chipdb
or the build, not the patch. If it fails there too, the committed
nextpnr-xilinx-rloc-group.patch is not the one PR #1's routed numbers came from.

## Owner-side data request (no board needed): the August n=128 ring raw data -- DONE (owner, db3c299b; result 2026-11-03)
**Delivered and used.** `research/board/ro_many_aug/` (bit, fasm, routed JSON, SDF, toolchain, measured.tsv). Result in
`research/data/fid/ring128/README.md`: on the measured route, all 128 periods lie between the full stack's FAST_MIN and
SLOW_MAX; the band model at 0.38 misses by +11.5% (MISMATCH), and one global x = 0.288 predicts every ring within 3%
(held-out splits all pass). The request text below is kept for the record.

The board-fidelity GLS (PROGRAM.md, "THE priority") has to be validated ring by ring. The repo has the ring
summary (76/128 slower than the SDF, offset ~+988 ps) but not the per-ring board periods, nor the August
`ro_many_top` routed.json/SDF/bit they were measured on (that route predates the lut-perm-sink patch and cannot be
rebuilt). If they still exist on the owner's machine, commit them under `research/board/ro_many_aug/`:
the raw `g*.log` (or whatever ro_many_measure.py read), `ro_many_top_routed.json`, `ro_many_top.sdf`, the `.bit`,
and its toolchain.txt. Self-check: `python3 cells/gls/fid/ring_predict.py --help` names the inputs it needs;
`md5sum` of the .bit should match any md5 recorded in the JOURNAL for that build.
Simplest form (no board needed, reads the cached raw logs in `build/hw/ro_many_top/raw`):

    cd cells && RO_OFFLINE=1 RO_MEAS_TSV=measured.tsv python3 hw/ro_many_measure.py; echo "exit $?"

Pass: exit 0 and `measured.tsv` has 128 rows (`g b links measured_ps spread predicted_ps`). Commit it with the
routed.json + SDF of that build; the cloud side runs `cells/gls/fid/acceptance.py --ro-many-data ...` on it.
