# Board queue

Experiments that have passed every check possible without the board, most
valuable first. Each one: branch/commit, exact commands, pass criterion
(self-reporting, never "read the scope"), and what a failure would mean.

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
Within-die scatter (band 0.38, draw 1, 2026-10-30): 1x (region 0.16 + wire 0.126) PASS on seeds 6 and 7 so far; 2x
(0.32 + 0.252) PASS on seed 8 and FAILS on seed 6 (vectors 7, 8, 12: one lap with an x compare, then stall).
Cause, confirmed by intervention: uori3's matched delay (chain X12-13 Y53-55, region factor 0.49 in this draw)
tracks a datapath at X0-5 Y56-76 (factors 1.56/1.54); with only that chain's arcs and wires scaled back x2.03,
all three vectors pass (39/175/146 laps, errs 0). Same mechanism as #3's seed-9 uori2 failure, beyond what the
ring data supports, so #2 stays queued; if the board fails vectors 7, 8, 12 with the rest passing, suspect uori3.

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
The board's vec 6 should land between the FAST_MIN and SLOW_MAX numbers; ~50-55 laps per 150 us is the band
prediction.

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

## Owner-side data request (no board needed): the August n=128 ring raw data
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
