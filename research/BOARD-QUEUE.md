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
build_hw.sh's default seed; routed.json md5 1c6a1fb9, sdf md5 6f8b99e6; toolchain in the
`.toolchain.txt` beside it: nextpnr 9c732bc6303458df, patches 789a7120c912d393, yosys v0.62,
fasm via prjxray's textX parser).

Use the committed bitstream, not a local rebuild: the local yosys may map a different netlist
(it did for soak_top, see JOURNAL 2026-10-25 19:21), and this bitstream is the one that was
GLS'd. To rebuild the same route in the cloud: `cd cells && BDC_SELECT_PADS=hw/gcd_hw_pads.json
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

## 2. gcd_hw with route-measured matched-delay sizes (R2) -- ~2.0x laps in routed GLS, every audit and routed GLS clean on 8 seeds
Same rig, pads and placement as #1, plus per-cell matched-delay sizes `research/data/gcd_hw_sizes_R2.vh`
(207 sizes; 199.9 ns of matched delay built per route, against 547.7 ns at bdc/emit.py's estimate).
Branch claude/research. No bitstream is committed (owner, 2026-10-25); build it in the cloud toolchain
(nextpnr 9c732bc6303458df, patches 789a7120c912d393, yosys v0.62). The default-seed build's md5s were
bit f3caefef, routed.json f51f2bf9, sdf 885b619f; check yours with md5sum before trusting the run:

    cd cells
    BD_SIZES=../research/data/gcd_hw_sizes_R2.vh BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw
    md5sum build/hw/gcd_hw/gcd_hw.bit build/hw/gcd_hw/gcd_hw_routed.json build/hw/gcd_hw/gcd_hw.sdf
    hw/board.sh python3 hw/gcd_measure.py --program
    sleep 60
    hw/board.sh python3 hw/gcd_measure.py; echo "exit $?"

Pass (self-reporting): `PASS -- all vectors correct, err_sticky=0x0000, ok_sticky=0xFFFF.` and exit 0.
Speed (secondary, only meaningful after a PASS): gcd_measure.py's per-vector latency in housekeeping
cycles per completed gcd; run #1's bitstream the same way and compare. Routed GLS predicts R2 at about
0.51x of #1's latency on the loop vectors (6, 12, 13). The housekeeping ring is placed per route, so
compare ratios across vectors, not absolute cycles.

What it would mean:
- PASS and ~2x: route-measured sizing of a compiled kernel's matched delays is safe and pays on silicon
  for gcd, as rule-A-only sizing did for xorshift in August (1.99x).
- PASS with no speedup: the matched delays are not on silicon's critical cycle (the GLS's flat cell arcs
  overstate them); still safe.
- FAIL while #1 passes: a too-short delay that rules A/E/H/I/J and corner GLS on 8 routes did not see --
  the most important possible result; send the full gcd_measure.py output.

Evidence (JOURNAL 2026-10-26 04:13 session): rules E/A/H/I/J 0 violations on seeds d, 2-8, worst
guarded rule A margin +190 ps (seed 2); routed GLS 16/16 errs=0 at nominal on all 8
seeds and at x0.9/x1.1 on d, 2-7 (gate clean on each); per-arc scatter to 25% 16/16 on two routes.
Laps: vec 6 mean 49.5 (47-54) vs 24-26 unsized. Sizes derived by hw/tighten_loop.sh gcd_hw over fresh seeds plus
1 link of headroom per cell, because sizes accepted on 3 seeds failed rule A on a 4th.

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
