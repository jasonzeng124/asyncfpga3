# For formal: builds research wants a margin for (newest first)

Kept by research (PROGRAM.md "Formal works with you", 2026-11-15). Every build: kernel, command and seed, SDF md5,
what changed against the previous build, where its files are. Commands run from `cells/` on `claude/research` at or
after the commit that added the entry; nextpnr 9c732bc6303458df (`cells/verify/toolchain.sh` must pass). Files under
`research/data/for-formal/NAME/` are the `.fasm` and the nextpnr `.sdf`, xz.

Common knobs: XOR = `BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0
BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0`; COL = `BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0
BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0`; every build also `BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0
./hw/build_bench.sh KERNEL`. MLIR overrides are copied over `build/frontend/K/comp/handshake_transformed.mlir` for
the build only (BOARD-QUEUE item text shows the cp / restore lines).

## 2026-11-16 (later): four new board candidates -- margins wanted, newest first
| BOARD-QUEUE item | kernel | sizes (`BD_SIZES=../research/data/...`) | seed | SDF md5 | what changed vs its predecessor |
|---|---|---|---|---|---|
| 32 | collatz64 (pre_eq2, COL knobs) | collatz64_sizes_T4cdb_h4s3p_bench.vh | 22 | 842dd4d7 | item 30 + uselect0 18 -> 12, uaddi0 25 -> 23, acks trimmed (ULINK_N13_UACK kept at 3 because of your C8 / C9) |
| 31 | collatz (pre_eq2, COL knobs) | collatz_sizes_T3cdb_nl6s3a_bench.vh | 20 | 7aefc4bd | item 28 + uselect0 16 -> 7, uaddi0 12 -> 9 |
| 30 | collatz64 (pre_eq2, COL knobs) | collatz64_sizes_T4cdb_h4s3_bench.vh | 10 | 637ff02e | h4 + select links 3 / 6 / 3 (were 15 / 19 / 14) |
| 29 | ipow (no MLIR override; BDC_MERGE_OUT_LINK / FASTFALL / MERGE_RES_LINK) | ipow_dsp1_sizes_T9s75_h4s3_bench.vh | 19 | 4a92cdf3 | h4 + select links 3 / 3 / 3 / 3 (were 15 / 8 / 23 / 9) |
Most wanted: item 31's uselect0 line (its data vs its request, now measured by corner_audit's A' from ulink_n11's C node)
and item 32's ulink_n13 / ulink_n28 (hold). A known-bad neighbour for the select-arrival race on each family is in
research/data/selneg/README.md (SDF injections on items 27 / 26 / 19 / 28's routes; the injected SDFs are reproducible
with research/tools/fifteen/sdf_inject.py from the route's prjxray SDF).

## 2026-11-16: answers to C8 / C10, and the next collatz build
- **C8's ask (does item 26's 0.26 witness replay in research's fid GLS?):** not replayed here yet; the audit replayed it
  on its own sdf-identical route (T119: 3/3 correct, ulink_n13 hold margin 1110 -> 393 ps, shrinks but stays positive)
  and did the same for C10's fcsel0 s24 witness (T120: correct). T120b reads C10's binding row
  (ulink_n_falseResult_3 stage[0]) as the kernel's INPUT n held against the host: `--datachange broad` releases n at
  the ack's fall, which the bench's clocked PS host (ps7_bench.v) does not. If that is right, a host model that holds
  operands until the next clocked write would move C10's margins; research would like those numbers with the
  host-side release bounded by one PS clock (12 ns) as well as with broad.
- **Next collatz build (exploratory, farm fcsel3a running):** item 28 with uselect0 16 -> 7 and uaddi0 12 -> 9
  (`BD_SIZES=../research/data/collatz_sizes_T3cdb_nl6s3a_bench.vh`, NEXTPNR_SEED=20, sdf 7aefc4bd, P 21.27 ns).
  The uselect0 shortening comes from a corner_audit fix (A' was refused because the cell's own request-join C nodes
  were counted as data). A margin at uselect0's line (its data vs its request) on this route is wanted.

## NEW board candidate: collatz item 28 (2026-11-15 evening)
Item 25's command with `BD_SIZES=../research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh` (select links at 3, the
unnamed ULINK_N10__4_UACK at 0), `NEXTPNR_SEED=20`, SDF md5 d86bdde5, P 25.81 ns. Every research check clean on 28
routes. A margin for its select links (arrival at umux0/1/2 and hold) is the number wanted most.

## Shortened select links, collatz (2026-11-15 evening) -- the margin wanted most
Item 25's command with `BD_SIZES=../research/data/collatz_sizes_T3cdb_nl6s{0,1,2}_bench.vh` (select links
ulink_n14__0 / ulink_n14__1 / ulink_n_index_11 DELAY at 0 / 1 / 2; nl6 otherwise). All gates pass on every route
(23 / 31 / 29), ~-10 ns per iteration (36.6 -> ~26). Rule E at the muxes is below 0 on many routes at 1 (to -393 ps),
on 2 of 29 at 2. Examples: fcsel2 seed 1 (sdf 5b538ca5, P 26.75 ns, E clean), fcsel2 seed 2 (fb1efc41, E -114 at umux0
worst), fcsel1 seed 24 (afab5445). fcsel0 seed 24 (sdf bb5fbbdb) is the base of two constructed races (research's
SDF injections, JOURNAL 2026-11-15): select -> umux1 join +3000 ps (gate passes at worst, FAST_MIN looks hung), and
ulink_n14__1 stage[1] enable +15000 ps. A margin (the kappa at which each select race fails) on fcsel1 / fcsel2
routes would decide whether rule E's rows here are real.

## Pending: the first shortened-select candidates (2026-11-15, farm running)
- xorshift item 27's structure with the four select links (ulink_n12__0/1/2, ulink_n_index_15 DELAY) at 1 (fxsel1)
  and at 0 (fxsel0), seeds 1-32; collatz item 25 / collatz64 item 26 / ipow h4 structures with the select links at 0
  (fcsel0 / fc64sel0 / fisel0). Seeds and md5s will be listed here when the farm returns; the sizes files are
  `research/data/*_fr4s1_bench.vh`, `*_fr4s0_bench.vh`, `*_nl6s0_bench.vh`, `*_h4s0_bench.vh`. The select rule was
  withdrawn today; these are the builds where a margin from you matters most.

## Board candidates (current)
1. **xorshift item 27** (BOARD-QUEUE list item 27, section ## 28): MLIR `research/data/fifteen/xorshift_predec.mlir`,
   XOR + `BDC_FORK_OUT_LINK=n11__0`, `BD_SIZES=../research/data/xorshift_sizes_T3s50_fr4_bench.vh`, `NEXTPNR_SEED=2`.
   SDF md5 a9bdac53. Changed vs item 23: the loop test reads i against n-1 (pre_dec.py), the fork-out link n30__0 gone.
   Files: not committed yet (rebuild from the command).
2. **collatz item 25** (list item 25, section ## 26): MLIR `research/data/fifteen/collatz_preeq2.mlir`, COL,
   `BD_SIZES=../research/data/collatz_sizes_T3cdb_nl4_bench.vh`, `NEXTPNR_SEED=24`. SDF md5 e001dc27.
   Files: `research/data/for-formal/item25_collatz_s24/`. Changed vs item 22: exit test n == 2 (pre_eq2.py).
   Note: its critical cycle is umux1's select ring; 27.4 of 35.9 ns is the 36-element select line ulink_n14__1
   (research/data/itercost/README.md, last section).
3. **collatz64 item 26** (list item 26, section ## 27): MLIR `research/data/fifteen/collatz64_preeq2.mlir`, COL,
   `BD_SIZES=../research/data/collatz64_sizes_T4cdb_h2_bench.vh`, `NEXTPNR_SEED=25`. SDF md5 6982a9d5.
4. **xorshift item 23** (list item 23, section ## 24): XOR + `BDC_FORK_OUT_LINK=n11__0,n30__0`,
   `BD_SIZES=../research/data/xorshift_sizes_T3s50_fr3_bench.vh`, `NEXTPNR_SEED=10`. SDF md5 2f825834.
   Files: `research/data/for-formal/item23_xorshift_s10/`. Research's static rule H has rows below 0 on it (ulink_n7
   -274 ps at the worst corner); the audit found them never live in simulation; research's time-separation check
   (research/tools/eventgraph/tsehold.py) clears ulink_n7 (+235) and leaves ulink_n8 (-26 worst, -196 FAST_MIN).

## Known bad, each with a good neighbour (your negative controls)
1. **BAD xf2_1** (xorshift, FAST_MIN gate 6/17: rounds 4 after 3 returns the 3-round value): XOR +
   `BDC_FORK_OUT_LINK=n11__0`, `BD_SIZES=../research/data/xorshift_sizes_T3s50_fr2_bench.vh`, `NEXTPNR_SEED=1`.
   SDF md5 dc138ea2. Files: `research/data/for-formal/BAD_xf2_1/`. The race (re-traced 2026-11-15, JOURNAL): ulink_n7's
   node falls at 4245062 ps (FAST_MIN, vectors research/data/fifteen/vec_xorshift_hold.hex); its acknowledge lets the
   counter's loop-back pipe (ulink_n_trueResult_6) reopen; the next i reaches n7's D at 4246343 and latch bit 1 changes
   at 4246605, 1.54 ns after the node fell, because n7's enable net reaches that bit late. A hold race at ulink_n7.
   Good neighbour: xf3_1 (same + `BDC_FORK_OUT_LINK=n11__0,n30__0`, sizes fr2 + the new link's defaults, seed 1;
   gates pass) -- a different route, so not a minimal pair.
2. **BAD nc64_7** (collatz64, FAST_MIN gate fails; the 2026-11-11 select failure): bench top, COL less the last three
   knobs as of 2026-11-11 (`BDC_CONST_DATA=1` only), `BD_SIZES=../research/data/collatz64_sizes_T4cd_bench.vh`
   (ulink_n14__1 shortened 19 -> 10, SDELAY 2 -> 1), `NEXTPNR_SEED=7`. SDF md5 98809562. Good neighbour pc64_7: the same
   with `BD_SIZES=../research/data/fifteen/selectrule/collatz64_sizes_T4cd_sel19_bench.vh` (19 / 2 restored), SDF md5
   acc06847, gates pass. A minimal pair (one line differs). The race: ulink_n13 / falseResult_5 hold windows
   (JOURNAL 2026-11-15 05:39 / 06:42).
