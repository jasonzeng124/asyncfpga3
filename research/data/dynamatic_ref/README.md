# Dynamatic's own number for ipow and gcd (PROGRAM.md "Use the quota", item 6)

**Both Dynamatic numbers below are ESTIMATES, not routes.** Dynamatic is not built in this container, so the
method behind the existing three numbers cannot be rerun. This file gives the method, what is missing, and an
estimate with its basis.

## How xorshift 12.73 / collatz 14.05 / collatz64 17.84 were obtained

- Script: `cells/hw/dyn_baseline.sh` (with `cells/hw/dyn_wrap.py`), in the repo since its first import
  (1b81a36f2, 2026-08-24). Steps: take Dynamatic's buffered `hw.mlir` (`build/dynbaseline/<k>/comp/hw.mlir`),
  export Verilog with Dynamatic's own `export-rtl` and `rtl-config-verilog.json` (line 50), wrap it in an
  I/O-bound top (inputs from registers, outputs XOR-reduced), then yosys `synth_xilinx` and nextpnr-xilinx on
  xc7z010clg400-1 with `--freq 250 --timing-allow-fail` (lines 83-84). Result: the nextpnr Fmax for `clk`,
  reported as period = ns/iteration "(1 cycle)" (line 95).
- Why 1 cycle: the buffering it describes (lines 17-20: one ONE_SLOT_BREAK_DV, DV latency 1, and one
  ONE_SLOT_BREAK_R per ring) is Dynamatic's `on-merges` placement (`HandshakePlaceBuffers.cpp`,
  `placeWithoutUsingMILP`: one opaque and one transparent slot on the output of every merge-like op). On a
  single-block loop with no multi-cycle unit, one iteration is one cycle.
- The numbers first appear in `README.md:148-150` (eaa900252, 2026-08-26). No journal entry, log or `hw.mlir`
  was kept (`build/` is gitignored). The JOURNAL first cites them at line 3130 (itercost, "progress 09:10").
- Caveats on the three numbers: each is ONE route at nextpnr's default seed (the script passes no `--seed`),
  which is against today's 4-seed rule. The nextpnr build is not recorded.

## What is missing for ipow and gcd

`dynamatic/` (and `circt/`) are absent here. The method needs `dynamatic-opt` (buffer placement and lowering to
`hw.mlir`) and `export-rtl` plus its `rtl-*-generator` binaries. The fixtures in `cloud/fixtures/frontend/`
stop at `handshake_transformed.mlir`, before buffer placement. Building Dynamatic means building LLVM, which was
not attempted (JOURNAL ~4056).

## Estimate: cycles per iteration from the graph x a period from the measured analogues

Cycles come from Dynamatic's own sources (upstream c88cf03, read only) applied to the fixtures' handshake MLIR:

- **ipow, 5 cycles per iteration.** `cf.mlir` is a single-block loop (bb1). It has two variable x variable
  `muli`. Dynamatic's Verilog `muli` (`data/verilog/arith/muli.v`, `mul_4_stage`) has latency 4
  (`components.json`: 4.0). The ring b -> mux -> [DV slot, 1 cycle] -> muli(b,b) [4] -> cond_br -> mux carries
  one token, so II = 5 under `on-merges` (r = r*b closes the same way). Even an MILP placement cannot go below 4,
  because the multiplier's latency is fixed.
- **gcd, 3 cycles per main (subtract) iteration + 1 cycle per inner shift.** The handshake MLIR has merge-like
  ops in every block, including single-predecessor ones (mux x3 bb10, mux x4 bb11, merge x4 bb9). `on-merges`
  buffers all of them. One trip round the subtract loop bb10 -> bb11 -> bb9 -> bb10 is therefore 3 slots. Each
  extra ctz shift (bb11 -> bb11) is 1 slot.
- **Period P:** taken from the measured analogues, not routed. The 32-bit kernels give 12.73 (xorshift) and
  14.05 (collatz); collatz64 gives 17.84. For ipow I use 12.73-14.05: its rings hold a compare, a shift, a select
  and a mux, and the multiply sits between registers. For gcd I use 12.73-17.84 (central 14.05): the bb10 cycle
  has a subtract, a compare, a negate and a select in series, and the graph is 4x larger.
- **Probe:** Dynamatic's `mul_4_stage`, run by itself through our flow (3 DSP48E1, `mul4_probe_top.v`, 4 seeds,
  `mul4_probe_routes.tsv`), closes at 396-461 MHz. Its critical path is a 2.2-2.5 ns fabric path. No DSP path
  ever shows as critical, so this nextpnr gives no usable timing for the multiply. The multiply stage is taken
  as not limiting at P ~ 13 ns, but `dyn_baseline.sh` could not have shown it if it were.

## Table

| kernel | Dynamatic ns/iteration | how obtained | our best async | async / Dynamatic |
|---|---|---|---|---|
| xorshift | 12.73 | route, 1 seed (dyn_baseline.sh) | 18.9 (BQ item 33) | 1.48 |
| collatz | 14.05 | route, 1 seed | 21.5 (BQ item 31) | 1.53 |
| collatz64 | 17.84 | route, 1 seed | 31.4 (BQ item 32) | 1.76 |
| ipow | **~67 (63.7-70.3)** | ESTIMATE: 5 cycles x P 12.73-14.05 | 36.2 sim (item 29); ~30.2 x0.70 candidate; board Aug 60.46 | **~0.54 (0.52-0.57); 0.45 for x0.70; 0.90 Aug board** |
| gcd, per main (subtract) iteration | **~42 (38.2-53.5)** | ESTIMATE: 3 cycles x P 12.73-17.84 | board Aug 156.5; sim gcd_ps P1 121.0 (band 0.38 + 1x scatter) | **~3.7 (2.9-4.1) board; ~2.9 (2.3-3.2) sim** |
| gcd, per inner ctz shift | **~14 (12.7-17.8)** | ESTIMATE: 1 cycle x P | board Aug 114.6; sim P1 77.0 | ~8.2 board; ~5.5 sim |

How the two gcd terms are defined: these are the per-iteration terms of the gcd cost model (`cells/hw/gcd_cost_fit.py`).
They are fitted over the replayed loop counters: k loop, pre-loop ctz, **main** and **inner ctz**. A "main iteration"
is one pass of the subtract loop: |a-b|, the first exit test of the ctz loop, then min and the `b == 0` test.
That is cf blocks bb10 -> bb11 -> bb9. Each further right shift of the ctz loop is counted separately as an
"inner ctz shift". gcd's latency per call depends on the operands (310 ns to 6.34 us on the board), so no single
per-call number compares. Async sources: `research/data/aug_gcd/README.md` and
`research/data/gcd_ps/cost_model_vs_board.tsv`. Note: SIM-VS-BOARD.md says the 0.288 band reads 8-10% slow
against the board.

## Caveats

- Both Dynamatic figures are estimates. The cycle counts depend on `on-merges` placement, which is inferred
  from `dyn_baseline.sh`'s comment and not recorded. With an MILP placement (fpga20 at a target period), ipow
  would be at least 4 x P (~51-56 ns), and gcd's cycles and period would both change.
- P is borrowed from other kernels' single-seed routes, so it carries their seed scatter (several hundred ps).
- Dynamatic's latency-4 multiplier was designed for Vivado DSP retiming at ~4 ns periods. Inside a slow
  handshake-limited clock it costs 4 cycles per recurrence. That latency, not the fabric, is why async ipow looks
  faster here.
- Turning these into measured numbers takes a Dynamatic build (an owner machine or a session that has one).
  Run `bdc/frontend.sh`, then `compile.sh` with `on-merges`, then `cells/hw/dyn_baseline.sh ipow|gcd`, on 4+
  seeds. The ns/iteration is then periods x 5 (ipow) and 3 (+1 per shift) (gcd), not periods x 1 as the script
  prints. Check the cycle count against Dynamatic's own simulation, because the script's "(1 cycle)" line would be
  wrong for both kernels.
