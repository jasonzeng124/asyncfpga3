# Board data: what each file here is for (research/BOARD-QUEUE.md has the items and their commands)

- `*_v3_s*_sizes.vh` -- items 38-41 (flow v3's automatic routes): the loop's sizes, built with cells/hw/build_bench.sh as
  each item's command says. `rejudge_2026-11-19_gate_strict.{sh,txt}`: their re-judgement under the strict gate.
- `{collatz,xorshift,collatz64}_v10_s1.spec` (+ `_sizes.vh`, `_trims.txt`) -- items 42 / 43 (and collatz64, kept OFF the
  board: research/JOURNAL.md 2026-11-21 04:17). A **spec** is what research/tools/suite/board_rebuild.sh rebuilds: the
  flow's own build (research/tools/fifteen/lane2.sh with the proved MLIR, the loop's sizes / seed / search knobs), the
  recorded trims by LUT INIT, the bitstream; it exits 1 unless the route's SDF and the trimmed FASM are the ones named.
- `suite_v10/` -- item 44: one spec per kernel flow v10 passed on a clean route (research/tools/suite/mk_board_specs.py
  from the farm's saves; every route rebuilt here byte for byte). research/tools/suite/board_suite.sh runs them all on
  the board with the gate's own vectors and rules (cells/hw/xsdb_bench_vec.tcl, research/tools/suite/board_vec_judge.py).
- `guard_g10/` -- item 45: the same kernels and seeds as three of item 44's thinnest routes, built with rule E's guard at
  10 % (research/tools/auto/auto_size.sh AUTO_GUARD_E=0.90,1.10).
- `screen_v10/` -- formal's B24 steer screen and rule E's path-error tolerance for every route of item 44 (census.md).

Rebuilding needs $TC with cells/verify/toolchain.sh passing (nextpnr 6e5d224472232d5d) and build/frontend/ as the earlier
items use it. A .bit's md5 varies between builds of the same FASM (its header carries a path), so the checks are on the
SDF and the FASM, never the bit.
