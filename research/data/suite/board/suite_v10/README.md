# Flow v10's suite, one route per kernel, for the board (2026-11-21)

One board_rebuild.sh spec per kernel that flow v10 (farm suite13t_s5a_v10_*, incl. its resume parts) judged PASS on a
rule-CLEAN route with bits EQUIVALENT and ffmux-clean: the route of its lowest such seed. Written by
`research/tools/suite/mk_board_specs.py research/data/suite/board/suite_v10 <the v10 result dirs>` (sizes and trims
are the farm's own files for the shipped iteration; the search structure and the proved MLIR as auto_size.sh's
AUTO_TRIM_ONLY path rebuilds a shipped route), then every spec rebuilt here: a spec's SDF is the farm's route (checked by
the rebuild) and its FASM the trimmed fasm of that rebuild (FASM=00000000: not rebuilt yet, or the rebuild did not
reproduce the farm's sdf -- research/JOURNAL.md says which).

Run all of them on the board, one self-judging loop (BOARD-QUEUE item 44): `research/tools/suite/board_suite.sh
research/data/suite/board/suite_v10` -- per kernel: rebuild (exit 1 on any mismatch), the expected results from the C
as suite_one.sh derives them for the GLS gate, the vectors on the board (cells/hw/xsdb_bench_vec.tcl), the gate's
rules (research/tools/suite/board_vec_judge.py). Tested here without a board: BQ_MOCK=1 BQ_SKIP_REBUILD=1 (5 kernels
PASS against the mock bench; a corrupted result, an array-writing kernel against unchanged arrays, and a missing spec
all fail).
