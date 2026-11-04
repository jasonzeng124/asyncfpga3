# PROGRAM.md item 2 for the other kernels: each August bench build on the full stack, board latency between the corners

For each build in research/board/aug/builds/: netlist decoded from its .bit (fasm2net --ps7), prjxray SDF of its route,
GLS_MODEL=fid, ps7_bench.v +VECFILE of the board's own FIXED vectors (research/tools/aug_board_vectors.py, from the
logs paired match=yes), 2 runs each, FAST_MIN and SLOW_MAX. research/tools/aug_x.py: x per vector, every result
checked against the board's. Files per build: <build>_board.tsv, _min.log, _max.log, _x.txt, _equiv.txt.

| build | bit | bits vs JSON | vectors | results = board | x (vectors >= 50 cycles) |
|---|---|---|---|---|---|
| gcd_bench_gen (../aug_gcd/) | f199866ea256 | EQUIVALENT | 24 | 24/24 (FAST_MIN; 14 clean at SLOW_MAX, the rest hit the harness race) | 0.211 (0.209-0.216) |
| ipow_bench_gen | 6dbf3faec62f | NOT EQUIVALENT: one live LUT written as constant 0 by the August FASM writer (JOURNAL) | 17 | 17/17 at both corners | 0.225 (0.219-0.229) |
