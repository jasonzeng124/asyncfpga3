# PROGRAM.md item 2 for the other kernels: each August bench build on the full stack, board latency between the corners

For each build in research/board/aug/builds/: netlist decoded from its .bit (fasm2net --ps7), prjxray SDF of its route,
GLS_MODEL=fid, ps7_bench.v +VECFILE of the board's own FIXED vectors (research/tools/aug_board_vectors.py, from the
logs paired match=yes), 2 runs each, FAST_MIN and SLOW_MAX. research/tools/aug_x.py: x per vector, every result
checked against the board's. Files per build: <build>_board.tsv, _min.log, _max.log, _x.txt, _equiv.txt.

| build | bit | bits vs JSON | vectors | results = board | x (vectors >= 50 cycles) |
|---|---|---|---|---|---|
| gcd_bench_gen (../aug_gcd/) | f199866ea256 | EQUIVALENT | 24 | 24/24 (FAST_MIN; 14 clean at SLOW_MAX, the rest hit the harness race) | 0.211 (0.209-0.216) |
| ipow_bench_gen | 6dbf3faec62f | NOT EQUIVALENT: one live LUT written as constant 0 by the August FASM writer (JOURNAL) | 17 | 17/17 at both corners | 0.225 (0.219-0.229) |
| isprime_bench_gen | dcf8404d572d | NOT EQUIVALENT: 3 F7-mux inputs whose JSON drivers are nextpnr GND buffers (output 0) and whose bits drivers are INIT-0 LUTs (output 0): benign by inspection | 16 run (of 25; trimmed to board latency <= 3000 cycles, and a container restart cut each corner at 16) | 16/16 FAST_MIN, 15/15 SLOW_MAX | 0.222 (0.220-0.226) |
| collatz_bench_gen | 6f62bf4a50fa | NOT EQUIVALENT: 1 F7-mux input whose JSON driver is a nextpnr GND buffer (\$PACKER_GND_NET\$LUT\$116) and whose bits read 0: benign by inspection | 29 | 29/29 at both corners | 0.222 (0.215-0.227) |
