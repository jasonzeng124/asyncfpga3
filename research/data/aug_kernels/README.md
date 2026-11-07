# PROGRAM.md item 2 for the other kernels: each August bench build on the full stack, board latency between the corners

For each build in research/board/aug/builds/: netlist decoded from its .bit (fasm2net --ps7), prjxray SDF of its route,
GLS_MODEL=fid, ps7_bench.v +VECFILE of the board's own FIXED vectors (research/tools/aug_board_vectors.py, from the
logs paired match=yes), 2 runs each, FAST_MIN and SLOW_MAX. research/tools/aug_x.py: x per vector, every result
checked against the board's. Files per build: <build>_board.tsv, _min.log, _max.log, _x.txt, _equiv.txt.

| build | bit | bits vs JSON | vectors | results = board | x (vectors >= 50 cycles) |
|---|---|---|---|---|---|
| gcd_bench_gen (../aug_gcd/) | f199866ea256 | EQUIVALENT | 24 | 24/24 (FAST_MIN; 14 clean at SLOW_MAX, the rest hit the harness race) | 0.211 (0.209-0.216) |
| ipow_bench_gen | 6dbf3faec62f | was NOT EQUIVALENT; corrected 2026-11-05: the LUT is constant 0 by its own netlist (LUT2 I1&~I0 with I0 and I1 packed on one GND pin), fasm_equiv now folds it -- not a FASM-writer defect | 17 | 17/17 at both corners | 0.225 (0.219-0.229) |
| isprime_bench_gen | dcf8404d572d | NOT EQUIVALENT: 3 F7-mux inputs whose JSON drivers are nextpnr GND buffers (output 0) and whose bits drivers are INIT-0 LUTs (output 0): benign by inspection | 16 run (of 25; trimmed to board latency <= 3000 cycles, and a container restart cut each corner at 16) | 16/16 FAST_MIN, 15/15 SLOW_MAX | 0.222 (0.220-0.226) |
| collatz_bench_gen | 6f62bf4a50fa | NOT EQUIVALENT: 1 F7-mux input whose JSON driver is a nextpnr GND buffer (\$PACKER_GND_NET\$LUT\$116) and whose bits read 0: benign by inspection | 29 | 29/29 at both corners | 0.222 (0.215-0.227) |
| collatz64_bench_gen | 5fbb1377a78f | EQUIVALENT | 27 FAST_MIN, 16 SLOW_MAX (a restart cut it) | 27/27, 15/15 | 0.224 (0.218-0.227) |

## Conclusion (item 2)
Five kernels, each on the bitstream the board measured, sit at x = 0.211-0.225 between the full stack's FAST_MIN
and SLOW_MAX (per-vector spread within a kernel ~0.01), every compared result equal to the board's. ring128's loops
sit at 0.288. The datapath does not sit slower than the rings, so the owner's default stands: the uncalibrated cells
at the same band as LUT + wire (0.288), gated also with them at SLOW_MAX. Since slowing CARRY4/F7F8/FF changes no
kernel latency (aug_gcd), the kernels' x is their matched-delay chains' and handshake LUTs': matched delays on this
die run ~10% faster than the model at 0.288 says. The gate therefore also runs that mix (chains 0.21, the rest
0.288, cells SLOW_MAX, + M): BQ#2 8/8 PASS (research/data/fid/bq2_worstcase.tsv).
Speed consequence: band 0.288 over-predicts every kernel's latency by ~9-10%.
Not run: the null builds (harness overhead; the corners' common term cancels in x anyway).
