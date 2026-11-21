# The August gcd_bench_gen on the full stack: where the kernel sits between the corners (PROGRAM.md item 2)

Build: `research/board/aug/builds/gcd_bench_gen` (owner, 1dd0a675): bit md5 f199866ea256 (2026-08-24 11:45, nextpnr
d216cb36a370f78a), the build whose `_gcdcost_*.log` runs are `logs/gcd_cost.tsv` (FIXED batches of 200, 100 MHz,
latmin/latmax in aclk cycles). It is also the async-latch-hang build (no synchroniser).

Full stack: netlist decoded from that .bit (fasm2net --ps7; EQUIVALENT to its routed JSON), prjxray SDF of its route
(xray_delay.py), GLS_MODEL=fid, host cells/gls/ps/ps7_bench.v with +VECFILE=gcdcost_vec.hex (the board's 24 (a, b)
pairs, one FIXED batch of 2 runs each). Analysis: research/tools/aug_cost_fit.py.

## Result (fit_min_max.txt)
x = (board latmin - FAST_MIN) / (SLOW_MAX - FAST_MIN), per vector with board latency >= 100 cycles:
**median 0.211, range 0.209-0.216** (12 vectors; the rest are left out at SLOW_MAX, below).

| cost term (ns) | FAST_MIN | board | SLOW_MAX | x |
|---|---|---|---|---|
| per k-loop iteration | 90.1 | 125.8 | 260.8 | 0.209 |
| per pre-loop ctz shift | 78.1 | 108.7 | 225.0 | 0.208 |
| per main-loop iteration | 112.8 | 156.5 | 335.7 | 0.196 |
| per inner ctz shift | 83.1 | 114.6 | 233.1 | 0.210 |

(The board column is the fit to the board table itself; it reproduces the recorded 127.1/108.3/156.5/114.6.)

Reading: on the like-for-like build the kernel sits at x = 0.21, FASTER than the ring band (0.288), not slower
(the 0.54-0.72 of the cost-model check came from a different build). The default band 0.288 for every cell type
over-predicts this kernel's latency by ~10% (e.g. gcd(48,18): 89 + 0.288*157 = 134 cycles vs 122).
LUT + wire structures on this die span x = 0.21 (this kernel: mostly RLOC'd delay columns and short in-CLB arcs)
to 0.29 (ring loops: one LUT and a routed hop per stage): one band does not fit both to better than ~8%.

## The August harness races in the sim at SLOW_MAX (not at FAST_MIN)
At SLOW_MAX, 10 of the 24 batches hit the harness's async-latch race (the bench's mismatch sticky, or the two runs
captured 700+ cycles apart); FAST_MIN had none. The board ran all 24 vectors 600 times with no mismatch (its
operating point, x = 0.21, moves i_ack's phase). These batches are reported, not fitted.

## Band 0.288 on the same build (fit_min_max_band.txt)
All 24 batches complete, none hits the harness race. Every vector is predicted 9-10% slow (48,18: 134 vs 122
cycles; 2^31-1,2^31-2: 1319 vs 1199), and the cost terms likewise (main 172.0 vs 156.5 ns, k 137.3 vs 125.8):
the kernel sits at x = 0.21 uniformly, whatever the vector, so the model's error on this kernel is one scale.

## Band 0.288 with CARRY4 / F7F8 / FF at SLOW_MAX (fit_all.txt)
2200 CARRY4, 4362 SELMUX2_1 and 1952 SLICE_FFX IOPATH arcs moved to SLOW_MAX: every vector's latency is
IDENTICAL to band 0.288's, cycle for cycle (even the simulation end time, 244286032 ps, is the same). The
uncalibrated cell types are not on this kernel's critical cycle at all.

So what the board's latency measures is the matched delays and handshake LUTs, as bundled data should: the
datapath (carries, F7/F8) has slack under its matched delay. Hence x = 0.21 is the silicon position of the
RLOC'd LUT delay chains, and ring128's 0.288 that of LUT + routed hops. The measured mix is the dangerous one:
matched delays FASTER, relative to the model, than the routed datapath they bound. That is the gate corner to run:
delay chains at 0.21, everything else at 0.288 (plus the uncalibrated cells at SLOW_MAX, plus M).
