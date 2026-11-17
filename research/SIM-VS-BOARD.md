# Where the simulation is not the board

Kept by research (PROGRAM.md "The board decides", owner 2026-11-16). One row per known difference between the
simulation that judges a build (cells/gls, GLS_MODEL=fid, run by research/tools/eventgraph/bench_gate.sh) and the board:
what the board showed in August, if anything, and what the simulation does about it. Newest changes at the top of each
row's text. "August" = the owner's board runs, research/board/aug/ (builds, logs) and research/board/ro_many_aug/.

| # | difference | August board evidence | what the simulation does |
|---|---|---|---|
| 1 | **Delay of each arc.** prjxray gives a [FAST_MIN, SLOW_MAX] band per arc, not this die's value. | 128 rings (LUT + wire only): band x = 0.2877 median, p05-p95 0.276-0.303, residual 0.76% per ring (research/data/fid/ring128/fit.txt). Kernel builds (gcd, ipow, isprime, collatz, collatz64; research/data/aug_kernels): x = 0.211-0.225, every result equal to the board's. gcd simulated at 0.288 is 9-10% slower than the board on every vector (research/data/aug_gcd). The ring / kernel gap is not explained. | `worst` corner: delay chains 0.21, rest 0.288, CARRY4 / F7F8 / FF at SLOW_MAX, setting M scatter, one seed. `draw:K` (2026-11-16): chains and rest each uniform over [0.20, 0.31] independently, CARRY4 / F7F8 / FF uniform over [0.20, 1.0], setting M scatter with seed K; a candidate is reported as the fraction of draws that return right answers. |
| 2 | **Cell types the rings never exercised**: CARRY4, MUXF7/F8, slice FF, DSP48. **The gap with the largest effect on the candidates (2026-11-17).** | Kernel x values include them only as part of whole-iteration time, and no August latency moves with their band: CARRY4 / F7F8 / FF from 0.2 to 1.0 changes ns per iteration by 0.0 / 0.0 / +0.2% (collatz / collatz64 / ipow; audit T145; formal A13): in bundled data the matched LUT chains set the cycle and the carry chains only settle inside them. So the board's latencies cannot place this band; only a carry-specific measurement can (a CARRY4 / F7 ring experiment is being designed for BOARD-QUEUE). Effect: collatz x0.55 route 30 fails exactly the draws with this band at 0.75 / 0.91 (farm shrink9); item 35's loop-entry race falls to ~0 ps near 0.9 (formal C38, audit T144). | Their band is drawn over [0.20, 1.0] per draw (`draw:K`), SLOW_MAX at `worst`. DSP48: research's own model (cells/gls/dsp_model.py); formal's decoder refuses DSP sites. |
| 3 | **Within-die variation.** | Residual 0.76% per ring after one global x, i.e. variation + model error together. | Setting M: region factor sigma 0.02 per 10x10 slices, per-pip factor sigma 0.126 averaged along each wire (gives ~1.34% per ring, conservative). No length-dependent offset: the ring fit by length (0.283 / 0.287 / 0.288 / 0.291 for 7 / 15 / 31 / 63 links) shows none worth modelling. |
| 4 | **Narrow pulses (glitches) into LUTs and C-elements.** No published 7-series LUT pulse rejection. | None. BOARD-QUEUE item 2 (H_RUNT, research/board/runt/) measures it. | LUT inputs are transport delays (every pulse passes); a LUT with feedback (latch, C-element) has a resolver: a pulse shorter than its loop delay minus WIN/2 is rejected, longer ones resolve by a noise law (TAU = WIN = 150 ps, unsourced). research/data/fid/runtc.md: 1-40 ps pulses never set a C-element; with the resolver off they oscillate (formal's model). |
| 5 | **Metastability (arbiters, synchronisers).** | None on kernels. | Resolver on state nodes (above); FF window from SDF TSU / THD with random resolution. Arbiters are emitted unconditionally (CLAUDE.md). |
| 6 | **Start-up.** Silicon has no X; an unreset latch powers up 0 or 1. | None. | Every LUT state node starts X; bd_link's data latch has no reset, so a race against its first value can leave X that spreads. The owner chose to keep this (2026-11-16): +META_INIT=0/1 stays opt-in, used only to tell a real failure from start-up X when a run hangs. |
| 7 | **The bits.** The board runs what is in the bitstream, not nextpnr's netlist. | Three August failures were bitstream bugs (lut-pinmap, DSP const pins, DSP AREG); reproduced by the full stack (research/data/fid/acceptance_status.md). | The netlist is decoded from the .bit (fasm2net), checked against the routed JSON (fasm_equiv); ffmux_scan; toolchain.sh fingerprint. |
| 8 | **The host.** The board's PS writes operands over AXI and polls; the bench FSM runs each vector N times. | August logs: FIXED mode N = 200, the board script asserts the repeatability latch (mism_st bit 0) and a SIG oracle. | ps7_bench.v (AXI master model, FCLK 83.3 MHz), N = 2 runs per vector. **Until 2026-11-16 the gate read only the last run's result and ignored the repeatability latch**: a build whose result stream lagged one call passed. Now a batch whose runs disagree fails (JOURNAL 2026-11-16). |
| 9 | **Inputs.** The board takes any value of the C signature. | n/a | Gate vectors are a few dozen per kernel, oracle compiled from kernels/*.c (kernel_oracle.sh). collatz / collatz64 vectors had no n = 1 (zero-trip) until 2026-11-16 (col14 / c6415). Paths the vectors cannot reach (32-bit loop counters) are covered only by the static rules, which are now tools, not gates. |
| 10 | **Voltage and temperature.** | One board, room temperature, one supply; x from that. | Covered only by the band ranges in row 1. |
| 11 | **Memory inference.** iverilog cannot see yosys memory inference (CLAUDE.md). | isprime's late read (August). | Kernels here have no memories. |

## ns per iteration, August builds, simulated against the board (research/tools/aug_periter.py, 2026-11-16)
Same bitstreams the board measured (research/board/aug/builds, logs match=yes), full stack at FAST_MIN and SLOW_MAX,
slope of latency on iteration count; the 0.288 and 0.222 columns interpolate between the corners per vector.

| kernel | vectors | board | FAST_MIN | SLOW_MAX | band 0.288 (ring128) | band 0.222 (kernels' fit; in-sample) |
|---|---|---|---|---|---|---|
| collatz | 20 | 92.73 | 65.16 | 188.76 | 100.76 (+8.7%) | 92.60 (-0.1%) |
| collatz64 | 12 | 117.89 | 83.04 | 237.37 | 127.49 (+8.1%) | 117.30 (-0.5%) |
| ipow | 17 | 60.46 | 42.20 | 122.53 | 65.34 (+8.1%) | 60.04 (-0.7%) |
| gcd main loop (research/data/aug_gcd) | 24 | 156.5 | | | 172.0 (+9.9%) | |

The model at the ring band is 8-10% slow on every kernel, consistently; at one kernel-fitted band it is within 1%
(fitted on these same runs, so that number is not a prediction). PROGRAM quotes collatz 91.96 / collatz64 112.71: other
vector subsets of the same logs. xorshift (47.66): its August build was rebuilt after the board runs, so there is no
bitstream to simulate; not compared. Correctness: every simulated result equals the board's on all five builds.

Open: xorshift has no August bitstream to compare.
