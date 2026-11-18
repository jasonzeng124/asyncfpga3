# Dynamatic's figure for every suite kernel: simulated cycles, ESTIMATED period (dynref, 2026-11-17)

For the compiler suite's table (`research/PROGRAM.md`, "A benchmark suite for the compiler": "Dynamatic's figure where
one exists (say how it was obtained, and mark an estimate as one) and the ratio"). Tool:
`research/tools/suite/dynamatic_est.py` (method in its header; checks in `research/tools/suite/test_dynamatic_est.py`).

**What is measured and what is estimated.**

- **Cycles: simulated, not estimated, and not measured on silicon.** Dynamatic's own buffer placement (its
  `dynamatic-opt`, `on-merges`, the same placement the three routed numbers used) on each kernel's
  `handshake_transformed.mlir` fixture. The buffered circuit then runs in a cycle-level model of Dynamatic's Verilog
  units. Every answer is checked against the kernel's C, compiled with gcc and run on the same arguments. A kernel
  whose model gives a wrong answer gets no number. None did: 62 kernels simulated, 310 of 310 calls return the C's
  answer.
- **Period: an ESTIMATE.** It is the longest combinational path of the buffered circuit in Dynamatic's own timing
  model (`components.json`, the delays its buffer placement uses), times one factor (0.793). The factor is fitted on
  the three kernels whose Dynamatic netlist was routed in 2026-08. Fit error: 7.3 % rms; worst leave-one-out error
  15.8 % (collatz). So every "ns per iteration" below is an ESTIMATE. The three routed periods (xorshift 12.73,
  collatz 14.05, collatz64 17.84 ns) are still the only measured Dynamatic periods. In the suite table, keep them for
  those three kernels.
- **Nothing here was synthesised, placed or routed.** Dynamatic's `export-rtl` is not in the owner's build, so no
  Dynamatic netlist can be made on this machine.

## Method

1. **Buffers.** `dynamatic-opt <fixture> --handshake-set-buffering-properties=version=fpga20
   --handshake-place-buffers="algorithm=on-merges timing-models=$DYN/data/components.json"`, then
   `--handshake-canonicalize --handshake-hoist-ext-instances`. These are compile.sh's `on-merges` branch and its
   export step. `on-merges` puts one ONE_SLOT_BREAK_DV (oehb) and one ONE_SLOT_BREAK_R (tehb) on the output of every
   merge-like op. It needs no solver. It ran on all 135 fixtures: this repo's 12, suitek's 13 new ones, and
   suited's 110 (Dynamatic's integration tests). The MILP placements (fpga20, fpl22, costaware, mapbuf) need Gurobi
   or CBC, and this build has neither: `LLVM ERROR: CBC not installed!` / `Gurobi not installed!`.
   `--dump-milp-models` writes nothing before that check, so the MILP could not be handed to another solver either.
2. **Cycles.** One unit per op, each transcribed from `dynamatic/data/verilog`:
   - eager fork (`eager_fork_register_block`), lazy fork, join, merge (lowest valid index wins, no internal buffer),
     mux;
   - control_merge: merge, then a tehb holding the index, then a 2-way eager fork;
   - cond_br, and the antitoken `selector` (select);
   - oehb and tehb buffers;
   - `muli`: a 4-stage lock-step pipeline enabled by its output oehb; `divsi` / `divui` / `remsi`: 35 stages;
   - load: two tehbs; store: wires;
   - `mem_controller`: fixed-priority read and write arbiters, the BRAM's 1-cycle read, the pending-store counter
     and `mc_control`.

   Every cycle, the valid / ready / data nets settle to their fixed point (event-driven; the same cycle counts as
   evaluating every unit every cycle, checked on 12 kernels), then the registers clock. The environment offers every
   argument and start token from cycle 0 until it is taken, and is always ready for results. **Cycles per call** =
   the cycle in which the last `end` operand is taken, counted from 1 (one call from reset).
   **Cycles per iteration** = the least-squares slope of cycles per call on the loop header's executions over the
   calls (one loop). With several loops, one coefficient is fitted per loop and the table gives the most executed
   loop's. With a single call (main()), it is the mean interval between the header's back-edge entries. Loops are
   the natural loops of the block graph carried by `handshake.bb`.
3. **Answers.** The C runs in one of two ways. With a vector file, a gcc driver calls the kernel on the vector's
   words; `cells/hw/gen_bench.py`'s domain masks are applied as the bench applies them, so both sides compute the
   same calls. Without one, the C's own `main()` runs with `CALL_KERNEL` replaced by a wrapper that records the
   scalars and arrays it passes, then the return value and arrays after the call. That one call (Dynamatic's own
   test input) is then simulated. Return values and all arrays after the call must match. Parameters are matched by
   name: Dynamatic drops unused memrefs.
4. **Lower bound for any placement** (column "lower bound, any placement"). This is a static count, not a
   simulation. For each loop, take the largest latency of a ring from a merge-like unit of its header back to that
   unit's own back-edge input, counting Dynamatic's unit latencies (muli 4, div / rem 35, memory read 1) and at
   least 1 per ring. Each such ring carries one token per iteration. Only blocks that run on every iteration count
   (blocks that dominate the loop's latches). No buffer placement, MILP included, can do fewer cycles per iteration
   on this circuit. The checks confirm it never exceeds the simulated figure.
5. **Period.** The nodes are (channel, data | valid | ready). The arcs inside each unit come from components.json:
   data (by width), valid, ready, and the mixed arcs valid->ready (VR), condition->valid (CV), condition->ready (CR)
   and valid->data (VD). Registers cut arcs: oehb cuts data and valid, tehb cuts ready, muli / div / load and the
   memory controller's read data are registered. One addition: control_merge valid -> index data (the priority
   encoder, at its valid delay). The period estimate is 0.793 x the longest path.

## Checks that can fail (`research/tools/suite/test_dynamatic_est.py`, all pass)

- Answers: the six original kernels on suite_one.sh's gate vectors (xor19, col18, c6419, ipow17, isp17, gcd18):
  107 of 107 calls equal the C.
- Cycles against a derivation that does not use this simulator (`research/data/dynamatic_ref/README.md`):
  - **xorshift, collatz, collatz64: 1 cycle per iteration. VERIFIED, exactly.** On every vector, cycles per call =
    2 + iterations (dyn_baseline.sh's "(1 cycle)").
  - **ipow: 5 cycles per iteration. VERIFIED, exactly.** cycles = 2 + 5 x iterations (the README's hand count:
    muli latency 4 + the ring's one opaque slot).
  - **gcd: 3 cycles per main iteration and 1 per inner ctz shift. VERIFIED.** A fit on the C's own loop counters
    (gcd_cost_fit.py's four terms) over 42 calls (gcdcost_vec.hex + gcd18.hex) gives base 9.0 + 1.04 per k-loop
    iteration + 1.03 per pre-loop ctz shift + **3.03 per main iteration + 1.00 per inner ctz shift**, worst residual
    7 cycles. Directly: in gcd(0x7fffffff, 0x7ffffffe), bb10's control_merge fires every 4 cycles, and each of those
    main iterations has exactly one shift. The table's "most executed loop" figure for gcd is the inner shift
    (bb11, 0.99). The block-execution fit on gcd18 alone gives bb10 2.09, which is less reliable: 18 calls, 6
    terms, worst residual 3.7 cycles. Use 3.03 / 1.00.
- Negative controls. Each injects a defect into the model and must be reported:
  - (a) xori computes OR: xorshift WRONG on 16 of 19 calls.
  - (b) every tehb forgets the token it holds: caught on ipow only.
  - (c) every eager fork forgets which outputs it already served: caught on ipow only.
  - (e) every 2-input mux takes the other input: caught on 6 of 6 kernels.
  - (d) muli latency 3: the answers stay RIGHT, and ipow drops to 4 cycles per iteration.

  (b) and (c) show the limit of the answer check: it covers only the paths the vectors exercise. Among the six,
  only ipow's multiplier makes a fork's outputs take a token in different cycles or fills a tehb. (d) shows that
  the answers cannot see a cycle-count error at all. The cycle counts rest on the transcription, and on the five
  kernels above where an independent count exists.

## Period calibration (Dynamatic's timing model vs the three routed periods)

| kernel | longest path in Dynamatic's model, ns | routed period, ns (1 seed, 2026-08) | 0.793 x model | error | leave-one-out |
|---|---|---|---|---|---|
| xorshift | 15.03 | 12.73 | 11.92 | -6.4 % | -8.1 % |
| collatz | 19.52 | 14.05 | 15.48 | +10.2 % | +15.8 % |
| collatz64 | 21.58 | 17.84 | 17.11 | -4.1 % | -7.2 % |

rms error 7.3 %; worst leave-one-out 15.8 %. Every critical path found has the same shape. It starts at the loop
counter's or the data's oehb, goes through compare -> cond_br (condition -> valid) -> control_merge -> fork -> the
mux's index valid, then into the mux data input's ready and back through the ready chain of the loop body to its
tehb. That is a real combinational path of the RTL. Sensitivity, same fit: data and valid arcs only gives worst
leave-one-out 15.8 %; data arcs only, 56 %. The full model is both the faithful one and the best of the three.
With 3 points, nothing better can be told apart.

## Table

How to read it:
- Vectors: the six originals use suite_one.sh's gate vectors. suitek's kernels use `kernels/<k>/vec.hex` (in
  `/tmp/bot/sa/suitek/repo`, not yet committed). The rest use the C's own `main()` (one call; for Dynamatic's
  integration tests, the input Dynamatic itself tests with).
- Fixtures: this repo's `build/frontend` first, then suitek's, then suited's (`/tmp/bot/sa/suited/repo/build/frontend`,
  Dynamatic's integration tests).
- "ns per iteration" = cycles per iteration x the estimated period. It is an ESTIMATE wherever it appears.
- Multi-loop kernels: the cycles-per-iteration column also gives the median back-edge interval of the other loops.
  An outer loop's interval includes its inner loops.

| kernel | vectors | Dynamatic cycles per call (simulated; answers = C) | cycles per iteration (simulated, on-merges) | lower bound, any placement | period, ns (ESTIMATE) | ns per iteration (ESTIMATE) | measured period, ns (routed, 1 seed, 2026-08) |
|---|---|---|---|---|---|---|---|
| admm | main() | not simulated (float argument) | - | - | - | - | - |
| atax | main() | not simulated (LSQ) | - | - | - | - | - |
| atax_float | main() | not simulated (floating point (memref<400xf32>)) | - | - | - | - | - |
| bicg | main() | not simulated (LSQ) | - | - | - | - | - |
| bicg_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - |
| binary_search | main() | 240 (1 call) | 3.00 (bb1, the most executed of 2 loops; median back-edge interval of the others: bb4 3) | 1 | 8.06 | 24.2 | - |
| branchloop | kernels/branchloop/vec.hex | 2-213 (14 calls) | 3.44 (bb1, the most executed of 2 loops; median back-edge interval of the others: bb3 1) | 1 | 10.70 | 36.8 | - |
| brhash | kernels/brhash/vec.hex | 2-770 (10 calls) | 3.00 | 1 | 12.13 | 36.4 | - |
| cmpchain | kernels/cmpchain/vec.hex | 2-6 (17 calls) | - | - | 7.68 | - (no loop) | - |
| cnn | main() | not simulated (LSQ) | - | - | - | - | - |
| collatz | research/data/eventgraph/gate/col18.hex | 2-336 (17 calls) | 1.00 | 1 | 15.48 | 15.5 | 14.05 (cycles x period = 14.05) |
| collatz64 | research/data/eventgraph/gate/c6419.hex | 2-951 (18 calls) | 1.00 | 1 | 17.11 | 17.1 | 17.84 (cycles x period = 17.84) |
| cordic | main() | not simulated (float argument) | - | - | - | - | - |
| countloop | kernels/countloop/vec.hex | 2-258 (10 calls) | 1.00 | 1 | 8.36 | 8.4 | - |
| covariance | main() | not simulated (LSQ) | - | - | - | - | - |
| covariance_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - |
| digitdiv | main() | 362 (1 call) | 39.50 | 35 | 7.69 | 303.8 | - |
| divergent_paths | main() | not simulated (LSQ) | - | - | - | - | - |
| factorial | main() | 393 (1 call) | 12.59 (bb2, the most executed of 2 loops) | 4 | 9.98 | 125.7 | - |
| fir | main() | 6002 (1 call) | 5.99 | 1 | 8.12 | 48.7 | - |
| fixed | main() | not simulated (float argument) | - | - | - | - | - |
| float_basic | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - |
| fold64 | kernels/fold64/vec.hex | 2-257 (10 calls) | 1.00 | 1 | 11.93 | 11.9 | - |
| gaussian | main() | not simulated (LSQ) | - | - | - | - | - |
| gcd | research/data/eventgraph/gate/gcd18.hex | 2-163 (18 calls) | 0.99 (bb11, the most executed of 5 loops; median back-edge interval of the others: bb3 1, bb5 1, bb7 1, bb10 4) | 1 | 12.55 | 12.4 | - |
| gemm | main() | not simulated (floating point (sitofp)) | - | - | - | - | - |
| gemm_float | main() | not simulated (float argument) | - | - | - | - | - |
| gemver | main() | not simulated (LSQ) | - | - | - | - | - |
| gemver_float | main() | not simulated (float argument) | - | - | - | - | - |
| gesummv_float | main() | not simulated (float argument) | - | - | - | - | - |
| get_tanh | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| gsum | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| gsumif | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| histogram | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| horner | kernels/horner/vec.hex | 2-1282 (11 calls) | 5.00 | 4 | 8.36 | 41.8 | - |
| if_convert | main() | 1125 (1 call) | 6.00 | 4 | 10.95 | 65.7 | - |
| if_loop_1 | main() | 202 (1 call) | 1.99 | 1 | 9.99 | 19.9 | - |
| if_loop_2 | main() | 202 (1 call) | 1.99 | 1 | 8.36 | 16.6 | - |
| if_loop_3 | main() | 303 (1 call) | 3.00 | 1 | 9.18 | 27.5 | - |
| if_loop_add | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| if_loop_mul | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| iir | main() | 5996 (1 call) | 5.99 | 4 | 8.12 | 48.7 | - |
| image_resize | main() | 1833 (1 call) | 1.97 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 61) | 1 | 9.64 | 18.9 | - |
| insertion_sort | main() | not simulated (LSQ) | - | - | - | - | - |
| ipow | research/data/eventgraph/gate/ipow17.hex | 2-157 (17 calls) | 5.00 | 4 | 10.00 | 50.0 | - |
| isprime | research/data/alltable/isp17.hex | 2-2139 (18 calls) | 1.00 (bb4, the most executed of 3 loops; median back-edge interval of the others: bb3 22, bb6 1) | 1 | 9.26 | 9.3 | - |
| iterative_division | main() | 5 (1 call) | - | - | 10.22 | - (no loop) | - |
| iterative_sqrt | main() | 72 (1 call) | 10.00 | 8 | 11.11 | 111.1 | - |
| jacobi_1d_imper | main() | not simulated (LSQ) | - | - | - | - | - |
| kernel_2mm | main() | not simulated (LSQ) | - | - | - | - | - |
| kernel_2mm_float | main() | not simulated (float argument) | - | - | - | - | - |
| kernel_3mm | main() | not simulated (LSQ) | - | - | - | - | - |
| kernel_3mm_float | main() | not simulated (floating point (memref<100xf32>)) | - | - | - | - | - |
| kmp | main() | not simulated (LSQ) | - | - | - | - | - |
| lfsrfind | kernels/lfsrfind/vec.hex | 3-514 (10 calls) | 2.00 | 1 | 9.74 | 19.5 | - |
| loop_array | main() | not simulated (LSQ) | - | - | - | - | - |
| loop_path | main() | 337 (1 call) | 2.00 | 1 | 16.13 | 32.3 | - |
| lu | main() | not simulated (floating point (memref<9xf32>)) | - | - | - | - | - |
| matching | main() | not simulated (LSQ) | - | - | - | - | - |
| matching_2 | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| matrix | main() | 162005 (1 call) | 5.93 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 5400, bb2 180) | 1 | 9.64 | 57.2 | - |
| matrix_power | main() | not simulated (LSQ) | - | - | - | - | - |
| matvec | main() | 60004 (1 call) | 5.98 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 600) | 1 | 8.14 | 48.7 | - |
| memsum | main() | 122 (1 call) | 5.74 | 1 | 9.92 | 56.9 | - |
| mul_example | main() | 1002 (1 call) | 9.91 | 1 | 8.06 | 79.9 | - |
| mvt_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - |
| nest3 | kernels/nest3/vec.hex | 2-242 (12 calls) | 1.00 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 11, bb2 3) | 1 | 11.06 | 11.1 | - |
| nested | kernels/nested/vec.hex | 2-290 (11 calls) | 1.00 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 8) | 1 | 9.98 | 10.0 | - |
| nested_conditionals_1 | main() | not simulated (LSQ) | - | - | - | - | - |
| nested_conditionals_2 | main() | not simulated (LSQ) | - | - | - | - | - |
| nested_loop | main() | 2419 (1 call) | 6.00 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 1208) | 4 | 7.43 | 44.6 | - |
| path_profiling | main() | not simulated (LSQ) | - | - | - | - | - |
| pivot | main() | not simulated (LSQ) | - | - | - | - | - |
| polyn_mult | main() | not simulated (LSQ) | - | - | - | - | - |
| prediction | main() | not simulated (floating point (memref<100xf32>)) | - | - | - | - | - |
| quadrec | kernels/quadrec/vec.hex | 2-258 (10 calls) | 1.00 | 1 | 9.09 | 9.1 | - |
| share_test_1 | main() | 11997 (1 call) | 5.99 (bb1, the most executed of 2 loops; median back-edge interval of the others: bb2 6) | 1 | 9.74 | 58.4 | - |
| share_test_2 | main() | 902 (1 call) | 8.92 | 1 | 10.30 | 91.9 | - |
| simple_example_1 | main() | 2 (1 call) | - | - | 2.38 | - (no loop) | - |
| single_loop | main() | 3009 (1 call) | 6.00 | 4 | 6.72 | 40.3 | - |
| sobel | main() | 11329 (1 call) | 4.67 (bb7, the most executed of 4 loops; median back-edge interval of the others: bb1 755, bb2 57, bb6 17) | 1 | 9.29 | 43.4 | - |
| sparse | main() | not simulated (floating point (memref<100xf32>)) | - | - | - | - | - |
| spmv | main() | 150 (1 call) | 5.15 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 7) | 1 | 8.36 | 43.1 | - |
| sqrtsub | kernels/sqrtsub/vec.hex | 2-258 (13 calls) | 1.00 | 1 | 8.36 | 8.4 | - |
| stencil_2d | main() | 1518 (1 call) | 4.66 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 54, bb2 17) | 1 | 8.68 | 40.4 | - |
| straight | kernels/straight/vec.hex | 1 (12 calls) | - | - | 14.92 | - (no loop) | - |
| subdiag | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| subdiag_fast | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| sumi3_mem | main() | 10002 (1 call) | 9.99 | 1 | 8.85 | 88.4 | - |
| symm_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - |
| syr2k_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - |
| test_bitint | main() | 62 (1 call) | 5.44 | 1 | 8.14 | 44.3 | - |
| test_bool_array | main() | 3 (1 call) | - | - | 3.56 | - (no loop) | - |
| test_constant_array | main() | not simulated (internal array (handshake.ram)) | - | - | - | - | - |
| test_divui | main() | 36 (1 call) | - | - | - (no arc in the model) | - (no loop) | - |
| test_double | main() | not simulated (type <f64>) | - | - | - | - | - |
| test_flatten_array | main() | 1067 (1 call) | 1.93 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 266, bb2 33) | 1 | 8.14 | 15.7 | - |
| test_fneg | main() | not simulated (float argument) | - | - | - | - | - |
| test_int16 | main() | 1 (1 call) | - | - | - (no arc in the model) | - (no loop) | - |
| test_internal_array | main() | not simulated (internal array (handshake.ram)) | - | - | - | - | - |
| test_loop_free | main() | 3 (1 call) | - | - | 3.85 | - (no loop) | - |
| test_memory_1 | main() | 10 (1 call) | 1.67 | 1 | 8.36 | 13.9 | - |
| test_memory_10 | main() | 11 (1 call) | 2.00 | 1 | 8.36 | 16.7 | - |
| test_memory_11 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_12 | main() | 13 (1 call) | 2.33 | 1 | 7.71 | 18.0 | - |
| test_memory_13 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_14 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_15 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_16 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_17 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_18 | main() | 20 (1 call) | 3.50 | 1 | 7.79 | 27.3 | - |
| test_memory_2 | main() | 10 (1 call) | 1.67 | 1 | 8.36 | 13.9 | - |
| test_memory_3 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_4 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_5 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_6 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_7 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_8 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_9 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_smallbound | main() | not simulated (LSQ) | - | - | - | - | - |
| test_stdint | main() | 1002 (1 call) | 9.91 | 1 | 8.14 | 80.7 | - |
| test_unroll | main() | not simulated (internal array (handshake.ram)) | - | - | - | - | - |
| threshold | main() | not simulated (LSQ) | - | - | - | - | - |
| triangular | main() | not simulated (LSQ) | - | - | - | - | - |
| trisolv | main() | not simulated (LSQ) | - | - | - | - | - |
| twoloops | kernels/twoloops/vec.hex | 3-258 (11 calls) | 1.00 (bb3, the most executed of 2 loops; median back-edge interval of the others: bb1 1) | 1 | 9.09 | 9.1 | - |
| unused_arg | main() | 2 (1 call) | - | - | 0.97 | - (no loop) | - |
| varshift | kernels/varshift/vec.hex | 2-258 (10 calls) | 1.00 | 1 | 11.84 | 11.8 | - |
| vector_rescale | main() | 6002 (1 call) | 5.99 | 1 | 8.12 | 48.7 | - |
| video_filter | main() | 5403 (1 call) | 5.93 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 180) | 1 | 9.64 | 57.1 | - |
| while_loop_1 | main() | not simulated (LSQ) | - | - | - | - | - |
| while_loop_2 | main() | not simulated (LSQ) | - | - | - | - | - |
| while_loop_3 | main() | 13 (1 call) | 5.00 | 4 | 6.80 | 34.0 | - |
| wrap_if | main() | not simulated (LSQ) | - | - | - | - | - |
| xorshift | research/data/eventgraph/gate/xor19.hex | 2-1002 (19 calls) | 1.00 | 1 | 11.92 | 11.9 | 12.73 (cycles x period = 12.73) |

Not simulated, and why (rows above with a dash):
- **LSQ** (40 kernels): Dynamatic's load-store queue has no model here. 56 kernels have an LSQ: these 40, plus
  14 counted under floating point and 2 under handshake.ram.
- **Floating point** (30 kernels): float arguments, float memories or float ops.
- **`handshake.ram`** (3: test_constant_array, test_internal_array, test_unroll): an array declared inside the
  kernel. bdc/hs/parse.py does not read the generic op form, and it has no model.
- **No arc in the model** (test_divui, test_int16): every arc of the circuit is registered or has 0 delay in
  components.json, so the model gives no period. Their cycles are still simulated and right.

## For the suite table

- The three routed kernels keep their measured figures (12.73 / 14.05 / 17.84 ns per iteration: 1 cycle x the
  routed period, now verified by simulation). The model's estimates beside them (11.92 / 15.48 / 17.11) show the size
  of the period error.
- Every other kernel: `dynamatic_est.tsv` (this directory) has one ESTIMATE line per kernel with a loop, in
  research/tools/suite/dynamatic_ref.tsv's format. **ipow becomes 50.0 (ESTIMATE)** in place of the hand estimate
  67. Both count 5 cycles; the period is now ipow's own (10.00 ns: its model path, 12.61 ns, is shorter than
  xorshift's 15.03, because the 4-stage multiplier registers its data path) instead of being borrowed from xorshift /
  collatz.
- gcd has two per-iteration terms. Use **3.03 cycles x 12.55 = 38.0 ns per main iteration** and **1.00 x 12.55 =
  12.6 ns per inner ctz shift**, both ESTIMATES. They sit at the low end of the hand estimate's ranges (38.2-53.5 and
  12.7-17.8). The table's single gcd figure (12.4) is the inner shift.
- A ratio against these figures inherits their error: about 16 % from the period (worst leave-one-out), plus the
  routing scatter of the three calibration routes (one seed each).

## What these figures do NOT capture

- **The period is an ESTIMATE.** It is Dynamatic's pre-synthesis per-unit delays, made for its own (Vivado) target.
  No LUT packing: a shift by a constant is wires in hardware and 2.5 ns in the model. No placement, no wires, no seed
  scatter. One factor, fitted on three single-seed routes; worst leave-one-out error 15.8 %.
- **Only `on-merges` placement.** Dynamatic's MILP placements (fpga20 / fpl22 at a target period) cannot run in this
  build (no Gurobi, no CBC). Where on-merges makes a loop wait for a multi-cycle unit (memory, `muli`, a divider),
  the MILP would give fewer cycles per iteration. The column "lower bound, any placement" shows how far that could
  go. Examples: memsum 5.74 -> >= 1, fir 5.99 -> >= 1, factorial 12.59 -> >= 4, ipow 5 -> >= 4. That bound is a
  static ring analysis, not a Dynamatic run. The MILP would also change the period: it buffers to a target. For the
  three routed kernels (1 cycle per iteration) the cycle count is the same either way; only the period would
  differ.
- **The cycle model is a transcription of Dynamatic's Verilog**, not Dynamatic's own simulation (export-rtl and
  hls-verifier are not built). The answer check catches value and protocol errors only on the paths the vectors
  exercise (controls b, c). It cannot see a cycle-count error at all (control d). Independent cycle counts exist
  for xorshift, collatz, collatz64, ipow and gcd only, and the model matches all five.
- **One call from reset**, with an environment that offers every argument at cycle 0 and is always ready. No
  back-to-back calls, no host I/O, no reset or start-up latency of a real testbench.
- **Memory** is an ideal BRAM with a 1-cycle read behind Dynamatic's mem_controller. No BRAM mapping and no memory
  timing.
- **Multi-loop kernels.** The cycles-per-iteration column is the most executed loop's figure. The async P (the
  event graph's maximum cycle ratio) may refer to another loop: compare loop by loop (the other loops' intervals
  are in the table, and per-loop fits are in `dynamatic_est.json`).
- **Vectors.** main() kernels have one call. Their cycles per iteration is the mean back-edge interval of that
  call, not a fit over several calls.

## Open problems

- **A MILP placement.** The MILP formulation (fpga20 in `HandshakePlaceBuffers`) could be solved with an open
  solver (scipy 1.11's HiGHS is installed). The result could go back into the IR with
  `--handshake-placebuffers-custom` (pred / outid / slots / type). Not attempted: it means reimplementing the
  FPGA'20 MILP from its paper and source.
- **LSQ kernels** (56): a cycle model of Dynamatic's LSQ (its generator is Python, in `tools/backend/lsq-generator`,
  which is not vendored here).
- **A better period** needs Dynamatic netlists routed here: export-rtl on a machine that has it, then 4+ seeds per
  kernel (`cells/hw/dyn_baseline.sh`). With more routed kernels the calibration could also check its own form
  (one factor vs affine vs per-op). With 3 points, nothing better can be told apart.

## Files

- `research/tools/suite/dynamatic_est.py`: the tool. Run `KERNEL [VECTORS]` for one kernel, `--calibrate` for the
  period fit, `--table [K...]` for this table (`--fixtures DIR` adds a build/frontend directory, read only).
- `research/tools/suite/test_dynamatic_est.py`: answers, cycle cross-checks and negative controls; all pass,
  about 5 min on one core.
- `research/data/suite/dynamatic/table.md`: the table above, as the tool writes it.
- `research/data/suite/dynamatic/dynamatic_est.tsv`: dynamatic_ref.tsv-format lines.
- `research/data/suite/dynamatic/dynamatic_est.json`: every call: arguments, cycles, result, the C's result,
  per-loop executions and intervals, fits, critical path, bound.

Run (one core): `python3 research/tools/suite/dynamatic_est.py --table --fixtures
/tmp/bot/sa/suitek/repo/build/frontend --fixtures /tmp/bot/sa/suited/repo/build/frontend --max-cycles 1000000`.
That took 7 minutes for 135 kernels. The toolchain is Dynamatic's owner build
(`/home/afpga/dynamatic/build/bin/dynamatic-opt`), components.json from its data/, gcc 13.3 (clang 18 from the
same build for `_BitInt`). There is no nextpnr: nothing here is routed.
