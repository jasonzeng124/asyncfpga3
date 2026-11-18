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

## Update 2026-11-18 (dynfig): memory kernels on the suite's own calls, latency per call, loop-free kernels

- **v2 vectors (arrays).** The suite's memory kernels and several of Dynamatic's tests run on v2 bench files
  (`research/data/suite/bench/README.md`: per call the operand words, then every array). The tool used to read such a
  file as one call per line. It now reads the bench's layout from the handshake signature, gives every call its own
  arrays, and takes the expected values from the suite's own oracle, `research/tools/suite/oracle_mem.sh` (the C): the
  result and every array after each call. Dynamatic's tests that used to run on their own main() (one call) now run
  on the suite's vectors (`research/data/suite/vec/K.hex`, as suite_one.sh picks them), so both sides compute the same
  calls. **66 kernels simulated, 409 of 409 calls right, results and arrays.** The 119 kernels whose vectors did not
  change give the same figures as before, column for column.
- **The memory units against Dynamatic's Verilog, cycle by cycle** (`research/tools/suite/dyn_memcosim.py`): two
  `load` units -> `mem_controller` (2 loads, 1 store, 1 control) -> a BRAM with a 1-cycle read. One side is the
  Verilog of `dynamatic/data/verilog` (mem_controller.v, mem_controller_loadless.v, support/mc_support.v, load.v,
  tehb.v, unedited, iverilog); the other is this tool's Load and MemController classes. Both run in the same random
  environment (back-to-back and gapped tokens, random readies). **8 seeds x 3000 cycles: every port equal in every
  cycle, and the BRAM contents equal at the end** (15631 reads, 6144 writes, 45 cycles with memEnd valid). Three
  negative controls, each caught on 8 of 8 seeds: the read data one register late; the read arbiter's priority
  reversed; a store that does not decrement the pending-store counter. For these units, "the cycle model is a
  transcription" is now a measured equality with the Verilog. It is still not Dynamatic's own simulator, and the BRAM
  is the testbench's ideal one.
- **Memory kernels, on the suite's vectors** (all ESTIMATES except the cycles):

| kernel | calls right (result and arrays) | cycles per iteration (on-merges) | period, ns (ESTIMATE) | ns per iteration (ESTIMATE) | latency per call, ns (ESTIMATE), mean |
|---|---|---|---|---|---|
| memsum | 5 of 5 | 5.98 (fit over 5 calls) | 9.92 | 59.3 | 1033 |
| dot2 | 8 of 8 | 5.98 | 9.92 | 59.3 | 1212 |
| gather | 9 of 9 | 6.98 | 9.92 | 69.2 | 1510 |
| fill (one store per trip) | 5 of 5 | 1.00 (exactly 3 + 1 x trips) | 10.95 | 11.0 | 208 |
| test_bitint | 6 of 6 | 5.44 (mean interval: 10 trips in every call, no fit) | 8.14 | 44.3 | 505 |
| if_loop_1 | 8 of 8 | 1.99 | 9.99 | 19.9 | 1146 |
| if_loop_2 | 8 of 8 | 1.99 | 8.36 | 16.7 | 1064 |
| sumi3_mem | 3 of 3 | 9.99 (mean interval) | 8.85 | 88.4 | 88540 |
| fir | 2 of 2 | 6.00 (mean interval) | 8.12 | 48.7 | 48738 |

  Why about 6 cycles on memsum, dot2 and fir: on-merges puts one oehb and one tehb after each merge. The sum's ring
  then waits for the load (address tehb, the arbiter, the BRAM's registered read, the data tehb) with one slot of
  buffering, so the loop runs at the memory round trip. The "lower bound, any placement" column says 1 for all of
  them: a MILP placement could pipeline the loads (see "Only on-merges" below). memsum's figure moves from 56.9
  (main(), one call, mean interval 5.74) to 59.3 (the fit over the suite's 5 calls, 5.98 cycles; intercept 2.5).
- **Latency per call** (`dynamatic_lat.tsv`, new). Per kernel: Dynamatic's cycles per call on the suite's own calls
  (suite_one.sh's vectors; for gcd that is gcd8, not gcd18), times the period ESTIMATE, and the trip count of each call
  (header executions of the most executed loop). `research/tools/suite/suite_table.py` compares this with our latency
  per call on the same calls, and uses the trip counts where our P is missing (below).
- **Loop-free kernels.** "ns per iteration" is undefined on both sides, so the figure is the latency per call.
  Dynamatic: cycles per call x period. straight 1 x 14.92 = 14.9 ns; cmpchain 2-6 cycles x 7.68 ns (mean 33.9);
  test_loop_free 3 x 3.85 = 11.6 ns; unused_arg 2 x 0.97 = 1.9 ns; test_int16 takes 1 cycle but has no period
  (every arc of its circuit is 0 in components.json). The periods of test_loop_free (model path 4.86 ns) and
  unused_arg (1.23 ns) are extrapolated far below the three calibration points (15.0-21.6 ns of model path), and
  0.97 ns is not a clock any FPGA runs. suite_table.py marks these two and leaves them out of the latency mean.
  **The right metric** is the kernel's own latency from operands to result, on both sides. Ours is not that yet. The
  bench's latmin counts from the harness's issue state to its capture of the result, in host cycles of 12 ns, and a
  constant kernel (test_int16) already takes 5 cycles = 60 ns. So for a kernel of a few ns the latency ratio
  measures the bench. The kernel's own latency is in every full-stack run's VCD: the rise of the kernel's input
  request to the rise of its result request, exact to the ps. Measuring it there is an open problem (below).
- **MILP (lead 8's task 4): not possible here.** dynamatic-opt (the owner's build of 2026-08-12) has CBC compiled out.
  Its solver factory holds only the stubs ("Gurobi not installed!", "CBC not installed!") and none of the CBC
  solver's code: no LP file or solution-file handling among its strings. The vendored tree (`dynamatic/`: build,
  data, include, integration-test) has no lib/ sources to rebuild from. So a CBC installed in user space
  (`pip install mip`) cannot be reached from this binary. The README's open problem stands: write the FPGA'20 MILP
  for an open solver and feed the result back through `--handshake-placebuffers-custom`.

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

- Memory kernels on the suite's v2 vectors (added 2026-11-18): memsum, dot2, gather, fill, test_bitint, if_loop_1,
  if_loop_2, sumi3_mem, fir -- every call's result and every array after it equal oracle_mem.sh's; fill is exactly
  3 + 1 x trips cycles. Negative controls: (f) a store writes data + 1: fill WRONG on 4 of 5 calls (the 4 with a
  store; the answers do not read the array, only the array check sees it); (g) the BRAM returns the word after the
  one addressed: caught on memsum, dot2, gather; (h) every call gets the previous call's arrays: caught on memsum,
  dot2, gather, test_bitint. And `dyn_memcosim.py` (above): the memory units equal to Dynamatic's Verilog in every
  cycle, three defects caught.

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
- Vectors: the six originals use suite_one.sh's gate vectors; the suite's kernels `kernels/<k>/vec.hex`; Dynamatic's
  tests that are in the suite `research/data/suite/vec/<k>.hex` (since 2026-11-18; v2 files with arrays where the
  kernel has memories, checked against oracle_mem.sh). The rest use the C's own `main()` (one call; for Dynamatic's
  integration tests, the input Dynamatic itself tests with).
- "latency per call" = cycles per call x the estimated period, mean (range) over the calls, on the suite's own calls
  (gcd: gcd8, the calls its draws run). An ESTIMATE wherever it appears; `dynamatic_lat.tsv` has it per call.
- Fixtures: this repo's `build/frontend` first (108 kernels on 2026-11-18), then suitek's, then suited's
  (`/tmp/bot/sa/suited/repo/build/frontend`, Dynamatic's integration tests).
- "ns per iteration" = cycles per iteration x the estimated period. It is an ESTIMATE wherever it appears.
- Multi-loop kernels: the cycles-per-iteration column also gives the median back-edge interval of the other loops.
  An outer loop's interval includes its inner loops.

| kernel | vectors | Dynamatic cycles per call (simulated; answers = C) | cycles per iteration (simulated, on-merges) | lower bound, any placement | period, ns (ESTIMATE) | ns per iteration (ESTIMATE) | latency per call, ns (ESTIMATE): mean (range) | measured period, ns (routed, 1 seed, 2026-08) |
|---|---|---|---|---|---|---|---|---|
| admm | main() | not simulated (float argument) | - | - | - | - | - | - |
| atax | main() | not simulated (LSQ) | - | - | - | - | - | - |
| atax_float | main() | not simulated (floating point (memref<400xf32>)) | - | - | - | - | - | - |
| bicg | main() | not simulated (LSQ) | - | - | - | - | - | - |
| bicg_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - | - |
| binary_search | main() | 240 (1 call) | 3.00 (bb1, the most executed of 2 loops; median back-edge interval of the others: bb4 3) | 1 | 8.06 | 24.2 | 1934.8 (1934.8-1934.8; 1 calls) | - |
| branchloop | kernels/branchloop/vec.hex | 2-213 (14 calls) | 3.44 (bb1, the most executed of 2 loops; median back-edge interval of the others: bb3 1) | 1 | 10.70 | 36.8 | 486.1 (21.4-2279.1; 14 calls) | - |
| brhash | kernels/brhash/vec.hex | 2-770 (10 calls) | 3.00 | 1 | 12.13 | 36.4 | 1443.8 (24.3-9342.3; 10 calls) | - |
| cmpchain | kernels/cmpchain/vec.hex | 2-6 (17 calls) | - | - | 7.68 | - (no loop) | 33.9 (15.4-46.1; 17 calls) | - |
| cnn | main() | not simulated (LSQ) | - | - | - | - | - | - |
| collatz | research/data/eventgraph/gate/col18.hex | 2-336 (17 calls) | 1.00 | 1 | 15.48 | 15.5 | 1500.6 (31.0-5201.1; 17 calls) | 14.05 (cycles x period = 14.05) |
| collatz64 | research/data/eventgraph/gate/c6419.hex | 2-951 (18 calls) | 1.00 | 1 | 17.11 | 17.1 | 3963.4 (34.2-16273.6; 18 calls) | 17.84 (cycles x period = 17.84) |
| cordic | main() | not simulated (float argument) | - | - | - | - | - | - |
| countloop | kernels/countloop/vec.hex | 2-258 (10 calls) | 1.00 | 1 | 8.36 | 8.4 | 341.1 (16.7-2157.2; 10 calls) | - |
| covariance | main() | not simulated (LSQ) | - | - | - | - | - | - |
| covariance_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - | - |
| digitdiv | main() | 362 (1 call) | 39.50 | 35 | 7.69 | 303.8 | 2784.0 (2784.0-2784.0; 1 calls) | - |
| divergent_paths | main() | not simulated (LSQ) | - | - | - | - | - | - |
| dot2 | kernels/dot2/vec.hex | 3-194 (8 calls) | 5.98 | 1 | 9.92 | 59.3 | 1212.2 (29.7-1923.6; 8 calls) | - |
| factorial | research/data/suite/vec/factorial.hex | 3-55 (12 calls) | 13.00 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb3 13) | 4 | 9.98 | 129.8 | 233.8 (30.0-549.1; 12 calls) | - |
| fill | kernels/fill/vec.hex | 3-43 (5 calls) | 1.00 | 1 | 10.95 | 11.0 | 208.1 (32.9-470.9; 5 calls) | - |
| fir | research/data/suite/vec/fir.hex | 6002 (2 calls) | 5.99 | 1 | 8.12 | 48.7 | 48738.0 (48738.0-48738.0; 2 calls) | - |
| fixed | main() | not simulated (float argument) | - | - | - | - | - | - |
| float_basic | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - | - |
| fold64 | kernels/fold64/vec.hex | 2-257 (10 calls) | 1.00 | 1 | 11.93 | 11.9 | 448.7 (23.9-3067.2; 10 calls) | - |
| gather | kernels/gather/vec.hex | 3-226 (9 calls) | 6.98 | 1 | 9.92 | 69.2 | 1510.5 (29.7-2240.9; 9 calls) | - |
| gaussian | main() | not simulated (LSQ) | - | - | - | - | - | - |
| gcd | research/data/eventgraph/gate/gcd18.hex | 2-163 (18 calls) | 0.99 (bb11, the most executed of 5 loops; median back-edge interval of the others: bb3 1, bb5 1, bb7 1, bb10 4) | 1 | 12.55 | 12.4 | 430.0 (25.1-1669.7; 8 calls, research/data/suite/vec/gcd8.hex) | - |
| gemm | main() | not simulated (floating point (sitofp)) | - | - | - | - | - | - |
| gemm_float | main() | not simulated (float argument) | - | - | - | - | - | - |
| gemver | main() | not simulated (LSQ) | - | - | - | - | - | - |
| gemver_float | main() | not simulated (float argument) | - | - | - | - | - | - |
| gesummv_float | main() | not simulated (float argument) | - | - | - | - | - | - |
| get_tanh | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| gsum | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| gsumif | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| histogram | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| horner | kernels/horner/vec.hex | 2-1282 (11 calls) | 5.00 | 4 | 8.36 | 41.8 | 1601.6 (16.7-10719.3; 11 calls) | - |
| if_convert | main() | 1125 (1 call) | 6.00 | 4 | 10.95 | 65.7 | 12319.3 (12319.3-12319.3; 1 calls) | - |
| if_loop_1 | research/data/suite/vec/if_loop_1.hex | 3-202 (8 calls) | 1.99 | 1 | 9.99 | 19.9 | 1145.8 (30.0-2017.1; 8 calls) | - |
| if_loop_2 | research/data/suite/vec/if_loop_2.hex | 3-202 (8 calls) | 1.99 | 1 | 8.36 | 16.7 | 1064.0 (25.1-1689.0; 8 calls) | - |
| if_loop_3 | main() | 303 (1 call) | 3.00 | 1 | 9.18 | 27.5 | 2780.5 (2780.5-2780.5; 1 calls) | - |
| if_loop_add | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| if_loop_mul | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| iir | main() | 5996 (1 call) | 5.99 | 4 | 8.12 | 48.7 | 48689.3 (48689.3-48689.3; 1 calls) | - |
| image_resize | main() | 1833 (1 call) | 1.97 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 61) | 1 | 9.64 | 18.9 | 17671.0 (17671.0-17671.0; 1 calls) | - |
| insertion_sort | main() | not simulated (LSQ) | - | - | - | - | - | - |
| ipow | research/data/eventgraph/gate/ipow17.hex | 2-157 (17 calls) | 5.00 | 4 | 10.00 | 50.0 | 513.9 (20.0-1569.3; 17 calls) | - |
| isprime | research/data/alltable/isp17.hex | 2-2139 (18 calls) | 1.00 (bb4, the most executed of 3 loops; median back-edge interval of the others: bb3 22, bb6 1) | 1 | 9.26 | 9.3 | 2501.2 (18.5-19815.3; 18 calls) | - |
| iterative_division | research/data/suite/vec/iterative_division.hex | 2-260 (15 calls) | 1.00 | 1 | 10.22 | 10.2 | 754.1 (20.4-2656.8; 15 calls) | - |
| iterative_sqrt | research/data/suite/vec/iterative_sqrt.hex | 2-172 (12 calls) | 9.98 | 8 | 11.11 | 110.8 | 758.2 (22.2-1910.8; 12 calls) | - |
| jacobi_1d_imper | main() | not simulated (LSQ) | - | - | - | - | - | - |
| kernel_2mm | main() | not simulated (LSQ) | - | - | - | - | - | - |
| kernel_2mm_float | main() | not simulated (float argument) | - | - | - | - | - | - |
| kernel_3mm | main() | not simulated (LSQ) | - | - | - | - | - | - |
| kernel_3mm_float | main() | not simulated (floating point (memref<100xf32>)) | - | - | - | - | - | - |
| kmp | main() | not simulated (LSQ) | - | - | - | - | - | - |
| lfsrfind | kernels/lfsrfind/vec.hex | 3-514 (10 calls) | 2.00 | 1 | 9.74 | 19.5 | 901.1 (29.2-5007.0; 10 calls) | - |
| loop_array | main() | not simulated (LSQ) | - | - | - | - | - | - |
| loop_path | main() | 337 (1 call) | 2.00 | 1 | 16.13 | 32.3 | 5436.7 (5436.7-5436.7; 1 calls) | - |
| lu | main() | not simulated (floating point (memref<9xf32>)) | - | - | - | - | - | - |
| matching | main() | not simulated (LSQ) | - | - | - | - | - | - |
| matching_2 | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| matrix | main() | 162005 (1 call) | 5.93 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 5400, bb2 180) | 1 | 9.64 | 57.2 | 1561805.2 (1561805.2-1561805.2; 1 calls) | - |
| matrix_power | main() | not simulated (LSQ) | - | - | - | - | - | - |
| matvec | main() | 60004 (1 call) | 5.98 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 600) | 1 | 8.14 | 48.7 | 488487.5 (488487.5-488487.5; 1 calls) | - |
| memsum | kernels/memsum/vec.hex | 3-194 (5 calls) | 5.98 | 1 | 9.92 | 59.3 | 1033.2 (29.7-1923.6; 5 calls) | - |
| mul_example | main() | 1002 (1 call) | 9.91 | 1 | 8.06 | 79.9 | 8077.7 (8077.7-8077.7; 1 calls) | - |
| mvt_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - | - |
| nest3 | kernels/nest3/vec.hex | 2-242 (12 calls) | 1.00 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 11, bb2 3) | 1 | 11.06 | 11.1 | 545.6 (22.1-2676.5; 12 calls) | - |
| nested | kernels/nested/vec.hex | 2-290 (11 calls) | 1.00 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 8) | 1 | 9.98 | 10.0 | 416.5 (20.0-2894.9; 11 calls) | - |
| nested_conditionals_1 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| nested_conditionals_2 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| nested_loop | main() | 2419 (1 call) | 6.00 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 1208) | 4 | 7.43 | 44.6 | 17964.5 (17964.5-17964.5; 1 calls) | - |
| path_profiling | main() | not simulated (LSQ) | - | - | - | - | - | - |
| pivot | main() | not simulated (LSQ) | - | - | - | - | - | - |
| polyn_mult | main() | not simulated (LSQ) | - | - | - | - | - | - |
| prediction | main() | not simulated (floating point (memref<100xf32>)) | - | - | - | - | - | - |
| quadrec | kernels/quadrec/vec.hex | 2-258 (10 calls) | 1.00 | 1 | 9.09 | 9.1 | 352.8 (18.2-2345.7; 10 calls) | - |
| share_test_1 | main() | 11997 (1 call) | 5.99 (bb1, the most executed of 2 loops; median back-edge interval of the others: bb2 6) | 1 | 9.74 | 58.4 | 116884.0 (116884.0-116884.0; 1 calls) | - |
| share_test_2 | main() | 902 (1 call) | 8.92 | 1 | 10.30 | 91.9 | 9293.0 (9293.0-9293.0; 1 calls) | - |
| simple_example_1 | main() | 2 (1 call) | - | - | 2.38 | - (no loop) | 4.8 (4.8-4.8; 1 calls) | - |
| single_loop | main() | 3009 (1 call) | 6.00 | 4 | 6.72 | 40.3 | 20222.5 (20222.5-20222.5; 1 calls) | - |
| sobel | main() | 11329 (1 call) | 4.67 (bb7, the most executed of 4 loops; median back-edge interval of the others: bb1 755, bb2 57, bb6 17) | 1 | 9.29 | 43.4 | 105282.0 (105282.0-105282.0; 1 calls) | - |
| sparse | main() | not simulated (floating point (memref<100xf32>)) | - | - | - | - | - | - |
| spmv | main() | 150 (1 call) | 5.15 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 7) | 1 | 8.36 | 43.1 | 1254.2 (1254.2-1254.2; 1 calls) | - |
| sqrtsub | kernels/sqrtsub/vec.hex | 2-258 (13 calls) | 1.00 | 1 | 8.36 | 8.4 | 292.0 (16.7-2157.2; 13 calls) | - |
| stencil_2d | main() | 1518 (1 call) | 4.66 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 54, bb2 17) | 1 | 8.68 | 40.4 | 13169.3 (13169.3-13169.3; 1 calls) | - |
| straight | kernels/straight/vec.hex | 1 (12 calls) | - | - | 14.92 | - (no loop) | 14.9 (14.9-14.9; 12 calls) | - |
| subdiag | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| subdiag_fast | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| sum3 | main() | 12 (1 call) | 1.00 | 1 | 8.36 | 8.4 | 100.3 (100.3-100.3; 1 calls) | - |
| sumi3_mem | research/data/suite/vec/sumi3_mem.hex | 10002 (3 calls) | 9.99 | 1 | 8.85 | 88.4 | 88540.1 (88540.1-88540.1; 3 calls) | - |
| symm_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - | - |
| syr2k_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - | - |
| test_bitint | research/data/suite/vec/test_bitint.hex | 62 (6 calls) | 5.44 | 1 | 8.14 | 44.3 | 504.7 (504.7-504.7; 6 calls) | - |
| test_bool_array | main() | 3 (1 call) | - | - | 3.56 | - (no loop) | 10.7 (10.7-10.7; 1 calls) | - |
| test_constant_array | main() | not simulated (internal array (handshake.ram)) | - | - | - | - | - | - |
| test_divui | main() | 36 (1 call) | - | - | - (no arc in the model) | - (no loop) | - | - |
| test_double | main() | not simulated (type <f64>) | - | - | - | - | - | - |
| test_flatten_array | main() | 1067 (1 call) | 1.93 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 266, bb2 33) | 1 | 8.14 | 15.7 | 8686.4 (8686.4-8686.4; 1 calls) | - |
| test_fneg | main() | not simulated (float argument) | - | - | - | - | - | - |
| test_int16 | research/data/suite/vec/test_int16.hex | 1 (1 call) | - | - | - (no arc in the model) | - (no loop) | - | - |
| test_internal_array | main() | not simulated (internal array (handshake.ram)) | - | - | - | - | - | - |
| test_loop_free | research/data/suite/vec/test_loop_free.hex | 3 (10 calls) | - | - | 3.85 | - (no loop) | 11.6 (11.6-11.6; 10 calls) | - |
| test_memory_1 | main() | 10 (1 call) | 1.67 | 1 | 8.36 | 13.9 | 83.6 (83.6-83.6; 1 calls) | - |
| test_memory_10 | main() | 11 (1 call) | 2.00 | 1 | 8.36 | 16.7 | 92.0 (92.0-92.0; 1 calls) | - |
| test_memory_11 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_12 | main() | 13 (1 call) | 2.33 | 1 | 7.71 | 18.0 | 100.2 (100.2-100.2; 1 calls) | - |
| test_memory_13 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_14 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_15 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_16 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_17 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_18 | main() | 20 (1 call) | 3.50 | 1 | 7.79 | 27.3 | 155.7 (155.7-155.7; 1 calls) | - |
| test_memory_2 | main() | 10 (1 call) | 1.67 | 1 | 8.36 | 13.9 | 83.6 (83.6-83.6; 1 calls) | - |
| test_memory_3 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_4 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_5 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_6 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_7 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_8 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_9 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_smallbound | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_stdint | main() | 1002 (1 call) | 9.91 | 1 | 8.14 | 80.7 | 8157.2 (8157.2-8157.2; 1 calls) | - |
| test_unroll | main() | not simulated (internal array (handshake.ram)) | - | - | - | - | - | - |
| threshold | main() | not simulated (LSQ) | - | - | - | - | - | - |
| triangular | main() | not simulated (LSQ) | - | - | - | - | - | - |
| trisolv | main() | not simulated (LSQ) | - | - | - | - | - | - |
| twoloops | kernels/twoloops/vec.hex | 3-258 (11 calls) | 1.00 (bb3, the most executed of 2 loops; median back-edge interval of the others: bb1 1) | 1 | 9.09 | 9.1 | 514.1 (27.3-2345.7; 11 calls) | - |
| unused_arg | research/data/suite/vec/unused_arg.hex | 2 (6 calls) | - | - | 0.97 | - (no loop) | 1.9 (1.9-1.9; 6 calls) | - |
| varshift | kernels/varshift/vec.hex | 2-258 (10 calls) | 1.00 | 1 | 11.84 | 11.8 | 493.6 (23.7-3054.2; 10 calls) | - |
| vector_rescale | main() | 6002 (1 call) | 5.99 | 1 | 8.12 | 48.7 | 48738.0 (48738.0-48738.0; 1 calls) | - |
| video_filter | main() | 5403 (1 call) | 5.93 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 180) | 1 | 9.64 | 57.1 | 52087.5 (52087.5-52087.5; 1 calls) | - |
| while_loop_1 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| while_loop_2 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| while_loop_3 | main() | 13 (1 call) | 5.00 | 4 | 6.80 | 34.0 | 88.4 (88.4-88.4; 1 calls) | - |
| wrap_if | main() | not simulated (LSQ) | - | - | - | - | - | - |
| xorshift | research/data/eventgraph/gate/xor19.hex | 2-1002 (19 calls) | 1.00 | 1 | 11.92 | 11.9 | 1177.4 (23.8-11942.6; 19 calls) | 12.73 (cycles x period = 12.73) |

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
- **Our latency per call at the kernel's boundary** (2026-11-18). The bench's latmin includes its own issue,
  synchroniser and capture (5 host cycles = 60 ns for a constant kernel), quantised to 12 ns. For a loop-free
  kernel the ratio therefore measures the bench. The full-stack run's VCD has the kernel's own latency: the rise of
  its input request to the rise of its result request, per call. lane2_run.sh could write it beside P.
- **A floor for the period estimate.** One factor on a model path extrapolates to 0.97 ns for unused_arg. A real
  Dynamatic circuit is limited by the device (clock tree, BRAM) long before that. The device limits for the xc7z010
  are not in this repository, so no floor is applied. The two kernels concerned are marked instead.

## Files

- `research/tools/suite/dynamatic_est.py`: the tool. Run `KERNEL [VECTORS]` for one kernel, `--calibrate` for the
  period fit, `--table [K...]` for this table (`--fixtures DIR` adds a build/frontend directory, read only).
- `research/tools/suite/test_dynamatic_est.py`: answers, cycle cross-checks and negative controls; all pass,
  about 5 min on one core.
- `research/data/suite/dynamatic/table.md`: the table above, as the tool writes it.
- `research/data/suite/dynamatic/dynamatic_est.tsv`: dynamatic_ref.tsv-format lines.
- `research/data/suite/dynamatic/dynamatic_est.json`: every call: arguments, cycles, result, the C's result,
  per-loop executions and intervals, fits, critical path, bound.
- `research/data/suite/dynamatic/dynamatic_lat.tsv` (2026-11-18): per kernel, Dynamatic's latency per call on the
  suite's own calls (cycles per call x period ESTIMATE), the calls' trip counts, the period and its model path; read
  by suite_table.py.
- `research/tools/suite/dyn_memcosim.py` (2026-11-18): Load / MemController against Dynamatic's Verilog, cycle by
  cycle (`--defect bram2|prio|nodec` for the negative controls); 8 seeds x 3000 cycles in about a minute.

Run (one core): `python3 research/tools/suite/dynamatic_est.py --table --fixtures
/tmp/bot/sa/suitek/repo/build/frontend --fixtures /tmp/bot/sa/suited/repo/build/frontend --max-cycles 1000000`.
That took 7 minutes for 135 kernels (2026-11-18: under 3 minutes for 139, one core). The toolchain is Dynamatic's owner build
(`/home/afpga/dynamatic/build/bin/dynamatic-opt`), components.json from its data/, gcc 13.3 (clang 18 from the
same build for `_BitInt`). There is no nextpnr: nothing here is routed.
