# Division and modulo: the frontend's remui and a divider in bdc (subagent divmod, 2026-11-18)

research/PROGRAM.md 2026-11-18, lead 4: "division and modulo (the frontend's remui; a divider cell under CLAUDE.md's
rule)". kernels/SUITE.md had digitsum stopping in Dynamatic's frontend (`failed to legalize operation 'arith.remui'`)
and digitdiv stopping in bdc (`no width rule for handshake op 'divui'`); Dynamatic's integer tests need divsi 3 /
divui 1 / remsi 1. This note: the frontend fix, the divider, the evidence, and what it does not show.

**Result.** digitsum, digitdiv, two new straight-line kernels (divmodu, divmods) and Dynamatic's test_divui compile and
pass simcheck against their C in both flows. On the full-stack gate at the worst corner (nextpnr 6e5d224472232d5d,
default flow, placeholder sizes) digitdiv (= digitsum's circuit) passes on 4 of 4 placer seeds, divmods (divsi +
remsi) on 4 of 4 and divmodu (divui + the BDC_FE_UREM remainder) on 4 of 4, every bitstream EQUIVALENT. The 32-bit
divider is ~1110 LUTs of array + 257 of enable chain + 151 CARRY4, settles in 122 ns at the worst corner (79
FAST_MIN, 225 SLOW_MAX; means of 4 routes), and its placeholder matched delay is 528 links (213 ns there).

## 1. Why the frontend refuses `%` on unsigned operands

Dynamatic's handshake dialect has `divsi`, `remsi` and `divui` and no `remui`
(dynamatic/include/dynamatic/Dialect/Handshake/HandshakeArithOps.td: `Handshake_DivSIOp`, `Handshake_RemSIOp`,
`Handshake_DivUIOp`, each `IsIntSizedChannel<32>` on both operands and the result). lower-cf-to-handshake converts
each arith op into its handshake twin, so `arith.remui` has nothing to become: `failed to legalize`. C's unsigned
`%` is the only one of the four that stops there; signed `%` lowers to `remsi`, `/` to `divui` / `divsi`.

**The fix, opt-in: `BDC_FE_UREM=1 ./bdc/frontend.sh K`** (step 4c, after step 4's opt passes and before
mem-dep-analysis). Each `%r = urem iN %x, %y` in the LLVM IR becomes

    %bdc.urem.q.r = udiv iN %x, %y
    %bdc.urem.m.r = mul iN %bdc.urem.q.r, %y
    %r            = sub iN %x, %bdc.urem.m.r

(exact mod 2^N for y != 0; y = 0 is UB for urem and udiv alike), then `opt -passes=early-cse` merges the new udiv
with an existing `x / y`, so digitsum's `v % b` and `v / b` share ONE divider. Choices, each checked:

- After step 4, not before: step 4's instcombine is the pass that would fold `x - (x / y) * y` back into `urem`.
- Not LLVM's own `div-rem-pairs` pass: it does the pair case (digitsum) but inserts `freeze`, and
  translate-llvm-to-std crashes on `freeze` (checked on digitsum: a stack dump, no cf.mlir). It also leaves a lone `%`.
- Only when the KERNEL's own function has a urem. The first version keyed on any urem in the module; polyn_mult's
  urems are in `main` (dropped at step 7), and early-cse on the module changed the kernel's own loads (all six
  comp/*.mlir differed). early-cse still runs on the whole kernel function when it has a urem, so it may merge other
  repeated expressions in such a kernel too (digitsum's MLIR came out equal to digitdiv's but for the name).
- A urem line of any other shape (trailing metadata, vector types) is left alone and the step fails loudly.

**Byte identity** (every fixture in build/frontend, 111 kernels: the bot's 108 plus digitsum, divmodu, divmods; all six
`comp/*.mlir` compared with `cmp`, frontend at this branch's head, `$HOME/dynamatic`):

| knob | identical | not |
|---|---|---|
| off (`BDC_FE_UREM` unset) | 109 / 111 | digitsum, divmodu: stop at `arith.remui` as before (their fixtures were made with the knob) |
| on (`BDC_FE_UREM=1`) | 111 / 111 | - |

So with the knob ON, every kernel that compiled before compiles to the same bytes; only a kernel whose own function has
an unsigned `%` changes (from "does not compile"). Default stays off, as the brief asked; it could be on.

## 2. The divider in bdc

**What is built.** `divui`, `divsi`, `remsi` and `remui` are compute units like `addi` (bdc/compute.py: `DIV`,
`div_datapath`, `DIV_TAP`, `_depth_class` "div"; bdc/emit.py: `result_channels`, `DELAY_BEARING`, `_op_*`;
bdc/bd-config.json): one `bd_join` over both operands, the `uor` anchor, ONE `bd_delay_gated` matched delay sized
by the rules like any operator's, and a combinational datapath. No new cell in cells/rtl/ (frozen): the datapath is
generated Verilog over yosys-inferred carry chains and kept LUT primitives, as the cmpi unit's kept LUT1 is.

**The array: restoring division, written out.** W stages; stage s decides quotient bit W-1-s. Before stage s the
partial remainder is below both the divisor and 2^s, so stage s works on s+1 bits only:
`t = {r(s-1), a[W-1-s]}`, `d = {0, t} - {0, b[s:0]}` (an (s+2)-bit subtract; its top bit is the borrow), and
`t >= b` exactly when b has no bit above s (`hi[s+1] = |b[W-1:s+1]` is 0) and the subtract does not borrow. The
stage passes on `d` or `t` through one kept LUT5 per bit (LUT4 in the last stage, built only for a remainder). `hi`
is a prefix OR of the divisor from kept LUTs of at most six inputs. Signed ops divide magnitudes (INT_MIN's is
2^31, as unsigned) and negate the quotient when the signs differ, the remainder when the dividend is negative: C's
truncation toward zero, the remainder with the dividend's sign.

**Each stage is gated by an enable** (the reason is section 4's first routed run): en(s) is tap 8 (s + 1) of a
chain of kept LUT2s (one stage more for a signed op), started by `hold = join | z_ack`; a stage's selects and its
quotient bit are 0 until en(s) rises. The chain rises a link at a time from the join and falls all at once when the
acknowledge falls (`tap(j) = tap(j-1) & hold`): this library's bundling contract holds data from req-rise until
ack-FALL (cells/rtl/bd_ctl.v, bd_steer), and a first version that closed the stages with the join zeroed z_data while
a steer downstream was still reading it (simcheck digitdiv: vector 0 wrong, then a deadlock). The result is the same
function once every enable is up, and the matched delay is still what makes it safe: rule A's data peak runs through
the enable chain (it starts at the join), and the routed peaks below include it. DIV_TAP = 8 links a stage is ~1.2x
(1.4x / 1.5x) an average stage of the ungated array at the worst corner (FAST_MIN / SLOW_MAX), from seed 1's numbers.

Why not Verilog's `/`: yosys maps it onto techmap.v's `$__div_mod_u`, which compares every stage against the divisor
shifted to 2W-1 bits. Synthesised alone (`synth_xilinx -family xc7 -flatten`, yosys 0.62, as flow.sh runs it), 32
bits, quotient only:

| datapath | CARRY4 | LUTs | MUXF7 / MUXF8 |
|---|---|---|---|
| Verilog `a / b` (yosys's own) | 640 | 3601 | 1460 / 615 |
| restoring array, select left to ABC | 151 | 1273 | 159 / 44, some with constant inputs (`MUXF7 (.I0(1'h0), .I1(1'h0), ...)`) |
| restoring array, kept select, ABC for the divisor scan | 151 | 1086 | 6 / 3, constant inputs again |
| **as built** (digitdiv's `bdc_divui_32`, in the bench) | 151 | 1898 = 1112 array + 257 enable chain + 528 matched delay + 1 uor | 0 / 0 |

Routed (nextpnr's SLICE_LUTX cells under `bridge_i.udut.udivui0`, seeds 1-3 alike): 1866 datapath (array + enable
chain + the pass-through LUTs the packer adds in front of CARRY4 inputs) + 528 matched delay, 151 CARRY4. The whole
digitdiv kernel: 4363 SLICE_LUTX (818 of them matched delays), 161 CARRY4, 3 DSP48E1.

The MUXF7s with constant inputs are the GND-buffer F7 class fasm_equiv calls NOT EQUIVALENT, and the cell whose
constant select nextpnr once left unrouted (research/JOURNAL.md, session of 2026-10-29, "progress 21:18"; fixed since
by the const-sinks patch, but the class is still reported). The written-out array has none; all routes here are
EQUIVALENT.

**What the hardware returns where C has no answer** (fixed by the structure; bdc/test_compute.py checks each):

| op | x / 0 | INT_MIN / -1 |
|---|---|---|
| divui | all ones | - |
| remui | x | - |
| divsi | x < 0 ? 1 : -1 | INT_MIN |
| remsi | x | 0 |

Dynamatic's own units return the same at x / 0 for divui and divsi (simulated, section 3).

**Not fused.** `FUSABLE_OPS` excludes the dividers: a fused region writes each op as one expression, a divider is
~W*W/2 primitives, and its delay dwarfs what a region saves. A divider is one unit with its own link in front.

**Matched delay (placeholder).** `default_delay("div", W) = max(16, 2 * DIV_TAP * (W + 1))` links: 528 at 32 bits,
twice the enable chain (the two-fold headroom CELL_DELAY's note argues for).

## 3. Dynamatic's own dividers (dynamatic/data/verilog/arith/, read and simulated)

`divui.v`, `divsi.v`, `remsi.v`: a pipelined restoring divider (Vitis HLS's `udiv_32ns_32ns_32_36`, one registered
stage per quotient bit) behind a 34-deep `delay_buffer` and an `oehb`: **35 cycles** from operands to result
(iverilog, Dynamatic's own files, valid in -> valid out). x / 0: divui all ones, divsi -1 (x >= 0) / 1 (x < 0), remsi
x. **Dynamatic's Verilog `remsi` is an UNSIGNED remainder**: `remsi.v` (marked "translated from the VHDL file using
an AI tool") instantiates `dynamatic_units_urem_...` on the raw operands, with no sign handling (the VHDL `remsi.vhd`
has `sign_i` / `sign_o`). Simulated: remsi(-7, 2) = 1 (C: -1), remsi(7, -2) = 7 (C: 1), remsi(-7, -2) = -7 (C: -1),
remsi(INT_MIN, 3) = 2 (C: -2), remsi(-1, INT_MIN) = INT_MAX (C: -1); divsi is right on all of them. A Dynamatic figure
for a kernel with a signed `%` of a negative operand (path_profiling) is the figure of a circuit that answers wrong in
Dynamatic's Verilog flow (lead 8 should know). research/tools/suite/dynamatic_est.py models remsi with C's semantics.

## 4. Evidence

**Unit level.** `python3 bdc/test_compute.py`: 168 / 168 (width, op) pairs (the 140 before plus the 4 dividers at
widths 1, 2, 3, 5, 8, 16, 32: every pair up to 5 bits, edges plus 400 random above), against Verilog's `/` and `%`
where C defines them and the table above where it does not (each reference is in DIV_REF). Exhaustive, all four ops
at once, every (a, b) pair (iverilog, bd_prims_sim.v; scratch testbench, not committed): 8 bits 0 mismatches of
65536, 10 bits 0 of 1048576. Negative controls in the same harness: quotient bit 0 inverted, 65536 of 65536 pairs
wrong; the guard of the stage deciding quotient bit 2 dropped (`uq[2] = en & ~d5[6]`), 24960 of 65536 wrong.

**Kernels** (simcheck `--c-oracle --timeout-us 400`, pre-route Verilog, bd_prims_sim.v arc timing, expected values from
the C through research/tools/suite/oracle.sh, vectors through veclint.py), final design:

| kernel | ops | vectors | default | BDC_AUTO=1 |
|---|---|---|---|---|
| digitdiv | divui, muli | kernels/digitdiv/vec.hex (18) | PASS | PASS |
| digitsum (`BDC_FE_UREM=1`; its MLIR is digitdiv's) | divui, muli | kernels/digitsum/vec.hex (18, digitdiv's) | PASS | PASS |
| divmodu (new, `BDC_FE_UREM=1`) | divui, muli, subi | kernels/divmodu/vec.hex (20) | PASS | PASS |
| divmods (new) | divsi, remsi | kernels/divmods/vec.hex (24) | PASS | PASS |
| test_divui (Dynamatic's, `x / 1083`) | divui | research/data/suite/vec/test_divui.hex (12) | PASS | PASS |

(simcheck's PASS is every vector right and every channel's token count equal to the number of vectors.)
Negative controls (simcheck `--dut` on divmodu's generated Verilog, hand-corrupted, final design): quotient bit 0
inverted (`uq[0] = tp[256] & d31[32]`): FAIL 20 / 20 vectors; the guard of the stage deciding quotient bit 20
dropped (`uq[20] = tp[96] & ~d11[12]`): FAIL 9 / 20 (the vectors whose divisor is >= 2^12 and reach that case); the
same file uncorrupted: PASS.

**bdc output of the other fixtures**: `emit.py --no-top`, default and `BDC_AUTO=1`, on all 111 fixture directories:
the 90 outputs the starting commit (7197d85c2) emits are byte-identical (cmp), and again after rebasing onto
0cebd725c (hangs' token-floor modes): its 90 outputs byte-identical; digitdiv, digitsum, divmodu, divmods, test_divui
and if_loop_3 now emit (the division kernels' Verilog is the same before and after the rebase, so the routes below
stand for it); every other refusal is the same message as before.

**Routed: the ungated array cannot be simulated.** The first routes (digitdiv seeds 1 and 2, nextpnr
6e5d224472232d5d, default flow: smoke.sh = build_bench.sh BD_NO_TIGHTEN=1 BD_SIZES=none BD_DSP=1, --freq 83) placed
and routed in ~5 minutes each, but their full-stack gates never returned: after 60 minutes no batch had finished (both
stopped; these two routes are not among the results below). One vector
alone on seed 2's compiled simulation: the zero-trip vector (no divide) 51 s, `odata` right; the 9-trip vector did
not finish in 20 minutes, and with +TEND=2500 ns (barely past the first divide) not in 10. cells/gls/prims.v keeps
every pulse (wires and LUT pins are transport delays), and a ripple of 32 subtract-and-select stages multiplies them:
each of a stage's s+1 inputs arrives as its own wave, each wave can toggle the borrow and every select, and the next
stage receives all of them. On silicon such pulses die in the gates; this simulator, which the project means to be
the ground truth, keeps them, so a design it cannot run cannot be judged. Hence the enables. The ungated array's rule
A on seed 1 (tighten.py on the prjxray SDF collapsed to one corner): data peak 92.0 ns at the worst corner (chains
0.21, CARRY4 / F7F8 / FF 1, rest 0.288), 52.3 FAST_MIN, 138.7 SLOW_MAX; its 512-link placeholder 204.9 / 145.9 /
425.3 ns.

**Routed: the gated array** (same flow and toolchain; gate = research/tools/eventgraph/bench_gate.sh at worst, i.e.
the bits decoded back to a netlist, prjxray delays, chains 0.21, CARRY4 / F7F8 / FF 1, rest 0.288, + M scatter; 2 runs
per vector; expected values from the C):

| kernel | seed | sdf | gate at worst | bits | divider rule A, worst: peak / request (margin after guard) | FAST_MIN | SLOW_MAX |
|---|---|---|---|---|---|---|---|
| digitdiv | 1 | 2e0eec55 | PASS 18/18 | EQUIVALENT | 120.7 / 211.6 ns (+66.8) | 78.4 / 150.4 | 222.7 / 440.1 |
| digitdiv | 2 | 0eadc172 | PASS 18/18 | EQUIVALENT | 126.5 / 211.8 ns (+60.0) | 82.8 / 150.6 | 233.3 / 440.9 |
| digitdiv | 3 | 9827c736 | PASS 18/18 | EQUIVALENT | 117.0 / 217.0 ns (+76.6) | 76.0 / 154.5 | 216.3 / 450.8 |
| digitdiv | 4 | 2eee037f | PASS 18/18 | EQUIVALENT | 124.3 / 210.4 ns (+61.2) | 80.3 / 149.5 | 226.8 / 438.0 |

Over the 4 seeds: the gated divider's data peak at the worst corner 122.1 ns mean (117.0 - 126.5), FAST_MIN 79.4
(76.0 - 82.8), SLOW_MAX 224.8 (216.3 - 233.3); the 528-link request 212.7 (210.4 - 217.0); rule A's margin after its
guard +66.2 ns (+60.0 - +76.6); tighten.py would cut the line to 363.5 links (341 - 378) at the worst corner.

Per loop iteration at the worst corner, with the placeholder sizes (gate's BENCHRES, host cycles of 12 ns): the
32-trip call (0xffffffff, base 2) 754 / 763 / 777 / 761 cycles on seeds 1-4, a 1-trip call 29, so (754 - 29) / 31 =
23.4 cycles: 280.6, 284.1, 289.5, 283.4 ns an iteration, 284.4 mean. Not a speed result: every line is at its
placeholder.

| kernel | seed | sdf | gate at worst | bits | divider rule A, worst: peak / request (margin after guard) | FAST_MIN | SLOW_MAX |
|---|---|---|---|---|---|---|---|
| divmods (divsi / remsi) | 1 | 7767fe2c | PASS 24/24 | EQUIVALENT | divsi 128.4 / 206.5 (+52.4), remsi 127.2 / 210.1 (+57.4) | 83.7 / 146.7, 82.7 / 149.4 | 233.1 / 429.7, 234.7 / 436.7 |
| divmods | 2 | 1d4df430 | PASS 24/24 | EQUIVALENT | divsi 140.2 / 205.2 (+37.0), remsi 131.4 / 200.5 (+42.8) | 93.1 / 145.9, 86.1 / 142.1 | 253.6 / 426.6, 241.1 / 419.0 |
| divmods | 3 | cc887fb6 | PASS 24/24 | EQUIVALENT | divsi 134.0 / 210.0 (+49.2), remsi 126.9 / 207.5 (+55.2) | 87.8 / 149.5, 81.9 / 147.4 | 245.0 / 436.1, 235.9 / 432.1 |
| divmods | 4 | d6035f2b | PASS 24/24 | EQUIVALENT | divsi 132.6 / 216.7 (+57.6), remsi 126.4 / 205.3 (+53.7) | 86.8 / 154.2, 82.0 / 145.8 | 241.7 / 450.4, 233.6 / 427.5 |
| divmodu (divui, BDC_FE_UREM) | 1 | 4342e498 | PASS 20/20 | EQUIVALENT | 117.4 / 204.1 (+63.2) | 76.3 / 145.2 | 216.4 / 423.8 |
| divmodu | 2 | 3be8591e | PASS 20/20 | EQUIVALENT | 118.3 / 209.0 (+67.1) | 77.1 / 148.7 | 219.8 / 434.3 |
| divmodu | 3 | 41b3b9c8 | PASS 20/20 | EQUIVALENT | 114.5 / 210.0 (+72.6) | 74.4 / 149.5 | 213.3 / 436.2 |
| divmodu | 4 | 9d4f3060 | PASS 20/20 | EQUIVALENT | 114.2 / 208.7 (+71.6) | 74.3 / 148.6 | 211.0 / 433.1 |

Means over the 4 seeds (range): the signed units are slower (the magnitudes' and the result's negations, one more
enable stage): divsi's worst-corner peak 133.8 ns (128.4 - 140.2), FAST_MIN 87.8 (83.7 - 93.1), SLOW_MAX 243.3
(233.1 - 253.6), margin +49.0 (+37.0 - +57.6); remsi 128.0 (126.4 - 131.4), 83.2, 236.3, margin +52.3 (+42.8 -
+57.4). divmodu's divui: 116.1 (114.2 - 118.3), 75.5, 215.1, margin +68.6 (+63.2 - +72.6). Routed size (SLICE_LUTX under the unit, seed 1): divsi 2098 + 528 matched delay, remsi 2127 +
528, 175 CARRY4 each; divsi has 4 SELMUX2_1 (F7 muxes in the negation logic, left to ABC): every bitstream is
EQUIVALENT all the same. One delay-model draw (bench_gate.sh draw:10101: chains 0.2299, rest 0.2874, CARRY4 / F7F8 /
FF 0.5261, + M scatter) on digitdiv seed 1: PASS 18/18, EQUIVALENT.

**The automatic path (suite_one.sh digitdiv 1 2 2) did not finish and was stopped.** auto_size.sh's iteration 0
built (route su_digitdiv_1_0, BDC_AUTO=1, every line at 0.3 x its estimate, the divider at 159 links, ffmux clean),
and its rule (corner_audit CA_SIZERULE=1 at two corners) ran the base audits in ~7 min and then one sensitivity run
per delay line, 76 lines a corner, > 2 min each at CA_JOBS=1: hours per iteration, the slowness lead 2 is about. What
iteration 0 does show, from tighten.py rule A on that route: the divider's peak 117.3 ns at the worst corner against
a 63.8 ns request, margin -77.0 ns, "PAD to 355" (FAST_MIN: PAD to 323, SLOW_MAX: PAD to 313). The start is short, as
AUTO_START_SCALE makes every line, and the rule sees it; whether the loop converges and the draws pass is not known.
The command that resumes it is in the subagent's out/resume_auto.sh.

## 5. What this does not show

- **Silicon.** Nothing here ran on the board. The gate is the full-stack GLS at one corner (+ scatter), 4 routes a
  kernel, all at the placeholder sizes, one draw on one route.
- **Margins under the draws, or under the sizing rule.** The routes are at the placeholder (528 links, ~1.75x the
  gated peak at the worst corner); the automatic path's start (estimates x 0.3, 159 links) is below the peak, so the
  rule has to raise it: on iteration 0 it asks for 355 links; nothing after that was run.
- **The enables' effect on silicon.** They cost time (peak 92.0 -> 120.7 ns at the worst corner on seed 1) and 257
  LUTs; they make the GLS tractable and probably cut glitch power, but no board measurement says what the ungated
  array would have done there. DIV_TAP is a knob nobody has swept (6 might do; 8 was chosen from seed 1's per-stage
  average with ~1.2-1.5x room).
- **Divisor 0 and INT_MIN / -1** are UB in C, so no kernel vector reaches them; what the hardware returns there is
  checked at the unit level only (test_compute, exhaustive 8 / 10 bits).
- **if_loop_3, covariance, trisolv, path_profiling** (Dynamatic's tests with divsi / remsi) were not run: if_loop_3
  emits now but needs the memory bench; the other three stop at other blockers (lsq, a memref deeper than a bd_mem).
- **A remainder from the frontend costs a multiply.** With BDC_FE_UREM, `x % y` is `x - (x / y) * y`: a DSP
  multiply and a subtract after the divider on digitsum's loop. A remui unit (built, tested at unit level) would give
  it for free, but Dynamatic's dialect has no remui to carry it; recognising divui + muli + subi in bdc would.
- **Speed.** Restoring division is W carry chains in series. A radix-4 or carry-save array, or an iterative divider on
  a ring, would be faster or smaller; not tried.
