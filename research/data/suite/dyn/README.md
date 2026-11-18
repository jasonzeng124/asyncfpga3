# Dynamatic's integration tests through this compiler

PROGRAM.md, "A benchmark suite for the compiler": "Take Dynamatic's own integration tests too, the integer ones that
fit (`dynamatic/integration-test/`, sources only) ... Say which do not compile, and why." The 2026-11-17 triage
(subagent suitew) is kept below as the record. This first part is the state on 2026-11-18 (subagent dyntests): the
bench takes a void kernel, the nine tests the store lowering unlocked (research/data/suite/stores.md) and fourteen
more that a load-first controller unlocks (lowered here) are in the suite, and every integer test has one row.

## Every integer test, today

| test | status today | what blocks it | emits (default / AUTO) | in the suite | RTL default / AUTO | routed smoke (seed 1, worst corner) | note |
|---|---|---|---|---|---|---|---|
| atax | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| bicg | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| binary_search | **passes routed smoke** |  | ok / ok | yes | PASS 7/7 / PASS 7/7 | default seed 1: PASS 7/7, EQUIVALENT | LL across two loops: chained across them (one token per execution of each) it deadlocked; the chain is built within one block only |
| cnn | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| complexdiv | does not compile (frontend) | frontend | - / - | - | - / - | - |  |
| covariance | does not compile (bdc) | lsq, op:divsi | no / no | - | - / - | - |  |
| divergent_paths | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| external_integration | does not compile (frontend) | frontend | - / - | - | - / - | - |  |
| factorial | **passes RTL** |  | ok / ok | yes | PASS 12/12 / - | - |  |
| fir | **passes RTL** |  | ok / ok | yes | PASS 2/2 / - | - |  |
| gaussian | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| gcd | in the suite |  | ok / ok | yes | - / - | - | one of the six original kernels: routed and drawn many times (research/data/suite/README.md); not rerun here |
| gemver | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| if_convert | **passes RTL** |  | ok / ok | yes | PASS 5/5 / - | - |  |
| if_loop_1 | **passes RTL** |  | ok / ok | yes | PASS 8/8 / - | - |  |
| if_loop_2 | **passes RTL** |  | ok / ok | yes | PASS 8/8 / - | - |  |
| if_loop_3 | does not compile (bdc) | op:divsi | no / no | - | - / - | - |  |
| iir | **passes RTL** |  | ok / ok | yes | PASS 3/3 / - | - |  |
| image_resize | **passes RTL** |  | ok / ok | yes | PASS 4/4 / - | - |  |
| insertion_sort | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| iterative_division | **passes RTL** |  | ok / ok | yes | PASS 15/15 / - | - |  |
| iterative_sqrt | **passes RTL** |  | ok / ok | yes | PASS 12/12 / - | auto path seed 1: not finished (kernels/SUITE.md) |  |
| jacobi_1d_imper | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| kernel_2mm | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| kernel_3mm | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| kmp | does not compile (bdc) | lsq, mc:>2 | no / no | - | - / - | - |  |
| loop_array | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| loop_path | **passes RTL** |  | ok / ok | yes | PASS 4/4 / - | - |  |
| matrix | emits |  | ok / ok | - | - / - | - | NOT in the suite: does not fit the gate (27000 multiply-adds + 5400 host words per call: hours of wall per call); default flow deadlocks in RTL, BDC_AUTO=1 passes (research/data/suite/stores.md) |
| matrix_power | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| matvec | does not compile (bdc) | mem>1024 | no / no | - | - / - | - |  |
| mul_example | **passes routed smoke** |  | ok / ok | yes | PASS 3/3 / PASS 3/3 | default seed 1: PASS 3/3, EQUIVALENT |  |
| nested_conditionals_1 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| nested_conditionals_2 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| nested_loop | **passes RTL** |  | ok / ok | yes | PASS 4/4 / - | - |  |
| path_profiling | does not compile (bdc) | lsq, op:remsi | no / no | - | - / - | - |  |
| pivot | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| polyn_mult | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| simple_example_1 | **passes routed smoke** |  | ok / ok | yes | PASS 4/4 / - | default seed 1: PASS 4/4, EQUIVALENT |  |
| single_loop | **passes RTL** |  | ok / ok | yes | PASS 5/5 / - | - |  |
| sobel | in the suite |  | ok / ok | yes | FAIL 0/3 / - | - | deadlocks in RTL in both flows (with or without the load chain or the capture latch): not explained |
| spmv | **passes routed smoke** |  | ok / ok | yes | FAIL 3/4 / - | auto seed 1: PASS 4/4, EQUIVALENT | default flow deadlocks on 1 of 4 vectors (RTL); BDC_AUTO=1 passes 4/4: the routed smoke is BDC_AUTO's emission |
| stencil_2d | **passes routed smoke** |  | ok / ok | yes | FAIL 0/4 / - | auto seed 1: PASS 1/1, EQUIVALENT | default flow deadlocks (RTL, every call); BDC_AUTO=1 passes: the routed smoke is BDC_AUTO's emission |
| sumi3_mem | **passes RTL** |  | ok / ok | yes | PASS 3/3 / - | - |  |
| test_bitint | **passes routed smoke** |  | ok / ok | yes | PASS 6/6 / - | auto path seed 1: PASS 2/2 draws (kernels/SUITE.md, nextpnr 9c732bc6303458df) |  |
| test_bool_array | **passes routed smoke** |  | ok / ok | yes | PASS 4/4 / PASS 4/4 | default seed 1: PASS 4/4, EQUIVALENT | LL in one block: with the two loads unchained (they tie at bd_arbiter) the routed smoke FAILED 1/4 (seed 1, build 447257a8); chained since |
| test_divui | does not compile (bdc) | op:divui | no / no | - | - / - | - |  |
| test_int16 | **passes routed smoke** |  | ok / ok | yes | PASS 1/1 / - | auto path seed 1: PASS 2/2 draws (research/data/suite/srcjoin.md) |  |
| test_loop_free | **passes routed smoke** |  | ok / ok | yes | PASS 10/10 / - | auto path seed 1: PASS 2/2 draws (kernels/SUITE.md, nextpnr 9c732bc6303458df) |  |
| test_stdint | **passes RTL** |  | ok / ok | yes | PASS 4/4 / - | - | an int8_t scalar: the bench now takes a narrow argument (one word's low bits) |
| threshold | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| triangular | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| trisolv | does not compile (bdc) | lsq, mem>1024, op:divsi | no / no | - | - / - | - |  |
| unused_arg | **passes routed smoke** |  | ok / ok | yes | PASS 6/6 / - | auto path seed 1: PASS 2/2 draws (research/data/suite/srcjoin.md) |  |
| vector_rescale | **passes RTL** |  | ok / ok | yes | PASS 4/4 / - | - |  |
| video_filter | **passes RTL** |  | ok / ok | yes | PASS 3/3 / - | - |  |
| while_loop_1 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| while_loop_2 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| while_loop_3 | **passes RTL** |  | ok / ok | yes | PASS 7/7 / - | - | RTL also on 4 edges with 46340 trips (while_loop_3_rtl.hex): not run (hours in RTL) |
| wrap_if | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| memory/test_constant_array | does not compile (bdc) | ram | no / no | - | - / - | - |  |
| memory/test_flatten_array | **passes RTL** |  | ok / ok | yes | PASS 2/2 / - | default seed 1: PASS 1/1, NOT EQUIVALENT | the route's bits are NOT EQUIVALENT to nextpnr's netlist (16 F7 muxes in the kernel's shifter not configured): reported, not judged |
| memory/test_internal_array | does not compile (bdc) | ram | no / no | - | - / - | - |  |
| memory/test_memory_1 | **passes routed smoke** |  | ok / ok | yes | PASS 6/6 / PASS 6/6 | default seed 1: PASS 6/6, EQUIVALENT |  |
| memory/test_memory_10 | does not compile (bdc) | mc:>2 | no / no | - | - / - | - |  |
| memory/test_memory_11 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| memory/test_memory_12 | does not compile (bdc) | mc:>2, mc:store | no / no | - | - / - | - |  |
| memory/test_memory_13 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| memory/test_memory_14 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| memory/test_memory_15 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| memory/test_memory_16 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| memory/test_memory_17 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| memory/test_memory_18 | does not compile (bdc) | mc:>2 | no / no | - | - / - | - |  |
| memory/test_memory_2 | **passes routed smoke** |  | ok / ok | yes | PASS 7/7 / PASS 7/7 | default seed 1: PASS 7/7, EQUIVALENT |  |
| memory/test_memory_3 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| memory/test_memory_4 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| memory/test_memory_5 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| memory/test_memory_6 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| memory/test_memory_7 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| memory/test_memory_8 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| memory/test_memory_9 | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| memory/test_smallbound | does not compile (bdc) | lsq | no / no | - | - / - | - |  |
| memory/test_unroll | does not compile (bdc) | ram | no / no | - | - / - | - |  |
| sharing/share_test_1 | **passes RTL** |  | ok / ok | yes | PASS 3/3 / - | - |  |
| sharing/share_test_2 | **passes RTL** |  | ok / ok | yes | PASS 3/3 / - | default seed 1: NOT-JUDGED decoder-refused: | no defined input in C (signed overflow in its own constants): expected values are -fwrapv's |

How to read it. *does not compile*: the frontend fails, or bdc refuses (every refusal is listed: `lsq` a load-store
queue, `mc:store` a store that is not its controller's last accessor, `mc:>2` more than two accessors on one
controller, `ram` an internal array, `op:<name>` an op with no lowering, `mem>1024` a memref deeper than one bd_mem).
*emits*: `bdc/emit.py --no-top` writes Verilog in that mode (default flow / `BDC_AUTO=1`); nothing more is claimed.
*in the suite*: research/tools/suite/kernels.txt, C in research/data/suite/dynsrc/, vectors from that C. *RTL*:
research/tools/suite/rtl_bench.sh (below): the bench's own generated Verilog, cells/sim's primitive models at 350 ps
per arc, the gate's PS model and verdict -- functional evidence only, no route. *routed smoke*: one route, seed 1, the
default flow's build (`BD_NO_TIGHTEN=1 BD_SIZES=none BD_DSP=1`, `--freq 83`, `--host-mem`; `_auto`: the same with
`BDC_AUTO=1`'s emission), judged by `research/tools/eventgraph/bench_gate.sh ... worst` (netlist decoded from the .bit,
prjxray SDF, chains 0.21, CARRY4/F7F8/FF/RAMB18E1 1, rest 0.288, + M scatter) with every array read back after every
call against the C, `GATE_ANNOTATE=1` and the ports' one-hot monitor. nextpnr 6e5d224472232d5d for every route here
(cells/verify/toolchain.sh all ok). One route at one corner is a smoke test, not a result (CLAUDE.md: 4 seeds).

**85 integer tests: does not compile (bdc) 48, passes RTL 20, passes routed smoke 12, does not compile (frontend) 2, in the suite 2, emits 1**

## 1. A void kernel on the bench

Most of Dynamatic's array tests return nothing; gen_bench.py captured a run on out0 only and refused them, and
oracle_mem.sh refused them too. Now (cells/hw/gen_bench.py `void_completion_lines`):

- **Completion.** A kernel with no out0 and at least one memory completes a call when every control result has
  arrived: `end` and each memory's `<m>_end` (its mem_controller's memEnd), as Dynamatic's own testbench takes all of a
  kernel's outputs together (hls-verifier's `join_valids`, research/data/suite/srcjoin.md). Their C-element join
  (`bd_join`) is the bench's o_req, so the batch FSM, the latency counters and the return to zero are those of an out0;
  ODATA reads 0 and the result is the arrays, read back through the host port after the batch.
- **Why memEnd is the completion.** For a memory with a store, bdc orders its ctrlEnd after every store of the call
  (stores.md section 2), and memEnd waits for ctrlEnd: a run is not complete -- the host does not read back, nor start
  the next run -- before the last store has reached the RAM.
- **Why `end` goes through a one-token link.** In bdc's lowering `end` is the start token passed straight through
  (`end ... %0#1`: the start fork's other outputs start the loop). A join acknowledges only when the call is over, and
  bd_fork acknowledges only when every output has, so `end` straight into the join would hold the start fork's request
  high until the call ends: the loop header could not return to zero, the deadlock stores.md measured inside the
  kernel. `bd_link #(.W(1))` acknowledges at once and holds the token for the join -- the same bd_link + bd_join pair
  bdc builds for a memory's memStart. No new cell.
- **The oracle** (research/tools/suite/oracle_mem.sh) calls a void kernel for its arrays and prints `void` per call;
  `ORACLE_MEMOUT` has the arrays. Arrays of more than one dimension (matrix, test_flatten_array, image_resize,
  video_filter: `int a[R][C]`) are held flattened, row-major, as the frontend's memref<R*C> is. `ORACLE_UBCHECK=1`
  builds the same C without `-fwrapv` under UBSan + ASan, to check that a vector file stays inside the C's defined
  behaviour (it fails, as it should, on single_loop with no exit before a[1000], if_convert reaching b[200], and
  stencil_2d at 15447: overflow).
- **The gate** (research/tools/eventgraph/bench_gate.sh): a `void` call passes only if GATE_MEMEXP held its arrays and
  they matched; without GATE_MEMEXP the verdict says "nothing checked, no pass".
- **Byte-identity.** Every bench file gen_bench.py wrote before for the 108 fixtures in build/frontend (`K --top
  K_bench_gen`, `K` with the default top, `K --null`: 130 files over 51 kernels, each kernel's `build/gen/K_kernel_bench.v`
  present, as the build has it) is `cmp`-identical after this change and after the narrow-argument change (section 4);
  the six original kernels and every suite kernel are among them. oracle_mem.sh's output and ORACLE_MEMOUT are
  byte-identical on the 11 existing v2 vector files (ORACLE_RUNS=2); memvec.py (new: per-element overrides
  `SPEC@I=V`) reproduces 7 existing vector files byte for byte.

## 2. The nine store tests

C copied byte for byte into research/data/suite/dynsrc/ (sha256 in its README), vectors written by
research/tools/suite/dyn_vecs.sh from domains read off each C (every written array filled with values the kernel does
not write, so a missing store shows on read-back; every file passes ORACLE_UBCHECK), expected values from the C.

- **All nine emit in all three modes. Eight ran in RTL here (default flow, 350 ps per arc, every call of the full
  vector set): seven pass** (if_convert 5/5, loop_path 4/4, nested_loop 4/4, simple_example_1 4/4, single_loop 5/5,
  test_flatten_array 2/2, while_loop_3 7/7). **stencil_2d deadlocks in the default flow** (every call: the batch FSM
  waits in S_WAIT_RES and nothing moves) **and passes with `BDC_AUTO=1`** -- the triple-nest class stores.md recorded
  for `matrix` and kernels/SUITE.md for nest3, the hangs lead's work, not the store lowering's. `matrix` was not rerun
  here (stores.md: the default flow deadlocks, `BDC_AUTO=1` returns outC 900 / 900 = C).
- **Eight of the nine are in the suite** (kernels.txt). **`matrix` is not: it does not fit the gate** -- 27000
  multiply-adds and 5400 host words per call (fill and read-back of three 900-word arrays), several hours of the
  decoded-netlist gate's wall per call at the measured speed (below); vectors exist (vec/matrix.hex, matrix_rtl.hex).
- **The gate's cost is the host port, not the kernel.** Measured on these routes: ~1250 s of wall for simple_example_1's
  4 calls x 300 host accesses (fill, +MEMCHECK read-back, read-back), i.e. about 0.24 us of circuit time per second of
  wall, ~14 min per 1000 host words. So the vector files of the large-array kernels keep 1-3 calls (`<name>.hex`, what
  the suite gates) and every call stays in `<name>_rtl.hex` (rtl_bench.sh): single_loop, loop_path, nested_loop
  (3 x 1000 words) ~85 min for one call; stencil_2d (1810 words) ~50 min; test_flatten_array (1024 words) 53 min
  measured; if_convert (400 words) 3 calls ~40 min.
- **Negative controls (RTL):** `BDC_MEM_NEG_STORE=addr` and `=data` (every store's address / data bit 0 flipped,
  stores.md's switch) on four void kernels: simple_example_1 0/4, while_loop_3 0/7, if_convert 0/3, test_memory_1
  2/6 (the two calls that store nothing pass) -- in every case "MEMORY wrong" on exactly the calls that store: the
  void bench judges the arrays and cannot pass on a missing or misplaced store.

## 3. A load first on one controller (`mc:load1st`)

Two accessors on one controller, a load first (LS: a load then a store on one array; LL: two loads), were refused:
the program-order token chain (`prev.z -> next.c`, bdc/mem.py) took the first accessor's z, which only a store
leaves free. stores.md section 6 named what LS needs and one hazard to settle first. Done here
(bdc/emit.py `_resolve_mem_accessors`, `_op_load`, `_op_mem_controller`; bdc/mem.py `CAPTURE`, `_emit_port_arb_host`):

- **The token.** The first load's z is forked (`bd_fork #(.N(2))`): its consumer and the second accessor's `c` both
  get the request, and the load sees the C-element of both acknowledges, so its operands are not released before the
  second accessor has taken its token. **Only when both accessors are in one basic block**: the chain pairs the k-th
  execution of one with the k-th of the other, which is program order only if both run once per execution of one
  block. Across blocks it deadlocks -- measured: binary_search (a load in each of two loops) hung on every vector until
  the chain was restricted. There, as in Dynamatic's own mem_controller (an arbiter, no order), the dataflow orders
  the two accessors and nothing else; both stations are plain. Cross-iteration order (a load of iteration k+1 after the
  store of iteration k) is stores.md's argument, unchanged: execution k+1 of a block starts from the block's control
  token of execution k, which waits for every store of execution k.
- **The hazard: the load's word is captured.** `z_data = p_rdata` is the RAM's DOADO itself, and bdc's sender rule is
  that data holds from the request's rise to the acknowledge's FALL (a consumer's latch is transparent until then). A
  lone station keeps that: its next access waits for its operands, which `hold` releases only once z_ack has fallen.
  A second station on the same port does not wait for this one's consumer -- the arbiter hands it the RAM as soon as
  this station's claim drops at `done` -- and its edge rewrites DOADO (a store: WRITE_FIRST returns the word it wrote).
  So every load on an arbitrated port is `bdc_load_cap_*`: the word goes through a bd_latch open while `~done & ~z_ack`
  (one LUT2 and W/2 LUT6_2): it closes when the RAM answered and reopens once the consumer's handshake is over. What it
  rests on, by construction and both in the safe direction: it closes two arcs after p_ack, which rule C places after
  DOADO is valid; the next RAM edge needs this claim to fall, the arbiter to hand over, the other station's DSETUP and
  the RAM's clock-to-out. The data path gains one latch arc after DOADO against z_req's one arc after p_ack: rule C's
  margin must cover it (measured margins 665-3194 ps, bench/README.md).
- **Checked, at the station** (research/tools/suite/tb_capture.v, RTL, 350 ps per arc): station A loads address 3
  (X); its consumer reads z_data only after HOLD_NS; inside that window station B stores Y at address 5. With the
  capture: X at HOLD_NS = 30 and 2. **Without it (the plain station, the negative control): Y at HOLD_NS = 30**
  (`bad00bad`), X at 2 -- a race, and the latch removes it. `BDC_MEM_NOCAP=1` emits a kernel without the latch.
- **The capture needs DCO >= clock-to-out, and cells/sim's RAM model breaks that at zero wire delay.** bd_mem's
  placeholder DCO is 12 LUT arcs, 1.5 ns at cells/sim's 124 ps, against the RAMB18E1 model's 2.454 ns clock-to-out
  (stores.md saw the same reading the host's data). A transparent consumer hid it; the capture latch freezes the
  previous word: test_memory_1 / test_memory_2 / binary_search / mul_example failed at 0 ps per arc and pass at 350
  (rule C's condition, which every route here meets by a wide margin; see section 5). Every RTL figure in the table is
  at 350 ps per arc (`RTL_ROUTE_PS`, cells/sim's own BD_ROUTE_PS: "a plausible hop time").
- **The bench's host slot on an arbitrated port.** `--host-mem` refused a third slot on bd_arbiter's two. The slot now
  stands OUTSIDE the arbiter (`bdc_memport_arb_host_*`): ORed into the RAM request after it, with the RAM's
  acknowledge split by a phase bit (the station's own `hold` C-element: rises with the host request, falls once the
  RAM has reset), so the arbiter never sees an acknowledge it did not ask for. Its obligation is the plain port's on one
  slot (never live while a kernel slot is; the bench keeps it: host accesses only between calls): the port checks it in
  simulation, and cells/gls/ps/gen_memport_mon.py now checks it on the routed netlist (host slot against either kernel
  slot; the kernel slots may contend, that is the arbiter's job).
- **Byte-identity.** `emit.py --no-top` on every fixture in build/frontend (108) in three modes (default, BDC_AUTO=1,
  BDC_HOST_MEM=1): all 135 outputs that emitted before are `cmp`-identical; every fixture that still fails keeps its
  first error message; 14 tests now emit in all three modes (42 new outputs): binary_search, iir, image_resize,
  mul_example, share_test_1, share_test_2, sobel, spmv, test_bool_array, test_memory_1, test_memory_2, test_stdint,
  vector_rescale, video_filter. research/tools/suite/dyn_blockers.py: `mc:load1st` is no longer a blocker (the shape
  column keeps LS / LL); on the 108 fixtures, the 59 with no blocker are exactly the 59 that emit.

- **Two loads**: chained like LS when they are in one block (test_bool_array, spmv's row[i] and row[i+1], sobel's two
  loads of in[x]), never across blocks (binary_search, share_test_1). Nothing two loads read changes, so the chain is
  not there for order: unchained, the two requests of one block come from one fork and tie at bd_arbiter on every
  execution, the runt case its header names (metastability not excluded, rate unmeasured). **Measured: test_bool_array
  with the loads unchained, routed seed 1, worst corner: FAIL 1/4** (one call's two runs returned different results,
  two calls' arrays read back wrong, one fill counted 4 host accesses for 2; bits EQUIVALENT, 0 one-hot overlaps), where
  RTL passed 4/4. Not proven to be the arbiter (no waveform was taken); with the chain the two requests are sequential
  by construction and the question does not arise.
- **RTL, all 14** (table below; default flow at 350 ps per arc, in-place kernels one run per call): the LS kernels
  test_memory_1 (6/6), test_memory_2 (7/7), mul_example (3/3), share_test_2 (3/3), test_stdint (4/4), image_resize,
  vector_rescale, video_filter, iir and the LL ones test_bool_array (4/4), binary_search (7/7), share_test_1 pass.
  **spmv deadlocks in the default flow on its first vector** (n = 10, every row 0-2 entries; the three others pass)
  **and passes all 4 with `BDC_AUTO=1`**; the same with the chain, without it, and without the capture: a storage
  deadlock of the default flow (the hangs lead), not this lowering. **sobel deadlocks in both flows** (every call; the
  same with the loads chained or not and with or without the capture latch): not explained here (a 4-deep nest with a
  branch around the inner two loops); it stays in the suite, marked.
- **At zero wire delay the RTL failed** on test_memory_1 (3/6), test_memory_2 (3/7), mul_example (0/3): cells/sim's
  DCO (12 x 124 ps) is shorter than its RAM model's clock-to-out (2.454 ns), so the capture latch froze the previous
  word -- the condition rule C exists for. Every route here has DCO well above clock-to-out (the gates pass); in RTL it
  needs a plausible hop (350 ps).

## 4. A scalar narrower than 32 bits (test_stdint)

`test_stdint(int8_t a[100], int8_t b)`: gen_bench.py asserted that every scalar was a multiple of 32 bits. A narrower
one now takes one operand word's low bits (as an array element narrower than 32 bits already did); memvec.py and
oracle_mem.sh count it as one word (oracle_mem.sh casts the word to the C type). Byte-identity as in section 1.

## 5. Routed smokes (seed 1, worst corner) and the RTL runs

Builds: `cells/hw/build_bench.sh K` with `BD_NO_TIGHTEN=1 BD_SIZES=none BD_DSP=1 NEXTPNR_SEED=1` (`--freq 83`,
`--host-mem`), each in a private copy of the clone's tree (`_auto`: with `BDC_AUTO=1`, emission only, no sizing loop:
the kernels that deadlock in the default flow). Gate: `bench_gate.sh ... worst` with `GATE_MEMEXP` (oracle_mem.sh's
ORACLE_MEMOUT: every array read back after every call), `GATE_ANNOTATE=1`, `PS_MON_GEN=cells/gls/ps/gen_memport_mon.py`,
`GATE_NRUNS` 1 for in-place kernels, else 2; the vectors are the suite's `vec/<name>.hex` (the gate files). nextpnr
6e5d224472232d5d (toolchain.sh all ok); every route met `--freq 83` (Fmax below is the bench clock's).

| kernel | flow | seed | Fmax (MHz) | .bit md5 | LUTs (bench) | gate, worst corner | wall (s) |
|---|---|---|---|---|---|---|---|
| binary_search | default | 1 | 116.33 | d97c1cb0 | 5553 | PASS 7/7 cycles 7532 VERDICT: EQUIVALENT  \| annotate DONE sdf-warn/err 0 \| memport one-hot: 7 batch line(s), host reqs 1313, kernel reqs 1088, overlaps 0 | 2196 |
| mul_example | default | 1 | 114.67 | 52993095 | 4036 | PASS 3/3 cycles 2820 VERDICT: EQUIVALENT  \| void: arrays only \| annotate DONE sdf-warn/err 0 \| memport one-hot: 3 batch line(s), host reqs 500, kernel reqs 600, overlaps 0 | 1347 |
| share_test_2 | default | 1 | 84.32 | 2923e64f | 7750 | NOT-JUDGED decoder-refused: fasm2net (the gate's bitstream decoder) refuses a DSP48E1 configuration it does not model (B_INPUT=CASCADE, USE_DPORT=TRUE, INMODE=00100: yosys's pre-adder / cascade use for share_test_2's multiplies); no gate ran | 0 |
| simple_example_1 | default | 1 | 113.34 | 527e6eca | 3591 | PASS 4/4 cycles 88 VERDICT: EQUIVALENT  \| void: arrays only \| annotate DONE sdf-warn/err 0 \| memport one-hot: 4 batch line(s), host reqs 1100, kernel reqs 8, overlaps 0 | 1251 |
| spmv | auto | 1 | 100.69 | 64dc0da7 | 7436 | PASS 4/4 cycles 864 VERDICT: EQUIVALENT  \| annotate DONE sdf-warn/err 0 \| memport one-hot: 20 batch line(s), host reqs 357, kernel reqs 300, overlaps 0 | 1312 |
| stencil_2d | auto | 1 | 99.33 | 731b66ec | 6363 | PASS 1/1 cycles 4420 VERDICT: EQUIVALENT  \| annotate DONE sdf-warn/err 0 \| memport one-hot: 3 batch line(s), host reqs 1810, kernel reqs 1064, overlaps 0 | 4110 |
| test_bool_array | default | 1 | 101.98 | 5f16960b | 3674 | PASS 4/4 cycles 104 VERDICT: EQUIVALENT  \| annotate DONE sdf-warn/err 0 \| memport one-hot: 4 batch line(s), host reqs 14, kernel reqs 16, overlaps 0 | 387 |
| test_flatten_array | default | 1 | 103.16 | 4772e0fa | 7053 | PASS 1/1 cycles 9394 VERDICT: NOT EQUIVALENT \| void: arrays only \| annotate DONE sdf-warn/err 0 \| memport one-hot: 2 batch line(s), host reqs 1024, kernel reqs 2048, overlaps 0 | 3159 |
| test_memory_1 | default | 1 | 107.71 | 45868bb0 | 4486 | PASS 6/6 cycles 136 VERDICT: EQUIVALENT  \| void: arrays only \| annotate DONE sdf-warn/err 0 \| memport one-hot: 6 batch line(s), host reqs 44, kernel reqs 24, overlaps 0 | 430 |
| test_memory_2 | default | 1 | 108.47 | 8fab6141 | 4554 | PASS 7/7 cycles 179 VERDICT: EQUIVALENT  \| void: arrays only \| annotate DONE sdf-warn/err 0 \| memport one-hot: 7 batch line(s), host reqs 65, kernel reqs 26, overlaps 0 | 683 |

`EQUIVALENT`: the netlist decoded from the .bit matches nextpnr's (fasm_equiv). **test_flatten_array's route is NOT
EQUIVALENT** -- 16 F7AMUX/F7BMUX cells with loads in nextpnr's JSON that the bits do not configure, all in the
kernel's shifter `ushli3`, and 5 nets whose pips differ (BYP inputs); the gate passed on the decoded netlist (what the
board would run), but by the suite's rule such a route is reported, not judged. Not investigated
(out/evidence/test_flatten_array_s1_equiv.txt); the const-sinks patch's class (F7/F8 selects) is the first suspect.
`host reqs` / `kernel reqs`: the one-hot monitor's counts of slot requests on the routed netlist; `overlaps 0`: the
host slot never requested while a kernel slot did (on an arbitrated port: against either kernel slot).

RTL runs (research/tools/suite/rtl_bench.sh: the generated bench and kernel, cells/rtl over cells/sim at 350 ps per
arc, ps7_bench.v, the gate's verdict; the full vector sets, `<name>_rtl.hex` where it exists):

| kernel | flow | runs per call | vectors | verdict | wall (s) |
|---|---|---|---|---|---|
| binary_search | auto | 2 | binary_search.hex | PASS 7/7 cycles 6314 | 4 |
| binary_search | default | 2 | binary_search.hex | PASS 7/7 cycles 7686 | 3 |
| factorial | default | 2 | factorial.hex | PASS 12/12 cycles 742 | 3 |
| fir | default | 2 | fir.hex | PASS 2/2 cycles 29904 | 42 |
| if_convert | default | 2 | if_convert_rtl.hex | PASS 5/5 cycles 17708 \| void: arrays only | 29 |
| if_loop_1 | default | 2 | if_loop_1.hex | PASS 8/8 cycles 7602 | 12 |
| if_loop_2 | default | 2 | if_loop_2.hex | PASS 8/8 cycles 6098 | 7 |
| iir | default | 2 | iir_rtl.hex | PASS 3/3 cycles 67332 | 180 |
| image_resize | default | 1 | image_resize_rtl.hex | PASS 4/4 cycles 43172 \| void: arrays only | 125 |
| iterative_division | default | 2 | iterative_division.hex | PASS 15/15 cycles 11700 | 9 |
| iterative_sqrt | default | 2 | iterative_sqrt.hex | PASS 12/12 cycles 2956 | 8 |
| loop_path | default | 2 | loop_path_rtl.hex | PASS 4/4 cycles 27134 \| void: arrays only | 78 |
| mul_example | auto | 1 | mul_example.hex | PASS 3/3 cycles 2943 \| void: arrays only | 6 |
| mul_example | default | 1 | mul_example.hex | PASS 3/3 cycles 3132 \| void: arrays only | 8 |
| nested_loop | default | 2 | nested_loop_rtl.hex | PASS 4/4 cycles 25582 \| void: arrays only | 45 |
| share_test_1 | default | 2 | share_test_1_rtl.hex | PASS 3/3 cycles 104130 | 227 |
| share_test_2 | default | 1 | share_test_2.hex | PASS 3/3 cycles 7350 \| void: arrays only | 40 |
| simple_example_1 | default | 2 | simple_example_1.hex | PASS 4/4 cycles 88 \| void: arrays only | 2 |
| single_loop | default | 2 | single_loop_rtl.hex | PASS 5/5 cycles 24020 \| void: arrays only | 20 |
| sobel | default | 2 | sobel.hex | FAIL 0/3 cycles 0 \| MEMORY wrong in batch(es) 0,1,2 | 14 |
| spmv | default | 2 | spmv.hex | FAIL 3/4 cycles 644 \| MEMORY wrong in batch(es) 0 | 8 |
| stencil_2d | default | 2 | stencil_2d_rtl.hex | FAIL 0/4 cycles 0 \| MEMORY wrong in batch(es) 0,1,2,3 | 13 |
| sumi3_mem | default | 2 | sumi3_mem.hex | PASS 3/3 cycles 54810 | 187 |
| test_bitint | default | 2 | test_bitint.hex | PASS 6/6 cycles 816 | 2 |
| test_bool_array | auto | 2 | test_bool_array.hex | PASS 4/4 cycles 112 | 1 |
| test_bool_array | default | 2 | test_bool_array.hex | PASS 4/4 cycles 112 | 0 |
| test_flatten_array | default | 2 | test_flatten_array_rtl.hex | PASS 2/2 cycles 19000 \| void: arrays only | 46 |
| test_int16 | default | 2 | test_int16.hex | PASS 1/1 cycles 20 | 1 |
| test_loop_free | default | 2 | test_loop_free.hex | PASS 10/10 cycles 270 | 1 |
| test_memory_1 | auto | 1 | test_memory_1.hex | PASS 6/6 cycles 133 \| void: arrays only | 2 |
| test_memory_1 | default | 1 | test_memory_1.hex | PASS 6/6 cycles 140 \| void: arrays only | 1 |
| test_memory_2 | auto | 1 | test_memory_2.hex | PASS 7/7 cycles 168 \| void: arrays only | 1 |
| test_memory_2 | default | 1 | test_memory_2.hex | PASS 7/7 cycles 179 \| void: arrays only | 1 |
| test_stdint | default | 1 | test_stdint.hex | PASS 4/4 cycles 2912 \| void: arrays only | 3 |
| unused_arg | default | 2 | unused_arg.hex | PASS 6/6 cycles 120 | 1 |
| vector_rescale | default | 1 | vector_rescale_rtl.hex | PASS 4/4 cycles 31668 \| void: arrays only | 22 |
| video_filter | default | 1 | video_filter_rtl.hex | PASS 3/3 cycles 42621 \| void: arrays only | 422 |
| while_loop_3 | default | 2 | while_loop_3.hex | PASS 7/7 cycles 983 \| void: arrays only | 3 |

## What this does not show

- **One route per kernel, seed 1, one corner (worst), no draws, no board.** CLAUDE.md asks for four seeds for any
  routed claim; these are smoke tests. No max / min corner. The automatic path (`suite_one.sh`: BDC_AUTO=1 with the
  sizing loop and draws) was not run on any of the new kernels; `_auto` routes are BDC_AUTO's emission at the default
  flow's build flags, unsized.
- **RTL is functional evidence only** (cell arcs plus a uniform 350 ps per arc, no route). It found the deadlocks and
  the zero-delay capture artefact; it cannot show bundling margins.
- **The capture latch's timing is argued, not audited by a rule of its own.** It needs DCO above the RAM's
  clock-to-out plus one latch arc (rule C's condition) and the next RAM edge after the latch closed (by construction
  through the arbiter, DSETUP and clock-to-out). The routed gates passed with bd_mem's placeholder DSETUP 8 / DCO 12;
  nothing here sizes them, and `BD_NO_TIGHTEN=1` routes do not run rule C.
- **Program order across iterations for LS is stores.md's argument**, unchanged (a load of iteration k+1 after the
  store of iteration k because the block's control token waits for the store); no kernel here has a load that reads
  what the previous iteration's store on the same controller wrote (Dynamatic puts an LSQ there).
- **The bench's host slot outside the arbiter** rests on the bench never accessing memory during a batch; the
  monitor checked it on every routed run here (0 overlaps), its own negative control (`+MEMPORTMON_FORCE`) was not run
  on an arbitrated port.
- **Vectors** are written from each C's domain (edges, Dynamatic's own main where it is defined, seeded random), not
  exhaustive; `share_test_2` has no defined input at all (signed overflow in its constants): its expected values are
  `-fwrapv`'s. In-place kernels are judged with one run per call; suite_one.sh runs two and now gives the oracle the
  same count (wrapping arithmetic on the second run).
- **Not investigated:** sobel's deadlock (both flows), spmv's and stencil_2d's in the default flow (the hangs lead),
  test_flatten_array's NOT EQUIVALENT bits.
- **Dynamatic's own figures** for these tests: none obtained.

## Reproduce

    ln -sfn $HOME/dynamatic dynamatic                                   # in a clone; never commit the link
    research/tools/suite/dyn_vecs.sh                                    # every vector file of section 2 and 3
    ORACLE_UBCHECK=1 ORACLE_RUNS=1 research/tools/suite/oracle_mem.sh K research/data/suite/vec/K.hex   # defined?
    RTL_ROUTE_PS=350 GATE_NRUNS=1 research/tools/suite/rtl_bench.sh K VEC EXP WORK MEMEXP                # RTL
    python3 research/tools/suite/dyn_blockers.py research/data/suite/dyn/blockers.tsv $(ls build/frontend)
    python3 research/tools/suite/dyn_status.py research/data/suite/dyn/status.tsv > table.md
    # the station's hazard and its negative control (python3 -c ... mem.emit_unit / emit_port into units.v):
    iverilog -g2012 -gspecify -Wno-timescale -DBD_ROUTE_PS=350 [-DCAP] cells/sim/bd_prims_sim.v cells/rtl/*.v units.v \
        research/tools/suite/tb_capture.v && vvp -n a.out +HOLD_NS=30

Files: `status.tsv` (the table), `emit.tsv` (emit.py per mode, the first error verbatim), `blockers.tsv` (every
refusal, regenerated 2026-11-18), `rtl.tsv`, `smoke.tsv`; the 2026-11-17 files `triage.tsv`, `whatif.tsv`,
`forcemc.tsv` are unchanged.

## Triage of 2026-11-17 (subagent suitew; kept as the record -- its counts, tables and blockers are the state before stores.md and before the load-first work; `blockers.tsv` is now regenerated)

Tools: the frontend is the owner's build in `$HOME/dynamatic` (`dynamatic-opt` md5 0875db47e1f20161,
`translate-llvm-to-std` e95e3810f7c5f595, `clang` ee7246ced54bd436). yosys 0.62 from `$TC` was used only to
elaborate (`read_verilog; hierarchy -check`), never to synthesize. nextpnr was not run (`cells/verify/toolchain.sh`
passes, 9c732bc6303458df, for the record).

### Counts

95 directories: **93 tests**, plus two **groups** that `bdc/frontend.sh` could not reach: `memory/` holds 23 tests
and `sharing/` 2 (`no such kernel source: dynamatic/integration-test/memory/memory.c`). `bdc/frontend.sh` now takes
the one group member of a name that is found nowhere else (names that resolved before resolve as before; all 114
fixtures, including the four that were already in `cloud/fixtures/frontend/`, reproduce byte for byte). So 118 tests.

| | 93 top-level tests | 25 tests in `memory/`, `sharing/` |
|---|---|---|
| float or double in the kernel (out of scope) | **33** | 0 |
| integer | **60** | 25 |
| frontend fails | 4: 2 float (`correlation_float`, `dct`), 2 integer (`complexdiv`, `external_integration`) | 0 |
| frontend ok | 89 (58 integer) | 25 |
| `bdc/emit.py` ok, default | **12** (all integer) | 0 |
| `bdc/emit.py` ok, `BDC_AUTO=1` | **12**, the same 12; every error message identical to the default's | 0 |
| bench ABI fits (scalar args in 2 words, one i32 result) | **4**: `factorial`, `gcd`, `iterative_division`, `iterative_sqrt` | 0 |

All four frontend failures are the same message from `translate-llvm-to-std` (step 6):
`LLVM ERROR: Not implemented llvm intrinsic function handling!`. The calls it cannot translate: `complexdiv`
`@llvm.abs.i32` (from `abs()`), `external_integration` `@port_A`/`@port_B` (external functions, Dynamatic's
external-module feature), `correlation_float` `@sqrt`/`@sqrtf`, `dct` `@cos`.

Why the 46 integer top-level tests that pass the frontend do not emit, by `emit.py`'s **first** error:

| first error (emit.py / mem.py, verbatim prefix) | tests |
|---|---|
| `EmitError: no width rule for handshake op 'lsq'` | 24 |
| `EmitError: mem_controller at line N: the first accessor in program order is 'load', not 'store'.` | 10 |
| `EmitError: mem_controller at line N has a store accessor.` | 8 |
| `mem.MemError: address width 14 asks for 16384 words; one bd_mem is 1024` (`matvec`; `trisolv`: width 20) | 2 |
| `EmitError: no width rule for handshake op 'divsi'` (`if_loop_3`) | 1 |
| `EmitError: no width rule for handshake op 'divui'` (`test_divui`) | 1 |

The 25 group tests: `lsq` 14, load-first port 4, `hs.parse.ParseError: ... expected an operation mnemonic, found
'"handshake.ram"'` 3, `mem_controller at line N has K accessors; only 1 (plain port) or 2 ... is implemented` 3, store
accessor 1. The 31 float tests that pass the frontend: 30 stop on a float type or op
(`memref<...xf32>`, `<f32>`, `<f64>`, `sitofp`, `negf`), `matching` on `lsq` first.

The 12 that emit: `factorial`, `fir`, `gcd`, `if_loop_1`, `if_loop_2`, `iterative_division`, `iterative_sqrt`,
`sumi3_mem`, `test_bitint`, `test_int16`, `test_loop_free`, `unused_arg`. Each module, default and AUTO, elaborates
against `cells/rtl/` (yosys `hierarchy -check -top bdc_<name>`, 24 of 24). `emit OK` means only that: no simulation,
no synthesis, no route.

### What blocks the rest: every refusal, not just the first

`emit.py` stops at its first error, and most tests have more than one blocker, so the first error does not say what a
fix would unlock. `research/tools/suite/dyn_blockers.py` reads each `handshake_transformed.mlir` with bdc's own parser
and applies the refusals `emit.py`/`mem.py` apply (`blockers.tsv`). Check: on all 114 frontend outputs the first
error `emit.py` raised is in the set, and the 12 that emit have an empty set.

Then `research/tools/suite/dyn_whatif.py` runs a copy of `emit.py` with exactly those refusals switched off (text
patches that must each apply once): **all 29 integer tests blocked only by patchable refusals pass every later stage
of `emit.py`** (link sites, ring depths, ...), so no hidden refusal behind the first ones (`whatif.tsv`). Negative
controls: with no patch, or only part of a test's set, the next refusal fires. The Verilog a patched emitter writes
is not a circuit (no store counter, undriven tokens); `OK` there means only that no other stage refused.

Blocker tags: `lsq` (a load-store queue), `mc:store` (a memory controller with a store), `mc:load1st` (two accessors
on one controller, a load first), `mc:>2` (more than two accessors on one controller), `ram` (an internal or constant
array), `op:divsi`/`op:divui`/`op:remsi`, `mem>1024` (a memref deeper than one bd_mem).

### The ranking (integer tests: 71 blocked, 60 top-level + 25 group minus the 12 that emit and 2 frontend failures)

| blocker | needed by | sole blocker of | where the work is | rough size |
|---|---|---|---|---|
| `lsq` | **39** (25 top-level, 14 group) | **25** | no lowering at all: `bdc/bd-config.json` `lsq: todo`; `emit.py` `result_channels()` has no rule. A bundled-data load-store queue: new cells (`cells/rtl/` is frozen: stated reason + routed GLS), a generator beside `bdc/mem.py` | large (weeks); but see the next section |
| `mc:store` | **33** | **9** | `emit.py` `_op_mem_controller` (the `has_store` refusal): memEnd needs Dynamatic's `remainingStores == 0`, an asynchronous up/down count of promised (per-block store-count constants, skipped today in `_resolve_mem_accessors`) against completed stores (each store's `z`, tied off today) | medium: ~300 lines + GLS of the race the emit.py comment names |
| `mc:load1st` | **21** | **3** | `emit.py` `_resolve_mem_accessors` (the `arb and ... != "store"` refusal): the program-order token is taken from the first accessor's `z`, which only a store leaves free; a load's `z` needs a fork into its consumer and the token | small: a fork in `_op_load` + the chain wiring, ~100 lines + GLS of a load-first port |
| `mc:>2` | 4 | 0 | `bdc/mem.py` `emit_port` ("N slots need a TREE of them with each leaf's select ANDed down its path to the root") + an N-long token chain in `_resolve_mem_accessors` | medium: ~200 lines + GLS of the tree |
| `ram` | 3 | 3 | `bdc/hs/parse.py` `_parse_op` (generic op syntax `"handshake.ram"() {...} : () -> memref<..>`), then `emit.py` treats the result as an internal memref. The two scratch arrays (`test_internal_array`, `test_unroll`) are written before they are read and need no contents; the constant table (`test_constant_array`) needs RAM contents, and `bd_mem`'s RAMB18E1 has no INIT (frozen cell) | small-medium |
| `op:divsi` / `op:divui` / `op:remsi` | 3 / 1 / 1 | 1 / 1 / 0 | `bdc/compute.py` `BINARY` + `default_delay()` class, `emit.py` `result_channels()`, `bdc/bd-config.json`. The what-if (Verilog `/` and `%` as a combinational unit) passes the rest of emit.py. A 32-bit combinational divider is on the order of 1000 LUTs and 32 carry chains deep: the code is small, the delay sizing and GLS are the cost. `test_divui` divides by the constant 1083 (a multiply-high would do) | medium |
| `mem>1024` | 2 | 0 | `bdc/mem.py` `check()` / `emit_port`: bank a memref over several bd_mem with an address decode. `matvec` (10000 words x 32 bits = 20 RAMB18 of the device's 120) fits; **`trisolv` (A[1000][1000], 32 Mbit) cannot fit the xc7z010's 2.1 Mbit of BRAM at all** | medium |
| frontend: `@llvm.abs` | 1 (`complexdiv`) | - | `bdc/frontend.sh`: rewrite the intrinsic into compare/subtract/select before step 6 (dynamatic/ is not ours to edit). From the C (not measured): complexdiv then needs `divsi` (6 divisions) and `mc:store` too | small |
| frontend: external calls | 1 (`external_integration`) | - | Dynamatic's external-module interface (`instance: todo` in bd-config.json) | out of scope for the suite |
| float | 33 | | | out of scope |

Greedy order (each step adds the blocker that unlocks most; counts are tests whose whole set is covered):
`lsq` +25, `mc:store` +14 (39), `mc:load1st` +19 (58), `mc:>2` +4 (62), `ram` +3 (65), `op:divsi` +2 (67),
`mem>1024` +2 (69, but `trisolv` cannot fit the device), `op:remsi` +1 (70), `op:divui` +1 (71).

**Without the LSQ, the three memory-controller items together (`mc:store` + `mc:load1st` + `mc:>2`) unlock 26
tests** (9 store only, 3 load-first only, 11 both, 3 store + N-way). They are the cheapest large block of the list.

### The LSQ tests through memory controllers instead (`force-mc`)

`bdc/frontend.sh` step 7 runs `--mark-memory-interfaces`, which places an LSQ wherever Dynamatic cannot prove two
accesses independent. compile.sh's other branch, `--force-memory-interface="force-mc=true"`, places controllers
everywhere. `research/tools/suite/dyn_forcemc.sh` reran steps 7-8 that way for the 39 integer LSQ tests (into a
scratch directory; no fixture changed) (`forcemc.tsv`): **36 of the 39 then need only `mc:store`, `mc:load1st` and
`mc:>2`** (19 load-first + store, 13 N-way + store, 2 store only, 2 all three); `covariance` also needs `divsi`,
`path_profiling` `remsi`, `trisolv` `divsi` and banking. With the refusals lifted, all 39 pass the rest of `emit.py`
(what-if). The controller shapes get long (`kmp` `SLSLL`, `gemver` `LSLSL`, `polyn_mult` `SLSLS`).

So the memory-controller work would cover 26 + 36 = **62 of the 71**. Whether that is **correct** is open and is
the real question: the LSQ is there because accesses may alias across iterations (`test_memory_5`:
`a[i] = a[i-1] + a[i-2] + 5`). bdc's token chain orders the accessors of one controller within an iteration
(`prev.z -> next.c`, bdc/mem.py); nothing shown here says it orders a load of iteration i+1 after a store of
iteration i. That needs an argument (or a proof) before `force-mc` is anything but a measurement.

### The bench ABI (`cells/hw/gen_bench.py`)

The 4 that fit (`factorial`, `gcd`, `iterative_division`, `iterative_sqrt`): `gen_bench.py <name> --top
<name>_bench_gen` writes a bench, and that bench elaborates against the emitted kernel and `cells/rtl/` (yosys
`hierarchy -check`, no warning about ports). Not synthesized, not routed.

What gen_bench.py does with the 8 that emit and do not fit:

- **memref arguments (6: `fir`, `if_loop_1`, `if_loop_2`, `sumi3_mem`, `test_bitint`, `unused_arg`): gen_bench.py
  accepts them and writes invalid Verilog.** A memref parses to width 0, `words_for(0)` is 0 words, and the port
  becomes `.di_data ({})` (yosys: `syntax error, unexpected '}'`); the kernel has no such port anyway (emit.py keeps
  the memory inside), and the `<memref>_start`/`<memref>_end` controls are left unconnected. **The same happens for
  `memsum`** (checked: `.a_data ({})`), so `cells/hw/build_bench.sh memsum` cannot synthesize as things stand. A
  one-line refusal of memref arguments would make this loud; a bench for a memory kernel needs a way for the host
  to fill the arrays before `start`. Today nothing can: `cells/rtl/bd_mem.v` (frozen) gives its RAMB18E1 no INIT and
  ties port B off, so every array starts all-zero and every answer is the degenerate one.
- **result width (`test_int16`, i16): accepted**; the 32-bit result bus is connected to a 16-bit port (yosys only
  warns `Resizing cell port ... out0_data from 32 bits to 16 bits`), so the top 16 bits the host reads are undriven.
  gen_bench.py never looks at the result.
- **4 operand words (`test_loop_free`): refused**, correctly (`needs 4 operand words ... only has 2`).

Also: gen_bench.py's `DOMAIN_RESTRICTIONS` is keyed by kernel name, which the suite rule forbids ("Nothing anywhere
in the flow is set for it by name"). The suite needs each kernel's domain to come from the suite's own description.

### Suite candidates now: scalar, emit OK, bench fits

`gcd` is already one of the six. New: `factorial`, `iterative_division`, `iterative_sqrt`. Domains below are read
from the C (main() and the kernel's own arithmetic); "UB" means C undefined behaviour (signed overflow), where the
oracle has no answer to compute unless it fixes wrapping semantics.

**`factorial(int n)`**: two loops in sequence, both trip counts set by the data (`while (n >= 3) n -= 3` with a
3-factor multiply, then `while (n > 0) n--`), 4 `muli` (the DSP path).
- Dynamatic's main: `n = rand() % 100`, `assert(n > 1)`, i.e. one n in [2, 99].
- Defined for n <= 12: 13! overflows int (UB). Any negative n is defined (both loops skip, returns 1).
- Trip counts: loop 1 floor(n/3) for n >= 3; loop 2 the remainder (0-2); both 0 for n <= 0. In the defined range
  loop 1 runs at most 4 times (n = 12) and the two together at most 5 (n = 11).
- Edge vectors: n = INT_MIN, -1, 0 (both loops 0 trips), 1, 2 (loop 2 only), 3 (loop 1 once, loop 2 zero), 5, 11,
  12 (largest defined). Random draws: n in [0, 12] (a draw over all of int is almost always negative, i.e. trivial).

**`iterative_division(int dividend, int divisor)`**: repeated subtraction, trip count |dividend| / |divisor|;
signs handled around the loop; an early exit for divisor == 0. LLVM's loop-idiom did not fold it into a `divsi`
(the emitted graph has subi/xori/select, no divide).
- Dynamatic's main: both `rand() % 100`, i.e. [0, 99]; divisor 0 is possible there (returns -1).
- UB: `ABS(INT_MIN)` (`-x` overflows), so neither argument may be INT_MIN. Everything else is defined.
- Trip count up to 2^31 - 1 (dividend INT_MAX, divisor 1): far too long for a bench vector. Bound the quotient for
  random draws, e.g. both in [-2^15, 2^15] (quotient at most 2^15), or Dynamatic's own [0, 99].
- Edge vectors: divisor 0 (no loop; returns -1, which is also a legal quotient, e.g. (-5, 5)); dividend 0 and
  dividend < divisor (0 trips, quotient 0: degenerate, never alone); dividend == divisor (1 trip); divisor 1 with
  the largest dividend the bound allows (most trips); each sign combination (-,+), (+,-), (-,-); dividend INT_MAX
  with divisor INT_MAX and INT_MAX - 1 (1 trip each); dividend -INT_MAX (= INT_MIN + 1, defined).

**`iterative_sqrt(int n)`**: binary search, trip count about log2(n) + 1 (at most 17 in the defined range, at
n = 66046), two `muli` (`mid * mid`) and an early exit on an exact square.
- Dynamatic's main: `n = rand() % 100`, i.e. [0, 99].
- UB above n = 92681: the first `mid` is n >> 1, and `mid * mid` overflows once mid >= 46341, i.e. n >= 92682.
  (After the first iteration every mid is smaller, so 92681 is the exact bound.) Negative n: the loop does not run
  (low 0 > high n) and n itself is returned.
- Edge vectors: n = INT_MIN, -1 (0 trips, returns n), 0 (returns 0: degenerate, not alone), 1, 2, 3, 4 (exact
  square, early exit), 99, 65536 (= 256^2), 92416 (= 304^2), 92680, 92681 (largest defined: mid 46340,
  46340^2 = 2147395600). Random draws: n in [-2^10, 92681].

**`gcd(int a, int b)`** (already benched; gen_bench.py restricts both to nonnegative, for the overflow cycle its
header records): Dynamatic's main uses the fixed pair (7966496, 314080416). Edge vectors: (0, b) and (a, 0) (early
returns), (0, 0) (returns 0: degenerate), (1, 1), (a, a), (1, INT_MAX), (INT_MAX, INT_MAX), (INT_MAX, INT_MAX - 1)
(coprime), (2^30, 2^30) (the common-power-of-two loop runs 30 times), (3 * 2^29, 2^30).

### Near candidates (one item away)

| test | what is missing | domain from the C |
|---|---|---|
| `test_loop_free(a, b, c, d)` | gen_bench.py `MAX_WORDS` 2 -> 4 (and the host register map) | no loops; three branches (a > 0; else b < 0; else). `b + c + d` and `a + d` can overflow (UB): the oracle must avoid those. Edges: a in {0, 1, -1}, b in {0, -1}, each branch, extreme values whose sums stay in range (e.g. a = INT_MAX, b = INT_MAX, c = INT_MIN, d = 0). Dynamatic's main: (1, -1, 2, 3) |
| `test_int16()` | gen_bench.py: a non-i32 result | no arguments; returns -1 as int16_t: one vector, and all-ones is the value a stuck-high bus also gives. A result-width test, not a benchmark |
| `test_divui(uint32 x)` | a `divui` unit | `x / 1083`, every uint32 defined. Edges: 0 (degenerate), 1082, 1083, 1084, 2^31 (sign bit set: unsigned semantics), 2^32 - 1. Dynamatic's main: 1084 |
| `if_loop_3` | a `divsi` unit + a memory bench | `sum /= dist` with dist = a[i] - b[i] >= 0: dist 0 is a division by zero (UB) |

The 6 memory tests that emit (`fir`, `if_loop_1`, `if_loop_2`, `sumi3_mem`, `test_bitint`, `unused_arg`) wait only
for the bench to load arrays.

### Reproduce

    ln -sfn $HOME/dynamatic dynamatic        # in a clone; never commit the link
    python3 research/tools/suite/dyn_triage.py OUT                       # all 95 directories -> OUT/triage.tsv
    python3 research/tools/suite/dyn_triage.py OUT2 $(ls dynamatic/integration-test/memory dynamatic/integration-test/sharing)
    python3 research/tools/suite/dyn_blockers.py blockers.tsv <every frontend success>
    research/tools/suite/dyn_forcemc.sh FM <lsq tests>                   # scratch, never build/frontend
    python3 research/tools/suite/dyn_whatif.py mc:store,mc:load1st build/frontend/vector_rescale/comp/handshake_transformed.mlir

`dyn_triage.py` removes every `BDC_*` variable from the environment before each emit (then sets `BDC_AUTO=1` for the
second). One core; 49 s and 3 min 37 s for the 95 in two runs here (a shared node), with identical results.

Files here: `triage.tsv` (all 118 tests and the 2 group directories: frontend, emit, AUTO, signature, ABI, gen_bench,
elaboration, every error verbatim), `blockers.tsv` (every refusal, controller shapes in program order, op
histogram), `whatif.tsv`, `forcemc.tsv`. Fixtures: `cloud/fixtures/frontend/<name>/comp/` for all 114 frontend
successes (float ones included).

### What this does not show

- That anything computes the right answer. Nothing was simulated, synthesized or routed; "emit OK" and "bench fits"
  are compile-level facts. "Unlocks N" is an upper bound for the same reason: the what-if shows only that no other
  stage of emit.py refuses.
- That `force-mc` is a correct substitute for the LSQ (open; see above).
- Area: `cnn` (seven-deep nest), the matrix kernels and anything with a combinational divider may not fit or route.
  The index arithmetic of every two-dimensional array is 64-bit in the frontend output (`i64` in the table: the
  row-major flattening's shifts and adds, which `--handshake-optimize-bitwidths` does not narrow).
- Dynamatic's own figures for these tests: none were obtained.

### All 95 directories

Columns: float (in the kernel itself, not only main(): `gemm` and `matching` have integer arguments and a float
accumulator); args (arrays read only / written / read+written, plus scalars); loops (L = for/while, D = do-while,
parentheses = nesting); C ops of note (mul, div, mod, var-shift, 64-bit, call); IR ops of note (from
`handshake_transformed.mlir`); frontend; bdc default; bdc `BDC_AUTO=1`; bench ABI; the first error, verbatim up to
its first full stop (`triage.tsv` has the whole message); every blocker (`blockers.tsv`). The args, loops and C-ops
columns come from small regex and tokenizer scripts over the preprocessed C (clang -E), checked by reading every
kernel; two were corrected by hand (`cnn`: its accesses are in macros; `matrix_power`: `mat[k][row[p]] +=`). The
scripts are not committed (they are in the subagent's out/ directory).

| test | float | args | loops | C ops | IR ops | frontend | bdc | bdc AUTO | bench ABI | first error | all blockers |
|---|---|---|---|---|---|---|---|---|---|---|---|
| admm | **float** | read+written; 1 scalar | L L(L L(L) L) | mul | shift×4, i64 | ok | FAIL | FAIL | - | `EmitError: function argument %arg1 is 'memref<30xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:store |
| atax | int | read+written | L(L L) | mul | muli×2, shift×4, i64 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq,mc:load1st,mc:store |
| atax_float | **float** | read+written | L(L L) | mul | shift×4, i64 | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<400xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:load1st,mc:store |
| bicg | int | read+written | L(L) | mul | muli×2, shift×4, i64 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq,mc:load1st,mc:store |
| bicg_float | **float** | read+written | L(L) | mul | shift×4, i64 | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<900xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:load1st,mc:store |
| binary_search | int | read only; 1 scalar | L L | - | - | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4: the first accessor in program order is 'load', not 'store'.` | mc:load1st |
| cnn | int | read+written | L(L(L(L)) L(L(L(L(L(L))))) L(L(L))) | mul,const-shift | muli×1, shift×13 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq,mc:store |
| complexdiv | int | read+written | L | mul,div,call | - | FAIL | - | - | - | `LLVM ERROR: Not implemented llvm intrinsic function handling!` | frontend |
| cordic | **float** | read+written; 3 scalar | L | mul,div | - | ok | FAIL | FAIL | - | `EmitError: function argument %arg1 is 'memref<2xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:store |
| correlation_float | **float** | read+written; 1 scalar | L(L) L(L) L(L) L(L(L)) | mul,div,call | - | FAIL | - | - | - | `LLVM ERROR: Not implemented llvm intrinsic function handling!` | frontend |
| covariance | int | read+written | L(L) L(L) L(L(L)) | mul,div | muli×1, divsi×1, shift×24, i64 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq,op:divsi |
| covariance_float | **float** | read+written | L(L) L(L) L(L(L)) | mul,div | shift×24, i64 | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<900xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float |
| dct | **float** | read+written | L(L(L(L))) | mul,call | - | FAIL | - | - | - | `LLVM ERROR: Not implemented llvm intrinsic function handling!` | frontend |
| divergent_paths | int | read+written | L | mul | shift×1 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq,mc:store |
| external_integration | int | scalars only (1) | none | mul,call | - | FAIL | - | - | - | `LLVM ERROR: Not implemented llvm intrinsic function handling!` | frontend |
| factorial | int | scalars only (1) | L L | mul | muli×4 | ok | ok | ok | **fits** (gen_bench ok, elaborates) |  | - |
| fir | int | read only | L | mul | muli×1 | ok | ok | ok | no: 2 memref arg(s) (gen_bench accepts it and writes `.<memref>_data ({})`: syntax error) |  | - |
| fixed | **float** | scalars only (1) | D | mul | - | ok | FAIL | FAIL | - | `EmitError: unrecognised channel type '<f32>' in type clause '<>, <f32>' -- add a rule, do not assume a width` | float |
| float_basic | **float** | read+written | L(L) | mul,div | shift×16, i64 | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<900xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:load1st,mc:store |
| gaussian | int | read+written | L(L(L)) | mul | muli×1, shift×6, i64 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| gcd | int | scalars only (2) | L L L L(L) | var-shift | shift×6 | ok | ok | ok | **fits** (gen_bench ok, elaborates) |  | - |
| gemm | **float** | read+written; 2 scalar | L(L(L)) | mul | muli×3, shift×16, i64 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'sitofp' -- add one to result_channels(), do not assume` | float,mc:load1st,mc:store |
| gemm_float | **float** | read+written; 2 scalar | L(L(L)) | mul | shift×16, i64 | ok | FAIL | FAIL | - | `EmitError: function argument %arg2 is 'memref<900xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:load1st,mc:store |
| gemver | int | read+written; 2 scalar | L(L) L(L) L L(L) | mul | muli×6, shift×16, i64 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq,mc:load1st,mc:store |
| gemver_float | **float** | read+written; 2 scalar | L(L) L(L) L L(L) | mul | shift×8, i64 | ok | FAIL | FAIL | - | `EmitError: function argument %arg2 is 'memref<100xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:load1st,mc:store |
| gesummv_float | **float** | read+written; 2 scalar | L(L) | mul | shift×8, i64 | ok | FAIL | FAIL | - | `EmitError: function argument %arg2 is 'memref<900xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:store |
| get_tanh | **float** | read+written | L | mul | - | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<1000xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float |
| gsum | **float** | read only | L | mul | - | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<1000xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float |
| gsumif | **float** | read only | L | mul | - | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<1000xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float |
| histogram | **float** | read+written; 1 scalar | L | - | - | ok | FAIL | FAIL | - | `EmitError: function argument %arg1 is 'memref<1000xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float |
| if_convert | int | read+written | D | mul | muli×1 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4 has a store accessor.` | mc:store |
| if_loop_1 | int | read only; 1 scalar | L | mul | shift×1 | ok | ok | ok | no: 1 memref arg(s) (gen_bench accepts it and writes `.<memref>_data ({})`: syntax error) |  | - |
| if_loop_2 | int | read only; 1 scalar | L | - | - | ok | ok | ok | no: 1 memref arg(s) (gen_bench accepts it and writes `.<memref>_data ({})`: syntax error) |  | - |
| if_loop_3 | int | read only; 1 scalar | L | div | divsi×1 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'divsi' -- add one to result_channels(), do not assume` | op:divsi |
| if_loop_add | **float** | read only | L | - | - | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<1000xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float |
| if_loop_mul | **float** | read only | L | mul | - | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<1000xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float |
| iir | int | read+written; 2 scalar | L | mul | muli×2 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 5: the first accessor in program order is 'load', not 'store'.` | mc:load1st,mc:store |
| image_resize | int | read+written; 1 scalar | L(L) | - | shift×8, i64 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4: the first accessor in program order is 'load', not 'store'.` | mc:load1st,mc:store |
| insertion_sort | int | read+written; 1 scalar | L(L) | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| iterative_division | int | scalars only (2) | L | - | - | ok | ok | ok | **fits** (gen_bench ok, elaborates) |  | - |
| iterative_sqrt | int | scalars only (1) | L | mul,const-shift | muli×2, shift×1 | ok | ok | ok | **fits** (gen_bench ok, elaborates) |  | - |
| jacobi_1d_imper | int | read+written | L(L L) | mul | shift×1 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| kernel_2mm | int | read+written; 2 scalar | L(L(L)) L(L(L)) | mul | muli×4, shift×14, i64 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq,mc:load1st,mc:store |
| kernel_2mm_float | **float** | read+written; 2 scalar | L(L(L)) L(L(L)) | mul | shift×14, i64 | ok | FAIL | FAIL | - | `EmitError: function argument %arg2 is 'memref<100xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:load1st,mc:store |
| kernel_3mm | int | read+written | L(L(L)) L(L(L)) L(L(L)) | mul | muli×3, shift×18, i64 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq,mc:store |
| kernel_3mm_float | **float** | read+written | L(L(L)) L(L(L)) L(L(L)) | mul | shift×24, i64 | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<100xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:load1st,mc:store |
| kmp | int | read+written | L(L) L(L) | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq,mc:>2 |
| loop_array | int | read+written; 2 scalar | L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| loop_path | int | read+written | D | mul | shift×1 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4 has a store accessor.` | mc:store |
| lu | **float** | read+written | L(L) L(L L) L(L(L)) L L(L(L L)) | mul,div | shift×20, i64 | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<9xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:>2 |
| matching | **float** | read+written; 1 scalar | L | mul | shift×1 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | float,lsq,mc:load1st |
| matching_2 | **float** | read+written; 1 scalar | L | mul | shift×1 | ok | FAIL | FAIL | - | `EmitError: function argument %arg1 is 'memref<1000xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:load1st |
| matrix | int | read+written | L(L(L)) | mul | muli×1, shift×12, i64 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4 has a store accessor.` | mc:store |
| matrix_power | int | read+written | L(L) | mul | muli×1, shift×4, i64 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| matvec | int | read+written | L(L) | mul | muli×1, shift×3, i64 | ok | FAIL | FAIL | - | `mem.MemError: address width 14 asks for 16384 words; one bd_mem is 1024 (RAMB18E1, x18).` | mc:store,mem>1024 |
| `memory/` | - | (group of 23 tests, listed below) | - | - | - | FAIL | - | - | - | `no such kernel source: dynamatic/integration-test/memory/memory.c` | - |
| mul_example | int | read+written | L | mul | muli×2 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4: the first accessor in program order is 'load', not 'store'.` | mc:load1st,mc:store |
| mvt_float | **float** | read+written | L(L) L(L) | mul | shift×8, i64 | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<900xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:load1st,mc:store |
| nested_conditionals_1 | int | read+written; 1 scalar | L | mul | muli×1, shift×1 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| nested_conditionals_2 | int | read+written; 1 scalar | L(L) | mul | shift×4 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| nested_loop | int | read+written | L(D) | mul | muli×1, shift×3 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4 has a store accessor.` | mc:store |
| path_profiling | int | read+written | L | mod | remsi×1 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq,mc:load1st,op:remsi |
| pivot | int | read+written; 2 scalar | L | mul | muli×1 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| polyn_mult | int | read+written | L(L L) | mul | muli×2 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq,mc:load1st |
| prediction | **float** | read+written; 1 scalar | L | mul | - | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<100xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:store |
| `sharing/` | - | (group of 2 tests, listed below) | - | - | - | FAIL | - | - | - | `no such kernel source: dynamatic/integration-test/sharing/sharing.c` | - |
| simple_example_1 | int | written | L | - | - | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4 has a store accessor.` | mc:store |
| single_loop | int | read+written | D | mul | muli×1 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4 has a store accessor.` | mc:store |
| sobel | int | read+written | L(L(L(L))) | mul | muli×2, shift×2 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 7: the first accessor in program order is 'load', not 'store'.` | mc:load1st,mc:store |
| sparse | **float** | read only | D | mul | - | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<100xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float |
| spmv | int | read+written; 1 scalar | L(L) | mul | muli×1 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 9: the first accessor in program order is 'load', not 'store'.` | mc:load1st,mc:store |
| stencil_2d | int | read+written | L(L(L)) | mul | muli×1, shift×5 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4 has a store accessor.` | mc:store |
| subdiag | **float** | read only | D | mul | - | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<1000xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:load1st |
| subdiag_fast | **float** | read only | D | mul | - | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<1000xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float |
| sumi3_mem | int | read only | L | mul | muli×2 | ok | ok | ok | no: 1 memref arg(s) (gen_bench accepts it and writes `.<memref>_data ({})`: syntax error) |  | - |
| symm_float | **float** | read+written; 2 scalar | L(L(L)) | mul | shift×36, i64 | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<900xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:>2 |
| syr2k_float | **float** | read+written; 2 scalar | L(L) L(L(L)) | mul | shift×28, i64 | ok | FAIL | FAIL | - | `EmitError: function argument %arg0 is 'memref<900xf32>', which is not a memref<NxiW> this backend knows how to parse.` | float,mc:load1st |
| test_bitint | int | read only | L | mul | muli×1 | ok | ok | ok | no: 2 memref arg(s) (gen_bench accepts it and writes `.<memref>_data ({})`: syntax error) |  | - |
| test_bool_array | int | read only | none | - | - | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4: the first accessor in program order is 'load', not 'store'.` | mc:load1st |
| test_divui | int | scalars only (1) | none | div | divui×1 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'divui' -- add one to result_channels(), do not assume` | op:divui |
| test_double | **float** | scalars only (0) | none | - | - | ok | FAIL | FAIL | - | `EmitError: unrecognised channel type '<f64>' in type clause '<>, <f64>' -- add a rule, do not assume a width` | float |
| test_fneg | **float** | scalars only (1) | none | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'negf' -- add one to result_channels(), do not assume` | float |
| test_int16 | int | scalars only (0) | none | - | - | ok | ok | ok | no: result out0:i16, the bench reads i32 (gen_bench accepts it; yosys: out0_data resized 32 -> 16 bits) |  | - |
| test_loop_free | int | scalars only (4) | none | - | - | ok | ok | ok | no: 4 operand words > 2 (gen_bench refuses) |  | - |
| test_stdint | int | read+written; 1 scalar | L | mul | muli×2 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4: the first accessor in program order is 'load', not 'store'.` | mc:load1st,mc:store |
| threshold | int | read+written; 1 scalar | L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| triangular | int | read+written; 1 scalar | L(L) | mul | muli×1, shift×4, i64 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| trisolv | int | read+written | L(L) | mul,div | muli×1, divsi×1, shift×12, i64 | ok | FAIL | FAIL | - | `mem.MemError: address width 20 asks for 1048576 words; one bd_mem is 1024 (RAMB18E1, x18).` | lsq,mc:load1st,mem>1024,op:divsi |
| unused_arg | int | read only; 1 scalar | none | - | - | ok | ok | ok | no: 1 memref arg(s) (gen_bench accepts it and writes `.<memref>_data ({})`: syntax error) |  | - |
| vector_rescale | int | read+written; 1 scalar | L | mul | muli×1 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4: the first accessor in program order is 'load', not 'store'.` | mc:load1st,mc:store |
| video_filter | int | read+written; 2 scalar | L(L) | mul,const-shift | muli×3, shift×27, i64 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4: the first accessor in program order is 'load', not 'store'.` | mc:load1st,mc:store |
| while_loop_1 | int | read+written | L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| while_loop_2 | int | read+written | L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| while_loop_3 | int | written; 1 scalar | L | mul | muli×1 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4 has a store accessor.` | mc:store |
| wrap_if | int | read+written; 1 scalar | L | mul | shift×5 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq,mc:store |

### The 25 tests inside `memory/` (23) and `sharing/` (2)

| test | float | args | loops | C ops | IR ops | frontend | bdc | bdc AUTO | bench ABI | first error | all blockers |
|---|---|---|---|---|---|---|---|---|---|---|---|
| memory/test_constant_array | int | read only | L(L) | - | - | ok | FAIL | FAIL | - | `hs.parse.ParseError: build/frontend/test_constant_array/comp/handshake_transformed.mlir:7:10: expected an operation mnemonic, found '"handshake.ram"'` | ram |
| memory/test_flatten_array | int | read+written | L(L(L)) | - | shift×4, i64 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4 has a store accessor.` | mc:store |
| memory/test_internal_array | int | read+written | L(L) L(L) | mul | - | ok | FAIL | FAIL | - | `hs.parse.ParseError: build/frontend/test_internal_array/comp/handshake_transformed.mlir:10:10: expected an operation mnemonic, found '"handshake.ram"'` | ram |
| memory/test_memory_1 | int | read+written; 1 scalar | L | - | - | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 5: the first accessor in program order is 'load', not 'store'.` | mc:load1st,mc:store |
| memory/test_memory_10 | int | read+written; 1 scalar | L | - | - | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4 has 3 accessors; only 1 (plain port) or 2 (arbitrated port -- bd_arbiter arbitrates exactly two requesters) is implemented` | mc:>2,mc:store |
| memory/test_memory_11 | int | read+written | L L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| memory/test_memory_12 | int | written | L | - | - | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4 has 4 accessors; only 1 (plain port) or 2 (arbitrated port -- bd_arbiter arbitrates exactly two requesters) is implemented` | mc:>2,mc:store |
| memory/test_memory_13 | int | read+written | L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| memory/test_memory_14 | int | read+written | L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| memory/test_memory_15 | int | read+written | L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| memory/test_memory_16 | int | read+written | L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| memory/test_memory_17 | int | read+written | L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq,mc:store |
| memory/test_memory_18 | int | read+written | L | mul | muli×1 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 5 has 3 accessors; only 1 (plain port) or 2 (arbitrated port -- bd_arbiter arbitrates exactly two requesters) is implemented` | mc:>2,mc:store |
| memory/test_memory_2 | int | read+written; 1 scalar | L | - | - | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4: the first accessor in program order is 'load', not 'store'.` | mc:load1st,mc:store |
| memory/test_memory_3 | int | read+written; 1 scalar | L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| memory/test_memory_4 | int | read+written; 1 scalar | L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| memory/test_memory_5 | int | read+written; 1 scalar | L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| memory/test_memory_6 | int | read+written; 1 scalar | L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| memory/test_memory_7 | int | read+written; 1 scalar | L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| memory/test_memory_8 | int | read+written; 1 scalar | L | - | - | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| memory/test_memory_9 | int | read+written; 1 scalar | L | mul | shift×1 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| memory/test_smallbound | int | read+written | L(L) | - | shift×1, i64 | ok | FAIL | FAIL | - | `EmitError: no width rule for handshake op 'lsq' -- add one to result_channels(), do not assume` | lsq |
| memory/test_unroll | int | read+written | L L | mul | - | ok | FAIL | FAIL | - | `hs.parse.ParseError: build/frontend/test_unroll/comp/handshake_transformed.mlir:10:10: expected an operation mnemonic, found '"handshake.ram"'` | ram |
| sharing/share_test_1 | int | read only | L L | mul | muli×2, shift×1 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4: the first accessor in program order is 'load', not 'store'.` | mc:load1st |
| sharing/share_test_2 | int | read+written | L | mul | muli×4, shift×14 | ok | FAIL | FAIL | - | `EmitError: mem_controller at line 4: the first accessor in program order is 'load', not 'store'.` | mc:load1st,mc:store |
