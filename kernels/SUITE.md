# The compiler benchmark suite

research/PROGRAM.md "A benchmark suite for the compiler" (owner, 2026-11-17): kernels chosen to cover shapes, not to
flatter the flow; each with an input range in which its C is defined, vectors that include the edges of that range,
and expected values computed from the C, never recorded from a run. Nothing in the flow is set for a suite kernel by
name. A kernel the compiler refuses, deadlocks on or gets wrong stays here, marked so: that is work for the compiler.

This file: the first scalar kernels, one per shape (suite agent `suitek`, 2026-11-17), plus the kernels that were
already here. Dynamatic's integration tests and the memory kernels are other agents' parts (see the end).

## How each kernel is checked

| step | command | what passing means |
|---|---|---|
| frontend | `./bdc/frontend.sh K` (fixtures: `cloud/fixtures/frontend/K/comp/`) | Dynamatic's passes produce `handshake_transformed.mlir` |
| bdc | `python3 bdc/emit.py build/frontend/K/comp/handshake_transformed.mlir --no-top -o K.v`, default and `BDC_AUTO=1` | bdc lowers every op |
| expected values | `research/tools/suite/oracle.sh K < kernels/K/vec.hex > kernels/K/vec.exp` | the kernel's own C, gcc -O1 -fwrapv, words mapped from its signature (`check_oracle.sh`: PASS) |
| vector rules | `python3 research/tools/suite/veclint.py kernels/K/vec.{hex,exp}` | bench format; no two consecutive answers equal; at most a quarter 0 |
| simcheck | `python3 bdc/simcheck.py <mlir> --c-oracle --timeout-us 400`, default and `BDC_AUTO=1` | pre-route Verilog (sim/bd_prims_sim.v arc timing) returns every expected value; NOT routed timing |
| routed smoke | `research/tools/suite/run_smoke.sh 1 3 K...` (`smoke.sh`: build_bench.sh BD_NO_TIGHTEN=1 BD_SIZES=none BD_DSP=1, seed 1, --freq 83; then `bench_gate.sh ... worst`) | the bitstream, decoded back to a netlist, with prjxray delays at the worst corner (+ scatter), returns every expected value, both runs of each vector agreeing |

**One seed is a smoke test, not a result** (CLAUDE.md: >= 4 placer seeds for any routed claim). The routed column says
"this route of this kernel computes the right answers at one corner", nothing about margins or other routes. Sizes are
bdc's placeholders (generous), so no ns-per-iteration number is quoted here. nextpnr 9c732bc6303458df (toolchain.sh
all ok).

## The table

Status words: **frontend** = stops in Dynamatic's frontend; **bdc** = bdc refuses (error quoted); **deadlock** = the
simulation never returns the answer of some vector (no wrong value seen); **PASS n/n** = every vector right.
"AUTO" = `BDC_AUTO=1`. Routed: gate at worst on seed 1; "EQ" / "NOT EQ" = the fasm_equiv verdict on the route's
bitstream (NOT EQ routes are not usable as board routes, whatever the gate says).

| kernel | shape | what it exercises | input range (C defined, trips bounded) | vectors | expected values | frontend / bdc | simcheck default / AUTO | routed s1 default | routed s1 AUTO |
|---|---|---|---|---|---|---|---|---|---|
| straight | straight-line arithmetic | add, sub, xor, or, and, constant shifts; one token through a loop-free graph | (a, b) any int32 | kernels/straight/vec.hex (12) | oracle.sh (C) | ok / ok | PASS 12/12 / PASS 12/12 | PASS 12/12, EQ | PASS 12/12, EQ (same fasm as default) |
| countloop | a counted loop | counter, its test, an accumulator, a loop-invariant operand | a any; n <= 256 (n < 0: 0 trips) | kernels/countloop/vec.hex (10) | oracle.sh | ok / ok | PASS 10/10 / PASS 10/10 | PASS 10/10, EQ | PASS 10/10, EQ |
| sqrtsub | a trip count that depends on the data | exit test between two loop-carried values (n - 1 - 3 - 5 ... >= next odd) | n <= 65536 (trips floor(sqrt n) <= 256; n < 0: 0) | kernels/sqrtsub/vec.hex (13) | oracle.sh | ok / ok | PASS 13/13 / PASS 13/13 | PASS 13/13, EQ | PASS 13/13, EQ |
| nest3 | a loop nest three deep | three rings sharing a token; innermost bound (i ^ j) & 3, often 0 | a, b <= 8 (<= 8 + 64 + 96 iterations) | kernels/nest3/vec.hex (12) | oracle.sh | ok / ok | **deadlock** (vector 1) / PASS 12/12 | **HANG** at vector 1 (FAIL 1/2), EQ; vectors 0-1 only (simcheck's deadlock prefix) | **WRONG** at vector 1,2,4,5,7,8,9,11 (FAIL 4/12), **NOT EQ**, FFMUX-flagged bitstream |
| twoloops | two loops in sequence | the second loop's trip count (x & 255) is the first loop's result | a any; n <= 128 (second loop <= 255) | kernels/twoloops/vec.hex (11) | oracle.sh | ok / ok | PASS 11/11 / PASS 11/11 | PASS 11/11, EQ | PASS 11/11, EQ |
| brhash | a branch inside a loop that if-conversion cannot remove | each arm 3 dependent steps: the MLIR keeps 6 merges and no select in the body | x any; n <= 256 | kernels/brhash/vec.hex (10) | oracle.sh | ok / ok | PASS 10/10 / PASS 10/10 | PASS 10/10, **NOT EQ** | PASS 10/10, EQ |
| lfsrfind | an early exit (a search with break) | a loop with two exits whose index meets after it; found test before the step | seed, key any (low 16 bits used); trips <= 256 | kernels/lfsrfind/vec.hex (10) | oracle.sh | ok / ok | **deadlock** (any search of >= 1 step) / PASS 10/10 | **HANG** at vector 1 (FAIL 1/2), **NOT EQ**; vectors 0-1 only (simcheck's deadlock prefix) | **WRONG** at vector 2,3,4,5,6,7,8,9 (FAIL 2/10), **NOT EQ**, FFMUX-flagged bitstream |
| quadrec | several live values across the back edge | a, b, c, d, i on one ring; a <- b <- c <- d are plain moves | x any; n <= 256 | kernels/quadrec/vec.hex (10) | oracle.sh | ok / ok | **deadlock** (vector 2, n = 4) / **deadlock** (same) | **HANG** at vector 2 (FAIL 2/3), EQ; vectors 0-2 only (simcheck's deadlock prefix) | **HANG** at vector 2 (FAIL 2/3), **NOT EQ**; vectors 0-2 only (simcheck's deadlock prefix) |
| horner | multiply (the DSP path) | a variable x variable muli on the loop-carried path | x any; n <= 256 | kernels/horner/vec.hex (11) | oracle.sh | ok / ok | PASS 11/11 / PASS 11/11 | PASS 11/11, EQ | PASS 11/11, EQ |
| fold64 | 64-bit arithmetic | i64 argument (two bench words), 64-bit add with carry across bit 31, shifts, compare (a select), constants | v any int64; trips = v & 255 | kernels/fold64/vec.hex (10) | oracle.sh | ok / ok | PASS 10/10 / PASS 10/10 | PASS 10/10, EQ | PASS 10/10, EQ |
| varshift | shifts by a variable amount | shli / shrui / shrsi by amounts from the loop state (barrel shifters on a ring) | x any; n <= 256 | kernels/varshift/vec.hex (10) | oracle.sh | ok / ok | PASS 10/10 / PASS 10/10 | PASS 10/10, **NOT EQ** | PASS 10/10, **NOT EQ** |
| cmpchain | a chain of compares | eq, slt, slt && slt, ugt, sge, ule: an if / else-if ladder (cond_br + 2 selects) | (x, y) any int32 | kernels/cmpchain/vec.hex (17; all 7 classes) | oracle.sh | ok / ok | PASS 17/17 / PASS 17/17 | PASS 17/17, **NOT EQ** | PASS 17/17, **NOT EQ** (same fasm as default) |
| digitsum | division / modulo | `v % b`, `v / b` by a variable divisor | x, base any (b < 2 means 10) | - | - | **frontend**: `error: failed to legalize operation 'arith.remui'` (lower-cf-to-handshake) | - | - | - |
| digitdiv | division (remainder as v - q*b) | divui and a muli | x, base any (b < 2 means 10) | - | - | ok / **bdc**: `EmitError: no width rule for handshake op 'divui' -- add one to result_channels(), do not assume` (both flows) | - | - | - |
| nested | a loop nest two deep | two rings sharing a token | a, b <= 16 (trips a * b <= 256) | kernels/nested/vec.hex (11) | oracle.sh (-fwrapv: the C overflows int, see below) | ok / ok | **deadlock** (vector 3: (5, 0)) / PASS 11/11 | **HANG** at vector 3 (FAIL 3/4), **NOT EQ**; vectors 0-3 only (simcheck's deadlock prefix) | PASS 11/11, EQ |
| branchloop | a loop inside a branch inside a loop | an inner loop in one arm of a branch that survives if-conversion | n any int32 (<= ~64 steps) | kernels/branchloop/vec.hex (14) | oracle.sh | ok / ok | PASS 14/14 / PASS 14/14 | not run (time) | not run (time) |
| memsum | memory: read only | a load in a ring (mem_controller) | - | - | - | ok / ok (bdc emits) | - (simcheck and the oracle drive scalars only) | waits for the bench ABI | waits for the bench ABI |
| gcd | Dynamatic's gcd (Stein): loops with guarded update chains | 13 control_merges, 14 merges, 38 cond_br | a, b >= 0 (bench mask) | research/data/eventgraph/gate/gcd18.hex | research/data/gcd_draws/gcd_oracle.sh (C + the bench mask) | ok / ok | PASS 6/6 / PASS 6/6 (REFS) | not re-run here | not re-run here |
| ipow | binary exponentiation | two variable muli | (b, e) any int32 (trips = bit length of e) | research/data/eventgraph/gate/ipow17.hex | oracle.sh = kernel_oracle.sh (byte for byte) | ok / ok | PASS 8/8 / PASS 8/8 (REFS); PASS 17/17 / PASS 17/17 (C oracle, ipow17) | not re-run here | not re-run here |
| collatz | Collatz stopping time | data-dependent trip count; if/else (if-converted to a select) | n & 0xFFFF, positive (bench mask) | research/data/eventgraph/gate/col18.hex | research/tools/fifteen/kernel_oracle.sh (mask applied) | ok / ok | PASS 8/8 / PASS 8/8 (REFS) | not re-run here | not re-run here |
| collatz64 | Collatz on 64 bits | i64 datapath | n < 2^32, positive (bench mask: high word 0) | research/data/eventgraph/gate/c6419.hex | kernel_oracle.sh (mask applied) | ok / ok | PASS 3/3 / PASS 3/3 (REFS) | not re-run here | not re-run here |
| isprime | trial division | a loop with two exits, nested shift-subtract modulo | n any int32 | research/data/alltable/isp17.hex | oracle.sh = kernel_oracle.sh (byte for byte) | ok / ok | PASS 10/10 / PASS 10/10 (REFS); PASS 18/18 / PASS 18/18 (C oracle, isp17) | not re-run here | not re-run here |
| xorshift | xorshift32 | xori, shli, shrui on a counted ring | rounds & 0xFFF (bench mask) | research/data/eventgraph/gate/xor19.hex | kernel_oracle.sh (mask applied) | ok / ok | PASS 8/8 / PASS 8/8 (REFS) | not re-run here | not re-run here |

**Summary (2026-11-17, seed 1).** The 14 new kernels: 13 pass Dynamatic's frontend (digitsum stops at `remui`),
12 pass bdc in both flows (digitdiv stops at `divui`). simcheck (pre-route): default 9 / 12, BDC_AUTO 11 / 12. Routed,
gate at worst: default 9 / 12 right (3 of them on NOT EQUIVALENT bitstreams), and the 3 that simcheck deadlocks hang
(quadrec, nest3, lfsrfind); BDC_AUTO 9 / 12 right (2 on NOT EQUIVALENT bitstreams), quadrec hangs as in simcheck,
lfsrfind and nest3 return wrong values on the two routes with the FFMUX bitstream defect. NOT EQUIVALENT bitstreams: 10
of 26 gated routes, all the known F7 / FF classes, none attributable to bdc. Open bdc work:
quadrec (both flows), lfsrfind / nest3 / nested (default flow), division and modulo.

## What the suite found (work for the compiler)

1. **quadrec deadlocks in both flows: bdc's ring floor counts stages, not tokens.** Its ring a <- b <- c <- d <-
   t(a, b, c, d) passes the loop header four times, so it carries four tokens; bdc gives it one link per back edge
   (4 stages) and RING_MIN_STAGES = 3 is met. simcheck hangs at the first vector that iterates more than once (n = 4;
   n = 0 and n = 1 pass), and so does the routed design: seed 1, default flow, bitstream EQUIVALENT, bench gate at
   worst on vectors 0-2: n = 0 and n = 1 right, n = 4 never completes (the AUTO route the same, on a NOT EQUIVALENT
      bitstream). It is in the circuit, not in simcheck's timing model. With the four rotation back edges deepened to 3
   stages
   (`BDC_LINK_DEPTHS=ulink_n_trueResult_14=3,ulink_n_trueResult_16=3,ulink_n_trueResult_18=3,ulink_n_trueResult_20=3`)
   simcheck passes 10/10. `research/tools/suite/ring_tokens.py` (stages - 2 x back edges, worst cycle) reads -4 on
   quadrec in both flows, +1 with the deeper links, and +1 or no cycle on every other fixture that emits (21 kernels,
   both flows). Proposed rule, NOT applied: a cycle that threads k back edges needs 2k + 1 stages (the existing
   one-token rule, generalised; checked on this one kernel). Work for goal 1: the automatic path has to place it.
   **Fixed in bdc (2026-11-18, research/data/suite/ringfloor.md): the token floor, on in both flows.** 2k + 1 per
   cycle is necessary, not sufficient (trueResult_14 at 7 stages meets it on every cycle and still deadlocks); the
   rule also needs 2K stages on a path that carries K more tokens than another path from the same fork to the same join
   (quadrec's loop-condition fork feeds every steer, so each rotation back edge needs 2). bdc now adds 2 stages on
   trueResult_16/18/20: simcheck PASS 10/10 both flows; each added stage removed alone deadlocks again.
2. **The default flow (no BDC_AUTO) deadlocks on three loop shapes; in simcheck BDC_AUTO's rule M removes it.**
simcheck, each
   vector alone. lfsrfind hangs on any search of one step or more ((1, 0xb400)); seed == key (0 steps) passes, also
   twice in a row. nested and nest3 hang exactly when an inner loop has 0 trips in an instance after its first one in
   the call: nested (1, 0) and (2, 1) pass, (2, 0) and (5, 0) hang; nest3 with inner trip counts 0, 1 / 0, 1, 2 /
   0, 1, 2, 3 passes ((1, 2), (2, 1), (1, 3), (3, 1), (1, 4)) and 0, 1, 1, 0 / 0, 1, 2, 3, 0 hangs ((2, 2), (1, 5),
   (5, 1)). Each kernel passes with only `BDC_MERGE_OUT_LINK` on its loop-header control_merges (rule M's output
   link); for lfsrfind the result link alone and rule F's fork links alone do not fix it, for nest3 rule F alone does
   not, and deeper back-edge links (3 stages) fix neither. ring_tokens.py finds no short cycle in these three, so it is
   another mechanism, not diagnosed further. Routed (seed 1, gate at worst on a prefix of the vectors): nest3 default
   (bitstream EQUIVALENT) never completes (8, 8), so this one is in the circuit too; lfsrfind default hangs at the
      one-step search, but on a NOT EQUIVALENT bitstream (F7 class, below), so that route alone does not separate the
   two. gcd's inner ctz loop also has 0 trips after earlier instances (at
   diff == 0) and gcd passes, so the loop's shape matters. Rule M was adopted for speed; on these shapes the default
   flow is not live without it.
   **Explained and fixed (2026-11-18, research/data/suite/ringfloor.md): the same token / stage argument.** Each of the
   three has a fork-join pair where one path crosses a back edge (one more token) with fewer than 2 stages, through the
   loop-header control_merge (nested / nest3: only when an inner loop is skipped after the outer back edge was used,
   which is the hang condition above). Rule M's olink is a stage on every such path. The token floor adds the storage in
   the default flow (lfsrfind: a link on trueResult_14; nested: falseResult_17 -> 2; nest3: falseResult_17, _33 -> 2):
   simcheck PASS 10/10, 11/11, 12/12; BDC_AUTO output unchanged.
3. **Division and modulo do not compile.** `v % b` stops in Dynamatic's frontend (`lower-cf-to-handshake`: failed to
   legalize `arith.remui`), before bdc; `v / b` reaches bdc, which has no cell (`no width rule for handshake op
   'divui'`). LLVM did not fold digitdiv's `v - (v / b) * b` back into a remainder.
4. **BDC_AUTO=1 built in a copy of cells/ bdc/ build/frontend (research/data/alltable/run_default.sh's tree) silently
   skips the proven MLIR rewrites**: `bdc/auto.py` runs `research/tools/fifteen/pre_{dec,eq2}.py` relative to `bdc/`,
   and a failed subprocess is skipped. Checked: on xorshift, auto.py applies pre_dec from the repository and nothing
   from a copy of bdc/ alone (different outputs). An AUTO number for xorshift, collatz or collatz64 built that way
   lacks the rewrites. `research/tools/suite/smoke.sh` copies the two scripts into its AUTO tree (no effect on the
   suite kernels: the rewrites are proven only for those three kernels' exact MLIR).
5. **Routes** (seed 1, both flows; one seed is a smoke test). Where simcheck passes, the route's gate passed
   too, except two AUTO routes whose bitstreams carry the FFMUX defect (below); where simcheck deadlocks, the route
   hangs at the same vector
   (quadrec both flows, lfsrfind default, nest3 default, nested default).
      **NOT EQUIVALENT bitstreams: 10 of the 26 gated routes (9 distinct bitstreams: cmpchain's AUTO route is its
   default route).** fasm_equiv finds an F7AMUX / F7BMUX (yosys's wide-LUT split,
   `...genblk1.mux7`, some inside the kernel: `bridge_i.udut.uxori2`, `bridge_i.udut.ucontrol_merge4`) whose input
   nextpnr's netlist drives from a LUT reading constant 0 in the bits ("DRIVER DIFFERS"), or an F7A / F7B / F8 group
   with loads left unconfigured (cmpchain default). That is the journal's known F7 class (nextpnr / FASM, not bdc).
   Such a route is not a board candidate whatever its gate says.
   **Two AUTO routes return wrong answers, and both carry the known FFMUX bitstream defect**
   (`research/tools/ffmux_scan.py`: a flop nextpnr placed whose D-input mux has no bit; it flags lfsrfind AUTO at
   CLBLL_R_X11Y44 CFF and nest3 AUTO at CLBLM_R_X9Y5 BFF, and none of the other 24 routes). From some vector
   on, every call ends after exactly 259 cycles with a stale value, both runs agreeing (lfsrfind 2 of 10 right, nest3 4
   of 12). fasm_equiv on both: an FF with loads that the bits leave unconfigured
   (`$auto$dfflegalize.cc:410:emulate_split_set_clr`), a LUT input that nextpnr drives from that FF reading constant 1,
      one LUT function differing on 2 of 8 input assignments. simcheck AUTO passes both (12/12, 10/10). Gating nextpnr's
   own routed
   netlist instead of the bits would separate bitstream from design; `cells/gls/ps/build_ps.sh`'s json path fails on
      these benches (`cells/gls/gen.py` net_of_pin: `KeyError:
   '$flattenbridge_i.$ge$build/gen/lfsrfind_bench_gen.v:584$1307
   .genblk1.slice[2].genblk1.carry4'`), and bench_gate's worst / draw corners band delays by bel name, which only the
   bits-decoded netlist has, so it was not done. The FFMUX flag is the evidence that these two are the bitstream's.
   cmpchain AUTO's first build failed only on build_bench.sh's 420 s per-seed PnR timeout (the HeAP placer alone took
      398 s at load 80-110 on the shared node); rebuilt with PNR_TIMEOUT=1500: PASS 17/17, and its FASM is
   byte-identical to the default route's (so is straight's: on these two loop-free kernels BDC_AUTO changes only RFAST
   on links with no delay, which leaves the netlist alone).

## Waiting for the bench ABI

The bench (`cells/hw/gen_bench.py`, `cells/gls/ps/`) drives at most two 32-bit operand words and returns one 32-bit
result. memsum (an array argument) and any kernel with more than two words wait for the bench ABI work (another agent);
`oracle.sh` refuses them (exit 2) rather than guess. Kernels the bench masks (gcd, collatz, collatz64, xorshift) keep
their own oracles (`research/tools/fifteen/kernel_oracle.sh`, `research/data/gcd_draws/gcd_oracle.sh`); `oracle.sh`
refuses them too, because the bench changes their inputs.

## Notes on the C

- Every new kernel computes in `unsigned` where it wraps, so its C is defined over the whole declared range without
  -fwrapv. The oracle still compiles with -fwrapv (kernel_oracle.sh's recipe).
- `nested` (existing kernel): `acc = (acc ^ (acc << 3)) + i + j` on a signed int overflows for most inputs (undefined
  in C). Its expected values assume two's-complement wrap (-fwrapv), which is what the hardware computes; clang's
  frontend output was not checked for a transformation that relies on the overflow being impossible (simcheck
  AUTO agrees with the -fwrapv answers on all 11 vectors).
- `varshift`: `(int)acc >> s` of a negative value is implementation-defined in C; gcc (oracle) and clang (frontend)
  both shift in the sign.
- The declared ranges keep trip counts <= ~256 because the routed gate simulates ~0.2 us of circuit time per wall
  second on this node (measured: straight 31.3 us in 2.4 min; bandfit's ipow 31.8 us in ~2.4 min), and each vector
  runs twice.
- Vectors include 0, 1, the largest value of the declared range, 0 trips (for loops: n = 0 and n = INT_MIN), the
  int32 extremes on unrestricted arguments, and a few interior values. Inputs were picked with a quick model of trip
  counts (e.g. lfsrfind's keys at known LFSR positions); every expected value is the oracle's.
