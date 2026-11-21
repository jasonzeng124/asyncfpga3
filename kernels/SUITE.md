# The compiler benchmark suite

research/PROGRAM.md "A benchmark suite for the compiler" (owner, 2026-11-17): kernels chosen to cover shapes, not to
flatter the flow; each with an input range in which its C is defined, vectors that include the edges of that range,
and expected values computed from the C, never recorded from a run. Nothing in the flow is set for a suite kernel by
name. A kernel the compiler refuses, deadlocks on or gets wrong stays here, marked so: that is work for the compiler.

This file: the first scalar kernels, one per shape (suite agent `suitek`, 2026-11-17), plus the kernels that were
already here; then Dynamatic's integer tests and two more memory shapes (suite agent `suitew`, 2026-11-18, its own
section below the first table).

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
| nest3 | a loop nest three deep | three rings sharing a token; innermost bound (i ^ j) & 3, often 0 | a, b <= 8 (<= 8 + 64 + 96 iterations) | kernels/nest3/vec.hex (12) | oracle.sh | ok / ok | PASS 12/12 / PASS 12/12 (2026-11-18, hangs; was **deadlock** (vector 1) / PASS 12/12 before ringfloor's token floor) | **HANG** at vector 1 (FAIL 1/2), EQ, before the token floor; vectors 0-1 only (simcheck's deadlock prefix) | **WRONG** at vector 1,2,4,5,7,8,9,11 (FAIL 4/12), **NOT EQ**, FFMUX-flagged bitstream |
| twoloops | two loops in sequence | the second loop's trip count (x & 255) is the first loop's result | a any; n <= 128 (second loop <= 255) | kernels/twoloops/vec.hex (11) | oracle.sh | ok / ok | PASS 11/11 / PASS 11/11 | PASS 11/11, EQ | PASS 11/11, EQ |
| brhash | a branch inside a loop that if-conversion cannot remove | each arm 3 dependent steps: the MLIR keeps 6 merges and no select in the body | x any; n <= 256 | kernels/brhash/vec.hex (10) | oracle.sh | ok / ok | PASS 10/10 / PASS 10/10 | PASS 10/10, **NOT EQ** | PASS 10/10, EQ |
| lfsrfind | an early exit (a search with break) | a loop with two exits whose index meets after it; found test before the step | seed, key any (low 16 bits used); trips <= 256 | kernels/lfsrfind/vec.hex (10) | oracle.sh | ok / ok | PASS 10/10 / PASS 10/10 (2026-11-18, hangs; was **deadlock** (any search of >= 1 step) / PASS 10/10 before the token floor) | **HANG** at vector 1 (FAIL 1/2), **NOT EQ**, before the token floor; vectors 0-1 only (simcheck's deadlock prefix) | **WRONG** at vector 2,3,4,5,6,7,8,9 (FAIL 2/10), **NOT EQ**, FFMUX-flagged bitstream |
| quadrec | several live values across the back edge | a, b, c, d, i on one ring; a <- b <- c <- d are plain moves | x any; n <= 256 | kernels/quadrec/vec.hex (10) | oracle.sh | ok / ok | PASS 10/10 / PASS 10/10 (2026-11-18, hangs; was **deadlock** (vector 2, n = 4) in both flows before the token floor) | **HANG** at vector 2 (FAIL 2/3), EQ, before the token floor (ringfloor.md: 8 / 8 routes PASS after); vectors 0-2 only (simcheck's deadlock prefix) | **HANG** at vector 2 (FAIL 2/3), **NOT EQ**; vectors 0-2 only (simcheck's deadlock prefix) |
| horner | multiply (the DSP path) | a variable x variable muli on the loop-carried path | x any; n <= 256 | kernels/horner/vec.hex (11) | oracle.sh | ok / ok | PASS 11/11 / PASS 11/11 | PASS 11/11, EQ | PASS 11/11, EQ |
| fold64 | 64-bit arithmetic | i64 argument (two bench words), 64-bit add with carry across bit 31, shifts, compare (a select), constants | v any int64; trips = v & 255 | kernels/fold64/vec.hex (10) | oracle.sh | ok / ok | PASS 10/10 / PASS 10/10 | PASS 10/10, EQ | PASS 10/10, EQ |
| varshift | shifts by a variable amount | shli / shrui / shrsi by amounts from the loop state (barrel shifters on a ring) | x any; n <= 256 | kernels/varshift/vec.hex (10) | oracle.sh | ok / ok | PASS 10/10 / PASS 10/10 | PASS 10/10, **NOT EQ** | PASS 10/10, **NOT EQ** |
| cmpchain | a chain of compares | eq, slt, slt && slt, ugt, sge, ule: an if / else-if ladder (cond_br + 2 selects) | (x, y) any int32 | kernels/cmpchain/vec.hex (17; all 7 classes) | oracle.sh | ok / ok | PASS 17/17 / PASS 17/17 | PASS 17/17, **NOT EQ** | PASS 17/17, **NOT EQ** (same fasm as default) |
| digitsum | division / modulo | `v % b`, `v / b` by a variable divisor | x, base any (b < 2 means 10; trips <= 32) | kernels/digitsum/vec.hex (18: x = 0, 1, 0xffffffff, 2^31, 2^31 - 1; base 0 / 1 (-> 10), 2, 3, 7, 16, 2^16, 2^31, 0xfffffffe, 0xffffffff; x < base) | oracle.sh | default frontend: **frontend** `failed to legalize operation 'arith.remui'` (Dynamatic has no remui); `BDC_FE_UREM=1`: ok (its MLIR equals digitdiv's but for the name) / ok | PASS 18/18 / PASS 18/18 | = digitdiv's (same MLIR) | not run |
| digitdiv | division (remainder as v - q*b) | divui and a muli | x, base any (b < 2 means 10; trips <= 32) | kernels/digitdiv/vec.hex (18, digitsum's) | oracle.sh | ok / ok (bdc's divider, research/data/suite/divmod.md) | PASS 18/18 / PASS 18/18 | PASS 18/18, EQ (seeds 1-4: PASS 18/18 each, all EQ; nextpnr 6e5d224472232d5d; divmod.md) | not run (stopped: the rule's per-line audit, divmod.md) |
| divmodu | division / modulo, straight-line | divui (a variable divisor), the remainder a - q * b (BDC_FE_UREM=1): q + 2 * r = 2a + q(1 - 2b), so any wrong quotient shows | a any uint32; b != 0 | kernels/divmodu/vec.hex (20: a = 0, 1, 2^31, 2^31 - 1, 0xfffffffe, 0xffffffff; b = 1, 2, 3, 2^16, 2^31 - 1, 2^31, 2^31 + 1, 0xffffffff; a < b) | oracle.sh | `BDC_FE_UREM=1`: ok / ok | PASS 20/20 / PASS 20/20 | PASS 20/20, EQ (seeds 1-4: PASS 20/20 each, all EQ) | not run |
| divmods | signed division / modulo, straight-line | divsi and remsi (two dividers), q ^ r | a, b any int32 but b = 0 and (INT_MIN, -1) | kernels/divmods/vec.hex (24: INT_MIN / 1, 2, -2, 3, INT_MAX, INT_MIN; INT_MAX / INT_MIN, -1, 1, -3; -1 / INT_MIN, 1, -1; every sign pair of 7 / 2; 0 / -1; |a| < |b|) | oracle.sh | ok / ok | PASS 24/24 / PASS 24/24 | PASS 24/24, EQ (seeds 1-4: PASS 24/24 each, all EQ) | not run |
| nested | a loop nest two deep | two rings sharing a token | a, b <= 16 (trips a * b <= 256) | kernels/nested/vec.hex (11) | oracle.sh (-fwrapv: the C overflows int, see below) | ok / ok | PASS 11/11 / PASS 11/11 (2026-11-18, hangs; was **deadlock** (vector 3: (5, 0)) / PASS 11/11 before the token floor) | **HANG** at vector 3 (FAIL 3/4), **NOT EQ**, before the token floor; vectors 0-3 only (simcheck's deadlock prefix) | PASS 11/11, EQ |
| branchloop | a loop inside a branch inside a loop | an inner loop in one arm of a branch that survives if-conversion | n any int32 (<= ~64 steps) | kernels/branchloop/vec.hex (14) | oracle.sh | ok / ok | PASS 14/14 / PASS 14/14 | not run (time) | not run (time) |
| memsum | memory: read only | a load in a ring (mem_controller) | - | kernels/memsum/vec.hex (v2, 5 calls) | oracle_mem.sh | ok / ok (bdc emits) | RTL (memtb.py, 5 calls x 2 runs, arrays = C): PASS / PASS (2026-11-18, hangs) | waits for the bench ABI | waits for the bench ABI |
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
**Update 2026-11-18 (subagent `hangs`, research/data/suite/hangs.md): simcheck now PASSES on all 14 in both flows**
(quadrec, lfsrfind, nest3, nested fixed by ringfloor's token floor; re-measured here, every vector). The routed
columns above are the 2026-11-17 routes, built before the token floor.
(2026-11-18, subagent divmod: division and modulo now compile -- digitsum with `BDC_FE_UREM=1`, digitdiv in bdc;
item 3 below and research/data/suite/divmod.md.)

## Dynamatic's integer tests and two more memory shapes (suite agent `suitew`, 2026-11-18)

The 11 integer tests of Dynamatic's that emit through bdc besides gcd (research/data/suite/dyn/README.md), and two
read-only memory shapes the owner listed that were missing: two arrays (`dot2`) and an index read from memory
(`gather`). Dynamatic's C is in `research/data/suite/dynsrc/<name>/` (copied unchanged, with sha256s; a `kernels/`
directory would shadow the test in `bdc/frontend.sh`), its vectors in `research/data/suite/vec/<name>.hex`
(`suite_one.sh` and `rejudge.sh` look there after `kernels/<name>/`); the frontend output of all 13 is in
`cloud/fixtures/frontend/<name>/comp/`. Expected values are compiled from the C at run time by `oracle.sh` (two-word
files) or `oracle_mem.sh` (v2 files: more than two words, or arrays), never recorded.

Columns: **bdc** = `bdc/emit.py --no-top`, default / `BDC_AUTO=1` (auto.py first) / `--host-mem` (what the bench
builds); **simcheck** = `bdc/simcheck.py --c-oracle --timeout-us 400`, default / `BDC_AUTO=1` (pre-route, arc timing;
memory kernels are checked on the bench path only); **smoke** = ONE routed run of the automatic path,
`research/tools/suite/suite_one.sh K 1 2 3` (seed 1, 2 draws K = 10101 and 10102, MAXIT 3: up to 4 routes, then up to
3 raise-only routes when none was clean; CA_JOBS=2, PNR_TIMEOUT=3600), nextpnr 9c732bc6303458df (toolchain.sh all
ok). dot2, gather, test_bitint, iterative_sqrt ran the flow as committed before this section; test_loop_free,
unused_arg, test_int16 ran it with the bd_mem start-scale change (item 1), which touches only unused_arg's lines.
One seed is a smoke test, not a result.

| kernel | shape | input range (C defined, trips bounded) | vectors | expected values | bdc | simcheck default / AUTO | smoke (seed 1, 2 draws) |
|---|---|---|---|---|---|---|---|
| dot2 | memory: two arrays | n any (clamped to N = 32; n <= 0: 0 trips); a[i], b[i] in [-8191, 8191] | kernels/dot2/vec.hex (v2, 8 calls): n = 32, 1, 0, 31, INT_MAX, INT_MIN; a = b = 8191 (2146959392), a = -b (-2146959392), ramps, random | oracle_mem.sh (kernels/dot2) | ok / ok / ok | RTL (memtb.py, 8 calls x 2 runs, arrays = C): PASS / PASS (2026-11-18, hangs) | **PASS 2/2 draws** (8/8 each), EQUIVALENT, ffmux clean; rule NOT CLEAN at it 6 (raise-only phase ran out: bd_mem C -1.5 .. -2.3 ns on 4 RAMs, unfixable); route 16751b81, 1410 LUTs, 840 ns per call (median); P printed 156000 ps (not checked) |
| gather | memory: an index read from memory, a[b[i]] | n any (clamped to 32); b[i] in [0, 31]; a[j] in [-2^21, 2^21] | kernels/gather/vec.hex (v2, 9 calls): b all 0, all 31, identity, reversed, random; a = +-2^21 everywhere (+-1107296256); n = 32, 33, 1, 0, INT_MIN, INT_MAX | oracle_mem.sh (kernels/gather) | ok / ok / ok | RTL (memtb.py, 9 calls x 2 runs, arrays = C): PASS / PASS (2026-11-18, hangs) | **FAIL 0/2 draws** (3/9 each: xxxxxxxx on the 6 calls that read a[j] with j != 0; right on n = 0, n = INT_MIN and b all 0), EQUIVALENT, ffmux clean; rule NOT CLEAN at it 5 (bd_mem B -2.4 .. -4.6 ns on the dependent load's RAM address, C -1.2 .. -2.6 ns; unfixable); route 9afa161e, 1429 LUTs. Diagnostic, not the flow: the same seed and sizes with bd_mem's lines at USETUP 20 / UCO 16 (route 6da7a61c): the full-stack run returns 9/9 right and draws 10101 / 10102 PASS 9/9 each, EQUIVALENT (item 1) |
| factorial | two loops in sequence, the first unrolled x3: 4 muli | n <= 12 (13! overflows int); n <= 0: both loops 0 trips, 1 | vec/factorial.hex (12): 12, 11, 10, 7, 5, 4, 3, 2, 1, 0, -1, INT_MIN | oracle.sh (dynsrc) | ok / ok / ok | PASS 12/12 / PASS 12/12 | not run (time) |
| iterative_division | repeated subtraction, signs around the loop, an early return on divisor 0 | dividend, divisor != INT_MIN (ABS overflows); quotient \|dividend\| / \|divisor\| <= 256 (trips) | vec/iterative_division.hex (15): divisor 0; 0, 1, 255, 256 trips; every sign pair; INT_MAX / INT_MAX, INT_MAX / (INT_MAX - 1), -INT_MAX / INT_MAX (-1), INT_MAX / 2^23 | oracle.sh (dynsrc) | ok / ok / ok | PASS 15/15 / PASS 15/15 | not run (time) |
| iterative_sqrt | binary search, an early exit on an exact square, mid * mid twice | n <= 92681 (mid * mid overflows above); n < 0: 0 trips, returns n | vec/iterative_sqrt.hex (12): 92681, 92680, 92416 (304^2), 65536, 99, 4, 3, 2, 1, 0, -1, INT_MIN | oracle.sh (dynsrc) | ok / ok / ok | PASS 12/12 / PASS 12/12 | not finished: stopped during it 2's audit to free the slot (time box; it 1: 22 negative, 10 raised, 2 unfixable) |
| test_loop_free | loop-free, three branches, 4 operand words | a > 0: b + c + d in range; a <= 0, b < 0: a + d in range | vec/test_loop_free.hex (v2 words=4 mems=0, 10 calls): every branch; a in {INT_MIN, -1, 0, 1, 5, INT_MAX}; b in {INT_MIN, -2^30, -1, 0, 2^30, INT_MAX}; sums at INT_MAX, INT_MIN, INT_MIN + 1 | oracle_mem.sh (dynsrc) | ok / ok / ok | PASS 10/10 / PASS 10/10 | **PASS 2/2 draws** (10/10 each), EQUIVALENT, ffmux clean; rule NOT CLEAN after 6 routes (the raise-only phase kept finding 2-5 small misses: umux0 / uselect0 / uaddi1 / one H, -8 .. -642 ps; steers' D -2.9 .. -3.4 ns, reported only); route 0a543d6b, 988 LUTs, 72 ns per call (median) |
| test_int16 | no argument; a 16-bit result (-1) | - (no input) | vec/test_int16.hex (1; the words are ignored) | oracle.sh (dynsrc): 0000ffff (masked: the bench zero-extends) | ok / ok / ok | PASS 1/1 / PASS 1/1 (2026-11-18, hangs; srcjoin's call join; was **FAIL** (timeout) / **FAIL** (timeout): out0 fired 94162 times for one start) | **FLOW-FAILED**, reported as `status=DOES-NOT-COMPILE ()`: auto_size.sh stops at the estimates, `est_sizes.py: no module bdc_test_int16 with parameters` (a kernel with no matched delay; bdc itself emits it) |
| test_divui | a `divui` by the constant 1083 (Dynamatic's test) | every uint32 | research/data/suite/vec/test_divui.hex (12: 1084, 0, 1082, 1083, 2166, 2165, 2^31 - 1, 2^31, 0xffffffff, 0xdeadbeef, 1083007, 1) | oracle.sh (dynsrc: Dynamatic's C) | ok / ok / ok (since 2026-11-18, divmod.md) | PASS 12/12 / PASS 12/12 | not run |
| test_bitint | memory: two narrow arrays (u16, u5), _BitInt, muli i21 | every element value (unsigned; 10 x 65535 x 31 < 2^32) | vec/test_bitint.hex (v2, 6 calls): all 65535 x all 31 (20315850), Dynamatic's main (1..10 x 10..1: 220), alternating pairs, random | oracle_mem.sh (dynsrc, clang: gcc 13 has no _BitInt) | ok / ok / ok | RTL (memtb.py, 6 calls x 2 runs, arrays = C): PASS / PASS (2026-11-18, hangs) | **PASS 2/2 draws** (6/6 each), EQUIVALENT, ffmux clean; rule NOT CLEAN at it 2 (bd_mem's C -1.2 .. -1.9 ns, B -5 / -44 ps, unfixable: see the note below); route b226e535, 610 LUTs, 252 ns per call (median); P not computed |
| unused_arg | memory: one load at a constant address, no loop; the frontend drops the unused array `a` (keeps a_start / a_end) | any | vec/unused_arg.hex (v2, 6 calls): used[0] = INT_MAX, INT_MIN, 1, -1, 0x13579bdf, 0; b varied (unused) | oracle_mem.sh (dynsrc; `a` absent from the file: filled two ways, must not matter) | ok / ok / ok | RTL (memtb.py, 6 calls x 2 runs, arrays = C): PASS / PASS (2026-11-18, hangs) | **FLOW-FAILED** (`RULE FAILED it=0`): tighten.py, `combinational cycle with no storage` -- the cycle is the kernel's `usource0` and the bench's a_end sink: the frontend drives the dropped memref's memEnd (a_end) from a `source`, bdc wires it to the port, and a source acknowledged by a delay is a ring oscillator (built with the bd_mem start-scale change, which does not touch this) |
| if_loop_1 | memory: load, multiply by 5, a branch (tmp > 10) in a loop to n | n <= 100 (the C does not clamp: n > 100 reads past a); a[i] in [-4294967, 4294967] | vec/if_loop_1.hex (v2, 8 calls): n = 100, 99, 50, 1, 0, INT_MIN; a = 4294967 everywhere (2147483500), 2 / 3 alternating (the compare's edge: 750), random | oracle_mem.sh (dynsrc) | ok / ok / ok | RTL (memtb.py, 8 calls x 2 runs, arrays = C): PASS / PASS (2026-11-18, hangs) | not run (time) |
| if_loop_2 | memory: if_loop_1 without the multiply | n <= 100; a[i] <= 21474836 (any negative) | vec/if_loop_2.hex (v2, 8 calls): a = 21474836 everywhere (2147483600), 10 / 11 alternating (550), INT_MIN / 21474836 alternating, random; n as if_loop_1 | oracle_mem.sh (dynsrc) | ok / ok / ok | RTL (memtb.py, 8 calls x 2 runs, arrays = C): PASS / PASS (2026-11-18, hangs) | not run (time) |
| sumi3_mem | memory: x * x * x summed over N = 1000 | a[i] in [-129, 129] (1000 x 129^3 = 2146689000) | vec/sumi3_mem.hex (v2, 3 calls): all 129, all -129, the ramp -129..129 repeated | oracle_mem.sh (dynsrc) | ok / ok / ok | RTL (memtb.py, 3 calls x 2 runs, arrays = C): PASS / PASS (2026-11-18, hangs) | not run (time; estimated 0.2 ms of circuit time per call in the gate, the host fill alone ~0.16 ms) |
| fir | memory: two arrays, one read backwards (di[999 - i]), N = 1000 | elements in [-1465, 1465] (1000 x 1465^2 = 2146225000) | vec/fir.hex (v2, 2 calls): all 1465 (2146225000); di = idx = 0, 1, ..., 999 (166167000; read forwards it would be 332833500) | oracle_mem.sh (dynsrc) | ok / ok / ok | RTL (memtb.py, 2 calls x 2 runs, arrays = C): PASS / PASS (2026-11-18, hangs) | not run (time; estimated 0.4 ms of circuit time per call in the gate, the host fill alone ~0.31 ms) |


**Summary (2026-11-18, seed 1).** 13 kernels: all 13 pass Dynamatic's frontend and bdc in both flows (and
`--host-mem`). simcheck (the 5 scalar ones): 4 / 5 pass in both flows; test_int16 hangs (free-running out0, item 2).
Routed smoke, automatic path, seed 1, 2 draws: **PASS** dot2, test_bitint, test_loop_free (2 / 2 each); **FAIL**
gather (0 / 2, bd_mem's address setup, item 1); **FLOW-FAILED** unused_arg (the rule refuses a source-sink ring,
item 2) and test_int16 (no delay line, item 6); iterative_sqrt stopped unfinished; 6 not run (time). No route ended
CLEAN under the rule; every bitstream EQUIVALENT and ffmux clean.

**What this found (seed 1; one route per kernel is a smoke test, not a result).**

1. **The automatic path ships every memory kernel with bd_mem's two lines shrunk, and its rule cannot size them;
   gather fails on it.** auto_size.sh starts from emit.py's estimates x AUTO_START_SCALE 0.3, bd_mem's address setup
   (DSETUP 8 -> 3) and clock-to-out / address hold (DCO 12 -> 4; bdc/mem.py: "DCO IS THE ADDRESS HOLD GUARD")
   included. corner_audit's rule names those chains `<port>_uport.umem<k>.{usetup,uco}` (BD_SZ_..._UPORT_UMEM0_UCO),
   emit.py's macros are BD_SZ_..._UMEM0_UCO: the rule prints "sizes.vh does not set (kept, measured)", lists the
   RAMs' B / C constraints as STILL SHORT with no line to pad, and every route keeps 3 / 4 (checked in the routed
   netlists: 3 / 4 cells). On every route built here (corners 0.20 / 0.31): test_bitint C -1181 .. -1893 ps, B -5 /
   -44 ps; dot2 C -1525 .. -2270 ps; gather C -1207 .. -2625 ps and B -2443 .. -4590 ps (the dependent load's
   address, ADDRARDADDR6, reaches the RAM 5.9 - 6.9 ns after the request, the manufactured clock edge 2.6 - 3.6 ns).
   test_bitint and dot2 pass their draws anyway; **gather does not** (both draws 3/9, the RAM returns X for every
   a[j] with j != 0). Diagnostic, not the flow: gather's final sizes with only bd_mem's lines raised (USETUP 20,
   UCO 16; seed 1, route 6da7a61c, EQUIVALENT): the full-stack run 9/9, and draws 10101 and 10102 (the draws that gave 3/9) PASS 9/9 each.
   A loop that can never be clean also runs its raise-only phase to the end (dot2 6 routes, gather 5).
   Proposed (commit "auto_size.sh: do not shrink bd_mem's USETUP / UCO at the start"): keep the two lines at the
   estimates, where suiteb measured positive B / C on memsum and fir (24 RAMs). Not enough for gather (its B is
   still about 0.6 - 2.7 ns short at DSETUP 8 by the same arithmetic): the line needs one name in emit.py and
   corner_audit.py so the rule can size it. Work for the flow.
2. **A `source` that reaches a function result is free-running (test_int16, unused_arg).** bdc lowers `source` to
   `bd_src` and `end` to wires (emit.py `_op_end`: each result is assigned to its port, no join with the call), so a
   result that depends on a `source` and on nothing else produces tokens without a call. test_int16 (`return -1`:
   out0 = `constant(source)`): simcheck FAIL (timeout) in both flows, out0 seen 94162 times for one start in 400 us.
   unused_arg: the frontend drops the unread memref `a` and drives its memEnd (`a_end`) from a `source`; the bench
   acknowledges `a_end` with a bd_delay, so source and sink form a ring oscillator, and the rule refuses the route
   (tighten.py `combinational cycle with no storage`: usource0 and ua_end_snk). Dynamatic's `end` is wires too (no
   end.v in its handshake library); in its clocked semantics such an output is simply valid every cycle. bdc needs a
   result tied to the call (joined with start; for a dropped memref, memEnd = its memStart). Work for the compiler.
   **Fixed in bdc (2026-11-18, research/data/suite/srcjoin.md): a result no call bounds is joined with the call's
   bounded control results.** emit.py finds the results whose tokens no call bounds (a least fixpoint over tokens:
   test_int16's out0, unused_arg's a_end, and gaussian's out0, which bdc refuses earlier at lsq) and joins each with a
   copy of every control result the call bounds (`end`, which Dynamatic makes start itself, and each memory's end) --
   what Dynamatic's testbench join waits for. --no-top output of the 107 fixtures, four ways: only test_int16 and
   unused_arg change; BDC_CALL_JOIN=0 restores the old wiring byte for byte. simcheck test_int16 PASS 1/1 and 6/6 in
   both flows (the old wiring: the same timeout, 94162 tokens). Routed smoke (suite_one.sh K 1 2 3, nextpnr
   6e5d224472232d5d): test_int16 PASS 2/2 draws (CLEAN it=0, nothing to size), unused_arg PASS 2/2 draws (6/6 each,
   CLEAN it=1), both EQUIVALENT, ffmux clean; with BDC_CALL_JOIN=0 both stop at the rule again (combinational cycle
   with no storage). One seed each: a smoke test.
3. **The oracles.** All 13 kernels' answers come from their C in a tree without `dynamatic/` (checked: identical to
   the answers with it). Four of Dynamatic's tests have no header (types in the .c: compiled into the driver), use
   `int main()` (renamed too), and test_bitint needs clang (`_BitInt`; gcc 13 has none): a machine without clang gives
   NO-ORACLE for it. unused_arg: the frontend drops the unused memref `a` but keeps `a_start` / `a_end`, so the bench
   has one memory and the C two; oracle_mem.sh reads the memrefs the frontend kept and fills a dropped array twice,
   refusing a call whose answer changes (negative control: dot2 with `b` dropped refuses n = 32, answers n <= 0).
4. **veclint.py reads only the two-word format.** The v2 files' answers were checked by hand against its rules (no two
   consecutive answers equal, at most a quarter 0): all pass. test_int16 has one vector (every answer is 0000ffff).
5. **lane2.sh on a fresh RUNS** failed at its lock (`RUNS/wt` missing) and suite_one.sh reported
   `status=DOES-NOT-COMPILE ()` for three kernels that compile; lane2.sh now creates the directory.
6. **A kernel with no delay line cannot enter the automatic path.** test_int16 emits (bdc: 0 matched delays), but
   auto_size.sh's estimates step stops (`est_sizes.py: no module bdc_test_int16 with parameters`) and suite_one.sh
   reports it as `status=DOES-NOT-COMPILE ()`. Not changed here (the kernel is wrong anyway, item 2).
   **Fixed (2026-11-18, srcjoin.md):** est_sizes.py writes a sizes file with no lines for a kernel with no matched
   delay, and auto_size.sh builds such a kernel once and judges that route (`CLEAN it=0 ... (nothing to size)` or
   `NOT CLEAN it=0`); test_int16 (still 0 delays after item 2's fix) goes through.

## A kernel that writes memory (subagent `stores`, 2026-11-18)

bdc now lowers a memory controller with a store (research/data/suite/stores.md): each block's outgoing control token
joins its stores' completions, so ctrlEnd, memEnd and the call's result come after every store has landed. `fill`
is the owner's "memory: write" shape. The read-modify-write shapes (a histogram, `a[i] = f(a[i])`) need a load and a
store on one array, which bdc does not build yet (stores.md, open problems).

| kernel | shape | input range (C defined, trips bounded) | vectors | expected values | bdc | simcheck | routed |
|---|---|---|---|---|---|---|---|
| fill | memory: written; one store in a loop, the index loop-carried (3, 10, 17, ... step 7 mod 32), n > 32 overwrites | n any (n <= 0: 0 trips; the index wraps, so any n stays in bounds); x any (wraps, -fwrapv) | kernels/fill/vec.hex (v2, 5 calls): (n, x) = (32, 0x12345678), (40, 0xdeadbeef), (7, -5), (1, 1), (0, 0x02468ace); a[] uniform in [-1000, 1000] | oracle_mem.sh (kernels/fill), final arrays with ORACLE_MEMOUT | ok / ok / ok | - (bench only; RTL research/tools/suite/tb_store1.v: 10/10 runs, arrays = C; memtb.py 5 calls x 2 runs, both flows: PASS, 2026-11-18, hangs) | default flow (run_default.sh's flags), worst: SEEDS-ROW; automatic path: AUTO-ROW |

## Every kernel that emits, both flows (subagent `hangs`, 2026-11-18)

research/data/suite/hangs.md has the commands and the per-kernel table. All 45 fixtures that emit (45 of 108; the 63
others are refused by bdc, unchanged), default and `BDC_AUTO=1`: scalar kernels through `bdc/simcheck.py --c-oracle`
(gcd, collatz, collatz64, xorshift through its REFS), memory kernels through `research/tools/suite/memtb.py` (RTL:
every array filled through its host slot, 2 runs per call, out0 and every array read back against the C).
Dynamatic's nine store tests have vectors now (research/data/suite/vec/: if_convert, loop_path, matrix, nested_loop,
simple_example_1, single_loop, stencil_2d, test_flatten_array, while_loop_3); the eight void ones cannot go on the
bench yet, so RTL is all they have; stencil_2d can (routed smoke below).

| kernels | default | BDC_AUTO |
|---|---|---|
| the 26 scalar kernels (the 14 above, the 6 originals, factorial, iterative_division, iterative_sqrt, test_loop_free, test_int16, sum3) | PASS, every vector | PASS, every vector |
| memsum, dot2, gather, fill, test_bitint, unused_arg, if_loop_1, if_loop_2, sumi3_mem, fir | PASS (arrays = C) | PASS |
| simple_example_1, while_loop_3, if_convert, test_flatten_array, loop_path, single_loop, nested_loop | PASS (arrays = C) | PASS |
| stencil_2d (memory, a three-deep nest) | **DEADLOCK** at the first call before; **PASS** with the token floor's pass-through modes. Routed smoke (seed 1, worst, nextpnr 6e5d224472232d5d): PASS 2/2 with the arrays = C (sdf b5afb083, EQUIVALENT, ANNOTATE_DONE 0); with `BDC_TOKEN_FLOOR_PASS=0` FAIL 0/2, both calls hang (sdf a9e684aa, EQUIVALENT) | PASS |
| matrix (void, a three-deep nest with a store) | **DEADLOCK** after its first inner loop before; **PASS** with the pass-through modes (call 0, 27000 trips, outC 900 / 900 = C) | PASS (stores.md, 1 call) |

## Dynamatic's tests with stores and with a load first (subagent `dyntests`, 2026-11-18)

The bench now takes a void kernel (a call completes on `end` and every memEnd; the result is the arrays read back) and
bdc lowers a controller whose first accessor is a load (research/data/suite/dyn/README.md, sections 1 and 3). 22 of
Dynamatic's tests join the suite (research/tools/suite/kernels.txt); `matrix` emits and runs in RTL but does not fit
the decoded-netlist gate (27000 multiply-adds and 5400 host words per call). C: research/data/suite/dynsrc/; vectors:
research/tools/suite/dyn_vecs.sh (every written array filled with values the kernel does not write; every file passes
oracle_mem.sh `ORACLE_UBCHECK=1`); `<name>_rtl.hex` holds calls too long for the gate. Expected values: oracle_mem.sh
(the C). In place (an array read, then written): one run per call (`GATE_NRUNS=1`), marked (1).

| kernel | shape | input range (C defined) | vectors (calls; gate file / RTL file) | RTL default / AUTO | routed (seed 1, worst) |
|---|---|---|---|---|---|
| simple_example_1 | memory: written; the frontend folds the 100-trip count, one store of the constant 100 into a[0] in the exit block (the ctrlEnd form of the store lowering); void | any a[] | vec/simple_example_1.hex (4) | PASS 4/4 / PASS 4/4 | default: **PASS 4/4**, EQUIVALENT, 113.34 MHz, .bit 527e6eca |
| while_loop_3 | a data-dependent trip count (i*i < bound), the store after the loop in the exit block; void | bound <= 46340^2 = 2147395600 (i*i in int); bound <= 0: 0 trips | vec/while_loop_3.hex (7) / while_loop_3_rtl.hex (4) | PASS 7/7 / PASS 7/7 | default: **PASS 7/7**, EQUIVALENT, 96.07 MHz, .bit 4ff29dab |
| if_convert | a do-while whose step (1 or 2) depends on a[i] (if-converted), writes b[i] = 1 at the new i; void | \|a[i]\| <= 10845877 (198*a[i] in int); a[198] >= 51 wherever i can stand at 198 (else b[200] is written) | vec/if_convert.hex (3) / if_convert_rtl.hex (5) | PASS 5/5 / PASS 3/3 | default: **PASS 3/3**, EQUIVALENT, 94.18 MHz, .bit aaca3a50 |
| test_memory_1 (1) | LS read-modify-write a[i] += 5, N = 4; void | n <= 4; a[i] <= INT_MAX - 5 | vec/test_memory_1.hex (6) | PASS 6/6 / PASS 6/6 | default: **PASS 6/6**, EQUIVALENT, 107.71 MHz, .bit 45868bb0 |
| test_memory_2 (1) | LS: load a[i+1], store a[i] (+5), N = 5; void | n <= 5, n > INT_MIN; a[1..4] <= INT_MAX - 5 | vec/test_memory_2.hex (7) | PASS 7/7 / PASS 7/7 | default: **PASS 7/7**, EQUIVALENT, 108.47 MHz, .bit 8fab6141 |
| test_bool_array | LL, no loop: a[0] \|\| a[1] over _Bool (memref i8) | a[i] in {0, 1} | vec/test_bool_array.hex (4) | PASS 4/4 / PASS 4/4 | default: **PASS 4/4**, EQUIVALENT, 101.98 MHz, .bit 5f16960b |
| binary_search | LL across two loops (each with a break): the first even index holding search, else the first odd, else -1 | any | vec/binary_search.hex (7) | PASS 7/7 / PASS 7/7 | default: **PASS 7/7**, EQUIVALENT, 116.33 MHz, .bit d97c1cb0 |
| mul_example (1) | LS a[i] = a[i]^3, N = 100 (two muli); void | \|a[i]\| <= 1290 | vec/mul_example.hex (3) | PASS 3/3 / PASS 3/3 | default: **PASS 3/3**, EQUIVALENT, 114.67 MHz, .bit 52993095 |
| share_test_2 (1) | LS, four muli, an accumulator; void | none: signed overflow for EVERY input (acc*i*456784 at i = 1); expected values are -fwrapv's | vec/share_test_2.hex (3) | PASS 3/3 / PASS 3/3 | default: **NOT-JUDGED decoder-refused:**, 84.32 MHz, .bit 2923e64f |
| test_stdint (1) | LS on int8_t: a[i] = a[i]^3 + b, an i8 scalar argument; void | any (x^3 fits int; the int8_t narrowing is gcc's modulo) | vec/test_stdint.hex (4) | PASS 4/4 / PASS 4/4 | default: **PASS 4/4**, EQUIVALENT, 111.77 MHz, .bit e3340403 |
| spmv | CSR sparse matrix-vector product: LL on row[], an index read from memory (vec[col[c]]), a store per row, an inner loop with 0+ trips | n <= 10, 0 <= row[i] <= 10, col[c] in [0, 9]; \|val*vec\|*10 <= INT_MAX | vec/spmv.hex (4) | FAIL 3/4 / PASS 4/4 | auto: **PASS 4/4**, EQUIVALENT, 100.69 MHz, .bit 64dc0da7 |
| sobel | LL on in[], two 9-tap sums clamped to [0, 255], out[x+y] written, 15x15 outer, 3x3 inner | \|in\|, \|g\| <= 15446 | vec/sobel.hex (3) | FAIL 0/3 / PASS 3/3 | not run (time) |
| test_flatten_array | a triple nest over [4][8][16], output = input reversed in the two inner dimensions; void | any | vec/test_flatten_array.hex (1) / test_flatten_array_rtl.hex (2) | PASS 2/2 / PASS 1/1 | default: **PASS 1/1**, NOT EQUIVALENT, 103.16 MHz, .bit 4772e0fa |
| image_resize (1) | LS on a 30x30 array: a = c - a; void | c - a in int | vec/image_resize.hex (2) / image_resize_rtl.hex (4) | PASS 4/4 / PASS 2/2 | not run (time) |
| vector_rescale (1) | LS a[i] *= c, N = 1000; void | \|a[i]*c\| <= INT_MAX | vec/vector_rescale.hex (2) / vector_rescale_rtl.hex (4) | PASS 4/4 / PASS 2/2 | not run (time) |
| stencil_2d | a triple nest, 3x3 filter over a 30-wide row, sol[c] written, returns the last sum | \|orig\|, \|filter\| <= 15446 | vec/stencil_2d.hex (1) / stencil_2d_rtl.hex (4) | FAIL 0/4 / PASS 1/1 | auto: **PASS 1/1**, EQUIVALENT, 99.33 MHz, .bit 731b66ec |
| iir | L (y[0], before the loop) then S (y[i], in it) on one array: tmp = a*tmp + b*x[i], returns tmp | a in {0, 1, -1}; \|b x[i]\|*1000 + \|y[0]\| <= INT_MAX | vec/iir.hex (1) / iir_rtl.hex (3) | PASS 3/3 / PASS 1/1 | not run (time) |
| share_test_1 | LL on each of two arrays across two loops (a[i] and a[999-i]), returns the sum | \|a\|, \|b\| <= 598 | vec/share_test_1.hex (1) / share_test_1_rtl.hex (3) | PASS 3/3 / PASS 1/1 | not run (time) |
| single_loop | do-while: c[i] = a[i]*b[i] until the product reaches 1000; three 1000-word arrays; void | some i <= 999 with a[i]*b[i] >= 1000; \|a\|, \|b\| <= 46340 | vec/single_loop.hex (1) / single_loop_rtl.hex (5) | PASS 5/5 / PASS 1/1 | default: **PASS 1/1**, EQUIVALENT, 96.24 MHz, .bit 3909d514 |
| loop_path | do-while: c[i] = a[i]+b[i] until 6(a[i]+b[i]) >= 1000 or i = 1000; void | \|a[i]+b[i]\| <= 429496729 | vec/loop_path.hex (1) / loop_path_rtl.hex (4) | PASS 4/4 / PASS 1/1 | not run (time) |
| nested_loop | two passes of single_loop's do-while, writing c[i] and c[i+400]; void | the exit by i = 599; \|a\|, \|b\| <= 46340 | vec/nested_loop.hex (1) / nested_loop_rtl.hex (4) | PASS 4/4 / PASS 1/1 | not run (time) |
| video_filter (1) | three LS ports on three 30x30 arrays: p = ((p - offset) * scale) >> 4; void | \|p - offset\| * \|scale\| <= INT_MAX | vec/video_filter.hex (1) / video_filter_rtl.hex (3) | PASS 3/3 / PASS 1/1 | not run (time) |

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
   **Fixed (2026-11-18, research/data/suite/divmod.md):** bdc builds divui / divsi / remsi / remui (a restoring array
   of W subtract-and-select stages, one matched delay, no new cell), and `BDC_FE_UREM=1 ./bdc/frontend.sh` rewrites
   an unsigned `%` as `x - (x / y) * y` (opt-in; with it on, the other 108 fixtures come out byte-identical).
   digitsum, digitdiv, divmodu, divmods and Dynamatic's test_divui pass simcheck in both flows. Routed (default
   flow, placeholder sizes, nextpnr 6e5d224472232d5d, gate at worst): digitdiv, divmods and divmodu each PASS on 4 of
   4 seeds, every bitstream EQUIVALENT. The routed GLS could not run the first, ungated array (a 32-stage ripple
   multiplies the GLS's transport-delay glitches: one divide did not finish in 20 minutes), so each stage is now gated
   by an enable chain. The automatic path was not run to the end (stopped in its first rule step).
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

6. **An inner loop's last trip and its next entry deadlocked in the default flow (matrix, stencil_2d; 2026-11-18,
   subagent `hangs`, research/data/suite/hangs.md).** The token floor's walks saw every loop iterating and never
   walked a loop's entry or exit, so the outer loop's ring through an inner loop was never checked: the inner
   header's control_merge cannot return to zero until the inner loop's next initial value (one link stage) is taken
   by the header mux, whose select is that control_merge's next index (0 tokens). The floor now also walks, for every
   loop with a loop nested in it, the mode where the inner loops pass through in one trip, and adds one stage there
   (matrix `ulink_n26`, stencil_2d `ulink_n45`); every other fixture's output is byte-identical; BDC_AUTO already had
   rule M's link there. `BDC_TOKEN_FLOOR_PASS=0` = the old output (the negative control, deadlocks).

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
