# Dynamatic's integration tests through this compiler (triage, 2026-11-17)

PROGRAM.md, "A benchmark suite for the compiler": "Take Dynamatic's own integration tests too, the integer ones that
fit (`dynamatic/integration-test/`, 95 of them, sources only) ... Say which do not compile, and why." This is that
triage: every one of the 95 directories through `bdc/frontend.sh`, `bdc/emit.py` (default and `BDC_AUTO=1`) and,
where the signature allows, `cells/hw/gen_bench.py`. **Nothing was routed or simulated.** No expected values are
written here; the oracle (`research/tools/suite/oracle.sh`, another subagent) computes them from the C.

Tools: the frontend is the owner's build in `$HOME/dynamatic` (`dynamatic-opt` md5 0875db47e1f20161,
`translate-llvm-to-std` e95e3810f7c5f595, `clang` ee7246ced54bd436). yosys 0.62 from `$TC` was used only to
elaborate (`read_verilog; hierarchy -check`), never to synthesize. nextpnr was not run (`cells/verify/toolchain.sh`
passes, 9c732bc6303458df, for the record).

## Counts

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

## What blocks the rest: every refusal, not just the first

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

## The bench ABI (`cells/hw/gen_bench.py`)

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

## Suite candidates now: scalar, emit OK, bench fits

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

## Reproduce

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

## What this does not show

- That anything computes the right answer. Nothing was simulated, synthesized or routed; "emit OK" and "bench fits"
  are compile-level facts. "Unlocks N" is an upper bound for the same reason: the what-if shows only that no other
  stage of emit.py refuses.
- That `force-mc` is a correct substitute for the LSQ (open; see above).
- Area: `cnn` (seven-deep nest), the matrix kernels and anything with a combinational divider may not fit or route.
  The index arithmetic of every two-dimensional array is 64-bit in the frontend output (`i64` in the table: the
  row-major flattening's shifts and adds, which `--handshake-optimize-bitwidths` does not narrow).
- Dynamatic's own figures for these tests: none were obtained.

## All 95 directories

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
