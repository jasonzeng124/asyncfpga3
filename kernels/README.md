# kernels/

C kernels written for this backend, run by `bdc/frontend.sh <name>` exactly
like Dynamatic's shipped `integration-test/` ones. A directory here shadows a
same-named one there, and nothing in `dynamatic/` is touched.

## Why these exist

Dynamatic ships 95 integration tests, but almost all of them are polybench
array kernels, and this backend has no memory yet (Stage 6, `bd_mem`). Of the
four that were ever compiled here, only `gcd` and `test_loop_free` are
memory-free — so the shipped suite runs out after two kernels, and one of
those is a single if/else chain.

These are memory-free by construction and each was chosen to reach something
`gcd` does not.

| kernel | reaches | verdict |
|---|---|---|
| `collatz` | running time that is a wild function of the input value, not its size | simcheck PASS |
| `ipow` | `muli` -- the first variable x variable multiplies this backend has ever emitted | simcheck PASS |
| `xorshift` | `xori`, `shrui` -- unsigned bit-mixing, no arithmetic | simcheck PASS |
| `isprime` | a 4-input `control_merge`, 6 `merge`, 30 `cond_br`: a loop with two exits | simcheck PASS |
| `collatz64` | a 64-bit datapath | simcheck PASS |

## Two things these kernels established

**The backend is width-generic.** `collatz64` is `collatz` with `long long`,
and it runs end to end. Its 113383 vector matters: 113383 is the smallest n
whose Collatz trajectory leaves int32, so it is a vector the 32-bit kernel
cannot answer at all. It returns 247.

**You cannot avoid a divider by writing the division yourself.** `isprime`
originally did `r = n mod d` as `while (r >= d) r = r - d;`. LLVM's loop-idiom
pass recognises that and folds it back into a `divui`, which had no cell here
-- the kernel written specifically to avoid needing a divider ended up
demanding one. Shift-and-subtract long division is non-affine, so the idiom
matcher leaves it alone. (Since 2026-11-18 bdc builds divui / divsi / remsi /
remui: a restoring array, bdc/compute.py div_datapath, research/data/suite/divmod.md.)

## The suite

`kernels/SUITE.md` lists every kernel here as a compiler benchmark: its shape, its input range, its vectors, where its
expected values come from, and how far it gets (frontend, bdc, simcheck, a routed gate). Two more traps found writing
it: `%` on unsigned operands stops in Dynamatic's own frontend (`lower-cf-to-handshake` cannot legalize
`arith.remui`: Dynamatic's handshake dialect has divsi, remsi and divui but no remui); `BDC_FE_UREM=1 ./bdc/frontend.sh`
rewrites it as `x - (x / y) * y` (opt-in, research/data/suite/divmod.md). `/` lowers to `divui` / `divsi` and signed
`%` to `remsi`, which bdc builds since 2026-11-18. Not a trap but a cost: LLVM folds a rotate `(x << 1) | (x >> 31)` into
`llvm.fshl.i32`, which `translate-llvm-to-std` expands into shifts on an i64 concatenation (checked 2026-11-17: it
compiles and passes simcheck, on a datapath twice as wide), so the suite's shift kernels avoid that shape.

## Adding one

Write `kernels/<name>/<name>.{c,h}` in the shape the shipped tests use (a
kernel function plus a `main` calling `CALL_KERNEL`), with a header comment that
says what shape it exercises and the input range in which its C is defined.

A suite kernel (scalar arguments, at most two 32-bit words: the bench's ABI) needs
no Python transcription: its expected values come from its own C, compiled by
`research/tools/suite/oracle.sh` (gcc -O1 -fwrapv), on a bench-format vector file
`kernels/<name>/vec.hex`, and `bdc/simcheck.py --c-oracle` uses the same oracle:

    ./bdc/frontend.sh <name>
    research/tools/suite/oracle.sh <name> < kernels/<name>/vec.hex > kernels/<name>/vec.exp
    python3 research/tools/suite/veclint.py kernels/<name>/vec.hex kernels/<name>/vec.exp
    python3 bdc/simcheck.py build/frontend/<name>/comp/handshake_transformed.mlir --c-oracle

The older route still works: add a reference implementation and vectors to
`bdc/simcheck.py`'s REFS / VECTORS. The reference must be transcribed from the C,
not from the emitted MLIR or Verilog -- an answer that shares assumptions with
the thing it is checking is not a check.

    python3 bdc/simcheck.py build/frontend/<name>/comp/handshake_transformed.mlir
