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
pass recognises that and folds it back into a `divui`, which has no cell here
-- the kernel written specifically to avoid needing a divider ended up
demanding one. Shift-and-subtract long division is non-affine, so the idiom
matcher leaves it alone. If a future kernel fails with `no width rule for
handshake op 'divui'`, this is why.

## Adding one

Write `kernels/<name>/<name>.{c,h}` in the shape the shipped tests use (a
kernel function plus a `main` calling `CALL_KERNEL`), then add a reference
implementation and vectors to `bdc/simcheck.py`. The reference must be
transcribed from the C, not from the emitted MLIR or Verilog -- an answer that
shares assumptions with the thing it is checking is not a check.

    ./bdc/frontend.sh <name>
    python3 bdc/simcheck.py build/frontend/<name>/comp/handshake_transformed.mlir
