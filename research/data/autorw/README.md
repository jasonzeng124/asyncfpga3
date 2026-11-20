# Proved loop-test rewrites in the automatic path (2026-11-20)

PROGRAM ("The automatic path must not carry a list of kernels"): a rewrite comes back into the automatic column when it
is a PASS -- it matches a structure on any kernel and what is proved is the pass, not an output file. Formal's shard A
has two: `formal/tools-A/rewrite/plain_pass.py` (the plain loop-test move `i + 1 < n -> i < n - 1`, PlainPass
certificate) and `eq2_pass.py` (the test on the update -> the test on the value, scripts of proved local steps). Each
matches by structure and writes its output only when Lean proves the rewritten graph equal to the input (token level,
every schedule); `auto_rewrites.sh` runs both.

## Census (default fixtures, claude/formal 2a34c3dfb, Lean v4.35.0, formal's farm lake cache)

`census.txt`. With `BDC_AUTO=1` as flow v8+ sets it (ring fusion on), plain_pass refuses every kernel ("0 matches of
the pattern in the import"): dfimport reads bdc's fusion plan, and ring fusion has already merged the increment with its
test. The import is therefore made with `BDC_RING_FUSE=0` (the proof is about the graph before ring fusion; ring fusion
is a separate rewrite of the emitted graph). Then:

- plain_pass PROVED: xorshift, countloop, twoloops, quadrec, horner, varshift;
- eq2_pass PROVED: collatz, collatz64;
- matched but refused (dfimport cannot import memory kernels): fill, if_loop_1, if_loop_2, test_memory_1, spmv;
- no match: the other 49.

The eight `*.mlir` here are those outputs; `research/tools/suite/suite_one.sh AUTO_PROVED_RW=1` (FORMAL_DIR = a built
claude/formal checkout) reproduces them byte for byte in the flow (checked: xorshift, collatz; gcd / fill -> none).
RTL bench against the C (`rtl_bench.sh RTL_MLIR=`): all eight PASS (xorshift 19/19, collatz 17/17, collatz64 18/18,
countloop 10/10, twoloops 11/11, quadrec 10/10, horner 11/11, varshift 10/10).

## A flow bug the first test exposed (fixed in 419115ec4)

`auto_size.sh` built every route from `MLIR_OVERRIDE` (lane2.sh) but took its START sizes from the original fixture's
emission. The rewritten graph's new fused cells therefore had no sizes macro and kept emit.py's generous defaults, which
no rule step lowers: on the first local loops (seed 1, flow v9) xorshift's uaddi0 sat at 24 elements (9.4 ns on the
cycle) and collatz's uselect0 at 86 (31.2 ns), untrimmed P 22275 / 50021 ps against suite13t's 18319 / 24676. The farm
request built on it (suite13t_s1c_arw) was withdrawn before it ran. No earlier request combined MLIR_OVERRIDE with the
sizing loop.

## Why the plain move needs a second pass under ring fusion: BDC_SIBLING_FUSE

Ring fusion (BDC_RING_FUSE=2, flow v8) fuses `x' = f(x); c = test(x')` into one cell. After the plain move the test
reads i itself, so ring fusion no longer applies: the increment and the test become two cells with a fork and links
between them. `bdc BDC_SIBLING_FUSE=1` (0218b747f, opt-in): a fork whose every output feeds fusable ops in two or more
regions merges them into one multi-result cell (one join, one matched delay over branches that now run side by side),
under ring fusion's three safety conditions. Unset: byte-identical emission. With the six plain-move MLIRs each kernel's
increment and test become one cell, and the six RTL benches pass. On the 62 default fixtures (no rewrite) it changes 23
kernels: a separate effect, to be measured.

## Measurements (to be filled)

| kernel, seed | flow | P untrimmed / trimmed (ps) | control: suite13t same seed | draws |
|---|---|---|---|---|
| xorshift s1 | v9 + trim (cycle scope) + plain move | (arw2, running) | 18319 / 17588 | |
| collatz s1 | v9 + trim (cycle scope) + eq2 | (arw2, running) | 24676 / 22751 | |
| xorshift s1 | v9 + trim (cycle scope) + plain move + BDC_SIBLING_FUSE | (sib, running) | 18319 / 17588 | |
