# Variable shifts with the amount masked: BDC_SHIFT_MASK (2026-11-22)

Research bot, session cluster-research-29671222-2.

## Why

varshift (flow v10 seed 1, 27.63 ns per iteration; Dynamatic's on-merges circuit 12.48) spends 14.8 ns of its critical
cycle in two shift operators' matched delay lines (ushrsi0: 19 element arcs, 8.4 ns; uxori2, fed by v >> k: 18, 6.4 ns).
bdc/compute.py lowered arith.shli / shrui / shrsi to `a << b` / `a >> b` / `$signed(a) >>> b` with b all 32 bits, so
yosys also builds the shift-by-32-or-more case.

## The circuit (yosys synth_xilinx, this toolchain; sh.v / sh2.v, depths.txt)

| shifter | topological depth (ltp -noff) |
|---|---|
| 32-bit, amount all 32 bits (>>>, >>, <<) | 13 / 14 / 14 |
| 32-bit, amount b[4:0] | 5 / 5 |
| 32-bit, amount (b & 31) | 5 / 5 / 5 |
| 64-bit, full amount / (b & 63) | 13 / 7 |

The masked forms also use about a sixth of the LUT / MUXF cells.

## Why it is legal

arith.shli / shrui / shrsi return poison when the amount is >= the bit width (C: the shift is undefined), so using the
low ceil(log2(width)) bits is a refinement of the operation. A literal amount folds either way and is left as it was.
Dynamatic's own units take the full amount (data/verilog/arith/shrui.v: `result = lhs >> rhs`), so its routed figures
pay for the wide shifter too.

## The knob

bdc BDC_SHIFT_MASK=1 (opt-in, 7e93d25ee): compute.binary_expr, used by the unit emitter and the fused-region emitter,
writes `(b & (2^k - 1))` for a non-literal amount. Unset: the emitted Verilog of all 62 suite kernels is byte-identical
to the previous bdc (BDC_AUTO=1). Set: only varshift (3 variable shifts) and gcd (1) change; every other kernel's shift
amounts are literals.

## Not shown yet

The loop with the knob (local A/B on varshift s1 under flow v13's environment, research/JOURNAL.md 2026-11-22);
gcd (its variable shift is the final u << shift, likely off the loop).
