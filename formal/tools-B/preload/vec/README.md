# tools-B/preload/vec: full-range vectors (shard B, 2026-11-17)
Research's gate format (`OPERAND0 OPERAND1` hex per line; `.exp` = expected out0, from tools-B/preload/oracle.c at S0 = 0,
which copies kernels/<k>/<k>.c; checked equal to formal/tools/margin/kernels.py).
- `c64hi`: collatz64, 64-bit n (the first column is the whole 64-bit n, not a 32-bit word: formal's simx drives the kernel
  boundary, which is 64 bits wide; the bench's high-word mask is outside the kernel). 0x1555555555555555: 3n + 1 = 2^62
  (a 62-bit carry); 0x0555555555555555: 2^60; four odd 62-bit n whose trajectories peak in [2^62, 2^63) with no overflow.
- `c32hi`: collatz, 32-bit n outside the bench's 16-bit mask: 0x15555555 (3n + 1 = 2^30), 0x05555555, four n peaking
  between 0x543f31a8 and 0x746c9680 (< 2^31), and 0xee2f (col18's highest peak).
Preloaded counter runs (`prun.sh`) need an I0 / S0 in the oracle; see FOR-RESEARCH B2.
