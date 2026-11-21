# Vector files formal keeps itself (shard C)
- `col17.hex`: research's col17 (commit 69846249a; deleted on claude/research at 05:39 on 2026-11-17 because the BENCH masks
  collatz's n to 16 bits, cells/hw/gen_bench.py DOMAIN_RESTRICTIONS). Formal's simx drives the kernel boundary directly with
  the full 32-bit n, so these vectors are valid for formal: 77671, 94959, 109881 peak at 31 / 30 / 30 bits; expected step
  counts from kernels.py (formal/tools/margin/kernels.py, derived from kernels/collatz) 231 / 301 / 309. A formal PASS on
  them is a statement about the kernel, not about what the bench can feed it on the board.
- `c6418.hex`: research's c6418 (commit 8ca0b86fc; deleted on claude/research at 05:39 for the same reason: the bench forces
  collatz64's high word to 0). Lines are "lo hi"; formal drives n = hi:lo (64 bits) as "0xHILO,0xHILO" (mk_bnd_sim maps
  collatz64's one 64-bit operand to both slots). Expected step counts from kernels.py: last three 267 / 282 / 285 (= research's
  c6418.exp). Trajectories peak at 63 bits.
