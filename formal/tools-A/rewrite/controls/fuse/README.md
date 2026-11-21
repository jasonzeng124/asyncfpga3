# fuse_check.py controls (shard A, 2026-11-19)

A = collatz fixture imported unfused (BDC_OP_FUSION=0, BDC_FORK_FUSION=0); B = a mutated copy imported fused (default).
Each mutation changes what the graph computes; each must be refused.

| B | mutation | result |
|---|---|---|
| `collatz_shrui.mlir` | `shli0` (n << 1, in 3n + 1) replaced by a logical right shift | REFUSED (normal forms differ), rc 2 |
| `collatz_swapped_port.mlir` | `addi2` reads fork3's output #2 (shli's operand) instead of #1: one token read twice, one never | REFUSED (normal forms differ, 29 vs 30 rules), rc 2 |

Unmutated, the same pair is PROVED (fuse_census.txt, collatz unfused).
