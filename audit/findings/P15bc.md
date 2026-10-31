# P15bc: audit of formal shards B and C, commits 0780fd30..f40e003a

Code under test: checkout of formal commit f40e003a in /root/wt-f14 (read only). Auditor files:
/home/user/asyncfpga3/audit/lean/P15/BC_*. git not touched.

STATUS: in progress (Python checks done; lake build of f40e003a still running, Lean items pending).

## Summary table

| # | claim | verdict | one-line reason |
|---|---|---|---|
| C1 | e6f97308/502da4fe: H_COMPUTE_FN for all 20 gcd_hw units (ushli0 for k<32), every input | (pending Lean) | Python: all 20 Lean netlists = committed fixture AND independent build, cell for cell; own sim 0 mismatches vs specs written from bdc's Verilog |
| C2 | e6f97308: GcdJoin "20 joins = unit functions" | (pending Lean) | function-level equalities only; NOT imported by any capstone theorem: H_COMPUTE_FN is still inside every capstone H_CELLS |
| C3 | d699b3b8: xorshift's 5 units, every input | (pending Lean) | Python: Lean = committed xorshift fixture; sim 0 mismatches vs C source; no independent xorshift build |
| C4 | 927ece3d/85f065da: Wip/Chcf/Neg.lean negative controls | (pending Lean) | |
| B1 | 6a490ebd/22c1807e: Bwit2 joint witness; 124 -> 136/175 | (pending Lean) | counts reproduced by own census; 2 of the 12 new links rest on "1-input join = wire" on the REQUEST side, false for the emitted fused units |
| B2 | e722adbf: 39 unbound sides (amerge 28, muxn 4, fork trees 6, source 1) | reproduced (Python) | |
| B3 | 076af340: steer/mux selects bound to bit 0 of control bus | (pending) | |
| B4 | f5040d10: Bwit2 negative control | (pending Lean) | |
