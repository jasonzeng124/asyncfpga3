# gcd judged by draws (PROGRAM 2026-11-17 "Use the quota" item 7)

Toolchain: nextpnr 9c732bc6303458df (patches 789a7120c912d393), `cells/verify/toolchain.sh` OK, 2026-11-17.

## What gcd's board candidates are, and what can be judged by draws

gcd's board items are not bench builds: BOARD-QUEUE list #1 is `gcd_ps` (P1 sizes, `build_hw.sh gcd_ps`, the
`gcd_ps.v` AXI harness) and list #3 is item 5, `gcd_hw` with `gcd_hw_sizes_R5s75.vh` + `BDC_LINK_FASTFALL=1`
(`build_hw.sh gcd_hw`, the `gcd_rig.v` vector-table rig). `bench_gate.sh` runs only the PS7 kernel bench
(`ps7_bench.v` host, `PS_DESIGN=<k>_bench_gen`), so neither board build can be put through the draws as it is.

What can: the same compiled kernel (`bdc/emit.py` on `build/frontend/gcd/comp/handshake_transformed.mlir`, fusion on,
no probe) in `gcd_bench_gen`, the bench every other kernel is judged on, with item 5's sizes and flags. The sizes
carry over unchanged: every one of R5s75's 220 macros names a `DELAY_` parameter of the bench kernel; only the macro
prefix differs (`BD_SZ_URIG_UDUT_` in the rig, `BD_SZ_BRIDGE_I_UDUT_` in the bench).

**No shared tool needed a change.** `eval_task.sh` / `lane2.sh` / `bench_gate.sh` build and judge gcd as they do the
others (`build_bench.sh` accepts gcd; `fullstack_dump.sh`, `eventgraph.py` and the gate are kernel-agnostic). The only
gcd-specific inputs are files here:

| file | what |
|---|---|
| `gcd_kernel.c` | Dynamatic's `integration-test/gcd/gcd.c` (not vendored here: no `kernels/gcd/`), as the auditor fetched it: `git show c4e69e111:audit/oracle/gcd_kernel.c` (sha256 of the original 759d5c3b...; includes replaced by `typedef int in_int_t;`, main dropped) |
| `gcd_oracle.sh` | `kernel_oracle.sh`'s method for gcd: compiles that C, applies the bench mask (a, b & 0x7FFFFFFF, `gen_bench.py` DOMAIN_RESTRICTIONS "gcd": nonnegative) |
| `gcd_bench_sizes_R5s75.vh` | `gcd_hw_sizes_R5s75.vh` with the bench prefix (sed), 220 sizes, same numbers |
| `gcd_bench_sizes_R5s75_x70.vh` | that x0.70 (`shrink_sizes.py`, ceil; 37 sizes moved; = R5 x ~0.53) |
| `vec_gcd.hex` | the itercost / event-graph vector for lane2.sh: `7fffffff 00000001` (31 main-loop iterations, one shift each: a regular loop) |

Build flags (item 5's recipe on the bench): `BDC_LINK_FASTFALL=1 BD_RLOC=v4 BD_PLACE_WEIGHT=1 BD_COLUMN_ROWS=9
BDC_SELECT_PADS=<repo>/cells/hw/gcd_hw_pads.json`, plus lane2.sh's own `BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0`.
(`build_hw.sh` defaults place weight 1 / column rows 9 for gcd_hw; `build_bench.sh` passes them only when set.)

## Vectors: `research/data/eventgraph/gate/gcd18.{hex,exp}`

18 pairs, all inside the bench domain (a, b <= 0x7FFFFFFF), expected values from `gcd_oracle.sh`, each also checked
equal to Python's `math.gcd`: small (0x30, 0x12); a == b (1,1), (0x7FFFFFFF, 0x7FFFFFFF), (2^30, 2^30); one operand 1
(1, 2^31-1), (2^31-1, 1); one operand 0 (0, 2^31-1), (0x12345678, 0) -- legal, handled by the C's early return, answer
nonzero; powers of two (2^30, 3*2^29) [k-loop 29], (2^16, 2^15); coprime large: Fibonacci F46 / F45, (2^31-3, 2^31-1),
(10^6, 10^6-1); a large common factor (9*223092870, 7*223092870) -> 223092870, (0x7FFFFFFE, 0x55555554) -> 0x2AAAAAAA;
the longest in-domain pairs found (random search of 3e5 pairs + structured ones): (2^31-1, 2^31-2) 31 main-loop
iterations + 59 shifts, (2^31-1, 2^30-1), (2^31-1, 2^30) (30 pre-loop shifts).
No answer is 0 (the only 0 is gcd(0, 0), left out), and **no two consecutive answers are equal**, so a result stream
that falls one call behind (the failure seen on xorshift / collatz controls) cannot pass by accident.
Oracle check: on `research/board/gcd_ps_vec1000.hex` (1000 pairs, answers from `bdc/simcheck.py ref_gcd`) the oracle's
output equals the file's third column byte for byte; it also reproduces the auditor's 16 `oracle_out.txt` values. There
was no earlier gcd `.exp` in `gate/`.

## Local result (one route)

R5s75 on the bench, `NEXTPNR_SEED=1` (built in a scratch copy of cells/ bdc/ build/frontend, not a git worktree):
sdf md5 5c1abff4, bit 97a12a3f, fclk0 closes at 110.17 MHz (target 83), fasm_equiv EQUIVALENT (only the benign kinds),
ffmux-clean. Event graph (fullstack_dump worst column without scatter, vector 7fffffff 00000001): **period P = 87201 ps**
per main-loop iteration + one shift (critical cycle 160 arcs, check PASS); latency 238 cycles of 12 ns = 2.86 us for that
call. (The August gcd_bench_gen at band 0.288: ~172 ns per main iteration + ~137 ns per shift; a different build:
other sizes, no fast fall, older toolchain.)

| run | parameters | verdict | cycles |
|---|---|---|---|
| draw 101 | chains 0.2548, rest 0.2819, carry/F7F8/FF 0.3701, M seed 101 | PASS 18/18, no mismatch latch | 5522 |
| draw 102 | chains 0.2132, rest 0.2450, carry/F7F8/FF 0.2739, M seed 102 | PASS 18/18, no mismatch latch | 5366 |
| worst (chains 0.21, CARRY/F7/FF 1, rest 0.288, + M) | -- | **not obtained**: OOM-killed twice on this shared machine | -- |

Draw numbers are the farm's K = 100*route + j for route 1, so gcddraw1 task 1 repeats them (a check that farm and
local agree). Per-batch BENCHRES lines, the draw parameters, the event-graph check and the toolchain fingerprint are
in `local_s1/`. The worst corner is in gcddraw1 as task 65 (with SLOW_MAX and FAST_MIN) on the same route.

Times: a gate run is ~20 min locally (iverilog compile ~6 min, peaking at **~9.3 GB**; vvp ~5.1 GB; xorshift's vvp is 2.4
GB). The first attempt at `worst` and draw 101 was OOM-killed on this shared machine (cgroup OOM, ivl; reported by
bench_gate.sh as `FAIL 0/18 cycles 0` with no BENCHRES: a build failure, not a verdict) and was rerun once memory was free.

## Farm request: `research/cluster/requests/gcddraw1.sh`

64 tasks: R5s75 on routes 1-32 and R5s75 x0.70 on routes 1-32, 4 draws each (K = 100*route + j, the same K for both
sizes on a route: paired). Prediction in its header. Read it with `research/tools/draws_table.py results/gcddraw1`
(the two halves key apart by their sizes path). The build is `eval_task.sh` with `TSE_ONLY=1` and no `TSE_VEC`, which
is build-only (lane2.sh: build, fasm_equiv, ffmux, event graph): the static corner_audit had not finished after 55 min on gcd locally (stopped; its tighten.log reported 44 boundaries below their constraint, a static lead only)
and decides nothing under PROGRAM 2026-11-16. `mem=48G` for gcd's larger gate sims.

## Caveats

- This judges gcd's kernel and sizes on the **bench**, not the board items' own harnesses (gcd_hw rig, gcd_ps AXI).
  The kernel netlist and sizes are the same; the routes, the harness and the placement around the kernel are not. A
  board item from this would be a gcd_bench_gen build (as items 27-35 are for the other kernels), with its own route.
- gcd_ps (BQ list #1) uses P1 = no per-cell sizes except umux21 16; it is slower than R5s75 by construction and is not
  run here. Its file (`gcd_ps_sizes_P1.vh`) already has the bench prefix and could be judged the same way.
- One local route, a few draws: a lead only. The farm request decides.
- The bench domain is nonnegative a, b only (the C overflows for opposite signs near 2^31 and can cycle forever;
  `gen_bench.py`). The vectors stay inside it; the oracle applies the same mask anyway.
- The x0.70 half is x0.70 of R5s75 (~x0.53 of R5): not a measured step from R5 but the next step down the same scale.
