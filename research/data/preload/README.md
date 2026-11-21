# Preloaded loop state: xorshift's counter across its long carries (2026-11-17)

PROGRAM "Paths no vector can reach": start the gate-level run with the loop state preloaded, on the same routed
design and the same bits, and check it against the C started from the same state.

## What the counter can reach at all

The kernel is `while (i < rounds) { ...; i = i + 1; }` with `int i` starting at 0. Dynamatic's form
(`research/data/fifteen/xorshift_predec.mlir`) is a do-while over (i, x, n = rounds - 1): the body runs with i,
`i + 1` (UADDI0) and `i < n` (UCMPI1, signed) are computed every iteration, joined at the steers (`ucond_br6_j`), and
the loop continues while i < n. Since rounds <= INT_MAX, n <= 2^31 - 2 and i + 1 <= 2^31 - 1: **the 31-bit carry
(2^31 - 1 -> 2^31) never happens in the C's own semantics.** The longest carry the kernel can need is the 30-bit one,
2^30 - 1 -> 2^30, after 2^30 iterations. The bench masks rounds to 12 bits (gen_bench.py), so the vectors reach
i < 4096 at most (xor19: i < 1000, carries up to 10 bits).

## Mechanism (opt-in)

The loop's entry values sit in two bundled-data pipes whose last-stage LUT latches feed the loop muxes:

| state | latch output net (the latch is a LUT with its own feedback) | in the unforced design |
| --- | --- | --- |
| i0 | `bridge_i.udut.n6_data[31:0]` (`ulink_n6.many.stage[1]`) | the constant 0 (`int i = 0`) |
| n  | `bridge_i.udut.n_trueResult_2_data[31:0]` (`ulink_n_trueResult_2.many.stage[1]`) | rounds - 1 from the bench |

`research/tools/preload/gen_preload.py` (run by `cells/gls/ps/build_ps.sh`'s existing `PS_MON_GEN` hook) finds, for
each of those 64 latch nodes, the net the LUT latch drives in the netlist decoded from the bitstream (BEL/pin ->
netlist wire via nets.map, as `gen_bench_mon.py`; it refuses a net not driven by a `.lat.` LUT with its own feedback)
and `force`s it, for a whole batch, to bit k of (i0, n) from `+PRELOAD=<file>` (one "i0 n" line per batch, like
`+VECFILE`). It re-forces when the PS7 model's batch index changes (bench idle) and reads every bit back
(`PRELOAD batch=.. readback .. OK` in run.log; a mismatch stops the run).

- Every bit, every reader: the force sits on the latch's output net, upstream of every routed interconnect arc
  (GLS_TRANSPORT_IC ICBUFs) to umux0 / umux2 and of the latch's own feedback pin, so every consumer sees the preloaded
  value through its own routed delay; nothing reads the latch's internal state.
- Timing class: the entry value is static during a call exactly as the constant 0 is in the unforced design, so the
  first iteration is timed as usual (mux select -> adder -> latch). Every later i and n is the loop's own, carried
  through the real latches, the real UADDI0 / UCMPI1 lines and the routed delays. The force is never released inside
  a call, so there is no "quiescent moment" to choose: the entry latch is read only when the mux selects it.
- Why not the loop-carried latches mid-call: an async loop has no quiescent moment inside a call, and the loop-carried
  latches are transparent while their token passes; a write there races the handshake. The entry latch is the one
  place the state is defined between calls (it is what `int i = 0` compiles to).
- x is not forced: x0 is the seed from the vector. The bench's rounds still drives the entry guard (rounds > 0) and is
  set to 1 on preloaded rows (its rounds - 1 is overridden by the n force).
- Oracle: `research/tools/preload/preload_oracle.sh` compiles `kernels/xorshift/xorshift.c` itself with its one line
  `int i = 0;` replaced by `int i = PRELOAD_I0;`, called with rounds = n + 1: body count n - i0 + 1, the same as the
  hardware's. It refuses n = INT_MAX (not expressible) and i0 > n. For i0 = 0 it reproduces xor19.exp (checked on
  every xor19 row with rounds > 0).
- Default unchanged: without `PS_MON_GEN` the module is not compiled; without `+PRELOAD` it forces nothing.

Shared-tool change (opt-in, default byte-identical): `research/tools/eventgraph/bench_gate.sh` takes `GATE_TBATCH`
(ns per batch before HANG; default 1200000 as before). `preload_gate.sh` sets 120000 (xor19's 1000-round batch takes
~35 us at worst), so a loop that a wrong count sends round 2^30 times is called a HANG after 120 us of simulated time
instead of 1.2 ms.

## Files

| file | what |
| --- | --- |
| `pre1.{hex,pre,exp,rows,notes}` | 12 batches: 2 controls (i0 = 0), k = 8 / 12 / 16 / 24 / 30 (i0 = 2^k - 3, n = 2^k + 2, the k-bit carry at iteration 3), 2^31 - 3 (the 31-bit start the owner named; see above), the 32-bit wrap -1 -> 0 (i0 = -3: a legal C state, the adder's longest chain), 81 iterations across 2^30, entry value 2^24 - 1, 2^30 - 2 |
| `xp1.{hex,pre,exp,rows,notes}` | xor19's 19 vectors with their natural state forced (i0 = 0, n = (rounds & 0xFFF) - 1; expected = xor19.exp) + pre1's 10 preloaded rows (the farm set) |
| `xorshift_sizes_x55a_add{1,2,4}.vh` | item 35's sizes with UADDI0 = 1 / 2 / 4 (`shrink_sizes.py --only 'UADDI0$'`) |
| `xorshift_sizes_x55a10_add{8,6,4}.vh` | x55a10 with UADDI0 = 8 / 6 / 4 (farm preload1) |
| `results.txt` | the local runs below, one line each |

Tools: `research/tools/preload/{gen_preload.py, preload_gate.sh, preload_oracle.sh, build_route.sh}`.
`build_route.sh` builds a route as draws2.sh / eval_task.sh / lane2.sh do (same flags, `NEXTPNR_SEED`), but in a
`git archive` tree under /tmp, without lane2's worktree and without writing into `research/data/eventgraph/graphs`.

## Commands

```
source /root/dev2/lib/fpgatoolchain/openxc7/export.sh
research/tools/preload/build_route.sh d2_x55a_21 research/data/xorshift_sizes_T3s50_fr4a_x55a_bench.vh 21
R=/tmp/claude-0/preload/runs
research/tools/preload/preload_gate.sh $R/hw/d2_x55a_21 $R/g/x $R/r/d2_x55a_21/xray.sdf pre1 worst      # or draw:K
research/tools/preload/preload_oracle.sh < research/data/preload/pre1.rows        # = pre1.exp
# negative control: sum bits 16-31 of i + 1 -> their latch +8000 ps (SDF only)
python3 research/tools/fifteen/sdf_inject.py $R/r/d2_x55a_21/xray.sdf inj.sdf 'slice\[[4-7]\]\.genblk1\.carry4/O' \
    'ulink_n_trueResult_6\.many\.stage\[0\]\.' 8000
```

## Results (local, toolchain nextpnr 9c732bc6303458df)

RESULTS_PLACEHOLDER

## What this does not show

- It is one route (item 35's, seed 21) plus one UADDI0 = 1 route, at `worst` and two draws; the farm request
  `research/cluster/requests/preload1.sh` is the many-routes x draws version.
- The preload replaces the entry values of i and n, not x: x0 is whatever seed the vector gives, so the preloaded rows
  test the counter's and compare's long chains, not a particular x state 2^30 rounds in (x's path has no carry chain).
- The first iteration of a preloaded call is not the long carry itself (the rows put it at iteration 2 or 3); one row
  (entry 2^24 - 1) puts it at iteration 1, where the forced entry value is static as the constant 0 is.
- Forcing a net bypasses that latch's own D -> Q arc for the entry value; the loop-carried values never go through the
  forced latch (they enter umux0 / umux2 on the other input).
- Same trick for collatz64's 63-bit values: not done here. collatz64's state is n itself (an input), so there the
  question is the bench's input mask, not a counter; the mechanism (force an entry latch from +PRELOAD, oracle from the
  C started at that state) carries over with the latch names of that kernel.
