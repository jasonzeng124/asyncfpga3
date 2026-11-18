# The memory kernels through the automatic path (subagent `memauto`, 2026-11-18)

PROGRAM 2026-11-18, lead 6: BDC_AUTO=1 + the flow's own sizing loop (`research/tools/auto/auto_size.sh`) + the draws,
through `research/tools/suite/suite_one.sh`, on the memory kernels. Everything routed here was built by nextpnr
`6e5d224472232d5d` (`cells/verify/toolchain.sh`: every patch fingerprint ok), `--freq 83`, on a node whose load
average was 30-60 on 16 cores (every simulation here ran at a fraction of a core).

## 1. dot2's "156 ns per iteration" was the host's fill cadence, not the kernel

`eventgraph.py ... auto` picks as its marker the kernel request net with the longest run of equal rise intervals.
A kernel with memories has the bench's host slot on every port (research/data/suite/bench/README.md): before each
call the host fills the arrays through the port, one access per 13 aclk = **156 ns**, so the port's merged request
`umem_controllerN_uport.m_req` rises at that clocked cadence 32 times in a row per array. On dot2 (suitew's local
route and farm suite8 seed 2) and sumi3_mem (farm suite8, both seeds) that net won: P = 156000 ps exactly, and
`check.txt` said `NO CYCLE through the marker` (the host's request is not on any kernel cycle). On test_bitint it won
too and the run was "steady state too short" (9 equal host intervals), P=NA.

Measured instead (farm suite8 dot2 seed 2, rebuilt here from its own `sizes_7.vh`: SDF `4d68e57e`, the farm's route
byte for byte): dot2's loop alternates **27849 / 28203 ps** (every kernel request net, steady over each 32-trip call),
so no net has two equal consecutive intervals and the stride-1 graph cannot be built. With `--stride 2 --k 6` the graph
of two iterations closes: **P = 56052 ps per 2 iterations = 28.03 ns per iteration**, `CHECK period equal: PASS`, the
critical cycle equal to trace.py's (114 edges). Cross-check from the bench's own latency (BENCHRES latmin, host cycles
of 12 ns): n = 32 -> 80 cycles, n = 31 -> 78, n = 1 -> 8, so (80 - 8) x 12 / 31 = 27.9 ns per trip.

The fix (committed, general, nothing per kernel):
- `eventgraph.py`: a rise while `bridge_i.mem_busy` is high (the bench's host memory sequencer; the net exists only
  in a bench with a host slot) is the host's, not an iteration: not counted, for the auto marker's choice and for the
  marker's own period. A design without that net takes the old code path (same rises, same choice).
- `eventgraph.py --k K` (the window, default 10) and `lane2_run.sh`: when the stride-1 graph gives no period, retry
  `--stride 2 --k 6` (a 32-trip loop has 15 stride-2 intervals per call; K + 6 must fit) and print P per iteration
  (the 2-iteration period / 2) with `stride=2` on the line. A route whose stride-1 graph works is unchanged.

## 2. The memory kernels: status

(table filled at the end of the session; see section 5)

## 3. Where a memory kernel's cycle goes

From the event graphs (whatif.py report, cycle_wire.py) of the routes above:

- **gather (a[b[i]]), farm seed 1 route `33b77519`, P 55.2 ns**: the critical cycle is the a-port's access, rise
  16.4 ns AND fall 16.4 ns, plus the b-port's rise 12.4 ns, plus the stations / links / mux between them (~10 ns).
  The a-port's return to zero is on the cycle because the b-station's operand release waits for its consumer's
  acknowledge (the a-station's `hold`), which falls only after the a-port's acknowledge has fallen (bdc/mem.py:
  "the operands are released when the PORT is quiet"). Wire is 85.7 % of the cycle; the matched delays' own
  chain wiring alone is 31.7 ns (97 hops): bd_mem's lines are long here (a-port DSETUP 20 / 23, DCO 13 / 13; the
  address comes from the other RAM's DOADO).
- **dot2 (s += a[i] * b[i]), farm seed 2 route `4d68e57e`, 28.03 ns per iteration**: no port return to zero on the
  cycle. Per two iterations (56.05 ns): the loop test (fused cmpi + cmpi + andi, 4.2 ns of chain), the steers and
  the index, the b load (port rise 10.8 ns: DSETUP 6, DCO 13), and the fused multiply-add `uaddi0` (muli + addi fused
  by BDC_OP_FUSION, one matched delay of 28 elements, 13.8 ns). The coupling: the loop test's result is forked to
  four steers (ufork8); the sum's steer (cond_br6) joins it with the multiply-add's output, so the test's fork returns
  to zero only after the multiply-add, and the next index waits for that. The sum ring alone (rise-only floor) is
  38.9 ns per 2 iterations: the multiply sits inside it because fusion merged the non-loop-carried muli into the
  loop-carried addi. Two general leads, not built here: (a) a link on a loop-test fork output whose steer's data is
  computed in the iteration (the converse of AUTO's rule F); (b) fusion that stops at a ring boundary (a region
  whose sink is on a cycle takes no operator that is not). whatif.py's `stage` / `depth` edits do not work on a
  stride-2 graph (a net has two nodes per period), so neither was predicted.
- **fill (one store in a loop), the stores subagent's seed 2 route `d269ddfe`, P 37.3 ns**: the port's rise and
  fall, 13.2 ns each, are on the cycle; the next cycle (the store-completion join, rise-only floor 30.4 ns) is close.

## 4. bd_mem FASTFALL (opt-in): the port's return to zero in one element

(filled at the end of the session)

## 5. Files

(filled at the end of the session)
