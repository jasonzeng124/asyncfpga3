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

The automatic path = `suite_one.sh K SEED` (BDC_AUTO=1, `auto_size.sh` MAXIT 4 + raise-only finish 3, the draws).
"farm" = farm suite8 (commit c605cc2a, 2 cores, 240-minute limit; per-task files on `claude/cluster`,
results/suite8/T). "here" = this session, nextpnr 6e5d224472232d5d. A route rebuilt here from the farm loop's own
`sizes_IT.vh` and seed is the farm's route when its SDF md5 matches (BDC_AUTO's emission for every kernel below is
identical at c605cc2a and at 7197d85c2, `cmp` without the header line). P = ns per iteration from the timed event
graph on the period vector (worst bands, no scatter); latency per call = suite_one's figure (median over the vectors
of the median over draws of BENCHRES latmin x 12 ns).

| kernel | seed | sizing loop | route (SDF) | P ns / iteration | draws | latency per call (median) | where |
|---|---|---|---|---|---|---|---|
| memsum | 1 | farm stopped by its time limit during rule 6 (raise-only phase; it 5: 3 negative) | it 6: the final code rebuilds the farm's 0aeee7a1 (LANE_NORUN); P was measured on 73576845, the same sizes built with an intermediate cell (section 4) | **28.21** (route 6, not the loop's last; answers 5/5 = C) | not run | - | farm + here |
| memsum | 2 | farm stopped during rule 5 | - | - | - | - | farm |
| dot2 | 1 | farm stopped during rule 7 (the last) | - | (suitew, older flow: 156 printed = the artifact) | - | - | farm |
| dot2 | 2 | NOT CLEAN after 7 | 4d68e57e (rebuilt here = farm's) | **28.03** (stride 2; farm printed 156.0) | 4/4 PASS 8/8 (farm) | 966 ns | farm + here |
| gather | 1 | NOT CLEAN after 7 | 33b77519 (rebuilt here = farm's) | 55.22 | 4/4 PASS 9/9 (farm) | 1824 ns | farm |
| gather | 2 | NOT CLEAN after 7 | 86c9d605 (rebuilt here = farm's) | 51.53 | **2/2 PASS 9/9** (here; the farm ran out of time before its draws) | 1758 ns | farm + here |
| fill | 1 | BUILD-FAILED at it 2: the bench's clocked side closed at 78.75 MHz < 83 (its latency statistics path, lat_final -> leading one -> adder, 12.7 ns) | - | - | - | - | stores |
| fill | 2 | NOT CLEAN after 6 | d269ddfe | 37.27 | 2/2 PASS 5/5, arrays = C (stores) | 324 ns | stores |
| test_bitint | 1 | NOT CLEAN after 7 | cf69bd3e | NA (10-trip loops: no steady state) | 4/4 PASS 6/6 (farm) | 288 ns | farm |
| test_bitint | 2 | NOT CLEAN after 7 | 3696e956 | NA | 4/4 PASS 6/6 (farm) | 288 ns | farm |
| unused_arg | 1 | CLEAN it 1 | 0553289e | NA (no loop) | 2/2 PASS 6/6 (srcjoin) | 72 ns | srcjoin |
| if_loop_1 | 1 | farm stopped during rule 7 (the last: the loop ships route 7 whatever that rule says) | b2ad5a7b (rebuilt here = farm's it 7) | **27.52** (answers 8/8 = C) | not run | (n = 100: 234 cycles, 2808 ns) | farm + here |
| if_loop_1 | 2 | farm stopped during rule 6 | - | - | - | - | farm |
| if_loop_2 | 1 | farm stopped during rule 7 (the last) | - | - | - | - | farm |
| if_loop_2 | 2 | NOT CLEAN after 7 | d9a6f9af | 31.15 (farm) | not run (time) | - | farm |
| sumi3_mem | 1 | CLEAN it 7 | 448634ea | (farm printed 156.0: the artifact) | not run | - | farm |
| sumi3_mem | 2 | CLEAN it 5 | 26f31958 (rebuilt here = farm's) | **27.86** (stride 2, one-call period vector; answer = C) | not run | (1000 trips: 2326 cycles, 27.9 us) | farm + here |
| fir | 1 | CLEAN it 6 | 01a9e080 | NA (farm) | not run | - | farm |
| fir | 2 | NOT CLEAN after 7 | b95f54ea | NA (farm) | not run | - | farm |

No memory kernel failed a draw or deadlocked on the automatic path's routes: 22 of 22 draws PASS (farm 16, stores 2,
srcjoin 2, here 2), every array read back after each call. Every full-stack run here (worst bands, no scatter) gave
the C's answers. The loops that did not finish are time, not failures: on the farm every
task that stopped was inside a rule step (corner_audit), and the shipped route of three of them (dot2 s1, if_loop_1
s1, if_loop_2 s1) is already built (route 7 is the loop's last whatever its rule says). sumi3_mem and fir never got
their draws: a call fills 1000 / 2000 elements through the host port at 13 aclk each and reads them back, which the
decoded-netlist simulation runs at a few microseconds of circuit time per minute.

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

`cells/rtl/optin/bd_mem_ff.v` is bd_mem with both of its lines bd_delay FASTFALL (LUT2 elements ANDed with the
line's input): they rise through DSETUP / DCO elements and fall one element after their input. Same ports, parameters
and instance names as bd_mem. `bdc/mem.py` emits bd_mem_ff instead of bd_mem on every port under `BDC_MEM_FASTFALL=1`
(opt-in); `cells/hw/build_bench.sh` reads a file of rtl/optin/ only for a kernel that instantiates its module.
`cells/rtl/bd_mem.v` is unchanged (why it is a separate module in a separate directory: "The cell, final form" below).
Emission (`emit.py --no-top`, every fixture in build/frontend, 108 x {default, BDC_AUTO=1, BDC_HOST_MEM=1, auto.py +
BDC_AUTO=1 + BDC_HOST_MEM=1}): with the flag unset, 180 / 180 outputs `cmp`-identical to the branch before this work
(7197d85c2) and the 252 refusals identical; with it set, exactly the 76 outputs of the 19 fixtures that have a memory
port differ, and only in their `bd_mem` -> `bd_mem_ff` lines. Routed, flag unset: farm memsum seed 1's route 6 rebuilt
from its own sizes is the farm's SDF 0aeee7a1.

Why it is safe (the cell's header has the argument): the RAM samples only ram_clk's rising edge, so setup (DSETUP)
and clock-to-out (DCO) keep their full rising lines; ack is ANDed with ram_clk in every uco element, so it cannot
fall before ram_clk has fallen at the line; the station releases its operands only after the port's ack has fallen,
so the next rising edge still needs the whole handshake plus a full DSETUP rise (ram_clk's low phase >= DSETUP's
rise, its high phase >= DCO's rise; measured in the event graphs of gather: high 11.4-13.1 ns, low 38.8-40.5 ns
with FASTFALL, 13.5-17.7 / 37.5-41.7 ns without). The address hold (released one arc after ack falls) is at least
DCO's rise, where the symmetric line gave twice that (tighten.py rule C states the 2x bound; with FASTFALL it
overstates). The GLS RAM model checks setup / hold windows, not the clock's minimum pulse width, so the draws
cannot see a pulse-width problem; the phases above are 10x any RAMB18 minimum pulse width.

The prediction (whatif.py memfastfall, on each base route's graph) and the routes, each built from the BASE loop's
own final sizes (no loop with the lever on; one route per kernel / seed, nextpnr 6e5d224472232d5d):

| kernel / seed | base route (P) | FASTFALL route (P) | predicted | draws on the same points (K) | latency per call |
|---|---|---|---|---|---|
| gather s1 | 33b77519 (55.22 ns) | 8e879c25 (51.90 ns, -6.0 %) | 48.8 | base 4/4 (farm), FASTFALL 2/2 PASS 9/9 (10101, 10102); cycles 1982 / 2018 -> 1898 / 1898 | n = 32: 154 / 157 -> 147 / 147 cycles |
| fill s2 (a store) | d269ddfe (37.27 ns) | 0d146c75 (32.55 ns, -12.7 %) | 35.1 | base 2/2, FASTFALL 2/2 PASS 5/5, arrays read back = C (10201, 10202); cycles 626 / 616 -> 544 / 538 | n = 40: 134 / 131 -> 113 / 112 |
| gather s2 | 86c9d605 (51.53 ns) | 1fb0e56b (45.83 ns, -11.1 %) | - | **the full-stack run returns xxxxxxxx on 6 of 9 calls** (no draw run) | - |
| gather s2, one raise-only rule step on 1fb0e56b | 86c9d605 (51.53 ns) | a1e0aef2 (47.39 ns, -8.0 %) | - | base 2/2, FASTFALL 2/2 PASS 9/9 (10201, 10202); cycles 1932 / 1848 -> 1776 / 1740 | median 1758 -> 1626 ns |
| dot2 s2 | 4d68e57e (28.03 ns) | not built (time) | 28.03 (no change) | | |
| if_loop_1 s1 | b2ad5a7b (27.52 ns) | not built | 26.85 | | |
| memsum s1 (route 6) | 73576845 (28.21 ns) | not built | 27.50 | | |
| sumi3_mem s2 | 26f31958 (27.86 ns) | not built | 27.86 (no change) | | |

**gather s2 with FASTFALL fails, and why.** The run log has `RAMB18 SETUP VIOLATION ... DI ... (input moved 488 ps
before the edge, needs 737 ps)` every 156 ns: the HOST's fill of b (umem_controller2_uport.umem0) writes its data
too late for the RAM clock. tighten.py rule B on that route (nominal SDF): "latest payload DIADI3 5200 ps, clk 6012
ps, t_su 737 -> margin 75 ps" -- 75 ps at nominal, negative at the draws' bands. It is a sizing miss on a route the
loop never saw: the variant reused the base loop's DSETUP (2 elements for that RAM: the base route had the margin), and the FASTFALL netlist placed
differently (its elements are LUT2s fed by the line's input as well; the chain's own wire on gather s1's cycle went
31.7 -> 22.0 ns). Any change to the netlist needs its own sizing loop: the lever's A/B has to run the loop in both
arms (out/memauto1.sh tasks 11-20).

**The rule catches it, and one step of the loop fixes it.** auto_size.sh's rule (corner_audit CA_SIZERULE, both
corners, CA_JOINAWARE, BD_SKEW_STEER_SELF, as the loop runs it) on route 1fb0e56b: rule B on
umem_controller2_uport.umem0.uram -244 ps at corner 0.20 and -267 ps at 0.31 (the GLS: -249 ps), "depends on
..._UMEM_CONTROLLER2_UMEM0_USETUP"; 8 negative rows in all. ratchet.py --raise-only --headroom 1 (the loop's phase 2)
raised 4 lines: that USETUP 2 -> 5, UMUX1 3 -> 5, UMUX3 2 -> 6, ULINK_N19__2 1 -> 3. The route built from those sizes
(a1e0aef2, seed 2, FASTFALL): **9 of 9 answers = C in the full-stack run, P 47.39 ns** (base 51.53: -8.0 %), and
**2 / 2 draws PASS 9/9** (table above). So the failure is the shortcut's (reusing another route's sizes), not the lever's: the static
rule sees the miss on the FASTFALL route, as on any other.

**The cell, final form.** The routes above were built with an intermediate version, a FASTFALL parameter on bd_mem
itself (my clone's commit 72c4933b9). That version changed a DEFAULT build: farm memsum seed 1's route 6, rebuilt from
its own sizes, came out 73576845 instead of the farm's 0aeee7a1 (gather seed 2 happened to come out identical): yosys
names a derived module after the parameters given, so `bd_delay #(.N(DSETUP), .FASTFALL(FASTFALL))` at 0 is not
`bd_delay #(.N(DSETUP))`. A second module, bd_mem_ff, under cells/rtl/ changed it again (d63c74bf): a module merely
read moves yosys's auto-name counter. The final form: `cells/rtl/bd_mem.v` byte for byte as it was, the variant in
`cells/rtl/optin/bd_mem_ff.v` (outside the rtl/*.v glob), and `cells/hw/build_bench.sh` reads an rtl/optin/ file only
for a kernel that instantiates its module. With it, route 6 of memsum seed 1 is the farm's 0aeee7a1 again
(LANE_NORUN rebuild, seed 1). bd_mem_ff has bd_mem's ports, parameters and instance names (usetup, gplain.ubuf, uco,
uram), so the sizing macros, rules B / C and the GLS RAM model see the same cell; its structure is the intermediate
version's at FASTFALL = 1. Rebuilt with the final form, fill seed 2 gives the intermediate route byte for byte
(0d146c75, P 32551 ps, the C's answers), and so does gather seed 1 (8e879c25, LANE_NORUN): those two rows hold for
the final code as it stands. gather seed 2's re-sized route does not reproduce (the final form gives ab524dec, not
a1e0aef2: the netlists differ only in the module's name, and that moves this route): ab524dec, full stack, **P 46.66
ns, 9 / 9 answers = C**, EQUIVALENT, ffmux-clean; no draw on it, and its own rule was not run.

## 5. Files

- `research/tools/eventgraph/eventgraph.py`: rises during the host's memory accesses (bridge_i.mem_busy) are not
  iterations (auto marker and the marker's period); `--k K` (the window).
- `research/tools/fifteen/lane2_run.sh`: no stride-1 period -> `--stride 2 --k 6`, P printed per iteration with
  `stride=2`.
- `research/tools/eventgraph/whatif.py`: `memfastfall[:INST]` (bd_mem's lines fall in one element; prediction).
- `research/tools/suite/suite_one.sh`: `SUITE_TAG=T` (a flow variant beside the default, same draw points) and
  `SUITE_SKIP_AUTO=1` (judge a loop that ran elsewhere, its route rebuilt from its own sizes); both opt-in.
- `research/data/suite/vec/sumi3_mem_period.hex`, `fir_period.hex`: one call each, the period vectors (suite_one's
  PV): the full stack and the event graph read one 1000-trip loop instead of three / two.
- `cells/rtl/optin/bd_mem_ff.v` (new), `cells/hw/build_bench.sh` (reads rtl/optin/X.v only for a kernel that
  instantiates X), `bdc/mem.py` (`BDC_MEM_FASTFALL=1` emits bd_mem_ff). `cells/rtl/bd_mem.v` unchanged.
- The local drivers (judge a farm loop's route here, P-only runs, one rule step, the emission check) are in the
  subagent's out/scripts/, not committed.

## 6. Open

- The six loops the farm stopped (memsum s1 / s2, dot2 s1, if_loop_1 s1 / s2, if_loop_2 s1), and the draws of
  gather s2 (2 more), if_loop_2 s2, sumi3_mem, fir: out/memauto1.sh (farm, time 600, 10 kernel / seed loops x
  {default, BDC_MEM_FASTFALL=1} with SUITE_TAG=mf on the same draw points).
- The lever with its own loop, 4+ seeds; then whether BDC_AUTO should turn it on for a kernel with memory.
- The fused multiply in the sum ring (dot2, sumi3_mem; fir and if_loop_1 have the same shape).
- tighten.py rule C states hold >= 2 x DCO; for bd_mem_ff the bound is DCO's rise (still 7x the 360 ps needed).
- fill seed 1's bench clock (83 MHz) on the loop's it 2 route.
- AUTO turns BDC_LINK_FASTFALL off for every kernel with a memory (emit.py refuses it there: "a fast-falling request
  shortens the RAM clock's low phase"); with a station between every link and bd_mem the claim looks broader than the
  hazard, but links' falls were not on any cycle above, so it was not examined.
