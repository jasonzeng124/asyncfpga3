# The default flow's "wrong values" on spmv and sobel (subagent `memorder`, 2026-11-18)

The journal (2026-11-18 22:52) recorded that bdc's default flow computes wrong values on spmv and sobel in
zero-wire-delay RTL (`research/tools/suite/memtb.py`, its default `--route-ps 0`): spmv FAIL 3 of 4 calls (out[]
elements 0 where the C writes nonzero), sobel FAIL 2 of 3; BDC_AUTO=1 was believed to pass, and the suspect was the
order of a later iteration's load against an earlier iteration's store. **It is neither an ordering bug nor the
default flow's.** It is the RTL model's RAM read boundary: at zero wire delay bd_mem's acknowledge (the emitted
placeholder DCO, 12 LUT arcs = 1488 ps) comes ~1 ns before the RAMB18E1 model's read data (clock-to-out 2454 ps,
prjxray's max), and a load that captures its word at the acknowledge (`bdc_load_cap`, every load on an arbitrated
port since dyntests' `mc:load1st`) returns the PREVIOUS word on its port. BDC_AUTO=1's emission fails identically at
0 ps; both flows pass as soon as the acknowledge trails the read data. dyntests had recorded this exact limit
(dyn/README.md section 3: "the capture needs DCO >= clock-to-out, and cells/sim's RAM model breaks that at zero wire
delay"; every RTL figure there is at 350 ps per arc) -- memtb (hangs', written before the captures existed) runs at
0 ps by default, and nothing in it flagged the boundary.

## 1. The mechanism (waves)

**spmv** (research/data/suite/dynsrc/spmv/spmv.c): `s = row[i]; e = row[i + 1]; for (c = s; c < e; c++) tmp +=
val[c] * vec[col[c]]; out[i] = tmp;` -- out[] is only stored (no read-modify-write; the brief's `out[row[i]] += ...`
is not this C). row[] has two loads in one block, chained (LL): `uload0` (row[i], slot 0) and `uload1` (row[i+1],
slot 1, its token is uload0's z), both `bdc_load_cap`. memtb `--vcd`, default flow, 0 ps, call 0 run 0, i = 0
(times in ps after the RAM clock edge of each access):

| access | RAM clock edge (ps, absolute) | bd_mem ack | station `done` | capture latch closes (`cap_open` falls) | DOADO changes | word captured |
|---|---|---|---|---|---|---|
| uload0, row[0] = 0 | 5 700 300 | +1488 | +1860 | **+1984** | **+2454** | the port's previous word |
| uload1, row[1] = 1 | 5 706 554 | +1488 | +1860 | **+1984** | **+2454** (0 -> 1) | 0 = row[0] |

So uload1 returns row[i], not row[i+1], and uload0 returns the word of the previous access on the port -- uload1's
of iteration i-1, address i, i.e. row[i] again (right by coincidence; at i = 0 the host's last word). s = e for every
row, every inner loop is empty, out[i] = 0. **Predicted bad elements = the rows the C finds non-empty: 7, 1, 0, 2 for
calls 0-3 -- exactly memtb's counts and addresses** (call 0 [0] [2] [3] ...; call 1 [9]; call 3 [0] [2]); out0 (the
last s) is right by the same coincidence. A plain station's consumer of a loaded value sees the same early
acknowledge: in call 3 (where the stale bounds send the inner loop over other rows) vec[]'s RAM reports an address
setup violation twice (522 ps against 566, the address being col[]'s read data) -- printed by the RAM model into
run.log and, until this change, not shown by memtb.

Classification asked for: **not** a stale read across iterations (RAW), not a lost store, not a store clobbered by a
later one -- a read of the previous word on the port because the read data is announced before it exists, a
bundling violation at the RAM's read boundary that only the RTL model has (section 3: a route is checked against it).

**sobel**: the two loads of `in[x]` (the frontend hoisted them out of the i, j loops into one block, bb5: LL,
chained, both captured) -- load0 returns the previous word on in[]'s port (in[x'] of the previous x), load1 returns load0's word
(in[x], right). An emulation of exactly that in Python (sobel_stale.py, in the subagent's out/extra/) reproduces the
RTL bit for bit with load0's word feeding sumY (not with it feeding sumX): call 1 run 0 out0 0000c33c (C:
0000c23d), run 1 0000c23d, out[] 6 elements wrong, the three memtb prints ([15]=b5 want b6, [17]=b7 want b8,
[20]=b9 want ba) identical; calls 0 and 2 right. Those two calls cannot see this defect at all: call 0's gX / gY are
the Sobel kernels, which sum to zero, so sumX = v * sum(gX) = 0 whatever v was read; call 2's in[] is constant, so
the previous word is the right one. (The suite's sobel vectors are degenerate for the in[] path in 2 of 3 calls.)

## 2. The experiments that pin it (memtb, 0 ps, nothing else changed)

| change (simulation only) | spmv default | spmv AUTO | sobel default | sobel AUTO |
|---|---|---|---|---|
| none (DCO 12, clock-to-out 2454) | FAIL 3/4 (bad 7, 1, 0, 2) | FAIL 3/4, identical | FAIL (call 1: out0 run 0, 6 out[]) | FAIL, identical |
| RAM model clock-to-out 2454 -> 1200 ps | PASS 4/4 | PASS 4/4 | PASS 3/3 | PASS 3/3 |
| DCO 12 -> 18 (testbench parameter) | PASS 4/4 | -- | PASS 3/3 | PASS 3/3 |
| 350 ps per arc (dyntests' RTL_ROUTE_PS) | PASS 4/4 | PASS 4/4 | PASS 3/3 | PASS 3/3 |

DCO sweep, spmv default, 0 ps: 12, 15, 16 FAIL (the same values), 17 FAIL (2 calls), 18, 19, 20 PASS. The latch
closes DCO x 124 + 496 ps after the edge (the port's acknowledge join, `done`, `ucapen`) and its LUT6_2 O5 arc
(~150 ps) needs the data before the enable falls: DCO 17 closes at 2604 = 2454 + 150 (fails), 18 at 2728 (passes).
The threshold is where the model's clock-to-out says it should be; nothing about token order moved.

## 3. Default flow against BDC_AUTO=1, and the routed smoke

- The contrast "default fails, AUTO passes" was a contrast between 0 ps (the bot's memtb runs) and 350 ps (dyntests'
  RTL table). At 0 ps AUTO's emission fails on the same calls, elements and values; at 350 ps (or with the
  acknowledge after the data) both pass. Both flows emit bd_mem's DCO = 12 (no route, no sizes in RTL).
- dyntests' "default flow deadlocks" rows for spmv and sobel were right for dyntests' tree (its emission times out in
  memtb at 0 ps with the boundary met and at 350 ps) and are stale on the branch: hangs' token floor, merged since,
  makes both complete (spmv: two links 2-stage, the only difference between the two emissions); both pass in both
  flows (section 5).
- **The default flow's spmv, routed for the first time** (dyntests routed only BDC_AUTO's emission, the default one
  deadlocking): `cells/hw/build_bench.sh spmv`, `BD_NO_TIGHTEN=1 BD_SIZES=none BD_DSP=1 NEXTPNR_SEED=1`, `--freq 83`,
  `--host-mem`, nextpnr 6e5d224472232d5d (toolchain.sh all ok); Fmax 104.24 MHz (pass at 83), .bit 8ca89059, sdf
  f7cdacc8. Gate (`bench_gate.sh ... worst`, every array read back after every call against the C, GATE_ANNOTATE=1,
  the ports' one-hot monitor, 2 runs per call): **PASS 4/4**, cycles 1046, fasm_equiv EQUIVALENT, ANNOTATE_DONE with
  0 SDF warnings / errors, one-hot monitor 357 host / 300 kernel requests, 0 overlaps (wall 978 s). One route, one
  corner: a smoke.
- What the routed smoke rests on: the gate simulates the RAM's clock-to-out from the route's prjxray SDF
  (cells/gls/prims.v: DO follows the edge by the SDF's CLKARDCLK -> DOADO arc, full max at `worst`), so a route whose
  acknowledge led its read data would have failed the gate the way 0 ps RTL does. spmv AUTO seed 1 passing it is one
  route's evidence that its DCO line covers the clock-to-out at the worst corner -- the property this hazard is about
  -- not evidence about an ordering that timing hides (there is none here, section 4). Rule C on that route
  (`cells/verify/tighten.py` on dyntests' `spmv_auto_s1` SDF, nextpnr 6e5d224472232d5d): all 10 DCO lines ok, the
  acknowledge trails the clock edge by 2970-5074 ps against the 2454 ps clock-to-out (margins 516-2620 ps); on row[]'s
  port, the two captures', 4678 / 4658 ps (margins 2224 / 2204). The same line in the 0 ps RTL model: 1488 ps.
- **The capture itself, on every route that has one** (new here: out/extra/capmargin.py, tighten.py's own SDF parser,
  false-arc pruning and arc values): the capture latch's enable must fall after the read data has reached its D pins.
  Enable: the shortest path from the RAM clock's driver through the DCO line, the port's acknowledge logic, `done` and
  `ucapen` (whose net to the 32 latch LUTs alone is 1.6-1.8 ns); data: T_CO 2454 + the longest DOADO -> D wire (up to
  2.3 ns: BRAM to CLB). **Worst capture margin per route, 11 routes with a capture station (dyntests' 10 smokes +
  the default-flow spmv route above): 2490 - 5261 ps** (test_bool_array s1 2490, mul_example 2669, spmv default s1
  3173, test_memory_2 3333, test_bool_array unchained 3804, spmv AUTO unchained 3814, binary_search 4074, test_memory_1
  4569, test_stdint 4602, spmv AUTO s1 4762, share_test_2 5261). So the stale capture of section 1 needs a DCO line
  about 2.5 ns shorter than any measured route's -- and NO rule checks it: on the default-flow spmv route rule C itself
  reports two VIOLATIONs (val[] and col[], plain ports: margins -149 and -46 ps, and +1 ps on a third), and the gate
  still passes it (a plain station's consumer closes its latch much later than the acknowledge); but nothing in the
  default flow sizes DCO, so the 12-link placeholder's routed length is whatever the placer makes it (2305-5238 ps on
  this route's 10 lines).

## 4. Ordering: why LS / LL in one block is ordered by construction, and how it was checked

The order a later iteration's access needs is built, not raced, for the two shapes bdc lowers on one controller:

- **Within a block (the chain)**: the first accessor's z is forked into the second's token (`c`). A station's
  acknowledge to its inputs (`hold`) rises only on z_ack, i.e. after its RAM access completed and its result was
  taken; the fork's acknowledge is the C-element of both branches. So execution k's first access cannot finish its
  handshake -- and its operands cannot be released for execution k+1 -- until execution k's second access has
  completed (its `c` acknowledged) and returned to zero. L(k+1) after S(k) (LS), S(k+1) after L(k+1), every access of
  one station in order: by the four-phase handshake, for any delays.
- **Across blocks** (no chain; iir's load before its loop, binary_search's two loops): what Dynamatic's own
  mem_controller has -- the arbiter, no order -- and the dataflow; the frontend gives an array a controller (not an
  LSQ) only when its dependence analysis finds nothing the dataflow does not already order (iir: y[0] before the loop,
  y[i >= 1] in it). stores.md section 2's argument (a block's control token waits for its stores) adds order on top.

Two checks of that, both new here (section 5):

- **The order itself, monitored.** Values cannot show an overtaking in these kernels -- an in-place loop's iterations
  touch different addresses -- so memtb now watches every chained port: at each RAM clock edge the arbiter's grant
  says which slot it is, and the sequence must alternate first, second, first, ... (`MEMTB ORDER`, a failure if not).
  `--order-all` applies the same check to an unchained port (binary_search's two loops), where nothing makes them
  alternate: the control that the check can fail.
- **The scatter** (`cells/sim` BD_JITTER, memtb `--jitter SEED:PCT`): every LUT arc of the design drawn per instance in
  [0.7, 1.3] x nominal, reproducibly per seed, the RAM boundary covered for the worst draw; and `--ram-slow N` (every
  RAM's DSETUP / DCO at least N arcs: every access ~50 ns at N = 200), the stress under which a second access that
  could overtake would.

## 5. Numbers

### Every memory kernel of research/tools/suite/kernels.txt, both flows (memtb as changed here, 0 ps, DCO covered)

`memtb.py K VEC --timeout-us 5000` (2 runs per call without refilling, every array read back against the C; the
suite's vector files: kernels/K/vec.hex or research/data/suite/vec/K.hex), default flow and `BDC_AUTO=1`, bdc as on
the branch, memtb with the RAM cover, the RAM monitor and the void fix (the order monitor and the quiet-port host came
later: with 0 changes under an acknowledge in every run below the host never met a busy port, so they change nothing
here; spmv and sobel were rerun with the final memtb: PASS 4/4 and 3/3 in both flows, 92 and 2340 ordered accesses
per flow, 0 out of order). Every DCO raised 12 -> 23 in the testbench (`MEMTB note`, 64 of 64 runs); the
monitor saw the acknowledge at least 2852 ps after the clock edge on every RAM and no read data change under an
acknowledge; no RAM setup or one-hot message in any run. **64 / 64 PASS.**

| kernel | default flow | AUTO | sim time default / AUTO (us) | wall (s) | RAM monitor (default; AUTO same unless noted) |
|---|---|---|---|---|---|
| memsum | PASS 5/5 | PASS 5/5 | 10.6 / 9.9 | 2 / 3 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| dot2 | PASS 8/8 | PASS 8/8 | 23.2 / 21.7 | 5 / 4 | 4 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| gather | PASS 9/9 | PASS 9/9 | 28.4 / 25.8 | 5 / 6 | 4 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| fill | PASS 5/5 | PASS 5/5 | 11.5 / 10.9 | 3 / 3 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| test_bitint | PASS 6/6 | PASS 6/6 | 7.5 / 6.7 | 1 / 1 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| unused_arg | PASS 6/6 | PASS 6/6 | 0.7 / 0.7 | 0 / 0 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| if_loop_1 | PASS 8/8 | PASS 8/8 | 48.2 / 42.4 | 8 / 9 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| if_loop_2 | PASS 8/8 | PASS 8/8 | 43.5 / 37.6 | 6 / 6 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| sumi3_mem | PASS 3/3 | PASS 3/3 | 261.1 / 219.3 | 154 / 151 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| fir | PASS 2/2 | PASS 2/2 | 206.7 / 170.5 | 31 / 32 | 4 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| simple_example_1 | PASS 4/4 | PASS 4/4 | 11.0 / 11.0 | 1 / 0 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| while_loop_3 | PASS 7/7 | PASS 7/7 | 22.9 / 22.4 | 2 / 3 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| if_convert | PASS 3/3 | PASS 3/3 | 68.4 / 62.7 | 19 / 17 | 4 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| test_memory_1 | PASS 6/6 | PASS 6/6 | 3.4 / 3.3 | 1 / 1 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| test_memory_2 | PASS 7/7 | PASS 7/7 | 4.1 / 4.1 | 1 / 0 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| test_bool_array | PASS 4/4 | PASS 4/4 | 1.1 / 1.1 | 0 / 1 | 1 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| binary_search | PASS 7/7 | PASS 7/7 | 49.2 / 44.8 | 3 / 3 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| mul_example | PASS 3/3 | PASS 3/3 | 30.7 / 29.5 | 11 / 11 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| share_test_2 | PASS 3/3 | PASS 3/3 | 60.6 / 59.4 | 70 / 72 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| test_stdint | PASS 4/4 | PASS 4/4 | 32.6 / 31.0 | 2 / 2 | 1 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| spmv | PASS 4/4 | PASS 4/4 | 13.9 / 13.5 | 3 / 3 | 10 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| sobel | PASS 3/3 | PASS 3/3 | 409.2 / 394.8 | 218 / 221 | 8 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| test_flatten_array | PASS 1/1 | PASS 1/1 | 66.9 / 61.9 | 14 / 14 | 4 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| image_resize | PASS 2/2 | PASS 2/2 | 201.6 / 182.2 | 97 / 98 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| vector_rescale | PASS 2/2 | PASS 2/2 | 165.0 / 156.9 | 18 / 20 | 2 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| stencil_2d | PASS 1/1 | PASS 1/1 | 71.5 / 70.9 | 11 / 10 | 6 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| iir | PASS 1/1 | PASS 1/1 | 131.2 / 126.2 | 63 / 59 | 4 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| share_test_1 | PASS 1/1 | PASS 1/1 | 170.9 / 132.4 | 74 / 67 | 4 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| single_loop | PASS 1/1 | PASS 1/1 | 107.7 / 105.2 | 9 / 7 | 6 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| loop_path | PASS 1/1 | PASS 1/1 | 93.9 / 93.1 | 12 / 7 | 6 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| nested_loop | PASS 1/1 | PASS 1/1 | 104.7 / 101.1 | 8 / 6 | 6 bd_mem, ack >= 2852 ps, 0 under-ack changes |
| video_filter | PASS 1/1 | PASS 1/1 | 176.4 / 166.7 | 217 / 220 | 6 bd_mem, ack >= 2852 ps, 0 under-ack changes |

15 of these 32 (the void kernels: simple_example_1, while_loop_3, if_convert, test_memory_1, test_memory_2,
mul_example, share_test_2, test_stdint, test_flatten_array, image_resize, vector_rescale, single_loop, loop_path,
nested_loop, video_filter) did not run at all through memtb at the branch's HEAD: since dyntests, oracle_mem.sh takes a
void kernel and prints `void` per call, and memtb (written by hangs when oracle_mem.sh still refused them and memtb fell
back to its own driver) crashed parsing it -- 11 of them crashed in this table's first pass; fixed here.

### spmv and sobel: the regimes, the controls (memtb, as changed here unless said)

| run | spmv default | spmv AUTO | sobel default | sobel AUTO |
|---|---|---|---|---|
| 0 ps, DCO covered (12 -> 23), the table above | PASS 4/4 | PASS 4/4 | PASS 3/3 | PASS 3/3 |
| 350 ps per arc (no cover needed: ack >= 5688 ps) | PASS 4/4 | PASS 4/4 | PASS 3/3 | PASS 3/3 |
| **`--keep-dco`** (the emitted 12 at 0 ps: the harness before this change, plus the monitor) | **FAIL**: 3 calls' out[] as in section 1, 318 read-data changes under the acknowledge, 4 RAM setup violations (vec[]) | **FAIL**, identical | **FAIL**: call 1 out0 / out[] as in section 1, 23656 changes under the acknowledge | **FAIL**, identical |
| rtl_bench.sh (the bench's own RTL, gate verdict), 0 ps | PASS 4/4 (DCO raised, emit.log) | -- | -- | -- |
| rtl_bench.sh, `RTL_KEEP_DCO=1` | FAIL 1/4, MEMORY wrong in batches 0, 1, 3 (4 RAM setup lines in run.log, not in the verdict) | -- | -- | -- |
| dyntests' own emission (its tree, before the merge), 0 ps covered / 350 ps | **TIMEOUT** at call 0 run 0 / **TIMEOUT** | -- | **TIMEOUT** / **TIMEOUT** | -- |

The last row settles dyntests' "default flow deadlocks": in its tree it did deadlock, at 0 ps (with the boundary met)
and at 350 ps; hangs' token floor, merged since (spmv: `ulink_n_falseResult_36` / `_40` 2-stage), removed it. At 0 ps
WITHOUT the cover the same emission returned wrong values instead of hanging (the journal's observation): the stale
row bounds made every inner loop empty, and the loop that deadlocked never ran.

### The order monitor, the scatter, slow RAMs, and their controls

All memtb, both flows unless said; "values" = out0 and every array against the C.

| run | kernels | result |
|---|---|---|
| order monitor, nominal arcs | the 11 kernels with a chained port (LS in one block: test_memory_1, test_memory_2, mul_example, share_test_2, test_stdint, image_resize, vector_rescale, video_filter; LL in one block: test_bool_array, spmv, sobel) | **0 accesses out of program order in 2 x 32 548** (spmv 92, test_memory_1 48, test_memory_2 52, test_bool_array 16, mul_example 1200, share_test_2 1200, test_stdint 1600, image_resize 7200, vector_rescale 8000, video_filter 10800, sobel 2340 per flow); values PASS |
| control: `--order-all` on binary_search (two loads in two loops: unchained, nothing makes them alternate) | binary_search | 1060 of 1088 "out of order" in both flows: the check fires when the order is not built (not judged; values PASS) |
| scatter +-30%, seeds 1-2 (spmv 1-8) | the 11 above + binary_search, iir, share_test_1 (unchained) | **68 / 68 PASS** (values; RAM monitor 0; where the monitor ran, 0 out of order: e.g. image_resize 14 400, video_filter 21 600, sobel 4680 accesses over the two seeds and flows) |
| scatter +-50%, seeds 1-8 | spmv | **16 / 16 PASS**, 736 ordered accesses per flow, 0 out of order |
| slow RAMs (`--ram-slow 200`: every DSETUP / DCO 200 arcs, ~25 ns each) + scatter +-30% seed 3, memtb with the quiet-port host | spmv, test_memory_1, test_memory_2, mul_example, test_stdint, test_bool_array, binary_search (vector_rescale and iir dropped: ~35 min each at 200-arc RAMs) | **14 / 14 PASS** (values); ordered accesses per flow 92 + 48 + 52 + 1200 + 1600 + 16 = 3008, 0 out of order; the acknowledge >= 24.1 ns after every edge, 0 changes under it (binary_search default took 1529 s of wall) |
| control: `BDC_MEM_NOCAP=1` (no capture latch), nominal and +-30% seeds 1-8 | spmv | **FAIL 18 / 18** (every row's bounds wrong, out0 = row[i+1]: call 1 0x0a for 0, call 3 9 for 5) |
| control: DCO 18 kept (capture ~270 ps after the read data, ~120 ps net of the latch's own arc), nominal, +-30% and +-50% seeds 1-8 | spmv | values right in 18 / 18 (the monitor flags every run: 487-598 read-data changes under the acknowledge, rule C's stricter condition) |

What the controls say. Without the capture the chain's second load rewrites DOADO before the first load's consumers
have taken their word, at the nominal arcs already: the capture is necessary, and memtb sees its absence. The order
check fires on a port whose accesses are not chained. But the scatter did NOT expose a ~120 ps net margin on a
2.7 ns path, at +-30% or +-50% per instance (a long chain's scatter averages out): passing it is weak evidence for
anything held by margin. The order claim rests on section 4's argument and on the monitor, not on the scatter.

**A harness defect the slow-RAM stress found, fixed here.** The first slow-RAM batch failed test_memory_1 and
test_memory_2 in both flows and mul_example in the default flow (its AUTO run was stopped): values, 14-223 read-data
changes under an acknowledge, 2-4 accesses "out of order". In test_memory_1 the first of them came after the last run
of the call had completed, in the host's read-back: on an arbitrated port the host slot
stands outside the arbiter and its acknowledge is gated by its own phase bit, so memtb's host task, which waited only
for that acknowledge to be low, could raise its request while the kernel's last access was still returning to zero
(DSETUP + DCO after the claim drops: ~50 ns at 200 arcs; memtb waits 3 ns). It now waits for every RAM of the port to
have returned to zero; then all three pass (row above). At the nominal arcs the port was always quiet in time (0 changes under an acknowledge in all 64 table runs).
The real bench's host is the PS, microseconds away; that the port is quiet before its first read-back is a timing
assumption of the bench, not checked by anything (section 8).

## 6. The change (harnesses and the simulation model; bdc's emission untouched)

- `research/tools/suite/memtb.py`:
  - **the RAM boundary**: every RAM delay parameter of the DUT whose DCO is shorter than the RAM model's clock-to-out
    + 3 arcs at `--route-ps` is raised in the testbench's instantiation (12 -> 23 at 0 ps; nothing at 350 ps), with a
    `MEMTB note:` line -- the condition rule C requires of every route; `--keep-dco` keeps every emitted RAM delay
    (the negative control). A monitor on every bd_mem counts read data that changes while its acknowledge is high
    (`MEMTB RAM-BOUNDARY`, a failure) and prints the smallest acknowledge-after-edge; the RAM model's setup violations
    and the ports' one-hot checks, until now only in run.log, are printed as `MEMTB VIOLATION` and fail the summary.
  - **program order**: on every chained arbitrated port the RAM edges must alternate first / second accessor
    (`MEMTB ORDER`, a failure if not); `--order-all` applies it to unchained ports too (a control).
  - **the host waits for a quiet port** before each request (section 5).
  - **void kernels**: oracle_mem.sh's `void` lines parsed (memtb crashed on all 15 void kernels at HEAD).
  - `--jitter SEED[:PCT]` (cells/sim BD_JITTER; DSETUP covered too), `--ram-slow N` (a stress).
- `research/tools/suite/rtl_bench.sh`: the same DCO cover through gen_bench.py's `BD_SZ_` macros (`RTL_KEEP_DCO=1`
  keeps the emitted value; emit.log says which); at RTL_ROUTE_PS = 350 nothing changes.
- `cells/sim/bd_prims_sim.v`: BD_JITTER, opt-in (one draw per LUT instance, both outputs). Without it the
  preprocessed model is identical to before (`iverilog -E` of both, comments stripped, `cmp`). cells/rtl/ untouched.
- **bdc/: unchanged** (`git diff <base> -- bdc/` empty), so every emission of every fixture in every mode is
  byte-identical to the branch's by construction; no AUTO emission changed, so no routed smoke was owed for one.
  Nothing in bdc needed changing: the order the brief asked to make hold by construction already does (section 4),
  and the stale captures came from a testbench that ran the design outside the timing every route is held to.

## 7. What it does NOT show

- **One new route, one corner.** The default flow's spmv seed 1 at `worst` is a smoke (CLAUDE.md: 4 seeds); the
  capture margins of section 3 are static numbers on 11 existing routes, not draws. Everything else is RTL: cells/sim's
  cell arcs (zero wire delay with the RAM boundary met, 350 ps per arc, the scatter, slow RAMs) -- handshakes
  complete, values and arrays match the C, the access order holds; nothing about routed timing.
- **The order claim rests on the handshake argument of section 4.** The monitor checks it on every chained port of the
  11 kernels that have one, in both flows, at the nominal arcs, under the scatter and with slow RAMs: a sample of delay
  assignments, not a proof. The scatter's power is limited (the DCO 18 control was not exposed at +-30% or +-50%).
- **Cross-block accesses on one controller** (no chain: binary_search, share_test_1, iir) are ordered by the dataflow
  only; the frontend gives such an array a controller rather than an LSQ only when it finds the accesses independent,
  and bdc checks neither. No kernel here has a load of a later iteration reading what an earlier one stored through a
  controller (the frontend puts such an array on an LSQ, which bdc refuses): a RAW across iterations was not exercised
  -- nothing can exercise it today.
- The RAM model's clock-to-out is prjxray's max (2454 ps) at every corner here; the routed numbers use tighten.py's arc
  values and the same constant.

## 8. Open problems

- **No rule checks the capture.** Rule C stops at bd_mem's acknowledge; the capture closes after the port's
  acknowledge logic, `done`, `ucapen` and a 1.6-1.8 ns fanout net, while the word crosses a DOADO -> latch wire of up
  to 2.3 ns. capmargin.py (out/extra) measures it: 2490-5261 ps on the 11 routes that have a capture, so nothing is near
  failing today; a rule (or the gate, on the routes it judges) is what would catch the route that is.
- **Nothing sizes DCO in the default flow (nor in a BDC_AUTO emission routed without the sizing loop).** Rule C on all
  19 routes at hand (dyntests' 18 smokes + the default-flow spmv here; 101 DCO lines): 17 routes clean (smallest
  margins 516-2754 ps), 2 with VIOLATIONs, both spmv, all on plain ports: default s1 val[] / col[] -149 / -46 ps (the
  gate passed it), AUTO unchained s1 col[] / vec[] -345 / -284 ps. A capture port tolerates ~2.5 ns more than rule C
  asks; a plain port's consumer tolerates a shortfall by its own path length. Neither is guaranteed by construction.
- **The host slot of an arbitrated port needs a quiet port, and only time provides it on the bench.** memtb now waits
  for it; on the board the PS's latency is microseconds against a return to zero of a few ns, and the routed one-hot
  monitor checks the host slot against the kernel slots' requests, not against the RAM's return to zero.
- **sobel's vectors are blind to its in[] reads in 2 of 3 calls** (call 0: the Sobel kernels sum to zero, so the sums
  do not depend on what was read; call 2: in[] constant). A call with non-zero-sum gX / gY and varying in[] would see a
  wrong in[] word on every x.
- Other testbenches of an emitted memory kernel at zero wire delay (tb_store1.v and tb_capture.v are the ones in the
  tree; neither is general) do not cover DCO; a new one should, or run at a plausible hop (350 ps).
