# Deadlocks and hangs over every kernel that emits (subagent `hangs`, 2026-11-18)

PROGRAM 2026-11-18, lead 3: "the suite kernels that deadlock or hang ... fixed in bdc, for every kernel."
Everything here is pre-route RTL (cells/sim/bd_prims_sim.v arc timing) unless a row says routed. The routed numbers
(sections 2 and 3) were built by nextpnr `6e5d224472232d5d` (`cells/verify/toolchain.sh` all ok before every build).

## 1. The table: every fixture that emits, both flows

`bdc/emit.py --no-top` on the 108 fixtures in build/frontend: **45 emit** in all three modes (default, `BDC_AUTO=1`,
`BDC_HOST_MEM=1`), 63 are refused by bdc in all three (unchanged here). Each of the 45 was run, default and
`BDC_AUTO=1` (auto.py's proven MLIR rewrites first, as the flow does):

- **scalar kernels** (26): `bdc/simcheck.py --c-oracle --timeout-us 400` on kernels/K/vec.hex or
  research/data/suite/vec/K.hex (ipow: research/data/eventgraph/gate/ipow17.hex; isprime: research/data/alltable/isp17.hex;
  sum3: suiteb's vectors); gcd, collatz, collatz64, xorshift through simcheck's REFS path (the bench masks their
  inputs, so oracle.sh refuses them);
- **memory kernels** (19): `research/tools/suite/memtb.py` (new; tb_store1.v's recipe made generic): fill every array
  through its `--host-mem` slot, R = 2 runs per call without refilling, read every array back; out0 and every array
  against the kernel's C (oracle_mem.sh, or the same recipe for void kernels and N-D arrays); a run that does not end
  within 5000 us of circuit time is a TIMEOUT. Vectors: the suite's v2 files; for Dynamatic's nine store tests new
  files in research/data/suite/vec/ (memvec.py; inputs chosen so the C stays in bounds: if_convert's a >= 60, loop_path
  and single_loop / nested_loop with exits before N, while_loop_3's bound <= 10000 and INT_MIN).

"before" = the branch as cloned (7197d85c2); "after" = with the token floor's pass-through modes (section 2). The
after column is measured where the Verilog changed (matrix, stencil_2d default) and is the before column elsewhere:
those 131 outputs are byte-identical.

| kernel | kind | vectors | default before | default after | BDC_AUTO (both) |
|---|---|---|---|---|---|
| straight | scalar | 12 | PASS 12/12 | = | PASS 12/12 |
| countloop | scalar | 10 | PASS 10/10 | = | PASS 10/10 |
| sqrtsub | scalar | 13 | PASS 13/13 | = | PASS 13/13 |
| nest3 | scalar | 12 | PASS 12/12 | = | PASS 12/12 |
| twoloops | scalar | 11 | PASS 11/11 | = | PASS 11/11 |
| brhash | scalar | 10 | PASS 10/10 | = | PASS 10/10 |
| lfsrfind | scalar | 10 | PASS 10/10 | = | PASS 10/10 |
| quadrec | scalar | 10 | PASS 10/10 | = | PASS 10/10 |
| horner | scalar | 11 | PASS 11/11 | = | PASS 11/11 |
| fold64 | scalar | 10 | PASS 10/10 | = | PASS 10/10 |
| varshift | scalar | 10 | PASS 10/10 | = | PASS 10/10 |
| cmpchain | scalar | 17 | PASS 17/17 | = | PASS 17/17 |
| nested | scalar | 11 | PASS 11/11 | = | PASS 11/11 |
| branchloop | scalar | 14 | PASS 14/14 | = | PASS 14/14 |
| factorial | scalar | 12 | PASS 12/12 | = | PASS 12/12 |
| iterative_division | scalar | 15 | PASS 15/15 | = | PASS 15/15 |
| iterative_sqrt | scalar | 12 | PASS 12/12 | = | PASS 12/12 |
| test_loop_free | scalar (4 words) | 10 | PASS 10/10 | = | PASS 10/10 |
| test_int16 | scalar (no argument) | 1 | PASS 1/1 | = | PASS 1/1 |
| sum3 | scalar (3 words) | 6 | PASS 6/6 | = | PASS 6/6 |
| ipow | scalar | 17 (ipow17) | PASS 17/17 | = | PASS 17/17 |
| isprime | scalar | 18 (isp17) | PASS 18/18 | = | PASS 18/18 |
| xorshift | scalar (REFS) | 8 | PASS 8/8 | = | PASS 8/8 |
| collatz | scalar (REFS) | 8 | PASS 8/8 | = | PASS 8/8 |
| collatz64 | scalar (REFS) | 3 | PASS 3/3 | = | PASS 3/3 |
| gcd | scalar (REFS) | 6 | PASS 6/6 | = | PASS 6/6 |
| memsum | memory, read | 5 calls x 2 runs | PASS | = | PASS |
| dot2 | memory, two arrays | 8 x 2 | PASS | = | PASS |
| gather | memory, a[b[i]] | 9 x 2 | PASS | = | PASS |
| fill | memory, write | 5 x 2 | PASS (arrays = C) | = | PASS |
| test_bitint | memory, narrow | 6 x 2 | PASS | = | PASS |
| unused_arg | memory, dropped memref | 6 x 2 | PASS | = | PASS |
| if_loop_1 | memory | 8 x 2 | PASS | = | PASS |
| if_loop_2 | memory | 8 x 2 | PASS | = | PASS |
| sumi3_mem | memory, N = 1000 | 3 x 2 | PASS | = | PASS |
| fir | memory, two arrays, N = 1000 | 2 x 2 | PASS | = | PASS |
| simple_example_1 | void, store in the exit block | 2 x 2 | PASS (a = C) | = | PASS |
| while_loop_3 | void, store after a loop | 5 x 2 | PASS | = | PASS |
| if_convert | void, store in a do-while | 2 x 2 | PASS | = | PASS |
| test_flatten_array | void, 3-deep nest, 3-D arrays | 2 x 2 | PASS | = | PASS |
| loop_path | void, loop with a break | 3 x 2 | PASS | = | PASS |
| single_loop | void, data-dependent exit | 2 x 2 | PASS | = | PASS |
| nested_loop | void, two-deep nest | 2 x 2 | PASS | = | PASS |
| **stencil_2d** | memory, 3-deep nest | 2 x 2 | **DEADLOCK** (call 0) | **PASS** | PASS |
| **matrix** | void, 3-deep nest, store | 2 x 2 | **DEADLOCK** (call 0, after the first inner loop) | **PASS** (call 0, 1 run: outC 900 / 900 = C, every one of the 900 stores = C when issued; 1013 us of circuit time) | PASS (stores.md: 1 call, outC 900 / 900; this Verilog unchanged since) |

**45 fixtures emit; before: 43 / 45 complete in the default flow (matrix and stencil_2d deadlock), 45 / 45 in
BDC_AUTO (matrix's from stores.md; its AUTO Verilog is unchanged since, my own 1-call run was stopped for time);
after: 45 / 45 in both.** No wrong value anywhere. kernels/SUITE.md said "deadlock" for nest3, quadrec, nested and lfsrfind:
stale since ringfloor (2026-11-18 04:44); all four pass in both flows here.

## 2. The deadlock left: an inner loop's exit and its next entry (matrix, stencil_2d)

**Where it stops (matrix, default flow, RTL, call 0).** Load and store completions counted: the first inner loop
runs (30 loads per array, 30 firings of the inner header control_merge2, 1 store, control_merge1 twice), then
nothing for 300 us. The VCD at the deadlock (every handshake of the kernel's top level, t = 44 us): the inner
loop's next initial value k = 0 sits in `ulink_n26` (one stage; req = 1, ack = 0 toward mux5), the next entry token
sits in `ulink_n32` toward control_merge2 (req = 1, ack = 0), and every handshake from control_merge2's result through
the exit to that link is in its return to zero (req = 0, ack = 1): result_5 -> cond_br10 -> falseResult_22 (the
inner exit) -> control_merge3 -> fork22 -> stdone_join_bb4 -> cond_br15 -> trueResult_35 (the middle back edge) ->
control_merge1 -> fork5 -> constant5 -> br10 -> fork6 -> extui9 -> n26. The link holds k = 0 until mux5 takes it;
mux5 takes it with its select, control_merge2's NEXT index (fork11 -> ulink_n49__5); control_merge2 cannot fire again
until its previous output has returned to zero, which is the chain the link is holding up. A cycle with no token.

**Why the token floor missed it.** ringfloor's walks see every loop iterating and never walk a loop's entry or exit
channels, so the circuit between an inner loop's last trip and its next entry -- the outer loop's own ring, through
the inner loop -- was never checked. In the walk view the deadlock above is: forward from control_merge2's result
along the exit, the middle back edge and the entry into mux5 (1 stage, 1 back edge: 1 - 2 = -1), a join turn at mux5
(+1), backward along the select to control_merge2's index (0), a fork turn at control_merge2 (result and index leave
together): **0 tokens**. BDC_AUTO's rule M (an output link inside every loop-header control_merge) adds +1 to it,
which is why both kernels already completed under BDC_AUTO. nest3 (also three deep) has no such walk: its entries
carry more stages.

**The change** (bdc/emit.py; `BDC_TOKEN_FLOOR_PASS=0` turns it off, negative controls only). For every loop P with a
loop nested in it, the floor also walks the graph in P's *pass-through mode*: P iterates, every loop nested in P passes
through in one trip (its entry and exit channels walked, with no tokens; its back edges not walked), every other loop
as before. Loops and nesting come from Dynamatic's blocks (each loop has one header block; L is nested in P when P's
header block < L's and L's latch block <= P's). One fix to the token test on the way: Dynamatic puts the extui of a
loop's initial value in the loop's own header block (matrix's extui9, extui7), which counted it as a back edge; the
test now reads a cast's operand's block. That alone changes no output.

**Checks.**
- Output: 45 fixtures x 3 modes, `--no-top`, before (7197d85c2) and after: **131 of 135 byte-identical**; the 4 that
  differ are matrix and stencil_2d, default and `--host-mem`, each by exactly one stage (`ulink_n26` 1 -> 2,
  `ulink_n45` 1 -> 2); BDC_AUTO's outputs of both unchanged; the 189 refusals unchanged (same exit code, same error).
  `BDC_TOKEN_FLOOR_PASS=0` gives the before output of both kernels in all three modes, byte for byte; with it,
  `BDC_LINK_DEPTHS=ulink_n26=2` (`ulink_n45=2`) gives the after output byte for byte. So the negative control (the
  before column, DEADLOCK) and the fix differ by that one stage only.
- RTL: stencil_2d default **PASS** 2 calls x 2 runs, out0 and all three arrays = C (was DEADLOCK at call 0, the
  stall at 26.2 us of circuit time, nothing moving after it: the same picture, n45 holding k2 = 0); matrix default
  **PASS** on call 0 (one run of 27000 inner trips, 1013 us of circuit time: outC read back 900 / 900 = C, every store
  checked against C as it was issued, inA / inB unchanged; the whole two-call file was not run: ~20 min of wall per
  run).
- Routed smoke, stencil_2d (one seed: a smoke, not a result; `research/tools/suite/smoke.sh stencil_2d 1 default`:
  build_bench.sh BD_NO_TIGHTEN=1 BD_SIZES=none BD_DSP=1, seed 1, --freq 83, nextpnr 6e5d224472232d5d; then bench_gate.sh
  at worst with GATE_MEMEXP = oracle_mem.sh's final arrays (2 runs per call) and GATE_ANNOTATE=1):
  - with the fix (ulink_n45 a 2-stage pipe): route sdf b5afb083, 93.74 MHz, EQUIVALENT, ANNOTATE_DONE 0 SDF warnings;
    **PASS 2 / 2**: both calls complete, both runs of each agreeing, out0 000030db / 0007a840 = the C, and all three
    arrays read back after each call = the C's final contents.
  - the negative control, the same flow with `BDC_TOKEN_FLOOR_PASS=0` (ulink_n45 one stage, nothing else different):
    route sdf a9e684aa, 91.87 MHz, EQUIVALENT, ANNOTATE_DONE 0; **FAIL 0 / 2: both calls hang** (completed = 0 after
    16594 bench cycles; the arrays wrong after both).
- `research/tools/suite/ring_tokens.py` (now every mode, and its cycle view with the same cast rule): over the 45
  fixtures x {default, BDC_AUTO}, 90 / 90 exit 0 (no short cycle, no short walk); with `BDC_TOKEN_FLOOR_PASS=0` exactly
  matrix and stencil_2d default report a 0-token walk, in the middle loop's pass-through mode. Before the cast rule the
  cycle view flagged matrix (-2), stencil_2d (0) and test_flatten_array (-2 / 0), all through an extui counted as a back
  edge; test_flatten_array completes in both flows, and the cycle view cannot see the matrix walk anyway (a fork / join
  walk, not a directed cycle: ringfloor.md).

**What this does not show.** Not a proof of liveness (the same model as ringfloor.md, one more family of modes;
memory ops still walked through, never turned at). The pass-through mode is the one-trip steady state; the deadlock
it caught happens at the transition after a 30-trip (matrix) or 3-trip (stencil_2d) inner loop, and that the one
predicts the other is shown on these two kernels, not derived for every shape. Routed: stencil_2d on one seed each
way (above); matrix not at all (void: the bench cannot run it).

## 3. The automatic ipow seed-4 start-up hang

Flow v1's automatic ipow route on seed 4 (farm suite1 task 28; its sizes research/data/suite/farm/suite1/
ipow_4_sizes_final.vh) hangs at the first call on draws 10401 and 10404 (journal 2026-11-18 05:54 / 06:28): completed = 0,
odata = x, the bench FSM x; with +META_INIT=0 or =1 it passes 17/17. Rebuilt here (`rejudge.sh ipow 4 <sizes> 0`, nextpnr
6e5d224472232d5d): **sdf 1ac15af5 = the farm's**, P 21607 ps, 1286 kernel LUTs, EQUIVALENT, ffmux-clean (the .bit differs
from the bot's 00:58 rebuild with 9c732bc6303458df, 447950e1 -> a41f1ae5: the const-sinks patch's GND pips; same SDF).

**Which storage starts X, and why the run does not recover** (draw 10401: chains 0.2517, rest 0.2416, CARRY4/F7/FF
0.5739; ipow17, first call (3, 1); every net of the bits-decoded netlist dumped for 6 us; no +META_INIT):
- The first net to go from a value to X is the stage of `ulink_n_trueResult_12` (1659657 ps), fed by the steer
  `cond_br9`, which sends the control token round the loop or out of it. Its LUT reads the request on A3 (ucond_br9_req
  through a 370 ps wire) and the select on A1 (n32_data, cmpi2's `e >> 1 > 0`, through a 1096 ps wire). ucond_br9_req
  rises at 1659023 (at the pin about 1659393); n32_data has no value until 1658863 (at the pin about 1659959): **the
  request is at the steer 566 ps before the select has any value**, so both branches go X. The X enters the link, the
  loop header's arbiter (control_merge0) and the bench's FSM; a C-element holds an X in its own feedback, nothing
  clocks it out, so the call never completes (the bench's next batch resets the kernel: batches 1-16 pass).
- cmpi2's output request (n32_req) rises at 1658411, 452 ps BEFORE its data has a value. Its operand e >> 1 comes from
  the data latch of `ulink_n31__1` (fed through shrsi0 from the latch of `ulink_n12__1`): n31__1_req at 1655476, its
  32 bits get their first value between 1655670 (bit 0, +194 ps) and 1657204 (bit 20, +1728 ps; bits 14-23 last),
  the enable net's skew over 16 latch LUTs (bd_link.v's header measured 1125 ps on another route). These latches are
  `bd_latch`, which has no reset: until the first token's enable reaches a bit, that bit is X (on the die: whatever it
  powered up with). With e = 1, e >> 1 = 0, and "0 > 0" is defined only when every bit is.
- **The sizing rule saw this path and the flow shipped it anyway.** Farm task 28's last audit (ca_4.txt, flow v1, at
  the rule's corner: chains / LUT / wire 0.21, CARRY4 / F7 / FF 1.0): `A -719 ps` on ucmpi2 "from ulink_n31__1.ctl: req
  2858, data 3473", `E -734 .. -1070 ps` on cond_br6..9 (select after request), proposal UCMPI2 5 -> 12 (it had been
  10 two iterations before; v1 lowered it). The loop ended NOT CLEAN after MAXIT 4 and v1 kept that route.
- **The race is there in every call; the gate only sees it at start-up.** Same route, same draw, +META_INIT=0, a
  warm-up call (3, 3) then (3, 0x200000) (every net dumped for 9 us): at that call's first test the steer's request
  reaches its LUT about 476 ps before the select's new value, so `cond_br9` first raises its EXIT branch
  (falseResult_13) for 474 ps, then switches to the continue branch; at the next iteration the compare's output itself
  glitches 1 -> 0 -> 1 for 359 ps (bits 19 and 20 of e >> 1 change together) and the exit branch gets a 359 ps runt in
  the middle of a continuing loop. In these 9 us (two calls of 2 runs, 48 trips in all): **40 runts narrower than 1 ns
  on the exit branch (17-474 ps), 28 on the continue branch (26 of them passed on by `ulink_n_trueResult_12`'s
  controller), 18 on the back edge of e >> 1 (trueResult_8; 9 through its link)**. The answers are right because the gate's runt model (SIM-VS-BOARD row 4: a
  pulse shorter than the receiving C-element's loop delay minus WIN / 2 is rejected; TAU = WIN = 150 ps, unsourced)
  rejects every one. At start-up the stale select is X instead of a wrong value, the X is not rejected, the
  C-elements hold it, and the call hangs. That is also why (3, 0x200000), (3, 0x400000), (5, 0x100000) pass after a warm-up
  call (5 / 5 batches x 2 runs, with and without +META_INIT=0): their wrong-branch pulses are defined runts, and
  rejected. (3, 3) as the FIRST call passes too (3 / 3 for (3, 3), (3, 1), (5, 13) with no +META_INIT, =0 and =1; not
  traced: "1 > 0" has a value once bits 0 and 31 do, "0 > 0" only once all 32 do). **So
  +META_INIT=0 / 1 passing never showed the route right; X start-up is the one place the gate catches this race.**
- **A clean route has none of it.** The ipow board candidate (flow v3 seed 2, BOARD-QUEUE item 38, sizes
  research/data/suite/board/ipow_v3_s2_sizes.vh; rebuilt here: sdf 81bbe268 = the bot's, P 22711 ps, EQUIVALENT,
  ffmux-clean; UCMPI2 = 10), the same draw, vectors and +META_INIT=0, 9 us: **no pulse narrower than 1 ns on any of
  the eight steer outputs** (every pulse a whole handshake); both calls right.
- The rebuilt route with the reset polarity below (different placement) has none of it: in the same 6 us trace,
  draw 10401, ipow17, no +META_INIT, no pulse narrower than 1 ns on any of the eight steer outputs; cmpi2's data
  arrives 1.3 ns BEFORE its request there (it arrived 452 ps after it on the original route).

**Can bdc define it at reset?** Yes, as a polarity (CLAUDE.md), with no new primitive and no cells/rtl change:
`BDC_LINK_RST=1` (opt-in; unset, every output is byte-identical) makes every link's data latch `bd_latch_rst` with
RESET_VALUE 0 (cells/rtl/bd_latch.v), in a link bdc composes from bd_link's own cells and instance names (bd_link_ctl
`ctl`, bd_delay `rdly` / `uack`), so the sizes and every rule's chain names apply unchanged. After reset nothing in the
kernel is X. Cost: one LUT per latch bit instead of one per two.

**Measured (nextpnr 6e5d224472232d5d, seed 4, the same sizes file, `BDC_LINK_RST=1 BDC_AUTO=1`, rejudge.sh):** route
sdf 995cfe18, P 23272 ps (the original: 21607), 4749 occupied LUT sites in the bench (4348: +401, the latch pairs split),
EQUIVALENT, ffmux-clean; **draws 10401, 10402, 10403, 10404: PASS 17/17 each, no +META_INIT** (10401 and 10404 are
the draws that hang on the original route). And cmpi2's output is defined 6.8 ns after the start (e >> 1 = 0 from the
reset).

**But the reset is not what fixed this route, and it would hide the race from the gate.** The rebuilt route is a
different placement, and on it the exit test arrives 1.3 ns ahead of the steers' requests and no steer emits a runt
(above): it would pass without the reset too, as far as this shows. On the original placement the race is there in
every call, and only X start-up makes the gate see it. **The fix is the sizing, on the same route:** the original route's own bits and prjxray SDF, with
`research/tools/fifteen/sdf_inject.py` adding 1500 ps to the four arcs from ucmpi2's matched delay (udly.chain.g[4])
to the joins of cond_br6..9 (the rule asked for UCMPI2 5 -> 12; nothing else changed, X start-up kept, no +META_INIT):
**draws 10401 and 10404 PASS 17/17**, batch 0 ((3, 1)) completing in 24 cycles as on every other route. Without the
1500 ps the same bits and SDF hang at batch 0 (the bot's runs, and the trace above).

**Recommendation.** Keep the gate's X start-up (the owner's choice, 2026-11-16): on this route it is the only thing
that failed. Leave `BDC_LINK_RST` off (it stays as an opt-in switch, byte-identical when unset): it removes X at
start-up for every kernel, and with it this race would pass every gate. Do not ship a route the rule calls NOT CLEAN
(flow v1 did here: A -719, E -1070 on the loop test; later flows still ship "NOT CLEAN by 2 / 4" routes, journal
2026-11-18 05:06 and 08:35). A cheap check the gate could add: no pulse narrower than ~1 ns on any steer output (a
steer's output rises only with a request whose select is stable, so a runt there is a select race by construction).


**What this does not show.** One route and four draws (and one injection) of one kernel; the runt counts are from
one draw (10401) and 9 us of circuit time. Whether a 0.47 ns runt on the exit branch is captured on the die is what
BOARD-QUEUE item 2 (H_RUNT) measures; the gate's runt model is unsourced. The other v1 / v2 routes were not scanned
for steer runts. The LINK_RST route's sizing was not audited (the sizes are the original route's).


## 4. Files

- `bdc/emit.py`: the token floor's pass-through modes (`_tf_structure`, `_tf_nested`, `tf_pass_modes`, `token_graph(...,
  mode=)`, `token_floor` over every mode; `BDC_TOKEN_FLOOR_PASS=0`), a back edge read from a cast's origin block;
  `BDC_LINK_RST` (opt-in; `bdc_link_rst` / `bdc_pipe_rst` generated from frozen cells).
- `research/tools/suite/ring_tokens.py`: the walk view reports every mode.
- `research/tools/suite/memtb.py` (new): RTL check of any kernel with memories (or none), out0 and every array against
  the C; `--route-ps`, `--vcd`, `--dut`. Negative controls: `BDC_MEM_NEG_STORE=addr` on fill FAILS 4 / 5 calls (32, 32,
  13, 2 elements wrong, the n = 0 call stores nothing), `=data` on simple_example_1 FAILS 2 / 2 (a[0] = 0x65, the C 0x64).
- `research/data/suite/vec/{if_convert,loop_path,matrix,nested_loop,simple_example_1,single_loop,stencil_2d,
  test_flatten_array,while_loop_3}.hex` (new, memvec.py).
- `kernels/SUITE.md`: the four stale "deadlock" cells, the memory rows' RTL column, a section with this table, finding 6.
- This file.

