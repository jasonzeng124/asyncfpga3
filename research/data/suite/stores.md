# Stores in bdc (subagent `stores`, 2026-11-18)

Until this, `bdc/emit.py` refused every memory controller that owns a store (`EmitError: mem_controller at line N has
a store accessor ...`): 33 of Dynamatic's integer tests needed it, 9 as their only blocker
(research/data/suite/dyn/README.md). This is the smallest lowering that keeps Dynamatic's completion promise, a suite
kernel that writes memory (`kernels/fill`), and what was checked. Everything routed here was built by nextpnr
`6e5d224472232d5d` (`cells/verify/toolchain.sh`: every patch fingerprint ok; the const-sinks patch build of
2026-11-18 01:27, commit 1b10f5dec; the subagent preamble's `9c732bc6303458df` is the binary before it).

## 1. What Dynamatic promises (its sources, read)

`dynamatic/data/verilog/handshake/mem_controller_loadless.v` (a controller's store side; `mem_controller.v` is it plus
a read arbiter) and `mc_control` in `data/verilog/support/mc_support.v`:

- `counter` (remainingStores, 32 bits, clocked): `+ ctrl[i]` for every count token presented this cycle (one per
  basic block that holds stores, per execution of that block; its value is that block's number of stores on this
  controller -- the `constant` operands of the accessor list), `- 1` per store issued to the RAM (`storeEn`).
  `ctrl_ready` is tied to 1: count tokens are never back-pressured.
- `allRequestsDone = (remainingStores == 0) && no count token valid this cycle`.
- `mc_control`: memStart moves IDLE -> RUNNING; ctrlEnd ("no more requests will come") is latched once;
  `memEnd_valid = ctrlEnd latched & allRequestsDone & RUNNING`; memEnd's handshake returns the FSM to IDLE.
- Loads are not tracked (its own comment: "we should also check that there are no loads pending").
- The function's `end` takes every memEnd as an operand: the call returns only when every controller says done.

So the promise is: **a call returns only after every store it made has reached the RAM.** Dynamatic keeps it with a
counter that is not ordered against ctrlEnd either: a count token still in a buffer when ctrlEnd is latched with the
counter at 0 would let memEnd fire early. Presumably the clocked circuit's short count path (a constant, accepted
every cycle) keeps that from happening; not checked here.

## 2. The lowering (`bdc/emit.py` `store_completion_rewrite`, `_op_store`, `_op_mem_controller`, `_op_end`)

There is no clock to run a counter on, and an asynchronous up/down counter would need an arbitrated merge of the +k and
-1 streams, an accumulator ring and a steer -- and would still race ctrlEnd: the count token of a block's last
execution and the control token that becomes ctrlEnd leave the same fork on different paths, so nothing structural
makes the count arrive first. What is built instead uses no counter and no new cell:

1. **Each store's completion becomes a channel.** The store station's `z` (bdc/mem.py: `z_req = done`, the RAM has
   answered, i.e. the write edge has happened and DCO has elapsed) was tied off. The rewrite gives each store node a
   third result `<addressResult>_stdone` (control).
2. **Each block's outgoing control token joins its stores' completions.** For every basic block B that holds a
   store: `stdone_join_bbB = join(B's outgoing control token, completion of every store in B)`, and B's terminator
   (`br` / `cond_br` whose data operand is control-typed; exactly one per block, else refused) takes the join's
   output instead. The exit block has no terminator: its stores join their own controller's ctrlEnd
   (`stdone_join_<controller>`; refused if that ctrlEnd does not come from the block).
3. **memEnd is unchanged**: the load-only lowering, a `bd_link` holding memStart joined with ctrlEnd.
4. **The count tokens are checked and sunk.** Per controller: exactly one count constant per block that has stores on
   it, its value equal to that block's number of stores on it, none elsewhere (else refused). Then `bd_snk` at the
   controller, so their producers are not stalled.
5. **The function's data results wait for the store controllers' memEnds.** bdc's `end` drives each result port from
   its own operand, so out0 could leave while the last store is in flight and a caller (the bench) would read the array
   early or start the next call. For a function with a store, `_op_end` joins the data results and the memEnds of the
   controllers that own a store, and forks the joined request to their ports. Only those: one of the other control
   results is typically the start token passed straight through (`single_loop`: `end ... %0#1`), and holding it held
   the start fork's acknowledge and with it the loop header's return to zero until the call ended -- a deadlock,
   measured (the first version joined every operand; fill's RTL run stopped after one store).

The rewrite is on the graph (a `join` node appended, a result added, one operand replaced), before every analysis
(`link_sites`, `ring_depths`, `token_floor`, BDC_AUTO's rules), so the new cycles through the stores get their storage
like any other. It runs only for a function with a store; nothing else changes (section 3, byte-identity).

**Why ctrlEnd is after every store.** (a) A basic block executes each of its ops once per execution, so each execution
of B yields exactly one completion per store in B (Dynamatic's own count constants say the same, and step 4 checks
them); a station handles one access at a time, so completions come out in execution order and the join pairs the k-th
outgoing token of B with the k-th completion of each of its stores. (b) Control is one token passed from block to
block, so every block execution lies on the causal chain that ends in the exit block, whose control is ctrlEnd. Hence
ctrlEnd, memEnd, and (step 5) out0 are causally after every store of the call: ordered by construction, not by a race.
This needs Dynamatic's single-token control (no speculation: bdc ignores `dynamatic.speculate`).

**What it costs.** A block's successor cannot start until the block's stores have landed: the control token waits for
each store (DSETUP + RAM + DCO, plus the station's join) every iteration. Dynamatic lets control run ahead of stores.
Not measured against a counter design (none exists here).

**The previous iteration's store and the next iteration's load (test_memory_5's question).** Not shown -- no kernel
with a load and a store on the same array can be built and run here yet (section 6). What the lowering gives, as an
argument only: execution k+1 of a loop body B starts from B's outgoing control token of execution k, which now waits
for every store of execution k. So every access of execution k+1 whose operands depend on that execution's control
token -- its address through a mux whose select is the header's control_merge index (every loop-carried value in
Dynamatic's lowering), or a constant triggered by the block's control -- is after every store of execution k. An
access whose operands do not depend on it (a value from a `source`-triggered constant, a value computed before the
loop and passed in without a mux) is not ordered by this. Nothing checks which case a kernel is in; Dynamatic's LSQ
placement is still what decides whether a kernel gets a controller at all.

**Within one iteration** the order of a controller's accessors is bdc's token chain (`prev.z -> next.c`,
bdc/mem.py), unchanged: one accessor, or two with the store first (SL). A store that is not the last accessor (SL)
now needs its completion twice -- the next accessor's token and its block's join -- and that fork is not built:
**SL is refused** (`a store chained before a load on an arbitrated port`). So today: a controller with exactly one
accessor, a store (S), or loads only. `mc:load1st` (LS, a load first) is refused as before.

## 3. Checks and numbers

### Emission

- **Byte-identity.** `emit.py --no-top` on every fixture in `build/frontend/` (105 directories), before (HEAD
  c7808ea6d) and after, in three modes: default, `BDC_AUTO=1`, `BDC_HOST_MEM=1`. The 33 fixtures that emitted before:
  **99 of 99 outputs `cmp`-identical**. Every fixture that failed before fails after with the same first error, except
  the 9 below. Re-checked after the bd-config.json change (all 129 outputs identical).
- **Dynamatic's tests whose only blocker was the store refusal: all 9 now emit**, in all three modes: `if_convert`,
  `loop_path`, `matrix`, `nested_loop`, `simple_example_1` (store in the exit block: the ctrlEnd form), `single_loop`,
  `stencil_2d`, `test_flatten_array`, `while_loop_3`. Each of the 27 modules, and fill's 3, elaborates against
  `cells/rtl/` (yosys `read_verilog -lib +/xilinx/cells_sim.v +/xilinx/cells_xtra.v`, `hierarchy -check -top
  bdc_<name>`: no error, no warning; the same command without the primitive library fails on LUT6_2, so it can fail).
  `map.py --report` on single_loop: "buildable today". Nothing of these 9 was routed.
- `research/tools/suite/dyn_blockers.py` (updated: `mc:store` now means "a store that is not its controller's last
  accessor"): 43 of the 106 frontend outputs have no blocker (33 before, + the 9, + fill). 13 tests now need only
  `mc:load1st`; 33 tests lost the `mc:store` tag.

### RTL (cells/sim primitives, zero wire delay: functional only)

`research/tools/suite/tb_store1.v` (fill through its `--host-mem` port: fill the array, run the kernel twice without
refilling, check out0 against the oracle, read every element back against the C's final array):

- fill, default flow: **5 calls x 2 runs, out0 10/10 = C, arrays 5/5 calls x 32 elements = C**. BDC_AUTO=1: the same.
- negative controls (`BDC_MEM_NEG_STORE`, bdc/mem.py: every store station flips bit 0 of its address / data):
  addr: arrays wrong in 4 of 5 calls (32, 32, 13, 2 elements; the n = 0 call writes nothing); data: 4 of 5 (32, 32,
  7, 1). out0 stays right in both (it does not read the array): the read-back is what catches a bad store.
- Dynamatic's `single_loop` (void; three 1000-word memories), its own completion (`c_end`): 2 calls (501 and 51
  iterations), **c read back 1000/1000 = C both times**. `simple_example_1` (the store in the exit block, joined
  into ctrlEnd): 2 calls, a read back 100/100 = C. `matrix` (the store in the middle block of a triple nest): default
  flow deadlocks with and without the join (see below); `BDC_AUTO=1`: 1 call, outC 900/900 = C. The C ran through a driver of the oracle_mem recipe
  (oracle_mem.sh refuses void kernels).
- The RTL testbench samples the host's read data 3 ns after the acknowledge: in this model bd_mem's placeholder DCO
  (12 LUT arcs, about 1.5 ns) is shorter than the RAM model's clock-to-out (2.454 ns), and sampling at +0.5 ns read
  the previous word. Post-route DCO is a routed chain checked by tighten.py rule C; the gate below is the judge.

### Routed (fill)

Builds: `cells/hw/build_bench.sh fill` with `BD_NO_TIGHTEN=1 BD_SIZES=none BD_DSP=1 NEXTPNR_SEED=s` (`--freq 83`,
`--host-mem`; research/data/alltable/run_default.sh's flags), each in a private copy of this tree
(the subagent's build_seed.sh; its scripts and the RTL testbenches of the Dynamatic tests are in its out/extra/). Gate: `research/tools/eventgraph/bench_gate.sh ... worst` (netlist decoded
from the .bit, fasm_equiv verdict, prjxray SDF, chains 0.21, CARRY4/F7F8/FF and RAMB18E1 1, rest 0.288, + M scatter,
FIXED mode, 2 runs per call at 83.3 MHz) with `GATE_MEMEXP` = oracle_mem.sh's ORACLE_MEMOUT (every array read back
after each call and compared with the C's final contents), `GATE_PLUSARGS=+MEMCHECK=1` (every word read back after
each fill), `GATE_ANNOTATE=1`, `PS_MON_GEN=cells/gls/ps/gen_memport_mon.py` (the port's one-hot check on the netlist).

| route | seed | Fmax (MHz) | .bit md5 | gate worst | fasm_equiv | gate.vvp | one-hot monitor (netlist) |
|---|---|---|---|---|---|---|---|
| fill | 1 | 107.16 | 056e2452 | **PASS 5/5**, arrays = C after every call, fill read-back 0 bad | EQUIVALENT | ANNOTATE_DONE, 0 SDF warn/err | 448 host / 160 kernel reqs, 0 overlaps |
| fill | 2 | 119.73 | e70c93c7 | **PASS 5/5**, same | EQUIVALENT | ANNOTATE_DONE, 0 | 448 / 160, 0 overlaps |
| fill | 3 | 108.32 | 1484a66c | **PASS 5/5**, same | EQUIVALENT | ANNOTATE_DONE, 0 | 448 / 160, 0 overlaps |
| fill | 4 | 98.09 | 8b43821a | **PASS 5/5**, same | EQUIVALENT | ANNOTATE_DONE, 0 | 448 / 160, 0 overlaps |
| fill, `BDC_MEM_NEG_STORE=addr` | 1 | 102.03 | feeb2e89 | **FAIL 1/5**: arrays wrong after calls 0-3 (32, 32, 13, 2 of 32 elements differ from the C); out0 right on all 5; the n = 0 call (no store) passes | EQUIVALENT | ANNOTATE_DONE, 0 | 448 / 160, 0 overlaps |

The negative control is the same kernel with every store's address bit 0 flipped in the generator (seed 1, same
flags): its answers are all right and its stores all happen (160), so only the arrays' read-back can catch it, and it
does, on exactly the calls that store -- the same damage counts as the RTL negative control. 160 kernel requests =
the C's stores, (32 + 40 + 7 + 1 + 0) x 2 runs. The answers are the oracle's (out0 d86f2f64
302b3fae 02345ec0 00000004 00000000). Latency per call (BENCHRES latmin, host cycles of 12 ns), n = 32, 40, 7, 1, 0:
seed 1 208 / 259 / 50 / 12 / 7, seed 2 227 / 283 / 54 / 13 / 8: about 6.4-7.0 cycles (77-84 ns) per loop trip, the
store's round trip included. Seeds 3 and 4 finished after the subagent stopped (the session hit the week's usage limit; read
by the main session 2026-11-18 16:52 UTC from the subagent's run directory): four routes, every one PASS 5/5 at the
worst corner; one corner only, no draws.

Static screen (`cells/verify/tighten.py` on each route's SDF; the gate is the judgement): rule B, the RAM's setup
(the store's address and data before the manufactured clock): seed 1 3457 / 3792 ps, seed 2 2605 / 2860 ps, ok;
rule C (clock-to-out): 1901 / 2057 and 2057 / 2450 ps, ok -- at bd_mem's placeholder DSETUP 8 / DCO 12. Rule D
(a steer's select stable before its request) reports 11 VIOLATIONs on each route: every steer of the kernel,
including the 5 of the entry block that the store lowering does not touch; the default flow does not size selects
(BD_NO_TIGHTEN=1: emit.py's SELECT_PAD = 4 estimate, PAD by 10-15 asked). Not investigated; the gate passed on both.

### The automatic path (BDC_AUTO=1, sizes from the rule)

`research/tools/suite/suite_one.sh fill 1 2 3` (PNR_TIMEOUT=3600, CA_JOBS=2; RUNS under the subagent's directory):
**status=BUILD-FAILED (it=2: TIMING FAILED: 78.75 MHz < 83 MHz target)** -- the bench's clocked side (its critical
path is in the PS-domain logic, `$auto$ff` -> abc LUTs -> a mux8, not the kernel) missed 83 MHz on the third route of
the sizing loop, so the loop stopped and no draw ran. Iterations 0 and 1 routed (rule: 7 and 24 negative rows, NOT
CLEAN; kernel links 201 -> 118/123 after the first proposal). Not part of suite_one, the route of iteration 1
(su_fill_1_1, .bit 9c2b6b55, BDC_AUTO's emission with the rule's sizes, NOT CLEAN by the rule) through the same
worst-corner gate as above: **PASS 5/5**, arrays = C after every call, EQUIVALENT, ANNOTATE_DONE 0, 448 / 160, 0
overlaps; latency 89 / 110 / 23 / 7 / 6 host cycles (about 2.6 cycles, 32 ns, per trip: 2.4-2.7x faster than the
default flow's estimates). Seed 2 (`suite_one.sh fill 2 2 4`): the loop ran to it 6 (raise-only finish, NOT CLEAN by 4
rows), route su_fill_2_6 (sdf d269ddfe), EQUIVALENT, ffmux-clean, P 37.27 ns per trip, **2 / 2 draws PASS 5/5** (K
10201: chains 0.30 / rest 0.21 / carry 0.95; 10202: 0.24 / 0.28 / 0.98), arrays = C after every call; latency per call
median 324 ns. One automatic route with draws: a sample, not a distribution.

### The ordering itself (RTL, cells/sim delays)

Removing the completion join (`BDC_STORE_NOJOIN=1`, a test-only switch: the store's z tied off as before, memEnd =
memStart held + ctrlEnd, nothing ordering ctrlEnd after the stores) is invisible at nominal delays: fill's RTL run
passes (0 of 10 out0 early, arrays right), because the last store happens to beat the exit path. That is why the
read-back cannot be the ordering's negative control. `tb_store1.v` counts the store station's completions and
checks, when out0 rises, that every store of the run (n, from the C) has completed. With the stores made slow
(bd_mem's USETUP 400 instead of 8, about 50 ns per store in this model -- the defect made larger than the race):
**with the join, 0 of 10 out0 early, arrays right; without it, 8 of 10 out0 early** (31 of 32, 39 of 40, 6 of 7 and 0 of 1 stores completed when out0 rose, both runs of each call; the n = 0 call stores nothing), with the arrays still right when read back afterwards. The same check passes at USETUP 8 with
and without the join. RTL only: it shows the structure orders the completion, not routed timing.

### What it does NOT show

- **Four seeds of one kernel at one corner** (default flow, all PASS), plus two automatic routes (one with 2 draws).
  No max / min corner run, no draws on the default-flow routes, no board.
- **One shape on the bench.** fill: one store, the controller's only accessor, in a loop body with a control
  terminator. The exit-block form (store joined into ctrlEnd) ran only in RTL (`simple_example_1`), the 9 Dynamatic
  tests were not routed, and none of them can go on the bench (void: gen_bench.py and oracle_mem.sh refuse them).
- **The ordering in a routed design is not instrumented.** The routed gate checks values and arrays and that the host
  never touched the port while a kernel slot held it (0 overlaps); the store-count-at-out0 check ran in RTL only, and
  its negative control needed a store slowed far beyond any route to fail (at nominal delays the race is won anyway).
- **Nothing about a load after a store on the same array**, in the same iteration or the next (section 2): no such
  kernel can be built here yet.
- **Not the cost.** The serialisation (a block's successor waits for its stores) was not compared with anything;
  77-84 ns per trip is fill's number, not a comparison.
- **Dynamatic's count values are not used at run time.** They are checked against the graph at compile time; a
  kernel whose count disagrees is refused; no fixture in build/frontend (106) is: neither that check nor the one-terminator check fired on any of them.
- **bd_mem's delays are the placeholders** (DSETUP 8, DCO 12) in the default-flow routes: rules B and C pass on both,
  but nothing here sizes them.
- **Matrix-shaped kernels (triple loop nest) deadlock in RTL in the default flow, with or without the completion
  join** (`BDC_STORE_NOJOIN=1` too): the same class as the suite's nest3 (kernels/SUITE.md, "simcheck deadlocks",
  default flow). With `BDC_AUTO=1` (the automatic path's emission) matrix completes in RTL: one call, 27000 inner
  trips, outC read back 900 / 900 = the C (inA, inB uniform in [-50, 50], outC preset 0x5a5a5a5a). So the store
  lowering works in the middle block of a triple nest under AUTO; the default flow's deadlock is not this work's.

**Merged with srcjoin (2026-11-18, main session).** srcjoin (`free_running()`, the call join in `_op_end`) landed on
the branch after this work's base. `_op_end` now runs the call join for a result no call bounds and this completion
join for a function with a store; a function with both is refused (EmitError: not combined yet; no fixture has both).
Checked after the merge, every fixture in build/frontend (108) x {default, BDC_AUTO=1, BDC_HOST_MEM=1}, `--no-top`:
the 105 outputs that emitted before the merge are byte-identical to the branch before it (79fec0d88); the 30 new
outputs (fill and the 9 Dynamatic tests, 3 modes) are byte-identical to this work's own tree; the only outputs that
differ from this work's tree are test_int16 and unused_arg (srcjoin's two kernels, 6 outputs), as expected.

## 4. Files

- `bdc/emit.py`: `store_completion_rewrite` (+ `_rebuild_index`, `_replace_operand`), the `Emitter` call before
  BDC_AUTO's rules, store's third result in `result_channels`, `_resolve_mem_accessors` (count tokens recorded, SL
  refused, the completion not absorbed), `_op_store` (z -> the completion channel), `_op_mem_controller` (the refusal
  gone, count tokens sunk), `_op_end` (data results joined with the store controllers' memEnds).
- `bdc/mem.py`: `BDC_MEM_NEG_STORE=addr|data`, the negative control (default off: byte-identical).
- `bdc/bd-config.json`: the store-having mem_controller entry `todo` -> `cells`; store's text.
- `kernels/fill/{fill.c, fill.h, vec.hex}`, `cloud/fixtures/frontend/fill/comp/*.mlir` (the six), suite list
  `research/tools/suite/kernels.txt`.
- `research/tools/suite/tb_store1.v` (RTL testbench), `research/tools/suite/dyn_blockers.py` (mc:store's meaning).

## 5. fill

`kernels/fill/fill.c`: `for (i = 0; i < n; i++) { x = (x ^ (x << 5)) + i; a[j] = x; s += x >> 3; j = (j + 7) & 31; }
return s;` -- one array, one store, no load (the controller's only accessor, so the bench's plain port + host slot);
the address loop-carried and not the induction variable; n > 32 writes some elements twice (the later write must win);
elements not reached keep their contents. Vectors `kernels/fill/vec.hex` (memvec.py, seed 7, arrays uniform in
[-1000, 1000]): (n, x) = (32, 0x12345678), (40, 0xdeadbeef), (7, -5), (1, 1), (0, 0x02468ace). Expected values and
final arrays: `oracle_mem.sh fill` with ORACLE_MEMOUT (the C; ORACLE_RUNS=2 gives the identical files, so the bench's
two runs per call agree): out0 d86f2f64 302b3fae 02345ec0 00000004 00000000. The n = 0 call is degenerate on purpose
(nothing written; result 0): it checks that nothing is written; the other four are not.

## 6. Open problems

- **LS is lowered since 2026-11-18 (dyntests, research/data/suite/dyn/README.md section 3)**: the load's z forked into
  the token (within one block), the hazard below settled by a capture latch in every load on an arbitrated port
  (tb_capture.v: the plain station returns the other station's word, the capture does not), and the bench's host
  slot outside the arbiter. SL is still refused. The original note:
- **Load-store on one array (LS / SL) cannot run.** LS needs `mc:load1st` (a fork on the load's z: its consumer and
  the store's token). SL needs the same fork on the store's z (the load's token and the completion join). Both put a
  2-way arbitrated port under the array, and `--host-mem` refuses a third slot on it, so the bench could not fill or
  read it: a host slot gated outside the arbiter is the cheap form (the bench already guarantees host and kernel never
  overlap). And one hazard to settle first: in LS the store may clock the RAM while the load's read data
  (`z_data = p_rdata`, the RAM's DOADO, WRITE_FIRST) is still being consumed -- the store's token arrives with the
  load's request, not after its consumers have captured the value. In SL the existing hold chain orders it (a store
  of iteration k+1 is presented only after the load of iteration k was acknowledged).
- **A histogram** (`h[x[i]]++`, kernels/histo was tried): Dynamatic's frontend puts an LSQ on h (it cannot prove the
  iterations independent), so it needs force-mc + LS + the arbitrated host slot.
- **More than two accessors** (`mc:>2`) and an N-way chain with stores in it: every store but the last needs the fork.
- ~~Void kernels on the bench~~: since 2026-11-18 (dyntests) a void call completes on `end` and every memEnd
  (research/data/suite/dyn/README.md section 1).
