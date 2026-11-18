# The bench's argument ABI for the benchmark suite (suiteb, 2026-11-17)

PROGRAM "A benchmark suite for the compiler" asks for kernels with more than two arguments and kernels that use
memory (read only, write, read-modify-write, two arrays, an index read from memory).  The bench
(`cells/hw/gen_bench.py`) could run neither: its operand file was two 32-bit words, and a memref argument had no
way in -- memsum emitted, but its array could never be filled, so its answer was always 0.  This directory
documents the extended ABI and what was verified on it.

## Results (nextpnr 9c732bc6303458df, cells/verify/toolchain.sh all ok)

Routes: `cells/hw/build_bench.sh K` with `BD_NO_TIGHTEN=1 BD_SIZES=none BD_DSP=1 NEXTPNR_SEED=1..4`, `--freq 83`
(research/data/alltable/run_default.sh's flags), each in a private copy of this branch's tree.  Gate:
`research/tools/eventgraph/bench_gate.sh ... worst` -- netlist decoded from the .bit (fasm2net, with the RAMB18E1
decoder below), fasm_equiv verdict, prjxray SDF, chains 0.21, CARRY4/F7F8/FF and RAMB18E1 1, rest 0.288, + M scatter,
FIXED mode, 2 runs per call at 83.3 MHz.  Every memory run also had `GATE_ANNOTATE=1` (gate.vvp: ANNOTATE_DONE, SDF
warnings counted), `PS_MON_GEN=cells/gls/ps/gen_memport_mon.py` (the ports' one-hot check on the netlist).  memsum
also had `+MEMCHECK=1` (every word read back after each fill) and `GATE_MEMEXP` (every array read back after each
call and compared with the C's final contents -- read-only arrays, so unchanged).  Expected values: oracle_mem.sh
(the C).  The routes were built from three commits of this work (3d7e853d4, 05f4da73f, b7d83ba62) whose generated
kernel and bench Verilog are identical for these kernels (cmp'd for memsum and sum3).

STATE WHEN PAUSED (2026-11-17 19:3x, the bot's stop order): what is below was measured; nothing else was.

| kernel | seed | Fmax (MHz) | bench_gate worst | fasm_equiv | gate.vvp | one-hot monitor (netlist) |
|---|---|---|---|---|---|---|
| sum3 (3 words) | 1 | 101.01 | PASS 6/6 | EQUIVALENT | ANNOTATE_DONE, 0 SDF warn/err | - |
| memsum | 1 | 107.09 | PASS 5/5, read-back 0 bad, final contents = C | EQUIVALENT | DONE, 0 | 448 host / 170 kernel reqs, 0 overlaps |
| memsum | 2 | 115.71 | PASS 5/5, same | EQUIVALENT | DONE, 0 | same, 0 overlaps |
| memsum | 3 | 101.69 | PASS 5/5, same | EQUIVALENT | DONE, 0 | same, 0 overlaps |
| memsum | 4 | 105.97 | PASS 5/5, same | **NOT EQUIVALENT (not investigated)** | DONE, 0 | same, 0 overlaps |

kernel_reqs 170 = the C's loads: n = 32, 20, 1, 0, 33 (capped at N = 32) -> 85 per run, 2 runs.  memsum's answers
(00000d25 ffff359a fffffc21 00000000 000073aa) are the oracle's (the C).

Negative control (arrays differ): memsum seed 1 with `memsum_neg.hex` (same n, arrays from another seed) against
the original expected file: **FAIL 1/5** (only the n = 0 call, which reads no element, matches); the answers the
hardware returned are exactly the C's for the arrays it was given (fffefbf5 00003de2 00000110 00000000 ffffbcc9).

NOT RUN (routes built, gates killed or never started): sum3 seeds 2-4 (routed 96.70 / 105.27 / 93.13 MHz); fir
seeds 1-4 (routed 104.21 / 107.84 / 117.22 / 115.73 MHz; fir_s1 was simulating 2 calls when stopped); the BRAM
model's negative controls (RAM clock inverted in the bitstream: `runs/hw/memsum_s1clkinv`; ADDR setup inflated to
20 ns in the SDF); the read-back negative (`memsum_bad.memexp`); the monitor's own negative (`+MEMPORTMON_FORCE`);
the max / min corners.  RTL-level only (not gate evidence): fir 3/3 and sum3 6/6 equal the oracle.  The bram fork's
memsum_s1 run before the RAM band change: PASS 5/5 (cells/gls/fid/bram/README.md).

Routed RAM boundary (verify/tighten.py rules B and C on each route's SDF; the host slot is one more requester on
the port's mux, and its request flop and data flops are on the measured paths):

| route | B: setup margin per RAM (ps) | C: clock-to-out margin per RAM (ps) |
|---|---|---|
| memsum s1 | 3869 / 2792 | 1414 / 1785 |
| memsum s2 | 3842 / 3013 | 839 / 1335 |
| memsum s3 | 4774 / 3815 | 665 / 1579 |
| memsum s4 | 3456 / 4410 | 1177 / 1727 |
| fir s1 (4 RAMs) | 3552 / 2859 / 2719 / 2732 | 2272 / 2121 / 1947 / 2087 |
| fir s2 | 3551 / 1465 / 1239 / 1500 | 2474 / 3194 / 2107 / 1988 |
| fir s3 | 3138 / 1798 / 2724 / 2618 | 3043 / 1727 / 2342 / 2700 |
| fir s4 | 3306 / 2965 / 3631 / 2931 | 2495 / 2133 / 1889 / 2219 |

All "ok" at bd_mem's placeholder DSETUP=8 / DCO=12 (n = 24 RAMs: setup 1239..4774 ps, clock-to-out 665..3194 ps).
These are tighten.py's own margins on nextpnr's SDF (its rule B adds its SLACK to the vendor window); they are a
static screen, the gate-level runs below are the judgement.

### Byte-identity of what the flow generates for the six original kernels

- `cells/hw/gen_bench.py K`, `K --null`, and `K` with the default top name, for gcd, ipow, collatz, collatz64,
  isprime, xorshift: 18 files, all `cmp`-identical to the output before this work (every kernel's
  `build/gen/K_kernel_bench.v` present, as the build has it).  Checked again after every gen_bench.py change.
- `bdc/emit.py --no-top` on 11 fixtures (the six, nested, branchloop, memsum, fir, test_loop_free): identical by
  default; with `--host-mem` identical for every kernel without a memref (all but memsum and fir).
  `build_bench.sh` now passes `--host-mem`, so the six kernels' emitted Verilog is unchanged.
- `cells/gls/ps/ps7_master.v` (gcd_ps's host): byte-identical after regenerating.  `ps7_bench.v` changed, so its old
  path was checked by behaviour: the RTL bench of ipow with `research/data/eventgraph/gate/ipow17.hex` (17 vectors)
  and of gcd with `gcd18.hex` (18) under the old and the new ps7_bench.v give run logs identical in every BENCHRES
  line, timestamps included (they differ only in the simulator's own source-line references).  An old file is
  detected by its first line not being the v2 header, and from there the AXI sequence is the old one.

## The ABI

### Operand words

Arguments map onto 32-bit operand words in signature order; an i64 takes its low word, then its high word; a
memref takes no word.  The file holds up to `MAX_WORDS = 10` words:

| word | register | byte offset | present |
|---|---|---|---|
| OP0, OP1 | 7'h02, 7'h03 | 0x08, 0x0C | always (as before) |
| OP2..OP9 | 7'h18..7'h1F | 0x60..0x7C | only when the kernel needs more than 2 words |

FIXED mode runs the words as written.  UNIFORM draws word k from the LFSR advanced k times (words 0 and 1 exactly as
before); LEGACY (gcd's old biased draw) applies to words 0 and 1 only and runs the others as written.  The six
original kernels' input masks (`DOMAIN_RESTRICTIONS`) are unchanged and apply only to them.

### Memories: a host port on each memory

`bdc/emit.py --host-mem` (or `BDC_HOST_MEM=1`; `cells/hw/build_bench.sh` passes it) gives every mem_controller's
plain `bdc_memport` ONE MORE one-hot slot, the last, wired to six kernel ports per memref argument (signature
order): `<m>_host_req/_ack/_addr[AW-1:0]/_wdata[DW-1:0]/_we/_rdata[DW-1:0]`.  It is the port's own slot protocol:
four-phase on req/ack, address/data/we bundled by req, read data valid while ack is high; the acknowledge and the
read data are the port's SHARED ones.  No new cell; `cells/rtl/` is untouched.  The kernel's own slots keep their
numbers, stations, wires and BD_SZ keys.

The bench drives those slots from the PS clock domain (`gen_bench.py host_mem_lines`, emitted only for a kernel
with memories):

| register | addr | byte | meaning |
|---|---|---|---|
| MEMADDR | 7'h20 | 0x80 | RW [15:0] element index, [23:16] memory number (memref args in signature order) |
| MEMWDATA | 7'h21 | 0x84 | W: mem[MEMADDR] <= data, then index += 1.  R: MEMRDATA |
| MEMCMD | 7'h22 | 0x88 | W [0]=1: MEMRDATA <= mem[MEMADDR], then index += 1 |
| MEMSTAT | 7'h23 | 0x8C | R [0] busy, [1] refused (sticky), [2] timeout (sticky), [31:16] accesses done.  W: clear |
| MEMRDATA | 7'h24 | 0x90 | R: the word the last access read (a write reads back what it wrote: WRITE_FIRST) |
| LAYOUT | 7'h28 | 0xA0 | R {nmem[31:24], nwords[23:16], 16'hB5C2}; present when nwords > 2 or nmem > 0 |
| MEMINFO[m] | 7'h30+m | 0xC0+4m | R {depth[31:16], element width[15:8], address width[7:0]} |

- The AXI write response to a MEMWDATA / MEMCMD write that starts an access is held until the access is over, so
  a run of writes paces itself (no polling) and a read's word is in MEMRDATA when its write response arrives.
- One access at a time: MEMSTAT[0] busy.  The sequencer sets address, data and we one aclk BEFORE it raises the
  request, waits (before raising it) for the port's shared acknowledge to be low -- the last access, the kernel's
  or its own, has returned to zero, so the request makes a fresh rising edge on the RAM's manufactured clock --
  and holds address/data until the acknowledge has been seen low again.  Every acknowledge is an asynchronous
  signal entering a clocked FSM, so each memory's gets its own 2-flop synchroniser (CLAUDE.md); the read data is
  sampled when the synchronised acknowledge is high (two clocks after the RAM produced it, while it holds).  An
  access that sees no acknowledge for 2047 aclk cycles is abandoned and flagged (MEMSTAT[2]).
- THE ONE-HOT OBLIGATION.  The plain port's mux is one-hot, so the host may use its slot only while the kernel
  uses none.  The bench REFUSES an access (MEMSTAT[1]; the write is still answered) while a batch runs
  (bench_busy) or while the kernel is held in reset (its port's acknowledge C-tree is reset with it, so the access
  could not finish).  The host therefore fills and reads memories between batches.  The manual 4-phase smoke path
  (CTRL.i_req) has no guard: do not mix it with memory accesses.
- A memref's `<m>_start` (its mem_controller's memStart) is forked with `start` and the operands on every call;
  its `<m>_end` (memEnd) is taken by a sink, like `end`.

Why not an arbiter on the host slot (CLAUDE.md "trust the arbiter").  The host and the kernel are never concurrent
requesters: one clocked controller issues calls and host accesses in strictly alternating phases, so there is no
arbitration decision to make.  An arbitrated port (`bdc_memport_arb`) would put bd_arbiter's decision and its
unmeasured metastability exposure on every KERNEL access, change what the benchmark measures, and it arbitrates
exactly two requesters (a kernel memory that already has two accessors would need a tree that is not built).
What remains is the obligation above, which the bench enforces structurally rather than by analysis.

### Vector files

The original format is unchanged: two hex words per vector (`$readmemh`), batch j runs vector j.  A file whose
FIRST line is `// benchvec words=W mems=M` is the v2 format: per call, the W operand words, then every element of
each of the M memories in signature order (one 32-bit word per element; an element narrower than 32 bits takes the
word's low bits), as whitespace-separated hex with `//` comments allowed anywhere.  The depths are the bench's
(MEMINFO); `ps7_bench.v` refuses a file whose LAYOUT disagrees or that is not a whole number of calls.  Per batch,
before starting it, `ps7_bench.v` writes OP0..OP(W-1) and fills every memory through MEMWDATA, then checks MEMSTAT
(a refused/timed-out fill or a wrong access count prints `BENCHMEM batch=j FILL FAILED`).  `+MEMCHECK=1` reads every
word back and prints `BENCHMEMCHK batch=j words=N bad=K`; `+MEMDUMP=1` prints every memory after the batch
(`BENCHMEM batch=j mem=m n=N data=w0,w1,...`).

`research/tools/suite/memvec.py K --call "w0 w1 .." ... [--calls N] --seed S [--range LO,HI] [--perturb N:D]`
writes a v2 file from the kernel's handshake signature; arrays are drawn per call from a seeded uniform range.

### The oracle

`research/tools/suite/oracle_mem.sh K VEC.hex > VEC.exp`: the kernel's own C (kernels/K, else
dynamatic/integration-test/K), gcc -O1 -fwrapv, CALL_KERNEL stubbed and main renamed -- the recipe of
`research/tools/fifteen/kernel_oracle.sh` and of the suite's `oracle.sh` -- with the argument mapping read off the
C signature (array lengths from the C's own `T a[N]`), so it shares nothing with the bench but the file format.
`ORACLE_RUNS=R` calls the kernel R times per call without refilling (the bench's NRUNS on a kernel that writes its
arrays); `ORACLE_MEMOUT=F` writes every array's final contents per call, in the form `+MEMDUMP=1` prints.

### The gate

`research/tools/eventgraph/bench_gate.sh` reads v2 files unchanged (the PS model detects them).  New, all opt-in
(without them its command line, simulation and verdict line are what they were): a batch also FAILS on a fill
failure or a `BENCHMEMCHK bad>0`; `GATE_MEMEXP=F` (oracle_mem.sh's ORACLE_MEMOUT) adds `+MEMDUMP=1` and FAILS a batch
whose arrays differ after it; `GATE_NRUNS` (default 2); `GATE_ANNOTATE=1` also runs gate.vvp and appends
`annotate DONE|MISSING sdf-warn/err N` to the verdict.

## Written arrays (step 3)

### What exists (bench side)

- Read-back after a call: `ps7_bench.v +MEMDUMP=1` reads every element of every memory through the host port after
  each batch and prints `BENCHMEM batch=j mem=m n=N data=...`.
- The C's final contents: `oracle_mem.sh` with `ORACLE_MEMOUT=F` writes `call=j mem=m data=...` per call (the same
  form), and `ORACLE_RUNS=R` runs the kernel R times per call without refilling, as the bench's NRUNS does.
- The gate: `GATE_MEMEXP=F` turns on `+MEMDUMP=1` and fails a batch whose arrays differ from F; `GATE_NRUNS` sets the
  runs per batch.  A kernel that writes its arrays sees its own writes on its second run, so the FIXED-mode
  repeatability latch (mism_st) may legitimately fire: gate such a kernel with `GATE_NRUNS=1` (or check with
  ORACLE_RUNS=2 that its two runs agree).
- Not built in the bench: a kernel with no `out0` (a void function, as most of Dynamatic's array kernels are:
  single_loop returns nothing).  The batch FSM completes a run on out0 only; such a kernel needs the run completed on
  `end` and every `<m>_end` instead.  And `<m>_end` is sunk today, not waited for: once memEnd means "every store has
  landed" (below), the bench must not declare a run complete, nor let the host read back, before it has seen it
  (latched and synchronised like o_req).

### What bdc needs for stores

The refusal is `bdc/emit.py Emitter._op_mem_controller` (`has_store` -> EmitError), and two things upstream of it:

1. **The completion obligation (memEnd).**  Dynamatic's store-side controller (`mem_controller_loadless.v`, with
   `mc_control` in `data/verilog/support/mc_support.v`) fires memEnd only when ctrlEnd has arrived ("no more requests
   will come"), AND `remainingStores == 0`, AND no count token is being presented.  remainingStores is an up/down
   counter: every basic block that contains stores sends the controller a COUNT token each time it executes, carrying
   how many stores that execution will make (the `constant` operands in the mem_controller's accessor list, e.g.
   single_loop's `%11`, which `_resolve_mem_accessors` skips today); every store that reaches the RAM decrements it.
   The load-only controller is the special case `allRequestsDone = 1`, which is what bdc builds now (a bd_link holding
   memStart, joined with ctrlEnd).  With a store, that shortcut lets memEnd fire while promised stores are still in
   flight, so the host -- or a caller -- would read the array before the last store landed.

   In bdc there is no clock to sample a counter on, so the counter has to be a token machine.  A design from cells
   that exist, none new:
   - an ARBITRATED MERGE (bd_arbiter -- "trust the arbiter") of the delta streams: each block's count token (+k) and
     each store station's completion z (-1) arrive concurrently and independently, so they cannot be OR-ed;
     one count stream plus one store station is one bd_arbiter; more blocks or stations need an arbiter tree, which
     is not built (bdc/mem.py refuses one for the same reason);
   - an accumulator ring: the merged delta into an adder (bdc/compute.py addi) whose result is held in a bd_link and
     fed back -- a ring, so three storage stages per simple cycle (CLAUDE.md);
   - an "ended" flag carried in the same ring (ctrlEnd joins the merge as a third input that sets it, so its arrival
     is ordered with the deltas instead of racing them), and after each update a steer (cond_br on
     ended && count == 0) that emits memEnd or discards;
   - memEnd then joined with the memStart link as now, and the ring's state reset to (0, not ended) for the next call.
   Its completeness rests on an ordering that must be checked, not assumed: a block's count token has to reach the
   merge before ctrlEnd does.  Control flow emits the count token before it can reach the exit block, but the two
   travel different paths and nothing in an asynchronous circuit makes the earlier one arrive first; a count token
   still in flight when ctrlEnd arrives with the count at 0 lets memEnd fire early.  The fix is structural, not a
   delay: derive ctrlEnd's path so that it passes through (joins with) the last count token, or count the count
   tokens against the block executions.  Dynamatic carries the same assumption in clocked form (its count tokens
   are accepted every cycle, `ctrl_ready = 1`, and nothing orders them against ctrlEnd either).
2. **The accessor list.**  `_resolve_mem_accessors` accepts one accessor (plain port) or two, the first a store
   (`bdc_memport_arb`, the store's z is the load's program-order token).  A histogram (`h[x[i]]++`) is load-then-store
   on one array: the load's z already feeds its consumer, so being the store's token too needs a fork that is not
   built; and the host slot would be a third slot on the arbitrated port (`--host-mem` refuses: an arbiter tree, or a
   host slot gated outside the arbiter, is needed).
3. **The count channels.**  Today they are skipped as accessors; with stores they must become the counter's +k
   inputs, or their producers stall on an acknowledge that never comes.

Size estimate: the token counter is ~150-250 lines in emit.py composing existing units (arbiter merge, addi, cmpi,
link, steer, join), plus its audit (tighten.py sees ordinary cells; the arbiter brings bd_arb.v's MTBF obligation,
which only hardware discharges), plus the bench's void-kernel / memEnd-wait completion (~60-100 lines in
gen_bench.py), plus a store-capable test path (an RTL testbench like cells/tb/tb_bdc_memseq.v, then routed GLS of
single_loop and a histogram with written arrays checked against the C).  Not small: not implemented here.

## What does not work yet

- **Stores** (bdc refuses them: `EmitError: mem_controller ... has a store accessor`) -- see above.  So no kernel that
  writes an array can be built yet, and the read-back / final-contents check is verified only on read-only arrays
  (where the final contents must equal the initial ones).
- **A memory with two accessors** (bdc_memport_arb): `--host-mem` refuses it (a third slot on a two-way arbiter).
- **A kernel without out0** (void) and **an out0 wider than 32 bits** are refused by gen_bench.py; a narrower out0 is
  zero-extended (Dynamatic's test_int16, int16_t: its oracle must mask to 16 bits, as oracle_mem.sh does;
  the suite's two-word `research/tools/suite/oracle.sh` -- uncommitted in /tmp/bot/sa/suitek/repo when read at
  18:45, line 75 `printf("%08x", (unsigned)K(...))` -- sign-extends an int16_t and would disagree with the bench on
  a negative one: it needs the same mask).
- **Elements wider than 32 bits** (an i64 array) are refused by gen_bench.py (one 32-bit host word per element).
- **`--null`** is refused for a kernel with memories (the null DUT would need a RAM behind every host port).
- **A kernel with no operand word and no memory** cannot be written in the v2 format (a call would be zero words);
  use the two-word format, whose words it ignores.
- **The board**: nothing here has run on silicon.  The register map is plain AXI registers on M_AXI_GP0
  (`cells/hw/xsdb_bench_gen.tcl`'s header lists them), but the xsdb driver has no v2 / memory-fill path yet: a fill
  is `mwr 0x40000080 [expr {m << 16}]` then one `mwr 0x40000084 <word>` per element, with the kernel out of reset and
  no batch running, then `mrd 0x4000008C` (MEMSTAT: [1]/[2] clear, [31:16] = the element count).
- **Time**: a fill costs about 13 aclk cycles per element (two 2-flop synchronisers and the AXI round trip), about
  160 ns at 83.3 MHz; fir's 2000 elements are about 0.31 ms of simulated time per call, which is most of its gate's
  cost.  On the board an xsdb `mwr` per element is far slower than that.
- **The manual smoke path** (CTRL.i_req) is not guarded against memory accesses.
