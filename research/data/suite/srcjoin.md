# A result no call bounds: joined with the call's bounded control results (srcjoin, 2026-11-18)

kernels/SUITE.md, suitew's item 2: two of Dynamatic's tests never finish a call because a `source` reaches a function
result with nothing tying it to the call. This note is the fix in bdc, the evidence, and what it does not show.

## The bug

bdc lowered `end` to wires (`_op_end`: each result assigned to its port). A `source` offers a token forever
(cells/rtl/bd_end.v: `req = ~ack`), so a result fed by a source and by no argument produced tokens with no call:

- **test_int16** (`return -1;`): `out0 = constant(source)`, `end = start`. simcheck `--c-oracle` in both flows:
  `FAIL (timeout) on vector 0`, `snk out0: 94162 seen` for one start in 400 us.
- **unused_arg** (`return used[0];`, `a` unread): the frontend drops the memref `a` but keeps `a_start` (sunk) and
  drives `a_end` (its memEnd) from a `source` -- already so in Dynamatic's `handshake.mlir`, before any bdc pass. The
  bench acknowledges `a_end` with a `bd_delay`, so source and sink were a ring oscillator, and the rule refused the
  route (suitew, nextpnr 9c732bc6303458df): tighten.py `combinational cycle with no storage`
  (`bridge_i.ua_end_snk.chain.g[0..1]` + `bridge_i.udut.usource0`).

## What Dynamatic means by it

- `source` (dynamatic/include/dynamatic/Dialect/Handshake/HandshakeOps.td): "a continuous control-only-token source.
  The source continously sets a 'valid' signal which the successor can consume at any point in time."
- `end`: "Terminator of every Handshake function. Its operands represent the parent Handshake function's results".
  It has no RTL in Dynamatic's library (wires in its export), so in Dynamatic's clocked circuit a source-fed result is
  simply valid on every cycle.
- Who consumes it once: Dynamatic's testbench (hls-verifier, `tools/hls-verifier/lib/HlsTb.cpp` on GitHub main, read
  2026-11-18 -- not vendored here, so this is second-hand) sends every control input, start included, exactly once,
  and takes the outputs TOGETHER: one `tb_join` (`join_valids`) over the valid of every result and every control
  output (memory ends, `end`), whose `ins_ready` drives each output's ready. A source-fed result is therefore consumed
  exactly once per call, when the call's other outputs are there.
- Dynamatic's `end` result is start itself: in all 104 fixtures that parse, the `end` operand is the start argument
  through forks only (never through the control flow). So "joined with end" and "joined with start" are the same
  thing. What comes late in a call is the memories' ends: a memory's end needs its controller's ctrlEnd, the exit
  block's control token (after the loops; in a one-block function such as unused_arg, a copy of start). bdc's
  load-only controller does not wait for loads in flight (Dynamatic's storeless controller does not either).

bdc's bench takes each output alone (out0 is captured as the call's completion; `end` and every `<m>_end` go to their
own sinks), so the join has to be in the circuit.

## The change

`bdc/emit.py`:

- `free_running(func)`: the values whose tokens no call bounds, decided on tokens, not reachability (a source reaches
  a result in 103 of the 104 fixtures that parse: every literal operand of every kernel, almost all bounded by the op
  the literal feeds). Least fixpoint: a source is free; a fork / lazy_fork / constant / br / buffer / trunci / extui /
  extsi / load when its (first) operand is (a load fires once per address); a join of channels (every compute op,
  the dividers included, cmpi, select, cond_br, join, store, mem_controller) when ALL operands are; a merge /
  control_merge when ANY is (one free input floods it); a mux when its select and any data input are. Arguments are
  never free. An op outside the table with a free operand stops the emitter (do not assume).
- `_op_end`: when some result is free, every CONTROL result the call does bound (`end`, and each memory's end) is
  forked (`bd_fork`, `<end>_ufork_<result>`: copy 0 to its port), and each free result is joined with one copy of
  each (`bd_join`, `<end>_ujoin_<result>`: one C-element with reset). Data, if any, is wired through: it is valid from
  the free result's own request until its acknowledge, which is the joined channel's acknowledge, so bundling holds
  with no delay (test_int16's is a constant). Every other result keeps its wires.
  Why those tokens: they are what Dynamatic's tb_join waits for besides the result. Start (= Dynamatic's `end`) alone
  would make it once per call, but a source-fed out0 joined only with it would tell the bench "done" at the call's
  start while the call's loops may still be running (gaussian, below, is that shape); a memory's end comes after the
  exit block's control token. The data result is not joined: the bench takes it on its own, and a control output's
  timing, beyond once per call, does not matter to the bench. The bd_src now sits behind a consumer that resets,
  which COMPILER-PLAN.md asks of it ("a `bd_src` must sit behind a consumer that resets").
- Refused, loudly: a free result and no control result bounded by the call.
- `BDC_CALL_JOIN=0` emits the old wiring (the negative control).

`research/tools/auto/est_sizes.py`: a kernel with no matched delay (test_int16 after the fix: 0 delays) gets a sizes
file with no lines (exit 0) instead of `no module bdc_<k> with parameters`; a file with no `bdc_<k>` module at all is
still an error. `research/tools/auto/auto_size.sh`: when the estimates have no line, it builds once (it 0), runs the
rule once, runs the full stack on that route and writes `CLEAN it=0 ... (nothing to size)` or `NOT CLEAN it=0: N
negative, none fixable by a line (nothing to size ...)`, which suite_one.sh parses as before.

## Which kernels change (cmp)

`bdc/emit.py --no-top` on every fixture, four ways: default; `BDC_AUTO=1`; `bdc/auto.py` then `BDC_AUTO=1` (what
suite_one.sh compiles); `bdc/auto.py` then `BDC_AUTO=1 --host-mem` (what build_bench.sh builds). Compared: exit code,
stderr (traceback line numbers and tree paths normalised) and the Verilog (line 1, the input path, skipped). Fixtures:
build/frontend's 105 plus dot2 and gather from cloud/fixtures/frontend (107; the shared 105 are identical in both).

| comparison | (variant, kernel) pairs identical | differ |
|---|---|---|
| commit c7808ea6d (a worktree of it) vs this change | 420 / 428 | test_int16, unused_arg, in all four variants |
| commit c7808ea6d vs this change with `BDC_CALL_JOIN=0` | 428 / 428 | none |

35 fixtures emit (all four ways), 72 stop with the same error as before. Why each changed kernel changes:

- **test_int16**: out0 is `constant(source)`. Now `uend0_ujoin_out0` = C(out0's source token, a copy of `end`) via
  `uend0_ufork_p_end`; `end` is start. Default and BDC_AUTO=1 emit the same Verilog.
- **unused_arg**: `a_end` is a bare `source`. Now `uend0_ujoin_a_end` = C(source, a copy of `used_end`, a copy of
  `end`) via `uend0_ufork_used_end` and `uend0_ufork_p_end`; `used_end` is the mem_controller's memEnd (join of the
  held used_start and ctrlEnd), `end` is fork0's third copy of start.

The fixpoint on all 104 fixtures that parse finds one more free result: **gaussian's out0** (LLVM folded `sum` to the
constant 29070, `constant18(source10)` into `end`). bdc refuses gaussian earlier (`no width rule for handshake op
'lsq'`), so its output does not change; once lsq is lowered its out0 will wait for c_end and a_end.

## Checks

### simcheck (pre-route, sim/bd_prims_sim.v arc timing)

`python3 bdc/simcheck.py build/frontend/test_int16/comp/handshake_transformed.mlir --c-oracle --timeout-us 400
--vecfile V`, expected values from the C (`research/tools/suite/oracle.sh test_int16`: 0000ffff, the i16 -1
zero-extended):

| V | default | BDC_AUTO=1 | default, BDC_CALL_JOIN=0 | BDC_AUTO=1, BDC_CALL_JOIN=0 |
|---|---|---|---|---|
| research/data/suite/vec/test_int16.hex (1 call) | PASS 1/1 | PASS 1/1 | FAIL (timeout) at vector 0, out0 94162 tokens | FAIL (timeout), the same |
| six calls in a row (a scratch file; the kernel reads no word) | PASS 6/6 | PASS 6/6 | FAIL (timeout) at vector 0, out0 94162 tokens | FAIL (timeout), the same |

simcheck's pass includes its token-count teeth: every output channel produced exactly as many tokens as calls. The
answer itself cannot tell the fix from the bug (the flood's first token carries the right value too); the count can.
unused_arg is a memory kernel; simcheck refuses its v2 file ("memory kernels are checked on the bench path only"),
so its evidence is the routed run below.

Every other suite kernel with vectors, re-run on this tree (`--c-oracle --timeout-us 400` on its vector file; the six
original kernels on simcheck's REFS): **50 / 50 PASS** (25 kernels x default / BDC_AUTO=1: straight, countloop,
sqrtsub, nest3, twoloops, brhash, lfsrfind, quadrec, horner, fold64, varshift, cmpchain, nested, branchloop, factorial,
iterative_division, iterative_sqrt, test_loop_free, test_int16, gcd, ipow, collatz, collatz64, isprime, xorshift). Their
Verilog is byte-identical to c7808ea6d's (the cmp), so this only confirms nothing else moved: the simulated finish times
equal research/data/suite/simcheck_raw.txt's to the ps for all 23 runs of it that passed there (the 5 that deadlocked
there, lfsrfind / nest3 / nested default and quadrec both flows, were fixed since by the token floor, ringfloor.md).

### Routed: one run of the automatic path each (a smoke test, not a result)

`RUNS=<own> PNR_TIMEOUT=3600 CA_JOBS=2 research/tools/suite/suite_one.sh K 1 2 3` (BDC_AUTO=1, sizes from the rule,
seed 1, draws 10101 / 10102 of the delay model, expected values compiled from the C at run time), built from this
change's commit. **nextpnr 6e5d224472232d5d** (the const-sinks binary installed 2026-11-18 01:27; toolchain.sh 10 / 10
ok; NOT the 9c732bc6303458df the suitew rows above were built with), `--freq 83` (fclk0 PASS: 108.04 / 101.34 MHz).

| kernel | auto path | route (sdf md5) | bits | kernel LUTs | full stack (it kept) | draw 10101 (chains 0.2299, rest 0.2874, carry 0.5261) | draw 10102 (0.2466, 0.2342, 0.3752) | latency per call |
|---|---|---|---|---|---|---|---|---|
| test_int16 | CLEAN it=0, nothing to size (est_sizes: no line; the rule: 0 negative rows at 0.20 and 0.31) | 21440296 | EQUIVALENT, ffmux clean | 3 (bd_src's LUT1, the fork's and the join's C-elements) | 1/1 (0000ffff, 2/2 runs) | PASS 1/1 | PASS 1/1 | 5 host cycles, 60 ns |
| unused_arg | CLEAN it=1 (it 0 and it 1: the same route, 5 lines, none the rule changed; 0 negative rows) | 0553289e | EQUIVALENT, ffmux clean | 89 | 6/6 | PASS 6/6 | PASS 6/6 | 6 host cycles, 72 ns (median; 432 ns for the 6) |

`status=PASS draws=2/2` for both (P=NA: neither kernel has a loop, so the event graph has no period). The routed
netlists hold the new cells: test_int16 `bridge_i.udut.uend0_ufork_p_end`, `uend0_ujoin_out0` (C-elements) and
`usource0`; unused_arg `uend0_ufork_p_end`, `uend0_ufork_used_end`, `uend0_ujoin_a_end` (a 3-input C-element) and
`usource0`. tighten.py's storage census on the rule's 0.20-corner SDF: test_int16 2 storage nodes and no storage-free
cycle; unused_arg 11 and none. unused_arg's answers (oracle_mem.sh, the C): 7fffffff 80000000 00000001 ffffffff
13579bdf 00000000.

unused_arg's only lines are bd_mem's (USETUP 8 / UCO 12 on its two RAMs, UHOLD 0). This tree's corner_audit could not
size them ("... _UPORT_UMEM0_UCO, which sizes.vh does not set (kept, measured)"), so the loop kept the estimates and
built the same route twice; the rule measured them positive at 0.20: B +735 / +1815 ps, C +654 / +1634 ps (RAM 1 /
RAM 0). corner_audit's mapping fix (ae57dc574, committed after this work's base c7808ea6d) lets the rule size those
lines; not re-run with it.

### Negative control (routed): the fix off, same seed, same toolchain

`BDC_CALL_JOIN=0` in the environment (it reaches build_bench.sh's emit.py; checked: the built kernel Verilog has no
`uend0_ujoin`), everything else as above, own RUNS:

| kernel | result | the rule (corner_audit, both corners 0.20 and 0.31) | the cycle (tighten.py's census on the 0.20 SDF) |
|---|---|---|---|
| test_int16 | `status=FLOW-FAILED (RULE FAILED it=0)` (route 139f7baf) | `RuntimeError: ... combinational cycle with no storage` | `bridge_i.udut.usource0.u` (core_o_req = ~o_ack_pl) and the bench's LUT `o_ack_pl = (bench_busy ? bench_o_ack : ctrl_o_ack) & core_o_req`; 0 storage nodes in the whole design |
| unused_arg | `status=FLOW-FAILED (RULE FAILED it=0)` (route e518f9f0) | the same | `bridge_i.ua_end_snk.chain.g[0].u`, `g[1].u` and `bridge_i.udut.usource0.u` -- suitew's cycle |

So on the current toolchain the old wiring still fails exactly where it did, and the rule's storage check is a check
that can fail here. For test_int16 it is the only routed check that can: with the old wiring the bench would capture
the flood's first token, which carries the right answer (0000ffff) -- by reading, not run (the rule stops the flow
first) -- so simcheck's token count is the functional check.

## What this does not show

- One route per kernel, one seed: a smoke test (CLAUDE.md: >= 4 seeds for any routed claim). Nothing here is a margin.
- No board run.
- That the routed circuits produce exactly one token per call: the bench cannot count result tokens, and neither
  kernel's answers depend on the wiring (test_int16's is a constant; unused_arg's free channel is a_end, not out0).
  What shows it is simcheck (test_int16, pre-route) and the structure (the free result now passes a C-element with
  reset that needs a token from the call; the rule's census finds no storage-free cycle). unused_arg's `a_end` count
  is not observed anywhere: its bench sinks `a_end`.
- gaussian (the third kernel the fixpoint finds) is not built: bdc stops at lsq before `end`.
- The Dynamatic testbench reading is second-hand (the file is not vendored; read through a web fetch of GitHub main).
- free_running() is exact only for the op table it lists. A shape the fixtures do not contain -- a source's constant
  forked both to a result and into a loop -- would deadlock with the join (the loop's second token waits for the
  result's join, which waits for the call's end). Dynamatic's own testbench would deadlock on it too (its tb_join
  holds the result until every output is there), so it is not expected from Dynamatic's frontend; it is not refused
  either.

## Files

- `bdc/emit.py`: `free_running()`, `call_join_plan()`, `CALL_JOIN` (`BDC_CALL_JOIN`), `_op_end`.
- `research/tools/auto/est_sizes.py`, `research/tools/auto/auto_size.sh`: a kernel with nothing to size.
- `research/data/suite/srcjoin.md`: this note. kernels/SUITE.md: items 2 and 6 point here.
