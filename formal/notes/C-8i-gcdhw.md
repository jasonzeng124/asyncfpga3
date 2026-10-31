# C-8i: the gcd graph bdc emits for gcd_hw, imported, computes the C gcd

## Verdict

**It works for the token-level (Kahn) layer.** Core Lean only. No sorry, axiom or native_decide in
`Formal/`. `formal/check.sh` passes on the four files: 832 declarations audited, about 3.6 min.

Proved: `Formal.Net.GcdHw.Gcd.gcd_hw_graph_computes_gcdC`. Take the dataflow graph that bdc emits
for gcd_hw. It is generated from bdc's own parser and fusion plan, not drawn by hand. Start it with
one token each on `a`, `b` and `start`. Take any fuel on which the C function (`gcdC`, a
transcription of `cf_transformed.mlir` at i32 with wraparound) returns `r`. Then:
1. some schedule reaches the store that holds `[r]` on `out0`, the token on `end`, and nothing else;
2. every complete run ends in exactly that store, after the same number of firings. This holds for
   every schedule and every way the 8 multi-input control_merges arbitrate;
3. no run, complete or not, is longer.

The theorem has no hypothesis on the inputs: it covers every i32 bit pattern on which the C loop
terminates. One goal is still open: `gcdC = Nat.gcd` for `a, b < 2^31` (H_NONNEG31). It is stated
in `Wip/C8i/Nonneg31.lean` with `sorry`, and checked numerically, but it is not proved.

## What gcd_hw is

`cells/hw/gcd_hw.v` is the JTAG harness around `hw/gcd_rig.v`, which instantiates `bdc_gcd`.
`cells/hw/build_hw.sh` emits `bdc_gcd` with
`bdc/emit.py build/frontend/gcd/comp/handshake_transformed.mlir --no-top --probe n138`.

That file is Dynamatic's gcd integration test. Its committed copy, and the one the importer
reads because `build/` is absent here, is `cloud/fixtures/frontend/gcd/comp/handshake_transformed.mlir`.
`cloud/setup-toolchain.sh` restores `build/frontend` from that copy.

gcd_hw has no separate kernel or C source in `kernels/`. The C semantics are taken from the same
fixture's `cf_transformed.mlir`, the lowering of Dynamatic's gcd.c, which is binary (Stein) gcd.
`cells/hw/uniform_oracle.py:k_gcd` is the Python transcription of the same function.

## Files and run commands

| file | what |
|---|---|
| `formal/tools/dfimport/mlir2lean.py` | importer. It imports `bdc/hs/parse.py` and `bdc/emit.py` read-only and reads bdc's `Emitter`: widths, fusion plan, and lowering choices. It emits `GcdHw.lean`. With `--segments` it runs a symbolic execution and emits `GcdHwSeg.lean`. `--summary` prints the symbolic CFG. |
| `formal/tools/dfimport/check.sh` | drift check: regenerates both files and diffs them against the committed ones. `--lean` also runs `formal/check.sh` on the four files. |
| `formal/lean/Formal/Net/GcdHwLib.lean` | hand-written library (see below) |
| `formal/lean/Formal/Net/GcdHw.lean` | GENERATED: `rules` (158), `spine`, the channel names, and the checks `ins_ok`, `outs_ok`, `spine_ok`, `bounded_ok`, `spine_nodup` (`decide +kernel`) |
| `formal/lean/Formal/Net/GcdHwSeg.lean` | GENERATED: 10 templates `T0..T9` and 18 segment certificates `seg0..seg17` |
| `formal/lean/Formal/Net/GcdHwProof.lean` | hand-written: the C transcription `gcdC`, the i1-rewrite lemmas, edges `e0..e17`, the loops, `reach_gcdC`, and the main theorem |
| `formal/lean/Wip/C8i/Nonneg31.lean` | open goal `gcdC_nonneg31` (sorry), plus `#eval` evidence |

```
formal/tools/dfimport/check.sh            # drift: regenerate + diff (seconds)
formal/tools/dfimport/check.sh --lean     # + formal/check.sh on the 4 files (~3.6 min)
cd formal && ./check.sh Formal/Net/GcdHwLib.lean Formal/Net/GcdHw.lean \
   Formal/Net/GcdHwSeg.lean Formal/Net/GcdHwProof.lean
```

To build the oleans (dependency order), from `formal/lean` with `LEAN_PATH=$PWD/.lake/build/lib/lean`:
`../slot.sh lean -o .lake/build/lib/lean/Formal/Net/X.olean Formal/Net/X.lean` for
X = GcdHwLib, GcdHw, GcdHwSeg, GcdHwProof.

Times and peak memory (one slot):

| file | time | peak memory | notes |
|---|---|---|---|
| GcdHwLib | 9 s | 0.6 GB | |
| GcdHw | 26 s | 1.3 GB | WF/spine checks by kernel decide |
| GcdHwSeg | about 290 s | 1.5 GB | 18 segments, 3 to 17 s each |
| GcdHwProof | 6 s | 0.7 GB | |

The lead has to add the four modules to `Formal.lean` and to `check.sh`; I do not own those files.

## Graph size and the ops that appeared

The MLIR has 239 ops: fork 42, cond_br 38, mux 22, constant 21, sink 16, source 15, br 15, cmpi 14
(eq, ne, slt, sgt; at i32 and i1), merge 14 (all 1-input), control_merge 13 (5 with 1 input,
7 with 2 inputs, 1 with 3 inputs), ori 5, trunci 5, andi 5, shrsi 5, extui 2, select 2, subi 2,
addi 1, shli 1, end 1.

After bdc's transforms the graph is **158 firing rules over 252 channels**, with a 34-channel
control spine:
* 29 `comp` rules. 20 of them are fused compute regions. Examples are `subi0+cmpi11+subi1+select1` (bb10's abs) and
  `cmpi4+andi2+cmpi5+ori2`.
* bdc folded the constants that sit in (source, constant) pairs into literals, and absorbed forks
  into regions (BDC_FORK_FUSION).
* `br` and 1-input `merge` are wires.
* a 1-input `control_merge` becomes one `cm` rule. An n-input `control_merge` becomes n `cm`
  labels: bdc lowers it as arbiter + fork.
* 22 mux rules (21 two-way, 1 three-way on i2), 38 branch, 31 fork, 22 cm, 16 sink.
* 20 ops were collapsed under H_SOURCE_ETERNAL: 4 sources plus the forks and constants they drive.

Ops in the rule library: `comp` (any expression over addi, subi, muli, andi, ori, xori, shli,
shrsi, shrui, all ten cmpi predicates, select, trunci, extui, extsi), `fork`, `branch` (cond_br),
`mux` (n-way), `cm` (control_merge input), `sink`.

## How the proof works

1. **Determinacy (generic).** `GcdHwLib.wfOn_of_check` derives 8b's `WFOn` from two Boolean checks:
   * every channel has one consumer;
   * every channel has one producer, except the outputs shared by control_merge inputs that sit on
     the spine.

   It also takes the invariant `Inv P` = "at most one token on the spine channels". This is
   H_ONE_INVOCATION, generalised from 8b's single loop to the whole function, and covers all
   8 multi-input control_merges at once.

   `closed_of_check` proves `Inv P` closed from a per-rule check: a rule that puts a token on the
   spine also takes one off it. 8b's `terminal_unique` and `no_divergence` then give `determinate`
   and `no_longer`. All the checks run on the generated `rules` by kernel `decide`.

   The spine is computed by the tool: control channels that are consumed, but not by a compute
   rule. Lean checks it, so a wrong choice fails the build rather than weakening the theorem.
2. **One schedule, symbolically.** The tool runs the rules on expression-valued tokens, firing the
   lowest enabled rule first. A run stops when every pending branch has an undecided condition.
   Then it splits on that condition and generalises the stuck store into a template whose data
   tokens are variables.

   This produced a 10-template CFG that matches the C blocks one to one:

   | template | block |
   |---|---|
   | T0 | entry |
   | T2 | bb1 |
   | T3 | bb2 |
   | T4 | bb3 loop |
   | T5 | bb5 loop |
   | T6 | bb7 loop |
   | T7 | bb8 |
   | T8 | bb10/bb11 loop |
   | T9 | bb9 |
   | T1 | final |

   Each of the 18 edges is a certificate `execL (symVI F) rules Ti sched = some (Tj.map (subst sig))`.
   The kernel checks it step by step against literal intermediate stores (`chainOK`).

   `sym_run` turns a symbolic run into a real run for every environment that satisfies the
   branch fact. It goes through `fire_hom`: symbolic firing maps to Nat firing under `eval env`.
3. **Glue to C.** `GcdHwProof` transcribes cf_transformed.mlir with the same `Ops`. It has one
   lemma per edge (`e0..e17`, environments are free variables), induction for each loop (`loop3`,
   `strip` for bb5/bb7/bb11, `mainLoop`), and `reach_gcdC`.

   The only arithmetic facts needed are that **Dynamatic's i1 rewrites preserve the C conditions**
   (`gEv_eq`, `gSc_eq`):
   * `((x|y)&1)==0` at i32 becomes trunci → i1 `andi` with true → i1 `cmpi eq` false;
   * `(x&1)!=0 || x<1` gets the same treatment.

   This is a real check on Dynamatic's bitwidth optimisation, not an assumption.

## Hypotheses and fidelity of each primitive

| item | model | fidelity / how to test |
|---|---|---|
| channel | unbounded FIFO (8b) | Token level only. bdc's links (1 to 2 slots) and wire channels (rendezvous) are not modelled; this is 8b's track-8a gap. Determinacy carries over to any capacity bound in which the same schedule fits (8b KahnBounded). |
| compute ops | `Ops.*` on Nat mod 2^w, as bdc emits them: `compute.BINARY` (Verilog `+ - * & \| ^ << >> $signed>>>`) and `CMPI` (signed = flip the MSB, then unsigned compare) | Equal to MLIR `arith` at width w wherever MLIR is defined. Differences: shift amounts ≥ w (MLIR poison; Verilog gives 0 or sign fill; the model follows Verilog). Not proved equal to core `BitVec`; that is a small follow-up. Testable by `bdc/test_compute.py`-style exhaustive vectors. |
| fused region | one strict node computing the region's expression DAG (bdc's `Region.ref`, folded literals) | Exact at token level: a region has one output, and all its inputs are joined. |
| cond_br | test is bit 0 of the condition (`bd_steer .s(cond_data[0])`) | exact |
| mux | 2-way selects on bit 0; n-way on the low ceil(log2 n) bits. An index ≥ n never fires. | The n-way out-of-range case in `bdc_muxn` is not modelled. It is unreachable here, because indices are cm literals. |
| control_merge | n labels, each forwards the token and emits its index. bdc's arbiter choice is the free label choice. | Determinate only under the spine invariant, which holds from the initial store (one start token). Two invocations in flight break it (8b). |
| H_SOURCE_ETERNAL (this tool's own step) | a `source`, and every fork or constant driven only by sources, is an always-valid literal. Its consumers read the value. | bdc does exactly this for the (source, constant) pairs it absorbs. This tool extends it to the 4 source→fork→constant chains that bdc leaves live (bd_src holds req high). At token level such a channel never blocks. Not proved against a model with explicit sources: in the unbounded model a source fires forever and there is no terminal state. Test: GLS on gcd_hw checks that those bd_src req nets stay high. Fidelity to the fabric: grade B, it is a wire. |
| inputs | any Nat on `a`, `b` (read as i32 bit patterns) | `gcdC` masks every op, so values ≥ 2^32 behave as their low 32 bits |
| H_NONNEG31 | **not assumed in the main theorem.** It is only needed for the open step `gcdC = Nat.gcd` | `#eval`: exhaustive on [0,40)², plus large vectors, all equal `Nat.gcd`. Negative patterns: (−6, 4) and (4, −6) do not terminate in 200 fuel; gcd(−1, −1) = −1. |

## Drift check

`check.sh` regenerates both generated files from the MLIR through bdc's code and diffs them.

Negative control: changing `constant14` (the −1 in bb10's `diff > -1`) to −2 in a copy of the MLIR
changes the fused region literal from 4294967295 to 4294967294. The diff catches it. If the file
were regenerated anyway, `seg17` would certify a different `sig17` and `e13`/`e17` would no longer
match `absd`, so the proof would break.

The importer pins bdc's environment knobs to the gcd_hw defaults (`check.sh` unsets the `BDC_*`
variables). An unfused build (BDC_OP_FUSION=0) is also supported by the importer (one comp per op),
but I did not prove it.

## What does not work / open

* **`gcdC = Nat.gcd` on [0, 2^31)², not proved.** The statement is in `Wip/C8i/Nonneg31.lean`.
  Route: per-op lemmas (`shrsi 32 x 1 = x/2`, `slt x 1 ↔ x = 0`, `absd = |a−b|`, `minC = min`,
  `shli` does not wrap because `gcd·2^k ≤ max a b`), then follow 8b's `gcdC` and finish with
  `gcdC_eq`. Estimated 1 to 2 h.
* Termination of `gcdC` for all inputs is not claimed. Negative inputs can loop, and the hardware
  would livelock too. This is the abs-probe story in `gcd_hw.v`.
* Below the token level (handshake, links, bundling, arbiter physics) nothing new is covered here;
  that is 8b's track-8a list.
* **Performance trap, worth knowing for reuse.** Checking a whole symbolic run in one kernel
  `decide` grows superlinearly: an 11-firing run passed 4 GB. `List.mapIdx` (it uses an Array
  accumulator) costs about 3 s per store.

  What fixed it:
  * a structural `applyGo`;
  * per-step certificates (`chainOK`);
  * standalone edge lemmas. Inline `edge` terms inside the loop proofs made the kernel unfold i32
    ops on symbolic arguments, which passed 4 GB again.

## Effort to finish / extend

| task | estimate |
|---|---|
| H_NONNEG31 bridge | 1 to 2 h |
| BitVec equality of `Ops` | about 1 h |
| Another kernel (collatz, ipow, isprime) | The tool and library are generic. The glue (`GcdHwProof`) is per kernel, about 1 to 2 h each. isprime's 2-exit loop and 4-input cm need the explore loop to allow more than one pending condition. |

## What it buys the project

* The graph in the theorem is the one bdc compiles, read through bdc's own code. A change in the
  MLIR, in bdc's parser, or in its fusion or lowering shows up as drift, and the proof then
  re-checks or fails.
* Determinacy of the whole gcd_hw dataflow graph under one invocation: arbitration outcomes in the
  8 control_merge arbiters cannot change the result or the firing count. This is the token-level
  half of the capstone theorem.
* A machine-checked agreement between the hardware's i1-rewritten loop conditions and the C's i32
  ones.

## Decisions taken (no one to ask)

* I used the gcd fixture. It is what gcd_hw compiles, and there is no other gcd_hw kernel.
* I exported bdc's post-fusion graph rather than the raw MLIR, because that is what bdc emits.
  Fused regions are modelled as single strict nodes, which is exact at token level.
* Sources: I chose the "eternal literal" abstraction (H_SOURCE_ETERNAL) over a capacity model,
  because an unbounded source has no terminal state.
* Values are Nat mod 2^w with the shared `Ops`, rather than BitVec. This keeps the graph-to-C
  matching definitional and omega-friendly.
