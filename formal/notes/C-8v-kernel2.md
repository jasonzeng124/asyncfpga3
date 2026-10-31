# C-8v: second (and third) kernel through the importer: ipow and collatz

**Status: DONE**

## Verdict

The C-8i model, importer and checker verify kernels other than gcd. The importer
(`formal/tools/dfimport/mlir2lean.py`) ran on ipow and collatz **with no kernel-specific
code**. The only change was generic naming options. `GcdHwLib` (the rule semantics,
determinacy checks and symbolic-run soundness) was reused unchanged.

**ipow** (`kernels/ipow/ipow.c`, two variable × variable multiplies, a rotated loop, 2
two-input control_merges). Core Lean, no sorry, axiom or native_decide. Proved:
* `Formal.Net.IpowHw.ipow_hw_graph_computes_pow`: assume `b` is any Nat and `e < 2^32`
  (every i32 bit pattern). From the store with one token on each of `b`, `e` and `start`:
  * a complete run exists;
  * every complete run, under any schedule and any arbitration, ends in the store with exactly
    `[ipowSpec b e]` on `out0`, the end token, and nothing else;
  * no run is longer.

  Here `ipowSpec b e = b^e mod 2^32` if `e < 2^31` (non-negative i32), and `1` otherwise.
* `ipowC_spec`: the hand transcription of the C, `ipowC`, terminates within fuel 32 on every
  i32 `e` and equals `ipowSpec`.
* Token-level liveness on all i32 inputs, with no fairness assumption: `ipow_hw_graph_live`,
  `_bounded`, `_no_infinite_run`, `_maximal`.
* `ipow_hw_graph_computes_ipowC`: the same as the first result, stated against `ipowC`
  directly (C-8i's form).

There is no input-range hypothesis beyond "e is i32". Unlike gcd, every i32 input terminates.

**collatz** (`kernels/collatz/collatz.c`) is the third kernel. Proved:
* `Formal.Net.CollatzHw.collatz_hw_graph_computes_collatzC`: if the C transcription
  `collatzC fuel n = some r`, then every complete run on every schedule ends with exactly `[r]`
  on `out0` and the end token. A complete run exists, and no run is longer.
* Liveness under the same hypothesis: `collatz_hw_graph_live`, `_no_infinite_run`, `_maximal`.
* `collatz_terminates_small`: for `1 ≤ n < 256` the hypothesis holds at fuel 200. This is
  checked by kernel `decide +kernel` on the C transcription. `collatz_hw_graph_small` therefore
  gives the result and the absence of infinite runs unconditionally for those n.
* `collatzC 200 27 = some 111`, the figure in the kernel's header comment.

**Termination of collatz is not claimed** beyond `[1, 256)`. It is the Collatz conjecture for
positive n, and it is false for n = 0 and for some negative i32 inputs (−1 → −2 → −1).

## Kernel choice

* **ipow** was the main target. It has a loop, a control_merge, a select-fused if, and real
  `muli`, which gcd never had. It is total on all i32, so the full gcd-style result
  (correctness and liveness) holds with no input restriction.
* **collatz** was added once ipow was done, to measure the cost of a third kernel. It took
  about 20 min of writing.

I also ran the importer `--summary` unchanged on all fixtures:

| kernel | result |
|---|---|
| collatz64 | 32 rules, 3 templates, 4 segments |
| xorshift | 36 rules, 3 templates, 4 segments |
| isprime | 10 templates, 18 segments |
| fir, single_loop | stop on `mem_controller`: memory is not modelled |

## Files

| file | what |
|---|---|
| `formal/tools/dfimport/mlir2lean.py` | **edited (C-8i's file, in my scope "extend generically")**. Adds `--ns`, `--graph-module`, `--label` and `--short`, whose defaults reproduce the gcd files byte for byte. Port names are now generic: `ch<ArgName>` per argument, `chOut` for the one data result, `chEnd` for the end token. gcd keeps `chA`, `chB`, `chStart`, `chOut`, `chEnd`. Nothing else changed. |
| `formal/tools/dfimport/check.sh` | **edited**. The drift check now regenerates gcd, ipow and collatz. `--lean` also checks the 7 new Lean files. |
| `formal/lean/Formal/Net/IpowHw.lean`, `IpowHwSeg.lean` | GENERATED: 38 rules over 59 channels, 8-channel spine; 3 templates, 4 segments |
| `formal/lean/Formal/Net/IpowHwProof.lean` | C transcription `ipowC`, the i1 rewrite lemma `gR_eq`, edges e0..e3, `loop_reach`, `reach_ipowC`, `ipow_hw_graph_computes_ipowC` |
| `formal/lean/Formal/Net/IpowHwLive.lean` | `ipowSpec`, i32 lemmas, `loop_spec`, `ipowC_spec`, the graph corollary, liveness |
| `formal/lean/Formal/Net/CollatzHw.lean`, `CollatzHwSeg.lean` | GENERATED: 32 rules over 49 channels; 3 templates, 4 segments |
| `formal/lean/Formal/Net/CollatzHwProof.lean` | C transcription, the rewrite lemmas `three_n`, `gN_eq` and `ne_eq_not`, the edges, the loop, the theorems, the finite termination check |
| `formal/lean/Wip/C8v/negctl.sh` | negative control (see below) |

The lead has to add the 7 modules to `Formal.lean`. They need `Formal.Net.GcdHwLib` but not
the slow `GcdHwSeg`.

## Commands that check

```
formal/tools/dfimport/check.sh                 # drift: 6 generated files (gcd, ipow, collatz) match, seconds
cd formal && ./check.sh Formal/Net/IpowHw.lean Formal/Net/IpowHwSeg.lean \
    Formal/Net/IpowHwProof.lean Formal/Net/IpowHwLive.lean
#   -> [audit] 719 declarations checked / [check] OK  (about 70 s under heavy slot contention)
cd formal && ./check.sh Formal/Net/CollatzHw.lean Formal/Net/CollatzHwSeg.lean Formal/Net/CollatzHwProof.lean
formal/tools/dfimport/check.sh --lean          # all of the above plus C-8i's four gcd files
```

Build times on one slot (lake): IpowHw 2 s, IpowHwSeg 12 s, IpowHwProof plus IpowHwLive under
10 s, CollatzHw* about 30 s in total, including the `decide +kernel` over n < 256. Each is under
1.5 GB. These kernels are much cheaper than gcd's 290 s Seg file because their segments have
fewer templates.

## How (and what was kernel-specific)

The recipe is C-8i's, unchanged:
1. Generate the graph and the symbolic CFG.
2. Write one `edge'` lemma per segment, with the target environment stated in C-level helper
   terms.
3. Prove one induction per loop template.
4. Prove a `reach_C` lemma by case analysis following the C.
5. `determinate` and `no_longer` from GcdHwLib give the every-schedule statement.
   `prefix_run` and the uniform bound give liveness.

Kernel-specific hand work, all of it about matching Dynamatic's rewrites to the C:

| item | ipow | collatz |
|---|---|---|
| loop rotation | entry tests `e > 0`; the body ends with the test on `e >> 1`. The glue starts the C loop either at the entry template or at the loop-head template. | same, on `n == 1` |
| i1 bit tests | `(e & 1) == 1` became trunci/andi/`cmpi eq … false` driving a `select` (`gR_eq`) | `(n & 1) == 0` the same (`gN_eq`) |
| other rewrites | none | `n != 1` became `n == 1` with swapped branches (`ne_eq_not`); `3*n + 1` became `(n + (n << 1)) + 1` by strength reduction (`three_n`, at i32) |
| r = 1 | the literal reaches the graph as `extui(i1 true)` (`extui11`) | steps = 0 as `extui(i1 false)` |

The spec side is ordinary arithmetic:
* ipow: the invariant `r * b^e mod 2^32` through `Nat.pow_mod` and `Nat.mul_mod`. `shrsi 32 e 1 = e/2`
  and `sgt e 0 ⟺ 0 < e < 2^31` for `e < 2^32`.
* collatz: no spec beyond the C transcription, since its meaning is the step count itself.

## Reuse from gcd (measured)

| part | reused? |
|---|---|
| `GcdHwLib.lean` (1033 lines: rule semantics, WF and spine checks, determinacy, symbolic soundness) | 100 %, unchanged |
| importer, symbolic explorer, certificate format, `check.sh` | about 97 %. About 40 lines of naming options were added; no logic changed. |
| proof skeleton (`edge`, `edge'`, `fact1`, `reach_trans`, `cnt_lmap`, `init_inv`, `final_terminal`, `ofL_sp`, `init_store`, `final_store`, the every-schedule theorem, the 4 liveness theorems, `run_of_seq`) | about 120 lines per kernel, copied with names changed. These belong in `GcdHwLib`, parameterised by `rules`/`N`/`spine`, but that file is C-8i's. |
| truly new per kernel | ipow: about 25 lines of C plus rewrite lemmas, about 40 lines of edges and loops, about 70 lines of `b^e` arithmetic. collatz: about 30 plus 40 lines, with no arithmetic spec. |

Wall-clock effort: ipow took about 45 min including the importer generalisation; collatz took
about 20 min of writing. Most of the elapsed time was waiting on the shared Lean slots.

**A third, or fourth, kernel:**
* **xorshift and collatz64**: the importer already gives 3 templates and 4 segments. Expect
  30 to 60 min each. The work is a C transcription plus one rewrite lemma per Dynamatic rewrite
  (collatz64 is i64: the `Ops` are width-generic). The value spec could take longer for
  xorshift, if one wants more than the C transcription.
* **isprime**: 10 templates and 18 segments, about gcd's size. Expect 1.5 to 2 h of glue. C-8i
  predicted that isprime would need more than one pending condition in the explorer; it did
  not (the explorer ran unchanged).
* **Memory kernels** (fir, single_loop) need a `mem_controller` / load / store model first.
  That is a new primitive, not glue.

## Drift check and negative control

`check.sh` regenerates all 6 generated files and diffs them against the committed ones. All
match, and gcd's output is byte-identical to before.

`formal/lean/Wip/C8v/negctl.sh` changes `constant2` (the shift amount of `e >> 1`) from 1 to 2 in a
temporary copy of the ipow MLIR. It then runs two controls:
1. **Drift.** The script regenerates the graph and diffs it against the committed files. The
   regenerated rule 24 becomes `shrsi … (.lit 2)`, and the diff catches it.
2. **Proof.** In a temporary overlay (`lean --root`; `Formal/` and `.lake/build` are not touched),
   the script compiles the regenerated graph and certificates, then the unchanged `IpowHwProof.lean`
   against them. The certificates still check, because they describe the mutated graph. The proof
   fails: `e0` and `e2` have unsolved goals, because their stated targets no longer match the
   graph's `e >> 2`.

Result: `[negctl] PASS (both controls fired)`. It takes about 1 min of Lean when a slot is free.

## Fidelity and hypotheses

These are the same as C-8i (see `C-8i-gcdhw.md`), with nothing new modelled:
* token level only, with unbounded FIFO channels;
* `Ops` at bdc's Verilog semantics: wrap-around `muli`, arithmetic `shrsi`, signed compare by
  flipping the MSB;
* fused regions as strict nodes;
* control_merge as free arbitration;
* H_SOURCE_ETERNAL, here for 3 source chains in ipow and 2 in collatz;
* H_ONE_INVOCATION, proved from the initial store, not assumed.

Kernel-specific points:
* **Signed overflow.** C leaves `r * b`, `b * b` and `3 * n + 1` undefined on overflow. The
  transcription uses i32 wrap-around, which is what the hardware computes. `ipowSpec` is the
  wrap-around power.
* **The fixture is the source.** The MLIR is the committed fixture
  `cloud/fixtures/frontend/<k>/comp/handshake_transformed.mlir`, which the build scripts read
  as `build/frontend/<k>/...`. I did not re-run the Dynamatic frontend from `kernels/<k>/*.c`.
  The link from the C source to that MLIR is Dynamatic's, and it is checked here only through
  the theorem: the graph computes the hand transcription of the C.

## What it does NOT show

* Anything below the token level: handshake timing, finite link capacity, bundling delays,
  arbiter metastability. This is the track-8a gap.
* Collatz termination for n ≥ 256, n = 0 or negative n. The collatz results are conditional
  there.
* That bdc's emitted Verilog implements the rules. The importer reads bdc's graph and lowering
  choices, not its Verilog.
* `BDC_OP_FUSION=0` and other knob settings: only the default build is proved.
* The `Ops` model is not proved equal to core `BitVec` (C-8i open item).

## Surprises

* The importer and symbolic explorer worked unchanged on four more kernels, including isprime,
  which C-8i expected to need changes.
* Dynamatic's strength reduction (`3n+1 → n + (n<<1) + 1`) and branch inversion (`!=` → `==`
  with swapped targets) appear in the collatz graph. Both are now machine-checked at i32.
* In the ipow graph the `end` token comes straight from the start fork. The end token is
  therefore produced long before `out0` and orders nothing.
* `decide` (the elaborator) hits max recursion on `collatzC 200 27`; `decide +kernel` takes
  seconds.
* Lean name clash: inside `namespace Formal.Net.IpowHw`, `Inv` is ambiguous between `_root_.Inv`
  and `GcdHw.Inv`. gcd did not hit this because its namespace is under `GcdHw`.
