# B-port-core: Phase 1 item B, port `Cells/` from `Prelim` to `Core` (probe P1)

Shard B, PROGRAM.md "After the feasibility verdicts", Phase 1 item B. Porting
guide: notes/A-substrate.md section 4.

## Problem statement

Before: shard B's cell proofs were stated over `Formal.Cells.Prelim`, a local
copy of the values and LUT semantics (`K3 = {f,t,x}`, `lutB`, the closure
`lutK`, `muxTree`) and over `CElemTiming.Trace`/`WinDelay`. Core had its own
copies (`Formal.Core.K3`, `Lut.eval`, `Lut.keval`, `Substrate.Sig`, `Win`),
and `Core.Bridge` related them through an explicit isomorphism `isoCells`.

After: `Prelim` no longer has semantics of its own. Every Cells theorem is a
theorem about Core's objects:

| Prelim name | now | how |
|---|---|---|
| `K3` | `abbrev K3 := Formal.Core.K3` | same type. `K3.f/t/x` are `@[match_pattern, reducible]` names for `zero/one/X` |
| `K3.ofBool` | `abbrev` of `Core.K3.ofBool` | same constant |
| `K3.join` | `def`, `join_eq_merge : join = Core.K3.merge := rfl` | own constant only so `simp [K3.join]` keeps unfolding to the `if` |
| `K3.not` | `def`, `not_eq_core : not = Core.K3.not := rfl` | same reason |
| `K3.mux` | unchanged def; `mux_eq` = the match `kevalT` inlines | |
| `muxTree g ins` | unchanged (Bridge unfolds it) | `muxTree_ofFn : muxTree g (List.ofFn v) = Core.kevalT k g v` |
| `lutK init ins` | **`muxTree init.testBit ins`** (Core's mux tree; was the closure over `completions`) | `lutK_ofFn : lutK L.init.toNat (List.ofFn v) = L.keval v`, `lutK_ofFn_spec` (= `L.kevalSpec v`) |
| old closure `lutK` | theorem `MuxTree.lutK_eq_closure` (also `lutK_eq_cloF/cloN`) | proved from `muxTree_eq_cloN` |
| `lutB init ins` | unchanged def (Bridge's proof unfolds it) | `lutB_ofFn : lutB L.init.toNat (List.ofFn x) = L.eval x` |
| `CElemTiming.Trace` | `abbrev Trace := Formal.Core.Substrate.Sig` | same type |
| `CElemTiming.WinDelay lo hi` | `abbrev WinDelay lo hi x y := Formal.Core.Substrate.Win lo hi x y` | same relation; `winDelay_def` restates the body |

Nothing is weakened: every theorem statement in every Cells file is
unchanged. The only proof edits are mechanical:

* `cases h : (… : K3) with | f | t | x` alternatives renamed `zero | one | X`
  (MuxTree, TernarySound, TernaryPhases, Latch, TernaryExact; 28 lines);
* the six places that unfolded the old closure definition of `lutK`
  (Bundling 1, TernarySound 2, LibEndMemMlink 2, OnNetlist 1) now rewrite with
  `MuxTree.lutK_eq_closure` (those four files import `Formal.Cells.MuxTree`);
* MuxTree: `muxTree_eq_lutK` is now `rfl`; `lutK_eq_cloN/cloF` are proved
  from `muxTree_eq_cloN` (statements unchanged), plus `lutK_eq_closure`.

Physical content: H_KLEENE_LUT is unchanged (the LUT is a pass-transistor mux
tree, an X select passes equal data). The only change is which of two proved
equal readings is the definition: `lutK` is now the mux tree (Core's
`kevalT`, research GLS order, I0 at the root) and the closure is a theorem.

## Design chosen, and why

Recommended design ("define Prelim via Core"), with two restrictions forced
by files I may not edit:

1. `lutB` keeps its body `init.testBit (lutIdx ins)`: `Core/Bridge.lean`
   proves `cells_lutB_eq_eval` by `simp [Formal.Cells.lutB, ...]`, and
   `Net/CoreLutPrelim.lean` by `rw [..., Formal.Cells.lutB, ...]`. Redefining
   `lutB` as `Lut.eval` on a `BitVec (2^ins.length)` would break both. `lutB`
   is literally Core's `Lut.eval` read through `List.ofFn` (`lutB_ofFn`, a
   three-step rewrite), so nothing is lost.
2. `muxTree` keeps its structure: Bridge and CoreLutPrelim unfold it.
   `lutK` was free to change, because both reach it only through
   `MuxTree.muxTree_eq_lutK`, whose statement is kept (now `rfl`).

Why `K3` as an `abbrev` with match-pattern constructor names rather than "keep
K3 and prove iso": the iso already existed (`Bridge.isoCells`); the point of
the port is that there is one `K3`. With the abbrev, `.f`/`.t`/`.x`, `match`
patterns, `decide`, `DecidableEq`, `cases … <;>` all keep working; only named
`cases … with` alternatives had to be renamed. `Bridge.toCells` is now the
identity function (provably, `cases a <;> rfl`).

Why `lutK := muxTree init.testBit` rather than `Lut.keval ⟨BitVec.ofNat _ init⟩
(ofList …)`: same semantics (`lutK_ofFn`), but no dependent `BitVec (2^len)`
in the hot path of the 200+ `decide` proofs, and Bridge/CoreLutPrelim keep
compiling. It is Core's `kevalT` node for node (`muxTree_ofFn` is proved by
unfolding one level, `cases v 0 <;> rfl`).

## Decide performance (kernel)

Micro-benchmark (`scratchpad/port/bench`), `arb_state` INIT
`0xFFF0FFB2ACACACAC`, all 3^6 = 729 K3 input vectors, `decide +kernel`,
wall time minus the 0.44 s import header:

| goal | old closure `lutK` | new mux-tree `lutK` |
|---|---|---|
| `∀ 6 K3, lutK S [...] ≠ .t ∨ True` | 1.35 s | 0.27 s |
| `∀ 6 K3, lutK S [...] = lutK S [...]` | 1.47 s | 0.37 s |
| `decide` (elaborator), 81 vectors | 0.25 s | 0.12 s |

Whole-closure wall time per file, sequential, same machine, before vs after
(not a controlled benchmark: other shards were compiling concurrently):
1333 s before, 1222 s after, over the 93 modules of the first closure (base.log vs new1.log). Largest per-file gains are on Kleene-heavy files
(OnNetlist 99 → 59 s, LibCtlMergeMux 27 → 10 s, LibEndMemMlink 27 → 9 s,
CElemFn 22 → 15 s); no file got materially slower beyond noise.

## Verification

All modules that transitively import `Formal.Cells.Prelim` (plus unbuilt
dependencies), compiled in topological order with
`scratchpad/port/comp.sh SRC OUT <modules>`: each is
`FORMAL_SLOT_CWD=SRC LEAN_PATH=OUT:<lake env LEAN_PATH> ../slot.sh lean <file> -o OUT/<path>.olean`,
where OUT is a private copy of `.lake/build/lib/lean/Formal` (so the shared
build was never touched while other shards were working; equivalent to the
`lake env lean … -o .lake/build/…` command with a shadow output dir).
Order: `scratchpad/port/topo.py`.

**Result: all 114 modules compile (rc=0), no file reverted.** The set is
every module that transitively imports `Formal.Cells.Prelim`, as of the live tree
at about 06:45 (B, C and A files, including other probes' untracked new Cells
files), plus the unbuilt or stale dependencies they need
(`Timing.WinArray*`, `Timing.RoutedCePairS1*`, `Net.Import.Netlist`, ...):

`Cells.AMerge2` `Cells.AMerge2Proof` `Cells.AMerge3` `Cells.AMerge3Proof` `Cells.AMergeGates` `Cells.AMergeSys` `Cells.AMergeTimed` `Cells.AMergeTimedC` `Cells.AMergeTimedW` `Cells.ArbA0Fork` `Cells.ArbAnalog` `Cells.ArbAnalog2` `Cells.ArbBinary` `Cells.ArbCorners` `Cells.ArbCornersPin` `Cells.ArbHandover` `Cells.ArbHeldTimed` `Cells.ArbHeldTimed2` `Cells.ArbInvolution` `Cells.ArbInvolution2` `Cells.ArbKleene` `Cells.ArbOverlapRace` `Cells.Bundling` `Cells.CElemCore` `Cells.CElemFn` `Cells.CElemInvolution` `Cells.CElemTiming` `Cells.CTree` `Cells.CTreeTimed` `Cells.ConstraintsFastFall` `Cells.ConstraintsLatchRst` `Cells.ConstraintsMore` `Cells.ConstraintsMux` `Cells.ConstraintsSel` `Cells.FifoFidelity` `Cells.GcdCells` `Cells.Latch` `Cells.LibCtlMergeMux` `Cells.LibEndMemMlink` `Cells.LinkHandshake` `Cells.LinkTimed` `Cells.MergeMuxSI` `Cells.MuxN3` `Cells.MuxN3Proof` `Cells.MuxRtzTimed` `Cells.MuxTree` `Cells.OnNetlist` `Cells.OnNetlistArb` `Cells.OnNetlistTimed` `Cells.OnNetlistTimed2` `Cells.OpsCounter` `Cells.OpsTimed` `Cells.OpsTimed2` `Cells.OpsTimedMux` `Cells.OpsTimedWit` `Cells.PinAssign` `Cells.PipePerPin` `Cells.PipeTimed` `Cells.PipeTimedN` `Cells.PipeWitness` `Cells.Prelim` `Cells.RulesKL` `Cells.TernaryExact` `Cells.TernaryOnBits` `Cells.TernaryOnBits2` `Cells.TernaryPhases` `Cells.TernarySound` `Core.Bridge` `Core.Discretize` `Core.Substrate` `Core.Substrate.Legacy` `Core.Substrate.Real` `Gen.All` `Gen.Cells` `Gen.Netlist` `Gen.PrelimSem` `Gen.ProofsArb` `Gen.ProofsCE` `Gen.ProofsCtl` `Gen.ProofsLatch` `Gen.ProofsLink` `Gen.ProofsMisc` `Gen.ProofsPrims` `Net.BridgeRing` `Net.BridgeWire` `Net.CoreLut` `Net.CoreLutPrelim` `Net.Fasm.Basic` `Net.Fasm.CePair` `Net.Fasm.CePairS1` `Net.Fasm.CePairS2` `Net.Fasm.CePairS3` `Net.Fasm.CePairS4` `Net.Fasm.CoreView` `Net.FasmLink.Basic` `Net.FasmLink.LinkArb` `Net.FasmLink.Proofs` `Net.FasmLink.S1` `Net.FasmLink.S2` `Net.FasmLink.S3` `Net.FasmLink.S4` `Net.Import.Cells` `Net.Import.Netlist` `Net.Import.PrelimSem` `Net.Import.Proofs` `Net.Ring` `Timing.GrantFork` `Timing.GrantForkInst` `Timing.RoutedCePair` `Timing.RoutedCePairS1Fork` `Timing.RoutedCePairS1Input` `Timing.RoutedCePairS1Loop` `Timing.WinArray` `Timing.WinArrayB`

One transient failure, not caused by the port: `Net.Import.PrelimSem` (C)
failed in BOTH arms (HEAD sources and ported) because the shared
`.lake/build` olean of `Net.Import.Netlist` was older than its source (C's
in-flight edit). After compiling `Net.Import.Netlist` from source it passes in
both arms; `Net.Import.Proofs` and `Net.FasmLink.Proofs` were then recompiled
on top and pass. `Net.MullerSI` and `Cells.AMerge3Proof` were OOM-killed once
under memory pressure from other shards and passed on rerun (MullerSI is no
longer in the closure: C has since decoupled `Net.Muller*` from Cells).

After the check, the fresh `.olean`s of these modules were copied into
`.lake/build/lib/lean` for every module whose live source still equalled the
compiled snapshot (112 modules; `.lake/build` has no `Formal/Gen` directory,
so the Gen oleans were not installed; PipeWitness, AMergeTimedC, OpsCounter
were being edited by their owners and were skipped). `lake build` was not run.

Files edited (all under `formal/lean/Formal/Cells/`): `Prelim`, `MuxTree`,
`CElemTiming`, `Bundling`, `TernarySound`, `TernaryPhases`, `TernaryExact`,
`Latch`, `LibEndMemMlink`, `OnNetlist`. No statement changed. No `sorry`,
`axiom`, `native_decide` added.

## What remains to delete Prelim

Prelim is now a naming layer. Deleting it means either moving it, or
rewriting B's list-indexed statements to Core's `Fin k →` vectors.

Smallest path (recommended): move the content of `Cells/Prelim.lean` to a
Core module (e.g. `Formal/Core/LutList.lean`, shard A's) under the same
namespace or with an `export`, and delete `Cells/Prelim.lean`. Files that
import `Formal.Cells.Prelim` and would need their import line changed:

* shard B: every Cells file (about 40).
* shard C: `Net/Fasm/Basic.lean`, `Net/CoreLutPrelim.lean`,
  `Gen/PrelimSem.lean`, `Net/Import/PrelimSem.lean` (and whatever else of C's
  in-flight files import it; grep `import Formal.Cells.Prelim`).
* shard A: `Core/Bridge.lean` (imports Prelim and MuxTree).

Full path (no list view at all): replace `lutB init [a,b,…]` by
`(Lut.ofNat init).eval ![a,b,…]`-style terms in ~300 `lutB` and ~200 `lutK`
occurrences, and `completions`-based lemmas (TernarySound, TernaryExact,
Bundling, LibEndMemMlink, OnNetlist, MuxTree) by Core's `Consistent`. This
buys nothing semantically (the equations above are already proved) and is
several days of edits; not recommended.

Independently of the choice, these become trivial and can be deleted or
simplified by their owners:

* `Core/Bridge.lean` section Cells: `toCells`/`ofCells` are the identity
  (`toCells a = a` by `cases a <;> rfl`); `cells_lutB_eq_eval`,
  `cells_lutK_eq_keval`, `cells_muxTree_eq_keval` are B's `lutB_ofFn`,
  `lutK_ofFn`, `muxTree_ofFn` up to `toCells = id`.
* `Net/CoreLutPrelim.lean` (C): `toP`/`ofP` are the identity; `lutK_eq_kevalL`
  is `Prelim.lutK` vs C's `kevalL`.
* `Core/Substrate/Legacy.lean` shard-B section: `win_iff_winDelay` is
  `Iff.rfl` on identical constants now (`WinDelay` unfolds to `Win`);
  `loop_iff` unchanged.
* `Core/Discretize.lean`: imports `Cells.CElemTiming` only for the bridges
  listed in A-substrate.md §4 "Left for shard A".

## Not done

* `CElemTiming.Transport`, `Loop`, `exc` are left as B definitions (Legacy
  maps them: `transport_fixed_win`, `loop_iff`). `Transport d` could become
  Core's `TraceDiscrete.Transport`, but Legacy states `transport_fixed_win`
  against B's, so it is left.
* Continuous-time and corner items 4-5 of the porting guide (state timing
  conditions as `EndpointOK` instances) are Phase 2 work, not a rename.
* No Cells theorem was restated in `Fin k →` form.

## How to re-check

From `formal/lean`, for each module `M` (path `P`) of the closure in
topological order (any order in which imports come first):

    PATH=$HOME/.elan/bin:$PATH ../slot.sh lake env lean P.lean -o .lake/build/lib/lean/P.olean

The closure is every module whose imports reach `Formal.Cells.Prelim`
(`grep -rl 'import Formal.Cells' Formal`, iterated). The probe used a private
copy of `.lake/build/lib/lean/Formal` as the output directory (put first on
`LEAN_PATH`) so other shards' checks were never disturbed mid-run.

Axioms of the new agreement lemmas (`lutK_ofFn`, `lutK_ofFn_spec`,
`lutB_ofFn`, `MuxTree.lutK_eq_closure`, `CElemTiming.winDelay_def`):
propext, Quot.sound, and Classical.choice for `lutK_eq_closure` (from `simp`); `winDelay_def` uses none (checked with `#print axioms`).
