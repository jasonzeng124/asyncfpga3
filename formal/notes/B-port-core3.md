# B-port-core3: deleting `Cells/Prelim` — a verified end-state patch (probe Bpd)

Shard B, 2026-10-29, PROGRAM.md Phase 1 ("port every Cells/ proof from Prelim
to Core. Delete Prelim"). Follows notes/B-port-core.md, B-port-core2.md (Bpt),
A-lutlist.md, A-lutlist2.md. `Formal/Core/LutList.lean` is now in the tree, so the
deletion could be compiled end to end for the first time.

**Verdict.** The patch below (B part + A/C part, plus `rm Formal/Cells/Prelim.lean`)
compiles: every one of the **338** modules that import Prelim directly or
transitively (B 196, A/C 142) compiles with Prelim **absent**, against the tree
at HEAD 0af7392 (+ the untracked Cells files present at 10:50 UTC). The
B part **cannot land on its own**: with Prelim kept and the A/C files
unpatched, 7 modules fail (§4). B's part, A's/C's part and the deletion must be
ONE commit. No statement changes meaning (§1); 17 A/C files need edits, all
mechanical (one import line, qualified renames, or one `open` line).

## 1. Prelim vs `Core/LutList`: every declaration has an equivalent

Textual diff of the two files below their `namespace` line: identical code except
(i) namespace `Formal.Cells` -> `Formal.Core.LutList`, (ii) Prelim's
`open Formal.Core` in `section CoreAgree` (LutList is inside `Formal.Core`, same
resolution), (iii) LutList adds `muxTree_eq_lutK` (`rfl`), (iv) shorter docstrings
in LutList (Prelim's H_KLEENE_LUT test sentence — GLS with an X-driven select pin
and equal data, or a slow edge on one pin — and "physical I0..I5 order not known"
are not in LutList's text; LutList's header says the order is Core's and Bridge
relates it to silicon). **Nothing is missing.**

`formal/lean/Wip/Bpd/PrelimLutList.lean` (Wip because it imports Prelim, which
is deleted; built on A's `Wip/LutList/PrelimEq.lean`) — **checker OK**
(`bcheck.py Wip/Bpd/PrelimLutList.lean`):

| Prelim `Formal.Cells.` | LutList `Formal.Core.LutList.` | theorem | proof | axioms |
|---|---|---|---|---|
| `K3`, `K3.f/t/x`, `K3.ofBool`, `K3.join`, `K3.mux`, `K3.not`, `K3.admits` | same names | `K3_eq f_eq t_eq x_eq ofBool_eq join_eq mux_eq not_eq admits_eq` | `rfl` | none |
| `lutIdx`, `lutB`, `completions` | same | `lutIdx_eq lutB_eq completions_eq` | list induction | none |
| `muxTree`, `lutK`, `o6B o5B o6K o5K` | same | `muxTree_eq lutK_eq o6B_eq …` | induction / rewriting | propext, Quot.sound |
| (LutList `muxTree_eq_lutK`) | — | `lutK_eq_muxTree` | | propext, Quot.sound |
| theorems `mux_eq lutIdx_ofFn entry_eq_testBit lutB_ofFn muxTree_ofFn muxTree_congr lutK_ofFn lutK_ofFn_spec K3.admits_iff_le K3.join_eq_merge K3.not_eq_core` | same | `<name>_stmt : type_of% @Formal.Cells.<name> = type_of% @Formal.Core.LutList.<name>` (the two statements are the same proposition) | `simp only [defn eqs]`; `mux_eq_stmt` by cases (two distinct auxiliary matchers) | propext (+ Quot.sound) |

All equalities are of whole functions (`funext`), any list length, any INIT.
`#print axioms` (via a deleted `#guard_msgs` companion): only `propext`,
`Quot.sound`, or none. No sorry/axiom/native_decide. Assumed: nothing.
Not covered: docstrings.

## 2. The switched copies and their check

Generator `formal/lean/Wip/Bpd/tools/mkpatch.py` (closure from
`tools/closure.py`, compile driver `tools/runall2.py`; paths point at
`/tmp/claude-0/probes/Bpd`, rerun them in that order). Rules (nothing else changes;
no statement, no proof):

* **R1** direct importers: `import Formal.Cells.Prelim` -> `import Formal.Core.LutList`.
* **R2** (B) every Cells file in Prelim's closure whose code (comments stripped)
  uses a Prelim short name: line `open Formal.Core.LutList` after the last `import`
  (top level; the files then enter `namespace Formal.Cells…` as before).
* **R2c** (A/C) the same line in non-Cells closure files that use a Prelim short
  name and contain a bare `open Formal.Cells` (incl. `open Formal.Cells … in`).
* **R4** qualified `Formal.Cells.<N>` -> `Formal.Core.LutList.<N>` for N a Prelim
  name (`K3`, `K3.*`, `lutB`, `lutK`, `lutIdx`, `muxTree`, `o6B`, `o5B`, …), code and
  docs. B: ArbKleene (`open Formal.Cells.K3`), PrelimCore.
* **R5** explicit-name open `open Formal.Cells (o5B o6B)` ->
  `open Formal.Core.LutList (o5B o6B)` (only Core/XAudit/Events8Arb). Without it,
  R2c alone fails there (`Unknown constant Formal.Cells.o5B`) — found by the check.
* Delete `Formal/Cells/Prelim.lean`.

Not done (not needed for the deletion): Bpt's R5 "trace half" (`CElemTiming.Trace :=
Substrate.Sig`) — a separate change; stale "Prelim" words in docstrings and the
file names PrelimCore / Net/CoreLutPrelim / Gen,Net/Import PrelimSem (45 files mention
"Prelim" in prose after the patch; cosmetic follow-up).

**Check method (end state, Prelim absent).** `formal/lean/Wip/Bpd/Formal/<path>`
holds the patched copy of every module in Prelim's reverse-import closure (338 =
196 Cells + 142 Core/Net/Gen/Timing), with every import of a closure module
renamed to its copy (`Formal.X` -> `Wip.Bpd.Formal.X`); imports outside the closure
(Core, Mathlib, `Formal.Core.LutList`) are the real ones. So no copy's import
closure contains `Formal.Cells.Prelim` (verified: no copy imports a real closure
module) and no declaration exists twice. Each copy compiled with
`/tmp/claude-0/btools/bcheck.py Wip/Bpd/Formal/<path>.lean` in dependency order
(one call per file). The copies differ from the real patched files only in those
import names.

**Result: 338 / 338 OK** (runs 2–5 of the driver on the moving tree, the last
incremental one at HEAD 0af7392 recompiling the 29 new/changed modules and their
dependents; Mathlib importers incl. ArbAnalog(2), CElemCore, CElemInvolution,
ArbInvolution(2), Core/Discretize, Substrate(.Real), TernaryChannels, XSimChanTern,
Delay/InvolutionLoop* all OK once Mathlib's ODE oleans finished). One transient
failure: ArbMultiToken (untracked, being edited by its probe; its later version
passes). Caveat: a copy compiled in an earlier run was not recompiled if its text
and its closure-copies were unchanged; a change in a non-closure dependency between
runs (e.g. Core/Kleene) would not have been seen. The lead's `lake build` +
check.sh after applying is the real test.

Per file (rules applied; every listed module compiled OK as a copy):

B changed (90): Cells.AMergeGates (R1+R2), Cells.AMergeSys (R1), Cells.ArbA0Fork (R1+R2), Cells.ArbAnalog (R1+R2), Cells.ArbBinary (R1+R2), Cells.ArbCornersPin (R2), Cells.ArbHandover (R1+R2), Cells.ArbHeldTimed (R1+R2), Cells.ArbKleene (R1+R4+R2), Cells.ArbNoWithdraw (R2), Cells.ArbOverlapPess (R2), Cells.ArbOverlapRace (R2), Cells.ArbSettled (R2), Cells.Bundling (R1+R2), Cells.CElemCore (R1), Cells.CElemFn (R1+R2), Cells.CElemStrict (R2), Cells.CElemStrict2 (R2), Cells.CElemTiming (R1+R2), Cells.CTree (R1+R2), Cells.CTreeTimed (R2), Cells.ConstraintsLatchRst (R2), Cells.ConstraintsMore (R2), Cells.ConstraintsMux (R2), Cells.ConstraintsSel (R2), Cells.ForkData (R2), Cells.KleeneBox (R2), Cells.KleenePess (R2), Cells.KleeneWin (R2), Cells.KleeneWinBound (R2), Cells.Latch (R1+R2), Cells.LibCtlMergeMux (R1+R2), Cells.LibEndMemMlink (R1+R2), Cells.LibGapLatch (R2), Cells.LibGapMux (R2), Cells.LibGapSteer (R2), Cells.LinkExact (R2), Cells.LinkHandshake (R1+R2), Cells.LinkTimed (R2), Cells.MuxN3Timed (R2), Cells.MuxRtzTimed (R2), Cells.MuxTree (R1+R2), Cells.Necessity2Delay (R2), Cells.Necessity2Latch (R2), Cells.Necessity3Pipe (R2), Cells.Necessity5Delay (R2), Cells.Necessity5Flink (R2), Cells.Necessity5Link (R2), Cells.NecessityMuxRtz (R2), Cells.NecessityReset (R2), Cells.NoRevert (R2), Cells.OnNetlist (R1+R2), Cells.OnNetlistArb (R1), Cells.OnNetlistTimed (R1+R2), Cells.OnNetlistTimed2 (R1+R2), Cells.OpsCounter (R2), Cells.OpsExact (R2), Cells.OpsExact2 (R2), Cells.OpsHold (R2), Cells.OpsTimed2 (R2), Cells.PinAssign (R1+R2), Cells.PipeTimed (R2), Cells.PipeTimedN (R2), Cells.PipeWitness (R2), Cells.PrelimCore (R1+R4+R2), Cells.ResetCapstoneWit (R2), Cells.ResetContract (R1+R2), Cells.ResetGcd (R2), Cells.ResetGcdNetR5 (R2), Cells.ResetGcdNetRe (R2), Cells.ResetGcdVec (R2), Cells.ResetGcdVec2 (R2), Cells.ResetGcdWave (R2), Cells.ResetWitness2 (R2), Cells.RigContract (R2), Cells.RulesKL (R2), Cells.SelfAuditB2 (R2), Cells.SelfAuditB5 (R2), Cells.SelfAuditB6 (R2), Cells.TernaryExact (R1+R2), Cells.TernaryOnBits (R2), Cells.TernaryOnBits2 (R2), Cells.TernaryPhases (R1+R2), Cells.TernarySound (R1+R2), Cells.ZeroDelayNetPhys (R2), Cells.ZeroDelayNetWit (R2), Cells.ZeroDelayRefine (R2), Cells.ZeroDelayTok (R2), Cells.ZeroDelayTokChain (R2), Cells.ZeroDelayTokWit (R2)

B unchanged, shadow-checked (106): Cells.AMerge2, Cells.AMerge2Proof, Cells.AMerge3, Cells.AMerge3Proof, Cells.AMergeTimed, Cells.AMergeTimedC, Cells.AMergeTimedW, Cells.ArbAMerge, Cells.ArbAnalog2, Cells.ArbCorners, Cells.ArbHeldTimed2, Cells.ArbInvolution, Cells.ArbInvolution2, Cells.ArbMultiToken, Cells.ArbPin, Cells.ArbPin2, Cells.AssumeGuaranteeCap, Cells.AssumeGuaranteeEnds, Cells.AssumeGuaranteeEndsCap, Cells.AssumeGuaranteeEndsNet, Cells.AssumeGuaranteeFork, Cells.AssumeGuaranteeLinks, Cells.CElemInvolution, Cells.CTreeExact, Cells.ConstraintsFastFall, Cells.ContractBridge, Cells.Contracts, Cells.ContractsB, Cells.ContractsLink, Cells.ContractsMux, Cells.ContractsOps, Cells.ContractsTrunc, Cells.ContractsTruncCel, Cells.ContractsTruncSteer, Cells.ContractsTruncWit, Cells.FifoFidelity, Cells.GcdCells, Cells.IpowCells, Cells.IpowCellsT, Cells.KappaCPPR, Cells.LibGapMuxN, Cells.LutFbBridge, Cells.LutFbBridge2, Cells.LutFbBridge2Env, Cells.MergeMuxSI, Cells.MuxN3, Cells.MuxN3Proof, Cells.Necessity2AMerge, Cells.Necessity2Arb, Cells.Necessity3AMerge, Cells.Necessity3Arb, Cells.Necessity3PipeCtl, Cells.Necessity4Mux, Cells.Necessity4MuxC, Cells.Necessity4MuxN, Cells.Necessity5Arb, Cells.Necessity5Mem, Cells.Necessity5PipeRst, Cells.Necessity6Mux, Cells.Necessity6MuxJ, Cells.Necessity6MuxN, Cells.Necessity6PipeSel, Cells.Necessity7Mux, Cells.Necessity7MuxN, Cells.Necessity7MuxNRuns, Cells.Necessity7MuxRuns, Cells.Necessity7MuxRunsN, Cells.NecessityMerge, Cells.OnGcdArb, Cells.OnGcdArbA0, Cells.OnGcdArbFix, Cells.OnGcdArbKappa, Cells.OnGcdArbKappaSrv, Cells.OnGcdArbKappaTight, Cells.OnGcdArbKappaTightA, Cells.OnNetlistArbKappa, Cells.OnNetlistArbKappaExact, Cells.OpsTimed, Cells.OpsTimedMux, Cells.OpsTimedWit, Cells.PipePerPin, Cells.ResetCapstone, Cells.ResetCapstoneGlue, Cells.ResetCapstoneMap, Cells.ResetCapstoneMapData, Cells.ResetGcdNet, Cells.RigIdx, Cells.RigLaps, Cells.RigSrc, Cells.RigSrcWitness, Cells.RigSrcWitnessData, Cells.RigToken, Cells.RingPhys, Cells.RingPhysStage, Cells.RingPhysWit, Cells.SelfAuditB, Cells.SelfAuditB3, Cells.SelfAuditB4, Cells.SelfAuditB6Data, Cells.SelfAuditB7, Cells.SelfAuditB8, Cells.WinFifo, Cells.WinFifoCausal, Cells.WinFifoN, Cells.ZeroDelayNet, Cells.ZeroDelayNetTok

A/C changed (17): Core.Bridge (R1+R4), Core.Delay.GLSResolveGen (R4), Core.XAudit.Events8Arb (R5), Gen.PrelimSem (R4), Gen.ProofsArb (R2c), Gen.ProofsCE (R2c), Gen.ProofsCtl (R2c), Gen.ProofsLatch (R2c), Gen.ProofsLink (R2c), Net.BridgeRing (R4+R2c), Net.CoreLutPrelim (R1+R4), Net.Fasm.Basic (R1+R2c), Net.Fasm.CePair (R2c), Net.Import.PrelimSem (R4), Net.Import.Proofs (R2c), Net.RingReset (R2c), Timing.RuntAck (R2c)

A/C unchanged, shadow-checked (125): Core.Delay.GLSResolve, Core.Delay.InvolutionLoopBridge, Core.Delay.InvolutionLoopRate, Core.Delay.InvolutionLoopSignal, Core.Discretize, Core.EnvFast.SteerEnv, Core.Substrate, Core.Substrate.Legacy, Core.Substrate.Real, Core.TernaryChannels, Core.XAudit.Events8Bridge, Core.XAudit.Events8BridgeSel, Core.XSimChanTern, Gen.All, Gen.ProofsMisc, Net.BridgeWire, Net.Capstone, Net.CapstoneCut, Net.CapstoneCutCells, Net.CapstoneCutSpine, Net.CapstoneLive, Net.CapstoneLiveArb, Net.CapstoneLiveNd, Net.CapstoneLiveNd2, Net.CapstoneLiveNdCert, Net.CapstoneLiveNdOff, Net.CapstoneLiveNdStart, Net.CapstoneLiveNdWalk, Net.CapstoneLiveSpine, Net.CapstoneLiveWit, Net.CapstoneLiveWitCells, Net.CapstoneLiveWitCex, Net.CapstoneLiveWitCexCells, Net.CapstoneLiveWitCexData, Net.CapstoneLiveWitCexStepA, Net.CapstoneLiveWitCexStepB, Net.CapstoneLiveWitData, Net.CapstoneLiveWitLib, Net.CapstoneLiveWitNd, Net.CapstoneLiveWitStepA, Net.CapstoneLiveWitStepB, Net.CapstoneLiveWitStepC, Net.CapstoneLiveWitStepD, Net.CapstoneLiveWitStepE, Net.CapstoneLiveWitStepF, Net.CapstoneNet, Net.CapstoneNetChk, Net.CapstoneNetDef, Net.CapstoneNetSound, Net.CapstoneO1, Net.CapstoneRefineGcd, Net.CapstoneRig, Net.CapstoneRigAll, Net.CapstoneRigAllPer, Net.CapstoneRigAllWalk, Net.CapstoneRigTime, Net.CapstoneSafe, Net.CapstoneWalk, Net.CapstoneWalkRun, Net.CapstoneWalkTab, Net.CapstoneWitness, Net.CapstoneWitness3, Net.CapstoneWitnessCells, Net.CapstoneWitnessData, Net.CapstoneWitnessLib, Net.CapstoneWitnessRun, Net.CapstoneWitnessTok, Net.CapstoneWitnessWalk, Net.CollatzCapData, Net.Fasm.CePairS1, Net.Fasm.CePairS2, Net.Fasm.CePairS3, Net.Fasm.CePairS4, Net.Fasm.CoreView, Net.FasmLink.Basic, Net.FasmLink.LinkArb, Net.FasmLink.Proofs, Net.FasmLink.S1, Net.FasmLink.S2, Net.FasmLink.S3, Net.FasmLink.S4, Net.IpowCapCut, Net.IpowCapCutSpine, Net.IpowCapMain, Net.IpowCapNet, Net.IpowCapNetChk, Net.IpowCapNetDef, Net.IpowCapNetSound, Net.IpowCapO1, Net.IpowCapSafe, Net.IpowCapWalk, Net.IpowCapWalkRun, Net.IpowCapWalkTab, Net.KernelCap, Net.KernelCapChk, Net.KernelCapCollatz, Net.KernelCapCut, Net.KernelCapCutSpine, Net.KernelCapDefs, Net.KernelCapGcd, Net.KernelCapHist, Net.KernelCapIpow, Net.KernelCapSafe, Net.KernelCapSound, Net.KernelCapWalk, Net.KernelCapWalkRun, Net.KernelCapXorshift, Net.OpsGen, Net.OpsLink, Net.OpsLinkWitness, Net.OpsPeriod, Net.OpsRingLive, Net.OpsTimedLive, Net.Ring, Net.RingFair, Net.RingGen, Net.RingResetCert, Net.RingTimed, Net.RingTimedPure, Net.XorshiftCapData, Timing.FbFirstRt, Timing.GrantFork, Timing.GrantForkInst, Timing.RoutedCePair, Timing.RuntAckInst

## 3. How to apply (one commit)

From the repo root, on a tree where both patches `git apply --check` (they do at
0af7392 + the working tree of 10:50):

    git apply formal/lean/Wip/Bpd/B.patch     # 90 B files + deletion of Formal/Cells/Prelim.lean
    git apply formal/lean/Wip/Bpd/AC.patch    # 17 A/C files (A: Core/Bridge, Core/Delay/GLSResolveGen,
                                              #  Core/XAudit/Events8Arb; C: the rest)
    cd formal/lean && lake build && ../check.sh

Every patched file is tracked and unmodified vs HEAD except
`Formal/Cells/KleeneWinBound.lean` (untracked, a running probe's file: one R2
line). If the tree has moved, regenerate (`tools/closure.py`, then
`tools/mkpatch.py OUTDIR [--shadow]`) — the rules are the spec, the diffs are an
instance. Also delete `Wip/Bpd/` afterwards or leave it (Wip is not built).

## 4. Negative result: B's part alone does not build

Second shadow tree (deleted after the run): B's patch applied, Prelim KEPT, A/C files
unpatched. 282 OK, **7 FAIL**, 21 skipped downstream:
`Core/Bridge` (l.451 `rw` finds no `Formal.Cells.…` pattern: MuxTree's statements
now name `Formal.Core.LutList.lutK`), `Core/XAudit/Events8Arb` (`Unknown identifier
o5B`… / `rfl` fails), `Net/CoreLutPrelim` (l.79 `rw`), `Net/BridgeRing`,
`Timing/RuntAck`, and B's own `Cells/OnNetlist` (l.551 `simp` no progress) and
`Cells/OnNetlistTimed` (l.243 `rw`) — these import C's `Net/Fasm/Basic`, whose
definitions (unpatched) are stated with Prelim's constants. No error was an
"ambiguous" name (Bpt's predicted clash did not occur); all are constant
mismatches `Formal.Cells.X` vs `Formal.Core.LutList.X`, which are equal (§1) but
distinct constants for `rw`/`simp`. Hence: one coordinated commit, as A-lutlist2
already said.

Comparison with A's `Wip/LutList2/apply_lutlist2.py`: same name set; A inserts the
`open` after each `namespace Formal.Cells…` line and edits A/C `open Formal.Cells`
lines in place; this probe inserts one top-level `open` after the imports and adds
R5 (Events8Arb, newer than LutList2) and the GLSResolveGen rename. A's version was
not end-state compiled (its note says "results to follow"); this one is.

## 5. The diffs

### 5a. Shard B (`formal/lean/Wip/Bpd/B.patch`)

```diff
--- a/formal/lean/Formal/Cells/AMergeGates.lean
+++ b/formal/lean/Formal/Cells/AMergeGates.lean
@@ -1,4 +1,5 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
+open Formal.Core.LutList
 
 /-!
 # Probe Cm, part 1: every LUT of `bdc_amerge2_0`, `bdc_amerge3_0`, `bdc_muxn3_32`
--- a/formal/lean/Formal/Cells/AMergeSys.lean
+++ b/formal/lean/Formal/Cells/AMergeSys.lean
@@ -1,4 +1,4 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 
 /-!
 # Probe Cm, part 0: a finite speed-independence checker with excitation masks
--- a/formal/lean/Formal/Cells/ArbA0Fork.lean
+++ b/formal/lean/Formal/Cells/ArbA0Fork.lean
@@ -1,4 +1,5 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
+open Formal.Core.LutList
 
 /-!
 # Probe 7g: the A0 isochronic-fork obligation of `bd_arbiter` (H_A0_FORK)
--- a/formal/lean/Formal/Cells/ArbAnalog.lean
+++ b/formal/lean/Formal/Cells/ArbAnalog.lean
@@ -2,7 +2,8 @@
 import Mathlib.Analysis.ODE.ExistUnique
 import Mathlib.Topology.Order.IntermediateValue
 import Mathlib.Analysis.Calculus.MeanValue
-import Formal.Cells.Prelim
+import Formal.Core.LutList
+open Formal.Core.LutList
 
 /-!
 # Track 7c: the arbiter's state node as an analog loop
--- a/formal/lean/Formal/Cells/ArbBinary.lean
+++ b/formal/lean/Formal/Cells/ArbBinary.lean
@@ -1,4 +1,5 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
+open Formal.Core.LutList
 
 /-!
 # Track 7, probe 7a: the arbiter in the binary model (tie and runt)
--- a/formal/lean/Formal/Cells/ArbCornersPin.lean
+++ b/formal/lean/Formal/Cells/ArbCornersPin.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.ArbCorners
 import Formal.Cells.PinAssign
+open Formal.Core.LutList
 
 /-!
 # Probe Bc2: ArbCorners' numeric results redone with the ROUTED pin of every seed
--- a/formal/lean/Formal/Cells/ArbHandover.lean
+++ b/formal/lean/Formal/Cells/ArbHandover.lean
@@ -1,4 +1,5 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
+open Formal.Core.LutList
 
 /-!
 # Probe 7e: the handover-ordering claim and the A0 hold (`cells/rtl/bd_arb.v`)
--- a/formal/lean/Formal/Cells/ArbHeldTimed.lean
+++ b/formal/lean/Formal/Cells/ArbHeldTimed.lean
@@ -1,4 +1,5 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
+open Formal.Core.LutList
 
 /-!
 # Probe 7h: timed exclusion of the HELD `bd_arbiter` (`cells/rtl/bd_arb.v`)
--- a/formal/lean/Formal/Cells/ArbKleene.lean
+++ b/formal/lean/Formal/Cells/ArbKleene.lean
@@ -1,4 +1,5 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
+open Formal.Core.LutList
 
 /-!
 # Probe 7b: the arbiter in Kleene three-valued logic
@@ -46,7 +47,7 @@
 
 namespace Formal.Cells.ArbKleene
 open Formal.Cells
-open Formal.Cells.K3
+open Formal.Core.LutList.K3
 
 /-! ## INITs and cells -/
 
--- a/formal/lean/Formal/Cells/ArbNoWithdraw.lean
+++ b/formal/lean/Formal/Cells/ArbNoWithdraw.lean
@@ -2,6 +2,7 @@
 import Formal.Net.CapstoneWitnessCells
 import Formal.Cells.LinkExact
 import Formal.Cells.OnGcdArbKappaSrv
+open Formal.Core.LutList
 
 /-!
 # Probe Bbare: can a gcd_hw arbiter client withdraw an unacknowledged request?
--- a/formal/lean/Formal/Cells/ArbOverlapPess.lean
+++ b/formal/lean/Formal/Cells/ArbOverlapPess.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.KleenePess
 import Formal.Cells.ArbOverlapRace
+open Formal.Core.LutList
 
 /-!
 # Probe Bov2: can a PESSIMISTIC LUT model explain the arbcell 8% filtered overlap?
--- a/formal/lean/Formal/Cells/ArbOverlapRace.lean
+++ b/formal/lean/Formal/Cells/ArbOverlapRace.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ArbBinary
+open Formal.Core.LutList
 
 /-!
 # Probe Bov: does a digital race trace of `bd_arbcell` explain the 8% overlap?
--- a/formal/lean/Formal/Cells/ArbSettled.lean
+++ b/formal/lean/Formal/Cells/ArbSettled.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ArbNoWithdraw
+open Formal.Core.LutList
 
 /-!
 # Probe Bset: the sharp H_SETTLED of the held `bd_arbiter`, its latency table on gcd_hw, and
--- a/formal/lean/Formal/Cells/Bundling.lean
+++ b/formal/lean/Formal/Cells/Bundling.lean
@@ -1,5 +1,6 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.MuxTree
+open Formal.Core.LutList
 
 /-!
 # Track 6c: matched delay lines (`bd_delay`) and the bundling condition (`bd_link`)
--- a/formal/lean/Formal/Cells/CElemCore.lean
+++ b/formal/lean/Formal/Cells/CElemCore.lean
@@ -1,4 +1,4 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.CElemTiming
 import Formal.Core.Delay.Pure
 import Formal.Core.Delay.Inertial
--- a/formal/lean/Formal/Cells/CElemFn.lean
+++ b/formal/lean/Formal/Cells/CElemFn.lean
@@ -1,4 +1,5 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
+open Formal.Core.LutList
 
 /-!
 # Track 5, probe 5a: the C-elements of `cells/rtl/bd_ce.v`, functional and Kleene
--- a/formal/lean/Formal/Cells/CElemStrict.lean
+++ b/formal/lean/Formal/Cells/CElemStrict.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.CElemFn
 import Formal.Cells.Latch
+open Formal.Core.LutList
 
 /-!
 # The C-element's own-feedback race must be STRICT in a per-pin mux-tree LUT
--- a/formal/lean/Formal/Cells/CElemStrict2.lean
+++ b/formal/lean/Formal/Cells/CElemStrict2.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.CElemStrict
+open Formal.Core.LutList
 
 /-!
 # The strict own-feedback race on every C-element variant, the latch pair, and reset release
--- a/formal/lean/Formal/Cells/CElemTiming.lean
+++ b/formal/lean/Formal/Cells/CElemTiming.lean
@@ -1,4 +1,5 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
+open Formal.Core.LutList
 
 /-!
 # Track 5, probe 5b: timing of the feedback-LUT C-element under bounded delays
--- a/formal/lean/Formal/Cells/CTree.lean
+++ b/formal/lean/Formal/Cells/CTree.lean
@@ -1,4 +1,5 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
+open Formal.Core.LutList
 
 /-!
 # bd_ctree: a tree of C-elements vs a flat N-input C-element (probe 5c)
--- a/formal/lean/Formal/Cells/CTreeTimed.lean
+++ b/formal/lean/Formal/Cells/CTreeTimed.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.CElemTiming
 import Formal.Cells.CTree
+open Formal.Core.LutList
 
 /-!
 # Track 5, probe 5f: timing of `bd_c3`, `bd_c4` and `bd_ctree`
--- a/formal/lean/Formal/Cells/ConstraintsLatchRst.lean
+++ b/formal/lean/Formal/Cells/ConstraintsLatchRst.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.Bundling
 import Formal.Cells.Latch
+open Formal.Core.LutList
 
 /-!
 # Probe P3b: timed theorems for `bd_latch_rst` (cell_constraints entries
--- a/formal/lean/Formal/Cells/ConstraintsMore.lean
+++ b/formal/lean/Formal/Cells/ConstraintsMore.lean
@@ -1,6 +1,7 @@
 import Formal.Cells.Bundling
 import Formal.Cells.LibEndMemMlink
 import Formal.Cells.LinkHandshake
+open Formal.Core.LutList
 
 /-!
 # Probe P3e: H_QFB_FIRST as a timed inequality (`bd_mlink.qfb_first`,
--- a/formal/lean/Formal/Cells/ConstraintsMux.lean
+++ b/formal/lean/Formal/Cells/ConstraintsMux.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.MuxRtzTimed
 import Formal.Cells.Bundling
+open Formal.Core.LutList
 
 /-!
 # Probe P3d: `bd_mux.uya` return-to-zero race (cell_constraints entry `bd_mux.uya_rtz_env`)
--- a/formal/lean/Formal/Cells/ConstraintsSel.lean
+++ b/formal/lean/Formal/Cells/ConstraintsSel.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.FifoFidelity
+open Formal.Core.LutList
 
 /-!
 # Probe P3a: per-pin `H_SEL_ORDER` for `bd_c2`, `bd_c3`, `bd_c4` (cell_constraints entries
--- a/formal/lean/Formal/Cells/ForkData.lean
+++ b/formal/lean/Formal/Cells/ForkData.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.Bundling
 import Formal.Cells.AMergeTimedW
+open Formal.Core.LutList
 
 /-!
 # Probe Bfd: H_FORK_DATA (fork branch data vs request) and H_AMERGE_IDX
--- a/formal/lean/Formal/Cells/KleeneBox.lean
+++ b/formal/lean/Formal/Cells/KleeneBox.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.LibGapLatch
 import Formal.Cells.LibGapMuxN
+open Formal.Core.LutList
 
 /-!
 # KleeneBox: the per-pin box iffs of `bd_steer`, `bd_mux`'s joins, `bdc_muxn`'s selected join and `bd_latch`, with K3 traces on EVERY pin
--- a/formal/lean/Formal/Cells/KleenePess.lean
+++ b/formal/lean/Formal/Cells/KleenePess.lean
@@ -2,6 +2,7 @@
 import Formal.Cells.ArbKleene
 import Formal.Cells.Latch
 import Formal.Cells.KleeneBox
+open Formal.Core.LutList
 
 /-!
 # KleenePess: pessimistic LUT models below H_KLEENE_LUT, and which cell results survive
--- a/formal/lean/Formal/Cells/KleeneWin.lean
+++ b/formal/lean/Formal/Cells/KleeneWin.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.KleeneBox
 import Formal.Cells.CElemStrict
+open Formal.Core.LutList
 
 /-!
 # KleeneWin: per-edge X windows with their own split (no H_X_UNIFORM)
--- a/formal/lean/Formal/Cells/KleeneWinBound.lean
+++ b/formal/lean/Formal/Cells/KleeneWinBound.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.KleeneWin
+open Formal.Core.LutList
 
 /-!
 # KleeneWinBound (probe Bwb): `+W` under H_W_BOUND, sufficient and needed, for every per-edge iff
--- a/formal/lean/Formal/Cells/Latch.lean
+++ b/formal/lean/Formal/Cells/Latch.lean
@@ -1,4 +1,5 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
+open Formal.Core.LutList
 
 /-!
 # Track 6a: the LUT latch `bd_latch` / `bd_latch_rst` (cells/rtl/bd_latch.v)
--- a/formal/lean/Formal/Cells/LibCtlMergeMux.lean
+++ b/formal/lean/Formal/Cells/LibCtlMergeMux.lean
@@ -1,4 +1,5 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
+open Formal.Core.LutList
 
 /-!
 # Lib1: every LUT of `bd_ctl.v`, `bd_merge.v`, `bd_mux.v`, binary and Kleene
--- a/formal/lean/Formal/Cells/LibEndMemMlink.lean
+++ b/formal/lean/Formal/Cells/LibEndMemMlink.lean
@@ -1,5 +1,6 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.MuxTree
+open Formal.Core.LutList
 
 /-!
 # Shard B, probe Lib2: `bd_end.v`, `bd_mem.v`, `bd_mlink.v`, and the parts of
--- a/formal/lean/Formal/Cells/LibGapLatch.lean
+++ b/formal/lean/Formal/Cells/LibGapLatch.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.Latch
 import Formal.Cells.LibGapMux
+open Formal.Core.LutList
 
 /-!
 # LibGapLatch: `bd_latch` setup_data, setup_pulse and hold, per pin, EXACT over the box
--- a/formal/lean/Formal/Cells/LibGapMux.lean
+++ b/formal/lean/Formal/Cells/LibGapMux.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.LibGapSteer
+open Formal.Core.LutList
 
 /-!
 # LibGapMux: `bd_mux`'s select timing at the joins, per pin, sufficient AND necessary
--- a/formal/lean/Formal/Cells/LibGapSteer.lean
+++ b/formal/lean/Formal/Cells/LibGapSteer.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.LibCtlMergeMux
+open Formal.Core.LutList
 
 /-!
 # LibGapSteer: `bd_steer`'s select timing, per pin, sufficient AND necessary
--- a/formal/lean/Formal/Cells/LinkExact.lean
+++ b/formal/lean/Formal/Cells/LinkExact.lean
@@ -2,6 +2,7 @@
 import Formal.Cells.NecessityReset
 import Formal.Cells.CElemFn
 import Formal.Cells.ContractsTrunc
+open Formal.Core.LutList
 
 /-!
 # LinkExact: ONE exact contract for one `bd_link` stage (controller + latch bit + feedbacks)
--- a/formal/lean/Formal/Cells/LinkHandshake.lean
+++ b/formal/lean/Formal/Cells/LinkHandshake.lean
@@ -1,4 +1,5 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
+open Formal.Core.LutList
 
 /-!
 # Track 6, probe 6b: `bd_link` / `bd_pipe` four-phase handshake
--- a/formal/lean/Formal/Cells/LinkTimed.lean
+++ b/formal/lean/Formal/Cells/LinkTimed.lean
@@ -1,6 +1,7 @@
 import Formal.Cells.CElemTiming
 import Formal.Cells.Bundling
 import Formal.Cells.LinkHandshake
+open Formal.Core.LutList
 
 /-!
 # Track 6, probe 6d: one timed `bd_link` stage, controller composed in
--- a/formal/lean/Formal/Cells/MuxN3Timed.lean
+++ b/formal/lean/Formal/Cells/MuxN3Timed.lean
@@ -1,6 +1,7 @@
 import Formal.Cells.OpsTimedMux
 import Formal.Cells.OpsTimed2
 import Formal.Cells.MuxN3
+open Formal.Core.LutList
 
 /-!
 # Shard B probe Mn: timed `bdc_muxn3_32` (gcd_hw's 3-way loop header)
--- a/formal/lean/Formal/Cells/MuxRtzTimed.lean
+++ b/formal/lean/Formal/Cells/MuxRtzTimed.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.CElemTiming
 import Formal.Cells.LibCtlMergeMux
+open Formal.Core.LutList
 
 /-!
 # Probe Lib4: the `bd_mux` return-to-zero race (H_MUX_RTZ) as a timing inequality
--- a/formal/lean/Formal/Cells/MuxTree.lean
+++ b/formal/lean/Formal/Cells/MuxTree.lean
@@ -1,4 +1,5 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
+open Formal.Core.LutList
 
 /-!
 # Fidelity of H_KLEENE_LUT: one Kleene 2:1 mux gives the closure semantics
--- a/formal/lean/Formal/Cells/Necessity2Delay.lean
+++ b/formal/lean/Formal/Cells/Necessity2Delay.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ConstraintsFastFall
+open Formal.Core.LutList
 
 /-!
 # Necessity2Delay: `bd_delay #(.FASTFALL(1))` flush conditions
--- a/formal/lean/Formal/Cells/Necessity2Latch.lean
+++ b/formal/lean/Formal/Cells/Necessity2Latch.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ConstraintsLatchRst
+open Formal.Core.LutList
 
 /-!
 # Necessity2Latch: `bd_latch_rst.setup_pulse` (H_PW) is tight to 1 tick
--- a/formal/lean/Formal/Cells/Necessity3Pipe.lean
+++ b/formal/lean/Formal/Cells/Necessity3Pipe.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.PipeTimedN
+open Formal.Core.LutList
 
 /-!
 # Necessity3Pipe: the data-side `bd_pipe` rows are tight to 1 tick
--- a/formal/lean/Formal/Cells/Necessity5Delay.lean
+++ b/formal/lean/Formal/Cells/Necessity5Delay.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.PipeTimedN
+open Formal.Core.LutList
 
 /-!
 # Necessity5Delay: `bd_delay[FASTRISE].ack_flush` (H_ACK_FLUSH) at the line level
--- a/formal/lean/Formal/Cells/Necessity5Flink.lean
+++ b/formal/lean/Formal/Cells/Necessity5Flink.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ConstraintsMore
+open Formal.Core.LutList
 
 /-!
 # Necessity5Flink: `bd_flink.qfb_first` (H_QFB_FIRST_T) is tight to 1 tick
--- a/formal/lean/Formal/Cells/Necessity5Link.lean
+++ b/formal/lean/Formal/Cells/Necessity5Link.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.RulesKL
+open Formal.Core.LutList
 
 /-!
 # Necessity5Link: `bd_link_dc` corrected rules K' and L' are tight to 1 tick
--- a/formal/lean/Formal/Cells/NecessityMuxRtz.lean
+++ b/formal/lean/Formal/Cells/NecessityMuxRtz.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ConstraintsMux
+open Formal.Core.LutList
 
 /-!
 # NecessityMuxRtz: `bd_mux.uxa_rtz_env` / `uya_rtz_env` are tight to 1 ps
--- a/formal/lean/Formal/Cells/NecessityReset.lean
+++ b/formal/lean/Formal/Cells/NecessityReset.lean
@@ -1,6 +1,7 @@
 import Formal.Cells.LibGapMux
 import Formal.Cells.ResetContract
 import Formal.Cells.Latch
+open Formal.Core.LutList
 
 /-!
 # NecessityReset: the reset-width rows, sufficient AND necessary, per pin
--- a/formal/lean/Formal/Cells/NoRevert.lean
+++ b/formal/lean/Formal/Cells/NoRevert.lean
@@ -2,6 +2,7 @@
 import Formal.Cells.PrelimCore
 import Formal.Net.Prelim
 import Formal.Core.LutTree
+open Formal.Core.LutList
 
 /-!
 # Probe Bng: which delay channels give H_NO_REVERT, and what a LUT needs for it
--- a/formal/lean/Formal/Cells/OnNetlist.lean
+++ b/formal/lean/Formal/Cells/OnNetlist.lean
@@ -1,4 +1,4 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.MuxTree
 import Formal.Cells.CElemFn
 import Formal.Cells.Latch
@@ -9,6 +9,7 @@
 import Formal.Net.FasmLink.S2
 import Formal.Net.FasmLink.S3
 import Formal.Net.FasmLink.S4
+open Formal.Core.LutList
 
 /-!
 # Probe Bn: shard B's cell theorems on the netlist read back from the bits
--- a/formal/lean/Formal/Cells/OnNetlistArb.lean
+++ b/formal/lean/Formal/Cells/OnNetlistArb.lean
@@ -1,4 +1,4 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.CElemTiming
 import Formal.Cells.ArbA0Fork
 import Formal.Cells.ArbHeldTimed
--- a/formal/lean/Formal/Cells/OnNetlistTimed.lean
+++ b/formal/lean/Formal/Cells/OnNetlistTimed.lean
@@ -1,4 +1,4 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.CElemTiming
 import Formal.Cells.Latch
 import Formal.Net.Fasm.Basic
@@ -6,6 +6,7 @@
 import Formal.Net.FasmLink.S2
 import Formal.Net.FasmLink.S3
 import Formal.Net.FasmLink.S4
+open Formal.Core.LutList
 
 /-!
 # Probe Bt: shard B's TIMED cell theorems on the routed bits (link_arb, 4 seeds)
--- a/formal/lean/Formal/Cells/OnNetlistTimed2.lean
+++ b/formal/lean/Formal/Cells/OnNetlistTimed2.lean
@@ -1,4 +1,4 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.CElemTiming
 import Formal.Cells.Latch
 import Formal.Cells.OnNetlistTimed
@@ -9,6 +9,7 @@
 import Formal.Net.FasmLink.S2
 import Formal.Net.FasmLink.S3
 import Formal.Net.FasmLink.S4
+open Formal.Core.LutList
 
 /-!
 # Probe Bt2: finishing the timed bridge on the routed bits (link_arb, 4 seeds)
--- a/formal/lean/Formal/Cells/OpsCounter.lean
+++ b/formal/lean/Formal/Cells/OpsCounter.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.OpsTimed2
+open Formal.Core.LutList
 
 /-!
 # Shard B, probe Lt3: are the operator cells' obligations NECESSARY?
--- a/formal/lean/Formal/Cells/OpsExact.lean
+++ b/formal/lean/Formal/Cells/OpsExact.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.OpsCounter
+open Formal.Core.LutList
 
 /-!
 # Shard B, probe Lt4: exact forms of the operator obligations
--- a/formal/lean/Formal/Cells/OpsExact2.lean
+++ b/formal/lean/Formal/Cells/OpsExact2.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.OpsExact
+open Formal.Core.LutList
 
 /-!
 # Shard B, probe Lt5: the remaining operator exactness items
--- a/formal/lean/Formal/Cells/OpsHold.lean
+++ b/formal/lean/Formal/Cells/OpsHold.lean
@@ -1,6 +1,7 @@
 import Formal.Cells.OpsTimed2
 import Formal.Cells.MuxN3Timed
 import Formal.Cells.LinkTimed
+open Formal.Core.LutList
 
 /-!
 # Shard B Phase 3, probe G3: operator data held until the consumer's ack FALL
--- a/formal/lean/Formal/Cells/OpsTimed2.lean
+++ b/formal/lean/Formal/Cells/OpsTimed2.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.OpsTimedWit
 import Formal.Cells.ConstraintsMux
+open Formal.Core.LutList
 
 /-!
 # Shard B Phase 2, probe Lt2 (part 1): the mux's DATA path, timed
--- a/formal/lean/Formal/Cells/PinAssign.lean
+++ b/formal/lean/Formal/Cells/PinAssign.lean
@@ -1,4 +1,4 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Net.Fasm.CePairS1
 import Formal.Net.Fasm.CePairS2
 import Formal.Net.Fasm.CePairS3
@@ -7,6 +7,7 @@
 import Formal.Net.FasmLink.S2
 import Formal.Net.FasmLink.S3
 import Formal.Net.FasmLink.S4
+open Formal.Core.LutList
 
 /-!
 # Probe Bp: which physical LUT pin carries which logical input (from the bits)
--- a/formal/lean/Formal/Cells/PipeTimed.lean
+++ b/formal/lean/Formal/Cells/PipeTimed.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.LinkTimed
+open Formal.Core.LutList
 
 /-!
 # Track 6, probe 6e: a timed N-stage `bd_pipe` (N = 2 in full)
--- a/formal/lean/Formal/Cells/PipeTimedN.lean
+++ b/formal/lean/Formal/Cells/PipeTimedN.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.PipeTimed
+open Formal.Core.LutList
 
 /-!
 # Track 6, probe 6f: a timed `bd_pipe` with any number of stages `N ≥ 1`
--- a/formal/lean/Formal/Cells/PipeWitness.lean
+++ b/formal/lean/Formal/Cells/PipeWitness.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.PipeTimedN
 import Formal.Cells.PipePerPin
+open Formal.Core.LutList
 
 /-!
 # Track 6, probe 6h: non-degenerate joint witnesses for the timed pipe
--- a/formal/lean/Formal/Cells/PrelimCore.lean
+++ b/formal/lean/Formal/Cells/PrelimCore.lean
@@ -1,6 +1,7 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.CElemTiming
 import Formal.Core.Substrate.Chan
+open Formal.Core.LutList
 
 /-!
 # PrelimCore: every Prelim / CElemTiming notion B's cell files use, against Core
@@ -57,24 +58,24 @@
 
 /-! ## 1. Values -/
 
-theorem k3_eq : Formal.Cells.K3 = Formal.Core.K3 := rfl
-theorem f_eq : Formal.Cells.K3.f = Formal.Core.K3.zero := rfl
-theorem t_eq : Formal.Cells.K3.t = Formal.Core.K3.one := rfl
-theorem x_eq : Formal.Cells.K3.x = Formal.Core.K3.X := rfl
-theorem ofBool_eq : Formal.Cells.K3.ofBool = Formal.Core.K3.ofBool := rfl
-theorem join_eq : Formal.Cells.K3.join = Formal.Core.K3.merge := Formal.Cells.K3.join_eq_merge
-theorem not_eq : Formal.Cells.K3.not = Formal.Core.K3.not := Formal.Cells.K3.not_eq_core
+theorem k3_eq : Formal.Core.LutList.K3 = Formal.Core.K3 := rfl
+theorem f_eq : Formal.Core.LutList.K3.f = Formal.Core.K3.zero := rfl
+theorem t_eq : Formal.Core.LutList.K3.t = Formal.Core.K3.one := rfl
+theorem x_eq : Formal.Core.LutList.K3.x = Formal.Core.K3.X := rfl
+theorem ofBool_eq : Formal.Core.LutList.K3.ofBool = Formal.Core.K3.ofBool := rfl
+theorem join_eq : Formal.Core.LutList.K3.join = Formal.Core.K3.merge := Formal.Core.LutList.K3.join_eq_merge
+theorem not_eq : Formal.Core.LutList.K3.not = Formal.Core.K3.not := Formal.Core.LutList.K3.not_eq_core
 
 /-- B's Kleene 2:1 mux is the node of Core's mux tree `kevalT`. -/
 theorem mux_eq (s a b : Formal.Core.K3) :
-    Formal.Cells.K3.mux s a b = match s with
+    Formal.Core.LutList.K3.mux s a b = match s with
       | .zero => a
       | .one => b
-      | .X => Formal.Core.K3.merge a b := Formal.Cells.mux_eq s a b
+      | .X => Formal.Core.K3.merge a b := Formal.Core.LutList.mux_eq s a b
 
 theorem admits_iff_le (a : Formal.Core.K3) (b : Bool) :
-    Formal.Cells.K3.admits a b = true ↔ Formal.Core.K3.Le a (Formal.Core.K3.ofBool b) :=
-  Formal.Cells.K3.admits_iff_le a b
+    Formal.Core.LutList.K3.admits a b = true ↔ Formal.Core.K3.Le a (Formal.Core.K3.ofBool b) :=
+  Formal.Core.LutList.K3.admits_iff_le a b
 
 /-! ## 2. LUTs on arbitrary lists -/
 
--- a/formal/lean/Formal/Cells/ResetCapstoneWit.lean
+++ b/formal/lean/Formal/Cells/ResetCapstoneWit.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ResetGcdVec2
+open Formal.Core.LutList
 
 /-!
 # Probe Brz (shard B): a non-degenerate witness for gcd_hw's network reset theorems
--- a/formal/lean/Formal/Cells/ResetContract.lean
+++ b/formal/lean/Formal/Cells/ResetContract.lean
@@ -1,8 +1,9 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.CElemTiming
 import Formal.Cells.CTreeTimed
 import Formal.Cells.TernarySound
 import Formal.Cells.TernaryPhases
+open Formal.Core.LutList
 
 /-!
 # Probe Rst (shard B, gcd_hw capstone): the design-level reset contract
--- a/formal/lean/Formal/Cells/ResetGcd.lean
+++ b/formal/lean/Formal/Cells/ResetGcd.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ResetGcdNet
+open Formal.Core.LutList
 
 /-!
 # Probe Rst2 (shard B, gcd_hw capstone): the reset contract on the RTL-level control netlist
--- a/formal/lean/Formal/Cells/ResetGcdNetR5.lean
+++ b/formal/lean/Formal/Cells/ResetGcdNetR5.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ResetGcd
+open Formal.Core.LutList
 
 /-!
 # gcd_hw's control network, regenerated from the SYNTHESIZED netlist (GENERATED)
--- a/formal/lean/Formal/Cells/ResetGcdNetRe.lean
+++ b/formal/lean/Formal/Cells/ResetGcdNetRe.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ResetGcd
+open Formal.Core.LutList
 
 /-!
 # gcd_hw's control network, regenerated from the SYNTHESIZED netlist (GENERATED)
--- a/formal/lean/Formal/Cells/ResetGcdVec.lean
+++ b/formal/lean/Formal/Cells/ResetGcdVec.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.ResetGcdWave
 import Formal.Cells.CElemStrict2
+open Formal.Core.LutList
 
 /-!
 # Probe Brst (shard B): the data vector every reset cell of gcd_hw sees at reset release
--- a/formal/lean/Formal/Cells/ResetGcdVec2.lean
+++ b/formal/lean/Formal/Cells/ResetGcdVec2.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.ResetGcdVec
 import Formal.Cells.LibEndMemMlink
+open Formal.Core.LutList
 
 /-!
 # Probe Bfw (shard B): gcd_hw's per-cell reset model derived from the network run, and the first-wave cells
--- a/formal/lean/Formal/Cells/ResetGcdWave.lean
+++ b/formal/lean/Formal/Cells/ResetGcdWave.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.ResetGcd
 import Formal.Cells.TernaryPhases
+open Formal.Core.LutList
 
 /-!
 # Probe Rst3 (shard B, gcd_hw capstone): from release through the first wave
--- a/formal/lean/Formal/Cells/ResetWitness2.lean
+++ b/formal/lean/Formal/Cells/ResetWitness2.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.ResetCapstone
 import Formal.Cells.ResetWitness2Data
+open Formal.Core.LutList
 
 /-!
 # Probe Bwit (shard B): a moving, varied-delay witness for gcd_hw's reset theorems
--- a/formal/lean/Formal/Cells/RigContract.lean
+++ b/formal/lean/Formal/Cells/RigContract.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ResetContract
+open Formal.Core.LutList
 
 /-!
 # Probe Rig (shard B, gcd_hw capstone): the rig's own obligations
--- a/formal/lean/Formal/Cells/RulesKL.lean
+++ b/formal/lean/Formal/Cells/RulesKL.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.Bundling
+open Formal.Core.LutList
 
 /-!
 # Probe Bk: tighten.py rules K and L (`bd_link_dc`) against a derivation
--- a/formal/lean/Formal/Cells/SelfAuditB2.lean
+++ b/formal/lean/Formal/Cells/SelfAuditB2.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ResetGcdWave
+open Formal.Core.LutList
 /-!
 # Self-audit of shard B (probe Bsa), part 2: a joint witness for the gcd_hw reset/wave chain
 
--- a/formal/lean/Formal/Cells/SelfAuditB5.lean
+++ b/formal/lean/Formal/Cells/SelfAuditB5.lean
@@ -2,6 +2,7 @@
 import Formal.Cells.LibGapMuxN
 import Formal.Cells.LibGapLatch
 import Formal.Cells.NecessityReset
+open Formal.Core.LutList
 /-!
 # Self-audit of shard B (probe Bsa2), part 5: non-degenerate witnesses for the box-exact theorems
 
--- a/formal/lean/Formal/Cells/SelfAuditB6.lean
+++ b/formal/lean/Formal/Cells/SelfAuditB6.lean
@@ -2,6 +2,7 @@
 import Formal.Cells.SelfAuditB6Data
 import Formal.Cells.ResetGcdNetR5
 import Formal.Cells.ResetGcdNetRe
+open Formal.Core.LutList
 
 /-!
 # Self-audit B6 (probe Bsa3): witnesses for shard B's 10-27 files the audit did not cover
--- a/formal/lean/Formal/Cells/TernaryExact.lean
+++ b/formal/lean/Formal/Cells/TernaryExact.lean
@@ -1,6 +1,7 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.TernarySound
 import Formal.Cells.TernaryPhases
+open Formal.Core.LutList
 
 /-!
 # Probe 7l: exactness of two-phase ternary simulation (Algorithms A and B)
--- a/formal/lean/Formal/Cells/TernaryOnBits.lean
+++ b/formal/lean/Formal/Cells/TernaryOnBits.lean
@@ -2,6 +2,7 @@
 import Formal.Cells.TernaryPhases
 import Formal.Cells.TernaryExact
 import Formal.Cells.OnNetlist
+open Formal.Core.LutList
 
 /-!
 # Probe Bx: ternary hazard / settling checker on the whole routed netlist
--- a/formal/lean/Formal/Cells/TernaryOnBits2.lean
+++ b/formal/lean/Formal/Cells/TernaryOnBits2.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.TernaryOnBits
+open Formal.Core.LutList
 
 /-!
 # Probe Bx2: more scenarios, shared O5/O6 reads, and a certificate generator
--- a/formal/lean/Formal/Cells/TernaryPhases.lean
+++ b/formal/lean/Formal/Cells/TernaryPhases.lean
@@ -1,6 +1,7 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.ArbKleene
 import Formal.Cells.TernarySound
+open Formal.Core.LutList
 
 /-!
 # Probe 7i: multi-phase ternary soundness, the remaining 7b scenarios, and a
--- a/formal/lean/Formal/Cells/TernarySound.lean
+++ b/formal/lean/Formal/Cells/TernarySound.lean
@@ -1,6 +1,7 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.MuxTree
 import Formal.Cells.ArbKleene
+open Formal.Core.LutList
 
 /-!
 # Probe 7f: soundness of two-phase ternary simulation (Eichelberger A/B)
--- a/formal/lean/Formal/Cells/ZeroDelayNetPhys.lean
+++ b/formal/lean/Formal/Cells/ZeroDelayNetPhys.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ZeroDelayNet
+open Formal.Core.LutList
 
 /-!
 # ZeroDelayNetPhys: the whole physical link chain refines ONE zero-delay run of C's chain
--- a/formal/lean/Formal/Cells/ZeroDelayNetWit.lean
+++ b/formal/lean/Formal/Cells/ZeroDelayNetWit.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ZeroDelayNetPhys
+open Formal.Core.LutList
 
 /-!
 # ZeroDelayNetWit: non-vacuity of the closed-loop chain refinement
--- a/formal/lean/Formal/Cells/ZeroDelayRefine.lean
+++ b/formal/lean/Formal/Cells/ZeroDelayRefine.lean
@@ -3,6 +3,7 @@
 import Formal.Net.OpsLink
 import Formal.Net.OpsSteer
 import Formal.Net.OpsMux
+open Formal.Core.LutList
 
 /-!
 # ZeroDelayRefine: physical cell traces ↦ C's zero-delay traces (cell half of Br2 / C-8x)
--- a/formal/lean/Formal/Cells/ZeroDelayTok.lean
+++ b/formal/lean/Formal/Cells/ZeroDelayTok.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ZeroDelayNetPhys
+open Formal.Core.LutList
 
 /-!
 # ZeroDelayTok: one `bd_link` stage carrying `k` tokens: the exact cross-token row
--- a/formal/lean/Formal/Cells/ZeroDelayTokChain.lean
+++ b/formal/lean/Formal/Cells/ZeroDelayTokChain.lean
@@ -1,4 +1,5 @@
 import Formal.Cells.ZeroDelayTok
+open Formal.Core.LutList
 
 /-!
 # ZeroDelayTokChain: the closed-loop `bd_link` chain carrying `k` tokens (physical half)
--- a/formal/lean/Formal/Cells/ZeroDelayTokWit.lean
+++ b/formal/lean/Formal/Cells/ZeroDelayTokWit.lean
@@ -1,5 +1,6 @@
 import Formal.Cells.ZeroDelayTokChain
 import Formal.Cells.ZeroDelayNetWit
+open Formal.Core.LutList
 
 /-!
 # ZeroDelayTokWit: non-vacuity of the `k`-token closed-loop chain (two stages, two tokens)
--- a/formal/lean/Formal/Cells/Prelim.lean
+++ /dev/null
@@ -1,182 +0,0 @@
-import Formal.Core.Kleene
-import Formal.Core.Lut
-
-/-!
-# Shard B preliminaries: the cell proofs' names for Core's values and LUTs
-
-Since the Phase-1 port (formal/notes/B-port-core.md) this file defines nothing
-of its own semantics: every name is Core's object, or a list-indexed view of
-it whose agreement with Core is proved here.
-
-* `K3` IS `Formal.Core.K3` (an `abbrev`). `K3.f`, `K3.t`, `K3.x` are
-  `@[match_pattern]` names for Core's constructors `zero`, `one`, `X`, kept so
-  that the cell files read as before. `K3.ofBool` is Core's;
-  `K3.join` and `K3.not` are Core's `K3.merge` and `K3.not` (`join_eq_merge`,
-  `not_eq_core`, both `rfl`; separate constants only so that existing
-  `simp [K3.join]` calls keep unfolding them).
-* `lutB init ins`   binary LUT: the INIT bit addressed by the inputs, I0 = LSB.
-  `lutB_ofFn`: on `List.ofFn x` it is Core's `Lut.eval` (any width `k`).
-* `muxTree g ins`   the Kleene mux tree over the table `g`, I0 at the root.
-  `muxTree_ofFn`: on `List.ofFn v` it is Core's `kevalT` (the mux tree that
-  defines `Lut.keval`), node for node.
-* `lutK init ins := muxTree init.testBit ins`   Kleene LUT = Core's mux-tree
-  semantics. `lutK_ofFn`: on `List.ofFn v` it is `Lut.keval`; with
-  `Lut.keval_eq_kevalSpec` it is also the closure specification ("t/f if every
-  INIT entry consistent with the inputs is 1/0, else x"). That closure form,
-  which was this file's definition of `lutK` before the port, is the theorem
-  `MuxTree.lutK_eq_closure` (file `MuxTree.lean`).
-  Hypothesis **H_KLEENE_LUT**: a 7-series LUT is a pass-transistor mux tree,
-  and a mux whose select is intermediate passes a definite value when both
-  data legs carry it, and an intermediate value otherwise (`K3.mux`).
-  Test: GLS with an X-driven select pin and equal data, or board injection of a
-  slow edge on one LUT pin with the other INIT legs equal.
-* LUT6_2: `O6 = INIT[I5..I0]`, `O5 = INIT[0,I4..I0]` (lower 32 bits).
--/
-
-namespace Formal.Cells
-
-/-- Kleene three-valued signal level: Core's `K3`. `x` = not a valid logic level. -/
-abbrev K3 := Formal.Core.K3
-
-namespace K3
-/-- Logic 0 (Core `K3.zero`). -/
-@[match_pattern, reducible] def f : K3 := Formal.Core.K3.zero
-/-- Logic 1 (Core `K3.one`). -/
-@[match_pattern, reducible] def t : K3 := Formal.Core.K3.one
-/-- Not a valid level (Core `K3.X`). -/
-@[match_pattern, reducible] def x : K3 := Formal.Core.K3.X
-
-/-- Core's embedding of `Bool`. -/
-abbrev ofBool : Bool → K3 := Formal.Core.K3.ofBool
-
-/-- Join of two readings of the same node: equal values stay, else `x`.
-This is Core's `K3.merge` (the glb in the information order), by `rfl`
-(`join_eq_merge`); it is kept as its own constant so that `simp [K3.join]`
-unfolds it to the `if`. -/
-def join (a b : K3) : K3 := if a = b then a else x
-
-theorem join_eq_merge : join = Formal.Core.K3.merge := rfl
-
-/-- Kleene 2:1 mux (the per-mux form of H_KLEENE_LUT): select `f` takes `a`,
-`t` takes `b`, `x` passes a value only when both legs carry it. This is the
-mux that Core's `kevalT` inlines at every node. -/
-def mux (s a b : K3) : K3 :=
-  match s with
-  | f => a
-  | t => b
-  | x => join a b
-
-/-- Strong-Kleene negation; Core's `K3.not` by `rfl` (`not_eq_core`). -/
-def not : K3 → K3
-  | f => t
-  | t => f
-  | x => x
-
-theorem not_eq_core : not = Formal.Core.K3.not := rfl
-
-/-- Is a Bool consistent with a K3 reading? (Core: `a ⊑ ofBool b`, `admits_iff_le`.) -/
-def admits : K3 → Bool → Bool
-  | f, b => !b
-  | t, b => b
-  | x, _ => true
-
-theorem admits_iff_le (a : K3) (b : Bool) :
-    admits a b = true ↔ Formal.Core.K3.Le a (Formal.Core.K3.ofBool b) := by
-  cases a <;> cases b <;> decide
-end K3
-
-/-- Address of a LUT entry: `ins` is `[I0, I1, ...]`, I0 the least significant bit. -/
-def lutIdx : List Bool → Nat
-  | [] => 0
-  | b :: bs => (if b then 1 else 0) + 2 * lutIdx bs
-
-/-- Binary LUT. -/
-def lutB (init : Nat) (ins : List Bool) : Bool := init.testBit (lutIdx ins)
-
-/-- All Boolean vectors consistent with a Kleene input vector. -/
-def completions : List K3 → List (List Bool)
-  | [] => [[]]
-  | a :: as =>
-    let rest := completions as
-    (if K3.admits a false then rest.map (false :: ·) else []) ++
-    (if K3.admits a true then rest.map (true :: ·) else [])
-
-/-- A mux tree over the table `g` (entry `j` = `g j`), the head input at the
-root: it selects between the even entries (head = 0) and the odd ones, each
-an identical tree over the remaining inputs. The physical I0..I5 order of the
-silicon tree is not known; this is one order (the research GLS order, and the
-order of Core's `kevalT`). -/
-def muxTree : (g : Nat → Bool) → (ins : List K3) → K3
-  | g, [] => K3.ofBool (g 0)
-  | g, s :: ss => K3.mux s (muxTree (fun j => g (2 * j)) ss) (muxTree (fun j => g (2 * j + 1)) ss)
-
-/-- Kleene LUT (hypothesis H_KLEENE_LUT): Core's mux-tree semantics. -/
-def lutK (init : Nat) (ins : List K3) : K3 := muxTree init.testBit ins
-
-/-! The LUT6_2 outputs. Pins listed `[I0, I1, I2, I3, I4, I5]`. -/
-def o6B (init : Nat) (ins : List Bool) : Bool := lutB init ins
-def o5B (init : Nat) (ins : List Bool) : Bool := lutB (init % 2 ^ 32) (ins.take 5)
-def o6K (init : Nat) (ins : List K3) : K3 := lutK init ins
-def o5K (init : Nat) (ins : List K3) : K3 := lutK (init % 2 ^ 32) (ins.take 5)
-
-/-! ## Agreement with Core (`Formal.Core.Lut`)
-
-Inputs as a Core vector `x : Fin k → _` (`x 0` = pin I0) are the list
-`List.ofFn x`; a Core `Lut k` with INIT `L.init : BitVec (2^k)` is the number
-`L.init.toNat`. -/
-
-section CoreAgree
-open Formal.Core
-
-theorem mux_eq (s a b : K3) :
-    K3.mux s a b = match s with
-      | .zero => a
-      | .one => b
-      | .X => Formal.Core.K3.merge a b := by
-  cases s <;> rfl
-
-theorem lutIdx_ofFn : ∀ {k : Nat} (x : Fin k → Bool), lutIdx (List.ofFn x) = addr x
-  | 0, _ => rfl
-  | k + 1, x => by
-      rw [List.ofFn_succ, lutIdx, addr, lutIdx_ofFn]
-      cases x 0 <;> rfl
-
-theorem entry_eq_testBit {k : Nat} (L : Lut k) (a : Nat) : L.entry a = L.init.toNat.testBit a :=
-  (BitVec.testBit_toNat L.init).symm
-
-/-- `lutB` on an input vector is Core's `Lut.eval`. -/
-theorem lutB_ofFn {k : Nat} (L : Lut k) (x : Fin k → Bool) :
-    lutB L.init.toNat (List.ofFn x) = L.eval x := by
-  rw [lutB, lutIdx_ofFn, Lut.eval, entry_eq_testBit]
-
-/-- `muxTree` on an input vector is Core's mux tree `kevalT`, for any table. -/
-theorem muxTree_ofFn : ∀ (k : Nat) (g : Nat → Bool) (v : Fin k → K3),
-    muxTree g (List.ofFn v) = kevalT k g v
-  | 0, _, _ => rfl
-  | k + 1, g, v => by
-      rw [List.ofFn_succ, muxTree, muxTree_ofFn k, muxTree_ofFn k]
-      rw [kevalT, mux_eq]
-      cases v 0 <;> rfl
-
-theorem muxTree_congr : ∀ (g g' : Nat → Bool) (ins : List K3), (∀ j, g j = g' j) →
-    muxTree g ins = muxTree g' ins
-  | g, g', [], h => by simp [muxTree, h 0]
-  | g, g', s :: ss, h => by
-      simp only [muxTree]
-      rw [muxTree_congr _ (fun j => g' (2 * j)) ss (fun j => h _),
-        muxTree_congr _ (fun j => g' (2 * j + 1)) ss (fun j => h _)]
-
-/-- `lutK` on an input vector is Core's `Lut.keval`. -/
-theorem lutK_ofFn {k : Nat} (L : Lut k) (v : Fin k → K3) :
-    lutK L.init.toNat (List.ofFn v) = L.keval v := by
-  rw [lutK, muxTree_ofFn, Lut.keval]
-  exact (congrArg (fun g => kevalT k g v) (funext (entry_eq_testBit L))).symm
-
-/-- `lutK` on an input vector is Core's specification `Lut.kevalSpec`. -/
-theorem lutK_ofFn_spec {k : Nat} (L : Lut k) (v : Fin k → K3) :
-    lutK L.init.toNat (List.ofFn v) = L.kevalSpec v := by
-  rw [lutK_ofFn, Lut.keval_eq_kevalSpec]
-
-end CoreAgree
-
-end Formal.Cells
```

### 5b. Shards A and C (`formal/lean/Wip/Bpd/AC.patch`)

```diff
--- a/formal/lean/Formal/Core/Bridge.lean
+++ b/formal/lean/Formal/Core/Bridge.lean
@@ -2,7 +2,7 @@
 import Formal.Core.Lut
 import Formal.Core.LutTree
 import Formal.Core.Ternary
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.MuxTree
 
 /-!
@@ -24,7 +24,7 @@
 | Kleene (canonical) | `Formal.Core.K3` | `zero one X` | `K3.merge`; mux `cmux` (defined here) |
 | LutTree | `Formal.Core.LutTree.K3` | `zero one X` | `LutTree.kmux` |
 | Ternary | `Formal.Core.Ternary.K3` | `zero one X` | `K3.meet`, `K3.sel` |
-| Cells.Prelim (shard B) | `Formal.Cells.K3` | `f t x` | `K3.join`, `K3.mux` |
+| Cells.Prelim (shard B) | `Formal.Core.LutList.K3` | `f t x` | `K3.join`, `K3.mux` |
 
 For each: `toX : Core.K3 → _`, `ofX`, both inverse laws (packaged as a
 `K3Iso`), preservation of `ofBool`, of the information order (Prelim has none:
@@ -93,7 +93,7 @@
 /-- Ternary's local copy. -/
 abbrev TK := Formal.Core.Ternary.K3
 /-- Shard B's (Cells.Prelim) copy. -/
-abbrev BK := Formal.Cells.K3
+abbrev BK := Formal.Core.LutList.K3
 
 /-- An explicit bijection between the canonical `K3` and a local copy. -/
 structure K3Iso (α : Type) where
@@ -200,23 +200,23 @@
 
 def isoCells : K3Iso BK := ⟨toCells, ofCells, ofCells_toCells, toCells_ofCells⟩
 
-@[simp] theorem toCells_ofBool (b : Bool) : toCells (K3.ofBool b) = Formal.Cells.K3.ofBool b := by
+@[simp] theorem toCells_ofBool (b : Bool) : toCells (K3.ofBool b) = Formal.Core.LutList.K3.ofBool b := by
   cases b <;> rfl
 
 /-- Prelim has no information order; its `admits a b` is "`b` is a Boolean
 refinement of `a`", i.e. Core's `a ⊑ ofBool b`. -/
 theorem toCells_admits (a : CK) (b : Bool) :
-    Formal.Cells.K3.admits (toCells a) b = true ↔ K3.Le a (K3.ofBool b) := by
+    Formal.Core.LutList.K3.admits (toCells a) b = true ↔ K3.Le a (K3.ofBool b) := by
   cases a <;> cases b <;> decide
 
-theorem toCells_merge (a b : CK) : toCells (K3.merge a b) = Formal.Cells.K3.join (toCells a) (toCells b) := by
+theorem toCells_merge (a b : CK) : toCells (K3.merge a b) = Formal.Core.LutList.K3.join (toCells a) (toCells b) := by
   cases a <;> cases b <;> rfl
 
 theorem toCells_cmux (s a b : CK) :
-    toCells (cmux s a b) = Formal.Cells.K3.mux (toCells s) (toCells a) (toCells b) := by
+    toCells (cmux s a b) = Formal.Core.LutList.K3.mux (toCells s) (toCells a) (toCells b) := by
   cases s <;> cases a <;> cases b <;> rfl
 
-theorem toCells_not (a : CK) : toCells (K3.not a) = Formal.Cells.K3.not (toCells a) := by
+theorem toCells_not (a : CK) : toCells (K3.not a) = Formal.Core.LutList.K3.not (toCells a) := by
   cases a <;> rfl
 
 end Cells
@@ -272,9 +272,9 @@
   | [] => 0
   | b :: w => b.toNat + 2 * lsbAddr w
 
-theorem lsbAddr_eq_lutIdx : ∀ w : List Bool, lsbAddr w = Formal.Cells.lutIdx w
+theorem lsbAddr_eq_lutIdx : ∀ w : List Bool, lsbAddr w = Formal.Core.LutList.lutIdx w
   | [] => rfl
-  | b :: w => by cases b <;> simp [lsbAddr, Formal.Cells.lutIdx, lsbAddr_eq_lutIdx w]
+  | b :: w => by cases b <;> simp [lsbAddr, Formal.Core.LutList.lutIdx, lsbAddr_eq_lutIdx w]
 
 theorem lsbAddr_ofFn : ∀ {k : Nat} (x : Fin k → Bool), lsbAddr (List.ofFn x) = addr x
   | 0, _ => rfl
@@ -432,31 +432,31 @@
 /-! ### Shard B's Cells.Prelim (`muxTree`, `lutK`) -/
 
 theorem cells_muxTree_eq_kevalT : ∀ (k : Nat) (t : Nat → Bool) (v : Fin k → CK),
-    Formal.Cells.muxTree t (List.ofFn (fun i => toCells (v i))) = toCells (kevalT k t v)
-  | 0, t, v => by simp [Formal.Cells.muxTree, kevalT]
+    Formal.Core.LutList.muxTree t (List.ofFn (fun i => toCells (v i))) = toCells (kevalT k t v)
+  | 0, t, v => by simp [Formal.Core.LutList.muxTree, kevalT]
   | k + 1, t, v => by
       rw [kevalT_succ, toCells_cmux, ← cells_muxTree_eq_kevalT k, ← cells_muxTree_eq_kevalT k,
         List.ofFn_succ]
       rfl
 
 theorem cells_muxTree_eq_keval {k : Nat} (L : Lut k) (v : Fin k → CK) :
-    Formal.Cells.muxTree L.init.toNat.testBit (List.ofFn (fun i => toCells (v i))) =
+    Formal.Core.LutList.muxTree L.init.toNat.testBit (List.ofFn (fun i => toCells (v i))) =
       toCells (L.keval v) :=
   cells_muxTree_eq_kevalT k L.entry v
 
 /-- **Shard B's closure semantics `lutK` (hypothesis H_KLEENE_LUT) = Core `keval`
 = Core `kevalSpec`.** -/
 theorem cells_lutK_eq_keval {k : Nat} (L : Lut k) (v : Fin k → CK) :
-    Formal.Cells.lutK L.init.toNat (List.ofFn (fun i => toCells (v i))) = toCells (L.keval v) := by
+    Formal.Core.LutList.lutK L.init.toNat (List.ofFn (fun i => toCells (v i))) = toCells (L.keval v) := by
   rw [← Formal.Cells.MuxTree.muxTree_eq_lutK, cells_muxTree_eq_keval]
 
 theorem cells_lutK_eq_kevalSpec {k : Nat} (L : Lut k) (v : Fin k → CK) :
-    Formal.Cells.lutK L.init.toNat (List.ofFn (fun i => toCells (v i))) = toCells (L.kevalSpec v) := by
+    Formal.Core.LutList.lutK L.init.toNat (List.ofFn (fun i => toCells (v i))) = toCells (L.kevalSpec v) := by
   rw [cells_lutK_eq_keval, Lut.keval_eq_kevalSpec]
 
 theorem cells_lutB_eq_eval {k : Nat} (L : Lut k) (x : Fin k → Bool) :
-    Formal.Cells.lutB L.init.toNat (List.ofFn x) = L.eval x := by
-  simp [Formal.Cells.lutB, ← lsbAddr_eq_lutIdx, lsbAddr_ofFn, Lut.eval, entry_eq_testBit]
+    Formal.Core.LutList.lutB L.init.toNat (List.ofFn x) = L.eval x := by
+  simp [Formal.Core.LutList.lutB, ← lsbAddr_eq_lutIdx, lsbAddr_ofFn, Lut.eval, entry_eq_testBit]
 
 /-! ### LUT6_2 `O5` -/
 
--- a/formal/lean/Formal/Core/Delay/GLSResolveGen.lean
+++ b/formal/lean/Formal/Core/Delay/GLSResolveGen.lean
@@ -534,7 +534,7 @@
 /-- The fid mux tree and B's `o6B` agree on the held node (B's `ArbHandover.held_q_eqn`). -/
 theorem fArb_eq_B (r1 r2 q rst a0 : Bool) :
     fArb r1 r2 q rst a0 =
-      Formal.Cells.o6B Formal.Cells.ArbHandover.INIT_HELD [r1, r2, q, rst, a0, true] := by
+      Formal.Core.LutList.o6B Formal.Cells.ArbHandover.INIT_HELD [r1, r2, q, rst, a0, true] := by
   rw [fArb_eq, Formal.Cells.ArbHandover.held_q_eqn]
 
 def arbF (r1 r2 rst a0 : Sig) : Nat → Bool → Bool := fun t q => fArb (r1 t) (r2 t) q (rst t) (a0 t)
--- a/formal/lean/Formal/Core/XAudit/Events8Arb.lean
+++ b/formal/lean/Formal/Core/XAudit/Events8Arb.lean
@@ -37,7 +37,7 @@
 
 open Formal.Core.TraceDiscrete (Sig Warp Mono)
 open Formal.Core.XAudit.Events2 (cel)
-open Formal.Cells (o5B o6B)
+open Formal.Core.LutList (o5B o6B)
 open Formal.Cells.ArbBinary (ARB_ST GRANT)
 
 /-! ## 1. The real cell, from its INITs -/
--- a/formal/lean/Formal/Gen/PrelimSem.lean
+++ b/formal/lean/Formal/Gen/PrelimSem.lean
@@ -9,7 +9,7 @@
 `Formal.Gen.Netlist` reads every netlist with shard A's Core semantics
 (`boolSem` = `Lut.eval`, `kleeneSem` = `Lut.keval` on `Formal.Core.K3`). Shard
 B's hand transcriptions (`CElemFn.c2K`, `ArbKleene.g1K`, `Latch`, ...) are
-still valued in Prelim's `Formal.Cells.K3`, so the `Proofs*` theorems that say
+still valued in Prelim's `Formal.Core.LutList.K3`, so the `Proofs*` theorems that say
 "generated gate = B's Kleene function" are stated with `kleeneSemP` below,
 which is the same interpreter with Prelim's `lutK`. They keep their exact
 pre-port statements. When B ports to Core, replace `kleeneSemP` by
@@ -26,19 +26,19 @@
 open Formal.Net.CoreLut Formal.Net.CoreLutPrelim
 
 /-- Decidability of `∀` over Prelim's `K3` (Prelim has none). -/
-instance K3.decForall {P : Formal.Cells.K3 → Prop} [DecidablePred P] : Decidable (∀ k, P k) :=
+instance K3.decForall {P : Formal.Core.LutList.K3 → Prop} [DecidablePred P] : Decidable (∀ k, P k) :=
   if h : P .f ∧ P .t ∧ P .x then
     isTrue (fun k => by cases k <;> simp_all)
   else
     isFalse (fun H => h ⟨H _, H _, H _⟩)
 
 /-- Kleene reading with shard B's Prelim `lutK` (pre-port `kleeneSem`). -/
-def kleeneSemP : Sem Formal.Cells.K3 := ⟨Formal.Cells.lutK, Formal.Cells.K3.ofBool⟩
+def kleeneSemP : Sem Formal.Core.LutList.K3 := ⟨Formal.Core.LutList.lutK, Formal.Core.LutList.K3.ofBool⟩
 
 /-- Binary reading with Prelim's `lutB`. It IS `boolSem` (`boolSem_eq_boolSemP`,
 `Bool` is shared), so a theorem about one is a theorem about the other; it is
 only here so that proofs by `rfl` against B's `lutB`-valued lemmas keep working. -/
-def boolSemP : Sem Bool := ⟨Formal.Cells.lutB, id⟩
+def boolSemP : Sem Bool := ⟨Formal.Core.LutList.lutB, id⟩
 
 theorem boolSem_eq_boolSemP : boolSem = boolSemP := by
   unfold boolSem boolSemP
@@ -55,16 +55,16 @@
 
 /-- `prim_tables` in Prelim's `lutB`, from the Core statement. -/
 theorem prim_tables_prelim :
-    (∀ a b s : Bool, Formal.Cells.lutB MUX_INIT [a, b, s] = (if s then b else a)) ∧
-    (∀ a b : Bool, Formal.Cells.lutB OR2_INIT [a, b] = (a || b)) ∧
-    (∀ a : Bool, Formal.Cells.lutB NOT_INIT [a] = !a) ∧
-    (∀ a b : Bool, Formal.Cells.lutB XOR2_INIT [a, b] = (a ^^ b)) := by
+    (∀ a b s : Bool, Formal.Core.LutList.lutB MUX_INIT [a, b, s] = (if s then b else a)) ∧
+    (∀ a b : Bool, Formal.Core.LutList.lutB OR2_INIT [a, b] = (a || b)) ∧
+    (∀ a : Bool, Formal.Core.LutList.lutB NOT_INIT [a] = !a) ∧
+    (∀ a b : Bool, Formal.Core.LutList.lutB XOR2_INIT [a, b] = (a ^^ b)) := by
   simp only [lutB_eq_evalL]
   exact ⟨prim_tables.1, prim_tables.2.1, prim_tables.2.2.1, prim_tables.2.2.2.1⟩
 
 /-- `mux_kleene` in Prelim's terms (`lutK`, `K3.mux`), from the Core statement. -/
-theorem mux_kleene_prelim : ∀ a b s : Formal.Cells.K3,
-    Formal.Cells.lutK MUX_INIT [a, b, s] = Formal.Cells.K3.mux s a b := by
+theorem mux_kleene_prelim : ∀ a b s : Formal.Core.LutList.K3,
+    Formal.Core.LutList.lutK MUX_INIT [a, b, s] = Formal.Core.LutList.K3.mux s a b := by
   intro a b s
   have h := lutK_eq_kevalL MUX_INIT [ofP a, ofP b, ofP s]
   simp only [List.map, toP_ofP] at h
@@ -72,11 +72,11 @@
   simp
 
 /-- Pre-port form of `ProofsPrims.prims_muxf_kleene` (Prelim `K3`, `K3.mux`). -/
-theorem prims_muxf_kleene_prelim : ∀ a b s : Formal.Cells.K3,
+theorem prims_muxf_kleene_prelim : ∀ a b s : Formal.Core.LutList.K3,
     Cells.prims_muxf8.gateN kleeneSemP "u0" .O [("l[0]", a), ("l[1]", b), ("sel[0]", s)] =
-        some (Formal.Cells.K3.mux s a b) ∧
+        some (Formal.Core.LutList.K3.mux s a b) ∧
     Cells.prims_muxf8.gateN kleeneSemP "u2" .O [("m0", a), ("m1", b), ("sel[1]", s)] =
-        some (Formal.Cells.K3.mux s a b) := by
+        some (Formal.Core.LutList.K3.mux s a b) := by
   decide +kernel
 
 end Formal.Gen
--- a/formal/lean/Formal/Gen/ProofsArb.lean
+++ b/formal/lean/Formal/Gen/ProofsArb.lean
@@ -8,6 +8,7 @@
 import Formal.Cells.ArbA0Fork
 import Formal.Core.Lut
 import Formal.Core.LutCells
+open Formal.Core.LutList
 
 /-!
 # 11d: the generated arbiter (`bd_arb.v`)
--- a/formal/lean/Formal/Gen/ProofsCE.lean
+++ b/formal/lean/Formal/Gen/ProofsCE.lean
@@ -5,6 +5,7 @@
 import Formal.Cells.CElemTiming
 import Formal.Core.Lut
 import Formal.Core.LutCells
+open Formal.Core.LutList
 
 /-!
 # 11d: generated C-elements (`bd_ce.v`), C-trees, fork and join (`bd_ctl.v`)
--- a/formal/lean/Formal/Gen/ProofsCtl.lean
+++ b/formal/lean/Formal/Gen/ProofsCtl.lean
@@ -3,6 +3,7 @@
 import Formal.Cells.LibCtlMergeMux
 import Formal.Core.Lut
 import Formal.Core.LutCells
+open Formal.Core.LutList
 
 /-!
 # 11d: generated steer, protocol converters, merge and mux (`bd_ctl.v`, `bd_merge.v`, `bd_mux.v`)
--- a/formal/lean/Formal/Gen/ProofsLatch.lean
+++ b/formal/lean/Formal/Gen/ProofsLatch.lean
@@ -5,6 +5,7 @@
 import Formal.Cells.Bundling
 import Formal.Core.Lut
 import Formal.Core.LutCells
+open Formal.Core.LutList
 
 /-!
 # 11d: generated latches, delay lines and the data mux (`bd_latch.v`)
--- a/formal/lean/Formal/Gen/ProofsLink.lean
+++ b/formal/lean/Formal/Gen/ProofsLink.lean
@@ -4,6 +4,7 @@
 import Formal.Cells.Latch
 import Formal.Cells.LinkHandshake
 import Formal.Cells.Bundling
+open Formal.Core.LutList
 
 /-!
 # 11d: generated links and pipes (`bd_link.v`)
--- a/formal/lean/Formal/Net/BridgeRing.lean
+++ b/formal/lean/Formal/Net/BridgeRing.lean
@@ -1,5 +1,6 @@
 import Formal.Net.Bridge
 import Formal.Net.Ring
+open Formal.Core.LutList
 
 /-!
 # Probe 8d: the ring theorems of probe 9a, for timed traces
@@ -190,10 +191,10 @@
 
 open Formal.Cells in
 /-- Pin position along its own transition from `v`: `0 = v`, `1 = X`, `2 = !v`. -/
-def pos (v : Bool) : Nat → Formal.Cells.K3
-  | 0 => Formal.Cells.K3.ofBool v
+def pos (v : Bool) : Nat → Formal.Core.LutList.K3
+  | 0 => Formal.Core.LutList.K3.ofBool v
   | 1 => .x
-  | _ => Formal.Cells.K3.ofBool (!v)
+  | _ => Formal.Core.LutList.K3.ofBool (!v)
 
 open Formal.Cells Formal.Cells.CElemFn in
 set_option synthInstance.maxSize 4096 in
--- a/formal/lean/Formal/Net/CoreLutPrelim.lean
+++ b/formal/lean/Formal/Net/CoreLutPrelim.lean
@@ -1,5 +1,5 @@
 import Formal.Net.CoreLut
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.MuxTree
 
 /-!
@@ -26,7 +26,7 @@
 open Formal.Net.CoreLut
 
 abbrev CK := Formal.Core.K3
-abbrev PK := Formal.Cells.K3
+abbrev PK := Formal.Core.LutList.K3
 
 def toP : CK → PK
   | .zero => .f
@@ -41,46 +41,46 @@
 @[simp] theorem toP_ofP (a : PK) : toP (ofP a) = a := by cases a <;> rfl
 @[simp] theorem ofP_toP (a : CK) : ofP (toP a) = a := by cases a <;> rfl
 
-@[simp] theorem toP_ofBool (b : Bool) : toP (Formal.Core.K3.ofBool b) = Formal.Cells.K3.ofBool b := by
+@[simp] theorem toP_ofBool (b : Bool) : toP (Formal.Core.K3.ofBool b) = Formal.Core.LutList.K3.ofBool b := by
   cases b <;> rfl
 
-theorem toP_merge (a b : CK) : toP (Formal.Core.K3.merge a b) = Formal.Cells.K3.join (toP a) (toP b) := by
+theorem toP_merge (a b : CK) : toP (Formal.Core.K3.merge a b) = Formal.Core.LutList.K3.join (toP a) (toP b) := by
   cases a <;> cases b <;> rfl
 
-theorem toP_kmux (s a b : CK) : toP (kmux s a b) = Formal.Cells.K3.mux (toP s) (toP a) (toP b) := by
+theorem toP_kmux (s a b : CK) : toP (kmux s a b) = Formal.Core.LutList.K3.mux (toP s) (toP a) (toP b) := by
   cases s <;> cases a <;> cases b <;> rfl
 
-theorem lutIdx_eq_lsbIdx : ∀ w : List Bool, Formal.Cells.lutIdx w = lsbIdx w
+theorem lutIdx_eq_lsbIdx : ∀ w : List Bool, Formal.Core.LutList.lutIdx w = lsbIdx w
   | [] => rfl
-  | b :: w => by cases b <;> simp [Formal.Cells.lutIdx, lsbIdx, lutIdx_eq_lsbIdx w]
+  | b :: w => by cases b <;> simp [Formal.Core.LutList.lutIdx, lsbIdx, lutIdx_eq_lsbIdx w]
 
 /-- **Boolean: Prelim's `lutB` is Core's `Lut.eval`.** -/
-theorem lutB_eq_evalL (init : Nat) (ins : List Bool) : Formal.Cells.lutB init ins = evalL init ins := by
-  rw [evalL_eq_testBit, Formal.Cells.lutB, lutIdx_eq_lsbIdx]
+theorem lutB_eq_evalL (init : Nat) (ins : List Bool) : Formal.Core.LutList.lutB init ins = evalL init ins := by
+  rw [evalL_eq_testBit, Formal.Core.LutList.lutB, lutIdx_eq_lsbIdx]
 
 theorem o6B_eq_o6L (init : Nat) (ins : List Bool) (h : ins.length = 6) :
-    Formal.Cells.o6B init ins = o6L init ins := by
-  rw [o6L_eq_evalL _ _ h, Formal.Cells.o6B, lutB_eq_evalL]
+    Formal.Core.LutList.o6B init ins = o6L init ins := by
+  rw [o6L_eq_evalL _ _ h, Formal.Core.LutList.o6B, lutB_eq_evalL]
 
 theorem o5B_eq_o5L (init : Nat) (ins : List Bool) (h : ins.length = 6) :
-    Formal.Cells.o5B init ins = o5L init ins := by
-  rw [o5L_eq_evalL _ _ h, Formal.Cells.o5B, lutB_eq_evalL]
+    Formal.Core.LutList.o5B init ins = o5L init ins := by
+  rw [o5L_eq_evalL _ _ h, Formal.Core.LutList.o5B, lutB_eq_evalL]
 
 theorem muxTree_eq_kevalTL : ∀ (t : Nat → Bool) (ins : List CK),
-    Formal.Cells.muxTree t (ins.map toP) = toP (kevalTL t ins)
-  | t, [] => by simp [Formal.Cells.muxTree, kevalTL_nil]
+    Formal.Core.LutList.muxTree t (ins.map toP) = toP (kevalTL t ins)
+  | t, [] => by simp [Formal.Core.LutList.muxTree, kevalTL_nil]
   | t, a :: as => by
       rw [kevalTL_cons, toP_kmux, ← muxTree_eq_kevalTL _ as, ← muxTree_eq_kevalTL _ as]
       rfl
 
 /-- **Kleene (H_KLEENE_LUT): Prelim's closure `lutK` is Core's `Lut.keval`.** -/
 theorem lutK_eq_kevalL (init : Nat) (ins : List CK) :
-    Formal.Cells.lutK init (ins.map toP) = toP (kevalL init ins) := by
+    Formal.Core.LutList.lutK init (ins.map toP) = toP (kevalL init ins) := by
   rw [← Formal.Cells.MuxTree.muxTree_eq_lutK, muxTree_eq_kevalTL, kevalL_eq_kevalTL]
 
 /-- The same, for a Prelim pin list. -/
 theorem lutK_eq_kevalL' (init : Nat) (ins : List PK) :
-    Formal.Cells.lutK init ins = toP (kevalL init (ins.map ofP)) := by
+    Formal.Core.LutList.lutK init ins = toP (kevalL init (ins.map ofP)) := by
   rw [← lutK_eq_kevalL, List.map_map]
   congr 1
   conv => lhs; rw [← List.map_id ins]
--- a/formal/lean/Formal/Net/Fasm/Basic.lean
+++ b/formal/lean/Formal/Net/Fasm/Basic.lean
@@ -1,5 +1,6 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.CElemTiming
+open Formal.Core.LutList
 
 /-!
 # Track 11b: the physical LUT netlist read from the FASM (the bits the board runs)
--- a/formal/lean/Formal/Net/Fasm/CePair.lean
+++ b/formal/lean/Formal/Net/Fasm/CePair.lean
@@ -3,6 +3,7 @@
 import Formal.Net.Fasm.CePairS3
 import Formal.Net.Fasm.CePairS4
 import Formal.Net.CoreLut
+open Formal.Core.LutList
 
 /-!
 # Track 11b: the ROUTED bd_c2 -> bd_c2n pair, read from the FASM, is the logical pair
--- a/formal/lean/Formal/Net/Import/PrelimSem.lean
+++ b/formal/lean/Formal/Net/Import/PrelimSem.lean
@@ -18,12 +18,12 @@
 open Formal.Net.CoreLut Formal.Net.CoreLutPrelim
 
 /-- Kleene reading with shard B's Prelim `lutK` (pre-port `kleeneSem`). -/
-def kleeneSemP : Sem Formal.Cells.K3 := ⟨Formal.Cells.lutK, Formal.Cells.K3.ofBool⟩
+def kleeneSemP : Sem Formal.Core.LutList.K3 := ⟨Formal.Core.LutList.lutK, Formal.Core.LutList.K3.ofBool⟩
 
 /-- Binary reading with Prelim's `lutB`. It IS `boolSem` (`boolSem_eq_boolSemP`,
 `Bool` is shared), so a theorem about one is a theorem about the other; it is
 only here so that proofs by `rfl` against B's `lutB`-valued lemmas keep working. -/
-def boolSemP : Sem Bool := ⟨Formal.Cells.lutB, id⟩
+def boolSemP : Sem Bool := ⟨Formal.Core.LutList.lutB, id⟩
 
 theorem boolSem_eq_boolSemP : boolSem = boolSemP := by
   unfold boolSem boolSemP
--- a/formal/lean/Formal/Net/Import/Proofs.lean
+++ b/formal/lean/Formal/Net/Import/Proofs.lean
@@ -3,6 +3,7 @@
 import Formal.Cells.CElemFn
 import Formal.Cells.Latch
 import Formal.Cells.ArbKleene
+open Formal.Core.LutList
 
 /-!
 # Track 11a: the imported netlists equal the cell specifications
--- a/formal/lean/Formal/Net/RingReset.lean
+++ b/formal/lean/Formal/Net/RingReset.lean
@@ -1,4 +1,5 @@
 import Formal.Net.BridgeRing
+open Formal.Core.LutList
 
 /-!
 # Probe C-9d (a): what bdc's reset puts in a ring, and the token count from it
--- a/formal/lean/Formal/Timing/RuntAck.lean
+++ b/formal/lean/Formal/Timing/RuntAck.lean
@@ -1,4 +1,5 @@
 import Formal.Timing.GrantFork
+open Formal.Core.LutList
 
 /-!
 # C-10j: does the grant-fork runt break the handshake? (H_RUNT_ACK)
```
