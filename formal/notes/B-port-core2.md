# B-port-core2: making the deletion of `Cells/Prelim` a mechanical import change (probe Bpt)

Shard B, PROGRAM.md Phase 1 ("port every Cells/ proof from Prelim to Core.
Delete Prelim"). Follows notes/B-port-core.md (values half, committed
e54d7ca) and A's notes/A-lutlist.md (probe LutList: `Formal.Core.LutList`,
Prelim's list API moved into Core under namespace `Formal.Core.LutList`).

State found: `Formal/Core/LutList.lean` is NOT in the tree yet; A's version
is at `lean/Wip/_snapA/LutList.lean` (A-lutlist.md: "claimed"). A's
`Core/EnvFast/SteerEnv.lean` now writes `Env.Gate` (l.84), so the Trace/WinDelay
half of the port is unblocked (checked below).

## 1. New file `Formal/Cells/PrelimCore.lean` (checks)

The dictionary: every Prelim / CElemTiming notion the Cells files use,
against Core. Plain language: nothing physical is assumed; all hypotheses are
length/delay side conditions.

| B notion | Core | theorem | exact? |
|---|---|---|---|
| `K3`, `K3.f/t/x`, `K3.ofBool`, `join`, `not` | `Core.K3`, `zero/one/X`, `ofBool`, `merge`, `not` | `k3_eq f_eq t_eq x_eq ofBool_eq join_eq not_eq` | `=` (`rfl`) |
| `K3.mux`, `K3.admits` | `kevalT` node; `K3.Le a (ofBool b)` | `mux_eq`, `admits_iff_le` | `=` / `↔` |
| `lutIdx l` | `addr (bvec l l.length)` | `lutIdx_list` | `=`, any list |
| `lutB init l` | `(lutOf l.length init).eval (bvec l _)` | `lutB_list`, `lutB_len` | `=`, any list, any INIT number (bits ≥ 2^len ignored both sides) |
| `muxTree g l` | `kevalT l.length g (kvec l _)` | `muxTree_list` | `=` |
| `lutK init l` | `Lut.keval` and `Lut.kevalSpec` | `lutK_list`, `lutK_len`, `lutK_list_spec` (via `kevalT_congr_lt`) | `=` |
| `o6B o6K o5B o5K` (6-pin list) | `Lut62.o6/.o5` `.eval/.keval` | `o6B_eq o6K_eq o5B_eq o5K_eq` | `=` (H: `l.length = 6`) |
| `completions` | `K3.Consistent` | `ofFn_mem_completions_iff`, `mem_completions_cons` | `↔` on `List.ofFn` |
| `CElemTiming.Trace` | `Substrate.Sig` | `trace_eq` | `rfl` |
| `CElemTiming.WinDelay lo hi` | `Substrate.Win lo hi` | `winDelay_eq_win`, `winDelay_iff_win` | `rfl` |
| `CElemTiming.Transport d` | `Substrate.Win d d` | `transport_iff_win` | `↔` |
| | Core `TraceDiscrete.Transport d d` | `transport_of_core` (Core ⇒ B), `not_core_of_transport` (B ⇏ Core: d=1, x≡0, y = [t=0]) | ONE-WAY: B leaves `[0,d)` free |
| `CElemTiming.exc init` | `(lutOf 6 init).eval (bvec [a,b,q,r,0,0] 6)` | `exc_eq_eval` | `=` |
| `CElemTiming.Loop` | two `Win` + `0 < dlmin+dwmin` | `loop_iff_win` | `↔` |
| `CElemTiming.Inertial d` | `TraceDiscrete.inertial (d-1)`, one tick late (`coreInertial d x t = inertial (d-1) x (t-1)`) | `inertial_of_core` (Core ⇒ B, H: `1 ≤ d`); `core_of_inertial` (B ⇒ Core from `d-1` on, under **H_POWERUP** `y (d-1) = coreInertial d x (d-1)`); `core_of_inertial_nonvacuous`; `inertial_powerup_needed` (d=2, x alternating, y≡1: a B behaviour, Core gives 0) | ONE-WAY; exact with H_POWERUP, which is necessary |

Not covered: silicon pin order (Core.Bridge), timing numbers. No Cells
theorem is restated.

Check (Core-only closure):

    scratchpad/bchk.sh formal/lean/Formal/Cells/PrelimCore.lean   ->  [bchk] OK
    #print axioms (all 40 theorems): none, or [propext], [propext, Quot.sound];
    inertial_powerup_needed also Classical.choice (from simp). No sorry/axiom/native_decide.

## 2. The patch (NOT applied)

Script and output in the probe scratch dir (`.../scratchpad/Bpt/`):
`gen/mkpatch.py` (generator), `patch/port-prelim.patch` (unified diff,
673 lines), `patch/files.txt` (57 Cells files), `patch/tree/` (patched
copies). The tree is moving; regenerate at apply time:

    python3 -I .../scratchpad/Bpt/gen/mkpatch.py formal/lean OUTDIR

Rules (all of them; nothing else changes, no statement, no proof):

* R1 (28 files, the direct importers incl. PrelimCore):
  `import Formal.Cells.Prelim` -> `import Formal.Core.LutList`.
* R2 (54 files: every Cells file in Prelim's closure whose code uses a Prelim
  name; they reach the names today through `namespace Formal.Cells`): add the
  line `open Formal.Core.LutList` right after the last `import`.
* R3 (ArbKleene l.49): `open Formal.Cells.K3` -> `open Formal.Core.LutList.K3`.
  (`open K3`, `open K3 in`, `open ArbKleene K3 in` need no change: checked in MuxTree.)
* R4 (PrelimCore only): qualified `Formal.Cells.{K3,lutB,lutK,mux_eq,...}` ->
  `Formal.Core.LutList.…`.
* R5 (CElemTiming, the trace half): add `import Formal.Core.Substrate.Chan`;
  `abbrev Trace := Formal.Core.Substrate.Sig`;
  `abbrev WinDelay (dmin dmax) (x y : Trace) : Prop := Formal.Core.Substrate.Win dmin dmax x y`
  plus `theorem winDelay_def … := Iff.rfl` (the old body).
* Then delete `Formal/Cells/Prelim.lean` (after A's and C's lines in §3).

Test compiles (copies under `Formal/Cells/_PortTest/`, lead deletes; the
copies import `Formal.Cells._PortTest.LutList`, a verbatim copy of
`Wip/_snapA/LutList.lean` with namespace `Formal.Core.LutList` unchanged; the
three files are byte-identical to `patch/tree/` up to that import name):

    BCHK_OUT=.../Bpt/olean scratchpad/bchk.sh Formal/Cells/_PortTest/{CElemTiming,MuxTree,ArbKleene}.lean
    -> [bchk] OK   (CElemTiming = R1+R2+R5, MuxTree = R1+R2 with `open K3` and
       its own muxTree_eq_lutK next to LutList's, ArbKleene = R1+R2+R3, decide-heavy)

Extra checks in the scratch dir only (no tree file touched):
* With Prelim.olean REMOVED and `Formal/Core/LutList.lean` placed as a real
  module: patched `CElemTiming` and patched `PrelimCore` compile (rc=0).
* Trace half vs the old blocker: real `CElemTiming` + R5, then the real
  `LinkTimed`, `PipeTimed`, `Core/EnvFast/SteerEnv`, `Core/Substrate/Legacy`
  recompiled on top: all rc=0, with `Formal.Core.Gate` visible in SteerEnv's
  closure. A's `Env.Gate` qualification fixes it.
* NOT checked (need Mathlib, not built: `lake build` still running): the
  Mathlib importers downstream of CElemTiming (CElemCore, CElemInvolution,
  ArbInvolution(2), ArbAnalog, Core/Discretize, Core/Substrate.Real). Of
  these only CElemCore, Discretize and Substrate(.Real) open `Formal.Core`;
  CElemCore uses no bare `K3` (only one `lutB`), so a clash is unlikely, but it
  is unchecked. The other 51 patched Cells files are unchecked (rule-identical
  to the three tested).

## 3. What remains for A and C (exact lines)

A (`Formal/Core/`):
* Commit `Wip/_snapA/LutList.lean` as `Formal/Core/LutList.lean` (prerequisite
  for everything here).
* `Core/Bridge.lean` l.5-6: `import Formal.Cells.Prelim` + `import Formal.Cells.MuxTree`
  -> `import Formal.Core.LutList`, and `Formal.Cells.X` -> `Formal.Core.LutList.X`
  in code (A's `Wip/_snapA/Bridge.lean` already does this).
* `Core/Substrate/Legacy.lean`, `Core/Discretize.lean`: no change
  (`import Formal.Cells.CElemTiming` stays; `win_iff_winDelay` stays `Iff.rfl`,
  checked for Legacy).

C (`Formal/Net`, `Formal/Gen`, `Formal/Timing`):
* Direct importers: `Net/Fasm/Basic.lean` l.1, `Net/CoreLutPrelim.lean` l.2
  (+ l.3 `import Formal.Cells.MuxTree` optional): `import Formal.Cells.Prelim`
  -> `import Formal.Core.LutList`, names as in A's trials
  `Wip/LutList/trial/{FasmBasic,CoreLutPrelim,GenPrelimSem,ImportPrelimSem}.lean`
  (`Gen/PrelimSem`, `Net/Import/PrelimSem`: qualified `Formal.Cells.{K3,lutB,lutK}`
  -> `Formal.Core.LutList.…`, no import change). After B's R5, CElemTiming no
  longer imports Prelim, so A's caveat for Fasm/Basic (ambiguous `o6B`) goes
  away; `open Formal.Core.LutList` there is enough.
* Files that get Prelim names through `open Formal.Cells` (no import change,
  add `open Formal.Core.LutList` next to that `open`):
  `Gen/ProofsArb` l.29 (K3), `Gen/ProofsCE` l.33 (K3), `Gen/ProofsCtl` l.19
  (K3 lutB o5B o6B), `Gen/ProofsLatch` l.29 (K3 K3.mux lutK), `Gen/ProofsLink`
  l.24 (lutB o5B o6B K3), `Net/Fasm/CePair` l.43 (K3 lutK), `Net/Import/Proofs`
  l.41 (K3 K3.mux), `Timing/RuntAck` l.61 (lutB), `Net/BridgeRing` l.191, 198,
  212 (`open Formal.Cells … in`: K3.ofBool; use `open Formal.Cells Formal.Core.LutList … in`).

Order: A commits LutList (+Bridge) -> C's direct-importer changes (A's
trials use qualified names, so they work with Prelim still present) -> ONE
commit with B's patch (§2), C's `open Formal.Core.LutList` additions and the
deletion of `Cells/Prelim.lean` -> full `lake build` + check.sh. The `open`
additions (B's R2 and C's) must not land while Prelim still exists: with both
`Formal.Cells.K3`/`lutB` (via `namespace`/`open Formal.Cells`) and
`Formal.Core.LutList.K3`/`lutB` visible, unqualified names are expected to be ambiguous (reasoned, not tested).
