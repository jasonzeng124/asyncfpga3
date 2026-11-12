# A-glsfix: GLSPass.lean under autoImplicit=false, and a sweep of Mathlib-free Formal/Core

STATUS (2026-10-29, probe GLSFix): DONE. GLSPass.lean now builds with autoImplicit=false. The
re-check of every Mathlib-free Formal/Core module (79 Core files plus 8 non-Core dependencies,
in dependency order, under the fixed check.sh) found no other file that needs autoImplicit=true.

## 1. GLSPass.lean
The audit was right. `theorem skew_fval {p w : Nat} (hp : 1 ≤ p) : (fun t => xor (delay
((skewA d w).w 2 0) (skewIn p 0) t) (delay ((skewA d w).w 2 1) (skewIn p 1) t)) = pulse false p w`
used `d` without binding it. With autoImplicit=true Lean silently added an implicit `{d : Nat}`.
With autoImplicit=false (the lakefile, and now check.sh) that is "Unknown identifier `d`", and the
later `rw [← skew_fval (d := d) hp]` (line 385) fails with "Invalid argument name `d`".

Fix (one line): `theorem skew_fval {d p w : Nat} (hp : 1 ≤ p) : ...`.

Meaning: unchanged. It is the same universally quantified implicit Nat that autoImplicit had
inserted. The statement holds for every `d`, because the wire delays of `skewA d w` do not
depend on `d`. No other declaration was touched, and every other statement is byte-identical
(`git diff`: 1 line).

Check: `formal/check.sh Formal/Core/Delay/GLSPass.lean` (its imports Trace/Discrete and
Delay/SAF had lake oleans) gave `[audit] 263 declarations checked` and `[check] OK`.
It was re-checked in the sweep below, this time with Trace/Discrete and SAF also re-elaborated
from source under autoImplicit=false.

## 2. Sweep of Mathlib-free Formal/Core modules
Method: the script `/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/glsfix/deps.py`
works out, for every .lean under Formal/Core that existed when the sweep started, whether it
imports Mathlib transitively.

18 of them do: Basic, Delay/{Corner, CornerCode, CornerDiff, Inertial, Involution,
InvolutionDMin, InvolutionTransfer, Pure}, Discretize, Fidelity, Substrate,
Substrate/{CornerNat, Real}, TernaryChannels, Trace/{Bridge, Event, Real}. These were not swept,
because Mathlib was not built.

The other 79 Core modules were checked in ONE check.sh call, in topological order, together with
their 8 non-Core dependencies: Cells/{Prelim, MuxTree, CElemTiming, Bundling, LinkHandshake,
LinkTimed, PipeTimed}, Net/Prelim and Timing/Semantics. The non-Core files were checked
read-only and not edited. So every file was elaborated from source with -DautoImplicit=false,
and each one saw only the freshly checked oleans of its dependencies. The order list is in
`/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/glsfix/order.txt`.

Result: no Lean error in any file. The axiom audit was clean for 5934 library declarations and
for all 9 executables (XAudit/{Events2Main, Events2MainStrict, Events2Pin, Events4Main,
Events5Main, Events7Main, Events8Main, EventsMain, Main}). The final line was `[check] OK`.
Log: `/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/glsfix/sweep1.log`.
So among these files, GLSPass.lean was the only one that relied on autoImplicit.

## Not covered
* The 18 Core modules that import Mathlib. They need Mathlib oleans. The lead's `lake build`
  applies autoImplicit=false to them, so that build is their check.
* Core files that other probes created during this session and that were untracked when the
  sweep ran. Examples: Delay/{CornerCell, GLSResolve, InvolutionLoop*, InvolutionTrace},
  Prims/*, XAudit/{BandCheck, Events8Bridge*, Events9*, Sound*}, XSimChanReal and XSimChanTern.
  They were not in this sweep; only XSimChan.lean already existed, and it passed. Each probe's
  own check.sh run (which now passes autoImplicit=false) is the check for those files.
* This checked the working tree, not a commit. Files that others edited after the sweep are not
  covered.
