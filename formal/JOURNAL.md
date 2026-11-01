# Formal feasibility journal

## 2026-10-27 -- branch created
Branched from claude/research at 3dc25ad. Program in formal/PROGRAM.md.

## Session Tue Oct 27 02:37:59 UTC 2026 (shard A, lead)
### progress 02:37
Lock taken (was epoch/none). Machine: 4 cores, 15 GB RAM, no swap. Starting track 1 (toolchain).
### progress 02:44
Toolchain. Blocked by the proxy (403): release.lean-lang.org (elan downloads),
Reservoir (lake's package lookup), cache.mathlib.org and
lakecache.blob.core.windows.net (Mathlib's prebuilt oleans). Workarounds:
Lean 4.35.0 from the GitHub release zip linked into elan; Mathlib v4.35.0 by
git URL in lakefile.toml; Mathlib built from source, but only the modules the
project imports (lake builds the transitive closure only). PROGRAM.md says
never build from source unless the cache fails: it fails.
- formal/slot.sh: flock semaphore, default slots = min(nproc-1, (memGB-2)/4)
  = 3 here. A `lake build` holds one slot but uses all cores; only the shard
  lead runs it.
- formal/check.sh: builds every module under formal/lean/Formal/ (lakefile
  globs Formal.+), a textual scan for sorry/admit/native_decide/axiom, then an
  axiom audit: every declaration in a Formal.* module, via collectAxioms, may
  use only propext, Classical.choice, Quot.sound (sorryAx and
  Lean.ofReduceBool fail it). Unproved work goes in formal/lean/Wip/ (not built).
- Import policy (to keep the from-source build small): import specific Mathlib
  modules, never `import Mathlib`.
### progress 02:48
11 shard-A probes launched as subagents: trace (ℝ, event list, discrete; common benchmark B0-B5), circuit layer + event/ℝ bridge, delay (pure, inertial, involution), Kleene LUT (INIT semantics, shared Core API), LUT mux-tree fidelity theorem, primitive fidelity table, literature x2. Mathlib subset builder running (lead only); probes ask for modules in Wip/REQUESTS.txt. Draft PR #3 opened.
### progress 02:59
check.sh hardened: per-file mode (`formal/check.sh Formal/X.lean ...`, used while
other probes' files are mid-edit); comment-aware textual scan (formal/scan.py);
audit imports Lean. Negative controls run: a sorryAx hidden from the scan fails
the audit (`negctl_sorry uses sorryAx`); native_decide fails both the scan
and the audit (`..._native.native_decide.ax_1_1`); a clean rfl theorem passes.
Bug found and fixed on the way: with pipefail, a failing `lean` made the
`| grep error && fail=1` branch never run -- the check could not fail. 
Claimed (check.sh OK, audit only propext/choice/Quot.sound):
- Formal/Core/Delay/Pure.lean (47 decls): bounded FIFO transport channel as a
  retiming relation; series composition is EXACTLY the sum band
  (chan_comp_iff); pulse width bounds w±(hi-lo); a pulse can vanish iff
  w ≤ hi-lo (pulse_vanish_iff); bundling lemma bundle_two_wires
  (ts + hiD ≤ loR). Open in Wip: event-list adequacy; bounded-skew variant.
- Formal/Core/LutTree.lean (core Lean only): mux-tree Kleene eval equals the
  INIT-table Kleene semantics for every k, INIT, K3 vector
  (evalTree_eq_tableEval); tree order irrelevant for the Kleene function
  (evalTree_swap); timed tree with arbitrary per-mux delays: single input
  change with equal endpoint values is glitch-free (sic_glitch_free) under two
  named hypotheses H_mux_kleene, H_sram; two-input changes across a function
  hazard glitch, order-dependently. Finding: research GLS's SLICE_LUTX builds
  the tree with A6 at the leaves (silicon: A6 at the root, per UG474); harmless
  for Kleene values, differs in timing.
Literature notes A-lit-1 (40 sources), A-lit-2 (Graphiti, Lean 4 Dynamatic
dataflow, ASPLOS'26; ACL2 link-joint async proofs; Lutsig HOL4 7-series LUT).
### progress 03:04
Claimed since last note: Core/Delay/Inertial, Core/Fidelity, Core/Trace/Event,
Core/Trace/Discrete, Core/Kleene, Core/Lut, Core/Ternary (see commit messages).
`formal/check.sh --committed` (new mode: lake build of git-tracked Formal/ modules
of all three shards, then the axiom audit): Build completed (902 jobs), 1531
declarations audited, OK. B and C have both chosen discrete ℕ-ps time for cell
and network proofs, independently; A's discrete probe recommends the same.
Running: trace-real, circuit layer, involution, corner-correlated bounds, LUT
hazard audit. Launching a K3 bridge (LutTree/Ternary K3 ≅ Core.K3).
### progress 03:20
Container restarted ~03:12 (disk kept); 4 probes resumed by message, builder restarted.
Trace/Real: RealComplete discharged (Real.exists_isGLB). Corner, Bridge, Circuit,
Trace/Bridge claimed (see commits).
**GLS comparison (notes/A-gls-compare.md, tools-A/gls-compare/run_all.sh).** The
research GLS (origin/claude/research cells/gls/prims.v, SLICE_LUTX with specify
paths under iverilog) implements neither inertial nor transport LUT delay but
"sample at fire": each input change schedules an update at t+d which copies the
function's value at the moment it fires; nothing is cancelled. Fitted 140/140
random traces (inertial 48, transport 4). Consequence: an edge that follows an
earlier change within d reaches the output EARLY, down to a few ps after its
cause. Reproduced by me with a 10-line tb: a pulse 1000-1120 then a rise at 1130
gives o6 rising at 1244 (114 ps, arc is 124). So the GLS can make a glitchy data
cone look settled up to one LUT delay early per glitching LUT: optimistic bundled
margins, the unsafe direction. Not measured: how often this occurs in a routed
design. The earlier statement in A-delay-inertial.md that "the GLS can never show
a LUT runt" holds only for isolated pulses; corrected by this note.
Agreement: LUT/MUXF7 X-propagation = Core kevalSpec on 43,767/43,767 vectors;
bd_c2 single-input flips clean. Disagreement: bd_c2 a,b 01→10 at q=0 is a hazard
in Lean (X), a sharp skew threshold in GLS (no X), and with a transport feedback
wire oscillates forever.
### progress 03:34 (heartbeat)
`formal/check.sh --committed`: all three shards' committed modules build, 4924
declarations audited, OK. First attempt died with exit 137 (OOM kill) on
Formal.Core.LutAudit while the Mathlib builder (4 parallel lean) and 3 probe
slots were running; rebuilt alone in 44 s. Memory, not proofs; a lake build of
Mathlib should not overlap full slot use (to fix in the builder).
Claimed since last note: Discretize, LutCells/LutAudit, Delay/SAF (final), XSim
(interim). SAF: the GLS's sample-at-fire channel is contained in transport [1,d]
and in no [lo,hi] with lo ≥ 2 (saf_not_transport): GLS per-LUT delay is an upper
bound only. GLS settle ≤ pure-delay settle on a chain but fails on reconvergent
logic (xor_settle_late); only the static bound survives (net_settle_static).
A GLS run equals the pure-delay run iff every fire copies the value its own
change set (saf_eq_delay_iff) -- checkable by a monitor in prims.v.
Running: XSim, Env (protocol environment model).
### progress 03:37
PROGRAM.md updated by the owner (arbiter = digital race, primary; 48-h plan).
Shard A phase 1/2 launched: Core Substrate consolidation (one ℕ-ps API, the
corner model as the delay model, ℝ bridge), the κ estimator tool, and the
whole-design X/hazard audit executable (xaudit). SAF (phase 2 item) already done.
Mathlib builder stopped and Log.Basic dropped from REQUESTS: building
Analysis.* from source on 4 cores costs hours and risks OOM next to 3 Lean
slots (one OOM kill already); it only served the optional involution exp/log
instance, which stays with exp/log as named hypotheses (ExpLog).
FEASIBILITY.md: verdicts for tracks 1-11 and 13 in; track 12 pending (C).
### progress 03:52
Push helper incident (lead tooling, no data lost): after rebasing in a detached
worktree, the main tree was moved with `reset --soft`, then `reset --mixed` +
`restore`, which left other shards' files stale or missing in my working tree
(never committed: each push went from the worktree). Restored every non-A path
from HEAD; the helper now uses `git reset --keep NEW` (updates every file
changed upstream, refuses if one has local edits).
Untracked Formal/Core/{Env,Substrate,XAudit} are probes in progress; they are
committed only after check.sh passes (Env currently fails: mid-edit).
### progress 03:58 -- FOR SHARDS B AND C: the Core Substrate has landed
`import Formal.Core.Substrate` (or `import Formal`). Porting guide, name map and
graded hypothesis list: formal/notes/A-substrate.md. State delay hypotheses with
`Win lo hi` (B's WinDelay is literally Win: `win_iff_winDelay` is Iff.rfl); use
`WinR` only where a quiet start is needed (`runOfWinR` gives C's Run). Corner
model: `CornerModel`, `Realizes`, `EndpointOK`, `bundle_realizes`; real-time
soundness `endpoints_sound_real`. Legacy bridges to both Prelims in
Formal/Core/Substrate/Legacy.lean (not imported by Substrate; it goes away with
the Prelims). When the Prelims are deleted, A removes the Prelim sections of
Core/Discretize.lean and Core/Bridge.lean (replacements already in
Substrate/Real.lean). Weakest hypotheses: H_AFFINE (grade C) and the value of κ (C;
per-path κ ≥ 0.31 from the rings, difference κ unmeasured: notes/A-kappa.md).
### progress 04:02
Env (mechanised SI environment model) claimed: bd_c2, bd_latch pair, bd_link 1-bit
are speed-independent under rules H, L and isoEn, each proved necessary; all
reachable multi-input LUT changes hazard-free. For shard B: Env + LutAudit are
available for bd_arb/bd_merge/bd_mux SI models (A is not modelling the arbiter, to
leave the digital race to B). Kernel memory limits Env at ~1000 states (2-bit
link > 6 GB); launched EnvFast (bit-packed Nat states, GMP kernel ops, proved-once
checker over an untrusted certificate).
### progress 04:23
xaudit claimed (Phase 2 A): `lake build xaudit`; `bash formal/tools-A/xaudit/run_all.sh`
with XAUDIT=formal/lean/.lake/build/bin/xaudit. Verified engine (array simulator proved
equal to XSim.val; untimed A/B equal to Ternary iterA/iterB; noX_sound); parser and
compiled code trusted (kernel re-check of the bd_c2 verdict in XAudit/Check.lean).
pipe3 (bd_pipe W=2 N=3, illustrative ±10% bands) clean at one corner; hold-violation
negative control flagged; slow own-feedback flags C-element glitches (obligation
"own feedback < fastest neighbour response", not found as a rule in tighten.py);
untimed: the Muller pipe is not delay-insensitive (expected). ring3: imprecision after
one lap (FIFO-aware domain needed). gcd_hw blocked: no routed JSON on disk, no FPGA
toolchain in this container.
Build fixes: (1) the root module Formal was never built (lakefile globs "Formal.+"
does not include Formal itself) -- full-mode check.sh could not have passed its audit
import; now globs = ["Formal", "Formal.+"]. (2) check.sh file mode wrote hand-built
oleans into .lake/build, which broke lake's C linking of xaudit; it now writes to
.lake/checkfile. Clean rebuild: 1540 jobs, 4m37s. Full `formal/check.sh`: 9003
declarations audited, OK.
### progress 04:55
EnvFast claimed: bit-packed proved-once checker over untrusted certificates;
bd_link W=2 (1048 states) proved (link2_sound) in ~20 s / 736 MB peak, where Env
needed > 6 GB. bd_merge control path: merge_sound under the documented exclusivity
obligation plus selFast; NEW: selFast is needed and is not stated in the RTL header
(merge_needs_selFast: the select LUT must settle before the x side moves again,
else sel gets a runt). Negative controls: certificate with a state removed is
rejected; unconstrained merge is rejected.
check.sh file mode, two more fixes: (1) per-run overlay dir (concurrent runs from
probes wiped a shared one mid-run); (2) the overlay is a symlink copy of lake's
oleans, because Lean resolves Formal.* from the first LEAN_PATH entry that has a
Formal/ dir. Negative control re-run: hidden sorryAx still fails the audit.
The heartbeat's --committed run was void (check.sh was edited while bash was
reading it); rerunning. Usage limit hit at ~04:45 (resets 04:50): the gcd_hw xaudit
probe stopped mid-way and will be resumed.
### progress 04:59
`formal/check.sh --committed` (all shards): build 2972 jobs OK, 11582 declarations
audited, OK. Running: gcd_hw xaudit (resumed), EnvFast bd_mux + merge data path,
event-time abstraction for loop precision (XAudit/Events).
### progress 05:58 (heartbeat)
Claimed since last note: XAudit/Events (closed Muller rings precise for all time; Race
obligation per pin; xevents exe), Events2 (open nets incl. pipe3 for every handshaking
environment, real n-input C-element INITs, delay chains, exact cycle-ratio period
certificates). Running: gcd_hw xaudit, EnvFast mux/merge-data, parser factoring +
xevents2 + choice (E5). Findings sent to the owner: C-element own-feedback obligation
(A xaudit + C FbBound) unchecked by the flow.
### progress 06:02 -- FOR SHARD C: committed tree does not build
`formal/check.sh --committed` FAILS since C's 77e8224 ("heartbeat, WIP snapshot"):
Formal/Net/HandshakeMuller.lean, Formal/Net/Muller.lean, MullerTimedCx.lean,
EndToEnd.lean, Fasm/CePair.lean, Import/Netlist.lean, Gen/Netlist.lean,
Gen/ProofsPrims.lean import `Formal.Net.CoreLut`, which is in no commit on any
branch (lake: "bad import 'Formal.Net.CoreLut'"; everything downstream fails,
incl. PerLink, EndToEnd*, Gen/*). Fix: commit Formal/Net/CoreLut.lean (after it
checks) or revert those imports. A has not touched C's files.
A's own modules all build (last per-file checks OK). gcd_hw xaudit claimed (see
commit bf952a1 and FEASIBILITY).
### progress 06:33
`formal/check.sh --committed` green again (C committed CoreLut): all library modules
audited together, each executable module (xaudit, xevents, xevents2, C's GcdHwProof)
audited alone. Claimed since last note: XAudit/Parse (shared trusted parser; refactor
byte-identical on 11 runs), xevents2, Events3 (choice: steer/OR-merge), EnvFast
mux/merge-data/steer (bd_mux: rtz, select hold past uj1, fork conditions -- not in the
RTL header; merge selFast withdrawn).
### progress 06:51
gcd_hw_hypotheses.md drafted (≈65 rows, graded, with tests; §7 lists contradictions).
**Correction, κ:** A-kappa's κ ≥ 0.311 used ring ratios against pre-lut-perm-sink-patch
SDFs (C-10c); corrected predictions match comparable rings to 1.1–6.7%. The bound
measured an SDF bug, not scatter. FEASIBILITY, FOR-RESEARCH, A-kappa corrected; the
owner was told the 31% figure earlier and is being told the correction. Open A items
from §7: X2 (Race/Back use ≤, the mux-tree equality case is a hazard: make strict),
X1 (EnvFast's data exemption leans on inertial filtering), X6 (steer select hold:
A says none needed, B/C require one).
### progress 07:21 (heartbeat)
Claimed since last note: Events4 (gcd_hw control at real widths, seed d; analysis in
Python, rule arithmetic in Lean, Beh4.safe open), contradictions X1/X2/X6 resolved
(Events2Strict, DataHyp, SteerEnv; xevents2strict exe), gcd_hw_hypotheses.md
(+ §7b resolutions). Corrected κ claim (pre-patch SDF). Running: Events5 (Beh4.safe +
seeds 3/4/5 + FASTFALL check), per-pin BackPin checker. --committed check running.
### progress 08:04 (heartbeat)
--committed check at ~07:45 green (3094 jobs, 20957 library decls + executables).
Claimed since last note: xevents2pin (per-pin, no H_ATOMIC_LUT), Events5 (Beh4.safe;
4 seeds; FASTFALL finding corrected to a rule-F head residual; 4 guardband survivors
sent to the owner). Running: Events6 (netlist link design_beh4, GuardOK, n-ary merge,
xevents5 vs ana5 cross-check).
### progress 08:46 (heartbeat)
--committed check green at ~08:30 (3109 jobs, 24054 library decls + executables).
Claimed: Events6 (netlist link design_beh4; xevents5; gcd verdict conditional on 45
residuals per seed). Running: Events7 (U3, guarded delay-line pins, GuardOK, 3-way
merge, cascade) aiming at a CLEAN slow/fast certificate on one seed.

## Session Tue Oct 27 10:38 UTC 2026 (shard A, lead; session_01HC49FuHh39ZuDhAHxHUAQa)
### progress 10:45
Took LOCK (previous A lock 08:46, 112 min stale; B/C locks also ~100 min stale).
Fresh container: setup.sh running (Lean zip from GitHub, Mathlib from source).
**Loss, correction:** the previous A session ended before committing the Events7
Lean modules. `Formal/Core/XAudit/Events7{Core,Excl,Cert,Beh,Main}.lean` are in no
commit on any branch; only `notes/A-events7.md`, `Wip/Events7.lean` and
`tools-A/xaudit/events7/` (certs, results) were committed (f4696cc). So the
"CLEAN at slow/fast on every seed" verdict in notes/A-events7.md is NOT claimed:
the xe7_*.txt outputs exist, the Lean that produced them does not. Being rebuilt
(probe E7r). Nothing in FEASIBILITY cited Events7.
Audit (claude/audit REPORT) rows on A's files, not yet answered: rule A as coded
(int(0.2*t), max(.,200)) has κ limit 25/276, not 1/11 (Corner.lean proves the
real-division rule); involution "transfer lemma" overstated (no relation to
Pure.Chan proved, no instance built, module imported by nothing); Ternary
soundness for transport/inertial only by prose; minor wording. Probes launched
for each; FEASIBILITY wording fixed by me.
For B: qualified `Env.Gate` in Core/EnvFast/SteerEnv.lean (B's request, JOURNAL-B
08:16), to be checked once Mathlib is built.
### progress 10:50
11 probes running: E7r (rebuild Events7 Lean), CornerCode (rule A as coded, audit),
InvTransfer (involution transfer lemma + instance, audit), TernSound (transport/
inertial ⊆ Causal, audit), K2 (second kernel via the cached FPGA toolchain + HOWTO),
GLSimp (what a passing GLS run implies), KapRes (indep-corner residuals under the
settled κ corner model), LutList (Core list-LUT API so B can delete Prelim), Lit3,
HypDoc (refresh gcd_hw_hypotheses.md against the current Lean), GLSdiff (model vs
current research GLS). FEASIBILITY: audit wording rows fixed (RealComplete
discharged; pulse width limit only at threshold; transfer lemma marked NOT proved;
rule A 1/11 is for exact division, code limit ≈25/276; 19 INIT constants/23
theorems; Ternary transport/inertial only prose). Mathlib: cache download attempt.
### progress 10:58
Lit3 done (notes/A-lit-3.md; paper hosts unreachable, entries tagged by source quality;
FEASIBILITY track 13 updated). HypDoc done: out/gcd_hw_hypotheses.md rewritten against
the Lean (read at file:line; no Lean run, Mathlib still building). Best end-to-end
statement: C's `gcd_hw_circuit_safe''` (CapstoneCut.lean:535) under H_CELLS, H_BUNDLE,
H_START_ONCE, H_WALK; safety only, first rig lap only, a,b < 2^31. Findings for B/C
(not A's files, not edited): RigContract.lean does not compile at HEAD (audit
REPORT.md:48), so a full check.sh fails until it is fixed or moved to Wip; B's reset
model `gNet` and the capstone's `Src` disagree on the initial request value; OpsGen's
per-cell bindings are not applied to the 367 operators; rule K (C-10l, WIP) fails
16-26 of 42 rows per route at every corner (meaning unconfirmed).
### progress 11:02 (times above in this session corrected to date -u)
GLSdiff done (notes/A-gls-compare-2.md, research 5d535d7): LUT function/X agree on
43,767 vectors; fid's LUT/MUXF channel = Lean per-pin transport (60/60 + 60/60). GLS
wrong on four: CARRY4 and latch still sample-at-fire under fid (early edges in carry
chains); flop treats X on SR/CE as 0 (hides X); FID_RESOLVE splits at TLOOP-WIN/2
(349 ps of 424) where a Float run of Lean's loop recurrence decides at ~TLOOP/2
(computation, not a theorem). Bullets added as FOR-RESEARCH §8; fidelity-table GLS
row updated (was "inertial", stale). Nothing claimed in Lean (Wip #eval only).
### progress 11:22
GLSimp claimed: Formal/Core/Delay/GLSPass.lean (check.sh with Trace/Discrete + SAF:
263 declarations, [check] OK; Lean core only). A passing sample-at-fire GLS run implies
the property only if silicon is exactly SAF at exactly the annotated delays; proved
counterexamples (XOR skew glitch, XOR3 capture, bd_c2 with feedback) pass the GLS at
124 ps and fail at another delay in the [45,124] band, under transport, or under
inertial; a faster LUT can fail where the slow arc passed (the slow column is not a
conservative corner). Sufficient condition proved: acyclic, monotone LUTs, rising
inputs => one run at the maxima bounds the band; two runs (FAST_MIN, SLOW_MAX) give
request-after-data. Not covered: per-pin arcs, GLS_FID, X, feedback nets (so not
gcd's datapath). Notes: notes/A-gls-pass.md.
### progress 11:57
E7r claimed: Events7{Core,Excl,Cert,Beh,Main}.lean rebuilt from notes/A-events7.md.
check.sh (with 25 deps listed; lake build not yet possible): library 2525 decls,
xevents7 2609, [check] OK. Rerun on the 4 gcd_hw R5 nets (md5s = events5/builds.txt):
byte-identical to all 16 committed xe7 outputs, 4 ablations and 6 negative controls.
So notes/A-events7.md's table now stands on committed Lean: slow and fast CLEAN on
every seed; gb residuals 0/0/0/1 (d/3/4/5); mixed (independent per arc) 9/13/10/8.
design_verdict7 still assumes GuardOK, SelOK, SelPart, H_ARB; the reader is trusted.
xevents7 lakefile stanza added. Open: W-E4g (GuardOK).
### progress 12:08
K2 done (north-star goal 3, second kernel): collatz rig built with the restored FPGA
toolchain (toolchain.sh 9/9, nextpnr 9c732bc6303458df), seeds d/4/5/6 (seed 3 failed
placement), cells audits pass. xevents5 (fuel 256; fuel 64 says NOT RECOGNISED on
65/73-element pin paths, any fuel is sound): CLEAN at slow and fast on all 4 seeds, gb
CLEAN 3/4 (seed 5: rig env uenv1 -9 ps, the same rig item as gcd seed 5), mixed 2-5
residuals per seed, 0 structural. Negative controls fail as required. xaudit certifies
one transaction (n=2) only at slowmax w=0 with a 10 ps step (weaker than gcd). How-to:
out/HOWTO-new-kernel.md. Fixed tools-A/xaudit/build.sh (Parse missing from MINE).
xevents7 on collatz next (Events7 is now committed).
### progress 12:17
K2: xevents7 on collatz, 16 rows, identical verdicts/residuals to xevents5 (collatz
has no guarded delay lines, no select partitions, no >2-arm merges, so the Events7
extensions are vacuous there): slow/fast CLEAN on all 4 seeds; gb seed 5 rig env
uenv1 -9 ps / uenv0 0 ps; indep 3/3/2/5. Negative controls fail. Mathlib build:
2529 oleans at 12:17.
### progress 12:21
CornerCode claimed (check.sh 21 decls OK): tighten.py's rule A as coded (SLACK=0) is
sound iff κ ≤ 25/276 (iff proved; audit row answered); SLACK ≥ 1 gives 1/11 again; the
float-to-floor equality is argued, not proved. FEASIBILITY 3b and FOR-RESEARCH §9 updated.
### progress 12:31
KapRes done (notes/A-kapres.md; xevents5, untrusted cover argument): under the settled
corner model (shared corner c in [0,1], local scatter κ) the "indep" timing residuals
of gcd_hw vanish: seeds d/3/4 have no timing item at any κ ≤ 0.10, seed 5 has one, the
rig environment pin urig.uenv1.u (not the kernel), which fails for κ ≥ ~0.08 at the
slow corner. Nothing survives at κ = 0. Caveats: the 45 structural items remain
hypotheses (xevents5, not 7); the cell-cover lemma (Corner.cell_band) is argued, not
proved. **Data finding:** committed fast band files have FAST_MIN > FAST_MAX on 2-20
arcs per seed and the checker silently reads such a band as [lo,lo] -- a front-end
input that should be rejected, not narrowed. Follow-up probe KapRes2: prove cell_band,
make the band reader reject lo > hi, rerun with xevents7.
### progress 12:36
LutList: Formal/Core/LutList.lean claimed (Prelim's list LUT API under Core; check.sh
with Kleene/Lut/LutTree/Ternary/Bridge: 738 decls OK). Bridge's switch to it is NOT
committed: it changes statement text (Formal.Cells.X -> Formal.Core.LutList.X, equal
by rfl/induction in Wip/LutList/PrelimEq.lean), and B's modules that use Bridge are
untested against that alone; kept as Wip/LutList/Bridge.switched.lean. Deleting Prelim
needs one coordinated commit (B + C + Bridge); the end-state trial compiled all 189
Mathlib-free dependents. Recipe and per-file diffs for B and C: notes/A-lutlist.md
(rerun the switch scripts on the live tree; B's tree has moved).
### progress 12:38
WE4g -> Events8 claimed (check.sh with deps: 2489 lib decls, xevents8 2724, OK):
GuardOK is no longer a hypothesis of the gcd_hw verdict; each of the 63 guarded pins
per row carries a Lean-checked guard certificate (BACK-G, LINE, ENTRY, EXIT, strict).
It is replaced by a narrower named count hypothesis **HDsub** (126 SUB judgements from
the guarded source D; the Events7 SUB rule is sound only from the label source; ~1 day
to close). design_verdict8 hypotheses: SatPin, constant wires/reset, H_ARB, SelOK,
SelPart, HDsub. Rows: slow and fast CLEAN on all 4 seeds (63/63 guards); gb: seed d
FAILS ENTRY on 3 arbiter guard pins (ucontrol_merge3.uarb1.ua2 pin0 -51 ps,
ucontrol_merge3.uarb1.ua1 pin0 -94, ucontrol_merge2.uarb1.ua2 pin0 -68), seeds 3/4
CLEAN, seed 5 only the rig uenv1 item; indep 46-51/63 guards. Negative controls
rejected. Wip/Events7.lean's fmax guardCnt shown wrong (guard_fmax_neg), superseded.
Next: probe HDsub.
### progress 12:51
InvTransfer claimed (check.sh with Pure/Involution: 191 decls OK): corrected transfer
lemma transfer_sep (threshold S > D - δmin, band [δ(S-D), D] closed at the top, output
is a Pure.Chan behaviour), exact for symmetric pairs (sep_threshold_sharp), instance
ratPair. Audit row answered; FEASIBILITY §3 rewritten. setup.sh finished (7561 s) with
one failure, Formal.Core.Bridge (built while LutList's switched Bridge was in the tree;
reverted since); full check.sh --committed running.
### progress 12:51
TernSound claimed (check.sh 833 decls OK): Formal/Core/TernaryChannels.lean. The audit
was right and the prose claim was not literally true: Causal is discrete-time, the
channels are ℝ-time; sampling is not Causal in general (sample_not_causal); zero lower
delay makes ternary simulation unsound (zero_delay_*_unsound). Proved: a continuous
class RCausal δ with soundness and settling (SettlesWithin, covers inertial), and
transport/inertial/bounded-inertial channels with positive lower bound are instances
(ternary_noGlitch_channels, ternary_settle_channels). FEASIBILITY §4 bullet replaced;
pulseWidth wording made one-sided. All four audit rows on A's files now answered.
### progress 12:57
DMin claimed (check.sh 222 decls OK): δmin exists for every InvolutionPair from its
fields (sSup argument, no continuity field); IsDMin-free versions of the headline
theorems; exact separation threshold sep_threshold_exact (rise strict, fall non-strict).

## Session Wed Oct 28 02:43:34 UTC 2026
### progress 02:43
New session (session_01HC49FyJ7SsMX5uaArAZWa3); previous A lock 14 h old, taken. Audit branch
unchanged since 2026-10-27 12:42 (e7b64c5); every row on A's files was answered last session.
Fresh sandbox: setup.sh running (Lean 4.35.0 from the release zip; cache.mathlib.org still 403,
so Mathlib builds from source again, ~2 h). Lost with the last sandbox (never committed):
Core/Delay/CornerCell.lean (KapRes2) and the Events9 Lean (HDsub); their notes/data survived.
Probes launched (12): HDsub->Events9, KapRes2 redo (cell_band proof, band reader rejects lo>hi,
κ sweep with xevents8), E8Hyp (SatPin/H_ARB/SelOK/SelPart bridged to B/C or shown mismatched;
joint witness), K3 (xevents on ipow and xorshift; HOWTO fixes), XSound2 (xaudit verdict sound for
transport/inertial channels, covered-window sound_postfix), GLSPass2 (per-pin fid GLS model),
InvTrace (full involution trace semantics), PrimsComb (MUXF7/F8, CARRY4, LUT6_2 in Core),
PrimsSeq (flops/latches; DSP/RAMB only if used), LutList2 (Prelim deletion patches on the live
tree), ForRes (FOR-RESEARCH refresh), Fid3 (GLS compare vs current research; per-primitive
fidelity table; FID_RESOLVE threshold).
### progress 02:50
ForRes done: out/FOR-RESEARCH.md rewritten (15 sections; research tip 350f9be). New: §1 rule A
times GND/VCC tie-off nets as data (C-10n, unfixed at 350f9be); §3 κ table (B's ConstraintsKappa:
box and SLOW-only checks unsound for κ>0; gcd_hw arbiters κ ≤ 0.0443; rule A as coded 25/276;
rule E 0.199); §4 prjxray-db BRKH_INT has 28 FAST tuples with FAST_MIN > FAST_MAX (local scan);
§5 rules tcheck replaces + front-end gaps. GLS CARRY4/latch SAF early edge and flop X-as-0
re-observed with iverilog on the current research prims (unchanged since 5d535d7). Nothing new
claimed in Lean; unverified readings are marked (rule A guard pre-lag, xray_delay fast corner).

## Session Thu Oct 29 07:12:24 UTC 2026
### progress 07:25
New session (session_01HC49Fwiv93CFgTH6CuFfLh); previous A lock 28 h old, taken. The
2026-10-28 session died about 10 minutes after launching its 12 probes; only their WIP
snapshot (fe4e8c0: Wip/_snapA, notes, tools) survived, nothing from it is claimed.
Audit (83b1290) has two new rows on A's files:
- **GLSPass REFUTED as a checked result** (module fails `lake build`: `skew_fval` uses an
  unbound `d`, which only elaborates with autoImplicit=true). Root cause is in check.sh:
  its per-file mode ran `lake env lean`, which does not apply the lakefile's
  `[leanOptions]`, so every single-file "check.sh OK" was checked under a weaker
  standard than the lake build. Fixed now: per-file mode passes `-DautoImplicit=false`
  and fails on any `error` line in the log. GLSPass is withdrawn as a claim until it
  builds under `lake build` (probe GLSFix). The auditor's clean build found it the only
  one of 422 modules failing, so other single-file claims stand on the lake build.
- **Events8 seed d gb ENTRY: 2 of 3 reproduce** (ua1 passes at +45 ps in the auditor's
  model). Our bands (xray_delay 99b10a6d) omit prjxray's a5lut->AMUX hop (62/78/163/202
  ps) on every O5-driven arc. Also A-events8.md:74 was wrong (ana5 listed all three).
  Probe E8Mux: add the OUTMUX hop to the band builder, rerun xevents8, correct the note.
Fresh sandbox again: setup.sh running (Mathlib from source, ~2 h).
### progress 07:17
12 probes launched (common brief: probes never touch git, write only their files, all Lean
through slot.sh, check with the fixed check.sh): GLSFix (GLSPass under autoImplicit=false;
re-check every Mathlib-free Core module with the fixed check.sh), E8Mux (OUTMUX hop in the
bands, band reader rejects lo>hi, rerun xevents8; audit row), HDsub (Events9 from the
snapshot), KapRes2 (CornerCell.cell_band, BandCheck, κ sweep with xevents8), InvTrace (full
involution trace semantics with chained cancellation), PrimsComb (LUT6_2, MUXF7/F8, CARRY4,
OUTMUX arcs), PrimsSeq (flops/latches; DSP/RAMB only if used), XSound2 (xaudit sound for
continuous-time channels), GLSPass2 (research's current fid GLS channel; what a pass implies),
K3 (xevents8 on ipow and xorshift; HOWTO), E8Hyp (bridges for design_verdict8's hypotheses to
B/C; joint witness), Fid3 (per-primitive fidelity table vs research 6524fa3). Not relaunched:
LutList2 (Prelim deletion needs B and C in one commit; patches stay in Wip/LutList2).
tools-A/snap.sh: lock refresh + WIP snapshot every 40 min (A files only).
### progress 07:43
Fid3 done (no Lean; iverilog/Float experiments on research 6524fa3, notes/A-fid3.md, rerun:
tools-A/glsdiff3/run-1029/run.sh): CARRY4 and latch early edge FIXED under GLS_MODEL=fid
(78de9c2; multi-pin CARRY4 60/60, default model 2/60); flop still reads x on SR/CE as 0 in both
models (research's new tb_f3_kleene_ff now requires it), latch X still pessimistic (harmless:
no design uses LDCE/LDPE); FID_RESOLVE still decides at exactly TLOOP - WIN/2; a Float
transcription of the involution OR loop puts the critical width at 0.50-0.58 TLOOP and shows a
pulse train while resolving (not a theorem). Tested patches for research in run-1029/patch/.
FEASIBILITY fidelity table replaced (6524fa3), FOR-RESEARCH §6 FIXED-for-fid, §7/§8 updated.
**For shard B:** does bd_arbiter's A0 hold tolerate the involution pulse train on q
(A-fid3 §3)? Next probe launched: InvLoop (the symmetric fixed point s* and unbounded laps
near it, in Lean).
### progress 08:01
GLSPass2 claimed: Formal/Core/Delay/{GLSFid,GLSPass2}.lean (check.sh, autoImplicit=false:
249 decls, [check] OK; Lean core only). GLSFid transcribes research 6524fa3's fid LUT channel
(fid_core.vh:122-227, prims.v:51-54,112-132): per-pin transport then the zero-time mux tree
(= INIT lookup for every INIT), +1 ps sampler; cross-checked against iverilog on the unmodified
source. GLSPass2: a fid run is one band behaviour; acyclic nets: past an STA horizon one run
gives the final values for the whole band (nothing before it); acyclic monotone nets with
rising inputs: the all-min and all-max runs bracket every band behaviour (existence of the two
corner runs assumed, not proved). Counterexamples: XOR with two pins at different points of
the band glitches for hi-lo while every consistent-corner run passes -- NOTE this is in the
independent per-arc band; under the κ corner model the glitch is bounded by the local scatter
only, not claimed here; AND with a falling input breaks bracket; a buffer with rise ≠ fall
loses a w-ps pulse that every fixed-delay fid run passes. Not covered: resolver trace
semantics (probe GLSResolve launched), CARRY4/FF/latch fid variants, feedback, real time.
Finding: a "rejected" runt on a state node is still emitted as a full-swing pulse to fanout
(fid_core.vh:30's comment is about the node's later value). For B: B-gls-vs-exact.md §3.1 is
stale (CARRY4, flops, latches and BUFGCTRL have fid transport variants at 6524fa3).
### progress 08:11
PrimsComb claimed: Formal/Core/Prims/{Xray,XrayData,Muxf,Carry,Lut62,Hops,GenCheck}.lean
(check.sh with C's CoreLut/Gen.Netlist as deps: 1331 decls, [check] OK, Lean core only; rerun
by the lead). Delay numbers generated (Wip/PrimsComb/xray2lean.py) from prjxray-db master
zynq7/timings/slicel.sdf/slicem.sdf (sha256 in XrayData; fast/slow corners, one corner per
statement; --check reports DRIFT after a mutated number). Proved: MUXF7/F8 Kleene mux (under
H_MUXF_PASS, constant transport per arc) monotone, X-containing, most-defined; select change
with equal data and any single-input change with unchanged output glitch-free for any delays;
the select-rises-while-deselected-input-changes glitch is forced for every admissible delay
pair (>= 16 ps fast / 22 ps slow; select arc slowest of all six muxes). CARRY4 (MUXCY+XORCY,
PRECYINIT mux): Boolean agreement, X containment, adder with S=a^b, DI=a (512 cases); no
single-pin hazard on any output; a two-pin (S0, DI0) hazard on CO0 whose order prjxray's bands
allow at both corners. LUT6_2: A6-rooted tree = Core's Lut62 for every INIT; O5 the lower
subtree. Site hops add per corner; a5lut->AMUX (62::78)(163::202) ps (the E8Mux audit
number). Equal to C's Gen models except one benign mismatch: C's carry-in is CI OR CYINIT,
silicon a PRECYINIT mux; equal under every decoded configuration (C-11f tie-off). Census:
gcd_hw uses LUT6_2, 857 MUXF7, 343 MUXF8, 59 CARRY4; collatz/xorshift/ipow use MUXF7 and
CARRY4 (from C's tcheck census, counts not exact here); ipow uses DSP48E1 -> probe PrimsDSP
launched. Not covered: slews, charge sharing, pulse filtering, CARRY4 internal stage timing,
LUT-tree per-rank skew. Mutation control: Lean half not run.
### progress 08:26
InvLoop claimed: Formal/Core/Delay/InvolutionLoop.lean (check.sh, Mathlib
Archimedean.Real only: 197 decls, [check] OK). Model: B's OR loop (zero-time OR of a runt
[0,s) with q, one InvolutionPair channel); the pulse-width ORBIT recurrence (B's orb copied),
not yet every signal-level solution (that is InvLoop2's bridge). Proved: half-lap maps strictly
decreasing and expanding; a stationary train (h, l) exists and is unique for every involution
pair; critical runt s* = δ∞↑ − l is the only width in (0, δ∞↑) that never cancels
(crit_unique); wider latches (pulses grow by a fixed c per lap), narrower dies; for every N
and ε there are runts within ε of s* on each side that take > N transitions, and for every
time B a latching runt whose last q edge is after B (digital metastability: unbounded
resolution time). Symmetric channel: duty exactly 50%, s* = δ∞ − w* with 2w* = δ(−w*), so
s* > δ∞/2 strictly (the goal "s* = δ∞/2" was wrong; corrected). Asymmetric: exact iff for
which side of δ∞↑ − (h+l)/2 s* lies. Float evaluation of the formula reproduces A-fid3's
0.500-0.581 TLOOP spread. Not covered: rate law, noise, multi-cell loops; reading TLOOP as δ∞
is a modelling choice. Correction pending (InvLoop2): A-fid3 §3 item 3's skew direction is
wrong in this model (slower rise moves s* up; Float only). InvLoop2 launched (signal-level
bridge to B's loop_orb/arb_eternal, rate law; needs Mathlib Topology oleans).
### progress 08:35
GLSFix done -- answers the audit's GLSPass REFUTED row: one-line fix, skew_fval {p w} -> {d p w}
(binds exactly the implicit autoImplicit added; the lemma holds for every d since skewA d w's wire
delays do not depend on d); check.sh 263 decls OK under autoImplicit=false. Sweep: all 79
Mathlib-free Core modules plus their 8 dependencies in B/C re-elaborated from source with
-DautoImplicit=false in one check.sh call: no error; 5934 library decls + the 9 XAudit executables
audited clean. Not covered: the 18 Mathlib-dependent Core modules (the lake build covers them once
Mathlib is built) and this session's new Core files (each probe's check.sh run is their check).
GLSPass reinstated in FEASIBILITY, GLSPass2 added.
### progress 08:35
InvTrace claimed: Formal/Core/Delay/InvolutionTrace.lean (check.sh with Pure/Involution/
InvolutionTransfer/InvolutionDMin: 321 decls, [check] OK). The IDM channel as a trace map
channel : List R -> List R (the non-forgetful algorithm of Fuegger/Nowak/Schmid as a fold; T measured
from the previous tentative output even if cancelled), proved equal to a declarative survivors
semantics (channel_eq); no transition cancels twice. Agreement with InvolutionTransfer under the
exact separation threshold; single pulse cancelled iff width <= dinf_up - dmin, else the output
width law with strict monotonicity; output strictly increasing, alternating, same final value,
each output in its window; ratPair examples incl. a cancelled runt shortening the next delay
(89/13 vs 7 for a forgetful channel); exp channel over an abstract ExpLog: cancelled iff
width <= tau ln 2. Not covered: gates/feedback (InvLoop2), simultaneous transitions, the equality
case at the threshold (paper text unreadable here; affects only the exact threshold), eta-noise,
the real exp/log instance (Wip/InvTrace/ExpReal.lean, needs Mathlib Log oleans).
### progress 08:38
PrimsSeq claimed: Formal/Core/Prims/Seq{Next,Flop,Latch,Xray,Gls,Sync}.lean (check.sh: 845 decls,
[check] OK, Lean core only; rerun by the lead). Census: gcd_hw's core has no flops; FDRE/FDSE only
in the rig, bd_flink (not emitted by bdc) and arb_mtbf; FDCE/FDPE/LDCE/LDPE in no design; ipow's
DSP48E1 combinational (AREG=0); RAMB18E1 in bd_mem (probe PrimsRam launched). FlopRel: each input
read over its own setup/hold (recovery/removal) window, X if not constant there; Kleene next state
(R beats CE); Q old until cqLo, merge inside the CK->Q band, new after cqHi; on a violation X up
to cqHi+res then one definite unspecified value (res = named H_FF_RESOLVE; no MTBF). Proved:
capture/hold/reset, X only in the window and contained after cqHi+res, a D change inside its window
really gives X, power-up INIT, CLR priority, non-vacuity (sim_rel); latch transparency/hold/X
containment; two-flop synchronizer output definite (sync_two_flop). GLS counterexample: research's
SLICE_FFX has a violation-free run with Q=0 where every Kleene run has Q=X (completion CE=1 gives 1).
Findings: prjxray-db ships no fast-corner setup/hold (makesdf writes SLOW only) -> named
H_WINDOW_SLOW_ONLY; fast CK->Q min 112 ps vs slow-only hold 241 ps (fast_hold_mismatch); research
GLS treats SR as synchronous only (no impact: no FDCE/FDPE used). Not covered: clock runts/min pulse
width, resolution time (parameter), latch G/GE pins, X on a latch gate, CLR runts.
### progress 08:44
PrimsDSP claimed: Formal/Core/Prims/{Dsp,DspData,DspTimed}.lean (check.sh with Xray: 700 decls,
[check] OK, Lean core only; rerun by the lead). ipow (K3's routed build, nextpnr 9c732bc6): 6 DSP48E1
= 2 multiplies, each a 3-DSP cascade of 17-bit slices, all *REG=0 (combinational), INMODE/ALUMODE/
CARRY* = 0, OPMODE X=Y=M with Z per DSP (0, PCIN>>>17, PCIN); netlist->Lean transcription by hand
(13 fields). Proved: ipowMul_eq -- the cascade under UG479's function of this mode = (a*b) mod 2^32
for all a, b (algebra); coarse X model (any X input bit -> every output bit X) sound for every gate
network computing the function, and the most defined such; the sharper low-bits rule needs
H_DSP_LOWBITS (a Booth cell breaks it). Timing under H_DSP_LUMPED (one lumped stage per port,
anything during settling): sampling at/after settleHi reads C's product, tight to 1 ps; prjxray
with zero cascade wire: settleHi 7267 ps slow / 3074 fast. Finding: nextpnr's routed SDF is not
an arc-by-arc upper bound (B->PCOUT 3850 vs prjxray 3851, PCIN->PCOUT 1710 vs 1713) and gives 5400 ps
A->ACOUT vs prjxray <= 723. Not covered: H_FASM_DSP (bitstream config), cascade wire delay,
fabric routes to A/B and from P, kappa, capture-latch setup, other modes. Lean half of the
mutation control not run.
### progress 08:46
XSound2 claimed: Formal/Core/{XSimChan,XSimChanReal,XSimChanTern}.lean, Formal/Core/XAudit/
{SoundCells,SoundPhys,SoundChain,SoundSteps}.lean (check.sh with Design/Fast/Untimed/Parse as deps:
1470 decls, [check] OK; SimChanReal/SoundPhys/SimChanTern use Mathlib). xaudit's verdicts are sound for
continuous time: any time type with a cell map (abstract step k covers every instant of cell k),
every gate = INIT function then a ChanCells channel with lo >= 1; for R time with cells of width q:
transport covered when lo*q <= Lo and Hi <= hi*q; bounded inertial (reject window rho) covered iff
rho <= (hi+1-lo)*q (necessity: inertial_wide_not_chanCells; one-buffer cex: simulator prints 1, the
inertial behaviour is 0). valF/noXF/constF/settledF restated as continuous-time theorems under
SatPhys. Parser: lo*u <= L whenever u <= L; a 'raised' arc (L < u) is NOT covered. SoundChain closes
Wip W1 (covered-window sound_postfix under Stale; phase gaps >= (n+1)D). Finding: notes/A-xaudit.md's
fidelity row 'no inertial filtering modelled is sound' is FALSE (an inertial channel holds an old
value after filtering; InertialCex) -- so a clean xaudit run does not imply a clean inertial
(Verilog-default) GLS; correction and an inertial xaudit option are probe XInert. Wip/XAudit.lean
chain_phases has an off-by-one (by inspection; superseded by SoundChain). Not covered: involution
channels, per-pin skew inside a LUT, mid-cell input changes, what D is.
### progress 08:50
InvLoop2 claimed: Formal/Core/Delay/InvolutionLoop{Bridge,Signal,Rate}.lean (check.sh with B's
CElemInvolution/ArbInvolution as deps: 994 decls, [check] OK; Mathlib). Bridge: A's orbit = B's orb,
B's Osc <-> all widths positive, any eternal gap = s*. Signal level (arb_trichotomy), under B's ALoop
hypotheses, 0 < s < dinf_up and the stationary train: for EVERY solution of the arbiter loop q is
eventually 1 iff s > s*, eventually 0 iff s < s*, oscillates after every time iff s = s*; arb_threshold
builds the train itself and shows a solution exists for every gap; B's arb_eternal gap = dinf_up - l*.
Rate law (slope bounds kappa <= delta' <= K on the channel): first-cancellation index m between
log(g/|s-s*|)/log(1+K) - 1 and log(max dinf/|s-s*|)/log(1+kappa) (power form in Lean); B's QuantHyp
holds at A's s* (quantHyp_of_stat), and laps_upper is new (B has no upper bound). Not proved: that a
real LUT+route satisfies the slope bounds (kappa = 0 gives no upper bound), noise, multi-cell loops,
InvTrace's channel as the loop semantics (B's loop_orb used instead; reason in notes). A-fid3 §3
corrected (skew direction; proved forms cited).
### progress 08:52
E8Mux done (no Lean; the unchanged xevents8 rerun on corrected bands) -- answers the audit's Events8
OVERSTATED row: CONFIRMED, seed d gb fails ENTRY on 2 pins, not 3. Cause: research xray_delay 99b10a6d
charged the slice OUTMUX hop only on O6/COUT exits; every O5, MUXF7/F8, CARRY4 O/CO and x5FF exit got 0.
Fix tools-A/xaudit/e8mux/xray_delay_e8mux.py (prjxray ROUTING_BEL hop, e.g. a5lut->AMUX 62/78/163/202 ps;
unknown OUTMUX source = hard error; equals research 7dc5dde on all 40,083 comb->comb arcs; OUTMUX numbers
equal Core/Prims/XrayData to the ps). Toolchain restored (toolchain.sh 9/9, nextpnr 9c732bc6303458df), 4
seeds rebuilt, all 8 md5s = events5/builds.txt. d gb: RESIDUAL 3 -> 2 (merge3.uarb1.ua2 -51, merge2.uarb1.ua2
-68 still fail; merge3.uarb1.ua1, an O5 guard, passes at ENTRY >= 41; auditor +45); slow/fast CLEAN on all
seeds; indep residuals 21/30/19/22; not uniformly favourable (some indep Line margins 4-78 ps worse). lo>hi
band rows now rejected by routed2x (or hulled with --inverted hull, reported). Negative controls fail as
required (NEGmux restores -94 exactly). notes/A-events8.md corrected (line-74 claim wrong). Open: Parse.toSteps
still narrows lo>hi to [lo,lo] (asked XInert, which owns Parse.lean now); events5-7/9, kapres, xaudit-gcd
results rest on the old bands and need reruns (HDsub and KapRes2 told).
### progress 08:55
GLSResolve claimed: Formal/Core/Delay/GLSResolve.lean (check.sh with GLSFid: 665 decls, [check] OK,
Lean core; file md5 unchanged between check and commit). FID_RESOLVE (research fid_core.vh:47-119 @6524fa3)
as a per-step state machine on bd_c2's single-cell loop (binary, xmode=0, feedback = o delayed TLOOP,
FID_LEVEL_PS=0; draws and resolution law free, so for every seed/TAU; runs exist and are unique). Proved:
a rejected runt is emitted full-swing; a commit with trp>0 gives two rising edges; a run with no RUNT/META
line = B's CElemTiming.Loop at that point (noRunt_loop), and B's four-phase hypotheses imply the resolver
never fires; seed dependence for every runt; hides_oscillation; follow_lost (a following wide pulse ending in
the ignore window is lost forever, vs B's c2_follow_hold). The resolver silently assumes an environment
hypothesis B does not have (no input change that vanishes within trp+TLOOP+1 after a runt). iverilog on the
unmodified sources: 480/480 pulses match; META_OFF control 10/12 mismatches. Not covered: X/META_X, multi-cell
loops, other cells (GLSResolve2 running), FID_LEVEL_PS != 0. FOR-RESEARCH §8 extended.
### progress 09:23
PrimsRam claimed: Formal/Core/Prims/{Ram,RamXray,RamBd}.lean (check.sh with Seq* deps: 1018 decls, [check] OK,
Lean core; my first run failed only because I omitted SeqFlop from the dependency list). RAMB18E1 as
bd_mem instantiates it (checked against cells/rtl/bd_mem.v: TDP port A x18, port B tied off, DOA_REG=0,
WRITE_FIRST, 1024x16, no INIT). RamRel in SeqFlop's style: per-pin windows, Kleene address decode
(H_BRAM_DECODE_KLEENE), X only on words consistent with the sampled address and bits where old/new differ,
never resolved until a clean access. Proved: Boolean agreement + soundness; correct write/read/write-then-read
with clean windows; WRITE_FIRST read-during-write returns new data; X containment; data/WE change inside
its window gives X; non-vacuity. Bundled-data obligation at one corner: req->CLKARDCLK >= payload + setup
(bd_mem slow: +737 ps DI) and ack > clock wire max + 2454 ps CLK->DO (fast +1098); necessity of the ack
condition by an admissible counter-placement. prjxray gaps: slow-corner windows only; TDP data only for the
upper RAMB18 (H_BRAM_LU_SAME); no min period (H_BRAM_PERIOD). Census: no kernel in kernels/ and not gcd_hw;
only testbenches/board rigs. For FOR-RESEARCH: cells/sim/bd_prims_sim.v's RAMB18E1 has no hold check, one
2454 ps point and does not poison on setup violation despite its header. For B: MemPort (LibEndMemMlink)
measures dcLo from the clock rise with <=; the real obligation needs the ram_clk-to-pin route max and <.
### progress 09:24
E8Hyp claimed: Formal/Core/XAudit/Events8Bridge{,Sel}.lean (check.sh over the 35-file Mathlib-free closure:
2926 decls, [check] OK). Partial discharge of design_verdict8's hypotheses (mapping table in
notes/A-e8hyp.md §2): SelOK bridged at every real filtered pin from B's LibGapSteer.steer_pin_ok
(design_verdict8_sel; the select wires' stability and the hold half stay open -> probe E8SelC); SelPart
discharged by construction (selPart_of_value); reset/time origin bridged by satPin_shift (gaps: no map from
B's gNet to A's d; B's reads not monotone). Mismatches with exact gaps: SatPin is the model itself (A's
channel is a B/C WinDelay but not conversely: win_origin_gap, win_overtake_gap; no map from d to C's FASM
netlist); H_ARB (HARB7) is not implied by any B/C theorem and needs 'never contested' (B's
arb_grants_eternal and A's arb_trichotomy show a contested arbiter can pulse forever) -> probe E8Arb.
Joint satisfiability: SatPin + constants + reset jointly satisfiable iff the netlist has a reset fixpoint
(Lean); untrusted fix0.py: 1747/1747 LUTs definite under rst=1 on all 4 seeds (no-rst control 0/1747).
HARB7+SelOK+HDsub jointly on one gcd_hw run: not shown; nothing found jointly unsatisfiable.
### progress 09:25
**E8Arb: negative result on the gcd_hw routed-timing verdict.** H_ARB as encoded (HARB7, the virtual
arbiter core in events4/model.py and cert6/cert8) is FALSE on real uncontested bd_arbiter runs:
Events8Arb.unc_not_harb (real INITs in A's per-pin semantics, B's ArbBinary read-only) gives a handover
trace, uncontested for every window W, with exclusive grants, that the virtual core cannot match -- D1:
the virtual R0 is the OR of the grants read after them, the real R0 = r1 q + r2 ~q is computed in ustate
from its own q read and can rise before the grant; D2: the virtual grant is 2 steps late (cert8's lo_c does
not subtract the two (1,1) bands). noFree_not_harb: C's untimed 'uncontended' (Unc 0) is not enough (a
contested runt trace pulses g2 forever with C's predicate true). Untrusted numbers: D1 outside the virtual
band on 11-18 of 18 grant->R0 pairs per seed/corner; E8Hyp's sim0 run violates HARB7 (R0 453 ps before
g2), so it is no witness. Consequence: design_verdict8/9's CLEAN rows currently cover no real run. Lean
file being checked; FEASIBILITY, gcd_hw_hypotheses and A-e8hyp corrected. Probe E8ArbFix launched
(corrected core, sufficiency theorem ArbOK + Unc W + RT1/RT1b => HARB7', reruns). No contested gcd_hw
schedule was found (weak evidence).
### progress 09:26
E8Arb claimed: Formal/Core/XAudit/Events8Arb.lean (check.sh with Events/Events2: 879 decls, [check] OK).
Precise reading of unc_not_harb: there EXIST arbiter bands B and a real-cell behaviour (ArbPin B, real
INITs), uncontested for every W, with exclusive grants, that no VMerge (any bands with loF+lo >= 1) matches
and that no VGrant with loF+lo = 4 matches. So the counterexample is at one admissible band choice; that
gcd_hw's actual arbiters are affected rests on the untrusted per-seed numbers (11-18/18 grant->R0 pairs).
Wip/E8Arb/Sufficiency.lean (with sorry) is not claimed.
### progress 09:32
K3 done (no Lean; routed-model results, not silicon): xevents8 (and xevents5) on ipow and xorshift, toolchain
9/9, nextpnr 9c732bc6303458df, --freq 100, one nextpnr at a time, md5s in tools-A/xaudit/k3/out/builds.txt.
ipow seeds d/3/4/5 (all audits pass): CLEAN on all 12 slow/fast/gb rows; indep residual 7/9/12/1 (all timing
margins). xorshift: seeds 4/6 did not place, 3/7 fail rule A (and 3 rule I) so are not results; d/5/8/9: 5/8/9
CLEAN at slow/fast/gb, d RESIDUAL 2 at all three -- both the rig's uenv0/uenv1 C-element pair, not the kernel;
indep 8/9/9/10. GuardOK not assumed (12/12 guard certificates). Negative controls rejected (entry/exit sized to
60000 ps for ipow's large margins). Caveats: (1) these are design_verdict8 instances, so they inherit H_ARB, now
refuted in its current encoding (E8Arb) -- the CLEAN rows cover no real run until E8ArbFix; (2) the event checker
does not see data bundling (rule-A-failing seeds are CLEAN here), so it does not replace the cells/ gates; (3)
ipow's DSPs are cut (--cut-type), the datapath is not covered. Finding: the rig's directly coupled env
C-elements (uenv0/uenv1) are the weakest control element across four kernels (model-level margin, not a
demonstrated race). HOWTO-new-kernel.md rewritten around k3/ and xevents8.
### progress 09:47
HDsub claimed: Formal/Core/XAudit/Events9{Cert,Beh,Main}.lean (check.sh over the 34-file closure: 2743 lib +
2829 exe decls, [check] OK; NOTE: checked against XInert's uncommitted additive edits to Parse.lean (+2 decls);
to be re-verified by check.sh --committed once the lake build finishes). HDsub is no longer a hypothesis:
rule dsub9 (a dsub line must cite an unlabelled S->D walk with <= 1 token), first_reach by strong induction on
time, dsub9_sound, hdsub_san; design_verdict9 = design_verdict8 without HDsub. The 2026-10-28 snapshot had a
real bug (dsub9_sound's monotonicity step had its arguments reversed), fixed without changing statements. Runs
(xevents9 via lake env lean --run): old bands 16 rows, 126/126 valid wS on every row, 11 CLEAN (same residuals
as Events8: margin failures, not HDsub); xevents8 rerun byte-identical to committed; E8Mux bands: A-e8mux's NEW
table exactly (d gb RESIDUAL 2). Controls NEGwsEnd/NEGwsTok/NEGwsMissing/NEGnows rejected, POSws1 accepted. A
CLEAN row now rests on SatPin, constants/reset, H_ARB, SelOK, SelPart -- and H_ARB is refuted in its current
encoding (E8Arb), so no real run is covered yet. lakefile stanza for xevents9 added.
### progress 09:47
GLSResolve2 claimed: Formal/Core/Delay/GLSResolveGen.lean (check.sh with GLSFid/GLSResolve: 979 decls, [check]
OK; md5s unchanged between check and commit; GLSResolve.lean untouched). GRun: the resolver on any single-cell
loop (feedback pin k of a fid mux tree); bd_c2's Run is an instance (run_iff_grun); bd_c2n and the arbiter's q
(ustate O6, equal to B's held_q_eqn) instantiated. seg_window_end makes fid_core.vh:36-37 precise. **Finding:
arb_double_ack** -- under the resolver, a near tie (r2 < TLOOP after r1) that commits late, with A0 reaching
ua2/ua1 inside the commit gap, acknowledges BOTH clients for one server transaction (A1 = A2 = 1 while A0 is
high), with exclusive grants at every instant and no X, so no check flags it; arb_gap_closed: if A0 arrives after
the gap, A2 stays 0 for every draw. Outside B's exclusion rows (the near tie violates H_REQ_SEP; bd_arb.v's
'metastable q' tier), but bd_arb.v's 'one loop delay' consumer rule is met and still fails: under the resolver it
needs trp_max + TLOOP. Lost follow: tolerated only argued. late_runt / late_runt_B formalise the iverilog-only
effect. iverilog (unmodified research sources): arbiter 120 runs 0 mismatches, 12 end A1=A2=1; late runt 160/160;
controls fail. Not covered: X, FID_LEVEL_PS != 0, multi-cell loops, closed-loop server, ugrant pin skew; how
often this can happen in gcd_hw (needs a near tie and a server answering within trp <= ~647 ps). For B: no
bd_arbiter row bounds the q node's resolution time.
### progress 10:27
E8ArbFix done (Lean check pending: Events9Arb.lean, Events9ArbBeh.lean). **Negative: with the corrected arbiter
core no gcd_hw row is CLEAN.** E8Arb's §4 fix was itself insufficient (shadow grants reading ctl through one (1,1)
pin do not fix D1: R0 and the grant read q over arcs hundreds of ps apart), so every virtual node now has F=Q=(1,1)
and the whole read sits in per-reader pin bands (K = min(Dq(g1),Dq(g2),Dq(R0)-2)-2, ...). Lean (claimed after check):
core_of_settle -- the real bd_arbiter (per-pin model, real INITs) is a behaviour of the corrected core under a settle
bound H and per-reader B1 (RT1/RT1b), B2 (rise protocol), C (fall protocol); non-vacuous (ho3_fix), and no old-core
behaviour (settle_not_old). Pipeline (xevents9, E8Mux bands, 16 rows): old mode byte-identical; corrected core
RESIDUAL >= 54 on every row -- 54 structural (6 per arbiter x 9: grant ctl-pin Back, shadow request-pin Back, A_b
guard walk), all relying on 'R0 is a merge of the grants', which is false for the real cell; closing them needs a
lower bound on the grant's count from the shadow's, which no log rule gives. All 830 real Back pins certified as
before. Recorded runs: old core wrong on 54/64 (N1) runs, corrected core 576/576 arbiter-runs match, mutations
caught (31/576, 128/576). model.py now builds the corrected core by default (XA_ARB=old for the old one). Probe
E9Par launched (liveness rule for the shadows).
### progress 11:04
InvExp claimed: Formal/Core/Delay/InvolutionExp.lean (check.sh with the involution chain: 1227 decls, [check] OK;
Mathlib Log/Sqrt). expR: a real exp/log InvolutionPair, delta(T) = T_p + tau ln(2 - e^{-(T+T_p)/tau}) (= the paper
form delta_inf + tau ln(1 - e^{-(T+delta_inf)/tau}), expR_paper), delta_inf = T_p + tau ln 2, dmin = T_p; a pulse is
cancelled iff width <= tau ln 2. **The formula in my probe brief was not an involution** (bad_not_involution, for
0 < T_p < tau ln 2); I wrote it from memory and the paper's full text is not reachable here. Stationary train in
closed form w* = tau ln x, x = (sqrt(1+8e^{T_p/tau}) - 1)/2, unique, 0 < w* < T_p; s* = T_p + tau ln(2/x). Slope
bounds kappa = q/(2-q) (q = e^{-T_p/tau}) on (-delta_inf, 0] and K(M) = r/(2-r) on [-M, inf) (no global K: delta'
blows up at the domain edge); laps_two_sided instantiated with every hypothesis discharged (exp_laps, exp_laps_log,
exp_resolution: for s != s* the first cancellation index m exists and is odd iff s > s*). Numeric table (Float,
the model, not silicon, TLOOP 424 ps read as delta_inf): time per e-fold of 1/|s-s*| 42460 / 1728 / 514 ps at tau
40 / 100 / 200 ps, matching A-fid3's TAU_eff by a second method and 3.4x-280x the research GLS's TAU = 150 ps. Bounds
are loose (global minimum slope, not the local gain).
### progress 11:10
Claimed after one consolidated check.sh over the XAudit closure (3690 lib decls + Events9Main 2829 + Events9SelMain
3461, [check] OK; md5s unchanged between check and commit; NOTE: checked against XInert's uncommitted additive
edits to Parse.lean, re-verify with --committed after the lake build):
- E8SelC: Events9Sel{,C,Hold,Split,Main}.lean. design_verdict9_sel (SelOK at real pins from B's stability/setup);
  design_verdict9_selC (stability from C's H_BUNDLE through a checked channel map chanOf/entOK; 126/126 select
  literals map on all 4 seeds; name matching to C's channels is untrusted mkmap.py); hold rows holdBand/holdBandS
  proved = B's H_HOLD_PIN; with H_ACK_LAG -> design_verdict9_selH/selS. Results (E8Mux bands; Lean and Python agree):
  split rows CLEAN on all 12 slow/fast/gb rows (min 411 ps) and indep seeds 4/5; indep d and 3 have 2 residual
  literals each (-47/-56, -124/-4 ps, steer-ack merge pins); source-anchored rows fail gb 3/4 and all indep.
  Controls NEGhold/NEGmap fail as predicted. Finding NEGack: chainOK does not authenticate the ack wire. xselhold
  exe stanza added.
- E8Causal: Events9Prefix{,Sel,Ext}.lean. safe8_upto / design_verdict9_upto (prefix verdict, lag 0), the all-times
  theorems re-derived as corollaries; causal_close; design_verdict9_selL replaces H_ACK_LAG by checked rows
  ackOK/ReqLine/AckLine at a SOURCE-anchored lag (not yet generated or run: probe E9SelRun). Finding
  sibling_lag_neg: E8SelC's split lag does not follow from causality for tokens routed to the sibling branch (min
  over arms needed) -- the split rows rest on a named hypothesis, not a causal consequence. Beh7P/ext/link_upto_P
  for the arbiter side; design-level prefix H_ARB still missing.
- E8ArbFix: Events9Arb.lean (core_of_settle: the real bd_arbiter is a behaviour of the corrected core under a
  settle bound H and per-reader B1/B2/C; ho3_fix non-vacuous; settle_not_old) and Events9ArbBeh.lean (HARB7' =
  HARB7 and FixShape, design_verdict9arb).
### progress 11:14
KapRes2 claimed (partial): Formal/Core/Delay/CornerCell.lean (Mathlib, 23 decls) and Formal/Core/XAudit/BandCheck.lean
(32 decls) -- check.sh with Design/Parse: 1672 decls, [check] OK (Parse checked as on disk incl. XInert's edits).
cell_band (A-kapres's cover lemma, now proved, without 0 <= ca / cb <= 1): every delay the corner model allows at any
corner in [ca,cb] lies in cornerband2.py's integer band; cell_band_nat for CornerNat; cover_mem. readBands =
parseBands behind jsonBandsOK: accepts exactly the checked files, then nothing dropped or narrowed; lo > hi rejected
(control: parseBands reads [202,105] as [202,202] silently); on real data it rejects the committed seed-d fast file
(20 inverted arcs) and accepts all 221 sweep files. Sweep (Events8Main, OLD arbiter core pinned with XA_ARB=old;
E8Mux bands): discharged on all of c in [0,1] by a cell cover for every seed at kappa = 0 and seeds 3/4 at kappa <=
0.06; seeds d/5 above 0 undetermined (cover unfinished; every point corner passes at 0.06). Point-corner failures:
d guard ENTRY merge2/merge3.uarb1.ua2 at 0.10/0.12; 5 rig uenv1 at 0.10/0.12 (0.08 at c=1, -2 ps); 3 one grant line
at 0.12, c=1; 4 none; none at kappa <= 0.06. All inherit Events8's hypotheses incl. the refuted HARB7. Todo: switch
Events*Main to readBands (one line each).
### progress 11:24
XInert claimed: Formal/Core/XAudit/SoundInertial.lean (new) and additive edits to Parse.lean/Main.lean (check.sh
with the XSimChan/Sound chain: 1273 lib + Main 1116 decls, [check] OK; md5s unchanged). xaudit gains an inertial
option (band key 'inertial', CLI --inertial widen|check --rho*): widen sets hi' = max(hi, lo + ceil(rho/u) - 1),
check refuses with exit 4; without the option output is byte-identical (5 small cases). Parse.checkedSteps rejects
lo > hi ('NOT RECOGNISED') -- the one non-additive edit; checkedSteps_ok/_inverted, toSteps_hi_ceil (no
narrowing). Proved: gates transport or bounded-inertial with window <= rho inside their step band => widened
design meets SatPhys, so noXF/const/fixpoint verdicts hold at every real instant (noXF_sound_inertial);
Verilog-default inertial covered (gateOK_verilog); widening happens only in the case XSound2 showed unsound
(widened_wide). Results: pipe3/ring3 unchanged at rho 15/50; gcd_hw seed d (E8Mux bands): rho 15 passes check
everywhere, rho 50 keeps the smax w0/w0.02 certificates, rho >= 75 loses smax w0 (likely window imprecision, not
sampled); the rho = delay-on-every-gate runs were killed (too slow), not results. Caveat: 2334 gcd arcs are raised
to 1 step, so no gcd verdict is covered by the continuous-time theorems at any rho (discrete model only). Fixed
tools-A/xaudit/build.sh compile order (Design before Parse). notes/A-xaudit.md fidelity row corrected.

## Session Sat Oct 31 07:13:39 UTC 2026 (shard A, lead; session_01HC49FvHJFQrSnLiAaBNpDZ)
### progress 07:13
Previous A lock 42 h old (session_01HC49Fwiv93CFgTH6CuFfLh, 2026-10-29 13:18), taken. That
session's last commits are WIP snapshots (Wip/_snapA); nothing in them is claimed. Fresh
sandbox: setup.sh running (Mathlib from source again, ~2 h). Audit read at pass 13
(formal 5a1ee8d2). Rows on A's files and what I did:
- **Events9Sel/Arb + FEASIBILITY (P12c, OVERSTATED, no gcd_hw run verified CLEAN).** Agreed.
  FEASIBILITY corrected: the old 'CLEAN on all 4 seeds' paragraph (§4b) now says it verifies no
  real run (HARB7 false, corrected core gives no CLEAN row); 'Lean check pending' on
  core_of_settle replaced by the audit's reading (q free, settle bound may be ~1e12, adds no
  soundness to design_verdict9arb); 'SelOK from C's H_BUNDLE' reworded (H_BUNDLE-shaped
  hypothesis on A's own wires; entOK only checks a buffer route exists).
- **Core/Prims/Seq (53d5cc9 P10b, OVERSTATED: windows SLICEL-only).** Confirmed: prjxray
  slicem.sdf REG_INIT_FF HOLD DIN (0.211::0.262) > SLICEL 0.241. Fix (pending check, Lean not yet
  built): SeqXray gains regFFM/ff5M/latM (SLICEM, hand-transcribed from prjxray-db master
  slicem.sdf; that master's slicel.sdf reproduces every SLICEL number in the file, so same db),
  site-selected regFFAt/ff5At/latAt, _ok lemmas, slicem_hold_longer, fast_hold_mismatchM; site type
  is the named hypothesis H_FF_SITE. The second half of the row ('X then definite' restates the
  free res) is now said in FEASIBILITY.
- **CornerDiff.diff_not_imp_scat (P13, witness degenerate).** Agreed. Ported the auditor's
  diff_not_imp_scat_strong (credited) and added diff_not_imp_scat_degenerate (pending check).
- **Fid3 remark (1fefbc0, REFUTED direction).** Already corrected in A-fid3/A-inv-loop on 10-29,
  but the wrong formula survived in out/FOR-RESEARCH.md and notes/A-gls-compare-2.md: fixed.
- **XInert (550e5b27, 'Verilog default' mildly overstated).** Agreed: one symmetric delta only (no
  rise/fall, X/Z or PATHPULSE band), and under rho = full gate delay the seed-d smax_w0 certificate
  is lost (it was in notes/A-xinert.md, not in the journal; now it is).
### progress 07:19
Lean 4.35.0 installed; Mathlib still building. Mathlib-free modules checked with plain `lean
-DautoImplicit=false` into a scratch olean dir over a copy of the tree (/tmp, not lake; same
toolchain and sources) plus check.sh's axiom-audit script. **Claimed** (all axioms standard,
scan.py clean): SeqXray (SLICEM windows, from the previous entry) and the 14 Events9 files the
2026-10-29 session left only in Wip/_snapA (it died before claiming them), copied unchanged:
- E9Par (Events9Par, ParBeh, ParRst, ParMain; notes/A-e9par.md, DONE there): log rule `par`
  for parallel virtual C-elements, `design_verdict9par` with named HRst. Its run table (10 of 16
  rows CLEAN on the corrected core) is from 10-29 and was not re-run; those rows still rest on
  HARB7', HRst, SatPin, constants/reset, SelOK, SelPart.
- E9SelRun (Events9SelL, SelLMain, SelJ; notes/A-e9selrun.md): design_verdict9_selT / selJ.
- E9Setup (Events9Setup, Full, FullMain): design_verdict9_full, one realisation for the corrected
  core + junction select rows + setup rows. No run table committed.
- E9ArbNet (Events9ArbNet, ArbNetRows, ArbNetEdge, ArbNetMain): design_verdict9arbnet replaces
  HARB7'/HRst by decidable per-arbiter checks (ArbOK 9/9 on the 10-29 runs) + trace conditions
  ArbCond; arbCond_of_edge reduces ArbCond to decidable rows ArbRowsOK + edge-window hypotheses
  (QClean = no metastability, quiet start, settle bound H, per-reader no-re-request/settled/A0-high
  windows). The printed B1 rows fail on 3 arbiter readers at seed d slow (-2, -190, -32 ps).
  NOT proved: that the printed rows imply the edge windows; nothing joins ArbNet to Full.
So no gcd_hw run is verified yet: the arbiter half now rests on ArbEdge instead of HARB7'.
Next: compose design_verdict9_full with design_verdict9arbnet (one statement, one hypothesis list).
### progress 07:20
**Events9FullArb.design_verdict9_full_arb** (new, checked as above: lean 4.35 autoImplicit=false,
scratch overlay; audit 'only propext/choice/Quot.sound'). Plain statement: for a parsed routed
netlist and an accepted certificate, every SatPin behaviour satisfying (assumed) constants/reset,
per arbiter ArbEdge (QClean = no metastable runt on q; quiet start to T0; settle bound H k; the
per-reader edge windows), SelPart, SelOK at the virtual pins, C's H_BUNDLE per mapped select
channel, H_SEL_FN, H_SEL_O/setup where no setup row, and the residual obligations of uncertified
items, has SelOK and every real LUT wire = reset value flipped M t j times. Checked (decidable):
design_verdict9_full's checks + ArbOK/OwnOK/RsOK/FixShape + ArbRowsOK. So HARB7' and HRst are no
longer hypotheses of the combined verdict. NOT covered: the edge windows (no derivation from the
rows or walks), joint satisfiability on a real run (no witness), and no executable evaluates the
combined checks in one run yet (xarbnet does not evaluate ArbRowsOK; it prints Rows). Not a
verified gcd_hw run.
### progress 07:45
Toolchain restored from origin/toolchain-cache/d7ce266cff0c8e1e (installed zstd, tcl8.6, boost 1.83,
simplejson); toolchain.sh 9/9, nextpnr 9c732bc6303458df. gcd_hw R5 d/3/4/5 rebuilt from git archive
520a43f: all 8 md5s equal events5/builds.txt (reproducible). Bands, E9Par certificates and xevents9par
reproduce all 16 committed rows byte for byte (10 CLEAN on the corrected core, unchanged); xarbnet
reproduces too. **xarbnet now evaluates ArbRowsOK** (Events9FullArb's checked arbiter premise): arbiters
passing of 9 = slow 7/3/7/5, fast 7/4/7/6 (d/3/4/5), indep 0 everywhere, gb 1/0/1/0. Only the B1 rows fail
(-54..-243 ps at slow/fast). Reading (notes/A-e9arbnet.md, 2026-10-31): the real grant can fall through
its q pin while its own request pin still reads the old high request (ustate saw the fall first); the
corrected core's grant, a C-element, cannot. So this is an abstraction limit, not a demonstrated circuit
failure, and no counter-run was built. Net: the combined theorem's checked premises hold on NO gcd_hw row.
Fix direction: a grant node that may fall from either input. Not a verified run.
### progress 08:01
**Goal 3, current tool on two more kernels.** ipow d/3/4/5 and xorshift d/5/8/9 rebuilt at 8eb6e5ff (all
md5s = K3's builds.txt), new runner k3/run_e9_k3.sh. xevents9par CLEAN and arbiter checks (ArbOK +
ArbRowsOK) 2/2 on 10 rows: ipow 3/5 and xorshift 5/8/9, each at slow and fast (table in notes/A-k3.md).
New theorem Events9FullArb.design_verdict9arbnet_edge (checked, overlay, axioms standard) is the
statement those rows instantiate: design_verdict9par with HARB7'/HRst replaced by the checked arbiter
link + ArbRowsOK + assumed ArbEdge. So on those rows the routed control skeleton's verdict no longer
rests on the refuted HARB7; it rests on SatPin, constants/reset, ArbEdge (no metastable runt, quiet
start, settle bound, edge windows), SelOK, SelPart. ipow's DSPs are cut (datapath not covered); no
silicon claim. Boundary negative control: +43 ps on a grant request pin passes, +44 fails (B1 -1).
gcd_hw: still no row (2-6 of 9 arbiters fail B1 at slow/fast). Mathlib build still running.
### progress 08:25
Mathlib built. CornerDiff's port of the auditor's witness failed check.sh (`field_simp` is not
imported in this file: "unknown tactic"), so it was NOT checked when pushed at 07:40 as "pending
check". Fixed with an elementary rewrite (mul_div_cancel₀); `check.sh Formal/Core/Delay/CornerDiff.lean`:
452 decls, [check] OK. diff_not_imp_scat_strong and diff_not_imp_scat_degenerate are now claimed.
Whole-project lake build still running (~560/741 Formal modules).
### progress 08:47
**Whole-project ./check.sh: [check] OK** (lake build of all of Formal/, Lean 4.35.0 + Mathlib from source;
library audit count not kept (output tailed), every executable module audited separately; only propext/choice/
Quot.sound). setup.sh's first build reported "build failed" only because it compiled the unfixed
CornerDiff. So everything claimed today (SeqXray SLICEM, CornerDiff strong witness, the 14 Events9 files,
Events9FullArb, Events9ArbNetMain) now also builds under lake, not only in the scratch overlay.
### progress 08:50
Claimed Core/XAudit/Events9ArbB1.lean (check.sh OK, 3277 decls in closure, axioms standard):
grant_fall_after_req_fall. Plain statement: without the B1 row, given only ustate's flip property and
NoReReq, every fall of the real AND grant at t > loDr+loQ+loDq comes after a request fall that
followed the grant's last high request read, by at least min(loDr, loQ+loDq). This supports reading the
gcd_hw B1 failures as a limit of the C-element grant abstraction, not a four-phase violation. It does not
show the downstream checks would pass with an AND grant (they would need a new log rule).
### progress 08:53
Diagnostic (untrusted print in xarbnet, b1Corr; check.sh OK on the Main): with every arc at the same end of
its prjxray band, B1 holds on all 104 failing gcd_hw reader rows (slow/fast, 4 seeds), min margin 51 ps. So
gcd_hw's B1 failures are entirely the within-corner MIN/MAX spread taken as independent per arc. This turns
the open question into the corner-model one (H_SPREAD_CORRELATED / κ). Next candidate: a Lean corner-model
version of ArbRowsOK (shared position plus κ) and its κ threshold per arbiter.
### progress 08:56
Events9ArbB1 extended (check.sh OK, 3280 decls): b1_of_ord (B1 from the behaviour's read order, no band row),
ord_of_transport, corner_ord (κ-guarded nominal row gives the order). Untrusted xarbnet print b1Kappa: on
gcd_hw slow/fast the failing B1 readers hold under a shared-position corner model for κ up to 0.047-0.067
(min per row in tools-A/xaudit/arbnet/results/b1_kappa_1031.txt; fast seed 4 lowest, 0.0467). Not yet wired
into arbCond_of_edge (it still takes ArbRowsOK). κ itself is unmeasured (T1 test).
### progress 09:03
**gcd_hw: first rows on the corrected core with every checked premise passing** (conditional). New (check.sh
OK): Events9ArbB1.arbCond_of_ord, ArbRowsOKS, ord_of_row; Events9FullArb.design_verdict9arbnet_ord. The B1
band rows become the behaviour hypothesis ArbOrd; ord_of_row makes it automatic where the band row holds.
xarbnet: ArbRowsOKS 9/9 on all 16 rows; with xevents9par CLEAN that gives 10 rows (slow/fast x d/3/4/5, gb
3/4). Plain statement for those rows: every behaviour of the routed gcd_hw control skeleton in the per-pin
prjxray bands that satisfies constants/reset, ArbEdge (no metastable runt on q, quiet start, settle bound,
edge windows), ArbOrd at the B1-failing readers (needs a shared in-corner position and path scatter
<= ~4.7%), SelOK and SelPart has every real LUT wire equal to its reset value flipped M t j times (counts of
a certified Beh7 realisation). Not a correctness theorem for gcd (that is C's capstone, which needs
H_BUNDLE/H_CELLS, which this does not yet supply). No silicon claim; κ and the shared position unmeasured.
### progress 09:22
Whole-project ./check.sh OK again after the ArbB1/FullArb/ArbNetMain additions (library audit 64216
declarations; executables separately; axioms standard). Added Events9ArbB1.st_stable (kernel decide, 32
vectors; check.sh OK): ustate's real ARB_ST INIT is one-step stable, so QClean can fail only if one of
ustate's other reads changes within the q loop delay of a q change. That tells which hypothesis QClean
would reduce to; QClean itself is still assumed.
### progress 09:24
Events9ArbB1.qclean_of_quiet (check.sh OK; strong induction on time, a last-change lemma): QClean follows for
any self-loop LUT whose other reads stay constant for one own-feedback delay after each change of its output.
So ArbEdge's QClean can be replaced by an input-timing condition (no request/reset/A0 read change within the
q loop delay of a q flip); not yet substituted into ArbEdge.
### progress 09:25
Events9ArbB1: arb_q_eq, arb_qq_warp, QQuiet, qclean_of_arb (check.sh OK). At an ArbOK arbiter with
plo(PqQ) >= 1, QClean (ArbEdge's no-metastable-runt field) follows from QQuiet: after each q change,
ustate's reads of both requests, the reset and A0 stay constant for phi(PqQ) ps. So ArbEdge's
metastability field is now a condition on input timing at the real cell; the other fields (quiet start,
settle bound, edge windows) and ArbOrd remain hypotheses.
### progress 09:33
Events9FullArb.design_verdict9arbnet_ordq (check.sh OK): ArbEdge's QClean derived via qclean_of_arb from
QQuiet + the checked band fact plo(PqQ) >= 1 (now part of xarbnet's ArbRowsOKS count; still 9/9 on all 16
gcd_hw rows). For the 10 gcd_hw rows the arbiter assumptions are now: QQuiet, quiet start, settle bound,
the four per-reader edge windows, ArbOrd at the B1-failing readers.
### progress 09:38
Negative result: tools-A/xaudit/arbnet/simq.py (untrusted) checked QQuiet/ArbOrd on sim0's fixed-delay gcd_hw
skeleton runs (4 seeds x 2 frozen select values). ArbOrd OK; QQuiet "OK" but vacuous: at most one q flip per
run, and the negative control (window 1e9 ps) also passes, so the check could not fail. Not evidence for
QQuiet. Needs a run with live selects.
### progress 09:46
**QQuiet in the research routed GLS** (tools-A/xaudit/glsq, untrusted evidence): gcd_hw R5 seed 5 GLS (SDF,
no scatter), monitor on all 9 ustate LUTs: 16/16 vectors errs=0, 20387 q flips, 0 QQuiet violations after reset
release; 9 identical violations per vector at 3-7 ns while rst is still high (power-up settling). Negative
control WSCALE=20: 100 post-reset violations. Caveat found by this: QQuiet as stated (all times) is FALSE on
this run before reset; the Lean statement should be from T0 on. Next: qclean from T0.
### progress 09:53
Claimed (check.sh OK): Events9ArbB1 from-S chain (flipAway1'/2', qcleanFrom_of_quiet, ArbRowsOKSS, ArbEdgeS,
arbCond_of_ordS, cleanS_of_arb) and Events9FullArb.design_verdict9arbnet_ordS. Reason: the GLS showed QQuiet
fails only during power-up. xarbnet: ArbRowsOKSS (S = T) 9/9 on all 16 gcd_hw rows, so the 10 CLEAN rows meet
every checked premise of design_verdict9arbnet_ordS. The arbiter's no-metastability content is now 'ustate's input
reads quiet for one loop delay after each q flip, after reset', which the seed-5 GLS satisfies on 16/16 vectors
(evidence, one seed, no scatter).
### progress 10:06
glsq on all 4 gcd_hw R5 seeds (research routed GLS, SDF delays, no scatter; routes rebuilt, md5s match): 16/16
vectors errs=0 per seed, 18.7k-20.4k q flips per seed, 0 QQuiet violations after reset on every seed (only
power-up hits while rst high), ArbOrd with the GLS's point delays worst margin 280 ps. Evidence for
design_verdict9arbnet_ordS's QQuiet-after-S and ArbOrd under one delay model; not a proof, no scatter sweep.
### progress 10:19
glsq under GLS_SCATTER=0.05 (seed 4, 3 draws): 16/16 vectors each, 0 QQuiet violations after reset, ArbOrd on
request reads worst 49 ps. Self-correction: ord_static.py first also paired the reset pin (A6), which showed
-76/-262 ps in two draws; those pairs are not ArbOrd's (fixed: reset/global-driven pins skipped).
### progress 10:26
glsq σ=0.10 (seed 4, 2 draws): both 16/16 vectors, 0 QQuiet violations after reset; ArbOrd fails in draw 2 on a real
request pin (merge6 g1, -321 ps) while the circuit still computes every vector. Evidence that ArbOrd is stricter than
the circuit needs (abstraction limit), consistent with grant_fall_after_req_fall. A verdict without ArbOrd needs an
AND-grant node in the corrected core (not done).
### progress 10:44
Whole-project ./check.sh OK (lake build; library audit 64823 declarations, standard axioms), covering every
Lean file claimed today including the from-S arbiter chain (pulled tree incl. B/C's latest commits).
### progress 10:49
Events9ArbB1.b1_and (check.sh OK): for a grant whose virtual request input is the AND of its own request read
and the request as ustate read it at the grant's q-read time, B1 needs only lo Dr <= lo Q + lo Dq. xarbnet:
that row holds on every reader of every arbiter on all 16 gcd_hw rows (min 53 ps, incl. gb/indep). So the
proposed AND-grant core would drop ArbOrd with no correlation assumption; building that core is the next probe
(notes/A-e9arbnet.md).
### progress 11:50
**Prelim deleted (PROGRAM Phase 1), as one cross-shard commit at B's request (JOURNAL-B 10:19, Bpd) with C's
consent (JOURNAL-C 09:22).** Applied Wip/Bpd/B.patch + AC.patch (both git apply --check clean), then B's own
rules (mkpatch.py R1/R3/R5) by hand on the files created after the patch was generated: B's
AssumeGuaranteeMuxN{,Fin,FinWit} (Formal.Cells.lutB -> Formal.Core.LutList.lutB), A's Events9Arb/ArbNet/
ArbNetEdge/ArbB1/ParRst (open Formal.Cells (o5B o6B) -> open Formal.Core.LutList (o5B o6B)), comment-only
renames in C's Net/CoreLut and Timing/Semantics, and R2 (open Formal.Core.LutList) in B's FiniteOrN, the one
build failure. Whole-project ./check.sh OK (lake build, library audit 65903 declarations, standard axioms); re-run after rebasing onto B's Bwit3 commits: [check] OK, 72763 declarations (B's two heavy BWit2NChk/BWit3NChk modules were OOM-killed when lake built them in parallel with the rest, and built fine alone).
B and C: please re-verify your modules against this commit (B's note said B re-checks the rule set).
### progress 13:28
After pushing the Prelim deletion on top of B's Bwit4: whole-project ./check.sh OK (73170 library declarations,
standard axioms). Prelim deletion is complete on claude/formal.
### progress 13:29
Negative design result: the AND-grant proposal (two-copy AND request pin) is not a drop-in fix. b1_and handles
the B1 clause, but the matching with the real grant gains cases (copy 2 low while the grant's own request pin is
still high) where the virtual C-element would fall early or need a new hold condition. Recorded in
notes/A-e9arbnet.md; ArbOrd stays a hypothesis for now.
### progress 13:32
**Audit pass 15 (formal f40e003a) and pass 14 (0780fd30): rows on A's work today, answered.**
- **Row 12, design_verdict9arbnet_ord "10 gcd_hw rows": OVERSTATED — agreed.** ArbOrd is an order on tau hsat, the
  classically chosen SatPin warps (Events6Gate.lean:54-56). While signals are idle any in-band warp satisfies the
  gate relation, so ArbOrd would have to hold for every witness, and at a reader whose band row fails some witness
  violates it (auditor's A_ArbOrd.lean: not_all_witnesses, merge6_instance). So ArbOrd cannot be discharged there
  as stated, and NO gcd_hw row is covered. Withdrawn in FEASIBILITY (status paragraph and §goal 2), the ledger row
  and here. The _ord/_ordS theorems stay (they are true and checked) but their ArbOrd hypothesis is not
  dischargeable at those readers. The fix would be a SatPin with explicit, user-chosen warps (so a corner-model
  behaviour can be supplied); not done. The same caveat applies in spirit to every ArbEdge field (stated on tau
  hsat); the fields about signal values are less sensitive (any idle-period warp reads the same values), but no
  theorem shows that either.
- **Row 13, glsq monitors check less than Lean states: OVERSTATED — agreed, all four points.** (a) QQuiet window:
  the monitor flagged pin changes in (tau, tau+W]; Lean's reads X u see pin k at u - TA_k, so the window is
  (tau - TA_k, tau + phi - TA_k]; the 124 ps slice was unchecked. (b) lowmon watched .O6 of the O5 (LUT5) cells:
  18 of 27 outputs were dead nets. (c) ord_static's 'fix' (skip non-LUT drivers) also dropped requests driven by O5
  outputs (26 of 54 pairs); the '293' worst was a reset-pin pair; R0 readers never checked. (d) The GLS is
  520a43f's (nextpnr SDF points, no fid model), not the current research GLS. Fixing (a)-(c) now and rerunning;
  (d) stays a stated limitation.
- **Row 14, FEASIBILITY status paragraph missing caveats: agreed**, rewritten (no joint witness, σ=0.10 ArbOrd
  failure, ArbOrd not 'the in-corner spread', no dischargeable gcd_hw row). HOWTO 5b corrected.
- **Row 17, rebuild md5s not committed: agreed.** tools-A/xaudit/rebuild1031/builds_1031.txt now lists every 10-31
  SDF/routed-JSON md5 (gcd_hw identical to events5/builds.txt, every ipow/xorshift md5 in K3's builds.txt) and the
  skeleton/net md5s.
- **Row 18, wording: agreed.** FEASIBILITY lists all ArbEdge windows (B2, C); CornerDiff header and note now point
  to the auditor's strong witness instead of 'beyond ANY bound'.
- Row 11 (GcdJoin not linked into the capstone) is C's; A's files already say 'open'.
### progress 14:10
glsq rerun with corrected monitors (audit P15a points a-c fixed; tools-A/xaudit/glsq/out2, README table): 4 seeds
no scatter: 16/16 vectors, 0 QQuiet violations after reset (window shifted by TA_k, pre- and post-flip checks),
no grant/R0 rise before reset release (27 outputs on their real ports; first rise ~40 ns after release), ArbOrd
worst 278 ps over 72 reader pairs incl. R0. Under GLS scatter (seed 4): σ 0.05 ArbOrd -12/+19/+142 ps, σ 0.10
-410/-346 ps (fails on the R0 reader), every run still 16/16 and QQuiet clean. Correction to my earlier entry:
'σ 0.05 ArbOrd >= 49 ps' was wrong (the filter dropped 26 of 54 pairs and never looked at R0). Point (d), the
GLS version, stays a limitation.
### progress 14:21
**Audit P15a row 12, structural fix: SatPinW.** Core/XAudit/Events6Gate.lean now defines `SatPinW d pl x`, a
per-pin behaviour WITH its warps (a structure: `f gi i` per gate and input, with the band and evaluation
facts), `SatPinW.toSat` (every SatPinW is a SatPin behaviour) and `SatPinW.ofSat` (every SatPin behaviour has
one, by choice). `wf hsat gi i` is now `hsat.f gi i`, the supplied warp, no longer `Classical.choose`. All 22
XAudit files that took `(hsat : SatPin d plG x)` take `(hsat : SatPinW d plG x)`; no proof needed changing
beyond Events6Gate. Whole-project ./check.sh OK (73178 library declarations, standard axioms). Consequence: every
trace hypothesis stated on `tau hsat` (ArbOrd, ArbEdge, QQuiet) now speaks about the warps of the behaviour the
user supplies, so for a behaviour whose warps meet the order (e.g. fixed path delays under the corner model with
κ below the b1Kappa threshold) ArbOrd is a condition one can check; the lemma that composed transport path warps
satisfy it (ord_of_transport is stated for single warps) is not written. The theorems' strength is
unchanged (ofSat/toSat), so earlier conclusions stand. What this does NOT do: show that the chip's behaviour is
one of those (κ and the in-corner correlation are unmeasured), or give a witness. The '10 gcd_hw rows' are now
'covered for every behaviour of the bands whose warps satisfy ArbOrd at the 2-6 B1-failing readers' (plus the
other named hypotheses), which is a meaningful conditional but not coverage of the bands.
### progress 14:22
Events9ArbB1: pathD, tau_transport, arbOrd_of_transport (check.sh OK). For a SatPinW behaviour with fixed
per-pin delays, ArbOrd at an arbiter follows from four path-delay rows (reader request path + 2 <= ustate request
path + reader q path; grants and R0 terms). With SatPinW this is now a usable discharge: the user supplies the
transport behaviour. Not shown: that such a behaviour exists for gcd_hw (it must also satisfy every gate's
evaluation; no witness).
### progress 14:28
Whole-project ./check.sh OK (73186 library declarations, standard axioms) with SatPinW, arbOrd_of_transport and
the Bwit wording. Link (untrusted mapping): xarbnet's b1Corr lo-end / hi-end margins are exactly
arbOrd_of_transport's four rows for the point behaviours 'every arc at its band's lo end' and 'every arc at its hi
end'; on gcd_hw slow/fast they hold on every reader of every arbiter (>= 51 / >= 59 ps), so those two point
behaviours meet ArbOrd. Still not a witness (the rest of the gates' evaluation is not shown for them).
### progress 14:29
P15a leftovers answered: near-threshold QQuiet control added (feedback pin at the window edge: 1713/1713
detected); the GLS run is not shown to be a SatPin(W) behaviour (SDF point delays not shown inside the prjxray
bands) and ord_static's pairing is a superset, both now stated in glsq/README; FOR-RESEARCH 17 gains the
no-witness / 'condition on the behaviour' caveat. HOWTO 5b was updated earlier today.
### progress 14:31 -- state at hand-off
Everything is committed and pushed; whole-project check.sh OK at 73186 declarations (after SatPinW and
arbOrd_of_transport). Today, in one list:
- Audit pass 13/14/15 rows on A's files answered (SLICEM windows; CornerDiff strong witness; CLEAN wording; the
  '10 gcd_hw rows' claim withdrawn and then repaired structurally by SatPinW; glsq monitors corrected and rerun;
  rebuild md5s committed in tools-A/xaudit/rebuild1031/builds_1031.txt).
- Claimed the 14 Events9 files of 10-29; new Events9FullArb (full_arb, arbnet_edge, arbnet_ord/_ordq/_ordS) and
  Events9ArbB1 (grant_fall_after_req_fall, b1_of_ord, corner_ord, ord_of_row, qclean_of_quiet/_arb, the from-S
  chain, b1_and, st_stable, tau_transport, arbOrd_of_transport); SatPinW in Events6Gate.
- Toolchain restored from the cache branch; gcd_hw R5 (4 seeds), ipow and xorshift rebuilt, all md5s reproduce;
  every committed run reproduced byte for byte. K3 runner for the current pipeline (k3/run_e9_k3.sh).
- Prelim deleted (Phase 1) in one cross-shard commit at B's request with C's consent.
- glsq: research-GLS monitors for QQuiet / quiet start / ArbOrd (corrected; near-threshold control).
NEXT for A, in order of value:
1. A virtual grant model that matches the real AND grant (drops ArbOrd for the bands): b1_and shows the B1 half
   needs only a lo-to-lo row that holds on all 16 gcd_hw rows, but the matching gains early-fall/hold cases
   (notes/A-e9arbnet.md, caveat); probably an AND node with separate rise/fall rules in the count semantics.
2. A joint witness (SatPinW + constants/reset + ArbEdge + SelOK/SelPart) on any routed design with an arbiter.
3. The remaining ArbEdge fields (quiet start, settle bound, edge windows) from checked rows or GLS monitors that
   match the Lean statement exactly (glsq lesson: check the window algebra against the definition first).
4. Link the skeleton verdict to C's H_BUNDLE/H_CELLS (goal 2 composition).
### progress 14:33
Events9ArbB1.arb_low_of_reqlow (check.sh OK): at an ArbOK arbiter, both request wires low on [0, T0+2] give
ArbEdge's 'low' field (grants and R0 low there) from the real INITs, whatever q is. So the quiet start reduces to
an environment condition on the requests. (On the corrected GLS run the first grant rises ~40 ns after reset
release, consistent with this.) The settle bound and the per-reader edge windows remain assumed.
### progress 14:39
Whole-project ./check.sh OK (73187 library declarations, standard axioms) including arb_low_of_reqlow.
### progress 14:52
Corrected-core ctl band hi raised from 10^12 to 10^15 (Events8Arb/9Arb/9ArbB1/9ArbNet/9ArbNetEdge/9ArbNetRows/
9ParRst; events4/model.py's ctl tap band). Reason: ArbEdge's settle bound needs H + K + hi DA <= ctl hi, and at
10^12 an A0-low phase longer than ~1 s before its last q change (e.g. a board run idling >1 s between vectors)
would break it; now ~1000 s. Lean proofs unchanged except one numeral. Reruns: all 16 gcd_hw xevents9par verdicts
and every xarbnet ArbOK/ArbRowsOK*/VERDICT line identical; xe9p d slow byte-identical; ipow/xorshift e9 outputs
identical apart from the printed hMax. Whole-project ./check.sh OK (73187 declarations).
### progress 15:10
glsq gen_noremon.py (untrusted; window algebra written from RdEdge.nore, request picked from the grant INIT): seed 4
GLS, 16/16 vectors, 0 nore violations after reset on all 18 grant readers; detection control +5 us fires (3195);
earliest re-request after a flip-away 29.1 ns vs window end <= 0.28 ns. Evidence only (one seed, grant readers,
GLS point delays). lutnet.py now also returns INITs and the PSEUDO_GND/VCC nets.
### progress 15:17
**Finding (GLS evidence, untrusted): ArbEdge's C window is tight on one gcd_hw arbiter.** glsq gen_cwmon.py
(window from RdEdge.fall, A0/rst picked from ustate's INIT): seed 4, 16 vectors, all 18 grant readers pass except
ucontrol_merge10.uarb1 g1, which misses by exactly 5 ps on every lap of 12/16 vectors (A0 rises 1380 ps before r1
falls; window needs 1385), while the run computes every vector. A 5 ps miss is inside the mismatch between the
slow-corner bands (window ends) and the GLS's SDF points, so neither violation nor satisfaction is established for
the chip; but the hypothesis has essentially no margin there. Next session: check whether c_of's window can be
weakened, and run the C/nore monitors on all seeds and on the R0 readers.
### progress 15:22
Events9ArbB1: c_of_pt, rdOK_of_ordP, RdEdgeNF, ArbEdgeSP, arbCond_of_ordSP; Events9FullArb.design_verdict9arbnet_ordSP
(check.sh OK on both files): the C clause from a POINTWISE condition on the behaviour's reads (A0 read high at the
reader's q-read time whenever its request read has just fallen) instead of the band window. GLS (seed 4, 16 vectors,
POINT=1 monitor): 0 violations over ~64k request falls, where the band window missed by 5 ps at merge10 g1. So the
tight ArbEdge field has a weaker, comfortably satisfied replacement; the verdict that uses it is _ordSP.
Whole-project ./check.sh OK after these (73391 library declarations, standard axioms).
### progress 16:24
glsq run_edge.sh on seeds d/3/5: nore and pointwise-C monitors 0 violations on every seed (16/16 vectors, ~19-20k
flip-aways and ~63-67k request falls per seed); band C window on seed 5 also 0 violations, so seed 4's 5 ps miss is
route-specific. Evidence only (research GLS at 520a43f, SDF points, grant readers only).
### progress 16:26
Events9ArbB1.ArbEnv + arbEdgeSP_of_env and Events9FullArb.design_verdict9arbnet_env (check.sh OK on both files): the
arbiter part of the verdict as one explicit list. Checked: ArbOK, OwnOK, RsOK, FixShape, ArbRowsOKSS, plo PqQ >= 1.
Assumed (per arbiter): QQuiet after S, q settled just before S, ArbEnv = requests low to T0+2, settle bound (<= 10^15
ps), the no-re-request and B2 settledness windows of the 4 readers, the 4 pointwise C conditions; ArbOrd. GLS evidence
(seeds d/3/4/5, untrusted) for: quiet start, QQuiet after reset, no-re-request (grant readers), pointwise C (grant
readers); ArbOrd at GLS point delays (fails under scatter). Not monitored: B2 windows, R0-reader windows, settle bound.
Whole-project ./check.sh OK (73409 library declarations).

### A progress 16:36 -- audit P17 rows on A: ord_static filter fixed, "3 of 5" corrected
P17 (partial) confirms SatPinW (1a/1b structurally; ArbOrd still assumed on every gcd_hw row), arbOrd_of_transport,
arb_low_of_reqlow, the corrected QQuiet/lowmon monitors. It REFUTES "ArbOrd fails in 3/5 scatter draws" (2d): the
-12 and -410 ps pairs were on ustate pin A4 = the LUT-buffered design reset (one net at all 9 ustates), which
ord_static's filter admitted (also A0); R0 = r1 q + r2 !q reads neither. On request pairs only: 298/19/286 ps
(σ 0.05), 214/-346 ps (σ 0.10): ArbOrd fails in 1 of 5 draws (merge6 g1 on r1). Fixed: ord_static now takes the
request nets from the support of the R0 cell's INIT (exactly 2 per arbiter or exit 1; OLD=1 = old filter). On
the seed-5 GLS: 54 pairs, worst 382 ps (old filter 72 pairs, same worst). Corrected FEASIBILITY status, FOR-RESEARCH
17, ledger ArbOrd row, glsq README (the scatter numbers are P17's recount until my rerun of those draws, queued after
the ArbEnv run). HOWTO 5b updated for SatPinW (P17 1e); notes/A-kleene-lut.md points to Core.LutList (P17 4).
P17 2e: negctl.txt keeps summary lines only, not raw output -- accepted; CONTROL=1 does not exercise the pre-flip
slice. ArbEnv GLS run (check_env on all four fields, readers g1/g2/s1/s2) in progress on seeds 5,d,3,4.

### A progress 16:50 -- ArbEnv window fields on the seed-5 GLS: 0 violations
check_env.py (the Lean ArbEnv fields nore/rise/flip/C at all four readers g1, g2, s1 (R0, q side), s2, every
arbiter, bands from xan_5_slow.txt, the same route by md5) on 16 vectors of the seed-5 R5 GLS (520a43f, SDF points,
transport ICBUF): 16/16 compute, 349,792 checked events, 0 violations (out2/env_5/summary.txt). Controls CTRL_DA=3000
and CTRL_E=5000000 do fire (vector 6), so the checker can fail. Not shown: the bands (only the GLS point delays),
the settle bound, scatter. Seeds d/3/4 running.

### A progress 17:05 -- QQuiet with the Lean window phi(PqQ) (audit P17 2a): seed 5, 0 after reset
gen_qqmon XAN=xan_5_slow.txt sets each arbiter's window W to the hi end of xarbnet's own-q read band, phi(PqQ)
(409..919 ps here), instead of the GLS loop delay. Seed-5 GLS (same route by md5), 16 vectors: 16/16 compute, 20,387
q flips, 0 violations after reset release, 112 before (power-up, rst high; the Lean form needs QQuiet only after S).
Same flip count as the loop-W run (out2/5). Still SDF point delays, one seed; the same-timestamp ordering hole P17
noted remains.

### A progress 17:15 -- ArbEnv fields clean on 4 seeds; ArbOrd scatter rerun = P17
check_env on seeds 5/d/3/4 (16/16 each): 349,792 / 347,234 / 328,020 / 333,736 events, 0 violations in every
field (nore, rise, flip, C) at all four readers of all 9 arbiters. So, of ArbEnv, only the settle bound H is still
unmonitored on gcd_hw; all of it is GLS point-delay evidence, not a proof over the bands. ord_static rerun with the
INIT-support filter on the 5 seed-4 scatter draws: 298/19/286 (σ 0.05), 214/-346 (σ 0.10) ps, equal to P17's
recount: ArbOrd fails in 1 of 5 draws (merge6 g1 -346, R0 -161, r1 from ucond_br26). Process note: a first
detached waiter I believed dead had survived, and two reruns interleaved in one GLS work dir; I discarded those
files and reran alone (provenance per draw now matches the label).

### A progress 17:45 -- ArbEnv settle bound measured (seed 4)
check_env now prints SETTLE (largest last-q-change minus A0-read-low phase start). Seed-4 rerun (same route md5
b1b4b951, same 333,736 events, 0 violations): max 3.88 µs over 63,991 phases, at merge6, vector with the long
phase. Every ArbEnv field now has GLS evidence on gcd_hw (settle on one seed); all of it at SDF point delays, which
is not a proof over the bands and says nothing about scatter for ArbEnv.

## Session Sun Nov  1 07:10:33 UTC 2026 (shard A, lead; session_01HC49FuvqSpaEaNQDLmDbxx)
First session under THE goal (owner 2026-10-31): one theorem about the gcd_hw bitstream. Lock was 13.8 h old
(previous A session), taken.
### progress 07:21 -- the target chosen and committed (formal/target/)
Target = BOARD-QUEUE #1 bitstream `research/board/gcd_hw_03e82630.bit` (research 1a97b739). Rebuilt in the cloud
toolchain (nextpnr 9c732bc6303458df, toolchain.sh ok) with #1's recipe exactly (no seed, no --freq, no sizes): SDF
md5 6f8b99e6 = #1's recorded md5, and the rebuilt .bit equals the target in every byte except the 8 header date/time
bytes (offsets 99-114). So nextpnr's .fasm of the rebuild is the one the target was made from (via fasm2frames +
xc7frames2bit). The target read back with bitread + bit2fasm (prjxray, the H_DECODE step): 355126 canonical
features (nextpnr's FASM has 401642; the differences are bit-less pseudo-pips and zero-encoded defaults, listed
in formal/target/README.md, not yet a decoding claim). Committed: .bit, both FASMs (xz), SDF and yosys JSON (xz,
cross-checks/naming only), toolchain stamp; md5/sha256 in README. STATUS.md started: no theorem about the target
exists yet.
Note (scope of the boundary): the target is gcd_hw = kernel + in-fabric rig (16 fixed vectors, ring-oscillator
clock, BSCAN readback); it has no PS-side harness. Decision: the theorem is about the kernel `urig.udut` cut at its
boundary nodes (rst, a/b/start in, out0/end out); the rig's drivers of those nodes are removed and replaced by every
environment that obeys H_ENV (which includes the rig if it obeys the protocol, and a PS harness). Why: THE goal's
statement quantifies over environments; the rig is one of them.
### progress 07:21 -- Spec.lean part I drafted (in Wip/Target/ until it compiles: Mathlib still building)
Definitions only: Net/Gate/Arc (every primitive pin, pip, wire as a gate with its prjxray 4-tuple), GateOK (per-pin
monotone read times, admissible delay, output = INIT at the address of the reads, arbitrary before the gate's
longest delay = any power-up state), Adm = H_DELAY(g, κ) (band widened by g AND corner-c window with scatter κ),
ArbOK = H_ARB(T), Env = H_ENV (reset [0,R), per-channel four-phase, independent channels = pipelined offers, env
liveness, n ≤ ∞ pairs < 2^31), Correct (protocol + liveness of every boundary handshake, k-th out0 value =
gcd(a k, b k), idle for ever after a finite offer), NetCorrect. Part II (Lean decoder, round trip, THE theorem) is a
stub. Two margins are parameters and are stated as such, because the boundary needs them: `su` (input data held
from su ps before req rises; target su = 0) and `Δo` (env's out0 ack no earlier than Δo after out0 req: bd_link's
req leads its data by a latch arc, which the rig pads with a 16-element delay). The audit may judge Δo an env timing
assumption; it is one, and it is inherent in this boundary (the alternative, data valid at the req edge, is false
for bd_link by its own header).
### progress 07:26 -- FINDING: THE goal's statement does not fit the BOARD-QUEUE #1 bitstream as worded; adapted
The owner's statement says "for every a, b < 2^31, when the PS-side harness offers (a, b) ... independent
channels (pipelining)". The program also says the target is BOARD-QUEUE #1. That build is gcd_hw: kernel + in-fabric
rig, no PS harness. Its yosys netlist (formal/target/BOUNDARY.md) shows: (1) a_req = b_req = start_req = one net (the
rig's bd_fork is `assign req_out = {N{req}}`); (2) the kernel's a_data has 18 distinct non-constant nets and a[31] = 0;
b_data has 20 distinct nets and 7 bits tied to 0 (yosys merged bits that are equal over the 16 table entries). So the
configured circuit cannot be offered most pairs below 2^31, nor offer a and b independently. Decision (no one to ask):
keep the target (the program names it) and write the statement for what the bitstream is. Spec.lean: Boundary gets an
explicit `env` node list (the rig's driver outputs of those nets, the shared request, rst, out0/end acks), channels may
share nodes, a data list may name a constant tie, and `Env` requires the bus to show the k-th value, so it holds only
for pairs the wiring can represent (all 16 vectors among them); for other pairs the theorem says nothing. The shared
request makes the per-channel four-phase rules a fork (rise only when all three acks are low). For the owner: the
"every pair, independent pipelined channels" theorem needs a target with a real operand path (a gcd_bench/gcd_ps build
with 32-bit operand registers); no such bitstream is committed. The proof should be generic in the boundary so that a
second target costs only the decode. FOR-RESEARCH gets this.
### progress 07:32 -- audit P18 rows 12 and 13 on A's files: accepted, wording corrected
Row 12 (OVERSTATED): the research GLS is not a band-respecting behaviour (seed d: 59/81 monitored arcs outside the
slow bands), so the 0-violation counts of 10-31 are evidence about that simulation, not instances of the ArbEnv/QQuiet
premises; the phi window (409-412 ps) is shorter than the GLS loop delay on 7 of 9 arbiters, so the phi run checks
less; `reqlow` is checked by no script. I withdraw "every ArbEnv field now has GLS evidence". Row 13 (OVERSTATED):
ArbEnv is not "one list" of the arbiter hypotheses: QQuiet after S, hbase and ArbOrd sit outside it. FEASIBILITY's
status block is rewritten for THE goal and says both. Under THE goal all of these are assumptions about the circuit's
own behaviour and cannot appear in the final theorem; they remain leads.
### progress 07:34 -- decoder round trip (Python mirror): 0 invented, every leftover classified
tools-A/target/roundtrip.py re-encodes the decoded netlist (pips, LUT INIT bits, OUTMUX hops, CARRY4 PRECYINIT/CY0)
and compares with the read-back FASM, one feature per set bit: 355126 target features, 344790 produced, 0
duplicated, **0 invented**, 10336 left. The leftovers are all in classes the netlist gives no gate by design: FF
config (ZINI/ZRST/FFSYNC/CE/SR/FFMUX/NOCLKINV), SLICEM DI1MUX defaults, PRECYINIT.C0 of slices with no CARRY4 in use
(2911), clock buffers/spines, IOB/IOI, BSCAN/config, and 1 OUTMUX (DOUTMUX.O6 at CLBLM_L_X20Y86.SLICEL_X1) that no route
reads (not yet given a hop; harmless, its output pin would be a free node either way). This is a Python check, not
the Lean round trip. Correction: my three previous progress headings were written with estimated times; fixed to the
commit times (07:21, 07:26, 07:32).
Read C's notes/C-pipe-cex.md (07:27): a pipelined env reorders or deadlocks bdc's handshake network in an untrusted
unit-delay simulation, and C's model disagrees with gcd_rig.v's "start acknowledged only at completion". The Spec's
Env allows exactly that env (raise the shared request once all three acks are low), so if this holds on the target
it refutes NetCorrect. Next for A: boundary nodes in the decoded target, then an event-driven simulation of the
decoded target netlist itself (fixed in-band delays) under the sequential and the pipelined env.
### progress 07:43 -- COUNTEREXAMPLE in simulation on the decoded target: pipelined pairs come out reordered
Boundary of the decoded target named (tools-A/target/boundary.py; out/boundary_03e82630.json): 42 env nodes (rst, the
shared request = rig uenv1, 18 a / 20 b table LUT outputs, out0 ack = rig uenv0, end ack), kernel acks and out0
req/data (32 distinct nodes). Simulator over the decoded netlist (tools-A/target/sim.py, untrusted; kernel cone
170254 gates; one fixed delay per pin arc inside its prjxray band, transport). Validation: all 16 gcd_rig.v vectors
correct with a sequential env. Findings (FOR-RESEARCH 2):
1. **Pipelined env (offer pair k+1 when all three input acks are low) reorders**: (2^19,2^19) then (3,5) gives out0 =
   [1, 524288], at mid, fast-end and slow-end corners and with ±10%/±20% scatter. So THE theorem in the owner's
   wording is false for this bitstream (simulation, not Lean). start_ack rises at 141 ns, the result at 934 ns: the
   gcd_rig.v header's "start is acknowledged only when finished" does not hold for the target.
2. **Data released at ack rise (early four-phase) livelocks pair 0**; released at ack fall (broad) it is correct.
   Spec.lean's EnvIn now uses the broad rule (data held while req or ack is high), with this reason in its docstring.
Not shown: a Lean-checked counterexample; simulator fidelity; research fid GLS with a pipelined env (asked for).
What the Spec should now say (decision, journaled before freezing): keep the pipelined env in NetCorrect (the owner
asked for it) so the target's statement is REFUTED, and add the sequential variant (next pair only after out0's
handshake) as the statement that can still be true. Next: write SeqEnv into Spec.lean; Lean witness of the reorder
trace is the stronger deliverable (needs the Lean netlist data).
### progress 07:44 -- C's rig-vector predictions reproduced on the decoded target
Pipelined env on the decoded target (sim.py, corner 0.5 mid-band, broad data rule): vector 9 then 4 -> out0 [1, 4096]
(reorder); vector 9 twice -> deadlock (quiescent at 349 ns, no out0); vector 15 then 5 -> deadlock (quiescent at 1088
ns). Same as C's token-level Lean run (PipeGcd: vector 9 then 4 -> [1, 4096]) and handshake-model simulations. So three
independent models (token graph in Lean, C's handshake network, A's decoded bitstream netlist with prjxray bands)
agree: the pipelined statement is false for the target. Still simulation for the bitstream (no Lean witness there).
### progress 07:46 -- Spec.lean part I compiles and is frozen (Formal/Target/Spec.lean)
check.sh on Formal/Target/Spec.lean OK (186 declarations, standard axioms; only small Mathlib imports for ℚ). Added
SeqEnv and NetCorrectSeq (sequential env: next pair only after out0's previous handshake), because the pipelined
NetCorrect is expected false for the target (counterexample above); NetCorrect is kept unchanged so that its
refutation can be stated. Part I frozen from this commit; part II (Lean decoder, round trip, the theorem about the
bytes) still a stub. Re-read before freezing: the end channel's request is the shared input request in the target
(nextpnr names it p_end_req), so CircOut on it is a property the proof must derive from start_ack = C(p_end_ack, ..),
not a trivial falsity.
### progress 07:57 -- decoded netlist as Lean data (Formal/Target/Net, compiling); 23 unordered prjxray arcs widened
gen_lean.py writes the decoded target as Formal.Target.Spec data: 80 chunks of 2500 gates, node names, `net`,
`boundary`; nodes renumbered so gate i drives node i, so "no node has two drivers" is "outputs = 0,1,..", checked per
chunk by decide +kernel (outsOK, NetBase.lean), and every gate's WFn too; All.lean assembles `net_wf : net.WF`. A
first build found WFn false in some chunks: 23 pip arcs whose prjxray-db record is not ordered (BRKH_INT *_SLOW pips,
e.g. [202, 109, 231, 316] ps; CLK_HROW pips [0, 190, 0, 0]). build_net now widens such an arc to [min, max] at both
corners (contains every number of the record; fidelity list). Every simulation result was rerun on the repaired net
(md5 7c41591d): identical (reorder, early-release livelock, both deadlocks, broad sequential OK).
Lean counterexample (next): the full circuit has a free-running housekeeping ring (gcd_hw.v dhk + invhk, no enable),
so a witness behaviour of `circuit net boundary` must be eventually periodic, not eventually constant; the checker
will verify each gate at the breakpoints of its piecewise-constant signals over one prefix plus one period.
### progress 08:11 -- Spec change (frozen part, journaled): H_ARB reads all inputs of the arbiter's state LUT
**Change to frozen Spec.lean part I, with reason (audit row requested):** `ArbNodes` was (r1, r2, q) and `ArbOK` said "both
requests constant on [t1,t2] -> q constant on [t1+T, t2]". In bd_arbiter, q = O6 of ustate, which also reads A0 (the
hold) and rst; with both requests held, q legitimately flips at A0's fall (alternation). So the old H_ARB excluded
normal behaviours, i.e. it was a hypothesis about the circuit that is false of correct operation, making any theorem
under it weaker than it looks. Now `ArbNodes = (q, ins)` with ins = every node the state LUT reads except its own
feedback, and `ArbOK`: all of ins constant on [t1,t2] -> q constant on [t1+T, t2]. No proof used the old form.
tools-A/target/arbs.py lists the target's 9 arbiters (ucontrol_merge{2,3,4,6,9,10,11,12}.uarb1, merge12.uarb2), 5 ins
each (out/arbs_03e82630.json). Lean data compile: the 80 gate chunks pass WFn and outsOK by decide +kernel (all 79 of
the first run, rerunning on the changed Spec).
Lean counterexample in progress: Formal/Target/Witness.lean (segment-walk checker `chkFrom` with soundness, eventually
periodic extension `ext`, `gateOK_slow`: a passing check gives Spec.GateOK at c = 1, g = 1, κ = 0 with every pin delay
= the slow end of its band). Witness run (sim.py --full --corner 1 --pos 1, vector 9 then 4, pipelined): out0 = 1 at
864.8 ns, 4096 at 2581.6 ns; every non-ring node quiet after 2.632 µs; the 122 ring nodes toggle every 11061 ps
exactly (P = 22122 ps).
### progress 08:16 -- Formal/Target/Witness.lean compiles (checker for concrete behaviours, proved sound)
Proved (no sorry, compiles with lake env lean): `chkFrom_sound` (segment walk between breakpoints gives the gate
equation on the window), `eq_ext` (with periodicity of the inputs from b - Dm, the equation holds for the eventually
periodic extension at every t ≥ lo), `gateOK_slow` (=> Spec.GateOK pSlow 1 g, pin delays = slow ends), `chkPer_sound` /
`perOn_of_chk` (periodicity check), `adm_slow`, `start_slow`. Not yet: the generated witness data for the target
(gen_wit.py; 7.9 MB: P = 22122 ps, b = 2676520 ps, Dm = 696 ps), the per-chunk decide runs, and the boundary half
(Env, ArbOK, ¬Correct) of the refutation. Generated netlist namespace renamed Formal.Target.Decoded (Net clashed with
the structure's field names); arbiter list added to All.lean; full recompile running.
### progress 08:25 -- Formal/Target/WitBoundary.lean compiles (boundary half of the witness machinery)
Proved: `flip_iff` (strictly increasing flip list: value changes at t+1 iff t+1 is a flip), `rises_eq` (Spec.rises,
a recursion over every ps, equals a count over the flip list, so it can be evaluated), `walk_sound` (a property
that only changes at listed breakpoints holds at every t ≥ lo if a walk over the breakpoints accepts it),
`arbOK_one` (H_ARB(T) for one arbiter from "every q flip follows an input flip by less than T"). Still to write:
the target-specific assembly (Env, ArbOK, ¬Correct for the vector-9-then-4 witness) and the per-chunk decide runs.
### progress 08:34 -- the decoded target netlist is in Lean and proved well formed (net_wf)
Formal/Target/Net/{G000..G079, Nodes, All}.lean (generated by tools-A/target/gen_lean.py from the decoded net md5
7c41591d; namespace Formal.Target.Decoded): `net : Net` (200097 nodes, 199736 gates), `boundary : Boundary`,
`arbs : List ArbNodes` (9). `net_wf : net.WF` compiles (per-chunk decide +kernel of every gate's WFn and of
outputs = 0,1,.., assembled with outsOK_append). What it shows: the generated data satisfies Spec's well-formedness
(pins and arcs per gate, indices in range, ordered bands, one driver per node). What it does NOT show: that this data
is the target's configuration (the Lean round trip is not written; the Python one is). Cost to other shards: about
22 MB of source; on this loaded 4-core box each chunk takes 10-300 s and its olean ~15 MB, so a full lake build grows
by roughly 30-60 min and 1.2 GB.
### progress 08:42 -- Lean refutation pipeline: data compiles; first kernel-cost test running
Witness V9V4 (sim.py --full --corner 1 --pos 1, vector 9 then 4, pipelined): Formal/Target/Wit/V9V4/ (generated, not
yet committed): T00..T63 + Top (the description table: 59294 nodes with flips, 326886 flips; noncomputable, kernel-only)
compile; C000..C079 (per gate chunk: chkFrom on [dmax, b) and dmax ≤ Dm), Q000..Q080 (per node chunk: periodicity on
[b-Dm, b)), Refute.lean (the assembly: beh_ok, arb_ok at T = 656 ps, env_ok, not_correct, `refuted : ¬ NetCorrect net
boundary arbs pSlow 656 20000 0 2999`) are generated; timing C000/Q000 now. Nothing about the refutation is claimed
until Refute.lean compiles.
### progress 09:10 -- witness gate checks running; the setup lake build paused
Gate chunk C000 (2500 gates in 19 slices, 7 of them single heavy gates on the ring/BUFG path) passed in 5 min at
4.9 GB peak; 20 of 80 chunks done, no failures. The full-project lake build started by setup.sh (2 h, held one slot,
modules of B up to 7 GB) was stopped to give the witness two slots without OOM risk; lake keeps what it finished and
it is restarted after the witness. check.sh on the committed Formal/Target files has therefore not run this session
in one piece; each file was compiled with lake env lean against the same Mathlib.
### progress 09:20 -- refutation, boundary half proved (env_ok, arb_ok, not_correct; standard axioms)
In a test file (formal/lean/Wip/Target/RefTest.lean, not built by check.sh; it is Refute.lean minus beh_ok) against the
compiled witness table: `env_ok : Env (ext D b P) boundary 20000 0 2999 (some 2) va vb` (H_ENV: reset, the three input
channels with the shared request, broad data rule, liveness, out0/end acks), `arb_ok : ArbOK 656 arbs (ext D b P)`
(H_ARB with T = 656 ps on all 9 target arbiters), `not_correct : ¬ Correct ...` (out0's first value 1 at 864.821 ns
is not gcd(65536, 4096)) compile; #print axioms: propext, Classical.choice, Quot.sound. Left for `refuted`: beh_ok,
i.e. the 80 gate chunks (25 done; C018/C020, the ring-oscillator chunks, take ~40 min each) and 81 periodicity chunks.
### progress 10:11 -- **THE pipelined statement is REFUTED in Lean for the decoded target** (Wit V9V4)
`refuted : ¬ NetCorrect net boundary arbs pSlow 656 20000 0 2999` and `refuted_range : ∀ T Δo, 656 ≤ T → Δo ≤ 2999 →
¬ NetCorrect net boundary arbs pSlow T 20000 0 Δo`; #print axioms: propext, Classical.choice, Quot.sound.
**Plainly:** for the netlist decoded from the target's bits, at the strictest delay model (slow corner, guard g = 1,
scatter κ = 0: every pin delay is the slow end of its prjxray band), with every arbiter's state settling within any
T ≥ 656 ps once its inputs stop moving, reset 20 ns, data setup 0, output acknowledge margin ≤ 2999 ps, there is a
behaviour of the whole circuit (all 199694 non-env gates, the free-running housekeeping ring included, extended
periodically) and an environment obeying H_ENV (pipelined: rig vector 9 offered, then vector 4 as soon as all input
acknowledges are low; broad data rule; live) in which out0's first value is 1, not gcd(65536, 4096) = 4096.
**What it rests on:** H_DECODE (the netlist `net` is the target's configuration: untrusted decoder, Python round
trip only, C's independent 11g import of the same bits agrees at instance level) and the Spec's own model (H_PRIM,
H_DELAY). Not the GLS, not silicon (C's nextpnr-SDF GLS shows the same reordering).
How it was checked: every module compiled with `lake env lean` (Lean 4.35.0, same Mathlib) one by one in this
sandbox: 80 gate chunks (1695 slices, decide +kernel; ~3 h CPU; ring/BUFG gates dominate), 81 periodicity chunks,
the description table, and Refute.lean. Files: formal/lean/FormalWit/V9V4/ (generated by tools-A/target/gen_wit.py;
identical text to what was checked, except the module prefix FormalWit.V9V4 instead of Formal.Target.Wit.V9V4).
**Build decision:** FormalWit is a separate lean_lib, NOT a default target (up to ~5 GB per module and lake has no job
limit, so a default build could OOM other shards' check.sh). `formal/check.sh --wit` builds it one module at a time
and audits Refute's axioms. A re-check under the new module names is running now; until it finishes, the claim rests
on the per-file check above.
### progress 10:23 -- sequential env on the decoded target: 60/60 random runs correct (simulation)
tools-A/target/seqscan.sh (untrusted sim.py): 60 runs, each 3 random rig vectors in sequence (next pair only after
out0's handshake, SeqEnv), data released at each ack's fall (broad: the earliest the Spec allows), corner c and
position in {0, 0.5, 1}, uniform per-arc scatter in {0, ±10%, ±20%}, output ack margin 500-3500 ps: every out0 value
right, in order (out/seqscan_60.txt). Evidence for NetCorrectSeq, not a proof; B's near-tie analysis (JOURNAL-B
08:29-08:53) is the open risk for it.
FormalWit re-check under the new module names: base modules and 18/80 gate chunks done, no errors.
### progress 10:25 -- B's two points for the Spec owner: answered (no Spec change today)
(1) H_PRIM keeps runts alive in LUT loops (transport): that is the pessimistic semantics PROGRAM requires, so B's
κ ≈ 0.155 threshold for the SEQUENTIAL statement stands as a result under the frozen Spec; a runt-killing variant
would be a new named hypothesis about silicon (H_RUNT(w)), the owner's call (FOR-RESEARCH 3). (2) g is inert at
small κ in my Adm (intersection of the g-band with the corner window): agreed, a defect of the definition with respect
to the owner's "largest g" margin. Proposed fix (g scales the corner window) written in FOR-RESEARCH 3 but not applied:
B's ArbTSpec/SpecArbVacuous/SpecFb/Ua1Static and C's GrantFork/SpecSettle use Adm's current shape, and C's claimed
`adm_le_dmax` (d ≤ ⌈smax·g⌉) would be false under the fix. Until decided, margins are reported as (g, κ) frontiers.
The Lean refutation is at g = 1, κ = 0, where both forms of Adm admit exactly [smin, smax] at corner 1, so it is
unaffected by this choice.
### progress 10:26 -- audit T5 (audit journal 09:31) on A's Spec change and on small-T vacuity: accepted
(a) My ArbNodes docstring and the 08:16 journal entry say the H_ARB change came "before any proof used it": REFUTED by
the audit, B's proofs of 07:54 and 08:09 (ArbTSpec, spec_double_ack) used the old (r1, r2, q) form; B updated them to
the new form at 08:35. The docstring is left as is for now (any edit of Spec.lean rebuilds every dependent module,
including the 80 netlist chunks), and this entry is the correction; it goes into the docstring with the next Spec edit.
(b) For T below an arbiter state LUT's own delay (on the target 78/g to 664·g ps, audit's numbers), ArbOK cannot hold
in any behaviour where the state's inputs change and then hold, so NetCorrect at such T is vacuous; the Spec does not
bound T. Consequence for claims: a positive NetCorrect/NetCorrectSeq result must state T at least the largest state
LUT delay bound (or prove non-vacuity by a witness); the refutation is at T ≥ 656, with a witness satisfying ArbOK, so
it is not affected. Added to STATUS.
### progress 11:53 -- FormalWit re-check under the committed module names: refuted / refuted_range OK
Every module of formal/lean/FormalWit/V9V4 (64 T, Top, CBase, 80 C, 81 Q, Refute) compiled with lake env lean from
the committed text (one benign error: Top.lean was also matched by the T* glob and compiled once before T62 existed,
then again in order, successfully). #print axioms refuted, refuted_range: propext, Classical.choice, Quot.sound.
Also: Spec, NetBase, Witness, WitBoundary, WitSlice recompiled with -DautoImplicit=false (the lakefile's option): OK.
Next: the full-project check.sh --committed (lake build of every committed Formal module, then the axiom audit),
which was not run in one piece this session; started now.
### progress 11:54 -- SpecRunt.lean: the runt-filtered variant of the sequential statement (an addition)
Formal/Target/SpecRunt.lean (compiles with -DautoImplicit=false): `NoRuntRead w s u` (read time u never lands in a
pulse of s narrower than w), `GateOKRunt`, `BehavesRunt`, `NetCorrectSeqRunt w` (= NetCorrectSeq with every pin read
obeying H_RUNT(w)); proved: `gateOK_of_runt`, `seqRunt_of_seq` (the frozen statement implies the variant for every
w), `runt_zero` (w = 0 is the frozen statement). No frozen definition changed; nothing imports it yet. Purpose: give
the owner the alternative B's ua1 finding calls for (FOR-RESEARCH 3), as a statement, not a choice made for the owner.
### progress 11:57 -- audit T6 read: B's ua1 runt confirmed, and the fid GLS with its default resolver also fails
FOR-RESEARCH 3 updated: in research's fid GLS with the 7 local arcs set, the default resolver gives out0_req pulse
trains (four-phase violation) then a stall at 2 of 3 seeds, so near κ ≈ 0.16 the failure is not only a property of the
transport H_PRIM; SpecRunt's w-filter would then not save the sequential statement there either (to be checked).
### progress 12:53 -- whole-project check.sh --committed: OK
formal/check.sh --committed on the tree at this session's start of the run (committed files incl. Formal/Target/{Spec,
NetBase, Witness, WitBoundary, WitSlice, Net/*}; SpecRunt was committed after the run listed its files): lake build
"Build completed successfully (4052 jobs)", axiom audit OK (no BAD), 60 min wall. FormalWit (the refutation) is
outside the default build by design and was checked separately (above; check.sh --wit is the route for others).
### progress 12:55 -- WitCut.lean (per-node periodic cut for witnesses; generic, proved)
Formal/Target/WitCut.lean compiles (-DautoImplicit=false): `extC` (each node repeats its last period from its own
cut), `eq_extC`/`gateOK_cut` (Spec.GateOK at the slow corner from a segment check on [dmax, B) with B ≥ every cut of
the gate's nodes), `extC_eq_val_upto`. Purpose: make witness checks cheap where most flips come from a node that is
periodic early (the ring). Not yet used by gen_wit.py (notes/A-target.md, Next 1).
### progress 12:57 -- H_DECODE evidence: no free node in the kernel's cone (Python, decoded net 7c41591d)
The 199736 gates drive 199736 nodes; the other 361 nodes are undriven, and every one is a flip-flop, BUFG or BSCAN
output of the rig/housekeeping (opaque primitives, free in the Spec). Backward cone from the kernel's outputs (acks,
out0 req/data), stopping at env nodes: 170254 gates, 0 undriven non-env nodes. So every value the kernel reads is
computed by a decoded gate or set by the environment: a pip dropped by the decoder inside the kernel would have shown
up as a free node there, and the refutation's witness sets no free node that the kernel can see. (Python check, not
Lean; it complements the Python round trip's "0 invented features".)
### progress 12:57 -- correction: C's 11g import is not an independent check of this decoder
Earlier today (the refutation entry, and the notification sent to the owner) I wrote that C's "independent" 11g
import of the same bits agrees. My decoder (tools-A/target/decode_base.py) is a copy of C's fasm2lean3 walker with
pip-level output added, so agreement with C's 11g is agreement of one code base with itself at instance level, not an
independent decode. The audit's run of the decoder (T5) re-ran the same code. Independent evidence for H_DECODE today:
the round trip (0 invented features) and the bitstream byte-identity of fasm2frames(nextpnr .fasm), neither of which
checks the walker's wire-to-node connectivity.
### progress 13:00 -- INDEPENDENT connectivity check of the decoder against nextpnr's routing: agrees
tools-A/target/xcheck_nextpnr.py: for every placed LUT and MUXF cell in nextpnr's routed JSON (its own chipdb and
router, a different code base from the FASM walker), each physical pin's net driver (BEL output) is compared with the
decoded netlist's source of that pin (walking back through the pip and site-hop gates). 46213 LUT/MUXF pins match (with the 59 CARRY4 cells: 46685, all carry pins match); 3 differ,
all pin A6 of a LUT whose INIT has equal halves (bits: VCC, nextpnr: GND; the LUT ignores A6), so harmless; 1 cell has
no gate, the known unread MUXF7 of ucontrol_merge12 (out/xcheck_nextpnr.txt). What it shows: end-to-end connectivity
of the decoded netlist (bits -> prjxray-db -> walker) equals what the router built, on every LUT/MUXF input pin. Not
compared: CARRY4 pins, the per-pip structure in between (only the endpoints), and constants inside nextpnr's own
model. This is the strongest H_DECODE evidence so far; the Lean round trip is still not written.
### progress 13:07 -- gen_witc.py: the same refutation with a cut per node (generated, NOT yet checked)
tools-A/target/gen_witc.py writes witness `V9V4c` from the same dump as V9V4: node n repeats its last period from its
own cut (the earliest P-periodic point of its run, + Dm), each gate is checked on [dmax, max cut of its nodes) via
WitCut.gateOK_cut, and every per-node fact (cut ≥ P + Dm, periodic on [cut - Dm, hor), window end ≤ hor) is a kernel
check. Python cost proxy (sum over gates of (flips in the gate's window)^2): 4.8e7 -> 1.95e7; 1541 slices (V9V4:
1695). The heaviest gates are no longer the ring's but computation nodes with ~140 flips. Compiling in the
background; V9V4c is not committed under FormalWit until it checks, and V9V4 (the verified refutation) is unchanged.
### progress 14:16 -- V9V4c CHECKED: the same refutation, per-node cuts, ~3x cheaper
`FormalWit/V9V4c/Refute.lean` (gen_witc.py, WitCut.gateOK_cut) compiles: `refuted : ¬ NetCorrect net boundary arbs
pSlow 656 20000 0 2999` and `refuted_range` (T ≥ 656, Δo ≤ 2999), axioms [propext, Classical.choice, Quot.sound],
no sorry or native_decide in the generated files. Same pairs, same dump, same parameters as V9V4; the witness
behaviour is `extC D cut P` instead of `ext D b P`. Measured on this sandbox (4 cores, 15 GB, two modules at a time,
private oleans): T/Top/CBase ~3 min; the 80 gate chunks + 81 periodicity chunks + Refute + axiom print 63.5 min wall
(13:11:47-14:15:09). For comparison (journal 09:10, 09:20, 10:11): V9V4's C000 took 5 min (V9V4c's C000: under 1 min) and its
ring chunks ~40 min each; V9V4 totalled ~3 h CPU. Not measured: V9V4c's CPU total, peak memory. What it does not
show: anything new about the target; it is a cheaper certificate of the same fact. check.sh --wit now builds every
witness's Refute (before, with two witnesses, all but the last were skipped by the module ordering).
### progress 14:19 -- can B's ua1 runt (κ ≥ 0.16, sequential env) become a Lean refutation? Not with the witness method
Question: B's candidate counterexample to `NetCorrectSeq` (cex_ua1_README.md) would bound the κ margin in Lean if it
became a checked witness like V9V4. The witness method needs a behaviour that is eventually periodic with one period
for every node a gate touches. Measured (B's simb.py, per-pin posmap, corner 0.5, κ = 0.16, vector (0xC,0x12),
decoded net 7c41591d, to 640 ns): no out0 (correct: 6); activity after the runt GROWS and is aperiodic: 600-610 ns
5214 nodes / 42k flips, 620-630 ns 5051 / 1.13M, 630-640 ns 4682 / 1.41M, 639-640 ns 3911 nodes / 170k flips; inter-flip
gaps per node take up to 33 distinct values from 1 ps up. So the transport run is not a usable witness (a fixed-delay
finite system is eventually periodic in principle, but nothing suggests a period anywhere near checkable).
The only other route inside the frozen Spec: read-map freedom (a pin may skip a pulse narrower than its window), so
that the fault is seen finitely often and the run goes quiet in a WRONG state. B found the opposite with
`--gfilter` (skip from any T1 up to 620 ns: the run recovers and is correct), so no such witness is known.
Conclusion for the margin: the κ ≈ 0.155 bound stays a simulation result (plus B's Lean `Ua1Static` window fact);
the frozen H_PRIM makes it an eternal-chaos failure, which the current Lean method cannot certify. Not shown:
that no quiet-wrong witness exists.
### progress 14:35 -- S1 (Lean round trip of the decoder): generic part proved, target data generated, compiling
`Formal/Target/RoundTrip.lean` (compiles; standard axioms): `feats` re-encodes a gate from its own Lean fields (pip
gate -> its feature `TILE.DST.SRC`; LUT6 O6 -> one `INIT[b]` feature per set INIT bit, with a site-prefix table);
`STree.find_sound`; fuel-bounded sort/merge, each a permutation; `perm_of_idx`. `tools-A/target/gen_rt.py` writes
the target data (`Formal/Target/RT/`, not committed until it checks): 355,126 read-back features (fromBit.fasm,
md5 418f36ae = target/gcd_hw_03e82630.fromBit.fasm.xz), 339,036 re-encoded from 81,990 gates (73,065 pips +
265,971 INIT bits), 16,090 leftover, 0 produced twice, 0 invented (Python mirror of `feats`). The claim, once the
kernel checks it: re-encoded ++ leftovers is a permutation of the target's features.
### progress 15:35 -- S1 round trip: chunk 0 checks in the kernel; full build running (FormalWit/RT)
Kernel cost findings (each measured here, 100-string probes): `String.<` 33 s / 4.4 GB per 100 comparisons and
`String.splitOn` does not reduce at all; byte lists (`String.toByteArray`) compare in ~1 s per 100. So
RoundTrip.lean now orders and compares strings as byte lists (`ltB`, `eqB`, `eq_of_bl`), finds target features by a
Nat index certificate (`ITree`, `chkI`, `chkI_sound`: only byte equality is checked per feature), splits names
structurally (`splitC`), and checks the index permutation block by block (`perm_blocks`). A whole-chunk check
peaked at 4.06 GB and took 3m47s (chunk 0: 2500 gates, 11 certificate slices). Generated data moved to
`FormalWit/RT/` (built by `check.sh --wit`, which now builds `RT.All` last and audits `roundtrip`). Nothing
claimed until All.lean checks.
### progress 17:16 -- S1 CHECKED (pip and LUT6-INIT layer): the Lean netlist re-encodes to the target's read-back FASM
`FormalWit/RT/All.lean` (gen_rt.py, RoundTrip.lean): `roundtrip : ((gates.flatMap (feats pre)) ++ lft.map get).Perm tf`,
axioms [propext, Classical.choice, Quot.sound], no sorry/native_decide. Problem, plainly: is every routing pip and
every LUT INIT bit of the decoded Lean netlist really in the bitstream's read-back, and is every such bit in the
read-back a gate of the netlist? Shown: the features recomputed by the kernel from the Lean gates' own fields
(73,065 pips: the gate name `TILE.DST.SRC`; 8,925 LUT6 outputs: one `TILE.SLICE.xLUT.INIT[b]` per set INIT bit,
265,971 bits), plus 16,090 explicitly listed leftover features, are exactly the 355,126 read-back features
(target/gcd_hw_03e82630.fromBit.fasm.xz, md5 418f36ae), each once. Not shown: (1) that a pip connects the right
electrical nodes (the decoder's wire-to-node merge from prjxray tileconn is not re-checked; the nextpnr cross-check
covers LUT/MUXF/CARRY4 pin drivers); (2) the FASM parsing (Python) and bit2fasm itself; (3) what the leftovers mean
(Python classes: FF/CE/SR config, IO and clock buffers, carry/output-mux selects, LUT DI routing); (4) O5, MUXF,
CARRY4 and constant gates (no INIT feature of their own); (5) the site-prefix table (prjxray tilegrid, 2,624 sites,
data). Measured: 64 subtrees + index check, 64 block merges (~3 min), 80 gate chunks (914 certificate slices; ~3.8
min and ~4 GB each, 3 at a time: 15:48-17:15), assembly 8 s. Built with private oleans; check.sh --wit builds it.
### progress 17:23 -- S1 part 2 CHECKED: every LUT5 output agrees with its LUT6 (o5_gates)
`FormalWit/RT/OAll.lean` (gen_o5.py, Formal/Target/LutPair.lean): `o5_gates : ∀ g ∈ gates, isO5 g → ∃ q ∈ gates,
o5match q g`, axioms standard. Plainly: an O5 output has no FASM feature of its own; its function is the low half
of its LUT's INIT. Shown: each of the 8,925 O5 gates follows an O6 gate with the same `<site>.<L>LUT.` name, reads
that O6's first five pins and has INIT = the O6's INIT mod 2^32, so with `roundtrip` its function is the
bitstream's. Not shown: that the O6's pin list is A1..A6 in order (the decoder's pin map; the nextpnr cross-check
compares pin drivers per physical pin). 80 chunks, ~10 s each (17:18-17:22).
### progress 17:23 -- what the round trip's 16,090 leftovers are (Python classes, decoded net 7c41591d)
5,460 slice output-mux selects (xOUTMUX.O6/O5/F7/F8/XOR/CY/xQ) and 3,206 carry selects (CARRY4.xCY0, PRECYINIT)
carry meaning: they pick what drives a slice's xMUX output and the carry chain's inputs. The decoder models them
as hop and CARRY4 gates and roundtrip.py re-encodes them, but the Lean gates do not carry the provenance needed to
re-encode them in the kernel, so `roundtrip` treats them as leftovers. That is the open semantic part of S1. The
rest has no meaning in the Spec: 4,183 FF configuration (FF outputs are free), 3,084 SLICEM LUT DI routing (no
LUTRAM), 157 clock-buffer/IO/config bits.
### progress 17:25 -- check.sh on the new default modules OK; full `check.sh --wit --committed` started
`check.sh Formal/Target/WitCut.lean Formal/Target/RoundTrip.lean Formal/Target/LutPair.lean`: OK, 537 declarations
audited. A full `--wit --committed` run (lake build of every committed module, then FormalWit one module at a time:
V9V4, V9V4c, RT, then the axiom audit) is running in the background (expected several hours); its result will be
journaled if the session lasts.
### progress 17:27 -- owner decisions 2026-11-01 read (PROGRAM.md, commit 94b7fd79); applying the g/κ fix to Spec.Adm
The owner approved (decision 3) `Adm` = d ∈ [(1-κ)·lerp(FAST_MIN,SLOW_MIN,c)/g, (1+κ)·lerp(FAST_MAX,SLOW_MAX,c)·g],
and says C's `adm_le_dmax` becomes false. That holds only if the separate global band [FAST_MIN/g, SLOW_MAX·g] is
dropped, so I apply the formula literally: Adm is the g-scaled corner window alone. Consequence, stated plainly: at
κ > 0 a delay may now exceed SLOW_MAX·g (up to (1+κ)·SLOW_MAX·g) or fall below FAST_MIN/g (down to
(1-κ)·FAST_MIN/g); before, the band clipped both. With it, `Gate.start` (the longest admissible delay, from which
the gate relation is required) becomes ⌈(1+κ)·SLOW_MAX·g⌉ per arc (was ⌈SLOW_MAX·g⌉); at κ = 0 it is unchanged.
At (g, κ) = (1, 0), the refutation's delay model, both forms admit exactly [SLOW_MIN, SLOW_MAX] at corner 1, so
the refutations' kernel checks are unchanged; their assembly lemmas are re-proved. Files: Spec.lean (A), Witness
(A), SpecSettle (C: dmax/dmin and adm_le_dmax/dmin_le_adm replaced, with the hypotheses they now need),
Ua1Static / ArbTSpec / SpecArbVacuous / SpecFb (B). Owner decisions 1 (new full-width target, when research
lands it), 2 (H_RUNT(w), w = 20 ps headline) and 4 (NetCorrectSeq is the target) are noted; 2 and 4 need no Spec
change (SpecRunt.lean exists). Audit row: requested in FOR-RESEARCH (the audit branch is not mine to edit).
### progress 17:33 -- Spec.Adm changed (owner decision 3); all six dependent files fixed; full check running
Done as planned (entry above): `Spec.Adm` = g-scaled window, `Gate.start` = max ⌈(1+κ)·smax·g⌉. Each dependent
file compiles against the new Spec (private oleans): Witness (adm_slow, start_slow re-proved), SpecSettle (C;
new `Sane`, `ArcsOK`, `arcsOK_of_wf`; `gate_stable`, `gateRule_sound`, `cert_sound`, `cert_sound_net` take
`Sane p` and, for the net, `N.WF`), Ua1Static (B; `ua1_numbers` still 865/852 and 852/860), SpecArbVacuous (B;
`delay_bound` restated per corner; `arbOK_excludes_handover` unchanged), SpecFb and ArbTSpec (B; proofs only),
plus SpecRunt, NetBase, WitBoundary, WitCut, ArbOKRepair. Statements that became FALSE and what replaces them:
SpecSettle.adm_le_dmax / dmin_le_adm (old band bounds) -> the κ-widened bounds with hypotheses; SpecArbVacuous
.delay_bound (∃M ∀c) -> ∀c ∃M. Also corrected Spec's ArbNodes docstring ("before any proof used it" was wrong,
audit). Full `check.sh --committed` started at 17:32. The FormalWit refutations and the round trip must be rebuilt
against the new Spec (their kernel checks do not involve Adm; at (g, κ) = (1, 0) both forms admit [smin, smax]).
