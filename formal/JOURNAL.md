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
