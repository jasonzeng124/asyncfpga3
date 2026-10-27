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
