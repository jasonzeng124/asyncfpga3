# Audit journal

## 2026-10-27 -- branch created
Program in audit/PROGRAM.md.

## Session Tue Oct 27 03:27:09 UTC 2026
Session session_01HC49FyHr5QA8JKjiqPQGZv. Lock was free (epoch placeholder).
Audited heads: formal=71ee3e8 research=19a93c1.

### progress 03:32
Lean 4.35.0 from GitHub zip (audit/tools/install_lean.sh, no elan). Clean worktrees of
origin/claude/formal 71ee3e86 and origin/claude/research 19a93c1. `lake build` of formal running
(Cells built quickly; Mathlib from source in progress). Research toolchain restoring via
cloud/setup-toolchain.sh into ~/audit-tc (cache hit). Textual sorry/axiom grep clean (2 hits in
comments). Wrote audit/tools/axiom_audit.sh (own collectAxioms over every Formal.* constant).
Subagents running: A/B/C statement+witness+mutation audits, transcription fidelity, GLS
sample-at-fire reproduction, rules J/I/F reproduction. #1 bitstream sha256 matches.

### progress 03:33
Toolchain restored (nextpnr sha256 9c732bc6303458df = committed toolchain.txt). BQ#1 route rebuild started in
clean worktree wt-rb1 (19a93c1). BQ#3 "~9%" found OVERSTATED from their own tables (8-seed vs 4-seed mean);
see audit/findings/research-stats.md.

### progress 03:41
Subagent results in: GLS findings (4 CONFIRMED, research prims.v "identical timestamps" comment OVERSTATED),
rules J/I/F (shard B's "68-161 ps wrong way" REFUTED: fast/slow corners misread as rise/fall; I verified in
prjxray makesdf.py; research bd_prims_sim.v has the same misreading -> REFUTED), shard C (3 OVERSTATED, rest
CONFIRMED, 10/10 mutants break), transcription (0 mismatches). BQ#1 rebuilt from clean: sdf md5 and bit payload
identical; routed.json md5 not reproducible (embedded paths). Still running: shard A and B statement audits;
formal lake build (Mathlib).

### progress 03:46
Formal clean build OK (981 jobs). Own axiom audit: 6707 constants, 0 bad; planted-sorry control caught 4/4. BQ#1 routed GLS with own judge + negative control delegated.

### progress 03:47
Shard A audit in: 2 OVERSTATED (rule A κ≤1/11 vs code truncation, verified tighten.py:1106; involution transfer lemma not formalised), minor wording; rest CONFIRMED with witnesses. Pass-2 build of formal head d420b53 started (wt-formal2).

### progress 03:54
Shard B audit in (1 OVERSTATED + scope notes; 13 CONFIRMED; new necessity result for C-element fork wait). Formal head d420b53: clean build OK, own axiom audit 9121/0 bad. Launching statement audits of the new modules.

### progress 03:59
Python claims in: C-10c numbers reproduce exactly but headline overstated (one silicon ring; global median scale drives the ratios). Research fasm2net checker works (negative controls) but reports NOT EQUIVALENT on the reproduced BQ#1 route: 3 A6 pins tied GND in JSON, unrouted, VCC on chip (harmless for those LUTs).

### progress 04:00
BQ#1 routed GLS reproduced with own judge: 16/16 correct (6149 laps); negative control (uori4 zeroed) fails as it should. routed.json md5 deterministic across my 2 runs (5703...) but != claimed 1c6a1fb9: unresolved.

### progress 04:07
Pass-2 A/B (d420b53): ArbHeldTimed/ArbHeldTimed2 'prjxray arcs' use the 56/124 rise/fall misreading (verified ArbHeldTimed.lean:583-615) -> threshold/margins are artefacts; MOUSETRAP 'iff' is only sufficiency. XSim, SAF (matches GLS value-change scheduling), Lib INITs, TernaryPhases, MuxTree, ArbBinary CONFIRMED. Running: C2 (import/fasm/ringcheck/rules), BQ#2/#3 + rule F gap.

### progress 04:16
Pass-2 C (d420b53): import/bitstream/RingCheck/Rules CONFIRMED with own resynthesis, own routes and bit read-back; two small overstatements (402 vs 403 ps; Kleene 'specs' are same-INIT transcriptions). Remaining: BQ#2/#3 agent.

### progress 04:27
Pass 3 started: formal head c5c6d8b building (ArbCorners 482f624, PipeTimedN ac753c1 new); research agent on eda0c0c bit controls, 9a02f6f collatz64, speedup tables. Research bd_prims_sim.v still has the 56/124 rise/fall comment at origin head.

### progress 04:57
Usage limit hit ~04:30-04:50 UTC: BQ#2/#3 and research pass-3 agents stopped mid-run and the formal3 build was killed at its time limit (new head imports ~2130 Mathlib jobs). All three restarted/resumed at 04:57.

### progress 04:58
BQ#2/#3 reproduced on default seed: sdf md5s match, GLS 16/16 both (own judge), #3 +8.7% loop vectors on this seed; rule F's omitted hop term leaves BQ#3 safe (+888 ps). #2 routed.json md5 does not reproduce while #3's does -> REFUTED row (recorded md5s for #1/#2 not from this commit's build).

### progress 05:02
Research pass 3 (9a02f6f): xorshift 1.71x/1.72x REFUTED as comparisons (6- vs 14-vector fits; verified journal lines 749/757); dsp_areg control OVERSTATED (detects an illegal injected state, not the real AREG=2 bug); collatz64 provenance overstated (named tool commit lacks rule F) though seed 3 with current tools is clean; bd_prims_sim.v still unfixed. Waiting on formal3 build.

### progress 05:57
New heads: formal 297d12c (1e7947a tcheck on 4 gcd_hw routes claims rule-pass/tcheck-fail rows incl. J 67/70 -> board risk; reproduction launched), research 7ad18c4. P3 (ArbCorners/PipeTimedN) agent running.

### progress 05:59
P3 (c5c6d8b): ArbCorners/PipeTimedN proved as stated; OVERSTATED: ArbCorners assumes q on ugrant pin A3 but formal's own read-back routes use A5 in 3/4 seeds (verified A5 arcs in prjxray CLBLM_R.sdf) -> rule J 8 ps optimistic not 26 conservative; guarded-rule-J FAST_MIN coverage needs a single wire ratio (cex -118.5 ps); PipeTimedN unit witness degenerate (auditor built a non-degenerate one).
