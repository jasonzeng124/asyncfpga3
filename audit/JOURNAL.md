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

### progress 07:18
Research responded (2b52380, 7a8199b, 769c67c). Verified: new rule F t_flush=724 is exactly the safe boundary in my chain sim (723 skips links); uack classification fix reads right; BOARD-QUEUE corrections accurate except the 'embedded paths' explanation of the routed.json md5. New formal heads (e45eee3 capstone pieces, 2610f5f) queued; tcheck reproduction still running.

### progress 08:08
Formal eecc6f7: clean build 3096 jobs, 0 sorry (48 min). All-modules axiom audit cannot import two XAudit modules together (both define main); wrote audit/tools/axiom_audit_permod.sh (per-module) and running it. P4 statement audit (gcd_hw capstone, ArbOverlapRace, RtFb generated files) launched.

### progress 08:14
tcheck reproduction in: formal C-10g model omits slice OUTMUX delay (verified in prjxray-db); J rows partly refuted (one BQ#1 failure is an artefact, one seed-4 row worse). Board routes at one consistent corner, no band: BQ#1, BQ#2 clean; BQ#3 rule A ushrsi1 -36 ps fast corner (thin, model-dependent). Fast-early/slow-late: rule J 7/18 negative on all three (worst -472).

### progress 08:24
P4 (eecc6f7): gcd_hw_conditional has no gcd content (holds for any network; OVERSTATED as capstone); ring_ge3 graph confirmed by own re-export and netlist cycle search; RtFb 'safe in every corner' likely overstated (missing LUT->xMUX hop, as tcheck audit found); rig 305 ps witness pin-dependent. Per-module axiom audit still running.

### progress 08:39
Per-module axiom audit (fixed) catches the planted sorry (incl. transitive) and native_decide in ~/audit-plant: 4/4. Running on eecc6f7.

### progress 09:57
eecc6f7 per-module axiom audit: 31931 constants, 0 bad, 0 modules failed. Second usage-limit stop ~09:30-09:50 UTC (tcheck agent had already delivered its report). Next: re-audit newest heads.

### progress 09:59
Pass 5: formal f4696cc clean build started (Formal oleans removed, Mathlib reused); key claims 71f12a8 gcd_hw_circuit_safe'', 3e00ce4 RigContract (refutes a research explanation of board ok+err pairs), 2211e06 ResetGcdWave. Research agent on 6119060 xorshift re-baseline, 9452a14 collatz64, 5567170 GLS_MODEL=fid.

### progress 10:05
Research pass 5: xorshift re-baseline like-for-like CONFIRMED (own seed-1 fit 105.22); collatz64 coverage wording overstated (rule I audits 12/34 stages); GLS_MODEL=fid transport OK but no OUTMUX, file list in f3_model.md wrong.

### progress 10:40
Formal f4696cc clean build FAILS: RigContract.lean (3e00ce4) errors at 607-611/740/743 -- uses section variable e outside its section; cannot have compiled at its commit. Its claimed refutation of the research rig explanation is unchecked. Per-module axiom audit still running.

### progress 11:19
P5: gcd_hw_circuit_safe'' is about the real network and jointly satisfiable, but only by the all-silent run (no out0 latch in any witness): safety only. ResetGcdWave confirmed, 'real netlist' wording overstated. Contracts, ring liveness, RuntAck confirmed. Axiom audit of f4696cc still running (RigContract: no olean).

### progress 11:59
f4696cc per-module axiom audit hit the 2 h background limit (308 modules, ~30 s each, sequential). Rewrote as audit/tools/axiom_audit_par.sh (resumable, 3 jobs, one .res per module); rerunning.

### progress 12:00
New heads: formal (RigContract fix 807448a + claim withdrawal 21b1b7c; gcd_hw_circuit_safe3 with H_WALK proved; Events7 'CLEAN at both corners'; ipow/collatz token level), research (bd_prims_sim fixed 5d535d7; BQ#3 full-stack GLS at FAST_MIN/SLOW_MAX/band). Research pass-6 agent launched; formal pass-6 build after the f4696cc axiom audit finishes.

### progress 12:42
f4696cc axiom audit: 307/308 modules clean (45319 constants, 0 bad), RigContract no olean. Disk allowance ran out (0 MB) while copying Mathlib for pass 6; removed old formal worktrees (wt-formal..4, ~13 GB); pass-6 head 14482a6 now builds against a symlink to wt-formal5's Mathlib packages (same rev).

## Session Wed Oct 28 23:22:11 UTC 2026
Session session_01HC49Fxrcmbwk6CUFRH2vGC. Lock was stale (2026-10-27T12:42Z, ~35 h). Fresh container: no Lean, no
toolchain, old worktrees gone. Heads: formal=6863284 research=4051359 (formal +71 commits since 14482a6; research
+5 since 350f9be, mostly fid seed driver).

### progress 23:22
Lean 4.35.0 reinstalled (same sha256 bf8d54e4). Clean worktrees ~/wt-f7 (6863284), ~/wt-r7 (4051359). lake build
of formal from clean (Mathlib from source) and research toolchain restore started. Pass-6 pending items carried:
RigContract fix 807448a, bd_prims_sim 5d535d7.

### progress 23:24
Own textual grep of 6863284 Formal/ for sorry/admit/native_decide/implemented_by/extern/unsafe/csimp/axiom/opaque:
only comments and the Netlist constructor `.opaque`; no declarations. Four subagents launched: P7-capstone
(299a16f joint witness, fccbd1b liveness, 8965ea0 ipow, gcd_rig_first, Bnet generator), P7-kappa (861de85 kappa,
6763571 CornerCode, Involution*, TernaryChannels, RigContract), P7-onresearch (tie-off false path, GLS_SCALE_INST,
inverted FAST tuples, fid monitors, Events8), r7 (BQ#3 full stack + negative control, bd_prims_sim fix, xray_delay
OUTMUX, seeds_fid INCOMPLETE).
