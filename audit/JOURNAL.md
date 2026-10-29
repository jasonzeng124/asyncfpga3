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

### progress 23:39
P7-onresearch in: tie-off false path in tighten.cell_boundary CONFIRMED on own ipow s3 route (-59 -> +4128 with
tie-offs dropped; conservative on the 4 routes but not by construction); GLS_SCALE_INST not applied to wire arcs in
wire-scatter mode CONFIRMED (silent); 28 inverted FAST tuples (all BRKH_INT) CONFIRMED by my own recount; CARRY4 /
SLICE_LATX sample-at-fire and FF X-hiding CONFIRMED; fid monitors gap CONFIRMED. Events8 and tcheck counts UNVERIFIED.

### progress 01:33
P7-kappa in (statement reading + own Python; Lean not yet run, build at ~3140/3270): ConstraintsKappa, CornerCode,
Involution*, TernaryChannels CONFIRMED by reading; OnNetlistArbKappa "exact per-pair thresholds" OVERSTATED (gap not
decided; own gap witness written); OnGcdArbKappa arithmetic reproduced, arc data vs route UNVERIFIED (routes not on
disk). audit/tools/run_p7k.sh waits for the build, then runs P7kAudit.lean + 7 mutants.

### progress 01:51
r7 in: BQ#3 full stack 16/16 at FAST_MIN/SLOW_MAX/band reproduced from a clean rebuild (sdf md5s match; I re-checked),
oracle matches gcd.c 16/16, unpatched-bits negative control fails exactly 5-8,11-13; bd_prims_sim fix, xray_delay
OUTMUX/FFMUX, seeds_fid INCOMPLETE logic CONFIRMED. No research refutation this pass.

### progress 01:56
Clean lake build of 6863284: EXIT 1. (a) Formal.Core.Delay.GLSPass (2a17ddf) does not compile: `d` unbound in
skew_fval (autoImplicit=false) -> REFUTED as checked. Root cause: formal/check.sh per-file mode runs `lake env lean`,
which ignores the lakefile's autoImplicit=false. (b) Formal.Net.MullerSI exit 137 = OOM (mine: too many concurrent
lean jobs); rebuilding alone. RigContract now builds -> CONFIRMED. P7k Lean: audit file compiles, 43 axiom lists
clean, 7/7 mutants fail (I diffed 3: real one-line semantic mutations). Killed the queued axiom audit (would have
raced the rebuild).

### progress 01:59
Rebuild of 6863284: every module except Formal.Core.Delay.GLSPass now builds (MullerSI OK alone; only GLSPass fails).
Per-module axiom audit (audit/tools/axiom_audit_par.sh, 2 jobs) started over all Formal modules.

### progress 02:01
P7-capstone in: gcd_hw_joint_witness CONFIRMED (out0 latches 6 = gcd 12 18; fed into the safety capstone itself;
mutants rejected) -- P5's open non-vacuity point closed. gcd_hw_live_final conditional (H_NO_DEADLOCK' open), no joint
witness. ipow_circuit_safe3 CONFIRMED with own overflow witness. Bnet generator reproduced from RTL (netlist sha256
matches). Pass 7 subagent work complete; axiom audit of 6863284 still running.

### progress 02:01
Research advanced to 73b08ca (CARRY4/LATX fid transport fix 78de9c2, DSP modes, acceptance --stack full, 8-seed BQ#3
full stack in progress). Pass-8 research subagent launched on clean worktree ~/wt-r8 (73b08ca). Formal unchanged.

### progress 02:29
Axiom audit of 6863284 done: 422 modules, 66779 constants, 0 bad, 1 no result (GLSPass, does not compile). Pass 7 on
formal complete.

### progress 02:33
r8 in (research 73b08ca): CARRY4/LATX fid transport fix CONFIRMED (X items still open by design); DSP model function
CONFIRMED but makes the DSP hard item unfalsifiable (x counted as MATCH) -> OVERSTATED; acceptance judge_full counts a
crashed unpatched run as full 'reproduces the board' (I read acceptance.py:519-538) -> OVERSTATED; BQ#3 seed 3 SLOW_MAX
reproduced with identical md5s and laps.

### progress 02:43
P8 (formal B 10-27 commits) in: Necessity rows, KleeneBox, LinkExact, ResetGcdVec2 CONFIRMED with scope notes; CTree
JSON 'exact' label mildly OVERSTATED; ArbPin2 per-arbiter numbers' provenance unverifiable (extraction not committed).
All audit files compiled against the 6863284 build, axioms clean, mutants fail. Both branches idle; next: wait for new
heads (heartbeat).

### progress 03:10
Both branches idle (formal 6863284, research 6edd071). Launched ev8 agent: reproduce Events8 gcd_hw slow/fast CLEAN and
gb seed-d ENTRY failures (UNVERIFIED row) with own route + own computation.

### progress 03:30
ev8 in: all 4 gcd_hw R5 seeds rebuilt (SDF md5s = recorded). Events8 slow/fast CLEAN CONFIRMED (ENTRY); gb seed-d
3 failures OVERSTATED: ua1 (-94) passes (+45) once prjxray a5lut->AMUX is charged (formal bands omit it on all 10,223
O5 arcs); -42 ps Events5->8 shift = per-pin LUT delay; A-events8.md:74 misstates Events5 (all 3 were listed, verified).

### progress 03:50
Branches idle. Launched r9: own full-stack BQ#3 seeds 4 and 5 at SLOW_MAX/FAST_MIN, ready to compare with research's
8-seed table when posted.

### progress 04:31
Research new: 54f2ce6 fasm2net decodes unused GND-source LUTs (seed-7 false livelock; seed 5 had 8 floating pips),
cf1fbf4 acceptance lut-pinmap MATCH. I read the MATCH json: genuine 7-vector non-completion, same dead set as my r7
reproduction -> CONFIRMED. Forwarded the decoder fix to the r9 agent (seeds 4/5 are affected: rerun with both decoders,
check the const-0 assumption against the routed JSON). Worktree ~/wt-r10 = cf1fbf4.

### progress 05:11
Research 6e679a5 (DSP hard items MATCH via x) read: disclosed caveat; my OVERSTATED label stands. d958b9d soft ring
items 'inside the band' -- noted, not audited yet. Seeds 7/9 FAST_MIN/SLOW_MAX rows posted; r9 still running 4/5.

### progress 05:52
Research 666ea57: gen.py dropped 1134/1218 SETUPHOLDs (negative side), so the default GLS flop setup/hold check was
silent on 284 flops in all earlier PASS results. Launched r11 agent (verify counts with own parser, rerun BQ#3, forced-
violation negative control, FFX/BUFGCTRL fid changes 923305d). Worktree ~/wt-r11 = 2f6dc9b.

### progress 06:12
r11 in: SETUPHOLD drop CONFIRMED (my own grep: 1218 lines, 1134 negative, rest SR); forced-violation control fires only
with fixed gen.py; BQ#3 still passes with margin. Historical default-GLS passes OVERSTATED on flop timing; BQ#1/#2
unverified under the fix. 923305d fid flop/BUFG changes CONFIRMED.

### progress 06:32
Research 82660cb: BQ#3 8 seeds x 2 corners 16/16. I recomputed every mean/range from the TSV: exact. Caveat: run on
fid 78de9c2 + 54f2ce6, before the SETUPHOLD fix, 923305d and 2nd decoder fix. Also new: d4896fe registered DSP48E1
model + dsp_areg property test (not yet audited). r9 (seeds 4/5) and r12 (BQ#1/#2 under fixed SETUPHOLD) running.

### progress 06:36
r9 in: BQ#3 seeds 4 and 5 at FAST_MIN/SLOW_MAX reproduced from clean, identical to research's TSV (md5s, laps). Seed 5
old-decoder PASS was luck of vector coverage (8 floating pips, unexercised ushrsi2 inputs); new decoder correct for
those sinks. 4/8 seeds now independently reproduced.

### progress 06:52
r13 in (d4896fe): registered DSP model matches yosys cells_sim on 1270 configs; but the dsp_areg FAIL rests on an
unverified decoder assumption (AREG=2 reading), and gen.py:173 defaults missing DSP register params to 0 (primitive
default 1) -- I read it. BQ#1/#2 re-run (r12) still running.

### progress 07:09
r12 in: BQ#1 and BQ#2 rebuilt (SDF md5s match) and re-run under the fixed SETUPHOLD check: 16/16, 0 violations, laps
identical, hold margins >= 425 ps; forced violation fails the run. All three board candidates' default-GLS passes stand.

### progress 07:55
New heads: formal 3e63dc1 (+24 commits: check.sh per-file now passes -DautoImplicit=false -- read, will test; GLSPass
withdrawn; kappa exact/tight withdrawn; Bj5 JSON; RigSrc joint witness; Necessity5, LutFbBridge, IpowCells, KleeneWin;
Fid3 GLS table), research 072f5f9 (acceptance status). Clean build of 3e63dc1 started in ~/wt-f9 (Mathlib packages
copied from wt-f7, same manifest). Agents: P9 (formal claims), r14 (Fid3 reproduction). Freed 5 GB of old work dirs.

### progress 08:06
r14 in: formal Fid3 GLS table reproduced (17 rows CONFIRMED, incl. resolver centre bias TLOOP-WIN/2 vs ~TLOOP/2, which I
read at fid_core.vh:82); Fid3's rise!=fall remark REFUTED in direction. Build of 3e63dc1 and P9 still running.

### progress 08:31
3e63dc1: clean build EXIT 1 only on withdrawn GLSPass (still under Formal/). Their fixed check.sh now FAILS GLSPass
(I ran it) -> fix CONFIRMED. P9 in: RigSrc joint witness CONFIRMED (closes UNVERIFIED row); Necessity5 iffs, KleeneWin,
IpowCells (contracts assumed), LutFbBridge (narrower than 'every') CONFIRMED; Bj5 JSON fixes CONFIRMED, 2 labels mild.
Axiom audit of 3e63dc1 running.

### progress 09:03
3e63dc1 axiom audit: 436 modules, 68113 constants, 0 bad, 1 no result (withdrawn GLSPass). r15 (ring128 summary,
BQ#2 full stack at 21cae6b) running.

### progress 09:13
Formal advanced to 84bc9e4 (+60 commits: GLSPass fixed, exact kappa thresholds, OUTMUX in Events8 bands, gcdnet
generator, Core/Prims, Involution trace/loop, ResetCapstone, ZeroDelayNet, ContractBridge, GLSResolve on research fid).
Clean build of 84bc9e4 in ~/wt-f10 (Mathlib packages moved from wt-f7, same manifest; wt-f7 removed). Agents P10a
(responses), P10b (A prims/involution/XSound2), P10c (B/C reset, zero-delay, ring), r16 (GLSResolve/GLSFid on research)
launched; r15 running.
