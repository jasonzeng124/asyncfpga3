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

### progress 09:20
r16 in: formal's GLSResolve findings on research fid reproduced with own C-element bench; fid_core.vh:35-37 'applied
late, not lost' REFUTED (read the lines myself; follow pulses <= TLOOP lost 40/40). GLSFid transcription CONFIRMED.

### progress 09:27
r15 in: ring128_summary soft MISMATCH reproduced exactly from 8 rebuilt routes (md5s match), grading correct; unstated
~1/3 false-fail rate of the all-7-inside criterion. BQ#2 full stack SLOW_MAX 16/16 reproduced. P10a/b/c running.

### progress 09:46
P10b in: Core/Prims arcs CONFIRMED (506/506 vs prjxray); Seq flop windows SLICEL-only -- SLICEM hold 262 > model 241 (I
checked slicem.sdf:618) -> OVERSTATED; 'X then definite' assumed; DSP and XSound2 minor overstatements; Involution
trace/loop CONFIRMED.

### progress 09:58
Formal 84bc9e4 clean lake build EXIT 0 -- first fully clean build (GLSPass fixed). P10a: all five answers to audit rows
CONFIRMED (exact link_arb thresholds incl. my 200/1103 point; gcd arb bracket; E8Mux agrees with my ev8 signs; gcdnet
generator byte-identical). Axiom audit of 84bc9e4 running; P10c running.

### progress 09:59
P10c in: ResetCapstone/ResetWitness2 (D=2,W=1), ZeroDelayNet, ContractBridge, IpowCellsT, ArbNoWithdraw, C-9d rings,
Necessity6 all CONFIRMED with scope notes; nothing refuted. Pass 10 subagents done; axiom audit of 84bc9e4 running.

### progress 09:59
Formal advanced again (424e8ee): self-reported refutations -- 9df5915 H_NO_DEADLOCK' false (kernel run), fccd12c HARB7
false on real arbiter runs so Events8/9 CLEAN covers no real run. Annotated the two affected REPORT rows as pending
re-check. Research efc6538: BQ#3 2x scatter fails seed 9 (self-reported). Pass 11 after the axiom audit.

### progress 10:45
84bc9e4 axiom audit: 503/503 modules, 78333 constants, 0 bad -- fully clean. Pass 11: clean build of formal 54b9e6e in
~/wt-f11 started.

### progress 10:54
r18 in: formal's arb_double_ack reproduced on my own bd_arbiter fid bench (both race directions; up to 37% of resolver
commits double-ack at server 600 ps; clean only >= ~1.0-1.2 ns); research's arbiter tests don't exercise it. Read
bd_arb.v:215-232 (metastable tier documented as NOT EXCLUDED). P11a and r17 running; build of 54b9e6e running.

### progress 12:10
P11a in: gcd_hw_live_final NOT vacuous (joint witness), but H_NO_DEADLOCK' hid start-release; final2 conditional on open
H_NO_DEADLOCK''. Events8/9 CLEAN OVERSTATED (rests on HARB7, unsound abstraction); gcd_hw_circuit_safe_phys moves
H_BUNDLE rather than discharging it; gcd_rig_all, KCap confirmed. Build of 54b9e6e had 2 OOM kills (concurrent lean);
rebuilding.

## Session Thu Oct 29 14:32:35 UTC 2026
Session session_01HC49Fw3HukeyddasJhP17A. Lock was stale (2026-10-29T12:10Z, ~2.4 h). Fresh container again: no Lean,
no worktrees. Heads: formal=1fd99ef0 (+48 since 54b9e6e; last non-WIP 6f76d839), research=034636b2 (+5 since efc6538).
Carried: build/axiom audit of 54b9e6e never finished (OOM); r17 never reported.

### progress 14:37
Lean 4.35.0 reinstalled (sha256 bf8d54e4, same). Worktrees ~/wt-f12 (formal 1fd99ef0), ~/wt-r12 (research 034636b2).
Clean lake build of 1fd99ef0 and research toolchain restore (JOBS=2) running. New own keyword scanner
audit/tools/kwgrep.py (comment/string-aware): 722 files under Formal/, 1 hit = Netlist constructor named `opaque`
(identifier, not the keyword); catches a planted `sorry`. Subagents P12a (shard C phys2-5, O4b, ChainSettle, 8z4),
P12b (shard B FiniteNet, SelfAuditB9, ArbCounterRuns, ArbAMergeRun, MuxN, Bj11), P12c (shard A InvolutionExp,
Events9Sel/Prefix/Arb, CornerCell/BandCheck, XInert) launched.

### progress 15:32
Toolchain restore EXIT 0 (cache branch; nextpnr sha 9c732bc6303458df). Lean build still in Mathlib (~2780 jobs).
r19 (BQ#3 seed-9 2x scatter) launched; P12a/b/c reading statements, writing findings as they go.

### progress 16:12
r19 in: BQ#3 seed-9 2x-scatter failure CONFIRMED from my own rebuild (sdf 74511ca2 matches; exactly vectors
2,3,9,11,13,15; threshold between 1.3125x and 1.375x; log-normal still fails; placement/factors confirmed, comparator
X30 not X30-31). OVERSTATED: BOARD-QUEUE #3 "8/8 seeds pass at 1x, 7/8 at 2x" -- the cited TSV has scatter rows for
only 4 seeds (I counted the rows myself); no logs. LOGN identity CONFIRMED but quoted md5 ebfb714c not reproduced.

### progress 16:21
Clean lake build of formal 1fd99ef0: EXIT 0 (3570 jobs). Axiom audit of 1fd99ef0 started (2 jobs). P12b in (I re-ran
its Audit.lean, rc 0, and read FiniteNet.lean:611 myself): Bfin2 chain derivation OVERSTATED (per-link existential
chain, witness is a relabelling); SelfAuditB9 CONFIRMED but withdrawal incomplete (same hole in Bnet chains and
infinite-run forms; status table/docstrings not updated); ArbCounterRuns, ArbAMergeRun, Bj11 CONFIRMED.

### progress 16:21
P12a in. Main finding (I read CapstoneRefine.lean:191 and compiled F1_TxWin.lean myself, rc 0, standard axioms):
TxWin.count quantifies over ALL k, so a channel with a TxWin is offered infinitely often; on any terminating gcd run
the dag/cert certificates are impossible (only exempt = assumed Held) and phys5_cls/_gen hypotheses are false
(out0 infinitely often from one start). phys4/5 "root certificates with tcheck rows" and "data fields from tcheck
rows" OVERSTATED. H_FN 176/221 OVERSTATED (96 really checked); 10o "9 lines" miscount (11); O4b fix only frozen-run
witnesses. phys2/phys4 Lean, ChainSettle iff, 8z4 CONFIRMED.

### progress 16:22
P12c in: InvolutionExp, Prefix, BandCheck/CornerCell CONFIRMED (own sympy + independent loop sim; own inverted-arc
count 20/37928). Events9Sel/Arb OVERSTATED: corrected arbiter core leaves q free, design_verdict9arb gets HARB7 from
HARB7' by projection; FEASIBILITY:438-443 still says CLEAN without the refutation (I read it). XInert "Verilog
default" mild. Pass 12 subagents all done. Axiom audit of 1fd99ef0 running (30 modules so far).

### progress 16:23
Research advanced to 103fbbe9 (answers to r16/r18: new resolver 055edd7, arbiter round-trip requirement, chain_dist,
BQ#3 reroute). Pass 13: r20 (new resolver vs my r16 bench + adversarial), r21 (double-ack under new resolver with my
r18 bench, requirement derivation corner, BQ#3 default-seed round-trip margins) launched. Worktree ~/wt-r13.

### progress 16:41
r20 in (I read nonmono.log myself): research's resolver rewrite fixes r16's follow_lost (my own bench: 0/40 -> 40/40).
Their "30/10" is 33/7 at 103fbbe9; x changes during resolution can still be lost; NEW non-monotone behaviour (second
drive cancels a pending commit: 3/40 and 5/40 latch with one pulse but not with two; old 0); wrong FB mask silent.
Axiom audit of 1fd99ef0 continuing; r21 running.

### progress 16:47
r21 in (I read arb_roundtrip.py's single-column design myself): their arbiter numbers reproduce on their bench and on
my rebuilt BQ#3 seed d (sdf 61e14755; 0/18, worst 691, own script exact). OVERSTATED: the 1200->1095 shift is bench
wiring, not the resolver (my r18 bench unchanged under the new core); "static lower bounds" uses one SDF column for
both sides of a race (mixed corners: -769 ps, 2/18); hold-window ">= 399 ps" is 19 ps on BQ#3 seed d.

### progress 17:05
Axiom audit of 1fd99ef0: 487/722 modules, 0 bad, 0 no-result so far. Formal head unchanged (1fd99ef0); research
b726f74b (progress only: new resolver reproduces BQ#2 seed 6 laps).

### progress 19:47
r22 in: BQ#2 seeds 6/7 full stack SLOW_MAX under the new resolver CONFIRMED from own builds and own gcd judge
(33/27/39, 31/25/36; old resolver byte-identical) -- but the resolver never fires on these runs, so the identity
tests nothing about it; negative control works and shows lap counts alone miss wrong results.
Axiom audit of 1fd99ef0 was interrupted (process gone; container apparently restarted ~17:33): 487/722 modules,
75477 constants, 0 bad, 0 no-result (audit/logs/axiom_par_1fd99ef0_partial.txt). The remaining 235 modules are
UNVERIFIED for this commit (all earlier commits were fully clean).
NOTE: list_triggers shows every scheduled task on the account (this audit routine, formal A/B/C, research, and my
own check-in) was disabled at 17:33 UTC. I take that as the owner pausing the program: I am not re-arming check-ins
or starting new long jobs. Lock released below. Session ends here with the branch pushed.

## Session Fri Oct 30 19:18:20 UTC 2026
Session session_01HC49FxkHmCaCFxFQ52sz3w. Lock was released by the previous session (2026-10-29T19:47Z). The routine
fired again, so I read last session's "program paused" note as superseded. Fresh container again. Heads:
formal=5a1ee8d2 (only owner PROGRAM.md/settings changes since 1fd99ef0; Lean sources identical), research=4b922e9b
(+49 since b726f74b).

### progress 19:23
Lean 4.35.0 reinstalled (sha256 bf8d54e4, same). Clean lake build of formal 5a1ee8d2 (= 1fd99ef0 Lean) in ~/wt-f13
running, to finish the axiom audit that was cut off last session (235/722 modules unchecked). Research worktree
~/wt-r14 = 4b922e9b. Toolchain: research's cache key no longer matches any cache branch. setup-toolchain.sh now
has an `XRAY_DB_REV=` line that the key's `^[A-Z_]+_REV=` grep picks up, even though the comment says it is "not
part of the toolchain fingerprint" (harmless, it only forces a rebuild). I unpacked toolchain-cache/d7ce266c (the
one I used last session) and am re-running setup with NO_CACHE=1, so cells/verify/toolchain.sh decides whether
it is valid.
Recomputed from the raw TSVs myself: BQ#3 new-resolver table: SLOW_MAX 8/8, vec 6 mean 32.75 (31-34); FAST_MIN
8/8, mean 89.625 (83-94). Every laps triple equals the old-resolver table (last row per seed+column). CONFIRMED.
BQ#2 seeds 6-9: 8/8 PASS, vec 6 31-33 / 86-93 (TSV). For BQ#2 seeds d,3,4,5 there is no committed TSV or log,
only journal prose ("28-32, 77-86"), so their half of "8 seeds x 2 corners" is UNVERIFIED from data.

### progress 19:35
Toolchain: fingerprint OK (nextpnr 9c732bc6303458df) on the d7ce266c cache with NO_CACHE setup. r23 (BQ#2 seed-6
2x-scatter failure, research 70c7237e/f5182bcc): my own route of BQ#2 with NEXTPNR_SEED=6 reproduces sdf c4ec8664
and xray sdf 1f7f03ea (prjxray-db 0a0added). Region factors recomputed with my own code (audit/r23/regionf6.py):
draw 1, 2x: (1,5) 0.4919 (1/f = 2.033), (0,5) 1.5573, (0,6) 1.5409 -> "0.49 / 1.56 / 1.54, x2.03" CONFIRMED.
Note that the datapath's stated span Y56-76 also covers region (0,7), factor 1.028, which the claim leaves out.
gen.py 9c39512e read: in arc mode interconnect already went through perturb() (and so through SCALE_INST), so the
fix changes only wire mode, and only under SCALE_INST or SCATTER_ONLY+REGION. "No result depends on it" is
plausible. The exact GLS_SCALE_INST prefix for the intervention is not recorded anywhere (journal prose only).
S13 MC file: I re-tallied it from the rows: 1x guarded<0 34/38, raw 15/38; 2x 37/37, 33/37, matching its SUMMARY
(arithmetic only; the rule-A runs themselves were not reproduced).
Running: full stack 2x draw 1 on vectors 7,8,12 + control 6. Lean build of 5a1ee8d2 in Mathlib.

### progress 19:50
r23: BQ#2 seed 6, full stack (bits-decoded netlist, xray SDF band, fid), region 0.32 + wire 0.252, draw 1, resolver
055edd7 (research 4b922e9b worktree): vectors 7, 8, 12 each give laps=1 errs=1, then nothing to 150 us. Control
vec 6 passes (48 laps, errs 0). The failure is CONFIRMED exactly (audit/r23/s2x.log; netlist_baked 9657121d).
Placement from my own extraction (audit/r23/place6.py): uori3 chain = 20 LUTs at X12-13 Y53-55, all in region
(1,5); datapath = 55 cells at X0-5 Y56-76, in regions (0,5) 27, (0,6) 22, (0,7) 6. CONFIRMED (6 cells sit in
the 1.03 region). Running: the intervention (uori3.udly x2.033), a placebo (uori4.udly x2.033), then 1x.

### progress 20:23
(Earlier headings in this session corrected to the real commit times: 19:23/19:35/19:50.)
r23 1x (0.16/0.126, draw 1) on my seed-6 route: vectors 7/8/12/6 PASS 184/156/42/51 laps, errs 0. That matches
their "seed 6 1x PASS 51/42/61" for v6/v12. Intervention attempt 1 used a hierarchical prefix and matched 0 arcs
(fid names are site/BEL). gen.py exits loudly on that, which is a good guard. I rebuilt the list from NEXTPNR_BEL
(20 BELs -> 159 arcs scaled). Intervention, then the placebo (uori4 chain), are running. Lean 5a1ee8d2 build
still in Mathlib.

### progress 20:45
r23 intervention CONFIRMED exactly: uori3 chain x2.033 (159 arcs) -> vectors 12/7/8 PASS 39/175/146, errs 0,
identical to the research numbers. My placebo (uori4's chain, same factor) still fails vec 7, so the effect is
specific to uori3. REPORT.md rows added (pass 13). Lean build of 5a1ee8d2 still in Mathlib (~2700 jobs).

### progress 20:56
Placebo complete: uori4 chain x2.033 -> vectors 7, 8, 12 all still fail (laps=1, errs=1). r23 C fully CONFIRMED.
chain_regions unconstrained row (12.9 / 49.1 / 16 of 50) reproduced with my own Manhattan-centroid code. uori3 is
not among the most distant chains (20.2), so distance is a weak proxy for the region-straddle exposure (finding
r23 G). Started: BQ#2 seed 8 route + full 16-vector 2x draw 1 (claimed PASS 46/36/53).

### progress 21:22
Clean lake build of formal 5a1ee8d2 (Lean sources = 1fd99ef0): EXIT 0, 3570 jobs, 0 errors
(audit/logs/formal_build_5a1ee8d2.log). Keyword scan (kwgrep.py) of the 722 Formal files: 1 hit, the same Netlist
constructor named `opaque` as before. Planted-sorry self-test: my collectAxioms check reports "BAD planted uses
sorryAx". Full per-module axiom audit (722 modules, 2 jobs) started; results go to ~/axres_5a1ee8d2.
BQ#2 seed 8 route: sdf b7733e23 and xray b93e281a REPRODUCED. 2x draw 1, 16 vectors running (0-3 pass so far).

### progress 21:33
Axiom audit 5a1ee8d2: 169/722 modules, bad 0, no-result 0 (snapshot audit/logs/axres_5a1ee8d2.txt). BQ#2 seed 8 2x
draw 1: vectors 0-6 pass, vec 6 = 46 laps as claimed. Queued next: BQ#2 seed 4 route + SLOW_MAX full stack (one
of the d,3,4,5 rows with no committed data).

### progress 22:04
Axiom audit of formal 5a1ee8d2 (Lean identical to 1fd99ef0) COMPLETE: 722/722 modules, 95239 constants, bad 0,
no-result 0. This closes last session's gap. REPORT row added. BQ#2 seed 8 2x: vectors 0-12 pass (v6 46, v12 36,
both as claimed); 13-15 running.

### progress 22:15
BQ#2 seed 8 2x draw 1, full stack, 16/16 PASS errs 0, v6/v12/v13 46/36/53: CONFIRMED exactly. chain_regions
"unconstrained worst +914" reproduced by running their tighten.py on my reproduced seed-6 SDF (50 cells, umux5
+914). This is reproduction of a quoted number, not independent evidence that rule A is right. Running: BQ#2 seed 4
route + SLOW_MAX full stack, then seed 7 2x.

### progress 22:18
Research moved on (a6ae390e): BQ#2 1x draw 1 PASS seeds 6-9 (seed 6 already reproduced, 51 laps). The chain-region
placement lead is parked with negative results (2x still fails on the constrained route, draws 1 and 2). These are
self-reported negatives, low priority. BQ#2 seed 4 route: sdf b1b4b951, xray f5fa0f9a. No md5 for this route is
recorded anywhere on research (git grep), so its reproducibility cannot be checked. SLOW_MAX full stack running
(claimed only as "28-32" for d/3/4).

### progress 22:29
Coverage check: 25 theorems named in FEASIBILITY.md are not individually covered in my report (list: grep of
backticked names vs REPORT/findings, filtered to Lean theorem/lemma names). Subagent P13 launched to audit their
statements and non-vacuity (gcd_hw_joint_witness3/consistent, gcd_hw_walk, endpoints_sound_real, ruleE_sound_diff,
diff_not_imp_scat, ring_kappa_iff, LutAudit arb_*, lap_cut_fails, bdc_closed_ring_empty, fast_hold_mismatch,
stF_runt, arb_eternal). It runs one Lean process at a time. BQ#2 seed 4 SLOW_MAX: vectors 0-2 pass so far.

### progress 22:50
P13 in. I re-ran its 6 Lean files myself: rc 0, no errors, no sorry. I read diff_not_imp_scat (CornerDiff.lean:230)
myself: the witness is degenerate (s=1, Pa=Pb), so OVERSTATED, though the claim is true (the auditor proved a
non-degenerate version). bdc_closed_ring_empty is mildly OVERSTATED ("every ring" relies on emit.py's output
shape, which is unchecked). The other 12 are CONFIRMED with scope notes. REPORT updated.

### progress 23:02
BQ#2 seed 4 SLOW_MAX full stack (own route, sdf b1b4b951): 16/16 PASS errs 0, v6/v12/v13 29/23/34. That fits the
journal's "28-32" range for d/3/4. No md5 or per-seed laps were recorded to compare against. REPORT row updated.
Next: BQ#2 seed 7 route + 2x draw 1 (claimed PASS 54/42/63), already queued.

### progress 23:05
BQ#2 seed 7 route: sdf ae90c9ef and xray 042034d2 REPRODUCED (match the TSV). 2x draw 1 full stack running.
Summary notification sent to the owner: no refutations this session; BQ#2 2x failure and its cause independently
confirmed; formal axiom audit clean; P13: 2 mild overstatements.

### progress 00:29
BQ#2 seed 7 2x draw 1 full stack: 16/16 PASS errs 0, 54/42/63, CONFIRMED exactly (route md5s reproduced). So
BQ#2 at 2x draw 1 stands at seeds 7 and 8 PASS and seed 6 FAIL, all three reproduced by me. Seed 9 2x was never
completed by research (OOM).

### progress 00:29
Research 53ad0e38/a3111697: on BQ#2 seed 6 at 2x, the unconstrained route fails draws 1 and 2 (draw 2 errs 15)
and passes draw 3. The chain-region route goes 1/3 and is 6-16% slower. Their reading is "no robustness gain".
Started: re-route seed 6 (md5 check), then 2x draw 2 on all 16 vectors at TEND 30 us (they say the failures
appear in the first laps), to check "errs 15".

### progress 00:48
Draw-2 check: my re-route again gives sdf c4ec8664 and xray 1f7f03ea. 2x draw 2 at TEND 30 us gives errs 15 =
claimed, CONFIRMED. But all 16 vectors stop within 1-4 laps, and vec 0 stalls with errs 0. That exposed a judge
defect (r23 I): seeds_fid.py:101-107 grades PASS when every vector has >= 1 lap and ends at the timeout with
summed errs 0, so a stall with no wrong compare passes. The runs I reproduced are unaffected: minimum laps per
vector are s1x 42, fix_uori3 39, s8_2x 36, s4_max 23, s7_2x 42. PASS rows I did not re-run rest on this judge
alone. Added as an OVERSTATED row at the top of REPORT.

### progress 00:50
Owner notified about the judge defect. BQ#2 seed 9 route: sdf 4a9b218e and xray 0117760c REPRODUCED (= TSV).
SLOW_MAX full stack running; I check all 16 vectors for stalls, not just errs.

### progress 01:42
BQ#2 seed 9 SLOW_MAX full stack: 16/16 errs 0, 31/25/36 = TSV, every vector's last lap > 147 us (no stall).
CONFIRMED. BQ#2 rows I reproduced myself are now: seeds d (r15), 4, 6, 7, 9 at SLOW_MAX (6/7 in r22); seeds 7, 8 2x PASS;
seed 6 2x draws 1 and 2 FAIL; seed 6 1x PASS.

### progress 01:42
Research d57bd982: BQ#2 seed 9 2x draw 1 "PASS 16/16 (49/39/58)"; BOARD-QUEUE now says 2x 3/4. Running it on my
seed-9 route with a per-vector stall check.

### progress 03:03
BQ#2 seed 9 2x draw 1: 16/16 errs 0, 49/39/58, no stalls. CONFIRMED. All four BQ#2 2x draw-1 rows (6 FAIL; 7, 8, 9
PASS) are now reproduced from my own routes, so BOARD-QUEUE #2's "2x 3/4" is CONFIRMED.

### progress 03:04
r23 K: research's 2x region-map spread table reproduced exactly with my code (over all 50 grid regions). Over
BQ#2 seed 6's 44 occupied regions, draw 3 has no region < 0.4 (its 0.12 region is empty). Failing draws 1-2
have one, passing 3-4 don't. "Draw 3 splits by route" contradicts their own table (PASS on both): minor
OVERSTATED. At 1x the occupied spread is already 1.7-2.2x.

### progress 03:23
The container restarted around 03:20 (disk kept; Lean, toolchain and worktrees intact). BQ#2 seed 7 2x draw 2
(claimed "FAIL errs 3"): seed-7 route md5s reproduced again. Vectors 0-9 finished before the restart: vec 7 and
8 fail (laps 1, errs 1); the rest pass at TEND 30 us. Vectors 10-15 relaunched.

### progress 03:37
BQ#2 seed 7 2x draw 2: errs 3 on vectors 7, 8, 12 (the same signature as seed 6 / uori3), others progress. CONFIRMED.

### progress 03:38
No new research claims (BQ#1 8-seed full stack in progress on their side); formal is unchanged since 5a1ee8d2.
Started BQ#2 seed 3 route + SLOW_MAX full stack to close part of the UNVERIFIED d,3,4,5 row.

### progress 04:28
BQ#2 seed 3 SLOW_MAX (own route sdf e0d4202b, xray 97de94b9; no md5 recorded on research): 16/16 errs 0, no stalls,
v6/v12/v13 28/23/32, inside the journal's "28-32". REPORT row updated.

### progress 05:17
BQ#2 seed 5 SLOW_MAX (own route sdf 030c36bd, xray fc056c5b; no recorded md5): 16/16 errs 0, no stalls, 32/25/37.
7 of 8 BQ#2 SLOW_MAX full-stack rows are now reproduced by me (d r15; 3, 4, 5, 9 here; 6, 7 r22; 8 via 2x and TSV
-- 8 SLOW_MAX itself not re-run). Remaining UNVERIFIED for BQ#2: FAST_MIN on d,3,4,5 (2 h each) and seed 8 SLOW_MAX.

### progress 06:11
BQ#2 seed 8 SLOW_MAX: sdf b7733e23 / xray b93e281a (= TSV), 16/16 errs 0, 31/25/37 = TSV, no stalls. All 8 BQ#2
SLOW_MAX full-stack rows are now reproduced from my own routes. Still UNVERIFIED: FAST_MIN on d,3,4,5.

### progress 06:33
Research a73267f8: BQ#1 full stack first 5 runs PASS (d SLOW_MAX 16/12/18 on sdf 6f8b99e6, d FAST_MIN 45/35/51,
3 SLOW_MAX/FAST_MIN, 4 SLOW_MAX). BQ#1's full stack has never been reproduced by me, so after the BQ#2 seed 5
FAST_MIN run I route BQ#1 at the default seed (check sdf 6f8b99e6) and run SLOW_MAX on all 16 vectors with the
stall check. The seed-5 re-route reproduced 030c36bd/fc056c5b (the build is deterministic).

### progress 08:04
BQ#2 seed 5 FAST_MIN (route md5s again 030c36bd/fc056c5b): 16/16 errs 0, no stalls, 88/71/102. That equals the
journal's "5 FAST_MIN 88/71/102" exactly. CONFIRMED. BQ#1 default-seed route + SLOW_MAX starting.

### progress 08:52
BQ#1 (top of BOARD-QUEUE) full stack, default seed: my route reproduces sdf 6f8b99e6; xray 357f17cb. SLOW_MAX 16/16
errs 0, no stalls, 16/12/18: CONFIRMED exactly. This is the first time I have reproduced the BQ#1 full stack.

### progress 08:53
Formal advanced to 0780fd30 (40+ commits on 2026-10-31: B Bwit/Bwit2 joint witnesses of the driver-bound
network theorem; C TxWin indexed by occurring transactions (answers my P12a row 18), H_COMPUTE_FN for 14 compute
units, vk2; A Events9FullArb/E9* claims, SeqXray SLICEM windows (answers P10b), CornerDiff strong witness (answers
P13), "design_verdict9_full_arb covers no gcd_hw row"). Clean worktree ~/wt-f14; Mathlib packages moved from wt-f13
(same lake-manifest); lake build of 0780fd30 running.

### progress 08:54
Keyword scan of 0780fd30 (795 Formal files): 1 hit, the same Netlist `opaque` constructor. The lakefile globs build
every module under Formal/ (Wip/ excluded), so my lake build covers every claimed module. Subagents P14bc (shards
B+C: TxWin repair, H_COMPUTE_FN 14 units with own netlist spot-check, Bwit/Bwit2 joint witnesses) and P14a (shard A:
Events9FullArb / arbnet_edge verdicts and coverage, grant_fall_after_req_fall, CornerDiff strong witness, SeqXray
SLICEM vs prjxray-db) launched; they compile only after my build finishes, one Lean process each.

### progress 09:54
Clean lake build of formal 0780fd30: EXIT 0, 3636 jobs, 0 errors (audit/logs/formal_build_0780fd30.log). Per-module
axiom audit of all 795 modules started (2 jobs; live log in scratch, results to ~/axres_0780fd30, snapshots via
axsnap.sh).

### progress 10:06
P14a in. I re-ran its 4 Lean files myself (rc 0, no sorry) and checked slicem.sdf (md5 5cdfd60b, hold 0.262).
CONFIRMED: design_verdict9_full_arb / arbnet_edge (conditional, assumptions listed), "covers no gcd_hw row",
10 ipow/xorshift rows CLEAN (counts), grant_fall_after_req_fall, the CornerDiff strong witness (mine, credited),
SeqXray SLICEM. UNVERIFIED: the "md5s reproduce" claims for the 10-31 rebuilds (no record committed). OVERSTATED
(minor): ArbEdge window wording in FEASIBILITY/HOWTO and the stale "beyond ANY bound" text. Axiom audit of
0780fd30 running (snapshot audit/logs/axres_0780fd30.txt). P14bc still running.

### progress 10:28
P14bc in. I re-ran its 3 Lean files (rc 0) and read out0_dag_witness myself. OVERSTATED: the "real gcd_hw run"
DAG certificate uses a hand-made 5-node obligation netlist whose bus value is 6 by construction (a relabelling);
the TxWin repair itself is CONFIRMED. Bwit joint witness CONFIRMED and not degenerate, but FEASIBILITY's "every tied
cell's pins driven by the netlist-named cell" drops the 63/175 and contract-cell qualifiers (OVERSTATED).
H_COMPUTE_FN for 14 units CONFIRMED with my own netlist transcription check. The subagent's "fixture hash
mismatch" is withdrawn: trim.py makes synth.json a trimmed netlist by design.

### progress 10:47
Axiom audit of formal 0780fd30 COMPLETE: 795/795 modules, 103483 constants, bad 0, no-result 0. REPORT updated (pass 14).

### progress 10:48
Formal advanced to f40e003a (about 50 more commits). The headline change: shard A design_verdict9arbnet_ord/_ordS
says "10 gcd_hw rows meet every checked premise with B1 as the behaviour hypothesis ArbOrd", plus "glsq" monitors
run on research's gcd_hw GLS. Shard C: H_COMPUTE_FN for all 20 gcd_hw units (ushli0 for k<32) + GcdJoin +
xorshift's 5. Shard B: Bwit2 (mux-extended, 124/175) and 136/175 via 1-input joins. ~/wt-f14 checked out at
f40e003a, Mathlib unchanged; lake build running (incremental: lake re-checks every module whose inputs changed, by
hash). Keyword scan of the 831 files: see below.

### progress 10:49
kwgrep on f40e003a (831 files): 1 identifier hit, as before. Pass-15 subagents launched: P15a (shard A: arbnet_ord/
ordS gcd_hw coverage conditional on ArbOrd/QQuiet, and whether the prose says so; glsq monitors on research GLS
vs the Lean definitions; the scatter-0.10 ArbOrd failure) and P15bc (C: H_COMPUTE_FN 20/20 + GcdJoin link into the
capstone, xorshift units, Wip negative controls; B: Bwit2 and the 136/175 census).

### progress 11:15
First lake build of f40e003a: EXIT 1. The only failure is Formal.Cells.BWitNChk, "Lean exited with code 137"
(SIGKILL, OOM: two subagent Lean processes plus the build). The other 3667 jobs built. Stopped my queued BQ#1
FAST_MIN GLS to free memory, and re-running lake build (logs/formal_build_f40e003a_r2.log). Not a proof failure
unless it recurs with memory free.

### progress 11:16
P15a in. Main finding (definitions read by me): ArbOrd, the hypothesis that now replaces the failing B1 rows for
gcd_hw, is an order on Classical.choose warps for all t > T0. During idle stretches any in-band warp satisfies the
gates, so at B1-failing readers ArbOrd cannot be proved for a real run. The "10 gcd_hw rows covered" result is
therefore OVERSTATED. The subagent's demonstration is a one-gate model with the merge6 numbers; my re-run of its Lean
file waits for the rebuild. Also OVERSTATED: the glsq GLS monitors check less than the Lean definitions say, and
the FEASIBILITY status paragraph lacks caveats. Statements and numbers otherwise CONFIRMED.

### progress 11:22
f40e003a rebuild (memory free): EXIT 0, 3672 jobs. BWitNChk builds, so the first failure was OOM only. I re-ran
A_ArbOrd.lean myself: rc 0, no sorry; not_all_witnesses / merge6_instance / b1_without_ord_false use [propext,
Quot.sound]. Axiom audit of f40e003a (831 modules, 2 jobs) started.

### progress 11:29
P15bc in. I re-ran BC_GcdJoin/NegNew/Bwit2/BwitNetAx (rc 0, no sorry) and read gcd_kernel.v:933-939 myself. CONFIRMED:
H_COMPUTE_FN for 20/20 gcd_hw units (own transcription check against fixture and my independent build) and xorshift's
5; Bwit2 witness (non-degenerate); census classes; negative controls (data-level). OVERSTATED: "1-input join is a wire
both ways" is false for ushrsi0/1's request (C-element + gated delay), so 134/175 not 136/175; GcdJoin does not link
H_COMPUTE_FN into the capstone (shard A's text says so correctly; commit message reads otherwise).

### progress 12:15
Axiom audit of formal f40e003a COMPLETE: 831/831 modules, bad 0, no-result 0. REPORT row added (pass 15).
BQ#1 d FAST_MIN GLS running.

### progress 12:15
Research 9ea05a7e: BQ#1 full stack 8 seeds x 2 corners PASS (TSV committed). My recompute from the TSV: SLOW_MAX
8/8, mean 15.875 (15-16), FAST_MIN 8/8, mean 45.875 (44-48), matching "15.9 / 45.9". Their d row sdf 6f8b99e6 / xray
357f17cb equals my rebuild. d SLOW_MAX already reproduced exactly; d FAST_MIN running; seed 9 SLOW_MAX (sdf 81d27cf3)
queued. Formal moved to 58251494 (B: Bwit3 164/175, fork trees 170/175; C: Out0Wit docstrings now say relabelling,
accepting my P14 row; A: b1_and). That is pass 16, after the BQ#1 runs.

### progress 12:16
Pass 16: ~/wt-f14 checked out at formal 58251494. Building the three NChk kernel-check modules one at a time, then
the rest. Their own howto (51660257) records that building two of them in parallel OOMs on 15 GB, the same as my
first f40e003a build. The BQ#1 d FAST_MIN GLS is running alongside.

### progress 13:26
BQ#1 d FAST_MIN: 16/16 errs 0, 45/35/51 (= TSV), no stalls. CONFIRMED. BQ#1 seed d now reproduced at both corners.
Formal 58251494 build: BWit2NChk was OOM-killed (code 137) twice, even when built alone, with my GLS (~4 GB)
running. BWit3NChk failed because it rebuilds BWit2NChk. I stopped the queued BQ#1 seed-9 run to free memory; the
full build continues, and BWit2NChk will be retried alone with nothing else running.

### progress 13:34
Formal 58251494 full build: EXIT 1. The only failing module is BWit2NChk (code 137, OOM during the parallel full
build). Everything else, including BWitNChk, built. Retrying BWit2NChk alone with nothing else running, under
/usr/bin/time -v, to get its peak RSS. If it cannot finish in 15 GB, BWit2NChk and its dependents (BWit3NChk,
Bwit2/Bwit3 Net) are UNVERIFIED as builds here.

### progress 13:56
BWit2NChk built alone: EXIT 0, peak RSS 10.3 GB (logs/bwit2nchk.log), so the earlier failures were OOM only.
BWit3NChk alone: EXIT 0. Full lake build of 58251494: EXIT 0, 3896 jobs (logs/formal_build_58251494_r2.log).
Axiom audit of 58251494 started. Note for the owner: two of the formal kernel-check modules need about 10 GB each,
so a 15 GB sandbox cannot build them in parallel. Their howto says so.

### progress 13:57
Pass-16 subagent P16 launched (B: Bwit3 164/175 and H_EXC_CLEAN, and whether the witness exercises a contested
arbitration; fork trees 170/175; A: b1_and on a proposed two-copy AND request pin; C: 11g bitstream import
provenance). BQ#1 seed 9 route + SLOW_MAX restarted.

### progress 14:15
P16 in. I checked its two overstatements myself: no BWit4Net exists although notes/B-hypotheses.md:544-555 names
its witness theorem; FiniteNetComb.lean:11 says "(no runt, no hazard)" but B_excclean.lean (rc 0, re-run by me)
shows a runt passes H_EXC_CLEAN. Arbiter mutual exclusion is still assumed via H_OTHER. CONFIRMED: 164/170 censuses,
Bwit3 (own INIT decoding), b1_and (576 margins; a proof-side virtual node, not a circuit change), 11g import.

### progress 14:25
BQ#1 seed 9 route: sdf 81d27cf3 and xray 7a495c31 REPRODUCED (= TSV), so BQ#1's non-default-seed routes reproduce too.
SLOW_MAX sim 7/16. Axiom audit 58251494: 403/865, bad 0.

### progress 14:51
BQ#1 seed 9 SLOW_MAX: 16/16 errs 0, 16/13/19 = TSV, no stalls. CONFIRMED. BQ#1 rows reproduced: d max, d min, 9 max.

### progress 15:02
Axiom audit of formal 58251494 COMPLETE: 1055/1055 modules, 118806 constants, bad 0, no-result 0. (An earlier note
here assumed 865 modules; the tree has 1055.) Formal has moved again: A withdrew "10 gcd_hw rows" (5e35b742) and
introduced SatPinW explicit warps (19195024), structurally answering P15a; corrected glsq says ArbOrd fails in 3/5
scatter draws; B added Bwit4 (170/175, answering P16's missing-BWit4Net row) and the N level 173/175 (no witness);
NChk peak cut to 4.9 GB. Pass 17 next, at the new head.

### progress 15:03
Pass 17: ~/wt-f14 at formal 464c5ea7 (1058 files); NChk-first build running. Subagent P17 launched: A's SatPinW fix
of P15a and whether any gcd_hw row now has ArbOrd discharged; corrected glsq monitors vs the Lean definitions; B's
Bwit4 (170/175), the N level (173/175), and whether NChk chunking changes what is checked; dangling citations after
the Prelim deletion. Research: BQ#1 1x scatter 3/3 PASS (4a48b6b4), not yet looked at.

### progress 16:10
BQ#1 d 1x scatter draw 1: 16/16 errs 0, 23/18/26 (= claim), no stalls. CONFIRMED. Formal build status: EXITMOD BWit2NChk 0 EXITMOD BWit3NChk 0 EXITMOD BWit4NChk 0 EXITMOD BWitNChk 0 

### progress 16:19
The container restarted again (~16:15). The formal 464c5ea7 build had all 4 NChk modules done (peak RSS 0.8-7.7 GB)
and stopped at 3379/3899; restarted (logs: formal_build_464c5ea7_r2). The P17 subagent was resumed from its
transcript; its partial P17.md (summary: SatPinW fix CONFIRMED structurally but ArbOrd still assumed on every gcd_hw
row; corrected glsq monitors match the Lean windows; Bwit4 and the 173/175 census CONFIRMED; no theorem lost in the
Prelim deletion) is committed. BQ#1 d 1x was already recorded.

### progress 17:16
Formal 464c5ea7 build: NChk modules (first log) + resumed full build EXIT 0, 3899 jobs. kwgrep 1 identifier hit. Axiom
audit of 1058 modules started. P17 subagent still running.

### progress 17:17
Research 30a80999: BOARD-QUEUE #1 "1x scatter 8/8 PASS (23-29)". No TSV rows; the journal gives laps for d, 6, 3 only.
OVERSTATED (documentation), same pattern as r19. The d row was reproduced by me. The session summary repeats the BQ#3
"1x 8/8" (r19) and the arbiter "worst 691 ps" (r21) claims. Formal 0965e2ad: A cites audit P17 ("ArbOrd fails 1 of
5 draws, not 3"), so formal already reads P17's partial findings.

### progress 17:18
P17 final. I re-ran A_SatPinW/B_axioms17/B_arbdump4 (rc 0) and checked R0's INIT support myself (0xACACACAC uses I0-I2
only). REFUTED: "ArbOrd fails in 3/5 scatter draws". Two of the three failing pairs are the design reset net; the
truth is 1 of 5. Formal already accepted this from P17's partial findings (44d30983). CONFIRMED: SatPinW structural
fix (ArbOrd still assumed on every gcd_hw row), corrected QQuiet/quiet-start/ArbOrd monitors (counts), Bwit4 170/175,
N level 173/175, NChk chunking, Prelim deletion lost no theorem.

### progress 18:00
The owner pushed an audit PROGRAM change (f33d8da3, 13:30 EDT): top priority is the formal shards' bitstream theorem
(formal/target/, Spec.lean, five allowed hypotheses). My push was rejected until I rebased onto it. At formal head
2f2e632d, formal/target/ and Formal/Target/Spec.lean do NOT exist yet (formal PROGRAM's "THE goal", 4ef44a05/95d0784d,
is from today). Prepared for it: audit/target_ref.md records my own BQ#1 default-seed build md5s (sdf 6f8b99e6, xray
357f17cb, fasm 1a3909f6), and my rebuilt bitstream payload is byte-identical to research/board/gcd_hw_03e82630.bit.

### progress 18:21
Axiom audit of formal 464c5ea7 COMPLETE: 1058/1058 modules, 119260 constants, bad 0. Pass 18 at formal 2f2e632d: formal/target
and Formal/Target present? 0 files.

### progress 18:22
Pass 18: ~/wt-f14 at formal 2f2e632d; NChk-first build running. Subagent P18 launched (A: ArbEnv / design_verdict9arbnet_env
field list and conditionality, the ctl band 10^15 change, GLS ArbEnv/QQuiet-phi monitors vs Lean, the R0 INIT-support
filter; plus any work toward the bitstream theorem).

### progress 18:23
Formal 2f2e632d build: all NChk EXITMOD 0, full build EXIT 0, 0 failures. Axiom audit started.

### progress 18:38
P18 in. I re-ran A_bandcheck.py (identical) and A_ArbEnv.lean (rc 0), and grepped the glsq tools for reqlow (none).
OVERSTATED: the GLS behind the "ArbEnv holds" evidence uses nextpnr point delays mostly outside the bands the
monitors check against (seed d slow: 59/81 arcs), so it is not a behaviour the theorem covers; reqlow is unchecked;
"one explicit list" leaves QQuiet/hbase/ArbOrd outside. CONFIRMED: ArbEnv theorem (conditional, stated), pointwise C,
INIT-support filter. Nothing yet toward the owner's bitstream theorem. Axiom audit of 2f2e632d running.

### progress 18:49
Research 0056e2b0/7dc80477: log-normal scan, BQ#3 seed 9 passes 1x and 1.5x, fails 2x (errs 6, same six vectors).
The 2x log-normal failure was already reproduced in r19 (s2x_logn). Started: my route of BQ#3 seed 9 (expect sdf
74511ca2) + log-normal 1.5x (region 0.24 / wire 0.189, draw 1) on all 16 vectors with the stall check.

### progress 19:26
Axiom audit of formal 2f2e632d COMPLETE: AUDIT-PAR constants=119323 bad=0 no_result=0 modules=1058. BQ#3 seed 9 route reproduced
(sdf 74511ca2, xray 7214582a); log-normal 1.5x sim running.

### progress 20:13
BQ#3 seed 9 log-normal 1.5x: 16/16 errs 0, no stalls. With r19's log-normal 2x FAIL, research's "threshold 1.5-2x" is
CONFIRMED.

### progress 21:35
BQ#2 seed 6 log-normal 1.5x (draw 1): 16/16 errs 0, 46/38/55 = claim, no stalls. CONFIRMED.

### progress 21:35
Research 95c22cf6 log-normal table: both known-failing routes pass 1.5x and fail 2x (BQ#2 seed 6 log-normal 2x "FAIL
errs 3"). The 1.5x points for both routes are reproduced exactly. Running BQ#2 seed 6 log-normal 2x (TEND 30 us).
The text again leans on S9's "double-counted" reading (r23 H caution stands), and calls log-normal "silicon-like
bounded speed-ups". Log-normal f = exp(sigma N) is never 0 (linear 1+sigma N clamps at 0), but its speed-up 1/f is not
bounded either; it is just much less likely at the tails.

### progress 22:03
BQ#2 seed 6 log-normal 2x: errs 3 on vectors 7, 8, 12 (the uori3 signature), others progress to TEND. The research
log-normal table (95c22cf6) is now fully reproduced: BQ#2 s6 1.5x PASS / 2x FAIL; BQ#3 s9 1.5x PASS / 2x FAIL.

### progress 23:36
r23 M: BQ#3 seed 9 log-normal 1.75x reproduced exactly (16/16, errs 0, 50/40/120), but the PASS is double-counted
glitches. On exactly the six 2x-failing vectors every completion emits two LAP/OK pulses 30 ps apart (lap ratio vs
1.5x: 1.97-2.00; others 0.98-1.00), and the real period is unchanged. REFUTED as a pass and as "threshold 1.75-2x".
No other PASS run I reproduced shows double laps (scan of all logs).

### progress 23:37
Research 7ceec350 tabulates failing scales: BQ#3 s9 1.75-2x (relies on the 1.75x "PASS" refuted in r23 M, so really
1.5-1.75x) and BQ#2 s6 1.5-1.75x. Their ">= 1.5x margin on the worst known route/draw" holds on my reproductions
(both 1.5x runs clean). They start a 1.5x draw-2 sweep next.

### progress 23:37
New tool audit/tools/lapcheck.py: per-vector STALL / DOUBLE (completion pairs < 1 ns) / ERR check on sweep logs, the
two failure modes the seeds_fid judge misses. Validation: flags exactly vectors 2,3,9,11,13,15 of the 1.75x run
(lapcheck_bq3_9_logn175.txt), CLEAN on bq3_9_logn15, bq2_6_logn15, s7_2x, bq1_d_1x, and flags all 16 vectors of the
failing s6_2x_d2. I will run it on every future GLS reproduction.

### progress 23:38
lapcheck over all 24 of this session's sweep dirs (audit/r23/lapcheck_all.txt): every run graded PASS is CLEAN (incl.
all BQ#1/BQ#2 SLOW_MAX/FAST_MIN, 2x seeds 7/8/9, the uori3 fix). Flags only on the known FAILs and on the
1.75x log-normal run. (s7_2x_d2's third flag is vec 10, cut off by the container restart and re-run in s7_2x_d2b.)
So the judge weakness has not hidden any failure in the rows I re-ran, except r23 M.

### progress 00:07
BQ#2 seed 6 log-normal 1.75x (route md5s again): errs 2 on vectors 8, 12 = "FAIL 2". lapcheck shows vector 7 also
breaks (double pulse, then stall, errs 0), so the uori3 set 7/8/12 fails, as at 2x. Failing-scale bracket on both
worst routes: 1.5-1.75x (my data).

### progress 01:24
Research 3270b5f1: log-normal 1.5x draw 2 on BQ#3 d,3,4,5 PASS (d 53/44/63, where linear 2x draw 2 failed with errs
15). Reproducing BQ#3 d draw 2 at full TEND with lapcheck (stall/double check).

### progress 02:38
BQ#3 d log-normal 1.5x draw 2: 16/16, 53/44/63 = claim, lapcheck CLEAN. CONFIRMED.

### progress 03:35
Research 96446990: BOARD-QUEUE #3 adds "log-normal 1.5x draw 2: PASS on all 8 seeds" and "seed 9's failing scale on
draw 1: between 1.75x and 2x". The latter contradicts r23 M (1.75x fails with double pulses), and it is now in
the board-facing document: OVERSTATED row added at the top. Spot-checking BQ#3 seed 9 1.5x draw 2 with lapcheck.

### progress 04:45
BQ#3 seed 9 log-normal 1.5x draw 2 (md5s again): 16/16, lapcheck CLEAN, v6 48. With seed d, 2 of the 8 draw-2 rows are
reproduced CLEAN.

### progress 05:16
The container restarted again (~05:10); disk intact, nothing lost except the branch watcher (re-armed). No new commits
on research (after 96446990) or formal (after 2f2e632d); formal/target still absent.

### progress 05:56
Research f691b29b: BQ#2 log-normal 1.5x draw 2 PASS on seeds 6-9 (12/12 routes with BQ#3). Spot-checking seed 6 draw 2
with lapcheck. BOARD-QUEUE #2 again says "bounded speed-ups".

### progress 07:06
BQ#2 seed 6 log-normal 1.5x draw 2: 16/16 lapcheck CLEAN, v6 49 = claim. CONFIRMED. On my data the worst known routes
of #2 and #3 are clean at 1.5x on draws 1 and 2 and fail at 1.75x on draw 1.

### progress 07:25
TOP PRIORITY (owner): the target appeared at formal a11503e9. Audit T1 (audit/findings/T1.md): every target md5 and
claim CONFIRMED independently. The .fasm/.sdf equal my own BQ#1 rebuild; the .bit differs from my rebuild only in
8 header date bytes; my own bitread + bit2fasm of the target reproduces their read-back FASM byte for byte; the
canonical feature counts match exactly. Spec.lean part I draft (Wip, unchecked): matches THE goal on inputs,
pipelining, safety+liveness, delays and H_ARB, but H_ENV adds harness timing margins su/Δo, which THE goal excludes.
That needs an owner decision. No theorem about the target exists yet.

### progress 07:49
TOP PRIORITY result (audit/findings/T2.md). In the fid GLS of the target's own FASM (1a3909f6, SLOW_MAX), the kernel
acknowledges its inputs at 0.99 us and delivers out0 at 9.99 us, so gcd_rig.v's "start acknowledged only when
finished" is false. With my own environment replacing the rig's env node (forced boundary nets, four-phase, data
held), offering vector 6 then (1,1) back to back gives out0 = [1, 0x20]: REORDERED. The sequential control is in
order. THE goal's theorem, as drafted (pipelined H_ENV), is FALSE for the target bitstream. C's counterexample is
confirmed; A's "would not hold two pairs" note is refuted.

### progress 07:53
T2 addendum: the pipelined replay also reorders at FAST_MIN (out0 = [1, 0x20]). The counterexample holds at both corners.

### progress 07:57
T2 addendum 2: pipelined (3,5),(3,5) and (8,8),(3,5) DEADLOCK on the target's fid GLS (both accepted, no out0 in 37 us).
Sequential (3,5),(3,5) answers 1, 1 within 1 us each. C's deadlock claim is CONFIRMED: THE theorem fails on liveness too.

### progress 08:03
Formal moved to 88c74e3c (25 commits): Spec.lean frozen (69c49057) with SeqEnv/NetCorrectSeq; B claims the frozen
Spec's ArbOK contradicts GateOK on held-arbiter handovers (NetCorrect vacuous there, f06ceb8e); A's decoder (pip level)
+ round trip (Python mirror) + decoded target as Lean data; C and A have Lean/sim witnesses of the reorder and
deadlock, consistent with my T2. Build of 88c74e3c running (NChk first). Subagents: T3 (frozen Spec diff, the
owner's checklist read from the Lean binders, the vacuity claim with my own Lean check) and T4 (run the decoder
round trip myself; own comparison against the read-back FASM; spot-check decoded LUTs).

### progress 08:33
T4 in (decoder round trip). I re-ran the subagent's re-encoder against my own read-back: 355126 read-back / 344790
re-encoded / 0 invented / 10336 left. CONFIRMED. All 7167 kernel-cone LUT sites match the bits and nextpnr. Leftovers
include FF and clock config with real function, but nothing reaches the kernel cone. The generated Lean net data and
its WF proof are not committed at 88c74e3c (UNVERIFIED), and the Lean-side round trip is not written yet.

### progress 08:39
T3 in (frozen Spec). I re-ran its 4 Lean files (rc 0, no sorry) and checked that ToyVacuous imports the frozen Spec with
no redefinitions. The frozen statement can be VACUOUS. ArbOK says q may change only within T of a request edge; for
T <= R+L a never-acknowledging toy netlist satisfies NetCorrect and NetCorrectSeq because no behaviour meets the
hypotheses, and such a netlist exists for every T. Also: section 7 calls NetCorrectSeq (extra SeqEnv binder, sequential
env) THE theorem, which deviates from the owner's pipelined statement; Env adds harness timing (R, su, Δo).
Formal 88c74e3c build EXIT 0.

### progress 08:44
Formal a3354d1c/08805763: B self-corrects a near-tie claim on the decoded target; A journal only. Nothing to grade.
Axiom audit of 88c74e3c running (60 modules done).

### progress 08:50
Formal 6603bdd1 (B: ArbClean, separated arbitrations decided by the frozen gate relation): queued for the next pass.
Watcher now batches routine formal commits hourly and wakes at once on Spec/target changes, research claims, or the
end of the axiom audit.

### progress 08:56
Formal 3d3ebb61 changed the FROZEN Spec: ArbOK repaired (ArbNodes = q + all non-feedback inputs of the state LUT),
journaled in the commit and the docstring ("before any proof used it"). The decoded target net data, Witness.lean,
WitBoundary.lean and WitSlice.lean are now committed. The 88c74e3c axiom audit was stopped (superseded) at 266
modules, 0 bad (2 no-result = the two runs I killed; logs/axres_88c74e3c_partial.txt). Build of 6f094d32 started.
Subagent T5 launched: whether the repaired ArbOK removes T3's vacuity, any residual small-T vacuity, the target
arbiter list against my own extraction, what Witness.lean proves, and whether the net data compiles.

### progress 09:18
Formal ce523cfc STATUS.md: theorems about the target so far = net_wf and C's 11g. The pipelined refutation V9V4.refuted
is "in progress, not claimed"; NetCorrectSeq is decomposed into S1-S6 (all open); "H_ENV + SeqEnv" is listed as
allowed. That is the deviation in T3's row, still awaiting the owner. 6f094d32 build: NChk done, full build running; T5
running.

### progress 09:31
T5 in. I re-ran ToyRepaired.lean (rc 0) and checked the commit timestamps. The repaired ArbOK removes T3's vacuity:
the never-acknowledging toy now FAILS NetCorrect for T >= D. A residual vacuity remains for T below the state LUT's delay
(on the target 78/g..664g ps), and the Spec does not bound T. "Before any proof used it" is REFUTED (B's 07:54 and 08:09
proofs used the old form). The target arbiter list matches my own extraction; the net data equals my decoder run and
compiles (build EXIT 0, 4052 jobs). The pipelined refutation is not committed yet.

### progress 09:59
New: research 57c0cea4 BQ#1 log-normal 1.5x draw 2 8/8 PASS ("all 20 candidate routes"); reproducing BQ#1 d with
lapcheck. Formal B f59c49bc..5ba857b7: candidate counterexample to the SEQUENTIAL NetCorrectSeq at g=1, kappa ~0.155-0.215
(arbiter 0's ack C-element ua1 latches a circulating 7 ps runt under transport semantics; no out0). Subagent T6
launched to reproduce it independently and replay it in the fid GLS (owner's checklist). A: refutation boundary half
compiles in Wip (not claimed).

### progress 10:03
The disk filled up (/: 0 bytes free). The BQ#1 d log-normal GLS build failed with ENOSPC, and lapcheck wrongly said
CLEAN on a run with no vector logs (fixed: it now flags "NO VECTOR LOGS"; earlier CLEAN verdicts all had per-vector
output). Freed space by deleting large regenerable intermediates (netlists, vvp images, routed json) of finished
r23 work dirs; kept the sweep logs and the bq1_d_max/min dirs. Now 5.6 GB free. GLS re-run.

### progress 10:35
T6 in (B's sequential-theorem candidate counterexample). The 7 ps runt mechanism is CONFIRMED independently: B's two
simulators, the subagent's own transport simulator on my decoded net (flip-for-flip), all delays inside Adm, and the
frozen H_PRIM admits transport. It is NOT yet a counterexample to NetCorrectSeq: only liveness can fail, and no finite
run reaches the nominal out0 time. fid GLS replay (7 local arcs changed): the same runt in transport mode; with the
default resolver, out0_req pulse trains (a four-phase violation) and then a stall (> 12 us without a lap at 2 of 3
seeds). The kappa 0.21 control matches the baseline exactly (checked by me: laps 2.087/3.499/4.912 us).

### progress 11:06
BQ#1 d log-normal 1.5x draw 2 (re-run after the disk-full failure): 16/16 lapcheck CLEAN (16 vector lines), v6 26.
CONFIRMED. 4 of the 20 "all pass" routes are now reproduced clean.

### progress 11:58
Formal 565af3b9: the pipelined refutation is now committed (FormalWit/V9V4, 228 modules; refuted / refuted_range at pSlow,
T >= 656). I read the statement: it uses the committed decoded target and reorders vector 9 then (1,1), consistent with
my T2. Building it one module at a time (/root/build21.sh: Formal first, then FormalWit) for my own build and axiom
check. SpecRunt.lean adds H_RUNT(w) as a sixth hypothesis, offered as an owner option. Findings: T7.md.

### progress 12:29
Formal 565af3b9 build: NChk modules then full build EXIT 0. FormalWit witness modules: 77 built so far, all rc=0
(~30 s and ~2.4 GB each). Research 100b2f13: log-normal 1.5x draw 3 partial (BQ#1 4/4); waiting for the summary.

### 13:35 T8: A's new H_DECODE evidence (formal c9484103)
- Decoder unchanged since 88c74e3c, Spec unchanged since 565af3b9 -> my T4 decode is the object. Own scripts t8/undriven_own.py
  (0 undriven of 170,324 kernel-cone nodes, 0 multiply-driven) and t8/carry_own.py (59 CARRY4 cells, 590/590 pins match
  nextpnr). A6 "mismatches": nextpnr cell netlist says GND, nextpnr ROUTING ties VCC (X16Y51) / leaves unrouted (X10Y92);
  bits follow the routing; halves equal -> harmless. Nits: "472" is the carry output-gate count, pins are 590; the check is
  independent of A's walker but not of prjxray's database (= H_DECODE). findings/T8.md, REPORT row.
- Witness build at 565af3b9 still running (C020, module 87/228, all rc=0 so far).
- 13:36 WitCut.lean (c9484103) compiled standalone on my 565af3b9 tree: standard axioms, conclusion = Spec GateOK pSlow 1. Row added.
- 13:38 B's Ua1Static: axioms standard (my build), arcs = my decode (loop equal, path unique chain), sums 865/852, 852/860 reproduced. T8 row 4.
- 13:40 started own fid GLS of the target route (wt-r14 BQ#1 default, xray 357f17cb) at log-normal 0.24/0.189 draw 3 (SEED=3), to check research 100b2f13 'BQ#1 draw 3: d 26/20/30 ... 16/16 errs 0'. Witness build continues (C020).
- 14:18 progress: witness build at C031 (98 modules, all rc=0). Draw-3 GLS: vectors 0-7 errs 0, vec 6 laps 26 (= research's 'd 26'). Formal a7312634 committed V9V4c (per-node-cut witness) -- queued.
- 14:19 V9V4c (a7312634) files extracted by git archive into my 565af3b9 tree (only additions since; WitCut md5 1e30ce2f equal); /root/build22.sh builds it module by module after the draw-3 GLS ends (memory). grep: no sorry/native_decide/axiom/extern in V9V4c or WitCut.
- 14:48 draw-3 GLS done: 16/16 errs 0, v6/v12/v13 = 26/20/30 exactly as research 100b2f13; lapcheck CLEAN. Row added. V9V4c build starting (build22).
- 14:58 progress: V9V4 at C063 (130 modules rc=0), V9V4c at T26 (28 rc=0). Formal: A started the Lean decoder round trip (RoundTrip, gen_rt.py; 4aa24410..02c8ceb5) -- audit when claimed.
- 15:36 progress: V9V4 at Q039 (186 rc=0), V9V4c at C028 (96 rc=0). A's RoundTrip still in progress (b6d7d4f1).
- 15:52 **T7 DONE: V9V4 refutation CONFIRMED.** 228/228 witness modules rc=0 (3.86 h); refuted / refuted_range types as claimed, axioms standard only; Lean net = my decode (lean_cmp 0 diffs at 565af3b9), Lean boundary = my boundary by name (t8/bnd_lean_cmp.py). V9V4c (a7312634) build continues.
- 17:16 V9V4c (a7312634) CONFIRMED: 229/229 rc=0, same refuted/refuted_range types, standard axioms. '~3x cheaper' -> 1.6x on my sequential builds (OVERSTATED, minor). T8 rows 5-6.
- 17:17 OWNER DECISIONS landed (formal 94b7fd79, research 690f1561, author Jason Zeng): full-width gcd_ps target; H_RUNT(w) allowed (w=20 headline); g/κ Adm fix approved; NetCorrectSeq with sequential env is the target. Mapped against audit items in a new REPORT section; still open: ArbOK residual vacuity T<D, harness margins R/su/Δo. audit/PROGRAM.md unchanged. Research also claims draw 3 BQ#2 4/4 PASS (1fd41af8) -- not re-run yet.
- 17:21 started own fid GLS of BQ#2 seed 6 (saved build /root/bq2s6: fasm 227bce4a, sdf c4ec8664, routed 8a833e53 = my draw-2 run; 68843 active pips, same as draw 2) at draw 3, to check research 1fd41af8 '6 59/49/69'.
- 18:01 Spec.Adm change 7050f26f read: literal owner formula; same set as old at (1,0) for all c in [0,1]; Gate.start covers all windows (c in [0,1], fmax<=smax); new caveat: NetCorrect admits any (g,κ), so claimed theorems must be at g>=1, 0<=κ<1. Build at formal head queued after the BQ#2 GLS.
- 18:46 BQ#2 s6 draw 3 done: 16/16 errs 0, 59/49/69 exactly as research 1fd41af8, lapcheck CLEAN. Row added. build23 (formal 65323d29) starting.
- 18:54 build23 (formal 65323d29, clean worktree): 4 NChk EXITMOD 0, full lake build EXIT 0 (4058 jobs; Spec, the 6 dependents, SpecSettle, RoundTrip, Net.* rebuilt, not cached). SpecSettle adm_le_dmax/dmin_le_adm replacements read: sound with Sane p (0<=κ<=1, 0<g), c in [0,1], ordered arcs. Axiom audit of the 99 rebuilt modules (tools/axiom_audit_par.sh now takes MODLIST) and V9V4c/RT witness build running.
- 19:07 65323d29: axiom audit of the 99 rebuilt modules 2052 constants bad 0; kwgrep Formal+FormalWit: 1 hit (constructor named opaque). REPORT Adm row updated. V9V4c witness at T35.
- 19:15 **T9: SpecRunt H_RUNT(w) DEVIATES from owner decision 2** -- imposed on zero-delay pips/hops too, where it bans (not filters) sub-w pulses; all 5 kernel handshake outputs are read by zero-delay hops, so NetCorrectSeqRunt w is blind to sub-w output glitches (ReqMoves violations). Own Lean lemma (lean/T9/ZeroPinRunt.lean) + own decode check (t9/zero_readers.py). A's simb H_RUNT points UNVERIFIED (gfilter skips zero-delay pins); 'clip does not bind' true for ua1 arcs only (26/14 arcs at κ .20).
- 19:55 **T10: new target gcd_ps_e6bb4aec CONFIRMED**: md5s consistent (formal/research/BQ#4); own rebuild from clean bfa659b4 reproduces fasm/sdf/xray and the bit payload; own read-back identical 740cc6bf; A's decoder on my read-back + my rt_own: 0 invented, 9017 left (= A); boundary identical, 32/32 distinct data nodes; undriven 0; CARRY4 380/380.
- 19:56 gcd_ps.v CDC read: 2-flop syncs on i_ack/o_req, O_DATA read after sync; no missing synchronizer (agrees with research). req_core async-clear recovery race only under a non-sequential host.
- 20:30 formal d8a97803 BOUNDARY-ps.md (H_ENV for the AXI slave) read: consistent with my CDC reading and with the decoded boundary node kinds (flops for rst/req/data, LUTs for out0_ack/pend_ack). Row added. V9V4c rebuild at C065 (132 rc=0).
- 21:08 V9V4c rebuilt at 65323d29 under the new Adm: 228/228 rc=0; refuted/refuted_range unchanged types, axioms standard. The refutation stands under the owner-approved Spec. RT (round-trip data) modules building next.
- 21:37 RT (Lean round trip, gcd_hw_03e82630): RoundTrip.lean read (feats = pip names + LUT6 INIT bits only; A's 'not shown' list accurate). Own check t11/rt_tf_cmp.py: Lean tf (355,126 leaves, sorted, indices 0..n-1) == my own canonical read-back as multisets. Stopped lake's 4-way parallel RT.All (4 x ~4 GB on 15 GB; rc=143 in wit log is mine) and restarted RT one module at a time (/root/build24.sh).
- 22:46 NetPS (96487b31): Lean data = my gcd_ps decode (0 diffs / 186,873 gates), boundary equal, 9/9 arbs = the 9 ustate LUTs with correct inputs. net_wf build pending. RT (gcd_hw) build at C032.
- 23:53 research d5cc80c2/31a32641 now reproduce reorder+deadlock on BQ#1's fid stack and call gcd_rig.v's header wrong: agrees with my T2. Row added. RT build at C058.
- 01:02 **T11: Lean round trip (gcd_hw) CONFIRMED**: 244/244 rc=0, roundtrip/o5_gates standard axioms on Decoded.gates (rfl); tf = own read-back; siteT = own prjxray lookup (2624/2624). Next: build formal head (NetPS net_wf, gcd_ps round trip ffd204f4).
- 01:04 disk was at 963 MB free: removed superseded worktree wt-f13 (5a1ee8d2), large regenerable GLS intermediates in /root/r23work (logs kept), t4work2 rerun dir, and the RT oleans (results recorded): 7.4 GB free. Started /root/build25.sh: formal 06c2a739, NetPS G*/All (net_wf) and the gcd_ps round trip RTPS module by module.
- 01:38 disk 2.8 GB during the RTPS build: removed V9V4/V9V4c oleans and C files (results recorded in T7/T8), old axres_* dirs, and r23work run dirs (logs kept); 4.1 GB free; disk watcher armed. build25 at RTPS.Rows (79 modules rc=0: NetPS 75 G + All, RTPS F/B/Top/Rows).
- 02:13 gcd_ps spot.py over all 7,171 kernel-cone LUT sites ALL OK; muxf 1163/1163 agree. RTPS build at C011.
- 02:49 T12 started: gcd_ps full-stack GLS on MY BQ#4 rebuild (/root/bq4ref) with research's harness (wt-r14 at research ee8d8869), MY 24 vectors (t12/own_vectors.py, seed 20261102, none from gen_vectors) and MY oracle (t12/check_psres.py, math.gcd): nominal, then log-normal 2x draw 2 (research 59773544 claims 8/8 seeds 24/24).
- 03:04 T12 nominal (no scatter): bit-decoded netlist EQUIVALENT, ANNOTATE_DONE, 24/24 OK by my own math.gcd oracle, out0 bundle margin 7.1 ns. 2x log-normal draw 2 running.
- 03:16 T12: gcd_ps seed d 2x log-normal draw 2: 24/24 by my oracle, margin 5738 ps = research. Rows added.
- 03:47 gcd_ps boundary bit order checked by my own bnd_names_own.py vs RTL register names in my rebuild's routing: 98/98 (a/b/out0 data bits, rst, req). Closes T10 row 5's UNVERIFIED. RTPS build at C042.
- 05:32 **gcd_ps Lean layer CONFIRMED**: build25 305/305 rc=0 at 06c2a739; DecodedPS.net_wf, RTPS roundtrip, o5_gates standard axioms; tf = own read-back (338,510); siteT 2423/2423; kwgrep 0. T11 rows 5-6, REPORT rows updated.
- 06:07 started own fid GLS of BQ#1 seed d (the old target's route, xray 357f17cb) at log-normal 3x (region 0.48, wire 0.378) draw 2, to check research d239ae2d / bq1_logn3x_draw2.tsv row d (16/16, 24/18/28).
- 07:12 BQ#1 seed d log-normal 3x draw 2: 16/16 errs 0, 24/18/28 exactly as research d239ae2d; lapcheck CLEAN (run survived a container restart). Row added.
- 07:46 B's answer to T6/T8 (746aba05): all corrections accepted and applied (README period 901, cex downgraded, recovery claim withdrawn). Logged under Responses.
- 07:49 T13: C's gcd_hw_seq (ed402afd) compiles, standard axioms, statement as claimed, 2-credit mutation breaks it. Row added.
- 07:50 started T12 FAST_MIN spot-check of research 28993bba (1000/1000 at both corners): chunk c07 of gcd_ps_vec1000.hex (lines 449-512, 64 vectors) on my rebuild, my oracle. Fixed run_ps.sh output cap (head -80 would truncate 64-vector runs; now 400).
- 08:11 T12 row 3: research's vec1000 chunk c07 at FAST_MIN on my rebuild: 64/64 by my oracle, min margin 4112 ps = research. Row added.
- 08:22 T14: B's RaceStaticPS (κ 0.435/0.44) confirmed on my gcd_ps decode (unique path, loop, sums with new Adm, cell name); ArbCleanPS data 9/9 (INIT, fb pin, tied pin); SpecFbChain + SpecChain compile, standard axioms.
- 08:54 T15: C's HuffmanPS recounted on my decode (19878/4597/15281, acyclic, depth 96) = C's numbers; B's TargetLinkPS compiles (concatenated), standard axioms. CViewPS Lean build to queue.
- 09:26 read C's tcheck κ* rows on gcd_ps (fab4c247/13b0f38e): binding rule F cm12.udly κ* 0.038 (sufficient condition), adversarial simb correct to κ 0.6 on 4 pairs; C labels both untrusted/evidence. κ* = (req-data)/(req+data) follows from the new Adm (no band clip) by reading; not re-run. No row (no proof claim). CViewPS build at V022 (105 rc=0).
- 09:58 T15 row 3: C's boundary_reset checked by own 3-valued fixpoint on my decode: rst=1 forces a_ack/b_ack/start_ack/out0_req to 0 from all-X; rst=0 control leaves them X. Lean build of BoundaryReset/Island/RaceTablePS/RaceFrontierPS queued after build26 (CViewPS, at V072).
- 10:25 T15 row 4: C's correct_n0 (n = 0) logical core confirmed by own greatest self-confirming island (85,465 nodes incl. the 4 outputs at 0). Lean builds of Idle0/IslandPS/BoundaryReset and B's RaceTable/Link/FrontierPS queued (build27 at 9d3e3a3d after build26).
- 10:44 build26 (eb4503b7) 311/311 rc=0: C's CViewPS collapsed view + HuffmanPS; comb_ranked/collapsed/view_complete standard axioms. build27 (9d3e3a3d) started.
- 10:51 C discharged correct_n0's side conditions: correct_n0_p1 (g=1, κ=0, R >= 353 ns; dcc8cc94) and correct_n0_all (all Sane p with κ<1, R >= Cp·A1 + 87·Cp·M1 + 1; baf03e79; Σdmin >= 1 holds because integer ceil of a positive window end). build27 at IslandChk3 (Reset module peaked at 13 GB); build28 (baf03e79: Idle0P1, Idle0All) chained after it.
- 11:00 build27 (9d3e3a3d): 24/25 rc=0; boundary_reset, island_PS, correct_n0, RaceTablePS, RaceFrontierPS standard axioms; RaceLinkPS OOM-killed (13.8 GB, exit 137) -> UNVERIFIED. build28 (baf03e79) running.
- 11:18 build28 (baf03e79) 12/12: correct_n0_p1/_all standard axioms; R bound 353,248 ps at (1,0). Non-vacuity open (no Lean behaviour witness for gcd_ps; C's caveat).
- 11:50 C's witness_n0 (d23f97eb, Wit0.lean): ∃ x, Behaves p1 (circuit net boundary) x ∧ Env x boundary 400000 su Δo (some 0) va vb (p1 = g 1, κ 0; reset 400 ns >= the 353 ns bound), plus witness_n0_correct. Building (build29 at cd5e452f, 153 modules). B withdrew the monolithic RaceLinkPS (4c765981) after the OOM; split version pending.
- 12:22 C's one-pair witness: Wit1 (58e82170; behaves_w1, w1_result: out0.req rises at 771,456 ps, data = gcd 12 18 at 774,455) and Wit1Env (w1_all_hyps' : Behaves p1 ∧ ArbOK T (T >= 220) ∧ Env (some 1) (12,18), su any, Δo 3000, R 400 ns ∧ SeqEnv). build30 (9f778d3b) chained after build29 (at W033).
- 12:51 build29 153/153: witness_n0 (gcd_ps behaviour under Env n=0 at p1, R 400 ns) standard axioms -> zero-pair theorems non-vacuous at (1,0). build30 (one-pair witness) running.
- 13:54 C revised the one-pair witness (24a3c3a3: L chunks, Wit1, + Wit1Correct w1_hyps_and_correct) and B split RaceLinkPS (4e76f75f: 183/185 rows, rows 174/184 unchecked for memory). build31 at aef36d4d chained after build30 (at X059).
- 14:08 build30 (9f778d3b, C's first one-pair witness): 79/79 rc=0. build31 (aef36d4d, revised witness + Wit1Correct + B's split RaceLinkPS) did not start from the chained watcher (nohup child died with the task shell); started by hand with setsid.
- 15:25 T15 row 8: C's one-pair witness (gcd 12,18; all NetCorrectSeq hyps + Correct) built, standard axioms. build31 had two concurrent instances (chain watcher did start + my manual setsid); killed the later one at RaceLinkPS.B08; remaining instance finishing RaceLinkPS.
- 16:25 build31 done: B's split RaceLinkPS rows_linked (183/185, rows 174/184 excluded) standard axioms. REPORT row updated.
- 16:58 build32 at formal head 0be49560: 4 NChk EXITMOD 0, default lake build EXIT 0 (4821 jobs, incremental). Axiom audit of all Formal modules added/changed since 65323d29 started (MODLIST /root/modlist_0be49560.txt).
- 18:38 axiom audit of 763 Formal modules changed since 65323d29 (at 0be49560): 4741 constants, bad 0; kwgrep 1 hit (opaque constructor). Row added.
- 19:09 quiet branches; started T12 SLOW_MAX spot-check: chunk c11 (lines 705-768) of research's vec1000 on my rebuild, my oracle (research claims min margin 12043 ps at SLOW_MAX).
- 19:30 T12 row 4: vec1000 chunk c11 at SLOW_MAX: 64/64 own oracle, margin 12043 ps = research.
- 07:18 research ee0483c4 answers RISK row 108 with scatter evidence, keeps it a non-refutation: logged under Responses (runs partly reproduced by me). Also 7a37857b cost model (not a target claim).
- 10:01 research 25847170: vec1000 at band 0.38 + 1x scatter (region 0.16, wire 0.126, draw 1) 1000/1000, margin 7341 ps. Spot-check of chunk c03 started (expect t_end 391156293, margin 7341).
- 10:18 T12 row 5: band+1x chunk c03 64/64 own oracle, t_end and margin identical to research's row.
- 14:50 research 60f3cb76: BQ#1 log-normal 3x draw 3 8/8 PASS (seed d 22/17/26). Own spot-check of seed d started (r23/run_point2.sh, region 0.48, wire 0.378, logn, seed 3).
- 15:37 BQ#1 seed d log-normal 3x draw 3: 16/16 errs 0, 22/17/26 exactly as research 60f3cb76; lapcheck CLEAN.
- 17:32 owner commit db3c299b on research: August n=128 ring raw data and build (answers BOARD-QUEUE's data request); noted, no audit claim yet.
- 18:19 T16: research's band recalibration (0.38 -> 0.288) from the owner's August ring data reproduced independently (md5s, bitstream = route, SDF f20c1bf4, own ring walk 0 ps vs pred, own fit 0.2877 / +11.45% at 0.38 / held-out <= 3.06%).
- 00:31 research 1d7d73c7 cell-type check (BQ#2 8/8 PASS at LUT+wire band 0.288, CARRY4/F7F8/FF at SLOW_MAX; seed 6 61/50/72): own spot-check of seed 6 started (saved build /root/bq2s6, wt-r14 now at research 22fe1811 for GLS_SDF_BAND_CELL).
- 01:33 cell-type check BQ#2 seed 6: 16/16 errs 0, 61/50/72 exactly as research 1d7d73c7; lapcheck CLEAN.
- 03:19 owner 1dd0a675 (research PROGRAM + research/board/aug: all August board builds and 331 logs): research to fit a datapath band on the August gcd build, default uncalibrated-cell band 0.288 with a SLOW_MAX cell gate, shrink matched delays to what the full stack proves, run the other kernels, one ordered board list. audit/PROGRAM.md unchanged. Audit focus when claims land: the datapath band fit (reproduce from the August build + logs) and every delay-shrink step (full stack both corners, >= 8 seeds, own oracle spot-checks).
- 05:25 T17 started: research item 2 (August gcd kernel x = 0.21). Board column = owner's table; x recomputed from research's logs (median 0.211; 48/48 results = math.gcd). Own FAST_MIN rerun of the August build running.
- 05:47Z T17: own FAST_MIN rerun of Aug gcd_bench_gen in progress (research 382c321b host, +VECFILE +NRUNS=2); first attempt on 22fe1811 lacked +VECFILE (1 batch), discarded.
- 06:06Z new research claim c73c8214 (band 0.288 on Aug gcd: 24/24 complete, every vector 9-10% slow, x=0.21 uniform). Queued own band run after aug_min (T17 row 4).
- 06:23Z T17 row 3 CONFIRMED exact: own FAST_MIN rerun 24/24 batches clean, latmin = research's on 24/24, x median 0.211. REPORT row added for 359e0728. Own band-0.288 run started (row 4).
- 06:37Z research bc77bdd1 (cell-slow = band latencies; 'x=0.21 is the chains'') -> T17 rows 5 (pending own rerun, queued after band run) and 6 (OVERSTATED as wording: inference across designs, conservative consequence).
- 07:12Z T17 row 4 CONFIRMED exact: own band-0.288 run = research's on 24/24 (end time equal), band/board 1.092-1.111, cost coefficients equal. Cell-slow run (row 5) started.
- 07:16Z lock; cell-slow run in vvp; research added tools aug_board_vectors.py / aug_x.py (tooling, no new claim).
- 07:57Z T17 row 5: cell-slow override verified in annot.sdf (CARRY4 90, SELMUX 1454, FFX 1950, + 2 SLICE_LATX latches moved by the SLICE_FFX knob). Sim running.
- 08:02Z T17 row 5 done: own cell-slow = research's cellslow log exactly; latmin = band 24/24, but latmax of (786432,262144) 334 vs 333 (also in research's logs) -> 'identical cycle for cycle' OVERSTATED (minor). T17 complete except SLOW_MAX own re-sim.
- 08:38Z lock; own SLOW_MAX rerun of Aug gcd in vvp (closes T17 row 3 UNVERIFIED part). No new research/formal claims.
- 09:15Z T17 row 3 closed: own SLOW_MAX rerun = research's max log on all 24 batches (race batches too); x from own runs only: 0.211. T17 complete.
- 09:16Z T17 row 7: per-term x 0.196-0.210 CONFIRMED from own runs.
- 09:18Z T17 row 8: GLS_SDF_BAND_INST chain selection CONFIRMED (own src-line selection = regex, 1183) and arc count 8756 reproduced; scope note (anchor + tail route not moved).
- 09:59Z lock; no new research/formal claims since ae13f18f / 0be49560.
- 10:40Z T18 started: research b624a41a BQ#3 cell check 8/8. sdf md5s for d, 9 = my earlier routes; journal/table swap seeds 4/5 laps; own seed-5 route + cell check running.
- 11:21Z T18: own seed-5 route sdf c71ed2cb / xray f3ca9bea = table's seed-5 row; cell check sim at vec 5/16.
- 12:02Z lock; T18 seed-5 cell check 13/16 vectors, errs 0 so far.
- 12:16Z T18 row 3: own seed-5 cell check 16/16 errs 0, 62/50/73 = TSV (journal 06:32 has 4/5 swapped), EQUIVALENT; rerunning for lapcheck (sweep logs deleted).
- 12:42Z lock; T18 seed-5 rerun for lapcheck in progress.
- 13:22Z lock; T18 seed-5 rerun in progress.
- 13:51Z T18 done: seed-5 rerun identical, LAPCHECK CLEAN; REPORT row for b624a41a.
- 14:03Z lock; no new claims (research locks only; formal 0be49560).
- 14:43Z lock; T18 seed-4 route + cell check running.
- 15:34Z lock; container restart at ~14:50 left the seed-4 run alive (setsid); watchers re-armed.
- 15:42Z T18 row 4: own seed-4 cell check 16/16 errs 0, 56/44/65 = TSV, md5s = TSV, lapcheck CLEAN. Research worst-case gate (journal 14:59, BQ#2 4/4) not yet tabled; will check seed 6 when it is.
- 15:44Z T19 started: own worst-case gate run (chains 0.21 + cells SLOW_MAX + 0.288 + M) on BQ#2 s6 ahead of research's table.
- 16:14Z lock; T19 run in progress.
- 16:55Z lock; T19 run in progress.
- 17:32Z T19 row 1: own worst-case gate run BQ#2 s6 (draw 1): 16/16 errs 0, 64/52/75, lapcheck CLEAN, 8756 chain arcs = research's. Awaiting research's table.
- 17:35Z lock; T19 draw-2 run in progress.
- 17:35Z T19 row 1 CONFIRMED exactly vs research 1c3df20c seed-6 row (64/52/75, draw 1). REPORT row added. Draw 2 running.
- 18:15Z lock; T19 draw-2 in progress.
- 18:17Z T20: research 7edc6af6 'live LUT written as constant 0 (FASM-writer defect)' REFUTED: both LUT2 inputs on A1 (X_ORIG_PORT_A1 'I1 I0', GND-driven), INIT 4'h4 -> constant 0 in the netlist; bits (own read-back) INIT 0 = correct; fasm_equiv false positive.
- 18:55Z lock; T19 draw-2 in progress.
- 18:57Z T21 started: research ca6756ba ipow x = 0.225. Board latencies own-extracted = research's 17/17, results = a^b mod 2^32. Own min/max sims running. (Research README repeats the T20-refuted 'live LUT'.)
- 19:15Z T19 row 2: worst-case gate BQ#2 s6 draw 2 PASS 16/16, 64/52/75, lapcheck CLEAN.
- 19:33Z T21 CONFIRMED: own ipow min/max = research's logs, results = board, x 0.226 median / 0.225 LS.
- 19:33Z T22: research d9b5dc8a isprime GND-buffer classification CONFIRMED (JSON GND buffers -> 0; own read-back INIT 0).
- 19:36Z lock.
