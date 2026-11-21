# C-aud: answers to the independent audit's OVERSTATED rows on shard C

**Status: DONE** (all 7 items; build + check.sh results at the bottom).

Verdict: every OVERSTATED row on shard C's Lean is answered. Two rows got new Lean theorems
(Ring fair window N(N-1)/2, rule A t = 403 / exact threshold). Two got new modules that
restate or refute the claim (RingGen over the generated LUT, CheckerFixedFn with the XOR
counterexample). The rest are docstring qualifiers. No statement was weakened. Pre-existing
files were edited as follows: doc-only in Checker.lean, CheckerToy.lean, Ring.lean (header)
and Capstone.lean; Rules.lean got doc text plus two new theorems (additive); notes/C-11a-import.md
got a wording fix.

Sources: `git show origin/claude/audit:audit/REPORT.md` (rows 13, 14, 15, 16, 27, 28, 42),
`audit/findings/{C,C2,P4}.md`, `audit/lean/C/gen/timing_audit_tail.lean`, `audit/lean/C2/Rules_audit.lean`.

## Table

| audit row | what changed (file:line, theorem names) | new status |
|---|---|---|
| REPORT 15 / C.md #3: Ring.lean header says the fair window is N(N-1)/2, but `fair_window` proves N(N-1) | NEW `formal/lean/Formal/Net/RingFair.lean`: `fair_window_half` (:82, `2 * is.length ≤ n*(n-1)`), `fair_window_div` (:89, `is.length ≤ n*(n-1)/2`), `every_stage_fires_half` (:94). Proved from `nf_dist` through a rotated sum (`sumTo_rotate`, `two_sumTo_id`). Ring.lean header (lines 50-58, doc only) now gives N(N-1) for `fair_window` and points to RingFair for N(N-1)/2 | **CONFIRMED as now stated**: the N(N-1)/2 claim is now a theorem. Not shown: that N(N-1)/2 is attained |
| REPORT 16 / C.md #9: ring_three/k_tokens are stated over a hand `ctl`; a flipped INIT still compiles | NEW `formal/lean/Formal/Net/RingGen.lean`. The transition system (`gateG` :42, `excitedG` :47, `ReachG` :51, `resetG` :57) is built from the generated `Formal.Gen.Cells.bd_c2n` / `bd_c2n_set` literals, read with `Netlist.next boolSem`. Reset is defined as what the generated cells drive under rst=1. Four `decide +kernel` facts on the literals (`gen_c2n_run` :61, `gen_c2nset_run`, `gen_c2n_rst`, `gen_c2nset_rst`). Headline theorems: `ring_three_gen` :105, `k_tokens_gen` :120, `ring_safe_gen` :132, plus a non-vacuity `example`. Mutant `formal/lean/Wip/Caud/RingGenMut.lean` flips INIT bit 0 of bd_c2n (0x..B2 to 0x..B3): it does NOT compile (`decide` proves `gen_c2n_run` false), and `#print axioms ring_three_gen`/`k_tokens_gen` then shows `sorryAx`. Control `Wip/Caud/RingGenCtl.lean` (same harness, xor 0) compiles with axioms `[propext, Classical.choice, Quot.sound]`. Logs are next to them (`*.log`) | **CONFIRMED**: the headline theorems now depend on the generated INIT. The original Ring.lean theorems are unchanged and still INIT-independent; cite the `_gen` versions for "real INITs" |
| REPORT 13 / C.md #1: `win_exact` "per-node exact" | NEW `formal/lean/Formal/Timing/CheckerFixedFn.lean` (namespace `Formal.Timing.FixedFn`): `xor_never_switches` :42 (auditor's counterexample), `xorRun` :61 (a FixedRun with node 1 = XOR exists, non-vacuity), `win_exact_needs_free_fn` :99. That theorem says there exist a WF net and a fixed function with `win = (5,5)`, fixed runs with that function exist, in none of them does node 1 switch, and with the witness's own function (5,5) is attained. Checker.lean (doc only): module title and bullets lines 1-35, `win_early_attained`/`win_late_attained`/`win_exact` docstrings (around :488-:510) now say "exact over the choice of cell functions; with fixed functions an upper bound" | **CONFIRMED as now stated** (exact over free cell functions; an upper bound for fixed functions, proved). Soundness was never in question |
| C.md #4: `check_exact_disjoint` has the same caveat | Checker.lean doc only: header bullet (:30-35) and the theorem docstring (:597-603): complete only over the choice of cell functions (`mixRun` picks OR/AND); with fixed LUT functions a failing check is only a possible violation | **CONFIRMED (function-agnostic sense, now stated)** |
| REPORT 14 / C.md #2: `corr_bd_violation` "justified under per-event delays" | CheckerToy.lean doc only: header §2 (:27-61) adds "What that does and does not justify". The run needs the wire 0->1 to turn one launch edge into three. Under monotone wires (fixed per-arc delay) the shared-arc check is conservative (`corr_fixed_safe`, on one example). The sound credit is `Formal.Timing.SharedPrefix.pot2_sound` (10l, H_CLEAN_EDGE), plus `Rules.race_sound_clean`/`ruleE_sound`, and `Rules.prefix_credit_needs_clean_edge` for necessity. Same qualifier in the `corrRun` docstring (:206-213) and a new `corr_bd_violation` docstring (:255-258). (SharedPrefix.lean is already at `formal/lean/Formal/Timing/SharedPrefix.lean`, identical to the tcheck copy; I did not create or touch it) | **CONFIRMED as now stated**: model fact, not physical justification |
| REPORT 27 / C2.md 4c: rule A "sound only for data paths <= 402 ps"; 403 unstated; SLACK omitted silently | Rules.lean: NEW `ruleA_band_sound_403` (:356) and `ruleA_band_threshold` (:363): `(∀ te, ruleAPass te tl → 1155*tl < 772*te) ↔ tl ≤ 403`. Doc: header item 3 (:28-36) and the `ruleAPass` docstring (:288-291) state that Lean models SLACK = 0. tighten.py:1106 has `req_guard = max(int(0.2*t),200) + SLACK`, and tighten.py:156-159 sets SLACK = 0 unless `--slack`. Only cells/verify/resize.sh:161-176 passes it (`BD_RESIZE_SLACK`, default 300). A positive SLACK only widens the guard, so soundness carries over and the >=404 counterexample is for SLACK = 0. Also noted: Nat `tl/5` = `int(0.2*t)` | **CONFIRMED, exact threshold**: <= 403 ps (the journal's "<= 402" is off by 1) |
| REPORT 28 / C2.md 1c: imported cells "proved equal to B's binary/Kleene specs" | notes/C-11a-import.md (verdict paragraph + the `_next_K` and `bd_arbcell` bullets) edited. JOURNAL-C.md NOT edited; corrected sentences for the lead below | **wording fixed in the note; journal sentence drafted** |
| REPORT 42 / P4: `gcd_hw_conditional` "every value latched on out0 is gcd a b" | Capstone.lean doc only: module doc (:31-40) and docstrings of `latched_const` and `gcd_hw_conditional` (:66-79). Both hold for ANY network, are definitionally `latched_const` with g := Nat.gcd a b, and carry no gcd content. The gcd_hw-specific theorem is `Formal.Net.CapNet.Gcd.gcd_hw_circuit_safe''` (Formal/Net/CapstoneCut.lean:535: gcd_hw's own operator network, H_CELLS, H_BUNDLE, H_START_ONCE, token-level H_WALK) | **CONFIRMED as now stated** |

## Corrected sentences for JOURNAL-C.md (lead to apply; I did not edit it)

JOURNAL-C.md:68-71, Track 11 (a). The current text reads "proved equal to B's binary/Kleene
transcriptions". Suggested replacement:

> (a) yosys JSON: 11 cells, project's own yosys 0.62 flow, generator + drift check
> (`formal/tools/import/import.sh --check`). The binary next-state of each C-element, latch and
> the arbiter is proved equal to an independent spec (`cSpec`/`clr`/`set`/`bmux`, the bd_arb.v
> header equations). The Kleene comparisons are against B's `lutK <INIT> [pins]` transcriptions
> of the same INITs, so they show only "same INIT and same pin order as B" (enough to carry B's
> Kleene theorems over, not a behavioural check); `bd_arbcell` is covered only that way. A
> flipped INIT bit fails the build.

Commit-message / progress wording ("proved equal to shard B's binary/Kleene specs", bea8b55):
cite as "binary: equal to independent specs; Kleene: equal to B's INIT transcriptions (same
INIT + pin order)".

Other journal sentences the lead may want to align (not edited by me):
* "rule A sound under E's band only for data paths <= 402 ps" (JOURNAL-C.md:59-60):
  "<= 403 ps (exact threshold, `Rules.ruleA_band_threshold`; SLACK = 0)".
* "per-node exact" (track 10a): "sound for every cell function; per-node exact over the
  choice of cell functions (an upper bound for fixed LUT functions, `FixedFn.win_exact_needs_free_fn`)".
* "ring_three / k_tokens with real bd_c2n INITs": cite `RingGen.ring_three_gen` /
  `k_tokens_gen`.

## Commands that check

```
cd formal/lean && export PATH=$HOME/.elan/bin:$PATH
FORMAL_SLOT_CWD=$PWD ../slot.sh lake build Formal.Net.Ring Formal.Net.RingFair Formal.Net.RingGen \
  Formal.Timing.Rules Formal.Timing.Checker Formal.Timing.CheckerToy Formal.Timing.CheckerFixedFn \
  Formal.Net.Capstone
cd .. && ./check.sh Formal/Net/RingFair.lean Formal/Net/RingGen.lean Formal/Timing/CheckerFixedFn.lean \
  Formal/Timing/Rules.lean Formal/Timing/Checker.lean Formal/Timing/CheckerToy.lean \
  Formal/Net/Ring.lean Formal/Net/Capstone.lean
# mutant / control (Wip, not built by lake):
cd lean && FORMAL_SLOT_CWD=$PWD ../slot.sh lake env lean Wip/Caud/RingGenMut.lean   # must FAIL
FORMAL_SLOT_CWD=$PWD ../slot.sh lake env lean Wip/Caud/RingGenCtl.lean   # must pass
```

## Files

New: `formal/lean/Formal/Net/RingFair.lean`, `formal/lean/Formal/Net/RingGen.lean`,
`formal/lean/Formal/Timing/CheckerFixedFn.lean`, `formal/lean/Wip/Caud/RingGenMut.lean` (+ .log),
`formal/lean/Wip/Caud/RingGenCtl.lean` (+ .log), this note.
Edited: `Formal/Timing/Checker.lean` (doc), `Formal/Timing/CheckerToy.lean` (doc),
`Formal/Net/Ring.lean` (header doc), `Formal/Net/Capstone.lean` (doc),
`Formal/Timing/Rules.lean` (doc + 2 theorems), `formal/notes/C-11a-import.md`.

## Fidelity / what this does NOT show

* RingGen uses the generated SYNTHESIZED cell (yosys `synth_xilinx`), not a placed/routed one
  (11b's FASM read-back covers physical INIT + pin permutation separately). Drift between
  `cells/rtl` and `Formal/Gen/Cells.lean` is caught by `gen.sh --check`, not by Lean. H_SI and
  H_RESET_CLEAN are unchanged.
* The mutant flips the INIT in a local copy of the literal (`bd_c2n_m`), not in the generated
  file. Editing Gen/Cells.lean itself would also break `Formal.Gen.ProofsCE` (as the 11d
  negative control already shows).
* `win_exact_needs_free_fn` is one counterexample. It does not say which real LUT functions
  attain their windows. Fixed-function exactness would need the functions in the checker.
* The `corr` conservativeness under fixed delays is still shown on one example only.
* `ruleA_band_threshold` is the SLACK = 0 rule. With `resize.sh`'s SLACK = 300 the threshold
  moves up (not computed here).

## Surprises

* Doc edits to Checker.lean / Ring.lean change their oleans, so their dependents (tcheck,
  SharedPrefix, the Capstone chain) rebuild. Building Capstone also rebuilt ~20 stale
  dependency modules that other probes had changed (OpsMuxN, GcdHwSeg, CapstoneRing). All built.
* JOURNAL-C.md:70 already says "transcriptions" rather than "specs". The overstated wording
  survives in the commit message (bea8b55) and in this note's old verdict paragraph (now fixed).

## Results (2026-10-27)

* `lake build` of the 8 modules above: `Build completed successfully (34 jobs)`.
* `./check.sh` on the 8 files: textual scan clean, `[audit] 2798 declarations checked`, `[check] OK`.
* `Wip/Caud/RingGenMut.lean`: exit 1, 1 error (`decide` proved `∀ a b q, stepOf bd_c2n_m a b q false = ctl a b q` false);
  `ring_three_gen`/`k_tokens_gen` depend on `sorryAx` there. `Wip/Caud/RingGenCtl.lean`: exit 0, axioms
  `[propext, Classical.choice, Quot.sound]`. scan.py is clean on both Wip files.

## Session 2026-10-29: probe aud2 (every REPORT.md row on shard C, re-checked)

Source: `git show origin/claude/audit:audit/REPORT.md` (150 lines), findings `C.md`, `C2.md`,
`P4.md`, `P5.md`, `P7-capstone.md`, `tcheck.md`, `p2-python.md`. Shard-C rows are those whose
claim is in JOURNAL-C.md, `formal/notes/C-*.md`, `Formal/{Net,Timing,Gen}` or `formal/tools`.
Rows on `Formal/Cells` (ArbPin2, OnGcdArbKappa, OnNetlistArbKappa, ArbCorners, PipeTimedN,
ArbHeldTimed, ArbOverlapRace, ResetGcdWave, ResetGcdVec2, Bnet, RigSrc, Contracts, CTreeExact JSON)
are shard B's and are not listed. Each claim below was checked against the Lean statement
(grep + read) before rewording. Only notes were edited; no Lean, no tool, no JOURNAL-C.md.

### OVERSTATED / REFUTED rows

| REPORT row (commit: claim) | verdict | answered? | what was done / still to do |
|---|---|---|---|
| 71ee3e86: `win_exact` "per-node exact" | OVERSTATED | yes (aud, 10-27: CheckerFixedFn) | nothing |
| 71ee3e86: `corr_bd_violation` "justified under per-event delays" | OVERSTATED | yes (aud, CheckerToy docs) | nothing |
| 71ee3e86: Ring header N(N-1)/2 | OVERSTATED (doc) | yes (aud, RingFair) | nothing |
| 71ee3e86: ring_three/k_tokens "with real bd_c2n INITs" | OVERSTATED (mild) | yes (aud, RingGen) | nothing |
| d420b53: rule A "sound only for data paths <= 402 ps" | OVERSTATED by 1 ps | yes (aud, `ruleA_band_threshold`: <= 403) | nothing |
| d420b53 / bea8b55: imported cells "proved equal to B's binary/Kleene specs" | OVERSTATED (wording) | yes: C-11a fixed (aud); JOURNAL-C.md Track 11 verdict now reads "independent binary specs (the Kleene comparisons only show the same INIT and pin order)" | the commit message cannot be changed; cite as in the aud table |
| 55fde94 (C-10c): "measured/predicted over 47 comparable rings 1.361 / 1.067 / 0.989" | OVERSTATED (numbers confirmed) | **now** | C-10c verdict bullet and §3 reworded: one measured ring; the 47 are re-routed predictions from another design; 1.067/0.989 depend on a population scale fitted to silicon (unscaled 0.939/0.605; 7-link scale 1.144/1.076, auditor's numbers, not re-run by me) |
| 1e7947a (C-10g): rule J "verdict agreement ... J 67/70"; model omits slice OUTMUX | PARTLY REFUTED | partly: C-10h (06:2x 10-27, after 1e7947a) added the driver-side hop (a5lut→amux, …) and gives Jx 71/72 | numbers: probe 10m (rerun of all rows). C-10g wording: 10m owns C-10g. Outside C-10g only C-10h cites J counts, and those already include the hop. JOURNAL-C.md:255 (session log) keeps the old sentence; the verdict block cites the OUTMUX gap with "10m re-running all rows" |
| 1e7947a (C-10g): "+490 ps on A1" (a mean); J over-credit "~95 ps avg (max 211)"; F ucmpi8 "from SDF-fallback arcs" | OVERSTATED / misattributed | partly: C-10h already re-classifies ucmpi8 as a band finding (guard weaker than band, as the audit says) | "+490"/"95 ps" appear only in C-10g (10m's) and JOURNAL-C.md:255/374 (session log, historical). No other C note repeats them (grep). 10m to fix C-10g |
| eecc6f7: `gcd_hw_conditional` "every value latched on out0 is gcd a b" | OVERSTATED | yes (aud, Capstone docstrings); **now** also C-8l verdict (qualifier: any network, no gcd content, cite `gcd_hw_circuit_safe3`) | nothing |
| eecc6f7 (1149aa1, RtFbGcd*): RT_FB "0 failures in every one-corner model" | OVERSTATED (likely) | partly | numbers: probe 10f2 (C-10f is 10f2's). **Now**: C-gcd_hw-hypotheses §3 R row cites C-10h's R/Rc (hop included; failures only at the rig's urig.uenv1, band only; kernel min seed d +23/+19) and flags C-10f's claim as pre-hop. No other C note repeats "every one-corner model" for gcd_hw (grep) |
| eecc6f7 (2610f5f): gcd_hw_hypotheses N12 "Negative inputs genuinely loop"; §0 stale about C-8l | OVERSTATED (minor) | **now** | checked `gcdC` (Net/GcdHwProof.lean:72-74): `b = 0` returns `some a` at once, so `gcdC (2^32-1) 0` returns; `(INT_MIN, INT_MIN)` from the audit. C-gcd_hw-hypotheses H_INPUT_RANGE row and §0.2 "range" row reworded; C-8k:105-106 and :115-116 reworded ("exhaust the fuel tried", non-termination not proved). §0 rewritten (Task 2). formal/out/gcd_hw_hypotheses.md (shard A) already says it no longer claims it (its row 44) |
| f4696cc (71f12a8): `gcd_hw_circuit_safe''` capstone | CONFIRMED as SAFETY only; liveness / non-vacuity UNVERIFIED | yes: non-vacuity by 8t (`gcd_hw_joint_witness`, audit 299a16f CONFIRMED); liveness reduced (8z) | recorded in C-gcd_hw-hypotheses §0 (T4w, T6) |

### CONFIRMED rows with a caveat on shard C

| REPORT row | caveat | answered? | done / to do |
|---|---|---|---|
| fccbd1b: `gcd_hw_live_final` | conditional; no joint witness (8t violates H_BOUNDED_DELAY'); 2092f12 correction (8u not to be cited) confirmed | yes in JOURNAL-C | **now**: C-8u carries a correction banner; C-gcd_hw-hypotheses §0 T6/T6x and register say "no witness" / "likely vacuous" |
| ae791b6 (8s2) / 824f130 (B): `gcd_rig_first`(`_env`) | non-vacuity partly argued / UNVERIFIED | **now** (wording) | C-8s2 "does NOT show" gets "no Lean witness; 8t's run is not one (start rises before out0 is acknowledged; not checked in Lean)". A witness is open |
| eecc6f7: gcdhw_ring_ge3 etc. | "8j's deadlock cannot occur" is an argument, not a theorem; FEASIBILITY row 8 stale | **now** for the note | C-gcd_hw-hypotheses T5 reworded. FEASIBILITY is shard A's |
| d420b53: 11b `q1_follow_hold_s1_ps` | non-vacuity witness constant-false (consistency only) | **now** | C-11b new "Non-vacuity" section: no witness in the tree; the audit's is constant-false; a switching witness is open |
| d420b53: 9b RingCheck | H_ONLY_LINKS_STORE not named in RingCheck.lean (notes only) | no (Lean) | C-9b already names it. To do (Lean owner / lead): one docstring line in `Formal/Net/RingCheck*.lean` naming H_ONLY_LINKS_STORE. Not done here (Lean is out of my scope) |
| f4696cc: RuntAck 288/288 + 304/304 (3e2c968, C-10j) | routes not the board bitstreams, not on disk; one corner per row (no band); depends on server latency and H_FF_DRAINED | **now** | C-10j verdict gets a one-paragraph scope qualifier (H_SRV and H_FF_DRAINED were already listed under "Hypotheses") |
| 1e7947a: tcheck E/F/H band-only, A artefact, RT_FB worse (seed 2 −114/−219, seed 4 −81/−201) | RT_FB at the rig is worse than 10g said | yes: C-10h already reports −117/−221 and −86/−243 with the hop | nothing |
| 7f46f23 (C-10n): tie-off false path | CONFIRMED; "0.9 ns" not seen by the auditor (2.0-4.2) | no | C-10n is 10m's; 10m to qualify "0.9-4.2" |
| 71ee3e86: muller_pipeline / muller_live | needs H_SI, isochronic fork, 3 liveness assumptions the journal sentence omits | partly in C-8a (lines 125-210 state the isochronic fork on c and DELAY = DACK = 0) | the JOURNAL-C Track 8 sentence "given per-link obligations" could add "under H_SI and an isochronic fork" (lead) |
| 299a16f, 8965ea0, 861de85…: joint witness, ipow_circuit_safe3, Ring, checker soundness, mutation tests, builds | CONFIRMED | — | nothing |

### Files edited (notes only, all wording)

`notes/C-gcd_hw-hypotheses.md` (new §0; H_INPUT_RANGE, H_MUXN_SEL, §3 R row, §5 status line,
§7 marked historical), `notes/C-8k-gcdnat.md`, `notes/C-10c-prjxdelay.md`, `notes/C-8u-live.md`
(banner), `notes/C-8s2-rig.md`, `notes/C-8l-capstone.md`, `notes/C-11b-fasm.md`,
`notes/C-10j-runtack.md`, this note. Not touched (other probes): C-10g, C-10n (10m), C-10f
(10f2), C-12a/b/c and C-10i (12d), C-11f (11f).

### Found while checking (not audit rows)

* C-gcd_hw-hypotheses §2 said H_MUXN_SEL is checked by rule E on `umux21`; 8w found no rule-E
  row for it on any of the 4 routes. Reworded to "unchecked".
* None of the 8m-8z modules (CapstoneSafe … CapstoneLiveNdWalk, CapstoneRig, CapstoneWitness3)
  is imported by `Formal.lean`. That is expected (lakefile globs every module under Formal/;
  Formal.lean imports only Core), not a gap.
