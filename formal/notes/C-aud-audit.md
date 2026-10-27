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
