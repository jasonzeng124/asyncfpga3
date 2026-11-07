# A-e9par (probe E9Par, shard A): a log rule for parallel virtual C-elements

STATUS (2026-10-29 ~11:45): DONE. Lean: new rule `par` (Events9Par.par_fact, runLogP_sound,
verdict9par), design_verdict9par (new named hypothesis HRst: one reset per arbiter's readers),
core_of_en_rst; check.sh OK on the import closure (§6). Generator tools-A/xaudit/par/. 16 rows: all 54
structural items certified on 10 rows (d/3/4/5 slow+fast, 3/4 gb: CLEAN), 51 / 53 on d gb / 5 gb,
28–36 on indep (lag > walk delay). Controls behave as predicted (§5; NEGpair vacuous).

## 1. Plain statement

**Problem.** With the corrected arbiter core (E8ArbFix) each grant `g_b` has a shadow `s_b`
(two virtual two-pin C-elements reading the same request and the same `ctl` through different
pin bands) and `R0` is the merge of the shadows. Every Events7/8/9 log rule bounds a node's
count from ABOVE by what it reads; 54 items per gcd_hw row needed a walk from a shadow to its
grant or back (E8ArbFix §4: (a) grant ctl-pin Back, (b) shadow request-pin Back, (c) the ack
A_b's guard EXIT walk), i.e. a LOWER bound on one C-element's count from its parallel twin's.

**The rule** (`Formal/Core/XAudit/Events9Par.lean`).
- `ParOK rs z y e tp pm` (decidable, from the certificate's own bands): `z`, `y` non-merge stages
  in the same reset class (`rs z = rs y ≠ 0`); each pin `q` of `y` is PARALLEL (`PinPar`) to pin
  `pm q` of `z`: same source, same kind (not guarded), same label if filtered, same operator if a
  line, same number of copies; `off z ≤ off y + tp`; `hiF y ≤ e + loF z`; and copy by copy
  `hiF y + hiC y q i ≤ e + loF z + loC z (pm q) i`.
- **`par_fact`** (proved): for every `Beh7` behaviour `x` with `RstSync x rs` (nodes of one reset
  class have the same reset signal `r`) and `Net4.OK7`: `M v z ≤ M (v + e) y + tp` for all `v`.
  Proof is direct, no induction: a non-merge stage's count is the min of its pin counts at its
  sample (`M_eq`); each copy of `y`'s pin samples no earlier than the same copy of `z`'s; a
  pin's count is monotone in its copies' counts (`pin_par`, all kinds incl. AND/OR lines); and
  `y`'s reset is over when `z`'s is (same `r`, anti-monotone, `hiF y ≤ e + loF z`).
- Log `LnP` = Events7 `Ln` (`base`) + `dsub` (a first-reach SUB line IN the log, sound by
  `Events9.dsub9_sound` when its `wS` is valid) + **`par w1 w2 z y e tp pm`**: from a walk
  `w1` ending at `z` (any label context) and an unlabelled walk `w2` from `y` with
  `e ≤ d1 + d2`, the walk with delay `d1 + d2 − e`, tokens `t1 + tp + t2`. A failing `par` /
  `dsub` line degrades to a trivial `refl` judgement (only the items citing it lose their
  certificate; the log is not rejected).
- **`runLogP_sound`**, **`verdict9par`** (proved): `Events9.verdict9` with this log; the item
  checks are the unchanged `backOK7` / `lineOK7` / `exclOK7` / `guardOK8` (sanitized hyp lines).
- **`design_verdict9par`** (`Events9ParBeh.lean`, proved): `Events9Arb.design_verdict9arb`
  (HARB7') with the log `LnP` and ONE new named hypothesis **`HRst`**: for each reset class
  `k ≠ 0` there is a signal `ρ k` such that every node of class `k` has an `ND7` node behaviour
  with reset `ρ k`. Same conclusion as design_verdict9arb.
- `Events9ParRst.lean` (proved): `VRdR` / `CoreFixR` / `CoreOfR` (the corrected core with ONE
  explicit reset for the four readers of an arbiter), `and_cel_rst`, **`core_of_en_rst`**:
  `Events9Arb.core_of_en` with the same hypotheses gives the corrected core with the common
  reader reset `decide (u < T0)`. So the common reset HRst asks for is what the cell-level
  sufficiency construction produces.

**Assumed** (a CLEAN `xevents9par` row): per-pin SatPin, constants + reset, HARB7' (the corrected
core; itself still a hypothesis, E8ArbFix), HRst (per arbiter: its two grants and two shadows
share one reset signal in their ND7 realisations), SelOK, SelPart; the trusted parser/reader.
**NOT covered**: the link CoreOfR → HRst over a parsed `Net4` (same gap as CoreOf → HARB7);
HARB7' itself (hstall / RdOK not discharged); the reset classes come from the (untrusted)
certificate's `rc` field and only shape HRst (a wrong class makes ParOK fail or HRst stronger,
never unsound). No Lean-level negative control of `par_fact` (controls are checker-level, §5).

## 2. Lean files (Mathlib-free, no sorry/axiom/native_decide)
- `Formal/Core/XAudit/Events9Par.lean` (imports Events9Cert): `PinPar`, `ParOK`, `LnP`, `degr`,
  `parJ`, `conclP`, `runFromP`, `runLogP`, `RstSync`, `pin_par`, **`par_fact`**, `degr_sound`,
  `parJ_sound`, `conclP_sound`, `runFromP_sound`, **`runLogP_sound`**, **`verdict9par`**.
- `Formal/Core/XAudit/Events9ParBeh.lean` (imports Events9ArbBeh, Events9Par): `HRst`, `ndAllP`,
  `design_behP`, **`design_verdict9par`**.
- `Formal/Core/XAudit/Events9ParRst.lean` (imports Events9Arb): `VRdR`, `vrdR_vrd`, `CoreFixR`,
  `CoreOfR`, `coreOfR_coreOf`, `and_cel_rst`, **`core_of_en_rst`**.
- `Formal/Core/XAudit/Events9ParMain.lean`: the `xevents9par` executable (Events9Main with the
  `LnP` reader: kinds `par`, `dsub9`; reset classes from node field `rc`; prints par/dsub9
  counts and degraded lines).
No existing file or statement changed. Lakefile/Formal.lean untouched.

## 3. Generator (`formal/tools-A/xaudit/par/`, untrusted)
- `cert9p.py` = events9/cert9.py + parallel pairs: for each arbiter (model.py `arbs`, mode fix)
  the ordered pairs `arb:g_b → vsh:R0/b` and back, identity pin map, lag
  `e = max(hiF y − loF z, max_{q,i} (hiF y + hiC y q i − loF z − loC z q i))` (the least lag ParOK
  accepts), `tp = 0`; every reader node gets `rc` = arbiter index + 1. The walk search may step
  `z → y` with delay `−e` (outside label contexts) only for an item whose search WITHOUT such
  steps fails, so cert9's walks are unchanged. Walks are emitted as left folds of `par` lines;
  a labelled walk from a guarded source through SUB then a pair is a `dsub9` LOG line (with wS)
  continued by `par` lines, cited by a `copy` hyp line. Controls `--no-par`, `--neg-lag=K`,
  `--neg-pair`, `--neg-rc`; `mutband.py` (NEGband).
- `xe9p.sh` (lean --run on an overlay `$OL`), `run.sh` (16 rows), `table.sh`, `neg.sh`.

## 4. Runs (16 gcd_hw rows, E8Mux corrected bands, xevents9par via lean --run on overlay ov2)
`par/run.sh` (inputs as arbfix/run.sh: `$S/e8mux/w/<seed>/new/skel.json` + band files passing
e8mux/checkbands.py), outputs `par/results/xe9p_<s>_<c>.txt`, `cert9p_<s>_<c>.txt`, table
`par/results/table.txt` (`par/table.sh`: "structural" = E8ArbFix's 54 items (a) grant ctl-pin
Back, (b) shadow request-pin Back, (c) ack guard; certified = residual in arbfix/results
xe9_*_fix.txt and not residual here). Every row: log accepted by runLogP, every emitted par line
passes ParOK (0 degraded), all 18 dsub9 lines valid, 9 reset classes / 36 nodes.

| seed corner | par lines pass/emitted | Back cert | guards cert | structural certified (a)+(b)+(c) | residual fix -> par |
|---|---|---|---|---|---|
| d slow | 54/54 | 866/866 | 63/63 | 18+18+18 = 54/54 | 54 -> 0 (CLEAN) |
| d fast | 54/54 | 866/866 | 63/63 | 18+18+18 = 54/54 | 54 -> 0 (CLEAN) |
| d indep | 43/43 | 852/866 | 50/63 | 16+12+7 = 35/54 | 67 -> 32 (RECOGNISED, RESIDUAL 32) |
| d gb | 53/53 | 866/866 | 60/63 | 18+18+15 = 51/54 | 54 -> 3 (RECOGNISED, RESIDUAL 3) |
| 3 slow | 54/54 | 866/866 | 63/63 | 18+18+18 = 54/54 | 54 -> 0 (CLEAN) |
| 3 fast | 54/54 | 866/866 | 63/63 | 18+18+18 = 54/54 | 54 -> 0 (CLEAN) |
| 3 indep | 42/42 | 851/866 | 46/63 | 15+12+1 = 28/54 | 69 -> 41 (RECOGNISED, RESIDUAL 41) |
| 3 gb | 54/54 | 866/866 | 63/63 | 18+18+18 = 54/54 | 54 -> 0 (CLEAN) |
| 4 slow | 54/54 | 866/866 | 63/63 | 18+18+18 = 54/54 | 54 -> 0 (CLEAN) |
| 4 fast | 54/54 | 866/866 | 63/63 | 18+18+18 = 54/54 | 54 -> 0 (CLEAN) |
| 4 indep | 43/43 | 850/866 | 52/63 | 15+13+8 = 36/54 | 67 -> 31 (RECOGNISED, RESIDUAL 31) |
| 4 gb | 54/54 | 866/866 | 63/63 | 18+18+18 = 54/54 | 54 -> 0 (CLEAN) |
| 5 slow | 54/54 | 866/866 | 63/63 | 18+18+18 = 54/54 | 54 -> 0 (CLEAN) |
| 5 fast | 54/54 | 866/866 | 63/63 | 18+18+18 = 54/54 | 54 -> 0 (CLEAN) |
| 5 indep | 42/42 | 852/866 | 49/63 | 15+13+4 = 32/54 | 66 -> 34 (RECOGNISED, RESIDUAL 34) |
| 5 gb | 53/53 | 865/866 | 62/63 | 18+18+17 = 53/54 | 57 -> 4 (RECOGNISED, RESIDUAL 4) |

- **10 of 16 rows CLEAN** (d/3/4/5 slow and fast, 3/4 gb): all 54 structural items certified.
  Under design_verdict9par those rows rest on SatPin, constants/reset, HARB7', HRst, SelOK,
  SelPart. They are exactly the rows that were CLEAN with the old (refuted) core in A-events9's
  corrected-band table (E8ArbFix: none CLEAN with the corrected core and the Events7 rules).
- d gb: 51/54; the 3 left are guards: ua2 of merge3/merge2 fail their ENTRY margin (−53, −70 ps;
  these are the 2 ENTRY residuals the old-core run already had), merge12.uarb2.ua2 has no walk
  (its pair lag 3099 ps > the walk's 2822 ps: the request pin is a delay line).
- 5 gb: 53/54 (merge12.uarb2.ua2 guard, same reason) + uenv1 Back −61 and the two Line −90/−70
  of E8ArbFix (not structural).
- indep rows: 28–36 of 54; the lag (band widths under independent corners, 580–5734 ps) exceeds
  the walk delay for the rest (cert9p reports `lag e > walk delay`), plus the margin failures
  the indep rows always had. These are real margin failures of the rule, not search failures.
- Real nodes unchanged: the min real Back margins equal E8ArbFix's (d 937/423/526, 3 748/332/416,
  4 919/400/553, 5 186/107/−61 for slow/fast/gb); cert9p only adds parallel steps to items whose
  search without them failed.

## 5. Negative controls (seed d slow, `par/neg.sh`, outputs `par/results/xe9p_d_slow_<TAG>.txt`)
Positive: CLEAN, 54/54 par lines pass.

| control | mutation | expected (from the rule) | result |
|---|---|---|---|
| NOPAR | `cert9p.py --no-par` | the E8ArbFix certificate: RESIDUAL 54 | 0 par lines; 830/866, 45/63; RESIDUAL 54 |
| NEGlag1 | every par line claims lag e − 1 | every line whose least lag is ≥ 1 degrades (one pair, merge2 g2 → shadow, has least lag 0, clamped) | 53 of 54 degrade; RESIDUAL 53 |
| NEGrc | shadows in reset classes of their own | `rs z = rs y` fails: all degrade | 54/54 degrade; RESIDUAL 54 |
| NEGsrc | every par line's pin map swapped (request ↔ ctl) | `PinPar` (source) fails: all degrade | 54/54 degrade; RESIDUAL 54 |
| NEGband | merge4.uarb1 shadow/0's request pin (4-copy delay line) band lowered by its slack + 1 = **1 ps** (`mutband.py … 0 auto`) | `mutband.py` recomputes ParOK: exactly lines 3388, 3406 (shadow/0 → grant) must fail | exactly 2 degrade; RESIDUAL 2 = that grant's ctl-pin Back and ua1's guard (the two items using shadow → grant) |
| NEGpair | `--neg-pair` (grant b with the other branch's shadow) | — | VACUOUS: the search finds no walk, no par line reaches the checker (RESIDUAL 54 for that reason only) |

Every degraded line leaves the log accepted (the degrade semantics), so these controls show the
checker re-derives each line from the certificate's bands and structure.
## 6. Check
The lead's .lake/build had XAudit oleans up to Events7Cert (+ Events5/6) this session, so check.sh was
run on the not-yet-built import closure of my files, in dependency order (the last four are mine):

    formal/check.sh Formal/Core/XAudit/Events8Arb.lean Formal/Core/XAudit/Events9Arb.lean \
      Formal/Core/XAudit/Events9ParRst.lean Formal/Core/XAudit/Events7Beh.lean Formal/Core/XAudit/Events8Core.lean \
      Formal/Core/XAudit/Events8Cert.lean Formal/Core/XAudit/Events8Beh.lean Formal/Core/XAudit/Events9Cert.lean \
      Formal/Core/XAudit/Events9Beh.lean Formal/Core/XAudit/Events9ArbBeh.lean Formal/Core/XAudit/Events9Par.lean \
      Formal/Core/XAudit/Events9ParBeh.lean Formal/Core/XAudit/Events9ParMain.lean
    ...
    [audit] 3073 declarations checked
    [check] audit (executable) Formal.Core.XAudit.Events9ParMain
    [audit] 2900 declarations checked
    [check] OK

Once lake has built Events9ArbBeh and Events9Arb: `formal/check.sh Formal/Core/XAudit/Events9Par.lean
Formal/Core/XAudit/Events9ParBeh.lean Formal/Core/XAudit/Events9ParRst.lean Formal/Core/XAudit/Events9ParMain.lean`.
Root imports if wanted: `Formal.Core.XAudit.Events9Par`, `…Events9ParBeh`, `…Events9ParRst` (not
Events9ParMain, which defines `main`). Lakefile stanza (NOT added):
`[[lean_exe]] name = "xevents9par" root = "Formal.Core.XAudit.Events9ParMain"`.
The runs used the overlay `$S/E9Par/ov2` (oleans compiled from the same sources with
-DautoImplicit=false by `$S/E9Par/lc2.sh`, from the sources as checked).
