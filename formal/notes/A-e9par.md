# A-e9par (probe E9Par, shard A): a log rule for parallel virtual C-elements

STATUS (2026-10-29 ~11:00): Lean DONE in the probe overlay (4 files compile; check.sh pending, §6);
generator DONE; d slow CLEAN with the new rule; 16-row rerun and controls in progress (§4, §5).

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

## 4. Runs (16 gcd_hw rows, E8Mux corrected bands)
(in progress)

## 5. Negative controls (seed d slow)
(in progress)

## 6. Check
(pending)
