# A-events9 (probe HDsub): HDsub proved by a first-reach SUB rule (shard A)

STATUS (2026-10-29, probe HDsub): DONE. Lean checked (check.sh OK, no sorry), 16 rows on old bands +
16 rows on E8Mux corrected bands, xevents8 comparison byte-identical, 4 negative + 1 positive control as expected.
check.sh OK (see "Check").

## Verdict

**HDsub is no longer a hypothesis.** `Events9.design_verdict9` is `Events8.design_verdict8`
with the 126 `dsub` hypothesis judgements PROVED by a new log rule `dsub9`, instead of
assumed. On gcd_hw R5 (seeds d/3/4/5) every one of the 126 judgements carries a valid
first-reach walk on all 16 rows, so the rows are exactly the Events8 rows (same certified
items, same margins, same verdict) with HDsub removed from the hypothesis list.

**Hypotheses of `design_verdict9` (exact; `Formal/Core/XAudit/Events9Beh.lean`).**
Given `Recog6 d net b rn rank rw fuel`, `net.OK7`, `runLog net b parts log = some J`, and the
checker's per-item results (`hcp`/`hcx`/`hcl`/`hcg`: `backOK7`/`exclOK7`/`lineOK7`, and
`guardOK8 … (hl.map (san J)) …` on the SANITIZED hypothesis lines) — all evaluated by
`xevents9` — then for every per-pin behaviour `x` of the parsed netlist with
- `SatPin d plG x` (the per-pin netlist semantics),
- constant wires (`x (wire 0) = false`, `x (wire 1) = true`), reset `x (wire rw) t = decide (t < T)`, `1 ≤ T`,
- `HARB7 net b rn x cv` (H_ARB),

and every select sequence `sel`, there is a `Beh7` `bh` realising `x` (its counts give `x`'s
control wires, its guarded count is `gcnt`) such that
- `SelPart sel parts` → `bh.SelOK` → (residual obligations of the items NOT certified: Back
  `P ≤ M+1`, merge `fodd ≤ 1`, line `ContigF`, guard `GuardPin`) →
  every real LUT wire equals its reset value flipped `M t j` times, at every time `t`.

On a CLEAN row the residual obligations are vacuous, so the verdict rests on: **SatPin,
constants + reset, H_ARB, SelOK, SelPart**. Neither GuardOK nor HDsub is a hypothesis.
Trusted (not proved): the JSON/netlist parsers, the certificate reader and its mapping to
`Net4`/`Bands4`/`RNode`/`Ln`/`GD`/`HLn9`, the printed numbers, and Lean's `--run`
interpreter/compiler. `design_guardOK9`: on a row with every guarded pin certified,
`Beh7.GuardOK` holds (same hypotheses).

**What it does NOT cover.** H_ARB, SelOK, SelPart remain hypotheses (E8Hyp's subject). The
bands are the committed ones (xray_delay 99b10a6d), which omit the slice OUTMUX hop on
O5/F7/F8 arcs (audit row; probe E8Mux); a CLEAN row is a statement about THOSE bands. The
indep/gb residual rows are unchanged from Events8 (margin failures, not HDsub).

## The rule `dsub9`

A `dsub` judgement (Events8) is a SUB conclusion for a labelled walk that starts at the
guarded source `a = D` instead of the label source `S`. Rule `dsub9` adds one premise:
a log line `wS`, an unlabelled walk `S → a` with at most one token (any delay):
`M v S ≤ M (v − dW) a + tW`, `tW ≤ 1` (`Events9Cert.WSOK`: `J[wS].u = false`, `c = none`,
`a = S`, `bb = a`, `t ≤ 1`).

Soundness, by strong induction on time `u` (`Events9Cert.first_reach`, abstract; instantiated
in `dsub9_sound`): with `m = M u a` and `s = F xm (u − d1)` the merge sample,
- if `M s S ≤ m`, conservation (`filt_ℓ m + Σ_{i≠ab} filt_i m ≤ m`) and `w1` give
  `filt_ℓ m ≤ P xm ab s + t1` (as the Events7 SUB rule);
- if `M s S ≥ m + 1`, `wS` says `a` had already reached `m` at `u' = s − dW < u`
  (strict because `F xm v < v`, `F 0 = 0`); monotonicity gives `M u' a = m`, and the induction
  hypothesis at `u'` plus monotonicity of `P xm ab ∘ F xm` give the bound at `u`.
Then `w2` finishes exactly as the Events7 SUB rule. This is the "first time S reaches 2k+1"
argument of A-events8 as a well-founded descent; no parity or timing margin is needed.

`san J : HLn9 → HLn` keeps a `dsub` line only if `wsOK J S a wS`; otherwise it becomes
`copy J.size` (no judgement, so a guard certificate citing it is rejected). `hdsub_san`:
`Events8.HDsub` holds for `hl.map (san J)` for EVERY behaviour. `verdict9` = `verdict8` on the
sanitized list with that proof.

Lean-level negative controls (in `Events9Cert`):
- `first_reach_two_tok_neg`: with `Sc v ≤ Dc (v − dW) + 2` (a 2-token walk) every other premise
  of `first_reach` holds and its conclusion fails (concrete counts). So `t ≤ 1` is needed.
- `dsub_counts_neg`: counts at ONE time satisfying `w1`, the other arm's U-bound and even the
  1-token walk at that time violate the conclusion: the descent in time is essential.

## Lean files (Mathlib-free)

- `Formal/Core/XAudit/Events9Cert.lean`: `first_reach`, `filt_tf`, the two controls, `HLn9`,
  `HLn9.isD`, `WSOK`/`wsOK`, `san`, **`dsub9_sound`**, **`hdsub_san`**, **`verdict9`**.
- `Formal/Core/XAudit/Events9Beh.lean`: **`design_verdict9`**, `design_guardOK9`.
- `Formal/Core/XAudit/Events9Main.lean`: the `xevents9` executable (Events8Main + `HLn9`
  reader with field `wS`, sanitizing with `san` before `guardOK8`).

Fixes made this session to the 2026-10-28 snapshot (Wip/_snapA): the `h3` monotonicity step
in `dsub9_sound` had its arguments reversed (a false `omega` goal); `let d1` blocked `omega`
(inlined); `HLn9.isD` moved from Main into `Events9` (field notation); two tactic fixes in the
`first_reach_two_tok_neg` proof; a dead `exact` removed. No statement changed.

## For the lead

Lakefile stanza (NOT added; lakefile.toml untouched):

```toml
[[lean_exe]]
name = "xevents9"
root = "Formal.Core.XAudit.Events9Main"
```

Root imports if wanted: `Formal.Core.XAudit.Events9Cert`, `…Events9Beh` (not `Events9Main`,
which defines `main`). Until the stanza exists, `tools-A/xaudit/events9/xe9.sh` runs it with
`lake env lean --run Formal/Core/XAudit/Events9Main.lean` against an overlay `$OL` of oleans
(built by `mk9.sh`, or here by the probe's scratch `bdeps.sh`; the lead's `.lake/build` had no
XAudit oleans yet this session).

## Check

The lead's `.lake/build` had no XAudit oleans this session, so check.sh was run on the whole
Mathlib-free import closure (34 files, in dependency order; the last three are this probe's):

    formal/check.sh Formal/Core/Kleene.lean Formal/Core/Lut.lean Formal/Core/Circuit.lean \
      Formal/Core/Trace/Discrete.lean Formal/Core/XSim.lean Formal/Core/XAudit/{Design,Parse,Events,
      EventsRing,EventsDesign,Events2,Events2Time}.lean Formal/Core/LutCells.lean
      Formal/Core/XAudit/{Events2Design,Events2Strict,Events2PinDesign,Events3,Events4,Events5Line,
      Events5,Events6Gate,Events6Cert,Events6Design,Events6Beh,Events7Core,Events7Excl,Events7Cert,
      Events7Beh,Events8Core,Events8Cert,Events8Beh,Events9Cert,Events9Beh,Events9Main}.lean
    ...
    [audit] 2741 declarations checked
    [check] audit (executable) Formal.Core.XAudit.Events9Main
    [audit] 2827 declarations checked
    [check] OK

Once lake has built Events8Beh, the short form is
`formal/check.sh Formal/Core/XAudit/Events9Cert.lean Formal/Core/XAudit/Events9Beh.lean Formal/Core/XAudit/Events9Main.lean`.

## Runs
All runs 2026-10-29, `lean --run` on the probe overlay (oleans compiled from the working tree
with `-DautoImplicit=false`), inputs regenerated by `events7/rerun/prep.sh` into the probe's
scratch dir: net.json md5 d 5c0830d5 / 3 1d655434 / 4 8da9f6cf / 5 1537cb0a (= events5/builds.txt),
committed bands (xray_delay 99b10a6d, no OUTMUX hop on O5/F7/F8).

**xevents9, 16 rows** (`tools-A/xaudit/events9/run9.sh`, `table9.sh` -> `table9.txt`,
outputs `xe9_<seed>_<corner>.txt`, cert9.py summaries `cert9_*.txt`): on every row
`126 labelled walks from a guarded source through SUB, 126 with a valid first-reach walk wS
(dsub9); none is a hypothesis`, and the log is accepted.

| seed | corner | guarded certified | min BACK-G / ENTRY / EXIT1 / EXIT2 (ps) | residual guard / all | verdict |
|---|---|---|---|---|---|
| d | slow | 63/63 | 5655 / 415 / 2665 / 4218 | 0 / 0 | CLEAN |
| d | fast | 63/63 | 2637 / 204 / 1144 / 1807 | 0 / 0 | CLEAN |
| d | indep | 51/63 | 2121 / 1 / 615 / 1004 | 12 / 21 | residual |
| d | gb | 60/63 | 4258 / 80 / 1788 / 3158 | 3 / 3 | residual |
| 3 | slow | 63/63 | 5300 / 422 / 1171 / 2782 | 0 / 0 | CLEAN |
| 3 | fast | 63/63 | 2402 / 184 / 482 / 1178 | 0 / 0 | CLEAN |
| 3 | indep | 46/63 | 1822 / 451 / 1742 / 5283 | 17 / 30 | residual |
| 3 | gb | 63/63 | 4145 / 88 / 548 / 1914 | 0 / 0 | CLEAN |
| 4 | slow | 63/63 | 5586 / 802 / 1548 / 2700 | 0 / 0 | CLEAN |
| 4 | fast | 63/63 | 2481 / 355 / 667 / 1146 | 0 / 0 | CLEAN |
| 4 | indep | 51/63 | 2037 / 25 / 1325 / 2626 | 12 / 22 | residual |
| 4 | gb | 63/63 | 4508 / 185 / 1026 / 1947 | 0 / 0 | CLEAN |
| 5 | slow | 63/63 | 4793 / 691 / 1994 / 3164 | 0 / 0 | CLEAN |
| 5 | fast | 63/63 | 2117 / 281 / 854 / 1310 | 0 / 0 | CLEAN |
| 5 | indep | 50/63 | 2697 / 2 / 376 / 446 | 13 / 21 | residual |
| 5 | gb | 63/63 | 3725 / 254 / 1294 / 2281 | 0 / 1 | residual (A-events7's Back `uenv1`) |

11 CLEAN rows now rest on SatPin, constants/reset, H_ARB, SelOK, SelPart only (Events8: plus HDsub).
The residual rows are margin failures exactly as in Events8, not HDsub (every dsub line is
accepted on every row).

**xevents8 comparison** (`events9/cmp8.sh`: cert8.py + Events8Main via `lean --run`, same
inputs): all 16 outputs are BYTE-IDENTICAL to the committed `events8/xe8_*.txt`. Diffing each
xe9 output against its xe8 output (after renaming the tool prefix) gives exactly 4 changed
lines per row, all wording: the hypothesis-judgement line, the guarded-pins label, the
RESIDUAL header (`design_verdict9`) and the VERDICT line (HDsub dropped). Every item,
margin and residual is the same.

**Negative controls** (`events9/neg9.sh`, seed d slow; each mutates `urig.udut.umux3.uxa.u`
pin 0's BACK-G `dsub` line; outputs `xe9_d_slow_<tag>.txt`):

| control | mutation | expected (from the rule) | result |
|---|---|---|---|
| NEGwsEnd | `wS` := the guard's LINE line `iX` (not an unlabelled S → D walk) | that pin residual | 125/126 valid wS, 1 no judgement; only umux3.uxa pin0 residual; RESIDUAL 1 |
| NEGwsTok | `wS` := new log lines (refl D; 3 × r1) = a VALID walk S → D with 2 tokens (BFS on the cert's nodes with `Net4.off`) | rejected only by `t ≤ 1` | same: only that pin residual; RESIDUAL 1 |
| NEGwsMissing | `wS` field removed | that pin residual | same; RESIDUAL 1 |
| NEGnows | `cert9.py --no-ws` | all 63 guarded pins residual | 0/126 valid, 63 guard residual; RESIDUAL 63 |
| POSws1 | positive control: same construction as NEGwsTok with 1 token | ACCEPTED | 126/126 valid; CLEAN |

POSws1 shows the appended-walk machinery is accepted by runLog and WSOK, so NEGwsTok's
rejection is the token bound and nothing else.

**xevents9 on the E8Mux corrected bands** (OUTMUX hop on O5/MUXF/CARRY4 exits; E8Mux's
`w/<seed>/new/` skeletons and bands, each band file passed `e8mux/checkbands.py`; run as
`TAG=_new run9.sh`, outputs `xe9_<seed>_<corner>_new.txt`, table `table9_new.txt`). Every row:
126/126 dsub lines with a valid wS, log accepted. Each output differs from E8Mux's
`e8mux/results/xe_<seed>_new_<corner>.txt` (xevents8, same bands) in exactly the same 4 wording
lines, so every item, margin and residual equals A-e8mux's NEW table:

| seed | corner | guarded certified | min BACK-G / ENTRY / EXIT1 / EXIT2 (ps) | residual guard / all | verdict |
|---|---|---|---|---|---|
| d | slow | 63/63 | 5655 / 532 / 3014 / 4916 | 0 / 0 | CLEAN |
| d | fast | 63/63 | 2772 / 247 / 1284 / 2087 | 0 / 0 | CLEAN |
| d | indep | 51/63 | 2121 / 60 / 755 / 1284 | 12 / 21 | residual |
| d | gb | 61/63 | 4258 / 41 / 2077 / 3736 | 2 / 2 | residual |
| 3 | slow | 63/63 | 5300 / 422 / 1515 / 3470 | 0 / 0 | CLEAN |
| 3 | fast | 63/63 | 2402 / 184 / 617 / 1448 | 0 / 0 | CLEAN |
| 3 | indep | 46/63 | 1822 / 451 / 1742 / 5283 | 17 / 30 | residual |
| 3 | gb | 63/63 | 4145 / 88 / 832 / 2482 | 0 / 0 | CLEAN |
| 4 | slow | 63/63 | 5911 / 802 / 1877 / 3156 | 0 / 0 | CLEAN |
| 4 | fast | 63/63 | 2613 / 355 / 798 / 1330 | 0 / 0 | CLEAN |
| 4 | indep | 54/63 | 2037 / 36 / 63 / 407 | 9 / 19 | residual |
| 4 | gb | 63/63 | 4560 / 185 / 1297 / 2287 | 0 / 0 | CLEAN |
| 5 | slow | 63/63 | 5121 / 802 / 2322 / 3820 | 0 / 0 | CLEAN |
| 5 | fast | 63/63 | 2249 / 343 / 986 / 1574 | 0 / 0 | CLEAN |
| 5 | indep | 50/63 | 2697 / 64 / 508 / 710 | 13 / 22 | residual |
| 5 | gb | 63/63 | 3997 / 283 / 1567 / 2827 | 0 / 1 | residual |

Same 11 CLEAN rows as on the old bands; d gb is RESIDUAL 2 (was 3). (H-variant bands not rerun.)

## Next

HDsub is closed. What a CLEAN row still assumes is H_ARB, SelOK, SelPart (probe E8Hyp) and
the trusted parser/mapping. The indep residuals are real margin failures under the independent
corner model; the d gb guard residuals (2 on corrected bands) are ENTRY margins.
