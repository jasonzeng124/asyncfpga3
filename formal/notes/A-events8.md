# A-events8 (probe WE4g): GuardOK discharged into count facts; one new, narrower hypothesis (shard A)

## Verdict

**Partly done.** GuardOK, the value-level hypothesis of `Events7.design_verdict7`, is no longer
a hypothesis. The new top theorem `Events8.design_verdict8` replaces it by a Lean-checked guard
certificate per guarded pin (`guardOK8`: ENTRY, EXIT, LINE, BACK-G, all with STRICT margins).
Two of the certificate's judgements per pin cannot be derived with the Events7 log rules.
They are assumed, as a NAMED count-level hypothesis **HDsub**: 126 judgements on gcd_hw
(2 × 63 guarded pins).

**Hypotheses of a CLEAN row of `design_verdict8`:**
- per-pin `SatPin` (the netlist semantics), the constant wires and reset;
- H_ARB (`HARB7`);
- SelOK, SelPart;
- **HDsub**, which is new and replaces GuardOK.

GuardOK is gone. `design_guardOK8` proves the Events7 hypothesis `Beh7.GuardOK` itself for this
realisation, under the same hypotheses.

**Why HDsub and not a full discharge.** BACK-G and the EXIT guard bound are labelled walks that
start at the guarded source `D` (e.g. `ulink_n55` stage 0 for `umux3.uxa`). They enter the
guard's arm of the mux OR (`umux3.uor`) by SUB. The Events7 SUB rule is sound only for a walk
that starts at the label's source `S` (its proof uses `filt false (M S) + filt true (M S) = M S`).
- **From `D`:** the count inequalities give the bound only up to one extra token. The other arm
  can already be inside a later transaction of `S` that `D` has not reached; I checked this by
  hand on the arithmetic.
- **From `S`:** the same walks need one token more than the 1 (BACK-G) and 0 (EXIT) allowed.
- **What closing it needs:** a causality ("first time `S` reaches `2k+1`") argument. That is
  W-E4g's remaining day; see Open.

So HDsub is a precise, checkable residue. It is 2 count inequalities per pin,
`filt (M u D) ≤ M (u − dB) j + tB` and `filt (M u D) ≤ M (u − dG) Gs`. They are computed by the
Lean checker (`hconcl`, `.dsub`) from accepted log lines. They are not value-level statements.

**Per row** (`tools-A/xaudit/events8/table8.txt`; strict margins, ps; the minima are over the
certified guarded pins):

| seed | corner | guarded pins certified | min BACK-G / ENTRY / EXIT1 / EXIT2 | residual (guard / all) | verdict |
|---|---|---|---|---|---|
| d | slow | 63/63 | 5655 / 415 / 2665 / 4218 | 0 / 0 | CLEAN |
| d | fast | 63/63 | 2637 / 204 / 1144 / 1807 | 0 / 0 | CLEAN |
| d | indep | 51/63 | 2121 / 1 / 615 / 1004 | 12 / 21 | residual |
| d | gb | **60/63** | 4258 / 80 / 1788 / 3158 | 3 / 3 | residual |
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
| 5 | gb | 63/63 | 3725 / 254 / 1294 / 2281 | 0 / 1 | residual (A-events7's Back `uenv1`, −61) |

How to read the table:
- **GuardOK is discharged (modulo HDsub)** on every slow and fast row, all four seeds, and on
  gb for seeds 3, 4 and 5.
- **The non-guard residual items are byte-identical to A-events7's on all 16 rows** (`diff` of
  the RESIDUAL Back/Line/Excl lines).

**Timing findings (GuardOK fails; reported, not weakened):**
- **d gb: 3 pins fail ENTRY.** These are the arbiter re-arm items of A-events5/7. The ENTRY
  margins are:

  | pin | ENTRY margin |
  |---|---|
  | `ucontrol_merge3.uarb1.ua2` pin 0 | −51 ps |
  | `ucontrol_merge3.uarb1.ua1` pin 0 | −94 ps |
  | `ucontrol_merge2.uarb1.ua2` pin 0 | −68 ps |

  ana's ENTRY rule listed only two of them (−26 and −52). The Lean bands use `plo − 1`/`phi − 1`
  steps and strict margins.
- **indep (mixed corner): 12 / 17 / 12 / 13 uncertified pins (d / 3 / 4 / 5).**
  - ENTRY failures are 12 / 17 / 11 / 13, down to −1357 ps (d).
  - EXIT1 failures are 0 / 2 / 2 / 1, down to −704 ps (seed 3).
  - BACK-G and EXIT2 never fail.
  - The 6 guarded delay lines: ENTRY ≥ 4557 and EXIT1 ≥ 9304 at d slow (`xe8_d_slow.txt`).

## What is proved (Lean, all in `Formal/Core/XAudit/`, check below)

**`Events8Core.lean`:**
- `lineCnt` (the AND/OR line count) and **`gcnt`**, the guarded count `filt (sel grp) br (lineCnt …)`.
- **`beh8`**, a `Beh7` whose `gc` is the running maximum of `gcnt` of `M8`. `M8` is the counts with
  `gcnt` built in; it is a recursion in time, so there is no circularity.
- **`beh8_M`** (`beh8.M = M8`) and **`beh8_gc`** (`beh8.gc = gcnt (beh8.cm)`).
- `GuardCnt`: the count-level facts BOUND, CONTIG and LABEL.
- **`guard_val`**: under these facts the guarded pin reads its count.
- **`safe8`**: `Beh7.safe` with GuardOK replaced pin by pin. Certified pins use `GuardCnt`;
  uncertified pins use `GuardPin`, which is GuardOK for that one pin.
- **`guardOK_of_cnt`**: `GuardCnt` for all guarded pins gives `Beh7.GuardOK`.
- Negative controls:
  - `guard_label_neg`: without LABEL, the pin reads high while the count says low.
  - `guard_fmax_neg`: the `fmax`-based `guardCnt` of `Wip/Events7.lean` is wrong for a split AND
    line.

**`Events8Cert.lean`:**
- `GD`; `HLn` (`copy` / `dsub`), `hconcl`; **`HDsub`**.
- `GuardOK8` / `guardOK8`: decidable, strict margins.
- **`guardOK8_sound`**: accepted log + HDsub + `GuardOK8` give `GStruct ∧ GuardCnt`. The LABEL
  fact is proved by a two-case argument:
  - ENTRY case: the guard advanced into a later transaction of `S`, so `D ≥ 2k+2` at a time
    covered by every copy. This contradicts a copy reading `2k+1`.
  - EXIT case: `D` completed transaction `k−1` at least `W` before, so at the stage's own sample
    both pins (`ar j = 2`) are past the feedback. This contradicts `Mq` odd.
- **`verdict8`**.

**`Events8Beh.lean`:**
- **`design_beh8`**: every per-pin behaviour is a `beh8`.
- **`design_verdict8`**.
- **`design_guardOK8`**.

**`Events8Main.lean`:** the executable `xevents8`, a copy of `xevents7` plus the guard section.

### Plain language: `design_verdict8`

**Assumed:**
- `Recog6` and `Net4.OK7`;
- an accepted log, and the certified items' Bool checks, including `guardOK8`;
- SatPin, the constants, reset, H_ARB;
- SelPart, SelOK, **HDsub**;
- for every item NOT certified, its obligation. For a guarded pin that is GuardOK for that pin only.

**Proved:** every real LUT wire equals `ph (v j) (M t j)` at every time. Here `M` is the count of a
fixed realisation whose guarded count is `gcnt`.

**NOT covered:**
- HDsub, open as above;
- SelOK/SelPart (bundling) and H_ARB (arbiter, metastability);
- the trusted reader and printing in `Events8Main`;
- `skel.py`;
- the analog/delay model.

**Structural restriction.** A certified guarded pin's stage has exactly two pins, the guard
being plain with offset 0. This is checked by `GuardOK8`; all 63 gcd guarded pins have that form.

### Check

Mathlib was built, but lake's build had no Events4–7 oleans, so the dependencies are listed.
From `formal/lean`:

    ../check.sh Formal/Core/XAudit/Events2PinDesign.lean Formal/Core/XAudit/Events4.lean \
      Formal/Core/XAudit/Events5Line.lean Formal/Core/XAudit/Events5.lean Formal/Core/XAudit/Events6Gate.lean \
      Formal/Core/XAudit/Events6Cert.lean Formal/Core/XAudit/Events6Design.lean Formal/Core/XAudit/Events6Beh.lean \
      Formal/Core/XAudit/Events7Core.lean Formal/Core/XAudit/Events7Excl.lean Formal/Core/XAudit/Events7Cert.lean \
      Formal/Core/XAudit/Events7Beh.lean Formal/Core/XAudit/Events8Core.lean Formal/Core/XAudit/Events8Cert.lean \
      Formal/Core/XAudit/Events8Beh.lean Formal/Core/XAudit/Events8Main.lean

Result:
- the textual scan passes;
- `[audit] 2489 declarations checked`;
- executable `Events8Main`: `[audit] 2724 declarations checked`;
- **`[check] OK`**.

There is no sorry, admit, new axiom, native_decide or bv_decide in the Events8 files.

## Tools and runs (`formal/tools-A/xaudit/events8/`)

**`cert8.py`** (UNTRUSTED) is a copy of `events7/cert7.py` with these changes:
- guarded pins get the guard's label as `grp/br`;
- a `guards` map gives, per pin, `S`, `iU`, `iW`, `iX` (log lines) and `iB`, `iG` (hypothesis
  lines `hyp`);
- `--no-guard`;
- labelled walks from `D` through SUB go to `hyp` as `dsub`, never into the log.

The first attempt put them into the log, and the checker rejected the whole log at the first such
line. That is the finding above.

**Scripts:**
- `mk8.sh` builds the olean overlay `/tmp/events8/olean`, which symlinks `/tmp/events7/olean`.
- `xe8.sh` runs `lean --run`.
- `run8.sh` runs the 16 rows with at most 2 jobs.
  - Inputs are `events7/rerun/prep.sh`'s, in `/tmp/events6/out`.
  - 2 of 16 outputs came out EMPTY with 2 parallel jobs (the known phenomenon). Rerun with
    `JOBS=1`, they were complete.
- `neg8.sh`, `table8.sh`.
- The outputs are `xe8_*.txt`, `cert8_*.txt` and `table8.txt`.

**Negative controls (`neg8.sh`, seed d slow).** Each must be rejected, and is:

| control | mutation | result |
|---|---|---|
| NEGentry | +5000 ps on both bounds of `umux3.uxa.u/I0` (the delay line's LUT input) | only `umux3.uxa` pin 0 residual: ENTRY −239 |
| NEGexit | +18000 ps on the upper bound of `umux3.uxa.u/I2` (the guard pin) | only that pin residual: EXIT2 −399 |
| NEGlabel | `iU` of that pin replaced by its `S → D` walk line (wrong judgement kind) | that pin rejected |
| NEGnoguard | `cert8.py --no-guard` | 63/63 guarded pins residual |

Lean-level controls: `guard_label_neg`, `guard_fmax_neg`.

## Open

**HDsub.** Prove the two `dsub` judgement families from the log plus the ENTRY-style S/D
alignment, using the "first time `S` reaches `2k+1`" argument:
1. `S`'s rise in transaction `k` needs the merged acknowledge past `2k`.
2. The other arm is bounded by `filt ¬b (M S)` at times before that rise, which is at most
   `filt ¬b (2k)`.
3. So the guard's arm is at least `filt b (2k)`.

This needs a new log rule with a minimum-time witness. Estimate: about one day.

`Wip/Events7.lean`'s `guardOK_of_entry_exit` is superseded. As stated, it fixes the `fmax`-based
count, which is wrong for split AND lines (`guard_fmax_neg`). Its ENTRY/EXIT hypotheses are
`True` placeholders.

## For the lead

**Lakefile stanza:**

```toml
[[lean_exe]]
name = "xevents8"
root = "Formal.Core.XAudit.Events8Main"
```

**Root imports, if wanted:** `Formal.Core.XAudit.Events8Core`, `…Events8Cert`, `…Events8Beh`.
Not `Events8Main`, which defines `main`.

**Effort:** about 4.5 h.
