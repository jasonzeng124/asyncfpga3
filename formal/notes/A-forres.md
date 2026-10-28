# A-forres: FOR-RESEARCH.md rewritten (shard A, phase 3; probe ForRes, 2026-10-28)

## What was done
`formal/out/FOR-RESEARCH.md` was replaced as a whole: 15 numbered sections. Each gives the
finding, the evidence (file:line in the research tip, or a Lean theorem), the change, and a
test command. No Lean was written or run; this probe made no proof claims.

Inputs read:
- the previous FOR-RESEARCH (git log -p, last edit 6763571);
- the last ~150 lines of JOURNAL.md, JOURNAL-B.md and JOURNAL-C.md;
- the notes: C-10n-kernels, A-kapres, A-kapres2 (WIP), A-gls-compare-2, A-gls-pass,
  B-constraints-kappa, B-gcd-arb-kappa;
- the audit REPORT rows on research (origin/claude/audit);
- `git log origin/claude/research` (tip 350f9be, last code change da38b8d), plus
  tighten.py, prims.v, build.sh, fid_core.vh, bd_arb.v, emit.py, xray_delay.py,
  toolchain.sh and bd_prims_sim.v at that tip, read with `git show` only.

## Verification done for this file (beyond reading notes)
- **CornerCode, ConstraintsKappa, OnGcdArbKappa, GLSPass, SAF, LutAudit:** grepped that every
  theorem cited exists in the tree. Their check status comes from the commits (6763571;
  861de85, B under Mathlib; GLSPass 11:22). I did not re-run them.
- **C-10n:**
  - `tools/kcheck/results/constsrc.tsv` confirms ipow s3 umuli1 17715 → 14226, and the
    overstatement range of 0.9-4.2 ns.
  - At the research tip, `tighten.py:674-697` `cell_boundary` has no `is_const` test, while
    `starts_reaching` has one. So C-10n is **not fixed** on research.
- **Rule-A guard and upstream_lag:** `tighten.py:1705-1712` adds the lag after the guard is
  computed. This is still true at the tip. Whether the guard should use the post-lag delay is
  still unverified.
- **Inverted FAST tuples (A-kapres):**
  - I scanned the local `prjxray-db/zynq7/tile_type_BRKH_INT.json`: 28 inverted entries
    (14 pips × 2 directions), `[0.202, 0.105, 0.231, 0.312]`.
  - `xray_delay.py` sums the columns per element and writes `(FAST_MIN:SLOW_MIN:SLOW_MAX)` to
    its SDF. So the research GLS fast-min corner is too slow by up to 97 ps per crossing on
    those arcs. This is my inference from the code, not a measurement.
  - The source trace is from A-kapres2, which is a WIP note (RESULTS_VERDICT placeholder,
    CornerCell.lean not in the tree). It is cited as WIP.
- **GLS (A-gls-compare-2):**
  - The research `prims.v` and `fid_core.vh` are unchanged since 5d535d7 (md5 equal to
    `tools-A/glsdiff/src/`).
  - I re-ran `tb_carry_saf.v` and `tb_seq_x.v` (iverilog 12, default and fid): O0 at 1223
    only, LQ at 3100 only, L1-L3 = x, F1/F2 = 1. Every §8 claim of the old file reproduced.
  - I did not re-run the FID_RESOLVE sweep.
- **B's split bug:** JOURNAL-B 11:50 and 12:00. C-10m's fix is not committed on claude/formal
  (no C-10m note, nothing in JOURNAL-C).
- **Audit:**
  - Row 11/34: "rise/fall differ 2.2×" REFUTED. It is fixed on research by 5d535d7; the
    audit's re-check is PENDING (row 60).
  - Row 12: annotated vs baked OVERSTATED. Still unfixed: `prims.v:47` and `build.sh:104-106`
    still claim identical timestamps.

## What changed relative to the previous FOR-RESEARCH, and why

**New items:**
- §1, rule A times constant tie-off nets (C-10n).
- §4, inverted prjxray FAST tuples and xray_delay.py (A-kapres, A-kapres2).
- §5, which rules tcheck replaces and the table of front-end gaps. This includes B's
  `extract.Prjx.split` bug, the DSP and CARRY4-CIN fallbacks, the rule-I first-stage
  coverage hole (audit row 46), and rule J's per-pin gap. It replaces the old placeholder
  "rules A/E/F/H/I/J will be filled in from shard C's verified checker".
- The §3 κ table, from B's kappa results: box and SLOW-only checks are unsound; the gcd_hw
  arbiters are safe for κ ≤ 0.0443 (0.0802 with the server credited; the cons reading fails
  at κ = 0); link_arb is safe at 1/11; uenv1 fails at about 0.08 (KapRes); rule A as coded is
  sound up to 25/276; rule E up to 0.199.
- §9, what a GLS pass implies (GLSPass): paired FAST_MIN/SLOW_MAX runs, and the
  annotated ≠ baked wording.

**Merged:**
- old 5 + 6c + part of 9 → §3;
- old 1 + 8 (CARRY4/latch) → §6;
- old 8 X handling → §7;
- old 8 FID_RESOLVE and scatter → §8;
- old 6b + 6c + 6c' → §11, updated to the Events8 seed-d guard-pin numbers (JOURNAL 12:38)
  and the K2 collatz uenv1 −9 ps;
- old 6e → §5.

**Status changes:**
- §6 and §10 are PARTLY FIXED: GLS_MODEL=fid has transport LUT/MUXF (5567170). The default
  build and CARRY4/latch are still SAF.
- §15 lists the research fixes:
  - SDF triples: e239db7, 801db02, 5d535d7;
  - rule F in-flight term: 7a8199b. Reading the code, it covers the bd_delay_gated head hop
    of old 6c'. It has not been re-run on routes, so the item is marked "re-check".
  - OUTMUX in xray_delay: 7dc5dde.

**Dropped:**
- The old §3 mux-tree order item: no GLS effect, confirmed by the audit. One line in §15.
- The old §4 SDF-triples item: fixed, now in §15.

## What this does NOT cover
- No new proofs. Every "proved" refers to existing, committed Lean, and I did not re-check
  it here.
- The §2 upstream_lag point, the §4 "GLS fast corner too slow" consequence, and the §15
  claim that rule F covers the head hop are code readings. None was run.
- The research branch may have moved after 350f9be. Re-check §15 before acting.

## Files written
- `formal/out/FOR-RESEARCH.md` (complete replacement)
- `formal/notes/A-forres.md` (this file)

## For the lead
- Nothing to add to the lakefile or the imports.
- When C-10m lands, update the split-bug row in FOR-RESEARCH §5. When A-kapres2 is claimed
  (CornerCell.lean, band reader rejecting lo > hi), drop "WIP" from §4.
- FEASIBILITY.md may want one row for the tie-off false path (§1) and one for the inverted
  prjxray tuples (§4). I did not edit FEASIBILITY.md.

## Suggested next probe
Re-run tighten rule F (7a8199b) and rule A with the §1 fix on rebuilt gcd_hw R5 seeds d/3 and
ipow seed 3. That closes the two "re-check" items in §1 and §15 with measurements instead of
code readings.
