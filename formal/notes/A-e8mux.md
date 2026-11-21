# A-e8mux (probe E8Mux, shard A): OUTMUX hop on O5/F7/F8 arcs, Events8 rerun

STATUS: done (tasks 1-4). No Lean file written or claimed; results are reruns of the unchanged Events8 checker on corrected bands.

Progress log:
- toolchain restored from origin/toolchain-cache/d7ce266cff0c8e1e (git cat-file, no fetch) into
  ~/dev2/lib/fpgatoolchain; cells/verify/toolchain.sh exit 0, 9/9 ok, nextpnr sha256 9c732bc6303458df.
  apt libs were already present; pip installed intervaltree + simplejson (prjxray imports).
- source: `git archive 520a43f` -> ~/e8src (no worktree); builds one nextpnr at a time
  (scratch e8mux/build4.sh). Seed d: SDF a9c4e265 AND routed.json b398103e = events5/builds.txt
  (both match; fasm_audit PASS; bitstream step fails on missing textx, not needed).
  Seeds 3/4/5 likewise: all 8 md5s (SDF and routed.json) equal events5/builds.txt.
- seed d, old calculator (99b10a6d) -> routed2x: net.json 5c0830d5 (= builds.txt) and band files
  identical to the committed ones key for key on slow / indep / gb; on fast exactly the 20 known
  lo > hi arcs differ (now the hull, A-kapres's data quirk).
- seed d, new calculator (e8mux/xray_delay_e8mux.py): changes 10534 O5-driven, 2459 MUXF7/F8-driven,
  298 CARRY4-driven and 264 FF(x5FF)-driven IC rows; 0 O6-driven rows. The 236 unchanged O5 rows are
  all O5 -> CARRY4 DI inside the slice (no OUTMUX). Shift at SLOW_MAX: O5 +202..+231 ps,
  MUXF +173..+195. new == research 7dc5dde (3e69bf6a) on all 40083 comb->comb IC rows.
  Seeds 3/4/5: the same (old = committed bands key for key except the 7 / 8 / 2 lo > hi fast arcs;
  nets 1d655434 / 8da9f6cf / 1537cb0a = builds.txt; 0 O6 rows changed; new == r7 on 40083 rows).
- xevents8 overlay built (e8mux/mkolean.sh, 26 modules, 0 errors). Reproduction: old bands, seed d
  gb -> results/xe_d_old_gb.txt is byte-identical to events8/xe8_d_gb.txt.

## Verdict

**The audit row is confirmed: of Events8's three d-gb ENTRY failures, two are real (under this
delay model) and one, `ucontrol_merge3.uarb1.ua1`, was an input artefact.**

The cause is the band builder: xray_delay 99b10a6d charges the slice OUTMUX only on O6 and COUT
exits. Adding prjxray's ROUTING_BEL hop for every other xMUX exit (O5, MUXF7/F8, CARRY4 O/CO, x5FF)
and rerunning xevents8 gives these d-gb results:
- merge3.uarb1.ua2 ENTRY −51 (unchanged);
- merge2.uarb1.ua2 −68 (unchanged);
- merge3.uarb1.ua1 certified (ENTRY ≥ 41; untrusted Python cross-check +39, auditor's own model +45).

The verdict changes on no other row. The slow/fast CLEAN rows stay CLEAN, with minimum margins
equal or larger. Some indep Line margins get worse (by 60-80 ps).

**What this rests on.** The rerun uses the same Lean checker (Events8, unchanged) on corrected
inputs. Nothing new is proved in Lean here. The claims are about which delay bands go into the
existing theorem `design_verdict8`.

**Assumed:**
- prjxray-db's ROUTING_BEL numbers are the right hop for an O5/MUXF exit;
- the `x5lut` entry, not `o5`, is the one that applies (the hull sensitivity, row set H below,
  covers both).

**Not covered:** everything A-events8 lists as not covered (HDsub, H_ARB, SelOK/SelPart, the delay
model itself).

## Old vs new (xevents8, strict margins, ps)

OLD = committed `events8/xe8_*.txt` (99b10a6d bands). NEW = `e8mux/results/xe_<s>_new_<c>.txt`.
Verdict text as printed.

| seed | corner | OLD: certified, min BACK-G / ENTRY / EXIT1 / EXIT2, residual guard / all, verdict | NEW: same |
|---|---|---|---|
| d | slow | 63/63 | 5655 / 415 / 2665 / 4218 | 0 / 0 | CLEAN | 63/63 | 5655 / 532 / 3014 / 4916 | 0 / 0 | CLEAN |
| d | fast | 63/63 | 2637 / 204 / 1144 / 1807 | 0 / 0 | CLEAN | 63/63 | 2772 / 247 / 1284 / 2087 | 0 / 0 | CLEAN |
| d | indep | 51/63 | 2121 / 1 / 615 / 1004 | 12 / 21 | RECOGNISED, RESIDUAL 21 | 51/63 | 2121 / 60 / 755 / 1284 | 12 / 21 | RECOGNISED, RESIDUAL 21 |
| d | gb | 60/63 | 4258 / 80 / 1788 / 3158 | 3 / 3 | RECOGNISED, RESIDUAL 3 | 61/63 | 4258 / 41 / 2077 / 3736 | 2 / 2 | RECOGNISED, RESIDUAL 2 |
| 3 | slow | 63/63 | 5300 / 422 / 1171 / 2782 | 0 / 0 | CLEAN | 63/63 | 5300 / 422 / 1515 / 3470 | 0 / 0 | CLEAN |
| 3 | fast | 63/63 | 2402 / 184 / 482 / 1178 | 0 / 0 | CLEAN | 63/63 | 2402 / 184 / 617 / 1448 | 0 / 0 | CLEAN |
| 3 | indep | 46/63 | 1822 / 451 / 1742 / 5283 | 17 / 30 | RECOGNISED, RESIDUAL 30 | 46/63 | 1822 / 451 / 1742 / 5283 | 17 / 30 | RECOGNISED, RESIDUAL 30 |
| 3 | gb | 63/63 | 4145 / 88 / 548 / 1914 | 0 / 0 | CLEAN | 63/63 | 4145 / 88 / 832 / 2482 | 0 / 0 | CLEAN |
| 4 | slow | 63/63 | 5586 / 802 / 1548 / 2700 | 0 / 0 | CLEAN | 63/63 | 5911 / 802 / 1877 / 3156 | 0 / 0 | CLEAN |
| 4 | fast | 63/63 | 2481 / 355 / 667 / 1146 | 0 / 0 | CLEAN | 63/63 | 2613 / 355 / 798 / 1330 | 0 / 0 | CLEAN |
| 4 | indep | 51/63 | 2037 / 25 / 1325 / 2626 | 12 / 22 | RECOGNISED, RESIDUAL 22 | 54/63 | 2037 / 36 / 63 / 407 | 9 / 19 | RECOGNISED, RESIDUAL 19 |
| 4 | gb | 63/63 | 4508 / 185 / 1026 / 1947 | 0 / 0 | CLEAN | 63/63 | 4560 / 185 / 1297 / 2287 | 0 / 0 | CLEAN |
| 5 | slow | 63/63 | 4793 / 691 / 1994 / 3164 | 0 / 0 | CLEAN | 63/63 | 5121 / 802 / 2322 / 3820 | 0 / 0 | CLEAN |
| 5 | fast | 63/63 | 2117 / 281 / 854 / 1310 | 0 / 0 | CLEAN | 63/63 | 2249 / 343 / 986 / 1574 | 0 / 0 | CLEAN |
| 5 | indep | 50/63 | 2697 / 2 / 376 / 446 | 13 / 21 | RECOGNISED, RESIDUAL 21 | 50/63 | 2697 / 64 / 508 / 710 | 13 / 22 | RECOGNISED, RESIDUAL 22 |
| 5 | gb | 63/63 | 3725 / 254 / 1294 / 2281 | 0 / 1 | RECOGNISED, RESIDUAL 1 | 63/63 | 3997 / 283 / 1567 / 2827 | 0 / 1 | RECOGNISED, RESIDUAL 1 |

Changes beyond d gb:
- **indep:** guard residuals per seed are d 12→12, 3 17→17, 4 12→**9**, 5 13→13. merge10.ua1,
  merge12.ua1 and merge9.ua1 of seed 4 now certify.
- **Non-guard residuals** are identical old vs new on all 12 slow/fast/gb rows. On indep they move:
  - the arbiter-grant Line items and the `ulink_n_index_97` / `merge12_f` Line items get 4-78 ps worse;
  - seed 4: Back merge10.ua1 improves from −246 to −180;
  - seed 5: the Back merge12_f pin0 −29 disappears, and two Line items at −40 appear (`ulink_n_index_97`
    stage0 and `merge12_f` pin0), so seed 5 indep goes from 21 to 22 residuals.
  - The fix adds delay on both sides of a race, so it is not uniformly favourable. Full lists are in
    `results/table.txt`.
- **Minimum margins.** The min EXIT1 on certified pins drops at 4 indep (1325 → 63) only because
  newly certified pins enter the minimum.

## Hull sensitivity (H): agreement with Formal/Core/Prims/Hops.lean (probe PrimsComb)

prjxray-db has two names for each OUTMUX input from a LUT: `x5lut`/`o5` and `x6lut`/`o6`, and the
fuzzer does not record which name is the LUT output. PrimsComb's `outMuxHull` takes the hull of
each pair.

**Same data.** The band builder reads `$TC/openxc7/share/nextpnr/prjxray-db/zynq7/timings/slicel.sdf`
and `slicem.sdf`. Their sha256 values (fd31d660…, 3d2da571…) are the ones in XrayData.lean's header.
All 118 `outMux`/`outMuxL` arms of XrayData.lean agree with this copy to the ps. No disagreement.

**What NEW uses.** NEW takes `x5lut` only, as research 7dc5dde does. Its O6 hop is the tile
pseudo-pip, which equals `x6lut`.

**Variant H** is `xray_delay_e8mux.py --rb-o5 hull`. It takes the hull for O5 (x5lut ∪ o5) and for
O6 (pseudo-pip ∪ o6):
- On every slow/fast/indep band file it only lowers lo: by 16-26 ps (slow) and 3-10 ps (fast).
  hi is unchanged, since `x?lut` has the larger MAX.
- The gb band files are identical to NEW. gb lo is 0.668·SLOW_MAX, and SLOW_MAX is unchanged.
  So the gb verdicts are the same: **d gb RESIDUAL 2**.

Results under H (`results/xe_<s>_hull_<c>.txt`):
- all slow/fast rows are CLEAN;
- indep: d 22 (+ Back `umux15.uj1` pin1 −12), 3 31 (+ Back `ulink_n_trueResult_28` stage0 pin0 −17),
  4 19, 5 22.

**If Lean and the bands must agree on the hull, use H.** The conclusion on the audit row is the
same either way.

## Negative controls (`neg.sh`, outputs `results/xe_d_new_*_NEG*.txt`, summary `results/neg.txt`)

| control | mutation | expected | got |
|---|---|---|---|
| NEGmux | d gb NEW, only arc `ugrant$LUT5 -> merge3.uarb1.ua1/I4` reset to its OLD band [289,433] (new [424,635]) | merge3.ua1 fails ENTRY again | 3 guard residuals, merge3.ua1 ENTRY **−94** (= OLD) |
| NEGentry | +5000 ps on `umux3.uxa.u/I0` (d slow NEW) | umux3.uxa pin0 ENTRY fails | ENTRY −239, 1 residual |
| NEGexit | +18000 on hi of `umux3.uxa.u/I2` | EXIT2 fails | EXIT2 −399 |
| NEGlabel | iU replaced by the S→D walk line | pin rejected | 1 guard residual |
| NEGnoguard | cert8 --no-guard | 63 residual | 63/63 residual |
| NEGinv | one arc set to lo = hi + 1 | run.sh refuses before xevents8 | "band file REJECTED" |

What NEGmux shows: the d-gb change from 3 to 2 failures comes from that single O5 arc, and the
reversion reproduces the Events8 number exactly.

Band-reader controls:
- `routed2x.py` on the OLD fast arcs without `--inverted hull` exits 1 on the first lo > hi row;
- `checkbands.py` on the committed `gcd/inputs/bands_d_fast` flags its 20 lo > hi arcs.

## lo > hi bands (task 1, second half)

- **`routed2x.py`:** a prjxray row with lo > hi is now REJECTED (exit 1) by default.
  - `--inverted hull` takes [min, max] and lists the row in the report. That is 17 rows for seed d
    fast; on the committed band files it was 20 / 7 / 8 / 2 arcs for seeds d / 3 / 4 / 5.
  - Any emitted band with lo > hi is a hard error.
  - These are only fast-corner rows (prjxray FAST_MIN > FAST_MAX). slow/indep/gb have none.
- **`e8mux/checkbands.py`:** rejects any band file with lo > hi or lo < 0. `run.sh` runs it before
  every xevents8 call.
- **NOT done (not my file):** the Lean reader `Formal/Core/XAudit/Parse.lean` `toSteps` still maps
  lo > hi to [lo, lo]. The lead should make `toSteps` or `bandFor` throw on `b.1 > b.2`, so the
  checker itself refuses. Until then the Python gates above are the only guard.
- All NEW/H fast bands are hulls, so the fast rows also differ from OLD on those arcs (≤ 61 ps
  widening). Fast verdicts are unchanged.

## Files (formal/tools-A/xaudit/)

- **`e8mux/xray_delay_e8mux.py`** is research 801db02 xray_delay.py (99b10a6d) plus the OUTMUX hop
  (ROUTING_BEL) for O5 / MUXF7/F8 / CARRY4 / x5FF exits. It has `--rb-o5 hull`. An unknown xOUTMUX
  source is a hard error.
  - The default-mode output was re-checked after the hull edit: arcs md5 91ec269e, identical.
- **`routed2x.py`:** the `--inverted` option, the lo > hi rejection, and report lines.
- **`e8mux/` scripts:**
  - `bands.sh`: routed → arcs → nets/bands/skeletons, variants old/new/r7/hull;
  - `run.sh`: cert8 + xevents8 per row;
  - `xe.sh`, `mkolean.sh`: the olean overlay of Events8Main's 26 modules not yet in lake's build;
  - `neg.sh`, `table.sh`;
  - `cmparcs.py`, `cmpbands.py`, `checkbands.py`, `entry_check.py` (untrusted Python ENTRY
    cross-check).
- **`e8mux/results/`:**
  - `xe_*` (16 NEW, 12 H, 1 OLD reproduction, 5 NEG) and `cert_*`;
  - `table.txt`, `neg.txt`, `hull_summary.txt`;
  - `bands_*.txt` (arc/net md5s), `builds_md5.txt`.
- Large files are NOT in the repo. They are routes, arcs TSVs and bands in the scratchpad
  `…/scratchpad/e8mux/{route,w}`, and the source in `~/e8src` (`git archive 520a43f`).
  - routed.json and SDF md5s equal events5/builds.txt, so a rebuild reproduces them.
  - arcs TSV md5s (old/new/r7/hull): d a3dd1178/91ec269e/d4eb3b6b/c1bf4f6d; 3 cf4df767/b572cda0/36dc5525/841d20fa;
    4 cbedb44e/fd5790b6/13c58250/e7e9f4fe; 5 b40c423b/7160dfbe/69131c79/410d7060.

## Open / for the lead

- **Parse.toSteps lo > hi:** make it a hard error (see above).
- **Re-derive the other committed band consumers** on corrected bands: events5–7, events9, kapres,
  k2 (k2 already used 7dc5dde), and A-xaudit-gcd. They all read 99b10a6d bands. Expect:
  - the same kind of shifts;
  - d gb's ENTRY residual count to drop by one wherever ENTRY is checked;
  - indep Line margins a little worse.
- **Optionally commit the NEW/H band files as .xz inputs** (about 1 MB per seed and corner) so later
  probes do not need the toolchain.

## Plan
1. Band pipeline: routed JSON + SDF -> research xray_delay.py 99b10a6d (arcs TSV) -> routed2x.py
   (net.json + bands) -> events4/skel.py -> events8/cert8.py -> xevents8. 99b10a6d charges the
   slice OUTMUX only from O6 (tile pseudo-pip X->>XMUX) and COUT; O5 / F7 / F8 / CARRY4 O,CO
   through xOUTMUX are charged 0. Fix in tools-A/xaudit/e8mux/ (copy of 99b10a6d + ROUTING_BEL
   hop for every other xOUTMUX source), cross-checked against research 7dc5dde (3e69bf6a).
2. Routed data is not on disk: restore toolchain (A-k2 procedure), rebuild gcd_hw R5 d/3/4/5,
   check SDF md5 against events5/builds.txt.
3. Rebuild bands, rerun xevents8 on 16 rows + negative controls, old vs new table.
4. Correct A-events8.md (line 74, ENTRY table).
