# ev8: formal shard A, Events8 (eb346fb), read at formal head 6863284 (~/wt-f7)

Auditor subagent, 2026-10-29. Scripts and small outputs: `audit/ev8/`. Large files: `~/ev8work` (md5s at the end).
No git command was run. No tracked file outside `audit/` was written.

| commit | claim (quoted) | verdict | evidence | note |
|---|---|---|---|---|
| eb346fb | "gcd_hw CLEAN at slow/fast on all 4 seeds" (A-events8 table: d/3/4/5 slow and fast, 63/63 guarded pins, residual 0) | **CONFIRMED (timing sample only; "CLEAN" is conditional)** | **Routes.** I rebuilt all 4 seeds. The SDF md5s equal events5/builds.txt: d a9c4e265, 3 e0d4202b, 4 b1b4b951, 5 030c36bd.<br>**Own ENTRY computation** (`entry.py`: prjxray RC with xrc.py, OUTMUX charged, prjxray LV-node convention), per-pin, on the 16 arbiter guard pins per seed:<br>- slow min: d 530, 3 419, 4 849, 5 800 ps;<br>- fast min: d 245, 3 181, 4 367, 5 345 ps;<br>- 0 pins ≤ 0.<br>**Formal min ENTRY** (all 63 pins): slow 415/422/802/691, fast 204/184/355/281. Mine is within 3 ps of these or larger.<br>**Input check.** All 21,596 O6-driven LUT→LUT arcs in the formal seed-d bands equal mine within 2 ps. All 10,223 O5-driven arcs do not (next rows). With those arcs corrected, the committed ana5 still gives slow/fast 402/405 on all 4 seeds, with the same 3 structural cascade stages and no new failure (`ana5corr/`). Every margin is the same or larger. | Not re-derived:<br>- Back, line, merge, BACK-G and EXIT items, except through the ana5 rerun;<br>- the Lean run of xevents8;<br>- HDsub, H_ARB, SelOK and SelPart, which a CLEAN row assumes (stated in the note). |
| eb346fb | "gb seed d fails ENTRY on 3 arbiter guard pins (−51/−94/−68 ps)": merge3.uarb1.ua2 −51, merge3.uarb1.ua1 −94, merge2.uarb1.ua2 −68 | **OVERSTATED (2 of 3 reproduced; the −94 pin is an input artefact)** | Own per-pin gb margins, gb = [0.668·SLOW_MAX, SLOW_MAX], from `entry_d_lv2.out`:<br>- **merge3.ua2: −49** (claim −51), FAIL reproduced;<br>- **merge2.ua2: −64** (claim −68), FAIL reproduced. If every tile wire of an LV node is charged instead of the prjxray worksheet's 2, it is −141;<br>- **merge3.ua1: +45, PASS** (claim −94).<br>**Why ua1 differs.** Its guard ugrant$LUT5 is an **O5** output, so it must leave the slice through AMUX. The formal bands (xray_delay.py 99b10a6d) omit the prjxray ROUTING_BEL a5lut→AMUX delay: [62, 78, 163, 202] ps for FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX. The arc is formal [289, 433] against mine [425, 635] at gb. This delay is on the EARLY (guard) side, so the formal result is pessimistic here.<br>With the formal bands and my formula I get −54/−96 for this pin, so the claim follows from its inputs. The correction alone turns it positive. | The omission is **systematic**: all 10,223 O5-driven LUT arcs in the formal bands are low by 202–231 ps at SLOW_MAX (`arcsall_d_slow_lv2.out`). The current research xray_delay.py (3e69bf6a) does charge x5lut→xMUX. On gb with the correction, ana5 gives 2 ENTRY failures, not 3 (`ana5corr_d_gb.txt`). |
| eb346fb (not explained in A-events8) | change from Events5 d gb ENTRY −52 (merge3.ua1) / −26 (merge2.ua2) / −9 (merge3.ua2) to Events8 −94 / −68 / −51 | **EXPLAINED: the model changed, not the inputs** | **Inputs are identical.** Events8's run8.sh takes events7/rerun/prep.sh's inputs. Those are the same xz files Events5 used: net_d.json md5 5c0830d5 and bands_d_gb.json.xz f21fa308. Rerunning the committed ana5 reproduces `ana5_d_gb.txt` exactly.<br>**Every pin moves by exactly −42 ps.** That is the gb LUT band width of the arbiter LUT, [82, 124], so 124 − 82. Events5's ana5 is atomic (H_ATOMIC_LUT: ua's own LUT delay cancels). Since A-events6, the Lean checker gives each LUT pin its own warp in the cell band, so the late pin takes hi = 124 and the guard pin lo = 82.<br>**My formula reproduces this.** Atomic minus per-pin is 41–42 ps at gb, 24 at slow and 11 at fast on every pin. On the formal bands it gives −54/−28/−11 (atomic) and −96/−70/−53 (per-pin). The formal values are 2 ps higher throughout (a rounding convention), with no sign change. | A-events6 §3 documents the per-pin effect, but only for Back items. A-events7 still quotes the gb ENTRY minimum as "−52". **A-events8's sentence "ana's ENTRY rule listed only two of them (−26 and −52)" is wrong**: `events5/ana5_d_gb.txt` lines 6–8 list all three (−26, −52, −9). |
| A-events5 provenance (inputs of Events8) | routes = gcd_hw R5 at research 520a43f (same as cbe4a52), BOARD-QUEUE #2 command, no --freq | **CONFIRMED for the SDF; commit differs** | I built at **73b08ca** (cp -a of ~/wt-r8), not 520a43f. The formal notes record no source md5s, only output md5s, so I could not compare source files with 520a43f.<br>- wt-r7 (4051359) and wt-r8 differ only under cells/gls; gcd_hw_sizes_R5.vh is 04039011 in both.<br>- Toolchain: ~/audit-tc, nextpnr sha256 9c732bc6303458df, 9/9 patch fingerprints ok.<br>- All 4 SDFs are identical to the recorded ones. | The routed.json md5s differ: d d4a432fd against b398103e. This matches the earlier bq23 finding: the JSON carries toolchain src paths. Normalising the path did not make it match; the cause is UNVERIFIED. The O6 arcs agree to ≤ 2 ps, so the routing is the same. |
| eb346fb | "GuardOK replaced by Lean-checked guard certificates on all 63 guarded pins plus a narrower count hypothesis HDsub" | **UNVERIFIED** | I did not re-check the Lean in this task. I only read xe8_*.txt: 63/63 certified on slow/fast rows, "126 judgements" HDsub. | Out of scope for this subagent. |

## Details

**ENTRY rule** (events4/ana.py and Events8 guardOK8). For arbiter `ua_b = C(grant_b, A0)`:

    margin = lo(A0→ustate) + F(ustate) + lo(ustate→ugrant) + F(ugrant) + lo(ugrant→ua) − hi(A0→ua)

The per-pin version subtracts ua's own LUT band width. The condition is that the A0 transition reaches ua
before the grant reacts to ustate having consumed that same A0 event.

**Model sensitivities** (seed d gb, per-pin; `entry_d*.out`):

| pin | formal bands, my formula | xrc LV-full + OUTMUX | xrc LV-2 + OUTMUX (= prjxray worksheet) | xrc LV-2, no OUTMUX |
|---|---|---|---|---|
| merge3.uarb1.ua2 | −53 | −49 | **−49** | +21 |
| merge2.uarb1.ua2 | −70 | −141 | **−64** | −64 |
| merge3.uarb1.ua1 | −96 | +45 | **+45** | −20 |

The no-OUTMUX column also drops the DMUX hop of A0 (merge3_f leaves through DMUX), which the formal bands do
charge. That is why merge3 rows change sign there.
- The formal bands charge O6→xMUX but not x5LUT→xMUX.
- merge2 is sensitive to the LV long-line RC convention. My xrc sums all 14 LVB tile wires; prjxray's worksheet
  and xray_delay.py charge 2. The difference is +233 ps on both of A0's arcs, and it does not cancel in a band.
- The bold column is my best estimate.

**Seeds 3/4/5 gb** (own, per-pin): min ENTRY on arbiter pins 91 / 189 / 286 ps, 0 failures. This agrees with the
claim that only seed d fails ENTRY at gb.

## Files
- `audit/ev8/entry.py`: own ENTRY calculator. Flags: `--lv2` (prjxray LV convention), `--nomux`.
- `audit/ev8/cmpbands.py`: formal bands against my arcs, per race arc, plus ENTRY from the formal bands.
- `audit/ev8/arcsall.py`: all LUT→LUT arcs.
- `audit/ev8/corrband.py`: formal bands with the O5 arcs replaced by mine.
- `audit/ev8/ana5corr/`: the committed ana5 run on the corrected bands. This is their tool, used as a consumer.
- Build logs: `audit/ev8/build_{d,3,4,5}.log`.

**Large files in `~/ev8work` (md5):**

| file | md5 |
|---|---|
| route/d/gcd_hw.sdf | a9c4e26566621e10399440c2d9a43af3 |
| route/d/gcd_hw_routed.json | d4a432fd8f3836a5a8458272a0a4d218 |
| route/3/gcd_hw.sdf | e0d4202b490ba60147b3a8ae982f7d51 |
| route/3/gcd_hw_routed.json | a10b2e2415b569622b225afb3364ada2 |
| route/4/gcd_hw.sdf | b1b4b951a9fca9e7433a7f1ccb51377d |
| route/4/gcd_hw_routed.json | 4a1ff2f6fdde754cc55e852dcaea794b |
| route/5/gcd_hw.sdf | 030c36bdec2da685cd9788ad06e865e8 |
| route/5/gcd_hw_routed.json | d1f0e89df1e15203fcb5e778e49130d9 |
| corr/d/{slow,fast,gb}.bands.json | 07cd11cf / d926a8f9 / ca6cafb0 |
| corr/3/{slow,fast,gb}.bands.json | f42522ec / 1bdf9945 / 5875a7c3 |
| corr/4/{slow,fast,gb}.bands.json | b99f15af / bcb91dec / 31c6e672 |
| corr/5/{slow,fast,gb}.bands.json | 1754fbef / 5e0ebb51 / ab70f938 |
| formal inputs, decompressed (net_d.json) | 5c0830d5, = events5/builds.txt |
