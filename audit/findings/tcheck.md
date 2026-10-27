# Audit: formal C-10g "Phase 2 tcheck rules A/E/F/J on 4 gcd_hw routes" (claude/formal 1e7947a)

I am an auditor subagent. I wrote every number below with my own scripts in `audit/tc/`. I did not run the formal shard's `extract.py`, `tcheck`, `sitepin.py` or `compare2.py`. Their result tables are copied unchanged into `audit/tc/theirs/` so that the comparisons can be rerun.

The rule scripts under test (`verify/skew.py`, `tighten.py` and `arb_fork.py` at research 19a93c1) are used only for what they define: the rule's graph, its sites, its launches and its walk. My delay model supplies every arc weight.

## 0. Which routes, and what I rebuilt

The commit message says "4 gcd_hw routes". These are the four C-10e routes: gcd_hw built with the BQ#1 recipe (`BDC_SELECT_PADS=hw/gcd_hw_pads.json BD_RLOC=v4`, fusion on, no sizes). Each has a different nextpnr seed: default (d), 2, 3 and 4.

| C-10g seed | their sdf sha256 | my build | BOARD-QUEUE |
|---|---|---|---|
| d | b238cc1a... | `/home/user/wt-rb1` (already rebuilt; sdf md5 6f8b99e6, sha256 b238cc1a): **identical** | **BQ#1, the boarded route** |
| 2 | a7e78067... | rebuilt in scratch from `git archive 19a93c1`, `NEXTPNR_SEED=2`: **identical** | a BQ#1 sibling seed (evidence only, not boarded) |
| 3 | b6613fcb... | rebuilt the same way: **identical** | sibling seed |
| 4 | 8186915d... | rebuilt the same way: **identical** | sibling seed |
| - | not analysed by C-10g | `/home/user/wt-bq23` (sdf md5 a9c4e265) | **BQ#2** (R5 sizes) |
| - | not analysed by C-10g | `/home/user/wt-bq23b` (sdf md5 61e14755) | **BQ#3** (R5 + link fast fall) |

C-10g did not look at BQ#2 or BQ#3 at all. I ran every check on them as well.

## 1. My delay model (`audit/tc/xrc.py`) and how I validated it

**What it computes.** For each routed net, xrc.py takes the ROUTING tree from `gcd_hw_routed.json`. It merges nextpnr wires into prjxray nodes, using tileconn.json from `$PRJXRAY_DB_DIR/zynq7/xc7z010`. It then computes the RC tree with the semantics of `prjxray/timing.py`:
- the output pin's R plus its intrinsic delay;
- wire pi models, where each node's RC is the sum over its tile wires;
- buffered and pass-transistor pips, with their src_to_dst intrinsic delay, R and in_cap; bidirectional long-line pips use dst_to_src;
- the input site pin's intrinsic delay.

All four corners come out as `[FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX]`.

**Physical pins.** The physical LUT pin is the CLB tile wire that feeds the site (for example, `CLBLM_M_C4` is pin C4). Checked over 47,710 arcs on BQ#1, the cell's port index equals that physical index in every case. nextpnr's SITEWIRE name is the permuted BEL pin, not the physical pin.

**Cell arcs.**
- LUT: the prjxray LUT6/LUT5 IOPATH of the physical pin.
- MUXF7/F8: the cell arcs, the select site pins (AX/CX/BX) and the in-site LUT→F7 hop.
- Anything not modelled keeps its SDF number. For consistent-corner runs it is instead scaled by the median model/SDF ratio of resolved arcs (`XRC_FBSCALE`). What remains unmodelled is about 12k arcs per route, almost all of them constant (VCC/GND) nets and rig flip-flops. On every failing row I list, the critical path has 0 such arcs unless I say so.

**The OUTMUX delay.** When a net leaves its slice through AMUX..DMUX, the model adds the prjxray ROUTING_BEL delay (`b6lut→bmux` and so on). That delay is 53-77 ps at FAST_MIN and 172-224 ps at SLOW_MAX.

**Validation against the claim's own numbers:**
- **Rule J.** I set `XRC_NOMUX=1`, which drops the OUTMUX term. My Jx fast/slow numbers then equal C-10g's tc_fast/tc_slow on **70 of 70 clients within 15 ps (mean +2 ps)** (`cmpj.out`).
- **Site pins.** My site-pin table then reproduces `results/sitepin_d.tsv`: A1 +487 against their +490, A3 +314 against +314, and so on (`sitepin_d.out`).
- **RT_FB.** My DUT minimum on seed d is fast/slow/fastG/slowG = 254/532/26/21 at `ucontrol_merge10.uarb1.ua2.u`, against their 252/530/23/19. These are LUT-only nets, so no OUTMUX term is involved.

So I reproduce their corner model to the picosecond. I also found one systematic difference between it and prjxray:

> **Finding M (new): C-10g's prjxray model omits the OUTMUX (?MUX routing-BEL) intrinsic delay.** On BQ#1, 18,446 of 40k LUT-input arcs leave the source slice through a ?MUX output. On those arcs the C-10g numbers are about 170-220 ps low at SLOW_MAX and 53-77 ps low at FAST_MIN. This moves individual race margins in either direction:
> - It is optimistic when the late side leaves through a MUX output. Example: seed 4 `merge12.uarb2#2`, J rows below.
> - It is pessimistic when the early side does. Example: seed d `merge6.uarb1#1`.

**Corner names used below:**
- **fast** and **slow**: one prjxray corner. The side that must be early gets that corner's MIN and the side that must be late gets its MAX. This is C-10g's `fast`/`slow`, H_ONE_CORNER.
- **fastG** and **slowG**: the same values with the project band, 0.772×early-side minus 1.155×late-side. This is C-10g's fastG/slowG, "the project's band", the skew.py/arb_fork GUARD_LO/GUARD_HI.
- **mix**: FAST_MIN on the side that must win the race and SLOW_MAX on the side that must lose it ("fast-early/slow-late"). No die is at both corners, so this is a box bound, not a physical corner.

Where a shared prefix exists, it is credited exactly: each side is measured from the branch point of the RC tree (J), or from the divergence node of the two measured paths (E, skew.py's own credit).

## 2. Verdict table

| # | Claim (1e7947a) | Verdict | Evidence |
|---|---|---|---|
| 1 | Their 4 routes | **IDENTIFIED** | Seeds d/2/3/4 of the BQ#1 recipe. My rebuilds give identical SDFs. Seed d **is** BQ#1's board route. BQ#2 and BQ#3 were not analysed by C-10g. |
| 2 | "with SDF numbers tcheck reproduces rule margins to the ps (E 471/472 ...)" | **CONFIRMED for E** (my reimplementation: 471/472 SDF raw margins equal skew.py's, `cmpe.py`). J: my SDF raw/guarded equal arb_fork's on all 72 clients. A/F: not separately re-proved; my corner runs use tighten.py itself. | `rulee_*.tsv` sdf_raw; `rulej_x.tsv` sdf_raw/sdf_guard |
| 3 | "every disagreement is rule-pass/tcheck-fail, from site pins ... or the weaker project guard" | **CONFIRMED in direction; OVERSTATED as a list of real problems** | Every disagreeing row I recomputed passes at **both consistent corners without the band**, with one exception: none on their 4 routes. The band (0.772/1.155) layered on prjxray corner bounds is what makes them fail. Their mechanism attributions are right except where Finding M changes the row (J d merge6#1, J 4 merge12.uarb2#2, E 3 umux4.uj1, RT_FB). |
| 4 | "A 172/200 (all 28 from SDF-fallback arcs)" | **CONFIRMED (artefact)** | With MUXF7/F8 modelled (`tighten_corners2_d.tsv`, `_4`), all 6 BQ#1 rows (ushli0, ushrsi0-4) and all 7 seed-4 rows pass fastG and slowG: BQ#1 min fastG +470 (ushrsi2), slowG +2377. The failures came from fallback arcs that keep the slow-ish SDF number inside the fast corner. Seeds 2 and 3 were not rerun through tighten. |
| 5 | "E 465/472" (7 credited E rows fail) | **CONFIRMED as band-only, with row-level corrections** | **d umux13.uj0** (BQ#1, udut): mine fast/slow +225/+538, fastG/slowG **-190/-412** (theirs -105/-201; mine is worse). **4 umux1.uj1**: +230/+533, -118/-245 (confirmed). **2 umux4.uj0, 3 umux4.uj0/uj1, 4 umux8.uj0/uj1**: with skew's own measured-path credit these pass the band in my model (+638..+1201 fastG). With no credit (E0) they are -353/-548 (2 umux4.uj0) and +13..+126 (others). The verdict depends on which credit is applied. No E row fails at a consistent corner without the band: min +225 fast / +533 slow over 472 rows. |
| 6 | "F 113/116" | **CONFIRMED as band-only** | **4 merge12.udly**: mine fast/slow +305/+667, fastG/slowG -212/-497 (theirs +317/+697, -176/-399). **d ucmpi8.udly** (BQ#1): with the MUXF arcs modelled, this is no longer a fallback row and still fails the band: +947/+2337 unbanded, **-487/-454** banded. Their "fallback, front-end gap" explanation for this row is therefore **REFUTED**: it is a guard-versus-band row like merge12. Seed 3 merge12 was not rerun. |
| 7 | "J 67/70" (3 Jx rows fail) | **PARTLY REFUTED** | **d merge6.uarb1#1** (BQ#1), theirs -10/-8: mine **+107/+266 PASS**. Artefact: the early side leaves through BMUX and the OUTMUX term was omitted. **2 merge12.uarb1#1**, theirs -35/-86: mine **+22/+49 PASS** (thin). **4 merge12.uarb2#2**, theirs -9/+39: mine **-111/-201 FAIL**, worse, because A0 reaches ua2 via DMUX. Unbanded, all 72 Jx rows on the 4 routes pass: min +144 fast, +385 slow (seed 4). |
| 8 | "H 630/632" | **CONFIRMED (band-only)** | **d ulink_n_falseResult_55 stage[1]** (BQ#1): mine fast/slow +187/+495, fastG/slowG **-24/-6** (theirs 138/373/-28/-19). Seed 2 ulink_n143 was not rerun. |
| 9 | "I 300/300" | **CONFIRMED on d and 4** | I passes fastG and slowG on d (min +162/+391) and on 4. It fails the band on BQ#2/#3 (section 4). |
| 10 | "SDF low by up to +490 ps on A1" | **OVERSTATED / misworded** | +490 is the **mean** of SLOW_MAX-SDF on A1, not a maximum: p10 387, p90 651, max 2071 in their model. With OUTMUX the mean is **+596** (p90 763, max 2280; nets through ?MUX alone: +683). At FAST_MIN the SDF is **high**, not low, by 210-590 ps mean. So "SDF low" is true only at the slow corner. |
| 11 | "J's pip estimate over-credits ~95 ps avg (max 211)" | **REPRODUCED in their model; OVERSTATED in prjxray** | With `XRC_NOMUX`: seed 2 mean 95 / max 211, seed 3 95 / 162, seed 4 89 / 137, seed d 106 / 148 (16 rows, excluding merge9 as they did). Exact match. With OUTMUX the over-credit is **33-68 ps mean (max 96-162)**, and the pip estimate **under**-credits on 1-4 clients per route, down to -353 ps (seed d merge9, which they could not resolve). "Permissive on 69/70" holds only in the OUTMUX-free model. |
| 12 | "RT_FB fails thinly at the env C-element urig.uenv1.u on 2 seeds (band only)" | **CONFIRMED, and worse** | Seed 2: mine fast/slow **+46/+164**, fastG/slowG **-114/-219** (theirs 139/375/-7/25). Seed 4: **+99/+197**, **-81/-201** (theirs 114/234/-37/-95). The feedback net to A1 leaves through a MUX output (OUTMUX plus the A1 site pin), 903-922 ps at SLOW_MAX against 295 in the SDF. Band-only: unbanded positive. This is in the **test rig (uenv1)**, not the kernel. DUT minimum is +26/+21 banded (seed d), reproduced. |

## 3. The disagreeing rows, one by one

Columns are fast / slow / fastG / slowG (mix). Location is udut (the kernel) or uenv (the rig).

**J (Jx, exact branch-point credit), `rulej_x.tsv`, `cmpj.out`**
- **d merge6.uarb1#1** (BQ#1, udut):
  - mine 372/887/**107/266** (mix -252);
  - theirs 224/536/-10/-8.
  - Verdict: artefact (Finding M).
- **2 merge12.uarb1#1** (sibling seed, udut):
  - mine 224/526/22/49 (mix -313);
  - theirs 155/355/-35/-86.
  - Verdict: thin pass in my model.
- **4 merge12.uarb2#2** (sibling seed, udut):
  - mine 144/385/**-111/-201** (mix -577);
  - theirs 235/594/-9/39.
  - Verdict: a real band failure, larger than claimed. The consistent corners pass.

**E, `rulee_full_*.tsv` / `rulee_fbs_*.tsv`, `cmpe.py`**

All seven credited rows plus E0. Every one passes unbanded at both corners.
- **d umux13.uj0** (BQ#1, udut): 225/538/**-190/-412**, same with no credit.
- d umux13.uj1, a new thin row from Finding M: 402/941/-18/-26.
- d umux19.uj1: E0 1619/3415/-74/-295. The verdict depends on the dominator credit, which C-10g grants and skew's credit does not.
- 4 umux1.uj1: 230/533/-118/-245.
- 2 umux4.uj0, 3 umux4.uj0/uj1 and 4 umux8.uj0/uj1: pass with skew's measured-path credit. E0 for 2 umux4.uj0 is -353/-548.

**F, `tighten_corners2_*.tsv`**
- **d ucmpi8.udly** (BQ#1, udut): 947/2337/**-487/-454**.
- 4 merge12.udly: 305/667/-212/-497.

**H**
- **d falseResult_55 stage[1]** (BQ#1, udut): 187/495/**-24/-6**.

**A (28 rows)**
- The 6 BQ#1 rows and the 7 seed-4 rows all pass fastG and slowG once MUXF7/F8 is modelled: BQ#1 ushrsi2 is 3075/8804/470/2892.
- Under mix they go to -1002..-2664, but mix is non-physical on 8-10 ns LUT-chain paths: it charges a ~2.5× corner span to one side.

**RT_FB, `rtfb_*.tsv`**
- uenv1.u seed 2: 46/164/**-114/-219**.
- uenv1.u seed 4: 99/197/**-81/-201**.
- uenv1.u on BQ#1 (d): +1083/+2011/+784/+1439.

## 4. BOARD-QUEUE routes: is there a real negative margin?

**Under a consistent corner without the band** (one prjxray corner; must-be-early side at that corner's MIN, must-be-late side at its MAX):

- **BQ#1 (d): no negative margin.** Minima over all rows of each rule:
  - E +225 fast (umux13.uj0);
  - J +301 (Jx; merge2.uarb1#1 fast);
  - A +2430;
  - F +811;
  - H +187 (falseResult_55 stage[1]);
  - I +1115;
  - RT_FB +254 (merge10.uarb1.ua2.u, udut).
- **BQ#2: no negative margin.** E +496, J +268, A +340 (umux4; ushli0 +410), F +516, H +377, I +494. RT_FB is +433 (udut).
- **BQ#3: one negative margin, rule A ushrsi1 (udut, a bundled shift cell) at the fast corner: -36 ps.**
  - At the fast corner, request at FAST_MIN = 5799 and data at FAST_MAX = 5835.
  - If every arc instead sits at the same extreme, it passes: all-FAST_MIN +762, all-FAST_MAX +1335.
  - tighten.py's **own** guard fails it on the all-FAST_MIN SDF: -137, "PAD to 23 -- VIOLATION". Request 5799, peak 5037, guard 899.
  - The slow corner passes (+2235).
  - Every arc in ushrsi1's cone is modelled, including MUXF7/F8 (`fbsurvey`-style check: 2 of about 3,300 arcs unmodelled).
  - The row also rests on rule A's H_BUNDLED_T0 assumption.
  - The SDF margin is +3100 raw / +1672 guarded. R5 thinned it from about 8000 on BQ#1. The request chain is LUT-dominated, and LUT arcs shrink to 0.36× at FAST_MIN while routing shrinks to about 0.6×, so the matched delay loses ground at the fast corner.
  - **I rate this a thin, model-dependent real risk, not a predicted failure.** It is the only negative unbanded consistent-corner margin I found on any board route.
  - Other BQ#3 minima: E +664, J +209, F +655, H +210, I +818. RT_FB +172 (uenv0.u, rig).

**With the project band on prjxray corners** (C-10g's fastG/slowG), the BQ routes do have negative margins:
- **BQ#1:**
  - E umux13.uj0 -190/-412 (and uj1 -18/-26, umux19.uj1 E0 -74/-295);
  - F ucmpi8.udly -487/-454;
  - H falseResult_55 -24/-6.
  - J and RT_FB do not fail on BQ#1.
- **BQ#2:**
  - A: 18 rows at fastG and 12 at slowG, down to -1570/-2412;
  - E: 14 ucond_br gates, down to -341/-244;
  - I: 3-4 rows, down to -38/-340;
  - J: merge9.uarb1#1 -6/-52.
- **BQ#3:**
  - A: 16/11 rows, down to -2263/-2721;
  - E: 14 ucond_br gates, down to -548/-360;
  - H: falseResult_55 -14/-17;
  - I: -14/-354;
  - J: merge2.uarb1#1 -20/-25;
  - RT_FB: rig uenv0.u -23/-31 and uenv1.u -2/-10.
- All of these are in udut except the RT_FB rows (uenv, the rig).

**Under fast-early/slow-late mixing** (FAST_MIN on the winning side, SLOW_MAX on the losing side, exact shared credit, no band), every route has negative rows:
- **BQ#1:**
  - J 7/18 clients, worst -252 (merge6.uarb1#1);
  - E 12/118, worst -2578;
  - H 5, worst -386;
  - RT_FB 6, worst -319 (udut merge10.uarb1.ua2.u).
- **BQ#2:** J 7/18, worst -472; E 61/118, worst -3639.
- **BQ#3:** J 7/18, worst -459; E 70/118, worst -3579; RT_FB 5, worst -340 (rig uenv0.u).

This is consistent with rules.md's -38..-260 for rule J on BQ#1. For E, A and F, mix is dominated by the fast/slow span on multi-ns LUT chains (0.36× against 1.0× per LUT arc), so on its own it is not evidence of a physical race.

## 5. Bottom line

**On the formal shard's claims:**
- The "proved checker on untrusted extraction" reproduces the rules' SDF arithmetic, and its prjxray corner model matches mine to the picosecond once I remove OUTMUX.
- That model omits the OUTMUX routing-bel delay of about 200 ps (Finding M). This flips 1 of their 3 J failures to pass (on the BQ#1 board route), makes the seed-4 J row and both RT_FB rows worse, and halves the J over-credit figure.
- All their failures are band-only, except that their F ucmpi8 "fallback" row is really a guard-versus-band row.

**On the board queue:**
- BQ#1 and BQ#2 have no negative margin at a consistent prjxray corner.
- BQ#3 has one: rule A ushrsi1 at -36 ps (fast corner, interval semantics; it also fails tighten's own guard on an all-fast SDF).
- All three BQ routes have several band-only negatives and many fast-early/slow-late negatives.

## 6. Files and commands (`audit/tc/`)

- `xrc.py`: the model (Route, Net, `route_arc`).
- `sitepin_cmp.py` → `sitepin_d.out`.
- `rulej_x.py` → `rulej_x.tsv`, and `XRC_NOMUX=1` → `rulej_x_nomux.tsv`; `cmpj.py` → `cmpj.out`.
- `rulee_x.py`:
  - (`runE.sh`: LUT-only, fallback = SDF) → `rulee_<seed>.tsv`;
  - (`runE2.sh`: `XRC_FBSCALE`) → `rulee_fbs_*`;
  - (`runE3.sh`: plus MUXF) → `rulee_full_*`;
  - `cmpe.py` compares them against theirs.
- `rtfb_x.py` (`runR.sh`) → `rtfb_<seed>.tsv`; `rsum.py` summarises them.
- `corner_sdf.py` writes single-valued corner SDFs to the scratchpad, not the repo. `runT.sh` runs tighten.py on them, using a scratch copy whose only change lists all F lines (`[:3]`→`[:999]`). `tparse.py` → `tighten_corners2_<seed>.tsv` (with MUXF) and `tighten_corners_*` (without); `tsum.py` summarises them.
- `skew_v_d.log` is skew.py -v on BQ#1, and `theirs/` holds C-10g's result tables.

Environment: `source ~/auditlogs/export_dev2.sh`. Rebuilt sibling seeds: `git archive 19a93c1` and `NEXTPNR_SEED=s BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw`, in the scratchpad.

## 7. Limitations

- **Elmore RC is the prjxray model.** Silicon is not.
- **Unmodelled arcs** are FF, CARRY4 and constant nets. They are either scaled or kept at the SDF number, and they are counted per row (`fb_arcs`).
- **RT_FB** uses LUT-only weights. Its request Dijkstra still uses SDF numbers on MUXF arcs.
- **E dominator credit** (C-10g's H_CLEAN_EDGE at the dominator X) was not reimplemented; I report skew's measured-path credit and no credit.
- **Not rerun:** F seed 3 merge12 and H seed 2 ulink_n143. The A/F/H/I rows for seeds 2 and 3 were not rerun through tighten.
- **H_BUNDLED_T0** underlies every bundled A row, including BQ#3 ushrsi1.
