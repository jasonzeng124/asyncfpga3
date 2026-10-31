# C-10f2: RT_FB with the driver-side OUTMUX (xMUX) hop

Shard C, probe 10f2 (track 10), 2026-10-29. About 3 h wall time (mostly waiting on a machine at
load ~22).

## Verdict

**C-10f's gcd_hw headline does not survive as stated. The audit row (P4) is right.**

- **gcd_hw.** With the hop, "0 failures in every one-corner model" is FALSE on seed 4.
  - Variant `fast` (FAST_MIN..FAST_MAX, RC in [0, E]): the rig's `urig.uenv1.u` (bd_c2n_set) fails
    by **−16 ps**. C-10f had +4; the audit predicted about −13.
  - slow, fastE and slowE still have 0 failures on all 4 seeds.
  - **The kernel (every C-element except the rig's uenv0/uenv1) has 0 failures in every one-corner
    variant on all 4 seeds.** Its worst is fast +70 and slowE +530, both on seed d and unchanged.
- **Rig.** The uenv ring now **fails on seed 4** in `fast`: a violating fixed-delay run exists in
  that model (kernel-checked).
  - It is thinner on seed 4 in the other variants too: slow +51, fastE +94, slowE +161
    (C-10f: +124, +114, +234).
  - On seed 2 it is fast +14 and slowE +162 (C-10f: +109 and +375).
- **Muller pipeline (64 stages, 8 seeds).** The race is still real on every seed at slowE, but it
  is smaller.
  - slowE: 1 to 8 of 64 fail (mean 3.9; C-10f: 4 to 12, mean 7.2). The worst slack is −4 to −218.
  - Reason: the hop also delays the RESPONSE, because the responding neighbour's output usually
    leaves through its own xMUX pin.
- **Same routes as C-10f.** All 12 routes were rebuilt FASM-byte-identical to C-10f's.
  RTFB_NO_HOP reproduces every C-10f count and worst slack exactly, so the hop alone causes every
  change above.

## The model change

`formal/tools/rtfb/rtfb_design.py`, `route_elems`: a route whose source is a LUT output leaving the
slice through AMUX..DMUX (FASM `<site>.<L>OUTMUX.O6` or `.O5`) now begins with that ROUTING_BEL
hop. The numbers come from prjxray-db `timings/slicel.sdf` / `slicem.sdf`, written
(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX) in ns. These are CORNERS, not rise/fall.

| hop | SLICEL xMUX | SLICEL xMUXL | SLICEM xMUX | SLICEM xMUXL |
|---|---|---|---|---|
| a6lut->amux | (0.071::0.088)(0.168::0.209) | (0.072::0.089)(0.194::0.241) | (0.071::0.088)(0.166::0.206) | (0.075::0.093)(0.171::0.213) |
| a5lut->amux | (0.062::0.078)(0.163::0.202) | (0.064::0.08)(0.185::0.229) | (0.066::0.082)(0.164::0.204) | (0.07::0.087)(0.174::0.216) |
| c6lut->cmux | (0.069::0.086)(0.166::0.205) | (0.072::0.089)(0.193::0.239) | (0.07::0.087)(0.166::0.205) | (0.075::0.093)(0.171::0.212) |

The b and d hops (5 and 6) all lie in 0.067-0.077 :: 0.084-0.095 (fast) and 0.168-0.186 ::
0.208-0.231 (slow).

- **Hull.** Which of the xMUX / xMUXL instances times a given site is not decoded. The verdict uses
  their HULL (H_OUTMUX_HULL), the same choice tcheck's extract.py has made since C-10h.
  Sensitivity runs use `RTFB_OUTMUX=amux|amuxl`.
- **Where the hop is charged.** It applies to the feedback, to the response's first net, and to the
  output of every responding LUT (O6 or O5 → xMUX). It sits before the first pip, outside the
  Elmore term.
- **Direct outputs.** A direct A..D output (a6lut → A) is a wire, 0 in prjxray, and gets no element.
- **The O5 case.** A C-element is the O6 of its LUT6, and 72 / 59 / 62 / 60 of the 363 gcd
  C-elements (seeds 4 / d / 2 / 3) have their feedback through an xMUX. O5 hops occur only on
  responding LUTs. `drv_hop` handles them: out = O5 gives `x5lut -> xmux`.
- **Whose code.** `drv_hop` / `outmux_table` were first drafted by the lost C-10m session (WIP
  snapshot 1553efe). C-10f2 checked, relabelled and documented them.

### Concrete example: seed 4, `urig.uenv1.u` (SLICE_X19Y77.CLUT), variant `fast`

Launch is uenv1's O6 edge at t = 0. The full run is in `build/gcd/uenv1_s4_fast.txt`.

- **Feedback**, every element at its max: c6lut->cmux 89, IMUX33 47, RC 62, site pin C1 215.
  It arrives at **413 ps**.
- **Response**, every element at its min: c6lut->cmux 69, IMUX41 38, RC 0, D1 174, uenv0's LUT
  A1→O6 45, IMUX30 38, RC 0, C5 33. It arrives at **397 ps**.
- The violation is **16 ps**.

The shared hop is what tips it:
- The hop is ONE physical element shared by both routes (uenv1's CMUX pin). The window model
  (per-element independence inside the corner) takes it at its max on one branch and its min on
  the other. That costs hi − lo = 20 ps under the hull.
- With one instance's numbers the cost is 17 ps: c6lut->cmux FAST is 69::86 for xMUX and 72::89
  for xMUXL, so the slack is **−13 ps** either way. The failure does not depend on the decode.
- With the shared hop at one exact value, the slack would be +4 ps, C-10f's number. That needs
  shared-element semantics, which the Lean model (`WinArrayB`: per-arc windows on a tree whose
  branches share only the launch) does not have.
- So the precise statement is: uenv1 fails RT_FB in the per-element `fast` model, the same model in
  which C-10f claimed 0 failures. It is not "fails on silicon".

## Results

### gcd_hw, 4 seeds, 363 C-elements each, with the hop

Routes come from `route_gcd.sh` (C-10e's recipe, no --freq), seeds d, 2, 3, 4. Each is
FASM-identical to C-10f's: b73e1ba0e4cba92f, 1ee50d56638ef0b3, 855635c4ebed15e5, b56d32b1eecdaed9.

Failing count / worst slack in ps (kernel-checked `gcdS_pass`, `gcdS_worst`):

| seed | in Lean | indep | fast | slow | fastE | slowE | worst element |
|---|---|---|---|---|---|---|---|
| d | 12 | 12 / −503 | 0 / +70 | 0 / +348 | 0 / +252 | 0 / +530 | ucontrol_merge10.uarb1.ua2 (kernel) |
| 2 | 10 | 10 / −498 | 0 / **+14** | 0 / +132 | 0 / +44 | 0 / +162 | rig uenv1 |
| 3 | 6 | 6 / −282 | 0 / +248 | 0 / +659 | 0 / +484 | 0 / +895 | rig uenv1 |
| 4 | 10 | 10 / −559 | **1 / −16** | 0 / +51 | 0 / +94 | 0 / +161 | rig uenv1 |

C-10f's numbers on the same routes without the hop, which RTFB_NO_HOP reproduces exactly here
(seed 4: `build/gcd/s4/rtd0.txt`), fast / slowE:

| seed | fast | slowE |
|---|---|---|
| d | +70 | +530 |
| 2 | +109 | +375 |
| 3 | +248 | +895 |
| 4 | **+4** | +234 |

**Kernel only** (all C-elements except urig.uenv0/uenv1), from `rtd.json`, failing / worst:

| seed | indep | fast | slow | fastE | slowE |
|---|---|---|---|---|---|
| d | 12 / −503 | 0 / +70 | 0 / +348 | 0 / +252 | 0 / +530 |
| 2 | 9 / −303 | 0 / +210 | 0 / +631 | 0 / +317 | 0 / +738 |
| 3 | 5 / −282 | 0 / +264 | 0 / +942 | 0 / +616 | 0 / +1294 |
| 4 | 9 / −202 | 0 / +341 | 0 / +990 | 0 / +516 | 0 / +1211 |

- **Rig only** (uenv1), fast / slow / fastE / slowE:
  - seed 2: +14 / +132 / +44 / +162;
  - seed 3: +248 / +659 / +484 / +895;
  - seed 4: −16 / +51 / +94 / +161.
  - On seed d, uenv1 has no response inside the bound (H_CONE).
- **Independent cross-check.** C-10h's tcheck numbers for uenv1 include this hop and come from a
  different extractor (tcheck extract.py). They are seed 2 "fast +44, slow +162" and seed 4
  "fast +94, slow +161". They equal fastE / slowE here exactly; tcheck's fast/slow use H_RC_EXACT.
- **Common corner (Python evidence):** see the section below.

### Muller pipeline, 8 seeds, with the hop

Routes come from `route_muller.sh` (`--freq 100 --seed s`). The FASM sha prefixes are identical to
C-10f's table, and the seed-1 read-back is byte-identical to 10d's fixture.

Failing C-elements of 64 (kernel-checked `m64sN_pass`; worst slack in `m64sN_worst`):

| seed | indep | fast | slow | fastE | slowE | sdf | C-10f slowE |
|---|---|---|---|---|---|---|---|
| 1 | 38 | 18 | 14 | 0 | 3 | 1 | 12 |
| 2 | 40 | 9 | 7 | 2 | 2 | 0 | 5 |
| 3 | 36 | 13 | 11 | 3 | 7 | 0 | 11 |
| 4 | 36 | 9 | 6 | 0 | 1 | 0 | 5 |
| 5 | 34 | 9 | 5 | 4 | 5 | 0 | 4 |
| 6 | 41 | 12 | 4 | 3 | 3 | 0 | 4 |
| 7 | 36 | 15 | 7 | 0 | 2 | 0 | 7 |
| 8 | 39 | 14 | 12 | 5 | 8 | 0 | 10 |
| **mean [range]** | 37.5 [34..41] | 12.4 [9..18] | 8.2 [4..14] | 2.1 [0..5] | 3.9 [1..8] | 0.1 [0..1] | 7.2 [4..12] |

Worst slack in ps, mean [range]:

| indep | fast | slow | fastE | slowE | sdf |
|---|---|---|---|---|---|
| −710 [−747..−666] | −102 [−144..−65] | −163 [−279..−76] | −29 [−104..+6] | −87 [−218..−4] | +96 [−7..+206] |

- **Range theorem.** `m64_seeds_slowE_range`: 56 to 63 of the 64 pass at slowE on every seed.
- **Worst stage.** Seed 8 `st[12]` (SLICE_X40Y99.CLUT), slowE −218. The run is in
  `build/muller/worst_s8_slowE.txt`:
  - feedback through CMUX: hop 239, IMUX 138, RC 34, C1 517 → 928 ps;
  - response from c[13] over direct pins: D4 229, LUT 100, C5 92 → 710 ps.
- **Sensitivity** (`build/muller/outmux_sensitivity.txt`), slowE failures per seed:

  | hop numbers | seeds 1..8 |
  |---|---|
  | xMUX only | 1, 1, 5, 0, 4, 1, 0, 5 |
  | xMUXL only | 1, 2, 4, 0, 5, 2, 0, 6 |
  | hull | 3, 2, 7, 1, 5, 3, 2, 8 |

  The race is real on 6 of 8 seeds under either decode, and on 8 of 8 under the hull.
- **Pins** (slowE, hull). The failing stages have the feedback on pin 1 (19), pin 2 (10) or pin 3
  (2), never on pins 4-6, as in C-10f.
- **Common corner** (every element at one end; Python evidence, `build/muller/point_summary.txt`):
  - seed 5 has 1 failing stage (−7 / −17 / −15 / −30 at Fmin / Fmax / Smin / Smax);
  - seed 8 has 2-3 failing stages (worst −68 at Smax);
  - the other 6 seeds pass;
  - C-10f had 5 of 8 seeds failing, seed 3 at −112; seed 3 now passes (+15..+34);
  - the points use hull end values.

### Common corner, gcd_hw seeds 2 and 4

Every element is put at the same end of its range (Fmin / Fmax / Smin / Smax, RC = E, hull
ends). This is Python evidence, from `build/gcd/s{2,4}/point.txt` and `build/gcd/point_summary.txt`.

| seed | failing (of 363) | uenv1 slack at Fmin / Fmax / Smin / Smax (ps) |
|---|---|---|
| 2 | 0 | +115 / +143 / +329 / +405 |
| 4 | 0 | +167 / +196 / +360 / +431 |

Seed 4's `fast` failure therefore exists only when elements are mixed within the corner: the shared
CMUX hop at its max on the feedback and its min on the response, together with RC at 0 on the
response. Under full correlation the rig has at least +167 ps.

## What is proved (kernel `decide +kernel`; no sorry, axiom or native_decide)

All of C-10f's theorem names are kept. Their numbers change; some theorems are new.

**`RtFbGcd`** (data `RtFbGcdS{d,2,3,4}`, regenerated). For each seed S:
- `gcdS_len`, `gcdS_pass`, `gcdS_worst`: new numbers.
- `gcdS_wf`, `gcdS_sep`: same statements.
- `gcdS_slowE_safe`, `gcdS_fastE_safe`: same statements, still true on all 4 seeds.
- `gcdS_indep_violated`.
- **New:**
  - `gcdS_wf1`, `gcdS_sep1`: side conditions for the fast/slow variants.
  - `gcdS_{fast,slow,fastE,slowE}_exact`: in that variant, the passing entries hold RT_FB in every
    run and the failing entries have a real violating fixed-delay run.
  - **`gcd4_pass` (fast: 9 of 10 pass) together with `gcd4_fast_exact`** is the kernel-checked
    "uenv1 violates RT_FB on seed 4 in the `fast` model".

**`RtFbMuller`** (data `RtFbM64S1..8`, all regenerated by rtfb_design.py `--lean-all`):
- **Seed 1.** Its data is now `RtFbM64S1` (a new file). 10d's `RoutedMuller64S1` has no hop and is
  untouched.
- **Per seed N:** `m64sN_pass` and `m64sN_worst` (new numbers), `m64sN_wf`, `m64sN_sep`,
  `m64sN_slowE`.
- **`m64_seeds_slowE_range`**: the bounds changed from 52..60 to 56..63.
- **New:** `m64sN_len` (64 entries).
- **Semantics change, a weakening.** Each Muller entry is now rtfb_design's whole-environment tree,
  not rt_all.py's one-hop DAG.
  - Stages with no response path inside the H_INDEP bound have an EMPTY response list:
    26, 24, 28, 28, 30, 23, 28, 25 of the 64 on seeds 1..8.
  - In Lean they pass trivially. Their real safety rests on H_CONE (Python, cross-checked by the
    unpruned Dijkstra: 0 disagreements).
  - C-10f's Lean held every stage's one-hop DAG in full.
  - The failing stages are all in Lean with their full trees, so every failing count is exact. The
    passing counts are kernel facts only for the stages that are in the bound.

**`RtFbCore`**: unchanged.

## Hypotheses (named) and non-vacuity

- **H_ONE_CORNER, H_RC_EXACT, H_INDEP** (10d): as in C-10f.
  - Non-vacuity: the `*_exact` theorems give explicit FixedRuns for the failing entries.
  - The `wf` side conditions make every entry's windows well-formed.
- **H_OUTMUX_HULL** (new): each xMUX use's real hop delay lies in the hull of the prjxray xMUX and
  xMUXL intervals for its sitetype and corner.
  - It holds if the site is timed by one of the two instances.
  - Witness: the sensitivity runs. Neither instance changes a gcd sign; 6-8 Muller seeds still fail.
- **H_CONE, H_UNKNOWN_ROUTE, H_OPAQUE_CUT**: unchanged from C-10f, Python-checked.
  - The unpruned Dijkstra agrees with the tree on every C-element of every route and variant
    (0 disagreements).
- **Not modelled: the correlation of ONE shared hop element** used by both feedback and response.
  - Leaving it out is conservative for RT_FB.
  - It is exactly why seed 4 fails at −16 instead of passing at +4.

## What does NOT check / not done

- **No GLS or board evidence.** C-10f §4 still applies. A GLS gives the shared CMUX hop ONE delay
  (one SDF cell), so it would most likely NOT show seed 4's 16 ps: the failure lives in the
  per-element model.
- **The gcd common-corner points** are Python only.
- **Not built:** xorshift and other kernels.
- **Not regenerated:** a --freq 100 Lean set. Its FASM is byte-identical, so its data would be too
  (only the `sdf` variant reads the SDF).

## Files

| file | change |
|---|---|
| `formal/tools/rtfb/rtfb_design.py` | hop documented, `--lean-all`, `RTFB_OUTMUX`, `RTFB_NO_HOP`, hop statistics line |
| `formal/tools/rtfb/route_gcd.sh` | new: C-10e's route recipe into rtfb/build, optional FREQ |
| `formal/tools/rtfb/gcd_rt.sh` | uses route_gcd.sh's trees; also writes the no-hop report rtd0.txt |
| `formal/tools/rtfb/muller_rt.sh` | rt_all.py (C-10f), then rtfb_design NO_HOP (must agree), then rtfb_design with the hop → Lean |
| `formal/tools/rtfb/lean_muller.py` | new: generates RtFbMuller.lean |
| `formal/tools/rtfb/lean_gcd.py` | `_exact` theorems, header, --freq / --nextpnr |
| `formal/tools/rtfb/summarize.py` | parses rtd reports |
| `formal/tools/rtfb/run.sh` | end to end |
| `formal/lean/Formal/Timing/RtFbM64S1.lean` | NEW data (seed 1 with the hop) |
| `formal/lean/Formal/Timing/RtFbM64S{2..8}.lean`, `RtFbMuller.lean` | regenerated |
| `formal/lean/Formal/Timing/RtFbGcdS{d,2,3,4}.lean`, `RtFbGcd.lean` | regenerated |

## Reproduce

    formal/tools/rtfb/run.sh              # 12 routes + analyses + Lean + check.sh
    formal/tools/rtfb/run.sh --no-route   # if build/ has the routes
    cd formal && ./check.sh Formal/Timing/RtFbCore.lean Formal/Timing/RtFbM64S{1,2,3,4,5,6,7,8}.lean \
        Formal/Timing/RtFbMuller.lean Formal/Timing/RtFbGcdS{d,2,3,4}.lean Formal/Timing/RtFbGcd.lean

- **Toolchain.** `cells/verify/toolchain.sh` passed, nextpnr **sha256 9c732bc6303458df** on every
  route. fasm_audit PASS and build_hw.sh PASS on every gcd route.
- **--freq.**
  - The Muller routes use `--freq 100`.
  - The gcd routes use C-10f's recipe (no --freq), so that the numbers being corrected come from
    the same routes.
  - `route_gcd.sh S 100` (NEXTPNR_FREQ=100) gives a **byte-identical FASM** on all 4 seeds; only the
    SDF line order differs. So every prjxray variant is also the --freq 100 result.
- **Time.** Each gcd analysis took 20-40 min on this loaded machine; each Muller seed about 1 min.

## check.sh

`./check.sh` on the 15 RtFb files above (RtFbCore, RtFbM64S1..8, RtFbMuller, RtFbGcdS{d,2,3,4},
RtFbGcd): **[audit] 481 declarations checked, [check] OK** (only propext / Quot.sound /
Classical.choice; no sorry, axiom or native_decide). Log: scratchpad f2check.log.
