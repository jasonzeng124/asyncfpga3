# B probe Bc: corner-consistent arc numbers for the arbiter probes (7e, 7g, 7h, 7j)

File: `formal/lean/Formal/Cells/ArbCorners.lean` (about 1370 lines, core Lean). It imports
`ArbHandover` (7e), `ArbHeldTimed` (7h), `ArbHeldTimed2` (7j) and `ArbA0Fork` (7g), all
read-only. The old files are untouched.

**Check.** It checks clean in about 7 s. There is no `sorry`, `admit`, `axiom` or
`native_decide`. `#print axioms` was run on all 64 named theorems, in a scratch copy:
- 50 give `propext, Classical.choice, Quot.sound`;
- 3 give `propext, Quot.sound`;
- 11 (the numeric `decide` facts) depend on no axioms.

The commands:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ArbHeldTimed2.lean -o .lake/build/lib/lean/Formal/Cells/ArbHeldTimed2.olean   # only if that olean is missing (it was; built once)
    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ArbCorners.lean

No shared definitions were added; everything is local to the file:
- data and corners: `Col`, `O6`, `O5_I0/I1/I2`, `Corner`, `RF`;
- 7e: `arcsC`, `simArcsC`, `InBoxA`, `worstA`;
- 7h/7j: `Rt`, `cDl`, the `m*` margins and `w*` wire parts, `InBoxD`, `Dw7h`, `Dw7j`, `rtOf`;
- 7g: `cellJ`, `wireJ`;
- witnesses: `x0`, `Dslow`, `Dfast`, `W1s`, `W2s`, `W1f`, `W2f`.

## Pin-map correction (audit P3 rows 1-2; probe Bc2, B-arb-corners-pin.md)

Every O5 number in this note is ONE prjxray line, `CLBLL_L.sdf` SLICEL A5LUT,
under the identity pin map (q on A3, 42/150 ps). The routed link_arb arbiters
put ustate and ugrant in CLBLM_R SLICEM A LUTs, and nextpnr chose the pins
(proved from the bits in `PinAssign`): q enters ugrant on A5 in S1, S3, S4
(`CLBLM_R.sdf` SLICEM A5 -> O5 48/116 ps) and on A3 in S2 (43/148). With the
routed pins (`ArbCornersPin`):
- RT1 is structural at SLOW_MAX and RT1b at FAST_MIN in S1, S3, S4; S2 has this
  note's pattern (RT1b at SLOW_MAX, RT1 at FAST_MIN). Exact condition:
  `gQ ≤ o6` / `o6 ≤ gQ` (`rt1_structural_iff`, `rt1b_structural_iff`).
- Rule J's flat 248 is 8 ps OPTIMISTIC for client 1 in S1, S3, S4 (true 240) and
  24 ps conservative in S2 (272), not "26 ps conservative"; a run that raw rule
  J passes and that acknowledges early is exhibited (`ruleJ_optimistic_run`).
- Skew caps at SLOW_MAX are 8 / 0 (S1, S3, S4) and 0 / 24 (S2), not 0 / 26; at
  FAST_MIN 0 / 3 and 2 / 0.
- `windows_exist_p10` is identity-pin specific: with ustate's q on A5 the pulse
  conditions have Af/As = 0.414 > 0.37.
- Guarded rule J's single-wire-ratio result is replaced by a per-wire band
  statement; the measured band [0.37, 0.82] is too wide for guarded rule J to
  cover FAST_MIN at any early-routing floor (`guard_band_fails`).
The tables below are kept as the identity-pin values; per-seed values are in
B-arb-corners-pin.md.

## Verdict

**Works.** All four items are done, and every number below is a Lean theorem unless it is
marked "arithmetic".

1. Every numeric instance of 7e/7h/7j is re-instantiated at a consistent corner, at both
   SLOW_MAX and FAST_MIN, with rise = fall. The old `prj`/`prjArcs`/`simArcs` are **proved
   to be** the corner mix: `prj_is_mix`, `prjArcs_is_mix` and `simArcs_is_mix` are `rfl`
   equalities with "rise = FAST_MAX, fall = SLOW_MAX".
2. A full box instance is given (each arc independently in [FAST_MIN, SLOW_MAX]), with the
   worst cases proved attained.
3. Corner sign changes are proved: an exact routing window as a function of the wire ratio
   `k = kn/kd`, the condition for it to be non-empty, and a universal guard. These are
   applied to RT1/RT2 and to rule J on 7g's own run semantics.
4. Rise/fall asymmetry is a named, unmeasured parameter, `RF` (H_RF_ASYM). Every reduction
   is stated with it, so the old numbers are the special case d6 = 68, d5a = 97, d5q = 98.

**Two corrections to B-gls-compare's table.** It assumed "all arcs equal d", but O5 and O6
differ within one corner.
- The skew caps are **not** 0/0. They are 0/26 ps at SLOW_MAX and 3/0 ps at FAST_MIN
  [identity pin map; routed seeds: 8/0 or 0/24 at SLOW_MAX, `ArbCornersPin.caps_seed`].
- The "consistent corner" of 7j's tightest margin is not "margin grows by d + 16". It is
  exactly `wfa2 ≤ smin + o5q + wa0s + wfb`, that is +150 ps at SLOW_MAX and +42 ps at
  FAST_MIN.

## Data used (exact)

The source is prjxray `CLBLL_L.sdf`, cell SLICEL. A copy is in this session's scratchpad at
`/tmp/claude-0/-home-user-asyncfpga3/7f52a4bc-3f11-5919-b34a-537c5f812fdf/scratchpad/bf_dl/CLBLL_L.sdf`.
It matches every number in `cells/sim/bd_prims_sim.v` and B-muxtree-fidelity.

All values are in ps.

| arc | FAST_MIN | FAST_MAX | SLOW_MIN | SLOW_MAX |
|---|---|---|---|---|
| A6LUT: A1..A6 → O6 (flat) | 45 | 56 | 100 | 124 |
| A5LUT: A1/A2 → O5 (I0/I1) | 44 | 55 | 122 | 152 |
| A5LUT: A3 → O5 (I2, q) | 42 | 52 | 121 | 150 |

Ratios:
- FAST_MIN/SLOW_MAX: O6 0.363, O5 I0 0.289, O5 I2 0.280.
- Wires (f1_compare, from B-gls-compare): median 0.55, p10 0.37, p90 0.82.

## Theorems

### §0 Data, corners and H_RF_ASYM

- `slowMax`, `fastMin`, `fastMax`, `slowMin` are `Corner`s built from the `Col` data.
- `*_vals` give their numbers.
- `RF` is H_RF_ASYM, the fall arc minus the rise arc per arc class:
  - It is **unmeasured**. prjxray has no edge split.
  - Test it on the board with an odd-inversion LUT ring against a buffer ring.
  - Only `d ≥ 0` is expressible, because the old channel is the rise-fast OR channel.
- `RF.sym` is the consistent default.
- `mixRise`/`mixRF` describe what the old probes used.

### §1 7e (bare-cell handover)

| old theorem (number) | corrected theorem | corrected number |
|---|---|---|
| `header_16ps` (16 ps at w = 0) | `overlap_C`: overlap = `max 0 (d6 − o5q − w)`; `corner_no_overlap`, `slow_header`, `fast_header` | **0 ps at every consistent corner, every w ≥ 0** |
| — | `header_needs_asym`: an overlap exists iff `d6 > o5q + w` | the 16 needs an unmeasured asymmetry larger than a whole O5 arc (`mix_header_16`: 16 = 68 − 52) |
| `header_routed` (w ≥ 16) | `corner_no_overlap` | every w ≥ 0 |
| `sim_overlap` (`max 0 (16 − R)`) | `sim_overlap_C`: `max 0 (d6 − o5q − R)` | 0 for every R with consistent arcs. `cells/sim`'s 16 is an artefact of its arcs |
| `header_r1_to_r2` (margin 28 + w) | `corner_r1_to_r2`, `r1_to_r2_margins` | no overlap; margin `2·o6 + w − o5a` = 96 + w (SLOW_MAX), 46 + w (FAST_MIN), 57 + w (FAST_MAX), 78 + w (SLOW_MIN) |
| `prj_overlap_caps` (72 / 94) | `corner_caps`, `caps_are` | cap = `max 0 (o6 − o5q)` / `max 0 (o5q − o6)`: SLOW_MAX **0 / 26**, FAST_MIN **3 / 0**, FAST_MAX 4 / 0, SLOW_MIN 0 / 21 |
| skew overlap | `skew_r2_to_r1_C` | r2→r1 overlaps iff `o5q < o6 ∧ σ > o5q + w`: **never at SLOW_MAX**, at FAST_MIN iff σ > 42 + w |
| | `skew_r1_to_r2_C` | r1→r2 overlaps iff `o6 < o5q ∧ σ > 2·o6 + w − o5a`: at SLOW_MAX iff σ > 96 + w, **never at FAST_MIN** |
| box, zero skew | `box_overlap_le`, `box_overlap_worst` | r2→r1 ≤ `max 0 (37 − w)`, attained at `worstA` |
| | `box_r1_to_r2_le` | r1→r2 ≤ `max 0 (62 − w)` (bound only; attainment not proved). So 7e's "the reverse never overlaps" holds only for the mix |
| box skew caps | `box_caps`, `box_caps_attained` | 82 / 105 |

### §2 7h/7j (held bd_arbiter)

**Reduction.** `cDl c r x` is 7h's `Dl` at corner c, with asymmetry r and routes x:
- `RT1_iff`, `RT2_iff`, `A0Fork_iff`, `RT1b_iff`, `RT2b_iff` and `A0Fork2_iff` rewrite every
  condition as `0 ≤ m D`.
- `decomp` proves `m(cDl c r x) = arc part(c, r) + wire part(x)` for all 14 margins.
- `mix_constants` checks that the mix gives back the old 180, 52, 108, 136, −16, 12, 40
  and 68.
- `corner_conditions`: at rise = fall, each condition is exactly `0 ≤ arc + wire`.

| condition | arc part (general) | old (mix) | **SLOW_MAX** | **FAST_MIN** | box worst |
|---|---|---|---|---|---|
| RT1 race | 2·o6 + d6 | 180 | 248 | 90 | −18 |
| RT1 structural (`g1fq ≤ g2r`) | o6 − o5q − d5q | — (false) | −26 (false) | **+3: RT1 is structural at FAST_MIN** (`rt1_fast_structural`; identity pins only, routed S1/S3/S4: −3) | — |
| RT2 pulse | o5q | 52 | 150 | 42 | −37 |
| RT2 g1 | o5q | 52 | 150 | 42 | −145 |
| RT2 forkA | o6 + o5q | 108 | 274 | 87 | +8 |
| RT2 forkG | o6 + o5q | 108 | 274 | 87 | −100 |
| A0Fork (7g) | 2·o6 + d6 | 180 | 248 | 90 | +90 |
| RT1b race | o5a + o5q + d5a − d6 | 136 | 302 | 86 | +7 |
| RT1b structural (`g2f ≤ g1rq`) | o5q − o6 − d6 | false | **+26: RT1b is structural at SLOW_MAX** (`rt1b_slow_structural`; identity pins only, routed S1/S3/S4: −8) | −3 (`rt1b_fast_race`) | — |
| RT2b pulse2 | o5q − d6 | **−16** | **150** | **42** | −37 |
| RT2b g2 | o5a + o5q − o6 + d5a − 2·d6 | 12 | 178 | 41 | −117 |
| RT2b forkA2 | o6 + o5q − d6 | 40 | 274 | 87 | +8 |
| RT2b forkG2 | o5a + o5q + d5a − 2·d6 | 68 | 302 | 86 | −72 |
| A0Fork2 | o6 + o5q | 108 | 274 | 87 | +87 |

How to read the table:
- Each condition is `0 ≤ arc part + wire part`. The wire parts are `wRT1`, `wPulse` and so
  on.
- `arcs_slowMax` and `arcs_fastMin` prove the two corner columns.
- `box_7h`/`box_7j` prove the box column for every `D` in `InBoxD`, and
  `box_7h_worst`/`box_7j_worst` prove the bound attained at `Dw7h`/`Dw7j`, which are in
  the box (`Dw7h_inBox`, `Dw7j_inBox`).
- The box worst corners differ between the two directions. Within one direction they are
  consistent with rise = fall. No condition contains both the rise and the fall of one
  arc, so the box values are the same without the coupling.

**`prj_pulse2_tight`, corrected** (`pulse2_zero_routing`). At zero routing the pulse2
condition holds iff `smin ≥ d6 − o5q`. At every consistent corner that is every
`smin ≥ 0`. The "wfa2 + 16" tightest margin of the arbiter does not exist. The pulse
condition is now `wfa2 ≤ smin + 150 + wa0s + wfb` at SLOW_MAX and `+42` at FAST_MIN; the
box gives `wfa2 + 37 ≤ smin + wa0s + wfb`.

**Arc-only margins** (`slow_arc_only`, `fast_arc_only`; routes 0). The server is taken as
two LUT1 arcs **at the same corner**: 248 ps at SLOW_MAX and 90 at FAST_MIN. The old probes
used 112 = 2 × FAST_MAX.

| | RT1 | pulse | g1 | forkA | forkG | fork | RT1b | pulse2 | g2 | forkA2 | forkG2 | fork2 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| old (mix, smin 112) | 292 | 164 | 276 | 220 | 332 | 180* | 248 | 96 | 236 | 152 | 292 | 108 |
| SLOW_MAX (smin 248) | 496 | 398 | 646 | 522 | 770 | 248 | 550 | 398 | 674 | 522 | 798 | 274 |
| FAST_MIN (smin 90) | 180 | 132 | 222 | 177 | 267 | 90 | 176 | 132 | 221 | 177 | 266 | 87 |
| box, smin 90 (`box_arc_only`) | 72 | 53 | 35 | 98 | 80 | 90 | 97 | 53 | 63 | 98 | 108 | 87 |

\* 7h's prose did not state the fork margin; 180 is the arc part.

**Plausible-routing margins (arithmetic, not proved).** These use 7h/7j's own routing
assumptions: smin ≈ 980, hops 434–945, feedback 100–945.
- At SLOW_MAX: RT2 pulse is 980 + 150 + 434 + 100 − 945 ≈ 0.72 ns, and pulse2 is the same.
  Every margin grows by the arc change (about +0.1 to +0.2 ns over 7h/7j's numbers).
- At FAST_MIN, scale the routing by about 0.55: smin ≈ 540, the arcs are as tabled. The
  pulse margin is ≈ 540 + 42 + 239 + 55 − 520 ≈ 0.36 ns.

All of them remain far above the scatter.

**Runt band** (7j, `stuck_pulse_vacuous`, `A1_band_corner`, `A1_band_asym`):
- With `c1r = c1f`, `A1_stuck`'s pulse disjunct is vacuous. A1 can stay stuck only through
  a late g1.
- The band is `0 < p < c1f + wfa1`. It is `δ < p < …` under H_RF_ASYM with δ = c1f − c1r.
- 7j's "68 < p" lower edge is the corner mix.
- With the band starting at 0, 7j's statement "the band is reachable only when RT2 pulse
  fails" still holds: the band's upper edge is unchanged.

### §3 Corner sign changes (cells scale ~0.28–0.36, wires ~0.55)

**Generic theorems** (`Flip` section). Each margin is `As + W` at SLOW_MAX and `Af + Wf` at
FAST_MIN, with **H_WIRE_RATIO** `kd·Wf = kn·W`, a single wire ratio `k = kn/kd` for that
margin's signed wire sum.
- `flip_iff`: (safe at SLOW_MAX and unsafe at FAST_MIN) ⇔ `−As ≤ W ∧ kn·W < −kd·Af`. The
  exact window is `W ∈ [−As, −Af/k)`.
- `flip_iff'` is the opposite flip: `W ∈ [−Af/k, −As)`.
- `flip_exists`: the dangerous window is non-empty ⇔ `kd·Af < kn·As`, i.e. `Af/As < k`.
- `fast_neg_iff`, in SLOW_MAX-margin terms: the FAST_MIN margin is negative ⇔
  `M < As − Af/k`. So **`As − Af/k` is the guard a SLOW_MAX check must add.**
- `guard_universal`: if `k ≤ 1` (H_WIRE_RATIO_LE1) and `Af ≥ 0`, then a SLOW_MAX margin
  `M ≥ As − Af` implies the FAST_MIN margin is ≥ 0.
- `no_flip_nonneg`: arcs ≥ 0 and wire part ≥ 0 means no flip.

**RT1/RT2 (7h/7j).**
- Every condition has `Af/As` between 0.23 and 0.363, below the p10 wire ratio 0.37
  [identity pin map; on the routed seeds up to 0.44, so at k = 0.37 several
  windows are empty, `ArbCornersPin.windows_seed`].
  `windows_exist_median` and `windows_exist_p10` prove the windows are non-empty at
  k = 0.55 and at k = 0.37.
- Every condition CAN change sign. The SLOW_MAX-margin windows are below (ps; the upper
  ends at k ≤ 1 are `As − Af`). Values are computed from `fast_neg_iff`; the
  non-emptiness is proved, the decimals are arithmetic.

  | condition | k = 0.37 | k = 0.55 | k = 0.82 | k ≤ 1 |
  |---|---|---|---|---|
  | RT1 race, fork | 5 | 84 | 138 | 158 |
  | pulse, g1, pulse2 | 37 | 74 | 99 | 108 |
  | forkA, forkG, forkA2, fork2 | 39 | 116 | 168 | 187 |
  | RT1b race, forkG2 | 70 | 146 | 197 | 216 |
  | g2 | 67 | 103 | 128 | 137 |

- Worked instances on the real conditions: `pulse2_flip` and `rt1_flip`.
- Two conditions cannot flip in the dangerous direction:
  - **RT1 as a whole** cannot fail at FAST_MIN (`rt1_fast_structural`); only its race
    disjunct flips.
  - **RT1b** cannot fail at SLOW_MAX (`rt1b_slow_structural`). It can fail at FAST_MIN
    whenever its race margin is negative (`rt1b_fast_race`), so a SLOW_MAX check of RT1b
    tells nothing about FAST_MIN.
- With 7h/7j's plausible routing (smallest SLOW_MAX margins ≈ 0.6–0.7 ns), every margin is
  far outside its window. The flip matters only for a margin already within about 0.2 ns
  of zero.

**7e overlap.**
- At zero skew the no-overlap margin is `o5q + w` with `w ≥ 0`, so `no_flip_nonneg`
  applies and there is no flip.
- With request-fork skew there **is** a k-independent, pure-arc sign change: the sign of
  `o6 − o5q` is −26 at SLOW_MAX and +3 at FAST_MIN. Which handover direction can overlap
  therefore swaps between corners (`skew_r2_to_r1_C`, `skew_r1_to_r2_C`). The overlaps are
  at most 26 ps (SLOW_MAX) and 3 ps (FAST_MIN), far below any detector filter.

**Rule J (7g), on its run semantics.**
- `client2_corner_flip` and `client1_corner_flip`: every SLOW_MAX run is safe and every
  FAST_MIN run acknowledges early (7g's `client{1,2}_iff`) ⇔ the SLOW_MAX routed part
  `wireJ` lies in `[−cellJ_slow, −cellJ_fast/k)`.
  - `cellJ` is the arcs plus site pins; `early_late` proves `early − late = cellJ + wireJ`.
- `ruleJ_arcs` (corrects 7g item 1). The early side's two arcs are 248 / 90 for client 2
  and 274 / 87 for client 1 (SLOW_MAX / FAST_MIN). The box is [90, 248] and [87, 274],
  not 145–180 / 87–117. Rule J's flat 2 × 124 is therefore exact for client 2 and 26 ps
  conservative for client 1 at SLOW_MAX. 7g's "biased unsafe by 68–161 ps" is withdrawn.
  [Identity pin map only. With q's routed ugrant pin, client 1 is 240 ps in S1, S3,
  S4 (rule J **8 ps optimistic**) and 272 ps in S2 (24 ps conservative):
  `ArbCornersPin.ruleJ_seed`, `ruleJ_A5_iff`, `ruleJ_optimistic_run`.]
- 7g's worst-case totals, redone (arithmetic, combining with 7g's unchanged pin term
  −337 / −498):

  | client | SLOW_MAX (was) | full box (was) |
  |---|---|---|
  | client 2 | −337 (−405) | −656 (−601) |
  | client 1 | −311 (−468) | −659 (−657) |

  The pin term stays the dominant gap. That is 7g's rule J′, unaffected.
- **Raw-sign rule J** (unguarded, read at SLOW_MAX) does not cover FAST_MIN. The window
  for client 2 is `0 ≤ M < 248 − 90/k`, 84 ps at k = 0.55. `ruleJ_raw_window` checks
  B-gls-compare's worked example: +133 at SLOW_MAX becomes about +27 at FAST_MIN, outside
  the window.
- **Guarded rule J does cover FAST_MIN** (`ruleJ_guard_covers_fast`), when
  [under ONE wire ratio for the whole signed wire sum; with per-wire ratios in
  the measured band [0.37, 0.82] it does not: the audit's E = 600, L = 525 route
  passes the guard and has a −118.5 ps FAST_MIN margin, and for that band a
  failing guarded route exists above every early-routing floor.
  `ArbCornersPin.perwire_exact`, `guard_band_fails`, `audit_cex`]:
  - the guard passes, `1155·(L + 124) < 772·(E + 372)` (arb_fork.py's 0.772/1.155 on
    nextpnr's flat arcs);
  - E ≥ 114 ps of early routing;
  - k ≤ 1;
  - Af ≥ 87.

  `ruleJ_guard_covers_slow` gives the SLOW_MAX side. `ruleJ_guard_small_E` shows the
  E ≥ 114 premise is needed: with E = 0 and L = 124 the guard passes and the margin is −37.
  The premise is mild, because the early chain always has two routed hops (≥ 295 ps each
  on the patched nextpnr). **Caveat:** this excludes site pins, as rule J does. With
  pins, Af can be negative (A0 on ua_k's A1 pin), and only rule J′ covers that.
- **P2b** (B-gls-compare) is now an exact prediction. Rows whose SLOW_MAX raw margin is in
  `[0, As − Af/k)` flip sign in the FAST_MIN xray-SDF GLS. Rows outside do not, given one
  common k per row.

### §4 Non-vacuity at consistent corners

`nonvacuous_corners` replaces 7j's `nonvacuous`, whose `D0` is the mix:
- `Dslow` (SLOW_MAX, routes 0, smin 248) and `Dfast` (FAST_MIN, routes 0, smin 90) satisfy
  all 12 conditions.
- Four explicit step-function runs satisfy `Run` for all t (`W1s_run`, `W2s_run`,
  `W1f_run`, `W2f_run`), with the server answering in exactly smin (`W_minserver_corners`).
- They satisfy `Scn`/`Scn2` for every horizon past the second server edge.

Every edge was derived by hand from the instant formulas. Examples:
- SLOW_MAX, 7h direction: TA = 400, QB = 524, RR = 674, TA2 = 922, A2↑ at 1046.
- FAST_MIN: TA = 134, QB = 179, TA2 = 311, A2↑ at 356.

`corners_exclusion` instantiates 7h's and 7j's exclusion theorems on these runs.

## What did not work / not done

- **H_WIRE_RATIO is a single ratio per margin.**
  - Per-wire ratio scatter (p10 0.37 to p90 0.82 on different wires of one margin) is not
    modelled. It would be the box applied to wires: each wire's fast value in
    `[0.37, 0.82] ×` its slow value. That is linear and routine, about 1 h.
    [Done for guarded rule J in `ArbCornersPin` §6 (B-arb-corners-pin.md); the
    7h/7j flip windows under a per-wire band are still not done.]
  - Site-pin delays sit inside 7h's routes but scale like cells (about 0.33–0.40), not
    like wires. Splitting them out needs the physical pins of a routed arbiter. No routed
    JSON/SDF is on disk.
- **Negative asymmetry** (fall faster than rise) cannot be expressed. The 7e/7h channel is
  the rise-fast OR channel; a fall-fast AND channel would need new trace lemmas.
- `box_r1_to_r2_le` is a bound; its attainment was not proved.
- The plausible-routing margins and 7g's corrected totals are arithmetic, not theorems.
- **Not re-instantiated here:**
  - `cells/sim/bd_prims_sim.v` (it is RTL-side; it should write rise = fall per corner);
  - ARBITER.md's "+68 ps stretch" (outside formal/);
  - the W = 1 passband.

  ARBITER.md's conclusion ("no copy should fire") gets stronger: the consistent-corner
  zero-skew overlap is 0, and the skew caps are 26 / 3 ps.

## Fidelity per primitive

| primitive | model and fidelity |
|---|---|
| LUT function | Exact: the real INITs via `lutB`/`o5B`/`o6B`, inherited unchanged from 7e/7h/7g. |
| LUT timing | The old probes' channels, unchanged. 7e/7h/7j: the rise-fast pure-delay OR channel, transport, no inertial rejection; at rise = fall it is a plain transport delay. 7g: per-pin transport. Only the numbers change: one prjxray column per corner, O6 flat over pins, O5 per pin (I0/I1 vs I2). Rise/fall asymmetry is the named unmeasured `RF`. |
| Routing / site pins | One fixed delay per pin (route plus site pin), as in 7h/7g. Corner scaling of the signed wire sum is the single ratio H_WIRE_RATIO. |
| Corners | Consistent: all arcs at one column. Box: each arc independent in [FAST_MIN, SLOW_MAX]. "Shared corner plus local scatter" (PROGRAM) lies between these two and is not modelled separately. |
| C-element / state node | A LUT plus a routed feedback, as in 7h (H_LOOP_POS). |
| Server | The relation H_SERVER_MIN. The arc-only instances take two LUT1 arcs at the same corner. |
| Metastability | Absent, as in 7e/7h/7j. |

## Effort and what it buys

**Effort.** The file is done. Remaining work:
- per-wire ratio box: about 1 h;
- the fall-fast channel for negative asymmetry: about ½ day;
- evaluating the flip windows on the 168 rule J survey routes (P2b): about ½ day once
  routed SDFs exist.

**What it buys.**
- The formal side no longer quotes corner-mixed numbers. Every old instance is proved to
  be the mix, and its corrected value is a theorem.
- The tightest margin of the held arbiter disappears.
- The handover-overlap explanation of the 8% is closed at the consistent corner.
- The SLOW_MAX-only checks get an exact, per-condition guard (`As − Af/k`) against corner
  flips.
- Guarded rule J is shown to cover FAST_MIN as rule J sees it; raw rule J is shown not to.
