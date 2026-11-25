# B-arb-kappa (probe Bk1): the routed arbiter's A0 fork under shard A's corner model

Shard B, 2026-10-27. File: `formal/lean/Formal/Cells/OnNetlistArbKappa.lean` (1029 lines, 84
theorems). It answers JOURNAL-B's open finding "ROUTED ARBITER SAFETY HINGES ON THE CORNER MODEL
(Bt3)". That finding said the fork is safe at one die corner, unsafe in the independent box, and
unsafe on 7/8 pairs at the fast corner with the guardband.

## Plain-language result

**Assumed.**
- The die has one corner `c`.
- Each arc's nominal delay at `c` is the interpolation of its fast and slow endpoint.
- Each actual delay is within `1 ± κ` of that nominal.

This is A's settled model, `Formal.Core.Substrate.CornerNat` (`Kappa`, `Corner`, `CArc`,
`Scat`, `EndpointOK`). The fork is 7g's exact gate-level condition (`ArbA0Fork.no_early_ack_iff`)
on the routed arcs of the four `link_arb` bitstreams:
- per-pin site pins inside the route arcs;
- per-pin LUT arcs as in ArbCornersPin, i.e. rule J'.

The A0 prefix shared by both branches is one wire, so it is one arc with one delay, and it
cancels.

**Proved, per seed × client.** There is an exact rational κ\* such that:
- **safe:** for every κ ≤ κ\*, at every corner, for every delay assignment within κ, every run
  of the gate relations is safe;
- **unsafe:** for every κ ≥ κ\* + 6/(E+L), there is a delay assignment within κ, at the binding
  corner endpoint, on which client k's ack rises early on every run, and such runs exist.

The gap between the two is at most 0.0057. It exists because delays are whole ps: there is
one ps of rounding per fork arc. It is not decided.

**NOT covered.**
- Delays varying per tick inside the scatter band. The run model has one fixed delay per arc
  per run, which is 7g's model, not C's `Behaves`/`WinDelay`.
- The A0 rise, and the arbitration (mutual exclusion) case.
- Kleene X and metastability.
- The value of κ itself.

**A's current κ estimate: none.** A-kappa.md and JOURNAL 06:51 withdrew the 0.311 ring bound: it
measured a pre-lut-perm-sink-patch SDF bug. κ is "unmeasured on the current toolchain" (per path
and on differences). The KapRes probe has not reported yet. So I give verdicts at the two
scatter limits the shipped rules are proved sound for:
- **rule A's 1/11**;
- **rule E's `kappaE = 383/1927 ≈ 0.1988`**. This is exactly the CLAUDE.md 0.772/1.155
  guardband, since `(1+κ)/(1−κ) = 1155/772` (`Corner.guard_kappa_iff`).

## Two readings of A's endpoints

A's `CArc` has one `F` and one `S` per arc. How prjxray's four numbers map onto them matters:

- **`lit`** (A's H_ENDPOINTS literally): `F = FAST_MIN` and `S = SLOW_MAX` (+ Elmore on
  routes), for every arc. The prjxray within-corner min..max spread then has to come out of κ.
  Note that SLOW_MIN ≈ 0.8 · SLOW_MAX is reachable only at κ ≳ 0.2.
- **`cons`** (side-pessimistic): early arcs `(FAST_MIN, SLOW_MIN)` and the late arc
  `(FAST_MAX + Elmore, SLOW_MAX + Elmore)`. At κ = 0 this is Bt3's one-corner reading with the
  shared-prefix credit, and κ is scatter on top of the prjxray corner windows.

Both are legitimate `CornerModel`s, because each fork arc is on only one side. `cons` is the one
I would use for a sign-off.

## Table (ps; early = wSt+aSt+wQG+aG+wGC, late = wAC, both past the shared prefix)

κ\* = min over the two endpoints of (E−L)/(E+L). The `unsafe` column is the proved κ from which
a counter-instance exists. The margin columns are arithmetic, (1−κ)E − (1+κ)L at the binding
endpoint, not Lean.

| reading | seed | client | E / L fast | E / L slow | binding | **κ\*** (safe ≤) | unsafe ≥ | at 1/11 | at κE 0.1988 | margin κ=0 / κE |
|---|---|---|---|---|---|---|---|---|---|---|
| lit | 1 | 1 | 686/196 | 2249/795 | slow | 727/1522 = **0.4777** | 0.4796 | safe | safe | 1454 / 849 |
| lit | 1 | 2 | 650/259 | 2231/955 | slow | 638/1593 = **0.4005** | 0.4024 | safe | safe | 1276 / 643 |
| lit | 2 | 1 | 756/192 | 2599/760 | slow | 1839/3359 = **0.5475** | 0.5493 | safe | safe | 1839 / 1171 |
| lit | 2 | 2 | 842/262 | 2789/940 | slow | 1849/3729 = **0.4958** | 0.4975 | safe | safe | 1849 / 1108 |
| lit | 3 | 1 | 763/183 | 2687/809 | slow | 939/1748 = **0.5372** | 0.5389 | safe | safe | 1878 / 1183 |
| lit | 3 | 2 | 754/258 | 2602/965 | slow | 1637/3567 = **0.4589** | 0.4606 | safe | safe | 1637 / 928 |
| lit | 4 | 1 | 704/246 | 2361/978 | slow | 461/1113 = **0.4142** | 0.4160 | safe | safe | 1383 / 719 |
| lit | 4 | 2 | 832/256 | 2761/942 | slow | 1819/3703 = **0.4912** | 0.4928 | safe | safe | 1819 / 1083 |
| cons | 1 | 1 | 686/375 | 1680/795 | fast | 311/1061 = **0.2931** | 0.2988 | safe | safe | 311 / 100 |
| cons | 1 | 2 | 650/453 | 1666/955 | fast | 197/1103 = **0.1786** | 0.1840 | safe | **UNSAFE** | 197 / −22 |
| cons | 2 | 1 | 756/378 | 1933/760 | fast | 1/3 = **0.3333** | 0.3386 | safe | safe | 378 / 153 |
| cons | 2 | 2 | 842/466 | 2088/940 | fast | 94/327 = **0.2875** | 0.2920 | safe | safe | 376 / 116 |
| cons | 3 | 1 | 763/404 | 1903/809 | fast | 359/1167 = **0.3076** | 0.3128 | safe | safe | 359 / 127 |
| cons | 3 | 2 | 754/461 | 1925/965 | fast | 293/1215 = **0.2412** | 0.2461 | safe | safe | 293 / 52 |
| cons | 4 | 1 | 704/464 | 1732/978 | fast | 15/73 = **0.2055** | 0.2106 | safe | safe | 240 / 8 |
| cons | 4 | 2 | 832/468 | 2054/942 | fast | 7/25 = **0.2800** | 0.2846 | safe | safe | 364 / 106 |

### Reading the table

- **`lit`.** All 8 pairs are safe up to κ ≥ 0.40, so they are safe at both reference values.
  The slow endpoint binds, because early arcs are nominally at SLOW_MAX there.
- **`cons`.** All 8 are safe at 1/11.
  - At the guardband's κ = 0.1988, **7/8 are safe and s1 client 2 is not**: κ\* = 0.1786, and
    the counter-instance is proved at 0.1988.
  - s4 client 1 clears by 8 ps (κ\* = 0.2055).
  - The fast corner binds in every pair, which matches Bt3's guarded flags.
- **Why Bt3 found 7/8 negative with the guardband and this finds 1/8.** Bt3's guarded numbers
  took the full A0 routes, with the shared prefix charged once fast (early) and once slow
  (late). Under A's model the prefix is one physical arc with one delay, so it cancels. The
  ps-for-ps difference is Bt3's `c` column (160–216 fast). With the same prefix credit the
  guarded fast reading is `cons` at κE.
- **The weakest pairs agree across all readings:** s1 client 2 and s4 client 1. They are the
  same as rule J's tightest pairs and Bt3's.

## Theorems (namespace `Formal.Cells.OnNetlistArbKappa`)

### Generic (§1–§2)

- **`Arc`, `dlOf`, `earlyArc`.** These are the 10 fork arcs (7g's `Dl` fields, with site pins
  folded into the routes as in `OnNetlistArb.dl7g`), the 7g record of an assignment, and the
  early chain as one `CArc`.
- **`fork_le_of_endpoint`.** `EndpointOK κ late early 0` plus `Scat κ c` on every arc gives
  `late ≤ early`, at every corner. The proof is core arithmetic; it is A's `bundle_endpoints`,
  re-proved without its Mathlib step `endpoint_nom`.
- **`safe{1,2}_of_le`, `not_safe{1,2}`.**
  - `safe{1,2}_of_le`: the fork inequality makes every run safe.
  - `not_safe{1,2}`: the strict reverse inequality, with positive loops, gives no safe run
    (`run_exists` + `client{1,2}_iff`).
- **`counter_core`.** At an endpoint corner it builds `wit`:
  - late arc `⌊(1+κ)v⌋`;
  - early arcs `⌈(1−κ)v⌉`;
  - every other arc at nominal.

  `wit` `Scat`s every arc and has late > early, given the 6-ps gap condition and a side
  condition that every arc is long enough for its rounded value to stay in its band.
  Supporting lemmas: `up_scat`, `down_scat`, `nom_scat`.

### Per pair (§3, generated; 16 pairs × readings)

- `A_s{n}c{k}_{lit,cons}`: the arc data.
- **`safe_s{n}c{k}_R (k : Kappa) (H_KAPPA : k.num * Q ≤ k.den * P) c d (H_SCAT) : Safe …`**,
  where `P/Q = κ*`.
- **`unsafe_s{n}c{k}_R (k) (H_KAPPA : k.den * (E−L+6) ≤ k.num * (E+L)) : ∃ c d, (∀ e, Scat …) ∧ ¬ Safe …`**.

### Verdicts (§4)

`verdict_s{n}c{k}_R_{κA,κE}` are the 32 decided instances at 1/11 and 383/1927. The only `∃ …
¬Safe` one is `verdict_s1c2_cons_κE`.

### Data ties (§5, `tie_s{n}c{k}`, decided)

- **Routes.** For every `lit` route arc, (F, S) equals C's generated `FasmLink.S{n}.pinDelay`
  box window. The shared prefix is tied through the two full routes.
- **LUT arcs.** These equal ArbCornersPin's SDF columns (`ArbCorners.O6`, and
  `ArbCornersPin.pinCol` at ugrant's q pin from the bits, `s{n}.ug`).
- **`cons` arcs.** They have the same F for early arcs and the same S for the late arc, and the
  SLOW_MIN LUT columns. Their early route S (SLOW_MIN) and late route F (FAST_MAX + Elmore) are
  Bt3's per-corner windows. Those are quoted in `OnNetlistArb.run7g_*`, but C's generated file
  does not carry them (Bt3 limitation 3), so they are not tied.

### Non-vacuity (§6)

- **`nonvacuous_lit`.** For all 16 arc tables, κ = 0 at the fast corner is a realisation (A's
  `realizes_fast`), and a run with those delays exists.
- **`hyps_satisfiable`.** κ = 0 meets the `safe_*` hypothesis and κ = 1 meets the `unsafe_*` one.
  Every `unsafe_*` hypothesis is met by κ = 1, since L ≥ 3.
- **Exactness.** At κ = κ\* the endpoint check is an equality, and above κ\* + 6/(E+L) a
  counter-instance exists, so κ\* is the threshold up to ps rounding.

### Data source (task item 3)

Bt3's scratch generator (`…/7f52a4bc…/scratchpad/bt3/`) and Bp's JSON no longer exist. The
per-arc fast/slow windows were taken from the proved statements of
`OnNetlistArb.run7g_c{1,2}_s{n}_{fast,slow}`:
- `dl7g` records of the form `c wSt aSt wQf wQG aG wGC wAC aC wCf`;
- lo record = corner min, hi record = corner max + Elmore.

That extraction is `scratchpad/Bk1/run7g.txt`. The routes were checked against C's `pinDelay`
in §5. Nothing was re-routed. Generator: `scratchpad/Bk1/gen.py` (plus `data.py`).

## Check status

- **Real file: checked against the real Mathlib on 2026-10-29 (probe Bkx18).** It imports `Formal.Core.Substrate.CornerNat`, which needs
  Mathlib, and Mathlib was not built (`.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean`
  absent; `lake build` pid 1333 still running). Check command, once Mathlib is built:
  `cd formal/lean && ../slot.sh lake env lean -DautoImplicit=false Formal/Cells/OnNetlistArbKappa.lean`.
- **What was checked: a core mirror**, `scratchpad/Bk1/Mirror.lean`.
  - It contains CornerNat's §1–5 definitions and lemma statements copied programmatically and
    verbatim, plus `realizes_fast`. Four lemmas whose proofs need Mathlib (`scat_band`,
    `band_sub_ind`, `nom_add`, `endpoint_nom`) are `sorry` in the mirror only.
  - Below that is the file's body, byte-identical (`diff` from the `namespace` line on).
  - Command: `LEAN_PATH=/tmp/bchk-olean2 ../slot.sh lean -DautoImplicit=false …/Mirror.lean`.
    Result: rc 0, only the 4 mirror `sorry` warnings, about 35 s. OnNetlistArb and ArbCornersPin
    oleans were refreshed by `bchk.sh` first.
  - `#print axioms` on all 84 theorems: 71 `[propext, Classical.choice, Quot.sound]`, 3
    `[propext, Quot.sound]`, 9 `[propext]`, 1 none. **No `sorryAx`.** The body uses none of the
    four sorried lemmas.
  - `set_option maxRecDepth 200000` is needed: omega's certificates on coefficients around 3700
    hit the default limit.
- **Mutations** (scratch copies), both killed:
  - s1c2-cons late F 453 → 460: `safe_s1c2_cons` fails;
  - κ\* 197 → 198 and the unsafe bound 203 → 202: both theorems fail.
- **Risk when the real file is checked.** Elaboration under Mathlib, e.g. a simp-set or lemma
  name difference in `Nat.lt_of_mul_lt_mul_right` or `Nat.le_of_mul_le_mul_left`. These are
  only fixes to proof scripts; the statements would not change.

## Findings

1. **Under A's corner model, the routed arbiter's A0 fork is safe on all 8 pairs at rule A's
   κ = 1/11.** At the guardband κ = 0.1988 it is safe on 8/8 in the literal reading and on 7/8
   in the side-pessimistic reading. **s1 client 2 is unsafe from κ ≈ 0.18** (κ\* = 197/1103).
   s4 client 1 is next (κ\* = 15/73 ≈ 0.2055).
2. **The shared A0 prefix being one arc is what moves Bt3's 7/8 to 1/8.** It is H_A0_SHARED,
   now a consequence of the model: one wire, one delay. Physically certain, as long as the
   prefix really is one routed wire tree (`routed.json`).
3. **A's `lit` endpoint convention is generous to early paths.** It is nominal SLOW_MAX at the
   slow corner, so the within-corner prjxray spread has to be inside κ. If A keeps this
   convention, κ must be estimated to cover about 0.1–0.2 of within-corner spread, which is the
   prjxray (max−min)/(max+min) alone. Worth a line in A's model note.
4. Whether the routes are safe now depends only on κ: is κ < 0.178 on these short tails? The
   differential tail ring (A-kappa.md) would measure exactly that. For the arbiter the tails are
   the A0 branch vs the ustate/ugrant chain.
