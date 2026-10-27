# B probe Bc2: ArbCorners' numbers with the routed pin of every seed (audit P3 rows 1-2)

Shard B, 2026-10-27. File: `formal/lean/Formal/Cells/ArbCornersPin.lean` (core Lean, about
700 lines, 52 theorems). It imports `ArbCorners` and `PinAssign` read-only (and through
them ArbHandover, ArbHeldTimed, ArbHeldTimed2, ArbA0Fork and C's `FasmLink.S1..S4`).

This answers audit rows 35-36 (`audit/findings/P3.md` rows 1-2,
`audit/lean/P3/ArbPinA5.lean`).

**No routing was done.** The pins come from C's committed fixtures, read back from the
four `link_arb` bitstreams, which were routed by **nextpnr sha256 9c732bc6303458df** (all 9
patches ok, `toolchain.sh` ok, per `fixture/link_arb_s*.toolchain`). The arcs come from
prjxray-db zynq7 `timings/CLBLM_R.sdf`, at
`/tmp/claude-0/-home-user-asyncfpga3/7f52a4bc-3f11-5919-b34a-537c5f812fdf/scratchpad/pins/pxdb/zynq7/timings/CLBLM_R.sdf`.
That file is byte-identical to the `mtbf/oldpnr/.../prjxray-db/zynq7` copy.

## Check

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/PinAssign.lean -o .lake/build/lib/lean/Formal/Cells/PinAssign.olean -i .lake/build/lib/lean/Formal/Cells/PinAssign.ilean   # only if that olean is missing (it was; built once, 14 s)
    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ArbCornersPin.lean

The file checks clean in about 5 s, with no output. There is no `sorry`, `admit`, `axiom`
or `native_decide`. `#print axioms` was run on all 52 theorems in a scratch copy:
- 19 use `[propext, Classical.choice, Quot.sound]`;
- 5 use `[propext, Quot.sound]`;
- 23 use `[propext]`;
- 5 use no axioms.

Two mutations were run on scratch copies, and both were killed:
- **S2's ugrant pin list `[0,4,2]` changed to `[0,2,4]`.** `s2_bits` fails because the
  bits' `Realizes`/`_src` no longer match, and so do the eight per-seed `decide`s. The pin
  lists are therefore tied to the bits, not typed in.
- **SLICEM A5 → O5 SLOW_MAX changed from 116 to 125.** `A5_vs_O6`, the structural, caps
  and rule J theorems all fail.

`Bundling.lean` was re-checked after its comment edit, and it is clean.

## Data (ps)

`CLBLM_R.sdf`, `LUT_OR_MEM5LRAM SLICEM/A5LUT`, `IOPATH A_k O5`:

| pin | FAST_MIN | FAST_MAX | SLOW_MIN | SLOW_MAX |
|---|---|---|---|---|
| A1 | 44 | 55 | 121 | 150 |
| A2 | 44 | 55 | 118 | 146 |
| A3 | 43 | 53 | 120 | 148 |
| A4 | 46 | 57 | 121 | 150 |
| A5 | 48 | 60 | 93 | 116 |
| O6, any pin (SLICEL and SLICEM, all letters and tiles) | 45 | 56 | 100 | 124 |

ArbCorners used SLICEL A3 (42/150) for q. SLICEM A3 is 43/148 (`slicem_A3_ne`).
A5 is the only pin with SLOW_MAX below O6 and FAST_MIN above it (`A5_vs_O6`).

The pins per seed are 0-based, as in `PinAssign`. Each seed's lists are proved from the bits
in `s{1..4}_bits`, which reuse PinAssign's `la*_ustate_o5/_src` and `la*_ugrant_o5/_src`
plus the site strings.

| seed | ustate site | ustate r1, r2, q | ugrant site | ugrant r1, r2, **q** |
|---|---|---|---|---|
| S1 | SLICE_X42Y94 A | A3, A4, A5 | SLICE_X42Y95 A | A1, A4, **A5** |
| S2 | SLICE_X42Y89 A | A3, A2, A5 | SLICE_X42Y87 A | A1, A5, **A3** |
| S3 | SLICE_X42Y93 A | A5, A2, A1 | SLICE_X42Y97 A | A3, A2, **A5** |
| S4 | SLICE_X42Y88 A | A1, A4, A5 | SLICE_X42Y91 A | A3, A2, **A5** |

All of these are `CLBLM_R_X29Y*.SLICEM_X0.ALUT`, according to C's importer comment. The Lean
check covers the site strings. The tile type and LUT letter come from the comment.

## Theorems (namespace `Formal.Cells.ArbCornersPin`)

### §1 Seven arc classes

- `PA` holds the pinned arcs at one corner:
  - `o6`;
  - ustate O5 from its r1, r2 and q pins (`uR1 uR2 uQ`);
  - ugrant O5 from its r1, r2 and q pins (`gR1 gR2 gQ`).
- `Seed.at s col` reads each O5 arc from its routed pin's SDF line.
- `cDlP` is 7h's `Dl` with these arcs, with rise = fall.
- **`decompP`**: each of the 14 7h/7j margins equals the pinned arc part plus the same
  wire part as ArbCorners. Two things no longer cancel:
  - RT1's race keeps `uR1 − gR1`, because ustate's and ugrant's r1 pins differ;
  - the pulse conditions read **ustate's** q pin (`uQ`), not ugrant's.
- **`margins_ofCorner`**: with `PA.ofCorner c` (identity pins), all 14 margins equal
  ArbCorners' `cDl c RF.sym` margins. ArbCorners is therefore the special case.

### §2 RT1 / RT1b structural (audit row 1)

- **`rt1_structural_iff`**: `(∀ routing, RT1) ↔ gQ ≤ o6`.
- **`rt1b_structural_iff`**: `(∀ routing, RT1b) ↔ o6 ≤ gQ`.
- In the "only if" direction, an explicit routing breaks the condition: a long
  r1 → ugrant route (respectively r2 → ugrant).
- **`structural_s1..s4`** and `structural_margins` give the per-seed results:

| seed (q on ugrant) | SLOW_MAX `o6 − gQ` | structural at SLOW_MAX | FAST_MIN `o6 − gQ` | structural at FAST_MIN |
|---|---|---|---|---|
| S1, S3, S4 (A5) | **+8** | **RT1** (RT1b is not) | **−3** | **RT1b** (RT1 is not) |
| S2 (A3) | −24 | RT1b (RT1 is not) | +2 | RT1 (RT1b is not) |
| ArbCorners (identity, SLICEL A3) | −26 | RT1b | +3 | RT1 |

So ArbCorners' `rt1b_slow_structural` and `rt1_fast_structural` hold for 1 of 4 seeds. In
every seed and at both corners, exactly one of the two is structural. Which one it is
depends on the pin.

### §3 Per-seed arc parts (`parts_slowMax`, `parts_fastMin`, `parts_identity`)

The order is RT1, RT1s, pulse, g1, forkA, forkG, fork, RT1b, RT1bs, pulse2, g2, forkA2,
forkG2, fork2.

| | SLOW_MAX | FAST_MIN |
|---|---|---|
| identity (ArbCorners) | 248 −26 150 150 274 274 248 302 26 150 178 274 302 274 | 90 3 42 42 87 87 90 86 −3 42 41 87 86 87 |
| S1 | 246 8 116 114 240 238 248 266 −8 116 142 240 266 240 | 89 −3 48 47 93 92 90 94 3 48 49 93 94 93 |
| S2 | 246 −24 116 114 240 238 248 294 24 116 138 240 262 272 | 89 2 48 47 93 92 90 87 −2 48 47 93 92 88 |
| S3 | 216 8 150 118 274 242 248 262 −8 150 172 274 296 240 | 95 −3 44 49 89 94 90 92 3 44 43 89 88 93 |
| S4 | 250 8 116 118 240 242 248 266 −8 116 142 240 266 240 | 91 −3 48 49 93 94 90 94 3 48 49 93 94 93 |

**What changes.**
- The pulse/pulse2 arc part (ustate's q-feedback pin) is 116/48 on A5 (S1, S2, S4),
  against ArbCorners' 150/42.
- S3's RT1 race is 216: ustate's r1 is on A5 (116) and ugrant's r1 is on A3 (148).
- Every non-structural SLOW_MAX arc part stays ≥ 114 ps. With 7h/7j's plausible routing (smallest margins
  about 0.6 ns) no conclusion about safety changes. Only the arc parts change, by up to
  −34 ps (pulse) and −32 ps (S3 RT1).

**Flip windows (`windows_seed`).**
- ArbCorners' `windows_exist_p10` ("every condition can flip at k = 0.37") is
  identity-pin specific. With ustate's q on A5, the pulse condition has
  Af/As = 48/116 = 0.414 > 0.37, so its window is empty at k = 0.37.
- At the median k = 0.55, every condition of every seed still has a window. The largest
  ratio is S3's RT1 race, 95/216 = 0.440.

The window bounds `As − Af/k` per seed (arithmetic, from the table above), at
k = 0.37 / 0.55 / 0.82 / 1:
- S1/S2/S4 pulse: −14 / 29 / 57 / 68;
- S3 pulse: 31 / 70 / 96 / 106;
- RT1 race: 5 / 84 / 137 / 157 (S1), and −41 / 43 / 100 / 121 (S3).

### §4 7e skew caps (`caps_seed`, `skew_r2_to_r1_s1_slow`, `skew_r1_to_r2_s1_slow`)

| | SLOW_MAX r2→r1 / r1→r2 | FAST_MIN |
|---|---|---|
| S1, S3, S4 | **8 / 0** | 0 / 3 |
| S2 | 0 / 24 | 2 / 0 |
| ArbCorners (identity) | 0 / 26 | 3 / 0 |

At S1 SLOW_MAX:
- r2 → r1 overlaps iff `σ > 116 + w`. ArbCorners says "never".
- r1 → r2 never overlaps. ArbCorners says "iff σ > 96 + w".

These apply ArbCorners' generic `skew_*_C` to `cornerOf s1S`. The caps stay ≤ 26 ps in
every seed, so the ARBITER.md conclusion is unaffected.

### §5 Rule J per seed, on 7g's run semantics

- **`client{1,2}_vs_flat`**: every run is safe ⇔ `flatJ p ≥ 248 − (aSt + aG)`.
  - `flatJ` is rule J's early − late with nextpnr's flat 2 × 124 arcs.
  - The bias `248 − (aSt + aG)` is exactly what the flat arcs get wrong. A positive bias
    means rule J is optimistic.
- **`ruleJ_seed`** gives the per-seed values:

| seed | client 1 early arcs (SLOW_MAX / FAST_MIN) | rule J at SLOW_MAX | client 2 |
|---|---|---|---|
| S1, S3, S4 (q on A5) | 240 / 93 | **8 ps optimistic** | 248 / 90, exact |
| S2 (q on A3) | 272 / 88 | 24 ps conservative | 248 / 90, exact |
| ArbCorners (identity) | 274 / 87 | 26 ps conservative | 248 / 90 |

- **`ruleJ_A5_iff`**: with the A5 arcs, client 1 is safe ⇔ `flatJ p ≥ 8`.
- **`ruleJ_A3_iff`**: with the A3 arcs, client 1 is safe ⇔ `flatJ p ≥ −24`.
- **`ruleJ_optimistic_run`**: `pOpt` has flat margin +7, so raw rule J passes it. A run on
  it exists (7g's `run_exists`), and on every run client 1's ack rises.
- **`ruleJ_conservative_run`**: `pCons` (S2 arcs) has flat margin −1, so rule J rejects it,
  yet every run is safe.
- **`ruleJ_guard_covers_slow'`**: the **guarded** rule J still covers SLOW_MAX on every
  seed.
  - ArbCorners' `ruleJ_guard_covers_slow` needed true arcs ≥ 248, which is false for
    S1, S3 and S4.
  - The guard itself implies `L ≤ E + 124`, so any `As ≥ 125` suffices.
- **`guard_fast_premise_seed`**: ArbCorners' single-ratio `ruleJ_guard_covers_fast` premise
  `Af ≥ 87` holds per seed (93 / 88 / 93 / 93, and 90 for client 2).

The 8 ps optimism is small next to the guard's 0.772/1.155 factors, so guarded rule J at
SLOW_MAX is unaffected. It matters for raw-sign readings and for any rule that would use
flat arcs without the guard.

### §6 Guarded rule J under per-wire ratios (audit row 2)

**Hypothesis H_WIRE_BAND.** Each routed wire has slow value `s` and fast value `F/d`, with
`a·s ≤ F ≤ b·s`. That is, each wire has its own ratio in `[a/d, b/d]`. This replaces
ArbCorners' single H_WIRE_RATIO. Test: per-net delays of one route in the FAST_MIN and
SLOW_MAX prjxray-SDF GLS.

**`perwire_exact` (the exact per-route condition).** For a route with early wires summing
to `E` and late wires to `L` (SLOW_MAX), the FAST_MIN margin is ≥ 0 for every per-wire
assignment in the band ⇔ `d·Af + a·E − b·L ≥ 0`. The worst case is attained with one wire
per side.

**`guard_band_covers` (uniform, sufficient).** Two conditions together imply that every
guarded route with `E ≥ E0` is covered:
- `772·b ≤ 1155·a`, i.e. k_max/k_min ≤ 1155/772 ≈ 1.496;
- `1155·d·Af + (1155a − 772b)·E0 ≥ 143963·b`.

**`guard_band_fails`, `band_cover_needs_narrow` (uniform, necessary).** If
`1155·a < 772·b`, then for every floor `E0` and every Af there is a route with E ≥ E0 that
passes the guard and has a negative worst-case FAST_MIN margin. Covering every route above
a floor therefore **requires** the narrow band.

**`audit_cex`** reproduces the audit's counterexample:
- band [0.37, 0.82], Af = 90, E = 600, L = 525;
- the guard passes and E ≥ 114;
- the wires are 222 ps (0.37) and 430.5 ps (0.82);
- the margin is **−118.5 ps**. The single ratio k = 0.55 gives +131.25 on the same route.

**`audit_cex_seeds`**: with client 1's per-seed Af, the margin is −115.5 ps (93) and
−120.5 ps (88).

**`p10p90_fails`**: 1155·37 < 772·82, so the measured p10-p90 band is too wide for **any**
floor.

**`band_examples`**:
- the sufficient condition contains ArbCorners' k = 1, E ≥ 114 case;
- a narrow band [0.55, 0.82] needs a floor of E0 = 7948 ps by this bound (Af = 87).

**Reading.** Guarded rule J's FAST_MIN coverage holds under one common wire ratio
(ArbCorners), and under any band at most 1.496 wide with a large enough early floor. It
fails under the measured p10–p90 band if per-wire ratios are independent. Whether real
per-wire ratios on one route are that independent is unmeasured; it is the same open
question as H_WIRE_BAND.

## Hypotheses (named)

- **Arc data.** prjxray `CLBLM_R.sdf` SLICEM A5LUT/A6LUT columns, one column per corner,
  rise = fall. prjxray has no edge split; H_RF_ASYM is not modelled here, see ArbCorners'
  `RF`.
- **Pins.** These are not hypotheses: they are PinAssign's bit-derived `Realizes`/`_src`.
  The tile type and LUT letter come from C's importer comment.
- **Routes and site pins.** One delay per pin (`Rt`, as in 7h). Rule J's `flatJ` keeps the
  delay set's routes and site pins.
- **H_WIRE_BAND** (§6), as above.
- **7e (`cornerOf`).** 7e's `Arcs` has one O5 arc for both r pins of g1. g1 = r1 ∧ q does
  not read r2, so the r2 value is never used by the transport LUT.

## What did not work / not done

- **The full box** (`InBoxA`, `InBoxD`, `box_caps` 82/105, `box_overlap_le` 37) was not
  redone per site. The audit notes that `box_caps` 105 becomes up to 112 at other
  letters/tiles. The 37 ps worst survives, because SLICEL A3 FAST_MIN 42 is the global
  minimum.
- **7h/7j flip windows under a per-wire band** were not done. Only rule J was done. The
  same `perwire_exact` pattern applies per margin (signed wire sums: positive wires at
  `a`, negative at `b`).
- **FAST_MAX / SLOW_MIN columns per seed** were computed in the script
  (`scratchpad/bc2/arcs.py`) but are not stated as theorems.
- **Toy delay sets.** `ruleJ_optimistic_run` / `ruleJ_conservative_run` use toy delay
  sets (zero routes, one late wire), not the routed fixtures. Their purpose is to show the
  8 ps bias is realisable on 7g's run model.
- **Uniform condition is not an iff.** The uniform sufficient condition (§6) is not proved
  tight. The integer floor of the guard makes the exact uniform iff messy; the pointwise
  iff is exact.

## Prose fixed

- `Bundling.lean:307`: the "distinct rise and fall arcs, 56..152" comment.
- B-arb-held-timed.md: "R0 and g1 fall arcs from I0 … 152", plus pointers to the per-seed
  parts.
- B-arb-held-timed2.md: a pointer.
- B-muxtree-fidelity.md: "the per-pin difference lives entirely in site-pin delays" now
  holds for O6 only; O5 varies per pin.
- B-arb-a0fork.md: the rule J "26 ps conservative" claims now carry the pin-map caveat,
  the "pins could not be read" line is updated, and the ARC_lo pin note is fixed.
- B-arb-corners.md: a pin-map correction section, plus inline caveats on the structural
  rows, caps, rule J, guarded rule J and `windows_exist_p10`.

The other rise/fall readings in these notes were already marked withdrawn.

## Verdict

**Works.** Both audit rows are answered with theorems:
- **Row 35** (pin map): RT1/RT1b structurality, the caps and rule J's bias are now exact
  functions of q's routed pin, instantiated on all 4 seeds. 3 of 4 seeds reverse
  ArbCorners' signs. Rule J is 8 ps optimistic there, with a realising run.
- **Row 36** (single ratio): replaced by an exact per-wire-band condition. The measured
  band defeats guarded rule J's FAST_MIN coverage at every floor.

**Effort to finish: about 0.5 day.** That covers the per-site box and the per-wire bands
for the 7h/7j margins.

**What it buys:**
- the formal side's arbiter corner numbers now come from the pins the bitstreams actually
  use;
- rule J' (B-arb-a0fork) should read the O5 arc of the routed pin, not a flat or
  identity-pin value;
- a FAST_MIN guard on routed wires needs either a measured per-route ratio correlation or
  a ratio band at most 1.5 wide.

## Fidelity per primitive

| primitive | model |
|---|---|
| LUT function | Real INITs, inherited from 7e/7h/7g. The pin maps are PinAssign's bit-proved `Realizes` on the physical INIT. |
| LUT timing | One transport arc per (LUT, physical pin, output) at one prjxray column, from the site's own SDF cell (CLBLM_R SLICEM A5LUT/A6LUT). Rise = fall. 7h/7j's rise-fast OR channel at rise = fall is a plain transport delay. |
| Routes / site pins | One fixed delay per pin (7h `Rt`, 7g `Dl`). The corner scaling is per-wire in a band (§6, rule J only). |
| C-element / state node | A LUT plus routed feedback, as in 7h. |
| Metastability | Absent. |
