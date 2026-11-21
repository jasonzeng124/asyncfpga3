# B-arb-kappa-exact (probe Bkx18): exact κ thresholds of the routed arbiter's A0 fork

Shard B, 2026-10-29. File: `formal/lean/Formal/Cells/OnNetlistArbKappaExact.lean` (2870 lines).
Checked with `/tmp/claude-0/btools/bcheck.py Formal/Cells/OnNetlistArbKappaExact.lean`: **OK**,
no warnings, about 2 min. It answers audit row 18 (`P7-kappa.md`: "exact per-pair kappa
thresholds" OVERSTATED). `OnNetlistArbKappa` proves the fork safe for κ ≤ κ\* and unsafe only
from κ\* + 6/(E+L), and leaves the gap between undecided. This file decides the gap for all
16 cases (8 seed × client pairs, 2 readings each).

Side result: `OnNetlistArbKappa.lean` itself now compiles against the real Mathlib
(bcheck OK, 2026-10-29). Its note still says it was checked only through a core mirror.

## The model (unchanged from `OnNetlistArbKappa`, i.e. A's `CornerNat`)

- **κ is rational** (`num/den`). **The corner is rational** (`w1/(w0+w1)`) and shared by the
  whole die.
- **Every delay is a whole number of ps** (`Nat`), within `1 ± κ` of the arc's nominal delay at
  that corner (`Scat`).
- The fork is 7g's gate-level condition, `Safe` (`ArbA0Fork`).
- §0 restates the definitions word for word. §8 (`Bridge`) ties them back:
  - `Scat` is A's `Formal.Core.Substrate.Scat`, by `Iff.rfl`;
  - the 16 tables equal `OnNetlistArbKappa.A_*` arc by arc, by `rfl`;
  - `Bridge.exact_*` restates every result in A's and Bk1's own types.

## Result

For each case, `exact_X (k) : (∀ c d, (∀ e, Scat k c (A_X e) (d e)) → Safe …) ↔ Below_X k`.

**15 of the 16 cases.** `Below_X k` is `k < u ∧ P_X(num, den) < 0`, where:
- `P_X` is an explicit integer quadratic form;
- its root κ_ex in [0, 1] is **irrational**, because the discriminant is not a perfect square.

Since κ is rational, safe ⟺ κ < κ_ex ⟺ κ ≤ κ_ex. The threshold is approached only at an
interior corner that moves with κ, and it is never attained there:
- at every rational κ > κ_ex there is a violating assignment, at a corner that depends on κ;
- at every κ < κ_ex, every corner and every whole-ps assignment is safe.

**s2c2 `cons`.** The threshold is rational, κ_ex = 94/325, and it is attained at the fast corner:
- κ < 94/325 is safe;
- κ ≥ 94/325 is unsafe, with a fixed fast-corner assignment.

**Not a staircase.** `safe_antitone` proves that `Scat` bands only grow with κ. So in every case
the safe κ form an initial segment, and the unsafe κ form the rest of [0, 1].

**Both sides are proved at the gate level.**
- *Safe side:* `Safe` holds over every run, for every corner and every whole-ps assignment.
- *Unsafe side:* the file exhibits a corner and an assignment that satisfy `Scat` on all ten
  arcs. On it every run acks early, and runs exist (`not_safe{1,2}`).

`bracket_X` pins κ_ex to within 1e-10, decided.

| seed | client | reading | old safe ≤ κ\* | old unsafe ≥ | **κ_ex (exact)** | whole-ps threshold at the endpoint corner alone | binding vector (wSt, aSt, wQG, aG, wGC) / late wAC | binding early arc | boxes |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 1 | cons | 0.29312 | 0.29877 | **0.2954922** | 0.296000 | (185, 32, 86, 34, 148) / 486 | wQG | 21 |
| 1 | 2 | cons | 0.17860 | 0.18404 | **0.1806787** | 0.181015 (= 82/453) | (215, 37, 100, 37, 145) / 535 | wQG | 16 |
| 2 | 1 | cons | 0.33333 | 0.33862 | **0.3356388** | 0.336100 | (150, 30, 135, 29, 161) / 506 | wSt | 13 |
| 2 | 2 | cons | 0.28746 | 0.29205 | **94/325 = 0.2892308** | same (attained, fast) | (160, 32, 144, 32, 231) / 600 | n/a (rational case) | 15 |
| 3 | 1 | cons | 0.30763 | 0.31277 | **0.3109273** | 0.311111 | (123, 32, 151, 34, 189) / 530 | wGC | 17 |
| 3 | 2 | cons | 0.24115 | 0.24609 | **0.2440256** | 0.244444 | (135, 35, 165, 35, 203) / 574 | wQG | 18 |
| 4 | 1 | cons | 0.20548 | 0.21062 | **0.2080708** | 0.208333 | (248, 36, 137, 39, 101) / 562 | wGC | 19 |
| 4 | 2 | cons | 0.28000 | 0.28462 | **0.2824745** | 0.282946 | (225, 33, 124, 33, 186) / 602 | wGC | 17 |
| 1 | 1 | lit | 0.47766 | 0.47963 | **0.4784366** | 0.478582 | (471, 65, 224, 61, 353) / 1175 | wGC | 51 |
| 1 | 2 | lit | 0.40050 | 0.40239 | **0.4011245** | 0.401993 | (538, 74, 256, 74, 388) / 1331 | wSt | 101 |
| 2 | 1 | lit | 0.54748 | 0.54927 | **0.5481793** | 0.548387 | (383, 56, 305, 67, 361) / 1173 | wQG | 68 |
| 2 | 2 | lit | 0.49584 | 0.49745 | **0.4963581** | 0.496809 | (424, 62, 338, 62, 507) / 1394 | wQG | 91 |
| 3 | 1 | lit | 0.53719 | 0.53890 | **0.5379863** | 0.538066 | (352, 58, 330, 54, 449) / 1244 | wGC | 58 |
| 3 | 2 | lit | 0.45893 | 0.46061 | **0.4593934** | 0.459677 | (411, 67, 386, 67, 475) / 1407 | wSt | 93 |
| 4 | 1 | lit | 0.41420 | 0.41599 | **0.4148922** | 0.415133 | (631, 73, 334, 68, 276) / 1383 | wSt | 60 |
| 4 | 2 | lit | 0.49122 | 0.49284 | **0.4917064** | 0.492119 | (548, 63, 290, 63, 438) / 1403 | wGC | 78 |

How to read the table:
- The "endpoint corner alone" column is the whole-ps threshold if only the fast corner (`cons`) or
  the slow corner (`lit`) were allowed. It comes from the Python analysis, not from Lean, except
  82/453, which `interior_s1c2_cons` brackets.
- The exact threshold always lies strictly inside the old gap.
- Except for s2c2 cons, the exact threshold is below the endpoint value. The binding corner is
  interior:
  - c\* ≈ 0.0003–0.003 for `cons`;
  - 1 − c\* ≈ 0.0002–0.013 for `lit`.

  The fractional ps there round better than at the endpoint.

### Verdicts (decided)

- **`verdict_κA`:** at κ = 1/11 all 16 cases are safe.
- **`verdict_κE`:** at κE = 383/1927 = 0.1988, 15 of 16 cases are safe. s1 client 2 `cons` is
  unsafe.
- **s4 client 1 `cons`:** the margin is now 0.2081 − 0.1988. It was 0.2055 under κ\*.

### Audit point (row 18): CONFIRMED, and sharpened

`audit_s1c2_cons_200` proves three things at κ = 200/1103 for s1c2 `cons`:
- κ = 200/1103 is unsafe (`¬ Below`);
- the auditor's own fast-corner assignment satisfies `Scat` (late 535 > early 534);
- that assignment is `¬Safe`.

So κ\* = 197/1103 is only the bound from the real relaxation.

The gap is also wider than the auditor found. `interior_s1c2_cons` shows that at κ = 0.1807:
- every fast-corner assignment is safe;
- the case is still unsafe, at an interior corner.

The exact whole-ps threshold is κ_ex ≈ 0.18067873, about 199.29/1103.

## Method (all in the file, kernel-checked)

### Safe side (`safe_X`)

1. A chain of corner boxes [p, q] covers [0, 1]: 13–101 boxes, end points with denominators up
   to 2^34.
2. `chainOK` is evaluated by `decide +kernel`. For every κ < u it bounds each early arc from
   below at p and the late arc from above at q, rounding outward to whole ps (`arc_lo`,
   `arc_hi`, `box_sound`).
3. In each box, one of two things holds:
   - `hi ≤ Σ lo`, so the box is safe outright;
   - `hi = Σ lo + 1`, and the box forces the one binding vector.
4. The forced vector is excluded exactly. `elim2` eliminates the corner from the two binding
   constraints (one early arc j, and the late arc). Two half-planes in (w0, w1) meet in the
   positive quadrant only if `a2·b1 ≤ a1·b2`, which here is `P ≥ 0`. That contradicts
   `P < 0`.

### Unsafe side (`unsafe_X`)

- **κ ≥ κ_fix:** a fixed endpoint-corner assignment, checked by `omega`. κ_fix is f(0) = M/F_L − 1
  for `cons`, and max_i(1 − m_i/S_i) for `lit`.
- **κ ∈ [κ_lo, κ_fix):** the corner `w0 = (den+num)·S_L − den·M`, `w1 = den·M − (den+num)·F_L`.
  At this corner the late arc sits exactly at its upper band end.
  - The binding arc's band condition *is* `P ≥ 0`.
  - The other 19 band conditions are quadratic forms in (num, den). Each is checked on
    [κ_lo, κ_fix] from the three Bernstein products (`bern`), by `grind`.
  - `pos_X` and `lo_X` are Bernstein certificates for the sign of P on [u, κ_fix] and [0, κ_lo].

### Mutations (scratch copies, each made the file FAIL)

1. P's constant term −27690 → −27689: `wit_s1c2_cons` and `bracket_s1c2_cons` fail.
2. s1c2 `cons` table, wGC F 176 → 177: the witness `grind` fails.
3. s2c2 `cons` threshold 94/325 → 940/3249: `bracket` fails and `safe` does not elaborate.

## Axioms

`#print axioms`, run in a companion file that was then deleted:
- `exact_*` (16), `Bridge.exact_*`, `audit_s1c2_cons_200`, `interior_s1c2_cons`, `cover_sound`,
  `elim2`: `[propext, Classical.choice, Quot.sound]`;
- `safe_antitone`: `[propext, Quot.sound]`;
- `bracket_*`, `verdict_κA`, `verdict_κE`: no axioms.

No `sorry`, `native_decide` or `axiom`.

## NOT covered

- Delays that vary from tick to tick: the model has one fixed delay per arc per run, as 7g does.
- The A0 rise, and arbitration (mutual exclusion).
- Kleene X and metastability.
- **The value of κ itself.** It is unmeasured; A withdrew 0.311.
- **The `cons` endpoints are not tied to any file.** These are the early SLOW_MIN and the late
  FAST_MAX + Elmore, taken from Bt3's per-corner windows (as in Bk1).
- **κ is not literally "≤ κ_ex" in the statements.** κ_ex is irrational, so each statement
  carries the quadratic `P < 0` together with the rational cut `u`, plus a 1e-10 bracket.
  The decimal values in the table come from floating-point root extraction.

## Files

- `Formal/Cells/OnNetlistArbKappaExact.lean`: the deliverable. It imports `ArbA0Fork` and
  `OnNetlistArbKappa`, and therefore needs Mathlib.
- **Generator scripts** (`/tmp/claude-0/probes/Bkx18/`): `exact.py` and `gen.py` enumerate the
  integer vectors and find the binding vector; `cert.py` makes the boxes, κ_lo, u and κ_fix;
  `emit.py` and `assemble.py` emit the Lean; `sanity.py` is an independent numeric check.
