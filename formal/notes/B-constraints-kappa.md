# B / constraints-kappa (probe Bk2): the exact corner-model form of the constraint shapes

File: `formal/lean/Formal/Cells/ConstraintsKappa.lean` (imports only
`Formal.Core.Substrate.CornerNat`; it uses A's `Kappa`, `CArc`, `Corner`, `Scat`,
`CornerModel.Realizes`, `pathDelay`, `EndpointOK`, `scat_path`, `cdiv`, `sumOver`; it copies
none of them). Proposed JSON patch (not applied):
`/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/Bk2/kappa_check.patch`.

## Check status

CornerNat imports Mathlib, and Mathlib was not built during this probe, so the real
file could NOT be checked with `lake env lean`. What was checked: the file's body,
appended to a core-only copy of CornerNat (Mathlib imports removed; the CornerNat proofs
that need `nlinarith`/`ring` fail there and become `sorry`, only in that test copy), with
`slot.sh lean -DautoImplicit=false`. My part of that file has no errors and no warnings.
`#print axioms`: the counter-examples need no axioms (or only propext/Quot.sound). The
general theorems show `sorryAx`, and it comes only from the test copy's `scat_path`. The
tactics in my part are core-only (`omega`, `decide`, `simp only`, `rw`), so they should
not change under Mathlib. **To do once Mathlib is built:**
`cd formal/lean && ../slot.sh lake env lean -DautoImplicit=false Formal/Cells/ConstraintsKappa.lean`.

## Problem statement

Shape: `ΣP + a ≤ ΣQ + b`. Here `P` and `Q` are lists of arc ids, each arc has FAST and SLOW
endpoints `F ≤ S`, and `a` and `b` are whole-ps constants: the margin plus the env/cell_param
bounds, taken at hi on the data side and at lo on the request side. The model is A's:
H_ENDPOINTS, H_AFFINE, H_SHARED_CORNER (one corner `c` for every arc) and H_SCATTER κ
(each delay is within `1 ± κ` of its nominal value at `c`), with delays in ℕ ps.
`AllOK M P Q a b` says the form holds for every realization.

Closed-form check, `GenOK κ (path P) (path Q) a b`. For each endpoint
`s ∈ {FAST, SLOW}`:

    (den+num)·Σ_P ep_s + den·a  ≤  (den−num)·Σ_Q ep_s + den·b        (κ = num/den)

With `b = 0` this is A's `EndpointOK` (`gen_iff_endpointOK`).

## Results (assumed / proved / not covered)

- `allOK_of_gen` (soundness). Assumes nothing beyond the model. Proves that `GenOK`
  implies `AllOK`. It extends A's `bundle_realizes` to a request-side constant `b`, which
  the JSON needs: most request paths carry an `env` term such as `Won` or `E`, and
  `EndpointOK`'s `m : ℕ` cannot express it.
- `worst_realizes`, `worst_P`, `worst_Q`, `endpointNat_of_allOK` (tightness/necessity).
  Assumes **H_DISJ** (no arc id on both sides). For each endpoint, the realization
  `worst` attains the integer worst case `EndpointNat`. That realization takes the
  corner at the endpoint, puts data arcs at `⌊(1+κ)x⌋` and every other arc at `⌈(1−κ)x⌉`.
  So `AllOK` implies `EndpointNat`.
- `gen_relaxed_of_endpointNat`, `sandwich` (no H_DIV). The ℕ-exact condition lies between
  `GenOK a b` (sufficient) and `GenOK` with `(|P|+|Q|)(den−1)` added on the right
  (necessary). That gap is less than 1 ps per arc.
- `allOK_iff_gen`, `allOK_iff_endpointOK` (EXACT). Assumes H_DISJ and **H_DIV**
  (`(1+κ)x` on data arcs and `(1−κ)x` on request arcs are whole ps). Proves
  `AllOK ↔ GenOK`.
  - Non-vacuity, `witness_div` / `witness_exact`: data `[40,140]`, request `[85,235]`,
    κ = 1/5, margin 20 meets every hypothesis. The check is tight at both endpoints, the
    SLOW worst realization gives `168 + 20 = 188`, and margin 21 fails.
- `allOK_cancel` (exact). A common prefix `C` (the same arc ids, hence the same delays)
  drops out: `AllOK (C++P) (C++Q) ↔ AllOK P Q`. This is the DiffScat situation, where only
  the divergent tails count.
  - `endpointOK_iff_diff`: `EndpointOK` is exactly `den·(R−D) ≥ num·(R+D) + den·m` at each
    endpoint. That is A's `DiffLow` with `κd = κ` (per-arc κ implies `κd = κ`,
    `diffScat_of_scat`), evaluated at the two corner endpoints.
- Counter-examples (all by `decide`):
  - `nat_rounding_not_exact`: without H_DIV, `EndpointOK` is not necessary (arcs `[1,1]`,
    κ = 1/5: every realization gives 1 ≤ 1, yet `6 ≤ 4` fails).
  - `endpointNat_not_sufficient`: the rounded endpoint check is NOT sufficient. With arcs
    `[0,3]`, κ = 1/5, both endpoints pass, but at the interior corner `c = 5/6` the delays
    3 vs 2 are admissible and break the form. So integer rounding at the endpoints only is
    unsound; use the unrounded `GenOK`.
  - `uncancelled_pessimistic`: without cancellation, a common IMUX makes `EndpointOK` fail
    although the form holds trivially.
  - `box_unsound_with_kappa`, `one_corner_unsound_with_kappa`, `slow_only_unsound`: see
    the next section.
- NOT covered:
  - An ℕ-exact closed form without H_DIV. The exact condition ranges over all rational
    corners; the sandwich bounds it from both sides.
  - Difference-only (DiffScat) hypotheses on the tails, which are in ℝ in A's files.
  - Per-traversal scatter of one element.

Current κ: unmeasured on the current toolchain. A-kappa.md's 2026-10-27 correction says
the 0.311 came from the LUT-permutation SDF bug; the comparable rings agree to 1.1% /
6.7%. κ = 0 reproduces the old one-column check.

## Verdict on the JSON `corner.rule` (114 `1C` entries + 2 `1C_both_corners_required`)

1. "evaluate in the SAME column at FAST_MIN and at SLOW_MAX (H_ONE_CORNER)": this is `GenOK`
   at κ = 0. It is right only if κ = 0, and unsound for κ > 0
   (`one_corner_unsound_with_kappa`).
2. "or as A's EndpointOK with kappa": right in spirit, and exact under H_DISJ + H_DIV. Two
   gaps: request-side env constants need `GenOK`'s `b`, and `conventions.form`'s
   `margin + |P| + |Q|` is the per-arc integer band form (`bundle_band`, for tcheck's Win
   channels). The realization-level check does not need it.
3. "box (every hi at SLOW_MAX, every lo at FAST_MIN) is always sound": **wrong under A's
   model** for κ > 0 (`box_unsound_with_kappa`: 10 vs 10 passes the box, but 12 vs 8 is
   admissible). The box is sound only with κ applied, `(1+κ)S` vs `(1−κ)F` (A's
   `independent_implies_endpoint`).
4. "A SLOW_MAX-only check must add the guard As − Af/k (fast_neg_iff)": this guard belongs
   to the H_WIRE_RATIO model, where every wire is exactly `k·` its slow value. A's model
   has per-arc F/S, and there the FAST endpoint check is the exact replacement. A SLOW-only
   check is unsound even at κ = 0 (`slow_only_unsound`). Recommendation: drop the guard
   wording for A-model checks and keep it only as the H_WIRE_RATIO alternative.
5. Never mixing rise = FAST with fall = SLOW: still right. `{I0|I1}` taken as max (data) or
   min (request) per endpoint is exact, because the pin choice commutes with the
   FAST ∧ SLOW conjunction.

Shared arcs. A key-match finds 33 forms with the same arc label on both sides
(setup_pulse, env_latency, reset, iso_*, ...). None should cancel automatically:
- setup_pulse's enable wire is two traversals (rise, then fall);
- `{I0|I1}` on the two sides can be different pins;
- the forms already start at a common launch.

A's model gives one delay per arc id, so cancelling such an arc would assume
H_SAME_TRAVERSAL (rise = fall and no per-traversal scatter). The patch therefore emits
`cancel: []` everywhere and states this rule.

## Proposed patch (in `/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/Bk2/kappa_check.patch`, generator + validator only)

- `CORNER_1C.rule` and `conventions.corner_rule` are rewritten per the verdict above, and
  a new `conventions.kappa_check` is added.
- Each entry gets `kappa_check`: `null` for the 11 entries with mode n/a or no forms;
  otherwise:

      {"check": "GenOK", "formula": ..., "constants": ..., "pins": ..., "cancel_rule": ...,
       "exactness": ..., "band_form": ..., "kappa": ...,
       "forms": [{"pairs", "data": [{"arcs", "constants"}], "request": [...], "cancel": []}],
       "lean": [allOK_of_gen, allOK_iff_gen, sandwich, allOK_cancel]}

- The validator requires the field, checks that `forms` lengths match, and checks the
  Lean names.
- I ran the patched generator in scratch: 123 entries, 112 with `kappa_check`. The patched
  validator's only errors are "ConstraintsKappa.lean is untracked" (448 = 112 × 4 refs),
  which clear once the file is committed.
