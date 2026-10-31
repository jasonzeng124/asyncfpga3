# A / delay-corner: corner-correlated delay bounds

Files:
- `formal/lean/Formal/Core/Delay/Corner.lean`: **proved**, namespace `Formal.Core.Corner`.
  It imports `Formal.Core.Fidelity` and `Formal.Core.Delay.Pure` and copies nothing from them.
- `formal/lean/Wip/DelayCorner.lean`: open statements with 2 `sorry`s. Not built.
- this note.

Check (from `formal/lean`, with `export PATH=$HOME/.elan/bin:$PATH`):

    ../slot.sh lake env lean Formal/Core/Delay/Corner.lean

Status:
- The check exits 0 with no output at all: no errors and no warnings.
- The file has no `sorry`, `admit`, `axiom`, `native_decide` or `bv_decide`.
- `#print axioms` on every main theorem gives at most `[propext, Classical.choice, Quot.sound]`.
  It was run on a copy in `/tmp/delay-corner/`, because Corner has no .olean yet.
- Extra Mathlib import: `Mathlib.Tactic.Ring`, which is already built.
- Wip check: `(cat Formal/Core/Delay/Corner.lean; tail -n +2 Wip/DelayCorner.lean) > /tmp/delay-corner/W.lean`,
  then run `../slot.sh lake env lean /tmp/delay-corner/W.lean`. It elaborates, with exactly two `sorry` warnings.

## Why this probe

The sound band for one arc on its own is `[fast_min, slow_max]`
(`Fidelity.ofCorners`), and it is 3–4× wide: IMUX is 0.038 → 0.138 ns.
`DelayPure.bundle_two_wires` needs `ts + hiD ≤ loR`, meaning the data path at slow max must
beat the request path at fast min. With independent bands that condition essentially never
holds for a matched delay. On a real chip, though, every arc on the die shares **one** PVT point
and only local scatter differs from arc to arc.

## The model: named hypotheses

All of these are explicit arguments or structure fields. None is an axiom.

| name | Lean form | meaning |
|---|---|---|
| **H-affine** | `Arc` (`F ≤ S`, `0 ≤ F`), `Arc.at' c = lerp F S c = (1-c)F + cS` | the nominal delay is affine in a corner parameter `c ∈ [0,1]`: fast endpoint at `c=0`, slow endpoint at `c=1`. prjxray's form, a cornered intrinsic plus a corner-independent Elmore RC term, is affine, so it is covered |
| **SharedCorner** | `∃ c, 0 ≤ c ∧ c ≤ 1 ∧ …` quantifying over **both** channels (`bundle_corner`), or one `c` passed to every arc (`path_scatter`, `ruleE_two_corner`) | one corner for every arc on the die, at least for the duration of one handshake |
| **LocalScatter κ** | `Scat κ D d : (1-κ)·D ≤ d ∧ d ≤ (1+κ)·D` | each real delay is within `1 ± κ` of its nominal delay at the shared corner. In the trace theorems this is the band of a `DelayPure.Chan`, so the delay may also vary from one transition to the next inside it |
| **Proportional corner** (special case) | `D = s·P`, with `s > 0` shared and `P` = SDF prediction | the model behind skew.py's comment "the common 0.975 cancels" |
| additive scatter θ (rule A only) | `ad ≤ s·((1+κ)P + θ)` | an absolute per-path error in SDF ps. It represents the ~988 ps per-loop offset seen in the 128-ring fit |
| die gradient δ | `near_corner`: `|c' - c| ≤ δ` | an arc whose own corner is off the shared one. This becomes additive scatter `δ·(S-F)` |

## What is proved (exact names)

**(1) Reduction to an endpoint and ratio condition.**
- `bundle_ratio_affine`: suppose `(1+κ)·D_data + m ≤ (1-κ)·D_req` holds at `c=0` and at `c=1`,
  with both paths affine. Then it holds for every `c ∈ [0,1]`. The reason is that the guarded
  difference is itself affine in `c`.
- `bundle_ratio_affine_iff`: the condition holds for all `c` exactly when both endpoint checks pass.
- `bundle_ratio_chord`: affinity is more than the proof needs. It is enough that `D_data` is on
  or below its chord (convex) and `D_req` on or above its chord (concave), with `|κ| ≤ 1`.
- `monotone_not_enough`: a counterexample. Two nondecreasing curves satisfy the condition at both
  endpoints and violate it at `c = 1/2`, because the data path jumps early and the request path
  jumps late. **"Nominal monotone in c" is therefore not sufficient.** The precise requirement is
  the chord condition, or affinity.
- `bundle_scaled_iff`: in the proportional case the condition is independent of `s`.

**(2) Composition.**
- `pathAt_eq_lerp` and `pathAt_eq_pathArc`: a path of affine arcs taken at one shared `c` is
  affine, with endpoints `ΣF` and `ΣS` (`pathArc`).
- `path_scatter`: if every arc satisfies `Scat κ`, the path satisfies `Scat κ`. The worst-case
  bound does **not** shrink with length. The `1/√n` averaging is statistics, not a bound.
- `corner_refines_band`: the corner model lies inside `Fidelity.DelayBound.widen (band) κ`, so
  every independent-band result still applies.

**(3) Trace level, through `DelayPure`.**
- `bundle_corner`: the data wire and the request wire are `DelayPure.Chan` channels whose bands
  are `(1±κ)·D(c)` at a shared `c`. Given only the two endpoint checks
  `ts + (1+κ)·D.F ≤ (1-κ)·R.F` and `ts + (1+κ)·D.S ≤ (1-κ)·R.S`, the data is settled whenever the
  request is seen. The proof is `bundle_ratio_affine` composed with `DelayPure.bundle_two_wires`.
- `independent_implies_corner`: the old condition implies the new one, so the corner model never
  loses a design the independent model accepts.
- `imux_example`: the new condition is strictly weaker. Take one IMUX as data and two IMUX as the
  request, with κ = 0.2. Both corner checks pass, while the independent check fails by about 2.7×.

**(4) The project's guardbands.** These are rule E in `cells/verify/skew.py` (select stable before
the request) and rule A in `cells/verify/tighten.py` ("the request is the last thing a cell
emits ... by the review's guardband max(0.2*t_data, 200 ps)").
- `guardLo = 0.772`, `guardHi = 1.155`, `kappaE = 383/1927 ≈ 0.1988`.
- `guard_kappa_iff`: `(1+κ)·GUARD_LO ≤ (1-κ)·GUARD_HI ↔ κ ≤ kappaE`.
- `ruleE_sound`: suppose skew.py's guarded margin `GUARD_LO·P_req − GUARD_HI·P_sel > 0` on the
  divergent tails is positive. Under a proportional shared scale `s` and local scatter
  `κ ≤ 0.1988`, the select really arrives before the request. Two facts make this work:
  - The shared prefix `C` up to the divergence point is one physical delay, so it cancels exactly.
  - Only the *ratio* GUARD_HI/GUARD_LO matters. The mean −3.64% that the constants were centred on
    is the shared scale, and it drops out.
- `ruleE_tight`: for any `κ` in `(0.1988, 1)` there are predictions that pass rule E but are
  violated by delays the model allows. So **rule E's guardband corresponds to exactly κ ≈ 19.9%
  of symmetric local scatter.**
- `guard_totals_imp_tails`: guarding the full arrivals (skew.py's older behaviour) implies the
  guard on the tails, because `GUARD_LO ≤ GUARD_HI`. The older behaviour was conservative, never
  unsound.
- `ruleE_two_corner`: when the corners are affine but not proportional, as with prjxray (an RC
  term with no corner), a single SDF point is not scale-invariant. Passing rule E on the
  **fast-endpoint and slow-endpoint predictions** is then sufficient for every `c`.
- `ruleA_sound_rel`: rule A is sound exactly for `κ ≤ 1/11 ≈ 9.1%` with θ = 0.
  `ruleA_tight` shows nothing larger works: take `P_data = 1000` and `P_req = 1200` with `κ > 1/11`.
- `ruleA_sound`: with both kinds of scatter, rule A covers `κ ≤ 1/22` together with `θ ≤ 50 ps`.
- `near_corner`: a die gradient becomes additive scatter.

**(5) Testing κ from the rings.**
- `ring_kappa_lower`: take two rings on one die, so the scale `s` is shared, with ratios
  `rᵢ = measured/predicted`. Then `rᵢ − rⱼ ≤ κ·(rᵢ + rⱼ)`.
- `guard_refuted_by_7link_rings`: the 7-link population of `ro_many_top` spans 0.773 to 1.470
  (cells/hw/README.md). That alone forces `κ ≥ 0.697/2.243 ≈ 0.311`, which contradicts `κ = 0.1988`.

## What the guardband means under this model

1. **The rule-E guardband is a proof hypothesis of κ ≤ 19.9%.** It is sound under SharedCorner
   whenever every divergent tail's SDF error stays within ±19.9% after the common scale is removed.
   The shared-scale part is genuinely free: `ruleE_sound` holds for every `s > 0`. This formally
   justifies skew.py's design choices to cancel the common 0.975 and to drop the shared prefix
   `t_c`.
2. **The ring data says κ = 19.9% is not a worst case.** The 7-link rings alone need κ ≥ 31%
   (`guard_refuted_by_7link_rings`). By the percentiles quoted in tighten.py's header (from the 128 rings), |residual| reaches 25.2% at p90
   and 34.6% at max. So 19.9% covers somewhere between the 52nd percentile (where 8.5% sits) and
   the 90th. skew.py itself calls the constants a 95/95 tolerance from n = 5, and that does not
   survive n = 128. Three caveats keep this from being a hard refutation:
   - Rings measure the **absolute** loop delay against the SDF. Rule E compares the **difference**
     of two tails. Correlated errors on the two tails would shrink the effective κ. tighten.py says
     the same: "Do not quote the ring numbers as a bound on rule A's margin without measuring the
     differential directly".
   - The 988 ps offset fit suggests part of the short-ring excess is an additive per-loop term (θ),
     not κ. With the offset removed, coverage only moves from 52% to 60% (README).
   - Rule E's tails are short, and short is where the ring scatter is largest.
3. **Rule A is weaker still.** Its 20% term covers κ ≤ 9.1% (`ruleA_sound_rel`, `ruleA_tight`),
   which is roughly the median ring scatter and not a bound. CLAUDE.md already says "8.5% is the
   median ring scatter, not a guardband". Rule A's floor of 200 ps buys θ ≤ 50 ps on top of
   κ ≤ 4.5%.
4. **An actionable change follows from `ruleE_two_corner`.** Once the board-fidelity GLS or a
   prjxray-based STA has both corner columns, run the rule-E and rule-A checks against **both** the
   fast and the slow predictions. Passing both is a proof for every intermediate corner, under
   H-affine. The present single nextpnr SDF covers only the proportional sub-case.

## How each hypothesis can be tested

- **LocalScatter κ (path level).** On one die and in one session, every ring shares `s`.
  - Estimator: `ŝ` = median of `rᵢ` (per length class, or after the two-parameter offset fit).
  - Then take `κ̂_q` = q-quantile of `|rᵢ/ŝ − 1|`.
  - The distribution-free lower bound is `(r_max − r_min)/(r_max + r_min)` (`ring_kappa_lower`).
  - Report `κ̂` per length class. Short rings are the relevant class for rule-E tails.
  - Rings bound *path*-level scatter. Arc-level κ is at least as large (`path_scatter` goes one way
    only), but path level is all the theorems need.
  - The raw per-ring data (`build/hw/ro_many_top/raw/gNN.log`) is not in the tree, so `κ̂_q` could
    not be computed here.
  - The **differential** κ needs a different rig: two rings sharing a launch node, or the
    "walk a matched delay to failure" experiment in cells/hw/README.md.
- **SharedCorner.** Existing evidence for it:
  - permutation tests by slot and by group show no clustering (p = 0.73 and 0.66);
  - repeatability across windows is 0.052%;
  - self-heating is ≤ 0.011%.

  So no regional or temporal corner variation is visible at this resolution, and δ ≈ 0. The next
  test: measure the 128 rings at two die temperatures. SharedCorner plus proportional predicts the
  same ratio `period(T₂)/period(T₁)` for every ring. The spread of that ratio across rings
  estimates the non-shared part (δ in `near_corner`).
- **H-affine and proportional.** Use two ring types with different arc mixes, for example
  LUT-heavy against long-wire-heavy, at three or more temperatures or VCCINT points.
  - H-affine predicts that `(period_A, period_B)` are collinear.
  - Proportional predicts the line passes through the origin.
  - prjxray's corner-independent RC term predicts a nonzero intercept, which would favour
    `ruleE_two_corner` over a single-SDF check.
- **GLS.** In the board-fidelity GLS, draw one `c` per run and an `ε ∈ [−κ, κ]` per arc. The
  theorems predict zero rule-E failures when both endpoint checks pass with `κ_check ≥ κ_draw`.
  `ruleE_tight` gives the negative control: at `κ_draw > 0.199`, a design that just meets rule E
  must be breakable.

## Fidelity notes

- *Affine in one scalar c* is an idealisation. Process, voltage and temperature are three axes,
  and different arc types (pip buffer, wire RC, LUT pin) respond to each with different
  sensitivities. A die is therefore really a point in a multidimensional corner space, and
  prjxray's fast and slow numbers are two corners of it. `bundle_ratio_chord` is the right
  generalisation: any family in which data delays lie below their chord and request delays above
  it.
  - When request and data use the *same arc types in the same proportions* (a matched delay built
    from the same routing), the paths are nearly proportional and the issue vanishes.
  - Matched delays built from LUT1 chains against data cones dominated by routing are exactly where
    it matters.
- Local scatter as a deterministic `±κ` is a worst case. The silicon reality is a distribution, and
  the population and union-bound form is discussed in the Wip file (it needs measure theory).
- prjxray's fast and slow columns are speed-grade process corners. The die's real `c` is unknown,
  which is why every theorem quantifies over it.
- The `Chan` band at a fixed `c` also absorbs slow temperature drift, because the delay may move
  within its band from transition to transition. `Wip.slow_pulse_survives` sketches the sharper
  bounded-drift version.

## What does not check (Wip/DelayCorner.lean)

- `ruleA_two_corner` (`sorry`): rule A at both endpoints implies rule A at every `c`. The proof
  rests on `max(t/5, 200)` being convex. About 1 hour.
- `slow_pulse_survives` (`sorry`): with a bounded drift rate ρ, a pulse keeps width `(1−ρ)·w`.
  Needs an sSup or IVT argument, and `ConditionallyCompleteLattice` is not built. Half a day once
  built.
- Population (probabilistic) LocalScatter: needs MeasureTheory, so it is described in text only.

## Verdict

**Works.** The corner-correlated model is about 30 elementary theorems, all `linarith`/`nlinarith`,
and it plugs straight into `DelayPure.bundle_two_wires` and `Fidelity.widen`.
- It turns the never-closing independent condition into two endpoint checks.
- It formally justifies skew.py's scale cancellation and prefix cancellation.
- It pins rule E's guardband to κ = 19.9% and rule A's to κ = 9.1%, both tight.
- It shows, from the published ring statistics, that κ = 19.9% is a population quantile rather
  than a worst case.

Effort to finish: about 1 day. That covers the two Wip items and a κ̂ table from the raw ring logs,
and it excludes the new experiments.

What it buys:
- A bundling proof that can actually close on this part.
- An exact statement of what the guardbands assume.
- A concrete recommendation: run rule E/A at both corner columns.
- A falsifiable set of board tests: the temperature-ratio spread for SharedCorner, collinearity for
  H-affine, and a differential rig for the κ that rule E really uses.
