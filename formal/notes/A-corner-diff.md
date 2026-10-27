# A / corner-diff: rules E and A under scatter on the difference, and the ring bound is attained

This note follows up `formal/notes/A-kappa.md`, section "Lean status", which proposed two lemmas:
`ruleE_sound_diff` and `ring_kappa_attained`. Both are now proved, together with the rule A analogues and
the "per-path implies difference, but not the reverse" pair.

File: `formal/lean/Formal/Core/Delay/CornerDiff.lean`, namespace `Formal.Core.CornerDiff`.
- It imports `Formal.Core.Delay.Corner` and `Formal.Core.Substrate.CornerNat`. Neither file was edited.
- It reuses `Scat`, `guardLo`, `guardHi`, `kappaE`, `guard_kappa_iff`, `ruleE_tight` and
  `ring_kappa_lower`.
- Nothing was put in `Wip/`, because nothing is left unproved.

## Check

    cd formal/lean && ../check.sh Formal/Core/Delay/CornerDiff.lean
    # [check] textual scan / lean / axiom audit: 450 declarations checked / [check] OK

The check passes cleanly: no sorry, no axiom, no native_decide, no warnings. Imports are Mathlib-free
beyond what `Corner.lean` already pulls in.

## The hypothesis

`DiffScat κd s Pa Pb da db`: `|(db − da) − s·(Pb − Pa)| ≤ κd·s·(Pa + Pb)`, written as two inequalities.
- Path `a` is the early one (data or select). Path `b` is the late one (request).
- `s > 0` is the shared proportional scale.
- With `d = sP(1+ε)` this gives `κd = |εb·Pb − εa·Pa|/(Pa+Pb)`. That is exactly `kappa.py pairs`'
  `κ_diff`, so the tool and the theorem measure the same number.
- **Why the normaliser is the sum.** Per-path κ then implies `κd = κ` with the same number, so the rule
  limits do not change meaning between the two models. With `Pb` alone as the normaliser, the map would
  depend on `Pa/Pb`.

`DiffLow` is only the lower half: the late path is late by at least `s((Pb−Pa) − κd(Pa+Pb))`. The
soundness theorems assume only `DiffLow`, so they are stronger. `DiffScat.low` connects the two.

## Theorems

| name | statement |
|---|---|
| `ruleE_sound_diff` | skew.py guard `0 < guardLo·Pr − guardHi·Ps`, `Ps ≥ 0`, `DiffLow κd`, `κd ≤ kappaE` (= 383/1927 ≈ 0.1988) ⇒ `C + as_ < C + ar`. No `κd ≥ 0` is needed. |
| `ruleE_diff_tight` | For **every** `κd > kappaE` there is a guarded pair with full two-sided `DiffScat κd` in which the select arrives strictly after the request. So the limit is exact. |
| `ruleA_sound_diff` | rule A (`Pr ≥ Pd + max(Pd/5, 200)`), `DiffLow κd`, `κd ≤ 1/11` ⇒ `ad ≤ ar`. |
| `ruleA_diff_tight` | For `κd > 1/11`, the 1000/1200 ps pair admits `DiffScat κd` with data after request. |
| `ruleA_sound_diff_mixed` | Additive difference term `θd ≤ 100` ps (rule A's 50 ps on each tail) and `κd ≤ 1/22` ⇒ `ad ≤ ar`. `ruleA_diff_mixed_tight`: with `θd = 100`, any `κd > 1/22` fails on 1000/1200. |
| `diffScat_of_scat` | `Scat κ (s·Pa) da ∧ Scat κ (s·Pb) db ⇒ DiffScat κ s Pa Pb da db`, so `f(κ) = κ`. |
| `diff_of_scat_sharp` | That map is attained: the early tail slow by κ and the late tail fast by κ give deviation exactly `−κ·s(Pa+Pb)`. So no `f(κ) < κ` holds. |
| `ruleE_sound_of_diff` | `Corner.ruleE_sound` follows as a corollary, which confirms the difference hypothesis is the weaker one. |
| `diff_not_imp_scat` | For every `K`, there are perfectly correlated tails (equal P, equal d) with `κd = 0` whose two tails both violate `Scat K`. So no `g` gives `DiffScat κd ⇒ Scat (g κd)`. |
| `rings_refute_path_not_diff` | Concrete instance. At `s = 2.243/2`, the 7-link ring ratios 1.470 and 0.773 are realised at per-path `κ = 0.697/2.243 ≈ 0.311 > kappaE`. On the same die and at that κ, a guarded tail pair (`Pr = 2`, `Ps = 1`) is correlated so that `κd = 0`, and `ruleE_sound_diff` proves the select arrives first. |
| `ring_kappa_attained` | At `s = (ri+rj)/2` and `κ = (ri−rj)/(ri+rj)`, both `Scat κ s ri` and `Scat κ s rj` hold. |
| `ring_kappa_attained_all` | The same holds for every ratio in `[rj, ri]`, so further rings within the range cannot raise the bound. |
| `ring_kappa_iff` | For `κ ∈ [−1, 1]` and `rj ≤ ri`: `(∃ s, Scat κ s ri ∧ Scat κ s rj) ↔ ri − rj ≤ κ(ri + rj)`. |
| `ring_kappa_below_infeasible` | For `κ < (ri−rj)/(ri+rj)`, no shared scale exists. |

## What this means

- **The rings refute the per-path hypothesis, not the difference hypothesis.**
  - The ring populations falsify per-path LocalScatter at rule E's and rule A's κ
    (`guard_refuted_by_7link_rings`, and `ring_kappa_iff` makes 0.311 the exact minimum).
  - The rules only need `κd`.
  - Per-path ⇒ difference holds with the same constant, and that constant is sharp. The reverse fails
    for every bound.
  - So a large absolute κ, which is all ring data can measure, is logically compatible with `κd = 0`.
    Ring data says nothing about `κd`, in either direction.
- **The number to measure is `κd ≤ 0.1988` (rule E) and `κd ≤ 1/11` (rule A, relative) on real tail
  pairs**, or `κd ≤ 1/22` together with `θd ≤ 100 ps` (rule A, mixed).
  - The differential tail ring in A-kappa.md measures exactly `DiffScat`'s quantity.
  - The shared body cancels exactly, as the prefix `C` does in `ruleE_sound_diff`.
- **`ring_kappa_attained`.** The tool's `κ_min` is the exact minimum consistent with ratio data under
  the model, not merely a lower bound.

## Fidelity and limits

- **Proportional corner only.** `D = s·P` with one `s`. The affine (two-endpoint) form of
  `Corner.ruleE_two_corner` is not lifted to `DiffScat`.
  - Lifting it is about 30 minutes of work: state `DiffLow` with `R.at' c`, `Sl.at' c` in place of
    `s·P`, and reuse `lerp_ge_of_ends` as `ruleE_two_corner` does.
  - It is not done here.
- **`DiffScat` is a per-pair hypothesis.** It is not derived from any arc-level model. Correlation
  between tails (shared arc types, neighbourhood, the same route) is what would make it small. That is
  an empirical claim, testable only with the differential tail ring (A-kappa.md, "What would settle
  it"), or in GLS on prjxray data only if that data models correlated variation (it does not today).
- **Edge direction.** As in A-kappa.md, ring κ mixes rise and fall. A tail pair sees one edge, so
  `κd` should be measured per edge.
- **No ℕ-substrate version.** `CornerNat.lean` is imported but not used. A decidable ℕ `DiffScat`
  check for the timing checker would be a short follow-up (about 1 h).

## Verdict

**Works.** Both proposed lemmas are proved, plus the rule A versions, the exact tightness of every
limit, and the one-way implication with a counterexample for the converse.

What remains is data, not proofs: `κd` on real tail pairs has never been measured.
