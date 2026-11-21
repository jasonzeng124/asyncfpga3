# A / corner-code: rule A exactly as tighten.py computes it

Files:
- `formal/lean/Formal/Core/Delay/CornerCode.lean`, namespace `Formal.Core.CornerCode`.
  It imports Mathlib only (`Algebra.Order.Archimedean.Real.Basic`, `Data.Nat.Cast.Order.Field`,
  `Tactic.Linarith`, `Tactic.NormNum`, `Tactic.Positivity`, `Tactic.Ring`), not Corner.lean. The corner model is restated inline with the same
  hypothesis shape as `Corner.ruleA_sound_rel`.
- this note.

Check (from `formal/`): `./check.sh Formal/Core/Delay/CornerCode.lean` →
`[audit] 21 declarations checked`, `[check] OK`. Also `../slot.sh lake env lean
Formal/Core/Delay/CornerCode.lean` from `formal/lean`: no output (no errors, no warnings).

## Problem

The audit (`origin/claude/audit:audit/findings/A.md`, first row, OVERSTATED) found this.
`Corner.ruleA_sound_rel` / `ruleA_tight` prove "rule A is sound iff κ ≤ 1/11", but they prove
it for the real-valued rule `Pd + max (Pd/5) 200 ≤ Pr`. `cells/verify/tighten.py` works in
integer ps and truncates the 20 % term (`req_guard`, l.1106). So the code accepts
`(t_l, t_e) = (1004, 1204)`, because `int(200.8) = 200`. That pair breaks at κ = 1/11. The
auditor's claimed exact limit for the code is 25/276 ≈ 0.09058.

## What the code does (read, not proved)

- `parse_sdf`: every IOPATH and INTERCONNECT delay goes through `int(...)`, so the arrivals
  are natural numbers.
- `req_guard(p, t) = max(int(0.2 * t), 200) + SLACK`.
- `check`: `margin = t_e - t_l - guard(t_l)`. In `rule_a_links`, `want > n` (the verdict
  "PAD ... VIOLATION") happens exactly when `margin < 0`. So a pair passes iff
  `t_l + guard(t_l) ≤ t_e`. That is `pass S te tl` in the Lean file. It is the same as shard
  C's `Formal.Timing.Rules.ruleAPass` at `S = 0`.
- `SLACK` is 0 by default. Only `verify/resize.sh`, and `hw/tighten_loop.sh` when
  `BD_TIGHTEN_SLACK` is set, pass `--slack`, and they do it for the length search. The gate
  (check.sh) runs with SLACK = 0. Both cases are covered below.
- **Float truncation.** For integers `0 ≤ t < 2^50`, `int(0.2*t) = t // 5`. This is NOT proved
  in Lean. The argument: the double nearest 0.2 is `0.2 + δ` with `δ ≈ 1.11e-17 > 0`. Write
  `t = 5k + j`. The exact product lies in `[k, k + 0.8 + 0.0125]`. Both `k` and `k+1` are
  doubles, rounding is monotone, and a rounding error near ≤ 2^48 is ≤ 0.03. So the rounded
  product lies in `[k, k+1)` and truncates to `k`. Scan: exhaustive over 0..10^7, plus
  10^6 random values below 2^50 and the last 10^5 below 2^50, with 0 mismatches. Mismatches do
  appear near 2^53, which is far beyond any path delay. The Lean model therefore uses `tl / 5`
  on ℕ (floor).

## Model (assumed)

Proportional shared corner, the same as `Corner.ruleA_sound_rel`. There is one scale `s > 0`
for the die. The real data delay is `ad ≤ s·(1+κ)·t_l` and the real request delay is
`ar ≥ s·(1-κ)·t_e`. Scatter is purely relative (θ = 0). `t_l` and `t_e` are the SDF
longest/shortest-walk arrivals.

## Proved (no sorry, axiom, native_decide or bv_decide)

- `pass_ratio`: `pass 0 te tl → 301·tl ≤ 251·te`, by omega on ℕ.
- `ruleA_code_sound`: if `κ ≤ 25/276`, then for every slack `S` a passing pair gives `ad ≤ ar`.
- `ruleA_code_tight` and `ruleA_code_unsound_1_11`: for κ > 25/276, the pair (1004, 1204)
  passes at S = 0 and fails with s = 1. κ = 1/11 is one such case.
- `ruleA_code_iff` (nominal) and `ruleA_code_model_iff` (with s, ad, ar quantified): at
  S = 0 the code's rule A is sound **iff κ ≤ 25/276**. **The auditor's 25/276 is confirmed as
  the exact threshold.**
- `ruleA_code_at`: the exact threshold for each `t_l` is `κ·(2t_l + g) ≤ g`, where
  `g = guard S t_l`.
  - Small `t` (`guard_small`, t_l ≤ 1004): the 200 ps floor dominates and the threshold is
    `100/(t_l+100)`. It is 1 at t_l = 0 and falls to its minimum 25/276 at t_l = 1004. This
    is the worst point overall.
  - Large `t` (`guard_large`, t_l ≥ 1005): `g = ⌊t_l/5⌋ ≥ (t_l−4)/5`, so the threshold is at
    least `(t_l−4)/(11t_l−4) > 25/276`. It tends to 1/11 for t_l ≡ 4 (mod 5).
- `ruleA_slack_sound`: with `S ≥ 1`, rule A is sound for κ ≤ 1/11, because one ps of slack
  covers the ≤ 4/5 ps truncation loss.
- `ruleA_slack_tight`: for every S and every κ > 1/11, some pair passes and fails. The pair is
  `t_l = 5q+4` with q large. So the threshold 1/11 is exact with slack, but no single point
  attains it.
- `real_imp_code` and `code_not_imp_real`: the real-valued rule implies the code's rule, and
  the converse fails at (1004, 1204).

Suggested FEASIBILITY wording: "the gate (SLACK = 0) is sound iff κ ≤ 25/276 ≈ 9.06 %. The real-valued idealisation, and the search with SLACK ≥ 1, are sound iff κ ≤ 1/11."

## Not covered

- That `int(0.2*t)` equals floor. This is a float argument, stated above but not proved in
  Lean.
- Affine (two-endpoint) corners. Rule A reads one SDF number per arc, so only the
  proportional corner is modelled.
- The additive scatter θ of `Corner.ruleA_sound`. The auditor reports that the κ ≤ 1/22,
  θ ≤ 50 version fails at (1004, 1204) for the code as well. It is not redone here.
- The bundled-channel `upstream_lag`. `check_bundled` adds `upstream_lag` to the margin
  after the guard has been computed on the pre-lag `t_l`, so the guard is on a smaller delay
  than the data path. Not modelled.
- Negative `--slack` values, which `int()` accepts. `pass_zero` needs S ≥ 0, which ℕ enforces.
- Whether the SDF walks are the real extreme paths, and whether the real silicon fits the
  shared-corner / scatter-κ model at all.

## Lead actions

- Root import: `import Formal.Core.Delay.CornerCode` in Formal.lean. No lakefile change.
- Update FEASIBILITY §3b to use the wording above.
