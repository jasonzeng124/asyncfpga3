# H_RUNT(w) forbids pulses on narrow-window LUT pins (shard B, 2026-11-07)

**Problem, plainly.** The owner's H_RUNT(w) (decision 2): "a LUT input pulse narrower than w ps does not propagate
to its output". `SpecRunt.GateOKRuntOn` (shard A) states it as: a LUT pin's read time never lands inside a pulse of
its source narrower than w. A read time must also be admissible: `t - f t ∈ [dlo, dhi]`. If a source pulse
`[a, b)` has `dhi - dlo < b - a < w`, at `t = a + dhi` every admissible read time is inside the pulse, so NO read
map exists: the behaviour is removed from the statement. The pulse is forbidden, not filtered. Audit row T9 found
the extreme case (zero-delay pins, window width 0); restricting the filter to LUT pins (A, 2026-11-06) removed that
case but not this one.

**Lean (standard axioms, check.sh OK):** `Formal/Cells/RuntForbid.lean`
- `runt_forbids`: the generic fact (any gate class L, pin, corner).
- `toy_no_clean_step`: a 4-gate toy at g = 1, κ = 0 (fixed arcs; `in` -> 10 ps and 25 ps copies -> XOR LUT `z`
  -> LUT `y` through a 5 ps arc): in every `BehavesRunt 20` behaviour the environment input never makes a clean
  step (constant 30 ps on both sides, at time ≥ 30), because the XOR's 15 ps reconvergence hazard would sit on
  `y`'s pin. `toy_step_w0`: under the frozen `Behaves` (w = 0) that step is a behaviour.
So H_RUNT(w) as written can constrain the ENVIRONMENT (a vacuity risk of the T5/T9 kind): a statement
`NetCorrectSeqRunt 20` holds for any environment move whose consequences contain such a forced pulse, whatever the
circuit then does.

**On THE target (Python, untrusted; `tools-B/ps/lutwin.py lean/Formal/Target/NetPS`):** of 48,293 support LUT pins,
the number whose admissible integer read delays (g = 1) are fewer than 20:

| corner c | κ = 0 | κ = 0.05 | κ ≥ 0.1 |
|---|---|---|---|
| 0 (fast) | 3,317 | 3,040 | 0 |
| 0.5 | 2,307 | 0 | 0 |
| 1 (slow) | 0 | 0 | 0 |

So the hole is confined to small κ near the fast corner, which is where the headline (w = 20, the largest proven κ)
would be stated if the frontier is reported per corner; at κ ≥ 0.1 every LUT pin's window has ≥ 20 integer delays
and the read-map form can always skip a sub-20 pulse (a window of W+1 points minus a pulse of < W+1 points leaves
a point; monotonicity is kept by reading before, then after the pulse).

**Not shown:** that the target's admissible behaviours carry pulses of width in [window, 20) on those pins' sources
(that is what would make a difference: forced -> vacuity for that environment; optional -> behaviours dropped).

**Proposed fix (for shard A, owner of SpecRunt.lean):** state H_RUNT as a filter on the value read, not a ban on the
read time. For a LUT pin, the gate reads `filt w s` instead of `s`, where `filt w s t = s t` if `t` lies in a
maximal constant run of `s` of length ≥ w (or one that starts at 0), and otherwise `filt w s (a - 1)` with `a` the
start of `t`'s run (well-founded: `a ≤ t`). It is total (every `GateOK` read map stays a read map), so it never
removes a behaviour; it suppresses a whole train of sub-w pulses (holding the last long-run value), which is the
owner's wording; and with w = 0 it is the identity (the frozen statement). Alternative with less change: keep
`NoRuntRead` but exempt read times whose whole admissible window lies in the pulse, reading the pre-pulse value
there. Either way the claim `NetCorrectSeq → NetCorrectSeqRunt w` must be re-proved: with a filter it is no longer
a restriction of behaviours, so the implication fails in general (a filtered read sees different values); the
owner's "w = 0 is the pessimistic bound" then has to come from a monotonicity argument, or the two statements are
reported side by side.
