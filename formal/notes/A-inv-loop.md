# A-inv-loop: the involution OR loop: pulse-width orbit, critical runt, unbounded resolution

Probe InvLoop, shard A, session 2026-10-29. File: `formal/lean/Formal/Core/Delay/InvolutionLoop.lean`
(imports only A's `Involution` plus `Mathlib.Algebra.Order.Archimedean.Real.Basic` for `sSup`; no
topology library). Scratch: `scratchpad/InvLoop/{ws.py,asym.py}` (Float checks, not theorems).

STATUS: done. `InvolutionLoop.lean` checked: `formal/check.sh Formal/Core/Delay/InvolutionLoop.lean` → `[audit] 197 declarations checked`, `[check] OK` (docstring-only edit after). Bridge to B's `orb` written but unchecked: `Wip/InvLoop/Bridge.lean` (needs Mathlib topology).

## The setting (what is assumed)

The loop of B's `CElemInvolution` / `ArbInvolution.stF_runt`: the zero-time OR of a runt `b = [0, s)`
and the loop output `q`, followed by ONE involution channel `P` (A's `InvolutionPair`: LUT and
feedback wire lumped), whose output is `q`. Every hypothesis is a field of `InvolutionPair`
(strictly increasing `δ↑, δ↓`, the involution law, `δ(0) > 0`, `δ < δ∞`). No continuity,
concavity or limit hypothesis is used: the continuity needed is DERIVED from monotonicity plus
the involution's surjectivity (`loc_cont`).

- `δ∞↑`, `δ∞↓` are A's fields `infUp`, `infDown`: the delay of a transition after a long quiet
  period (the first transition, `T = ∞`). A transport GLS with loop delay TLOOP corresponds to
  reading TLOOP as `δ∞` (the SDF number is the delay of an isolated edge; with no rise/fall split,
  `δ∞↑ = δ∞↓ = TLOOP`). That identification is a modelling reading, not a theorem.
- `lo s n` is exactly B's recurrence `orb P s n` (copied, same equations; the `rfl` bridge to B's
  `orb` is not written because B's module needs Mathlib topology, unbuilt when this ran).
  `wd s n = lo s (n+1) - lo s n` are the pulse widths of `q` (even `n` high, odd `n` low).
  `Chain s n` (= B's `chainS`) says the first `n` widths are positive. The first `m` with
  `wd s m ≤ 0` is the first cancellation; by B's `loop_orb` `q` is then constant after the last
  surviving transition: 1 if `m` is odd (latched), 0 if `m` is even (lost). The link to B's
  signal-level statement is by B's theorem, not re-proved here.

## What is proved

1. **Width recurrence and expansion.** `wd (n+1) = δ_n(-wd n) - wd n` (`wd_succ`). The half-lap
   maps `w ↦ δ(-w) - w` are strictly decreasing and expanding, `|Δout| > |Δin|`
   (`fu_exp`, `fd_exp`); the lap map `F` has `F b - F a > b - a` (`F_exp`). The only input is
   strict monotonicity of `δ`.
2. **Stationary train, critical runt.** `Stat h l`: `δ↑(-h) = h + l = δ↓(-l)` (a pulse train with
   high `h`, low `l`, period `h + l`). It exists for every involution pair (`stat_exists`, IVT
   proved with `sSup`) and is unique (`stat_unique`). Its critical runt is
   **`s* = crit l = δ∞↑ - l`**: at `s*` the orbit is the train for ever (`wd_crit`,
   `wd_crit_pos`).
3. **Either side of `s*` (goal 2).** `latch`: `s* < s < δ∞↑` gives a first cancellation at an odd
   index (latched). `latch_grow`: while it runs, every high pulse is at least `c > 0` wider than
   the previous one and every low gap is narrower. `lost`: `0 < s < s*` gives a first cancellation
   at an even index (lost); `lost_shrink`: highs shrink by at least `c > 0` per lap.
   `crit_unique`: `s*` is the ONLY width in `(0, δ∞↑)` that never cancels (so B's `arb_eternal`
   witness is this `s*`, by B's `Osc` = our `∀ n, 0 < wd n`; that equality is by the definitions,
   not checked by Lean).
4. **Digital metastability (goal 3).** `laps_unbounded_above/below`: for every `N` and `ε > 0`
   there are runts in `(s*, s* + ε)` that latch and in `(s* - ε, s*)` that are lost, each after
   MORE than `N` cancellation-free transitions. `resolution_unbounded`: for every time `B` there
   is a latching runt whose last `q` transition is after `B`. There is no bound on resolution
   time in this model.
5. **Symmetric channel (goal 1).** `Sym` (`δ↑ = δ↓`): the train has 50% duty, `h = l = w*`
   (`Sym.duty`, from uniqueness plus the swap symmetry), with **`2w* = δ(-w*)`** (`Sym.fixed`).
   So the fixed point of the circulating pulse is half the loop delay that the train itself
   sees, `δ(-w*)`. But the critical INPUT runt is **`s* = δ∞ - w*`, NOT `δ∞/2`**:
   `Sym.crit_gt_half`: `s* - δ∞/2 = (δ∞ - δ(-w*))/2 > 0` and `s* > δ∞ - δ(0)/2`;
   `Sym.crit_lt`: with `δmin = d`, `d/2 < w* < d`, so `δ∞ - d < s* < δ∞ - d/2`.
   `exp_crit` (A's exp-channel, `δmin = T_p`): `δ∞/2 < s* < δ∞ - T_p/2 = τ ln 2 + T_p/2`.
   The excess over `δ∞/2` comes from the first lap: the runt enters a loop with a long low
   history (delay `δ∞`), the train circulates with the shorter delay `δ(-w*)`.
   Float check (`ws.py`, `s* = δ∞ - w*` with the exp channel): `s*/TLOOP` = 0.500, 0.502, 0.514,
   0.543, 0.581 for τ = 40, 60, 100, 150, 200 ps at TLOOP 424, and 0.500-0.534 at TLOOP 624. These are
   the A-fid3 §3 orbit numbers, so the formula explains the drift that note saw.
6. **Asymmetric channel (goal 4).** `crit_bounds`: `δ∞↑ - (h+l) < s* < δ∞↑` and
   `h + l < min(δ↑(0), δ↓(0))`. `asym_iff`: `h < l ⇔ δ↑(-h) < δ↓(-h)` (rise faster than fall at
   the train's operating point) `⇔ s* < δ∞↑ - (h+l)/2`. `asym_up_le_down` / `asym_down_le_up`:
   the same with the interval hypothesis `δ↑ ≤ δ↓` on `(-δ↓(0), 0)` (or the reverse).
   Note: for an exp-like channel the slope of `δ` exceeds 1 near the left end of the domain, so the
   interval hypothesis can fail for natural skewed channels. `asym_iff` is the statement to use.
   **Correction to A-fid3 §3 item 3.** That note guessed that the centre moves to
   `TLOOP·δ↓/(δ↑+δ↓)`. Float check (`asym.py`, the skewed involution family
   `δ↑(T) = δ(T-a)+a`, `δ↓(T) = δ(T+a)-a`, exp δ, TLOOP 424, τ 100; `δ∞↑ = 424 + a`) gives:
   a = -40/-20/-10/0/+10/+20/+40 ps → s* = 58/105/149/218/291/343/407 ps. So a slower rise moves `s*`
   UP (the guess moves it down), and 10 ps of rise/fall skew moves `s*` by about 70 ps. The
   orbit simulation confirms lost at s* - 0.5 and latched at s* + 0.5. This is a Float computation,
   not a theorem. The Lean statement is `asym_iff` plus the bounds.

## What this says about FID_RESOLVE's centre (the model, not silicon)

In the lumped single-channel involution model of a LUT state loop:
- The threshold is a single sharp `s*` with deterministic outcomes on each side and unbounded
  resolution time at it. This is the structure the GLS resolver imitates.
- With `δ↑ = δ↓ = ` the loop delay read as `δ∞ = TLOOP`, `s*` lies in `(TLOOP/2, TLOOP - δmin/2)`, and
  for the exp channel in `(TLOOP/2, τ ln2 + T_p/2)`. TLOOP/2 is the limit when the loop is mostly pure
  delay (τ small); 0.50-0.58·TLOOP for τ ≤ 200 ps at TLOOP 424.
- The GLS centre TLOOP - WIN/2 (349 of 424 ps) lies inside this model's range only if
  `TLOOP - WIN/2 < TLOOP - δmin/2`, i.e. `δmin < WIN` (150 ps). For the exp channel that means
  `T_p < 150 ps`, `τ ln2 > 274 ps`: a loop that is mostly RC slew, not transport. Nothing measured
  supports that (prjxray arcs are transport numbers). So the model supports moving the centre
  toward TLOOP/2 (A-fid3's patch), with the band above as the model-uncertainty width.
- Rise/fall asymmetry, which prjxray does not give, moves `s*` strongly (by much more than the skew
  in the Float example). So a centre fixed from symmetric data is fragile. The board measurement
  (hw/arb_mtbf 50% point) is the only way to settle it.
- Not covered: noise or jitter (the model is deterministic), loops through more than one cell,
  whether a LUT plus route is an involution channel at all (hypothesis `H_CH` of B), and the
  identification of TLOOP with `δ∞`.

## Status

- Claimed: `formal/lean/Formal/Core/Delay/InvolutionLoop.lean` (no sorry/axiom; check.sh OK, 197 decls).
- Not claimed: `formal/lean/Wip/InvLoop/Bridge.lean` (`lo = orb`, `Osc ↔ ∀ n, 0 < wd`, B's
  eternal gap = `crit`). It is not compiled because B's `CElemInvolution` imports Mathlib topology
  modules that were unbuilt. Once they are built, check it and move it to `Formal/`.
- Not proved: a rate (how many laps as a function of `|s - s*|`, the TAU_eff of A-fid3). B's `window_lower`
  covers that under its `QuantHyp`. Signal-level latch/lost statements for every solution go through B's
  `loop_orb` plus the bridge (not done here).
