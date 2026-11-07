# B-arb-analog2: probe 7k, closing the analog probe's gaps

Track 7 (arbiter), analog layer. File: `formal/lean/Formal/Cells/ArbAnalog2.lean`
(CLAIMED; imports `Formal.Cells.ArbAnalog` read-only; ~890 lines).

## Check

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH ../slot.sh lake env lean Formal/Cells/ArbAnalog2.lean

STATUS (2026-10-27): checks clean. No errors, no warnings, no sorry/admit/axiom/
native_decide. ~15 s wall. `#print axioms` (run on the file, then the lines were
removed) for `xsol_isSol`, `inst_not_exclusive`, `inst_metastable`,
`inst_aperture_upper`, `aperture_lower_bound_local`, `inst_window_lower`,
`inst_undecided_exists`: only `[propext, Classical.choice, Quot.sound]`.

## (a) Non-vacuity: one concrete loop for which every hypothesis is proved

### The transfer function `Fx`
With `sat x = max 0 (min 1 x)`, `w = sat v - 1/2`, `phi v = w (1 - 2|w|)`,
`P = sat(2a) - sat(2b)` (net set/reset drive, thresholded at mid-rail),
`H = sat(2 min(a,b) - 1)` (both requests above mid-rail):

    Fx(a, b, v) = v + H phi(v) + max(P,0) (1 - sat v) - max(-P,0) sat v

* `Fx_lip`: **H_LIP with L = 6**, globally (all three pins).
* `Fx_init`: **H_INIT**: at all 8 rail corners `Fx` equals `rail (qNext r1 r2 q)`,
  where `qNext` is the REAL `bd_arbcell` INIT `64'hFFB2_FFB2_FFB2_FFB2` read with
  `lutB` (from `ArbAnalog`).
* Hold region: `Fx(1,1,v) - v = phi(v)`; equilibria 0, 1/2, 1; slope at mid-rail
  `G'(1/2) = 2` (loop gain 2), slope 0 at the rails.

### Loop, stimulus, solution
* `m0 : Loop`: `tau = 1`, `F = Fx`, `L = 6`.
* `S0 = rampStim (fun _ => 1) sat 1 sat_lip`: r1 already high, `r2(t) = sat(t - s)`,
  a unit ramp starting at the timing `s` (the canonical timing sweep of
  `ArbAnalog`, H_STIM_LIP with `M = 1` comes from `rampStim`).
* `xsol s t = psi(Af(t-s) - Af(-s), Yc s t)` from `q(0) = 0`:
  set phase `Yc = 1 - exp(-(Bf(t-s) - Bf(-s)))` (`Bf`, `Af` are the explicit
  piecewise-quadratic antiderivatives of the drive P and of the hold weight H
  along the ramp); hold flow `psi A y = 1/2 + w/(2|w| + (1-2|w|) e^{-A})`, the
  closed-form solution of `v' = phi v` (two-sided logistic).
* `xsol_isSol : IsSolFamily m0 S0 0 xsol`: **global existence on `[0, ∞)` for
  every `s`**, proved from the closed form (case split on the phase at `t`;
  each case uses eventual equality in `𝓝[≥] t` with an explicit `HasDerivAt`).
  The general global Picard-Lindelof for a globally Lipschitz field was NOT
  needed and is NOT proved.

### Hypotheses proved for the instance (sweep `s ∈ [0, 2]`, `tw = 3`)
| hypothesis | lemma | value |
|---|---|---|
| H_TAU, H_LIP, H_INIT | `m0` fields, `Fx_lip`, `Fx_init` | tau 1, L 6 |
| H_STIM_LIP | `rampStim` | M 1 |
| IsSolFamily (existence) | `xsol_isSol` | closed form |
| H_ENDS (VIL 1/4, VIH 3/4, every `T ≥ 3`) | `inst_H_ENDS` | `q_0(T) ≤ 1/4`, `q_2(T) ≥ 3/4` |
| H_HOLD_INPUTS | `inst_hold` | both requests = 1 for `t ≥ 3` |
| `F(1,1,vs) = vs` | `inst_heq` | `vs = 1/2` |
| `vs ∈ uIcc(q_sA(tw), q_sB(tw))` | `inst_hvs` | |
| H_LOCAL_GAIN_UP/DN | `inst_gain_up/dn` | any `g ∈ [1,2)`, band `2r < 2 - g` |
| H_SPREAD | `inst_spread` | `c = exp(-9/4)`, `s* = log 2 - 1/4` |

Instantiated theorems:
* `inst_not_exclusive`: for every `T ≥ 3` some `s ∈ [0,2]` has `1/4 < q(T) < 3/4`.
* `inst_metastable`: `metastable_forever` applied; `inst_sstar_meta` checks it
  independently from the closed form (`q_{s*}(t) = 1/2` for all `t ≥ 3`).
* `inst_aperture_upper`: undecided on `[3,T]` ⇒ `|s - s*| ≤ (r/e^{-9/4}) e^{-(g-1)(T-3)}`.
* `inst_undecided_exists`: for every `T ≥ 3`, `0 < r < 1/2` there IS `s ≠ s*` in
  the sweep undecided on all of `[3,T]` — so `hund` in `aperture_upper_bound` is
  satisfiable by non-trivial timings, not only by `s*`.

## (b) Matching rates: lower bound at the local rate

General (any `Loop`, any `Stim`, any solution family), namespace
`Formal.Cells.ArbAnalog2`:
* `sandwich_up` / `sandwich_dn`: with **H_LOCAL_GAIN_UP/DN** (gain ≥ g) and new
  **H_LOCAL_GAIN_HI_UP/DN** (`G v - v < (gh-1)(v - vs)` on `(vs, vs+r]`, mirror
  below; physical fact: closed-loop small-signal gain near `vs` is at most `gh`;
  test: same SPICE/GLS closed-loop sweep around `vs` as the lower bound), a node
  starting at offset `d` with `d e^{(gh-1)(T-tw)/tau} ≤ r` satisfies
  `d e^{(g-1)(t-tw)/tau} ≤ |q(t) - vs| ≤ d e^{(gh-1)(t-tw)/tau}` on `[tw, T]`
  (fencing lemma `image_le_of_deriv_right_lt_deriv_boundary` for the upper
  side, `grow_lower` from ArbAnalog for the lower side). `gh ≥ g ≥ 1` is derived,
  not assumed.
* `stays_at`: started on `vs`, stays (ODE uniqueness).
* `undecided_of_close`: `|q(tw) - vs| e^{(gh-1)(T-tw)/tau} ≤ r` ⇒ undecided on `[tw,T]`.
* `aperture_lower_bound_local`: with the Groenwall spread `C(tw)` of `sol_dist_le`,
  `C |s - s*| e^{(gh-1)(T-tw)/tau} ≤ r` ⇒ undecided on `[tw, T]`.

So the bad-timing window `W(T)` (timings undecided on `[tw,T]`) satisfies

    s* ± (r/C) e^{-(gh-1)(T-tw)/tau}  ⊆  W(T)  ⊆  s* ± (r/c) e^{-(g-1)(T-tw)/tau}

both rates LOCAL (the old lower bound used the global `K = (L+1)/tau`). They
coincide in the limit `g, gh → G'(vs)` as the band `r → 0`. Instance
(`inst_window_lower`): `gh = 2` exactly (the slope at mid-rail), `g` any value
`< 2 - 2r`, so the rates are `1/tau` and `(1 - 2r)/tau`.

Not proved: a single-rate `Θ(e^{-(g-1)(T-tw)/tau})` with `g = G'(vs)` exactly.
That needs a linearization/conjugacy argument (the nonlinear correction
`∫ (G'(v) - g)/(v - vs)` must converge, e.g. `G ∈ C^{1,α}` near `vs`); with
strict two-sided bounds the best one gets is the sandwich above, i.e.
`Θ` up to a factor `e^{(gh - g)(T-tw)/tau}` that can be made `e^{ε(T-tw)}` for any ε.

## (c) H_SPREAD from F

Derived for the instance only (`inst_spread`): the set phase leaves
`q(tw) - 1/2` with `|.| ≥ |1/2 - e^{-(1/4+s)}| ≥ e^{-9/4} |s - s*|` (the hold
phase only enlarges the offset, `abs_psi_ge`). A general derivation from F is
NOT done: it needs a lower bound on `∂q(tw)/∂s`, i.e. the variational equation
plus a positivity assumption on how the request drive moves F off the rails
(F strictly increasing in r1-set drive in the contention window). H_LIP and
H_INIT alone do not imply it (a F that ignores the requests near mid-rail is
Lipschitz and rail-correct and gives no spread). Estimated effort: 1-2 days.

## Fidelity per primitive

* **State LUT (`Fx`)**: a concrete continuous transfer function, rail-correct
  (REAL INIT via `lutB`) and Lipschitz. It is ONE witness, not a model of the
  real mux tree: off the rails its shape (thresholded drives, a hold weight that
  switches the regenerative term off while a request is below mid-rail, a cubic
  `phi`) was chosen to make the ODE solvable in closed form. Its only role is to
  show the hypotheses of the analog theorems are jointly satisfiable by a
  physically plausible loop (gain 2 at mid-rail, stable rails, set/reset drive).
  Nothing about the real LUT's gain or aperture follows from its constants.
* **Feedback wire + LUT delay**: one first-order lag, `tau = 1` (time unit).
  The ramp of r2 is one `tau` long.
* **Inputs**: r1 a constant 1 (already high), r2 a linear ramp of slew 1
  starting at `s`. No glitches.
* **Grant LUT, rst, A0**: not modelled (as in `ArbAnalog`).

## What did not work / was avoided
* A general global-existence theorem was avoided by choosing F so that the ODE
  solves piecewise in closed form; the set and hold phases are separated by the
  thresholds in P and H (P > 0 only while r2 < 1/2, H > 0 only while r2 > 1/2).
* `Real.log_two_gt_d9` lives in `Mathlib.Analysis.Complex.ExponentialBounds`
  (not imported); used `log_le_sub_one_of_pos` / `one_sub_inv_le_log_of_pos`.

## Verdict

**Works.** (a) done: the analog theorems are NOT vacuous; one explicit loop with
the real INIT at the rails, the canonical ramp stimulus, an existence proof on
`[0, ∞)` and every hypothesis of `analog_arbiter_not_exclusive`,
`metastable_forever` and `aperture_upper_bound` proved, plus a proof that the
undecided set in `aperture_upper_bound` contains timings other than `s*`.
(b) done in the two-sided form: lower bound now at the local rate `(gh-1)/tau`;
exact single-rate Θ not proved (needs a C^{1,α} linearization, ~1 day).
(c) done for the instance; general derivation from F open (~1-2 days, needs an
extra monotonicity hypothesis on F's request dependence). Spent ≈1.5 h.
What it buys: the analog layer's results (Buridan, metastable-forever, the
two-sided exponential window, MTBF form `tau_eff = tau/(g-1)`) are now known
to be about a non-empty class of loops, and the window's two exponents are both
local loop gains, which is the quantity the board must measure.
