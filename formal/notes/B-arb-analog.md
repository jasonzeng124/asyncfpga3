# B-arb-analog: probe 7c, the arbiter's state loop as an ODE

Track 7 (arbiter), analog layer (PROGRAM.md "The model the owner has in mind",
item 4). File: `formal/lean/Wip/Cells/ArbAnalog.lean` (STATUS: see "Check"
below; it moves to `formal/lean/Formal/Cells/ArbAnalog.lean` only once it
checks clean against Mathlib).

## Model

The state node `q` of `bd_arbcell` (bd_c2n_set, `INIT 64'hFFB2_FFB2_FFB2_FFB2`,
pins `[r1, r2, q, rst, 0, 0]`) and of `bd_arbiter` (`ustate`,
`INIT 64'hFFF0_FFB2_ACAC_ACAC`, pins `[r1, r2, q, rst, A0, 1]`, `q` on O6) is
one first-order gate:

    tau * v' = F(r1(t), r2(t), v) - v,     v = q's voltage, 0 = GND, 1 = VCCINT

* `Loop` (structure): `tau`, `F : ℝ → ℝ → ℝ → ℝ`, `L : ℝ≥0` and three named
  hypotheses
  * **H_TAU** `0 < tau`.
  * **H_LIP** `|F a b v - F a' b' v'| ≤ L (|a-a'| + |b-b'| + |v-v'|)`: finite
    small-signal gain of the mux tree + input buffers on every pin. Test: SPICE
    or board DC sweep of one LUT pin with a slow ramp.
  * **H_INIT** `F(rail r1, rail r2, rail q) = rail (qNext r1 r2 q)` for all
    Booleans, where `qNext` is the REAL INIT evaluated with Prelim's `lutB`.
    Static levels are restored at the rails. Test: any binary GLS / board run.
* `Stim`: input families `u1 s t`, `u2 s t` indexed by the timing parameter
  `s`, with **H_STIM_LIP** `|u_i s t - u_i s' t| ≤ M |s - s'|` (finite slew).
  `rampStim ρ1 ρ2 M` is the canonical sweep `r1 = ρ1(t)`, `r2 = ρ2(t - s)` with
  `ρ2` M-Lipschitz; H_STIM_LIP is PROVED for it.
* `IsSolFamily m S v0 x`: `x s` solves the ODE on `[0, ∞)` (right derivatives,
  `HasDerivWithinAt ... (Ici t) t`) from `x s 0 = v0`, for every `s`.
  The theorems quantify over every solution family. Existence (Picard-Lindelof)
  is not proved here; it is needed only for non-vacuity (see "Not done").
* **H_ENDS** (argument of the main theorem): at the two ends `sA ≤ sB` of the
  sweep the node is at valid levels of opposite value at time `T`. This is
  "the cell works when the requests are far apart", the uncontested
  behaviour that the binary/Kleene probes and tb_arb establish.
* **H_HOLD_INPUTS** (`HoldInputs`): from `tw` on both requests are fully high
  for every timing in the sweep, so the node is in its hold region
  `G v = F(1,1,v)`.
* **H_GAIN** (`exists_equilibrium`): `G a ≤ a` and `G b ≥ b` for some `a ≤ b`:
  regenerative feedback in the hold region. With `G'(vs) = g > 1`
  (`unstable_equilibrium`) this is the gain > 1 of a physical LUT loop.

## Theorems (all in namespace `Formal.Cells.ArbAnalog`)

INIT facts (core Lean, `decide`; also checked standalone against Prelim):
* `qNext_eq_arbiter`: bd_arbcell's state INIT and the shipped bd_arbiter's O6
  agree whenever `rst = 0, A0 = 0` (the window in which q is live).
* `qNext_eq_C`: the INIT is `C(r1, ~r2)` = `r1·~r2 + q·~(~r1·r2)`.
* `arbiter_holds_on_A0`: with `A0 = 1` the shipped node outputs `q`
  regardless of the requests (the ack-hold).
* `Loop.rail_hold`: from H_INIT, `F(1,1,0) = 0` and `F(1,1,1) = 1`.

Goal 1, Buridan/Marino:
* `sol_dist_le` (Groenwall, `dist_le_of_approx_trajectories_ODE`):
  `|x s T - x s' T| ≤ (2 L M / tau) · gronwallBound 0 K 1 T · |s - s'|`,
  `K = (L+1)/tau`. The solution for timing `s'` is treated as an approximate
  solution of the ODE for timing `s`, with defect `≤ 2LM|s-s'|/tau`.
* `H_CONT_of_lipschitz`: **H_CONT is a theorem, not a hypothesis**: for
  `T ≥ 0`, `s ↦ x s T` is continuous (Lipschitz).
* `buridan`: abstract IVT form (continuous `f` on `[sA,sB]` hits every value
  between `f sA` and `f sB`).
* `no_valid_level`: valid 0 at one end, valid 1 at the other ⇒ some `s` with
  `VIL < f s < VIH`.
* `analog_arbiter_not_exclusive` / `not_forall_valid`: for every `T ≥ 0`,
  under H_TAU, H_LIP, H_INIT (only used for the hold facts), H_STIM_LIP and
  H_ENDS, `¬ ∀ s, x s T ≤ VIL ∨ VIH ≤ x s T`. **"For every input timing, q is a
  valid level by time T" is false, for every T.** Mutual exclusion of the
  grants is therefore not unconditionally provable in any model whose gates
  are continuous: the grant LUT is another continuous map of (r1, r2, q), so the
  same argument puts a grant at an invalid level.

Goal 2, the saddle:
* `Loop.exists_equilibrium`: H_GAIN ⇒ `∃ vs ∈ [a,b], F(1,1,vs) = vs` (IVT).
* `Loop.unstable_equilibrium`: `F(1,1,vs)=vs`, `G'(vs) = g > 1` ⇒ field
  derivative `(g-1)/tau > 0`, field `> 0` on a right neighbourhood and `< 0`
  on a left one: `vs` repels (in the two-gate picture, a saddle; in this
  one-gate model, an unstable node of a 1-D flow).
* `metastable_forever`: if `vs` lies between the states reached at `tw` by the
  two ends of the sweep (H_HOLD_INPUTS, `F(1,1,vs) = vs`), then ONE timing
  `s*` gives `x s* t = vs` for ALL `t ≥ tw` (IVT + `ODE_solution_unique`).
  Stronger than goal 1: `s*` does not depend on the observation time.
* `stays_near`: `|x s t - vs| ≤ |x s tw - vs| · exp(K (t - tw))`
  (`dist_le_of_trajectories_ODE`).
* `aperture_lower_bound`: `|x s t - vs| ≤ C(tw) |s - s*| exp(K (t - tw))`.
  So every timing within `δ / (C(tw) exp(K(t - tw)))` of `s*` is still within
  `δ` of the metastable point at resolution time `t`: the bad-timing aperture
  cannot shrink faster than `exp(-K t)`. This is the LOWER-bound half of the
  e^(-t/tau) law, i.e. "only a probabilistic bound holds, and it is at best
  exponential". The upper-bound half (aperture ≤ c·exp(-(g-1)t/tau), what
  MTBF needs) needs a local lower bound on the gain around `vs` and a
  comparison argument for escaping trajectories; not done (see below).

## Mathlib ODE facts: what exists, what was used

| Mathlib fact | exists | used |
|---|---|---|
| `IsPicardLindelof` + `exists_eq_forall_mem_Icc_hasDerivWithinAt` (local existence, ExistUnique.lean) | yes | no (existence is not needed for the impossibility direction; see Not done) |
| `norm_le_gronwallBound_of_norm_deriv_right_le` | yes | indirectly (through the next two) |
| `dist_le_of_approx_trajectories_ODE` (Groenwall for approximate solutions) | yes | YES: continuous dependence on the timing parameter |
| `dist_le_of_trajectories_ODE` | yes | YES: `stays_near` |
| `ODE_solution_unique` (Icc, Lipschitz in x) | yes | YES: `metastable_forever` |
| `gronwallBound`, `gronwallBound_of_K_ne_0` | yes | YES (`gronwallBound_zero_left`) |
| `intermediate_value_uIcc`, `intermediate_value_Icc` | yes | YES |
| `hasDerivAt_iff_tendsto_slope`, `slope_def_field` | yes | YES (instability sign) |
| continuous dependence on parameters as a packaged theorem | no | derived from the approximate-trajectory Groenwall above |

All Mathlib lemmas take right derivatives `HasDerivWithinAt f f' (Ici t) t`,
which is exactly what a solution started at `t = 0` has; no extension to
negative time was needed.

## Check

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH ../slot.sh lake env lean Wip/Cells/ArbAnalog.lean

(after it checks clean, the same with `Formal/Cells/ArbAnalog.lean`).
STATUS: written while Mathlib's oleans were not yet available; see the end of
this file for the result of the check.

## Connection to the repo

* `cells/docs/ARBITER.md`, "Exclusion has three tiers": the third tier
  ("metastable q: not excluded") is now a THEOREM for the analog model, under
  stated hypotheses, not just an engineering claim. The first two tiers are
  binary-model claims (other probes).
* "A plain tie resolves deterministically": in the binary model, at exactly
  `s = 0`. In the analog model this is a single point of the sweep; nearby
  timings drive `F` with intermediate `r1, r2` (partial set or reset), and the
  edge of the bad window is not at `s = 0` exactly. Continuity says there IS a
  bad timing between any two timings that resolve differently; it does not say
  where. The binary claim and the analog theorem are consistent.
* `cells/verify/MTBF.md`: the analog model justifies the obligation "the
  failure rate MUST BE MEASURED" (no proof can replace it: `not_forall_valid`)
  and the MTBF form (rate ∝ aperture · exp(-t_r / tau_eff), tau_eff =
  tau/(g-1)). `aperture_lower_bound` is the half that says the rate is
  nonzero at every resolution time. It also shows the rig's denominator
  point: only timings within an exponentially small window of `s*` are at
  risk, so MTBF per arbitration event is the wrong unit; MTBF per contested
  event (MTBF.md, "The exposure figure is not a metastability bound") is.
* The unexplained 8% of `arb_mtbf` copies (ARBITER.md): the model says the
  failure rate depends EXPONENTIALLY on `tau_eff = tau/(g-1)`, i.e. on the
  small-signal gain `g` of the loop at its metastable point. `g` is a property
  of the physical pin/level of the mux tree that `q` re-enters (pass-transistor
  depth, buffer), so a pin-dependent `g` would turn small pin differences into
  large rate differences. This is consistent with the one surviving lead (q on
  A5 fires 2/107 vs 13/85) and with badness not surviving a rebuild (pin
  assignment changes). It is a HYPOTHESIS (H_PIN_GAIN: the loop gain at `vs`
  depends on the LUT pin `q` enters), not a result; the confirming test is the
  one ARBITER.md already proposes (force q onto A5 everywhere), plus a SPICE /
  GLS measurement of per-pin small-signal gain. Caveat: copies that fire
  "continuously within 2 minutes" are hard to reconcile with a rate law unless
  their aperture·rate is very large; the model does not exclude a structural
  cause.

## Fidelity per primitive

* **State LUT (bd_c2n_set / ustate):** modelled by a continuous `F`
  constrained only at the 8 rail corners by the REAL INIT (via `lutB`) and by a
  global Lipschitz bound. This is weaker (more general) than the
  pass-transistor mux tree: every mux tree with buffered inputs and finite
  gain is such an `F`, so the impossibility results hold a fortiori for the
  real LUT. The per-pin structure of the tree is NOT modelled (all three pins
  share one Lipschitz constant `L`).
* **Feedback wire + LUT delay:** lumped into one first-order lag `tau`
  (single-pole RC). A pure transport delay in the loop (delay-differential
  equation) is not modelled; the impossibility argument needs only continuous
  dependence, which also holds for DDEs, but the proofs here are for the ODE.
* **Inputs r1, r2:** arbitrary waveforms with finite slew (H_STIM_LIP); no
  glitches assumed or excluded.
* **Grant LUT:** not modelled separately; it is another continuous map of
  `(r1, r2, q)`, so the same IVT argument applies to `g1`, `g2` (stated in
  prose, not proved as a separate theorem).
* **rst, A0:** taken as constant 0 during the contention window
  (`qNext_eq_arbiter`); `A0 = 1` holds q (`arbiter_holds_on_A0`), which only
  moves the window (ARBITER.md "aperture"), it does not remove it.

## Not done / unproved

* Existence of the solution family (global Picard-Lindelof on `[0, ∞)`):
  Mathlib's `IsPicardLindelof` gives local existence on a ball; a global
  version for globally Lipschitz fields needs either a bounded-field argument
  (F is bounded on the physical range, but that is not assumed) or stitching.
  Not needed for soundness of the impossibility theorems (they are for every
  solution family), only for non-vacuity. Effort: ~1 day.
* Upper-bound half of the e^(-t/tau) law (bad aperture ≤ c·exp(-(g'-1)t/tau)
  given `G v - v ≥ (g'-1)(v - vs)` near `vs`): needs a comparison/escape lemma
  (monotonicity of `(x - vs) exp(-λ t)`). Effort: ~1 day.
* Deriving H_ENDS from the ODE (that far-apart requests resolve): needs
  quantitative bounds on `F` off the rails (e.g. `F ≥ 1 - ε` on the set region).
  Effort: ~1-2 days; the binary probes already cover the digital version.
* DDE (transport delay) model of the loop.
