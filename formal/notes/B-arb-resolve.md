# Probe 7d: linearized resolution of the arbiter loop (e^(-t/tau) law, probabilistic bound, MTBF)

Track 7 (arbiter), shard B. Lean file: `formal/lean/Formal/Cells/ArbResolve.lean`
(CLAIMED: checks clean). Mathlib (reals, derivatives, Lebesgue
measure). No `sorry`/`admit`/`axiom`/`native_decide`.

## Check status

**Checks clean** (no errors, no warnings) against Lean 4.35.0 / Mathlib v4.35.0
built from source, 2026-10-27, in ~7-9 s wall. Promoted from `Wip/Cells/` to
`Formal/Cells/ArbResolve.lean` (the Wip copy is removed). `#print axioms` on
`LinLoop.prob_unresolved_dt`, `gain_prob_unresolved`, `LinLoop.sol_unique`,
`LinLoop.inBand_iff`: only `propext, Classical.choice, Quot.sound`.
No `sorry`/`admit`/`axiom`/`native_decide`. No unproved goals.

Check command (from `formal/lean`, through the slot semaphore):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH ../slot.sh lake env lean Formal/Cells/ArbResolve.lean

The file imports six Mathlib modules, not `Mathlib`:
`Analysis.SpecialFunctions.{ExpDeriv,Log.Basic}`, `Analysis.Calculus.MeanValue`,
`Analysis.Calculus.Deriv.MeanValue`, `MeasureTheory.Measure.Lebesgue.Basic`,
`Topology.Order.DenselyOrdered` -- all inside the closure the shard lead's
`lake build` target list already builds. A lemma
`densityBound_of_withDensity` (a measure `volume.withDensity f` with `f <= p`
on `N` satisfies `DensityBound`) was written but dropped, because
`MeasureTheory.Measure.WithDensity` pulls in convolution/Radon-Nikodym and is
not in the built closure; it is a 5-line proof (`withDensity_apply`,
`setLIntegral_mono'`, `setLIntegral_const`) to restore if that module is
built. Until then `DensityBound` is the hypothesis itself (any measure, a
bound on measurable subsets of `N`).

## Model

The state node `q = C(r1,~r2)` of `bd_arbcell` is one LUT6 output routed back
to one of its own input pins (`bd_c2n_set`, `cells/rtl/bd_ce.v`). In the runt
condition (r1 and r2 moving in opposite senses within one loop delay, see
`cells/docs/ARBITER.md`) the set and reset drives are both momentarily off and
the node is a bare positive-feedback loop. Analog layer (PROGRAM.md layer 4):

    tau * v' = f(v) - v

with `f` the static transfer of the LUT from the fed-back pin to `O6` with the
other pins frozen. A crossing `f(vs) = vs` with slope `g = f'(vs) > 1` is the
metastable point. Linearized: `tau v' = (g-1)(v - vs)`,
`tau_r = tau/(g-1)`, `v(t) - vs = (v0 - vs) e^{t/tau_r}`.

Named hypotheses (structure fields / explicit hypothesis arguments):

| name | stands for | how to test |
|---|---|---|
| `H_tau_pos` | the node has a real RC (LUT output stage + feedback wire + input buffer) | nonzero ring period of the feedback loop (GLS/board) |
| `H_gain_gt_one` | loop gain at the crossing > 1, i.e. the loop is bistable (it is a latch) | `serv` set on the board; DC transfer slope in a transistor-level model (none in repo) |
| `hode` (linear) | after the runt ends the node obeys the linearized first-order ODE | only in an analog model; prjxray has no gain data |
| `H_escape` / `H_gain_band` | in the band `|v-vs|<delta` the escape rate is at least `gamma = (g_min-1)/tau`, i.e. `(f(x)-x)(x-vs) >= (g_min-1)(x-vs)^2` | slope of the DC transfer over the band |
| `H_density` (`DensityBound mu N p`) | the law of the initial offset has density `<= p` on the band: the request-edge timing is spread smoothly, no atom, no lock | histogram `Δt` of `r1`/`r2` edges in routed GLS; the CLEN1=3/CLEN2=5 drift in `arb_prot` is designed to produce it |
| `H_affine_offset` (`v0 = vs + k Δt`, `k ≠ 0`) | the offset the runt leaves on the node is proportional to the overlap time | sweep `Δt` in an analog model; it is the first-order term of a smooth map |
| `delta` | the band a consumer reads as an intermediate level (LUT input threshold uncertainty) | not in prjxray; a fabric fact |

## Theorems (all in `Formal.Cells.ArbResolve`)

Linear loop (`LinLoop` = `tau, g, vs, H_tau_pos, H_gain_gt_one`):

- `LinLoop.sol_hasDerivAt`: `sol v0 t = vs + (v0-vs) exp(t/tau_r)` has derivative
  `(g-1)/tau * (sol - vs)` at every `t`. `LinLoop.sol_ode`: the physical form
  `tau * deriv sol t = (g-1)(sol t - vs)`. `sol_zero`: `sol v0 0 = v0`.
- `LinLoop.sol_unique`: any `v` with `HasDerivAt v ((g-1)/tau (v t - vs)) t` on
  `[0,T]` equals `sol (v 0)` on `[0,T]` (integrating factor
  `(v - vs) e^{-t/tau_r}` has zero derivative; `constant_of_has_deriv_right_zero`).
  `sol_unique_Ici`: the same for all `t >= 0`.
- `LinLoop.sol_dev`: `|sol v0 t - vs| = |v0 - vs| e^{t/tau_r}`; `sol_vs`: started
  exactly at `vs` it never moves.
- `LinLoop.inBand_iff` (2): for `v0 ≠ vs`, `delta > 0`:
  `|v(t) - vs| < delta ↔ t < tau_r * log(delta / |v0 - vs|)` for every real `t`.
  So the exit time is exactly `escTime = tau_r ln(delta/|v0-vs|)`;
  `dev_at_escTime`: the deviation equals `delta` there; `escTime_pos`.
- `LinLoop.no_deadline` (5): for every `T`, `delta > 0` there is `v0 ≠ vs` still
  within `delta` at `T`. No fixed read time makes exclusion deterministic.
- `band_set_eq`, `band_set_volume`: `{x | |x-a| c < delta} = Ioo (a - delta/c) (a + delta/c)`,
  of Lebesgue measure `2 delta / c`.
- `LinLoop.unresolved_eq`, `unresolved_volume` (3, interval form): the set of
  `v0` unresolved at `T` is the interval `vs ± delta e^{-T/tau_r}`, length
  `2 delta e^{-T/tau_r}`.
- `DensityBound mu N p`: `mu s <= p * volume s` for measurable `s ⊆ N` (the
  density hypothesis, stated without Radon-Nikodym).
- `prob_band`, `LinLoop.prob_unresolved` (3, measure form): `T >= 0`, density
  `<= p` on the band ⇒ `mu {v0 | |v(T) - vs| < delta} <= 2 p delta e^{-T/tau_r}`.
- `LinLoop.prob_unresolved_dt`: in terms of the edge timing `Δt` with
  `v0 = vs + k Δt`: `nu {Δt | unresolved at T} <= q (2 delta/|k|) e^{-T/tau_r}`,
  `q` = density bound of `Δt`. This identifies the aperture `T0 = 2 delta/|k|`.

Nonlinear loop (true `f`, comparison with `g_min`):

- `nonlinear_growth`: `v' = F(v)` on `[0,T]`, escape rate `>= gamma` in the band,
  trajectory in the band on `[0,T]` ⇒ `(v0-vs)^2 e^{2 gamma t} <= (v t - vs)^2`
  (`(v-vs)^2 e^{-2 gamma t}` is monotone: `monotoneOn_of_deriv_nonneg`).
  `nonlinear_growth_abs`: `|v0 - vs| e^{gamma t} <= |v t - vs|`.
- `nonlinear_prob_unresolved`: family of trajectories `traj v0`, density `<= p`
  ⇒ `mu {v0 | in band on all of [0,T]} <= 2 p delta e^{-gamma T}`.
- `gain_prob_unresolved`: the same in circuit terms, `tau v' = f(v) - v` and
  `H_gain_band: (f x - x)(x - vs) >= (g_min - 1)(x - vs)^2` in the band ⇒
  bound `2 p delta e^{-T/tau_r,max}`, `tau_r,max = tau/(g_min - 1)`.
  Note: no existence/uniqueness for the nonlinear ODE is needed — the theorem
  quantifies over any trajectory family that satisfies it.

MTBF:

- `mtbf_lower`: per-event failure probability `<= f2 T0 e^{-T/tau_r}` at event
  rate `f1` (so `lambda <= f1 f2 T0 e^{-T/tau_r}`) ⇒
  `MTBF = 1/lambda >= e^{T/tau_r} / (T0 f1 f2)`. (Pure algebra; the
  probabilistic content is in `prob_unresolved_dt` with `q = f2`, the density of
  the phase of a uniform stream of rate `f2`.)

## What the formula says the project must measure (re `cells/verify/MTBF.md`)

`MTBF = e^{T/tau_r} / (T0 f1 f2)` has two unknown cell parameters and one
design parameter:

1. **tau_r = tau/(g-1)** (resolution time constant). Not derivable from
   prjxray-db: it has digital arc delays, not the small-signal gain `g` of the
   mux tree + buffers at mid-rail, and not `tau` of the analog node. It must be
   measured as a *slope*: the failure rate at two or more resolution times `T`
   gives `-1/tau_r = d ln(rate)/dT`. Zero-failure runs (which is all
   `arb_prot` has) bound the rate but can never give a slope.
2. **T0 = 2 delta/|k|** (aperture). The intercept of the same fit. Its product
   with `f2` is exactly the "contested fraction" `MTBF.md` says is unmeasured
   (order 1e-3 by an aperture/period estimate): per arbitration the probability
   of landing in the dangerous window is `f2 T0`, and the theorem
   `prob_unresolved_dt` makes the rescaling precise.
3. **T** (time between the decision and the consumer's read). The model says
   the grants read `q` with no resolution time at all (one LUT level); the
   width filter `W` sets the `T` that the overlap detector sees
   (W=1: ~80-160 ps, W=2: ~160-320 ps per `ARBITER.md`). So the existing W=1 /
   W=2 rigs are a two-point `T` ladder; converting their *rates* (not the
   "fired at least once" counts) into a fit would give `tau_r` and `T0`
   directly. The depth ladder was correctly retired (it changed the circuit,
   not `T`).

Consequence: with `tau_r` and `T0` measured, an MTBF at any `T` and any
request rates follows by the formula; without them, `arb_prot`'s zero-failure
exposure is a bound on the total rate per arbitration only (as `MTBF.md` says),
and the formal result cannot convert it into a metastability bound.

### Connection to the unexplained 8% (a hypothesis, not a result)

The rate is exponential in `T/tau_r`, so modest copy-to-copy differences in
`tau_r` move per-copy rates by orders of magnitude. `tau_r = tau/(g-1)` depends
on which pin the fed-back `q` enters (depth of that pin in the pass-transistor
mux tree changes both the node capacitance `tau` and the gain `g`), and on the
feedback wire load. That is consistent with three facts in `ARBITER.md`: the
surviving lead is pin A5 (q on A5 fires 2/107, others 13/85), badness is not a
fixed per-copy property (43/50 bad copies clean on rebuild, which re-assigns
pins), and the flow's digital timing model cannot express it (prjxray has no
per-pin O6 data and no gain at all). Back-of-envelope: "fired within 2 min" at
~1e8 events/s versus clean for ~14 h is a per-event probability ratio of
>~1e3, i.e. `Δ(T/tau_r) >~ 7`: at `T ~ 160 ps` that needs `tau_r` to differ by
a factor of a few between pins. Test that discriminates it from a structural
cause: a metastability mechanism gives a Poisson rate `∝ f1 f2` (scales with
both oscillator frequencies) and `∝ e^{-T/tau_r}` (falls exponentially with W);
a structural glitch scales with event rate only and does not fall
exponentially with W. The `q`-on-A5 build that `ARBITER.md` proposes is the
other half of the test.

## Confirms PROGRAM.md's expected result

`no_deadline` + `prob_unresolved` (and the nonlinear versions): in this model
the LUT arbiter's mutual exclusion at a fixed read time is NOT provable
unconditionally — for every `T` some initial offsets are still unresolved — and
only the probabilistic bound `2 p delta e^{-T/tau_r}` holds, under a
density hypothesis on request timing. (A binary/Kleene model cannot show this;
it needs the analog layer.)

## Fidelity statement

| primitive | model here | fidelity |
|---|---|---|
| LUT (state node `q`) | static transfer `f` from the fed-back pin, first-order node `tau v' = f(v) - v`, other pins frozen | coarse: real LUT is a pass-transistor mux tree behind input buffers, so the true node has several poles and the transfer depends on the pin's depth in the tree. A one-pole model is the standard metastability model; the exponential law survives any number of poles asymptotically with `tau_r` = the dominant unstable pole, but the constant `T0` does not. `f`, `g`, `tau` are not in prjxray-db. |
| feedback routing | folded into `tau` | intra-site feedback (0 ps routed in the shipped cell) is a short wire; its C adds to `tau`. |
| grants / consumer | a threshold band `|v - vs| < delta` read at time `T` | idealization: the real consumer is another LUT whose input buffer has its own gain; a real read that is "wrong" may need a smaller or larger `delta`. Any fixed `delta` gives the same `e^{-T/tau_r}` law. |
| set/reset drive (r1, r2) | only through the initial offset `v0 = vs + k Δt` | first-order (affine) in `Δt`; holds for a smooth drive near the coincidence. |

## How hard were the Mathlib parts

Easy. The whole file (≈490 lines, 28 theorems) was written blind while
Mathlib was still building, from grepping the Mathlib sources for lemma names,
and checked on the first run with zero errors; the only edits afterwards were
lint warnings (`field_simp` already closed four goals the trailing `ring` was
meant for; `Set.mem_setOf_eq` is deprecated in favour of `Set.mem_ofPred_eq`).
What made it easy:
- ODE: no Mathlib ODE library needed. Uniqueness of the linear ODE is the
  integrating factor `(v - vs) e^{-t/tau_r}` plus `constant_of_has_deriv_right_zero`;
  the nonlinear comparison is `(v-vs)^2 e^{-2 gamma t}` plus
  `monotoneOn_of_deriv_nonneg`. Derivatives are built with `HasDerivAt.mul/exp/
  const_mul/div_const/sub_const` and closed with `congr_deriv` + `ring`.
  (Gronwall / Picard-Lindelöf would be needed only for *existence* of the
  nonlinear trajectory, which the theorems avoid by quantifying over any
  trajectory.)
- Exit time: `lt_log_iff_exp_lt`, `lt_div_iff₀`, `div_lt_iff₀` in one `rw` chain.
- Measure: the unresolved set is literally an `Ioo`; `Real.volume_Ioo` gives its
  length, and the density bound is applied to that one measurable set
  (`measure_mono` for the nonlinear superset). No integrals at all.
The hard part is not Lean, it is the physics: `tau`, `g`, `delta`, `k` and the
density are hypotheses with no source in prjxray-db.

## Verdict

**Works** (done, claimed, checks clean). Effort spent ≈1 h of writing plus
waiting for Mathlib; effort to extend: (a) restore the `withDensity` lemma once
that module is built (minutes); (b) existence of the nonlinear trajectory via
`Mathlib.Analysis.ODE.PicardLindelof` for a Lipschitz `f` (≈half a day); (c)
a multi-pole node (mux-tree depth) — the dominant-unstable-mode version — is
real work (days; linear ODE systems / matrix exponentials in Mathlib are thin).
What it buys the project: a machine-checked statement that (i) a LUT arbiter's
exclusion at any fixed read time is not deterministically provable
(`no_deadline`), (ii) the failure probability is `<= q T0 e^{-T/tau_r}` under
named hypotheses, also for the nonlinear loop with `g_min`, and (iii) hence the
MTBF formula `e^{T/tau_r}/(T0 f1 f2)`, which turns `cells/verify/MTBF.md`'s open
"contested fraction" into the measurable product `f2 T0`, and says the two
numbers the board must deliver are `tau_r` (a slope of log-rate vs resolution
time — impossible from zero-failure runs) and `T0` (its intercept).
