# A / track 3 / delay channel (a): bounded pure (transport) delay

Files:
- `formal/lean/Formal/Core/Delay/Pure.lean`: proved, namespace `Formal.Core.DelayPure`
- `formal/lean/Wip/DelayPure.lean`: open statements (`sorry`), not built
- this note

Check (from `formal/lean`, with `export PATH=$HOME/.elan/bin:$PATH`):

    ../slot.sh lake env lean Formal/Core/Delay/Pure.lean

Status: checks with exit 0, no errors, no `sorry`/`admit`/`axiom`/`native_decide`.
`#print axioms` on the main theorems gives only `[propext, Classical.choice, Quot.sound]`.
Remaining warnings are deprecations only: this Mathlib flags the
`Mathlib.Data.Real.Basic` import and `if_pos`/`if_neg`.
The Wip statements elaborate when concatenated with Pure.lean; they have two `sorry`s.

## The model

The signal type is `Sig := ℝ → Bool`. It is minimal and self-contained, so it
can be ported to whatever representation the representation probe chooses.

`Chan lo hi x y` holds iff there is a **read-time map** `σ : ℝ → ℝ` (structure
`Retime lo hi`) such that:
- `y s = x (σ s)` for every `s`: the output at time `s` shows the input as it
  was at time `σ s`;
- `s - hi ≤ σ s ≤ s - lo`: what the output shows is between `lo` and `hi` old;
- `σ` is nondecreasing.

An input transition at time `t` appears at the output where `σ` crosses `t`,
so its delay is in `[lo, hi]`. The delay is allowed to vary from transition to
transition, and also within a run, without restriction other than the band.

**Order crossing: FIFO, with annihilation.** Because `σ` is monotone, the
output can never show an older input after a newer one, so transitions never
overtake. Suppose two transitions would cross: the leading edge of a pulse
gets a long delay and the trailing edge a short one. Then `σ` jumps over the
pulse and the pulse disappears (`pulse_can_vanish`). This is the right choice
for a buffered FPGA wire:
- A buffered pip or wire is a chain of CMOS inverting stages. Each stage
  switches when its input crosses threshold, so edges come out in the order
  they went in.
- When rise and fall delays differ by more than a pulse's width, the pulse
  shrinks into a runt and then vanishes. It never comes out inverted.
- A non-FIFO model, in which each transition is delayed on its own and the
  output is the parity of the transitions that have arrived, would turn a
  "crossed" pulse into an *inverted* pulse. No buffer does that.

The FIFO-with-annihilation reading is also the standard semantics of a
transport delay whose delay varies over time (y(s) = x(s − d(s))).

The read-time formulation was chosen over a list of events because
composition, monotonicity and the fixed-delay case become one-line function
algebra, and because no finiteness or well-formedness side conditions are
needed. The cost is that the link to the per-transition textbook picture is
not proved yet: it is `Wip.events_adequate`.

## What is proved (all in `Formal.Core.DelayPure`)

Structure:
- `chan_shift`: any fixed delay `d ∈ [lo, hi]` is a behaviour.
- `chan_total_iff`: the channel has a behaviour for every input iff `lo ≤ hi`.
- `chan_fixed_iff`: when `lo = hi = d`, the channel is the function
  `y s = x (s - d)`. Fixed delay is exactly the special case.
- `chan_mono`: widening the band (`lo' ≤ lo`, `hi ≤ hi'`) only adds
  behaviours.

Series composition:
- `chan_comp`: `[lo1,hi1] ; [lo2,hi2] ⊆ [lo1+lo2, hi1+hi2]`.
- `chan_decomp`: **the converse also holds**, given `lo1 ≤ hi1` and
  `lo2 ≤ hi2`. Every behaviour of the sum band factors through an intermediate
  signal. The explicit split is `σ2 s = max (s-hi2) (σ s + lo1)` and
  `σ1 u = max (u-hi1) (min (u-lo1) (σ (u+hi2)))`.
- `chan_comp_iff`: series composition is *exactly* the sum band. So a path of
  pure-delay segments can be collapsed into one channel with no loss of
  precision.

Stability and transitions:
- `stableOn_out`: if the input is stable on `[a,b]`, the output is stable on
  `[a+hi, b+lo]`. The window shrinks by `hi-lo`.
- `stableFrom_out`, `stableBefore_out`: the one-sided versions.
- `step_out`: for a single transition at `t0`, the output keeps the old value
  before `t0+lo`, has the new value from `t0+hi` on, and changes only once
  (FIFO: no glitch on a clean step).

Pulses (`pulse w` is high on `[0,w)`):
- `pulse_out_support`: the output is high only inside `[lo, w+hi)`. Its width
  is at most `w + (hi-lo)`.
- `pulse_out_core`: the output is high on all of `[hi, w+lo)`. Its width is at
  least `w - (hi-lo)`.
- `pulse_survives`: if `w > hi-lo`, the pulse always survives.
- `pulse_can_vanish`: if `w ≤ hi-lo`, the constant-low output is a behaviour.
  This is the explicit collapse witness: the leading edge is delayed `hi` and
  the trailing edge `lo`.
- `pulse_can_pass`: the same narrow pulse can also pass unchanged, so the
  channel really is nondeterministic.
- `pulse_vanish_iff`: given `lo ≤ hi`, the pulse can vanish **iff**
  `w ≤ hi-lo`. The dichotomy is tight.

Bundled data ("the request arrives after the data"):
- `req_arrival_lb`: if the request input still has its old value before `t0`,
  any time at which the receiver sees the new value is `≥ t0 + lo_req`.
- `bundle_req_after_data` and `bundle_req_after_data'` (the unbounded hold
  version): suppose data at the receiver is stable on `[t0+td, t1]` and
  `td ≤ lo_req`. Then at every request-arrival time `s ≤ t1` the data equals
  its settled value.
- `bundle_two_wires`: the same with the data passing through its own
  pure-delay wire `[loD,hiD]`. The condition becomes `ts + hiD ≤ loR`: the
  data's slow corner must come before the request's fast corner. The hold end
  becomes `t1 + loD`.
- `req_can_arrive_at_lo`: tightness. The request can arrive at exactly
  `t0+lo`, so the channel bound alone gives nothing better than `td ≤ lo`.

All modelling assumptions are explicit arguments: the band, the stability
windows and the launch time. There are no axioms.

## What is not done (Wip/DelayPure.lean)

- `events_adequate`: every per-transition delay assignment that stays in the
  band and in FIFO order is a `Chan` behaviour. This links the model to the
  event-list picture and to SDF transport delays. The proof idea is a
  piecewise `σ`. It needs the event-list signal type, so it waits for the
  representation probe's choice. Estimate: half a day.
- `SkewRetime` and `skew_pulse_survives`: a refinement in which the delay is
  allowed to vary by at most `κ ≤ hi-lo` within a run. Collapse then needs
  `w ≤ κ`. Proving survival needs a supremum or intermediate-value argument on
  `σ`. That needs `Mathlib.Order.ConditionallyCompleteLattice` or real
  `sSup`, which are not built yet. Estimate: half a day once those are built.

## Verdict

**Works.** The channel, exact series composition, monotonicity, the
fixed-delay case, the pulse-width bounds with a tight collapse dichotomy, and
the generic bundling lemma are all proved with elementary tactics (`linarith`,
`split_ifs`). The only Mathlib modules used are `Data.Real.Basic`,
`Tactic.Linarith` and `Tactic.NormNum`. The effort to finish (the Wip items
plus porting to the final signal type) is about 1 day.

What it buys the project:
1. A sound abstraction for routed wires. Composition is exact, so a
   multi-segment net can be summarised by one band per sink arc.
2. The bundling condition (`slow data ≤ fast request`) as a reusable lemma,
   with the right corners on each side.
3. A precise statement of *why* pure-delay reasoning is pessimistic about
   pulses.

## Fidelity to 7-series silicon

- **Band.** For a routed arc (driver pin to sink pin):
  - `lo` = prjxray's **fast-corner min**, summed or Elmore-computed along the
    arc with `prjxray/timing.py`.
  - `hi` = **slow-corner max**.

  Research's PROGRAM says the board should fall inside [fast min, slow max] and
  not on any one corner. The band is that interval. Two cautions apply:
  - prjxray matches Vivado to about ±1.5% on non-clock nets, so `lo` and `hi`
    should be padded by that tolerance (`chan_mono` makes any padding sound).
  - The data must be for the board's speed grade (-1).

  Explicit hypothesis H-band: every transition through the arc on this die is
  delayed by a value in [fast min, slow max] (padded). Test: the n=128 ring
  periods must lie inside the summed bands (`chan_comp_iff`). A ring slower
  than the slow max refutes the model or the data.
- **Composition caveat.** `chan_comp_iff` says bands add along a series of
  *independent* channels. Elmore RC is not segment-additive, because the
  downstream C loads the upstream driver. So the band must be computed per
  sink arc by the RC-tree calculator, not by adding per-pip bands taken out of
  context. Per-pip bands are only sound if each pip's band already covers
  every load it can see.
- **FIFO and annihilation.** These hold for buffered pips (CMOS stages).
  Pass-transistor pips plus wire RC are also order-preserving (an RC network
  is monotone). Hypothesis H-fifo: no routed arc reorders edges. A GLS
  transport delay with rise ≠ fall can be checked against `pulse_out_*`.
- **Where the model is pessimistic (sound but loose).**
  - It lets the delay jump anywhere in the band between two edges a picosecond
    apart. Real variation within a run is (a) the rise/fall asymmetry, which is
    tens of ps, and (b) slow PVT drift.
  - So `pulse_can_vanish` overstates collapse. A real wire kills only pulses
    narrower than roughly the rise/fall skew plus inertial filtering, not
    narrower than the whole PVT band.
  - `SkewRetime` (Wip) is the refinement for this. Its κ would come from the
    rise/fall columns of the prjxray SDF cell arcs (pips have no rise/fall in
    prjxray, so κ for wires is an explicit hypothesis to be measured).
- **Where it is optimistic.** It is binary. A narrow pulse really produces a
  runt or half-level output that a downstream LUT may see as anything. That
  belongs to the inertial and involution channels (tracks b and c), not to
  this one. For pulses narrower than about 2× a stage delay, use those.
- **Relation to today's GLS.** `cells/gls/prims.v` models each routed arc as a
  transport delay (ICBUF) with one fixed number per run. Corners are runs at
  x0.9 and x1.1. Each GLS run is one `chan_shift` behaviour, the `lo = hi`
  case. The proofs cover the whole band, including delays that differ between
  edges and between arcs, which GLS samples only at a few points.
