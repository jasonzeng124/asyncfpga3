# bd_arbcell: what is established, and what is not

`bd_arbcell` is the decision element of a two-way mutual-exclusion
arbiter, built from two LUTs on xc7. It is the only cell in this library
whose correctness is a *rate* rather than a property, and this document
separates what has actually been demonstrated about it from what has
not.

The short version: the cell's structure, its exclusion property, and its
handover margin are established, in two independent simulation regimes
and against a routed netlist. Its metastability failure rate is not
established, and the rig built to measure it has so far measured its own
instrumentation instead.

## Structure

One state node, read straight and complemented:

```
q  = C(r1, ~r2)          bd_c2n_set, one LUT6 in combinational feedback
g1 = r1 . q              one fractured LUT6_2, O5
g2 = r2 . ~q             the same LUT6_2, O6
```

A C-element is an SR latch whose set is `r1.~r2` and whose reset is
`~r1.r2` — the two conditions under which one channel is unambiguously
asking alone. On a tie both are false, `q` holds, and the previous
winner is asked to give way first. Because `q` only ever moves while
exactly one request is up, sustained contention forces alternation.

The complement is free: `~q` is a bubble on the pin that reads it, and
an inverter is never a cell on this fabric. So there is one feedback
wire in the whole element and one logic level in its loop. The textbook
NAND mutex has two of each, and loop delay is what sets the resolution
time constant, so this construction is strictly better placed than the
textbook one for the failure mode that matters.

Two LUTs total. `verify/lutcost.py` confirms this against a synthesised
netlist rather than by inspection.

### Both grants must occupy one fractured site

This is a placement requirement, not a preference. Two separate LUTs
have identical intrinsic delay but land in different sites with
different routing, and routing on this part moves about a nanosecond
between builds. One fractured `LUT6_2` has a fixed O5-versus-O6 delta of
tens of picoseconds, identical every time.

A constant asymmetry only biases tie-breaking, which is harmless. An
asymmetry that moves between builds means a measured failure rate does
not transfer to the next bitstream, which would make any
characterisation worthless. `hw/check_fracture.py` enforces this against
the routed netlist and records a baseline so that a later build which
silently unfractured a pair is caught rather than trusted.

## Exclusion holds for a settled q

Exactly one of `q` and `~q` is high, so at most one grant can be. Both
grant LUTs read the same net, so no amount of routing skew changes which
value it holds. This is structural and needs no timing argument.

## The handover margin holds, and this was measured

Exclusion *during handover* is a weaker claim and had to be checked
rather than asserted. When `q` toggles, one grant must fall while the
other rises. On this fabric a LUT falls roughly 2.5x slower than it
rises — from prjxray's characterised arcs, O5 rise 55 ps / fall 152 ps,
O6 rise 56 ps / fall 124 ps. With cell arcs alone the falling grant is
still high when the rising one arrives, and `g1 & g2` is briefly true.

Interconnect delays both edges equally. It does not widen the overlap;
it moves the whole decode past it. So the margin is one that routing
supplies, and the question is whether real routing supplies enough.

Two independent benches answer this, reaching the same conclusion by
different paths:

- **`tb/tb_arb.v`** drives the full arbiter through protocol sequences
  and counts overlap instants during handover.
- **`tb/tb_arb_overlap.v`** drives a bare `bd_arbcell` with two
  free-running, non-commensurate oscillators (4108 ps and 5461 ps
  half-periods) so that relative phase sweeps the entire offset window
  rather than sampling one point in it, and counts every overlap.

| regime | `tb_arb` overlaps | `tb_arb_overlap` overlaps |
| --- | --- | --- |
| `BD_ROUTE_PS=0` (arc-only) | 1 | 89 |
| `BD_ROUTE_PS=354` (routed) | 0 | 0 |

Both regimes are gated in `check.sh` and both are green.

The arc-only regime is deliberately hostile: it is the library at its
most fragile, since routing is about 74% of a real hop and an arc-only
figure lands roughly three times short. That the hazard appears there is
what makes the routed result meaningful — a bench that only ran in the
routed regime would pass without ever exercising the thing it claims the
margin covers. `tb_arb_overlap` asserts *both* directions for exactly
this reason: it fails if the hazard disappears from the arc-only regime,
because that would mean the bench had stopped testing anything.

The overlap that does appear arc-only is narrow. Measured width is 8 to
16 ps, consistent with the fixed arc delta above, and one link of delay
filtering removes every instance of it (89 of 89). This matters for the
next section.

## The width discriminator

A structural overlap and a metastable excursion are different in
duration by orders of magnitude, and that makes them separable:

```
filtered = raw & bd_delay(W)(raw)
```

An overlap survives only if it is still true `W` links later. Two LUTs.
The `(* keep *)` attribute is required on the AND, because an optimiser
would otherwise notice that `a & delay(a)` is "just `a`" and fold the
delay away; the delay is the entire point and it is invisible to logic
optimisation.

Measured passband, from injecting known-width pulses through the filter
in simulation:

| pulse width | survives W=1 | survives W=2 |
| --- | --- | --- |
| ≤ 80 ps | no | no |
| 160 ps | yes | no |
| 320 ps and above | yes | yes |

A clean cutoff, and it sits where it needs to: the ~16 ps structural
overlap is rejected outright, while anything on the order of a real
resolution time constant passes. The same construction is used by the
threshold ladder in `hw/arb_mtbf.v` to calibrate the detector floor, so
the passband is measured on the die rather than assumed.

This filter works and is deployed. It is genuinely useful independent of
the MTBF question: it makes a detector *selective* rather than merely
sensitive.

## What is NOT established: the failure rate

A LUT is a digital mux tree. It will propagate whatever voltage its
input reaches, including a metastable intermediate. A Seitz mutex is
this decision element plus an analog metastability filter, and the
filter is the part that makes the name mean something — it is not
buildable on this fabric at all.

So on near-simultaneous requests this cell can not only go metastable,
it can hand a metastable level straight to its grant outputs, which is
the one failure mode the analog filter exists to prevent. A plain tie
(both requests rising together from idle) is resolved deterministically,
since set and reset are both false and `q` simply holds. What remains is
a runt on the set or reset condition: `r1` and `r2` moving in opposite
senses within one loop delay of each other, driving the loop for less
time than it needs to commit.

What is available instead of a filter is resolution time. Metastability
decays exponentially, so added stages buy MTBF without a true filter.
That turns "is this correct" into "what is the failure rate", and the
failure rate must be measured on silicon. `verify/MTBF.md` is the
procedure and `hw/arb_mtbf.v` is the rig.

**No simulation in this tree can discharge that obligation.** A LUT in
`sim/bd_prims_sim.v` resolves in one arc, always. Every overlap counted
by either bench above is an ordinary digital hazard. That is precisely
why the width filter can be calibrated against them — everything the
benches count is the thing the filter must reject — but it is also why a
green `check.sh` says nothing whatsoever about the metastability rate.

### The depth ladder measures itself, not the cell

The rig's original design was a ladder of channels, each feeding `q`
through a `bd_delay` chain of a different length before the grant
decoder reads it, on the theory that more delay buys more resolution
time and the anomaly rate should fall with depth.

It rises with depth instead, monotonically, in both simulation and
hardware. The reason is that only `q` is delayed — `r1` and `r2` reach
the decoder live. `q` toggles only while `r1 != r2`, so at the instant
`q` moves, `r1 & r2` is false and no overlap is possible. Delay `q` by
N links and that protection is gone: the decoder reads a *stale* `q`
against live requests, and the window over which the two can disagree
grows with N.

So the ladder measures a decorrelation window that it creates itself.
Nothing in it is metastability. A matched-delay variant (delaying `r1`
and `r2` by the same chain) was tried in simulation and made the count
worse at every depth, so the obvious fix is not a fix.

The correct instrument is a **width** ladder rather than a depth ladder:
decode the unmodified cell, then ask how long the ambiguity persisted,
by filtering the raw overlap at a range of widths. Every channel is then
bit-for-bit the library cell, `q` is never delayed, and the quantity
measured — the rate at which grant ambiguity outlives T — is the MTBF
question as stated. This is verified in simulation but is not yet the
deployed rig.

## Current hardware status

Deployed build, seed 12, width discriminator on all six channels,
running against two free-running rings at approximately 122 MHz and
92 MHz.

Depth 0 is `bd_delay` with N=0, a straight bypass, so that channel is
bit-for-bit the unmodified library cell. After 2.47 hours and roughly
5.3e12 stimulus edges:

```
depth 0   (   0 ps)  clean      [FILTERED:clean]    0 window-hits
depth 1   ( 121 ps)  clean      [FILTERED:clean]    0 window-hits
depth 2   ( 944 ps)  FIRED      [FILTERED:clean]
depth 4   (1064 ps)  FIRED      [FILTERED:FIRED]
depth 8   (3295 ps)  FIRED      [FILTERED:FIRED]
depth 16  (6413 ps)  FIRED      [FILTERED:FIRED]
```

The unmodified cell has recorded zero events, on both the sticky bit and
the free-running counter. Before the width filter was added, every
channel including depth 0 saturated at approximately 97% of all windows
with the overflow flag set; the filter took depths 0 and 1 to exactly
zero and removed overflow everywhere. That is the clearest evidence that
the earlier saturation was the structural overlap and not the cell.

Read this for what it is. It is a strong *negative* result on the
unmodified cell over a real exposure, and it is consistent with both
simulation regimes. It is not a measured MTBF, and it cannot become one
until the ladder is replaced, because the channels that still fire are
firing on an artifact of their own instrumentation.

## Summary

| claim | status | evidence |
| --- | --- | --- |
| two LUTs, one fractured site | established | `verify/lutcost.py`, `hw/check_fracture.py` |
| exclusion for settled `q` | established | structural |
| handover margin holds when routed | established | `tb_arb`, `tb_arb_overlap`, both regimes |
| overlap exists arc-only, and is narrow | established | 8–16 ps measured, 89/89 filtered out |
| width filter separates the two | established | measured passband, deployed |
| unmodified cell clean over 2.47 h | observed | hardware, seed 12 |
| metastability failure rate | **not established** | requires the width ladder |

The cell is sound as far as anything short of a metastability
measurement can establish. That measurement remains outstanding, and
`rtl/bd_arb.v`'s header is correct that nothing in this tree discharges
it — not one gate, not all of them.
