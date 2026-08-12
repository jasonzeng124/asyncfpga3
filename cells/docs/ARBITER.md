# bd_arbcell / bd_arbiter: what is established, and what is not

`bd_arbcell` is the decision element of a two-way mutual-exclusion arbiter,
built from two LUTs on xc7. `bd_arbiter` is that element wrapped in the
four-phase protocol, and it is the thing a compiler backend emits. This is the
only cell in the library whose correctness is a *rate* rather than a property,
and this document separates what has been demonstrated from what has not.

The short version: the structure, the cost, and exclusion for a settled state
are established. Exclusion during handover is established for `bd_arbiter` and
conditional for the bare cell. The metastability failure rate is bounded, not
known. And one hardware observation — that about 8% of identically-built copies
of the bare cell glitch permanently while the rest never do — **remains
unexplained after six hypotheses were tested and refuted.**

## Structure

One state node, read straight and complemented:

```
q  = C(r1, ~r2)          one LUT6 in combinational feedback
g1 = r1 . q              one fractured LUT6_2, O5
g2 = r2 . ~q             the same LUT6_2, O6
```

A C-element is an SR latch whose set is `r1.~r2` and whose reset is `~r1.r2` —
the two conditions under which one channel is unambiguously asking alone. On a
tie both are false, `q` holds, and the previous winner is asked to give way
first. Because `q` only ever moves while exactly one request is up, sustained
contention forces alternation.

The complement is free: `~q` is a bubble on the pin that reads it, and an
inverter is never a cell on this fabric. So there is one feedback wire in the
whole element and one logic level in its loop. The textbook NAND mutex has two
of each, and **loop delay is what sets the resolution time constant**, so this
construction is strictly better placed than the textbook one for the failure
mode that matters. That is not a small point — it is the only lever on the
failure rate that the cell itself controls, and this cell is already at its
optimum.

Two LUTs for the element, four for the arbiter. `verify/lutcost.py` confirms
both against a synthesised netlist rather than by inspection.

### Both grants must occupy one fractured site

A placement requirement, not a preference. Two separate LUTs have identical
intrinsic delay but land in different sites with different routing, and routing
on this part moves about a nanosecond between builds. One fractured `LUT6_2`
has a fixed O5-versus-O6 delta of tens of picoseconds, identical every time.

A constant asymmetry only biases tie-breaking, which is harmless. An asymmetry
that moves between builds means a measured failure rate does not transfer to
the next bitstream, which would make any characterisation worthless.
`hw/check_fracture.py` enforces this against the routed netlist and records a
baseline, so a later build that silently unfractured a pair is caught rather
than trusted. In `bd_arbiter` the *state* node is fractured too — `q` on O6
paired with `R0` on O5 — and the same gate covers it, because if that pair
splits the arbiter stops being four LUTs and `R0` stops reading the same `q`
the grants read.

## Exclusion has three tiers

They must not be quoted as one.

| tier | status | why |
| --- | --- | --- |
| settled `q` | **structural** | exactly one of `q`/`~q` is high; both grants read the same net |
| during handover | **structural in `bd_arbiter`** | the ack-hold separates the grants by a server round-trip |
| metastable `q` | **not excluded** | rate must be measured; intrinsic to arbitration |

### Settled

Exactly one of `q` and `~q` is high, so at most one grant can be. Both grant
LUTs read the same net, so no amount of routing skew changes which value it
holds. Structural; no timing argument.

### During handover

A weaker claim for the bare cell. When `q` toggles, one grant must fall while
the other rises, and on this fabric a LUT falls roughly 2.5x slower than it
rises — prjxray's arcs are O5 rise 55 / fall 152, O6 rise 56 / fall 124. With
cell arcs alone the falling grant is still high when the rising one arrives.
Interconnect delays both edges equally, so it does not widen the overlap; it
moves the whole decode past it. The margin is one that routing supplies.

Two independent benches confirm this for the bare cell, by different paths.
`tb/tb_arb.v` drives the full arbiter through protocol sequences;
`tb/tb_arb_overlap.v` drives a bare `bd_arbcell` from two free-running,
non-commensurate oscillators so relative phase sweeps the whole offset window.

| regime | `tb_arb` overlaps | `tb_arb_overlap` overlaps |
| --- | --- | --- |
| `BD_ROUTE_PS=0` (arc-only) | 1 | 89 |
| `BD_ROUTE_PS=354` (routed) | 0 | 0 |

Both are gated in `check.sh` and both are green. The arc-only regime is
deliberately hostile — routing is about 74% of a real hop — and
`tb_arb_overlap` asserts *both* directions, so it fails if the hazard ever
disappears from the arc-only regime, because that would mean the bench had
stopped testing anything.

**In `bd_arbiter` this tier is not a timing question at all.** The state node
holds `q` while the shared resource is acknowledging, so the falling and rising
grants are separated by an entire server round-trip instead of racing within
~100 ps. See `rtl/bd_arb.v`'s header for why that hold is unconditional and has
no parameter to turn it off.

### Metastable

A LUT is a digital mux tree. It propagates whatever voltage its input reaches,
including a metastable intermediate. A Seitz mutex is this decision element
plus an analog metastability filter, and the filter is the part that makes the
name mean something — it is not buildable on this fabric at all.

So on near-simultaneous requests this cell can not only go metastable, it can
hand a metastable level straight to its grants. A plain tie (both requests
rising together from idle) resolves deterministically, since set and reset are
both false and `q` simply holds. What remains is a runt on the set or reset
condition: `r1` and `r2` moving in opposite senses within one loop delay.

**The ack-hold does not fix this and nothing here can.** It does not even
relocate the race to a safe place: `q`'s evaluation window opens at ack-fall,
and a request arriving on that edge is exactly the runt condition. What it
plausibly buys is *aperture* — `q` is live only between ack-fall and the next
grant rather than continuously — which is a rate argument and is not measured.

This is not a defect of this cell. Every arbiter in every technology can be
raced; the analog filter changes the rate, not the existence. The two levers on
that rate are loop delay, where this construction is already optimal, and the
consumer's distance from the decision. Metastability decays exponentially, so a
grant read N hops downstream has had N hops to resolve, and four-phase bundled
data puts a full handshake in between. **A consumer must not read a grant
within one loop delay of the decision.** That is the cell's only obligation on
its user.

## The width discriminator

A structural overlap and a metastable excursion differ in duration by orders of
magnitude, which makes them separable:

```
filtered = raw & bd_delay(W)(raw)
```

An overlap survives only if it is still true `W` links later. Two LUTs. The
`(* keep *)` attribute is required on the AND, because an optimiser would
otherwise notice that `a & delay(a)` is "just `a`" and fold the delay away.

Measured passband, from injecting known-width pulses in simulation:

| pulse width | survives W=1 | survives W=2 |
| --- | --- | --- |
| ≤ 80 ps | no | no |
| 160 ps | yes | no |
| 320 ps and above | yes | yes |

**The deployed rigs use W=2, not W=1.** One link was tried first and hardware
refuted it: at one link, 50 of 192 population instances recorded permanent
filtered events; at two links, 15 did. The price is stated with the result — a
two-link filter measures the rate of ambiguity outliving ~160 ps, not the rate
of ambiguity, and an MTBF is always quoted against a resolution time.

## The depth ladder was retired

The original rig was a ladder of channels, each feeding `q` through a
`bd_delay` chain of a different length before the grant decoder read it, on the
theory that more delay buys more resolution time and the anomaly rate should
fall with depth.

It rose with depth instead, monotonically, in both simulation and hardware.
Only `q` was delayed — `r1` and `r2` reached the decoder live. `q` toggles only
while `r1 != r2`, so at the instant `q` moves no overlap is possible; delay `q`
by N links and the decoder reads a *stale* `q` against live requests, over a
window that grows with N. The ladder measured a decorrelation window it created
itself. A matched-delay variant (delaying `r1` and `r2` equally) was tried and
made the count worse at every depth.

The replacement is a **width** ladder: decode the unmodified cell, then ask how
long the ambiguity persisted. Every channel is then bit-for-bit the library
cell and `q` is never delayed. That is what `hw/arb_mtbf.v` deploys.

## Hardware: the bare cell

`hw/arb_mtbf.v`, 192 independent depth-0 instances, W=2, driven by two
free-running rings at ~342 MHz and ~260 MHz.

```
RAW      fired: 139/192     (positive control: the structural overlap)
FILTERED fired:  15/192     [0,5,21,29,30,35,38,57,76,85,89,90,157,177,179]
  14 of those fired within 2 min of load -- structurally broken placements
  1 LATE ARRIVAL: instance 30, clean at load, fired at 2.35 h

exposure   125 eligible instances x 13.77 h = 1721 instance-hours
bound      MTBF >= 1.7e3 h   (95% CI 0.066 .. 197 years)
```

### The 8% is not explained

Fifteen of 192 identically-built copies glitch permanently; 177 never do. All
192 are structurally identical in the routed netlist — detector on O6, grants
on O5/O6, filter LUTs INIT-identical, C-element feedback intra-site at 0 ps.
Only routing delays and pin assignments differ, and 191 of the 192 routed
signatures are distinct, so the design contains no natural pair of "the same
copy built twice".

Refuted, each across all 192 rather than on a pair:

- **LUT input pin for `q`, as originally claimed** — the explanation in commit
  `eadeb23` was a two-point fit quoting arcs from a build whose placement no
  longer existed.
- **grant→detector interconnect skew** — 146 copies at *exactly* 0 ps skew
  still fire at 6.8%.
- **the width filter's own race margin** — p = 0.60.
- **die position / process variation** — no spatial clustering, p = 0.23.
- **"badness is a fixed per-copy property"** — 43 of 50 bad copies became clean
  on rebuild; the overlap between builds is barely above chance.
- **~20 further netlist quantities**, screened together: nothing survives
  multiple-comparison correction.

A full rise/fall-aware prediction — per-pin O5 arcs, O6 flat, per-instance
routing, both edges, the +68 ps stretch each O6 LUT adds to a positive pulse —
caps the structural overlap at 96 ps at zero skew against a minimum filter
threshold of 203 ps. **It predicts that no copy should ever fire.** Ten
zero-skew copies fire continuously. So the surviving pulses are not the
handover overlap, and the mechanism is below what the flow's timing model can
express.

One lead survives, and it is a lead and not a cause: copies where `q` touches
pin **A5** on either the C-element feedback or the grant decoder fire at 2/107,
the rest at 13/85 (selection-corrected permutation p = 0.0006; within the 146
zero-skew copies alone, 1/77 vs 9/69, p = 0.005). prjxray characterises O5 per
pin and O6 not at all, so per-pin O6 differences are a gap in the
characterisation data rather than a fact about the silicon — a LUT6 is a mux
tree and its pins cannot really be identical. The confirming test is a build
with `q` forced to A5 everywhere; it has not been run.

**None of this is a property of `bd_arbiter`.** The rig drives the bare
element from two oscillators that ask 10^8 times a second and ignore the
answer, with no protocol, no server and no back-pressure. That is the right
scope for characterising the element and the wrong scope for quoting a number
about a compiled design.

## Hardware: the arbiter as shipped

`hw/arb_prot.v` measures the configuration a compiler emits: 96 instances of
`bd_arbiter`, each with a real four-phase server and two self-timed clients
that always want the resource back. Three sticky bits per instance:

```
serv  A1 ^ A2   normal exclusive service       MUST be 1
viol  A1 . A2   both clients acked at once     MUST be 0
ovl   g1 . g2   both grants high, filtered     MUST be 0
```

`viol` is the exact signature of the protocol defect written up in
`rtl/bd_arb.v`: `A1 = C(g1,A0)` is still *holding* high when `g2` rises against
a still-high `A0`. The unheld state node manufactured half its acknowledges.

**`serv` is why the zeros mean anything.** Every detector here is a LUT
feedback latch, and a latch that never sets reads identically to one that
cannot. An instance whose `serv` bit is clear has proved nothing and is
excluded from the denominator. `tb/tb_arb_prot.v` gates this in simulation
before any hardware time is spent, in both timing regimes.

Latest poll, 26.56 h elapsed:

```
serv  96/96
viol   0/96
ovl    0/96

exposure   8.868e14 arbitration events
bound      MTBF >= 2.956e14 arbitrations   (95% CI, Rule of Three)
rate       96.60 MHz per instance, measured on die
```

The host was disconnected for roughly 14 h of that span — the JTAG cable
detached from the WSL guest — and the run was unaffected, because the host only
reads. That the design still answers with its correct constants and tag after
the gap is what makes the dark hours countable: the fabric is SRAM-configured
and this bitstream lives nowhere but the fabric, so a design that still responds
is a design that never lost power. The constant check is the continuity witness.
The free-running handshake counter is not, and cannot be — `hold_run` gates it,
so it only advances during measurement windows and says nothing about the
interval between polls.

Exposure is counted in **arbitration events, not seconds** — instance 0's
client-1 request drives a counter, so the handshake rate is measured on the die
rather than estimated from chain lengths.

### The event count is the wrong denominator for metastability

Counting arbitration events is right for the two structural failure modes —
early ack and grant overlap — because either can in principle occur on any
arbitration. **It is the wrong denominator for metastability.** A metastable
decision requires both requests to arrive within the mutex's decision aperture
of each other. Arbitrations where one request leads the other by more than
that aperture are settled by structural exclusion and never had a chance to
fail, yet they are counted in the total all the same.

The two client chains have different lengths (CLEN1=3, CLEN2=5), so their
relative phase drifts and sweeps through coincidence rather than locking away
from it — the rig samples the dangerous window rather than avoiding it — but
the **fraction** of arbitrations that land inside the aperture has never been
measured. An aperture-over-period estimate puts it at order 1e-3, which would
make the real bound on the metastability rate about three orders of magnitude
weaker than the figure the script prints. Until that fraction is measured, the
quoted number bounds the **total** failure rate per arbitration and must not
be quoted as a bound on the metastability rate.

There are two fixes: count near-coincident arrivals in the routed simulation
and rescale, or add a coincidence detector to the rig so the board reports its
own contested-event count. The latter is a rebuild, and a rebuild erases the
accumulated exposure.

## Summary

| claim | status | evidence |
| --- | --- | --- |
| two LUTs / four LUTs, fractured sites | established | `verify/lutcost.py`, `hw/check_fracture.py` |
| exclusion for settled `q` | established | structural |
| handover margin, bare cell, routed | established | `tb_arb`, `tb_arb_overlap`, both regimes |
| handover exclusion in `bd_arbiter` | established | the ack-hold; `tb_arb` |
| width filter separates the two | established | measured passband, deployed |
| bare cell, 192 copies, 1721 instance-hours | observed | 1 late arrival, bound quoted |
| why 8% of copies glitch permanently | **unexplained** | six hypotheses refuted; one lead |
| metastability failure rate | **bounded, not known** | requires `arb_prot` on silicon |

The cell is sound as far as anything short of a metastability measurement can
establish, and `rtl/bd_arb.v`'s header is correct that nothing in this tree
discharges that obligation — not one gate, not all of them.
