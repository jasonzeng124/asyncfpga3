# Measuring `bd_arbcell`'s failure rate

`rtl/bd_arb.v` says the failure rate must be measured on hardware and that
nothing in this tree discharges the obligation. This file is the procedure it
points at. It is not a gate — it is a long-running experiment on the board, and
it is the first thing in this project that genuinely cannot be done at a desk.

## Why it cannot be simulated

`tb_arb` runs the arbiter through forty contended transactions in two timing
regimes and passes. That result is worth exactly what it costs: a Verilog LUT
model resolves every input to 0 or 1 in zero time and will never produce the
intermediate voltage the whole question is about. There is no version of this
bench that finds a metastability failure, so a green run is not evidence.

The cell is the decision element of a mutex. A Seitz mutex is that element plus
an analog metastability filter, and on a LUT fabric the filter is not buildable
at all — a LUT is a digital mux tree that will propagate whatever level reaches
its input, including an intermediate one, straight to both grant outputs. What
is buildable is *resolution time*: metastability decays exponentially, so extra
stages between the decision and its consumers buy MTBF without a filter. The
question is therefore not "is this correct" but "what is the failure rate", and
that is a measurement.

## The failure mode to look for

A plain tie — both requests rising together from idle — is not it. Set
(`r1·¬r2`) and reset (`¬r1·r2`) are both false there, so `q` holds and the
previous winner takes it, deterministically. `tb_arb` covers that case.

What remains is a **runt on the set or reset condition**: `r1` and `r2` moving
in opposite senses within one loop delay of each other, driving the loop for
less time than it needs to commit. That is the event to sweep through.

## The experiment

**Stimulus.** `r1` and `r2` are each driven by a self-timed four-phase client
of the form `r = bd_delay(~A)` — the client re-requests as soon as its own
acknowledge falls, with no external clock. The two clients use different chain
lengths (CLEN1=3, CLEN2=5), so their loop periods differ and the relative
phase between `r1` and `r2` drifts continuously across the full range instead
of sitting still. The point of that drift is the same as it would be for any
other source of a slowly-changing offset: a fixed phase relationship can sit in
a safe part of the decision window for hours and prove nothing, so the rig
needs the offset to keep moving. Building both clients from `bd_delay` chains
means they share the primitive, and hence the PVT behaviour, of everything else
in the library.

**Detection.** Each instance carries three sticky bits. `viol` is `A1·A2`,
both clients acknowledged at once — the protocol defect described below, kept
as a canary in case it ever comes back. `ovl` is `g1·g2` after width
filtering, a real grant overlap. `serv` is `A1^A2`, exactly one client
acknowledged, and this bit must set: a LUT feedback latch that never fires
reads identically to one that structurally cannot, so an instance whose
counters are all zero after hours on the board is indistinguishable from one
that never ran. Instances with `serv` unset are excluded from the denominator
rather than counted as zero anomalies.

**Readout.** The counters are read back over BSCANE2 / JTAG, driven from the
host by `hw/arb_prot_measure.py`. There is no PS involvement and no AXI path;
the fabric is polled directly through the debug scan chain.

**Filtering, not sweeping.** The original plan was a sweep over resolution-
stage depth, fitting MTBF against depth on the theory that one depth is a data
point and the slope is the result. That sweep is retired. Only `q` was ever
going to be delayed in that scheme, not `r1` and `r2`, so the depth ladder
measured a decorrelation window the ladder itself created rather than a
property of the cell — deeper resolution looks better in that setup for
reasons that have nothing to do with metastability decay. It was replaced by a
width filter: `filtered = raw & bd_delay(2)(raw)` with WFILT=2, which keeps a
pulse only if it is still present two delay stages after it started. That
discriminates a real overlap, which persists, from a short glitch, which does
not — by pulse width, not by how much resolution depth was budgeted.

## Placement, and why the numbers do not transfer without it

Both grants must sit in **one fractured site**. Two separate LUTs have
identical intrinsic delay but land in different sites with different routing,
and routing on this part moves about a nanosecond between builds. One fractured
site has a fixed O5-versus-O6 delta of tens of picoseconds, identical every
time.

A constant asymmetry only biases which side wins a tie. An asymmetry that moves
between builds means a measured MTBF does not carry to the next bitstream —
which would make the whole characterisation worthless. So pin the site, and
re-measure if it moves.

`flow.sh` confirms the packing; it does not confirm the placement is stable
across builds, and that is worth checking before spending hours on the board.

## Results

Two rigs have run on the board.

`arb_mtbf`, the bare cell, is retired from the board. It carried 192
instances at W=2. 125 of them were eligible (`serv` set) across 13.77 hours,
for 1721 instance-hours of exposure. One instance arrived late — instance 30
first set `serv` at 2.35 h in — and is counted only from its arrival. Zero
`viol`, zero `ovl` across that exposure gives MTBF >= 1.7e3 h.

`arb_prot`, the arbiter as shipped, is currently running. It carries 96
instances, all 96 with `serv` set, zero `viol` and zero `ovl`. At 26.56 h
elapsed that is 8.868e14 arbitration events, and the Rule-of-Three 95% bound
on that exposure is MTBF >= 2.956e14 arbitrations. The measured handshake rate
is 96.60 MHz per instance against 97.5 MHz predicted by the routed simulation.

## The exposure figure is not a metastability bound

The arbitration-event count above is every handshake completed by every
eligible instance. That is the right denominator for the two structural
failure modes this rig actually watches for — early ack and grant overlap —
because either one can in principle occur on any arbitration, contested or
not. It is the wrong denominator for metastability.

A metastable decision requires both requests to arrive within the mutex's
decision aperture of each other. An arbitration where one request leads the
other by more than that aperture is settled by structural exclusion before the
mutex is ever in danger — it never had any chance to fail — and yet it is
counted in the total the same as a near-coincident one. The differing client
chain lengths mean the relative phase between `r1` and `r2` drifts and sweeps
through coincidence rather than locking onto a fixed offset, so the rig does
sample the dangerous window rather than avoiding it. But the fraction of
arbitrations that actually land inside the aperture, as opposed to outside it,
has not been measured. An aperture-over-period estimate puts that fraction at
order 1e-3, which would make the true bound on the metastability rate roughly
three orders of magnitude weaker than the figure quoted above.

Until that fraction is measured, the number in the Results section is a bound
on the total failure rate per arbitration — early ack, overlap, and
metastability combined — and must not be quoted as a bound on the
metastability rate specifically.

There are two ways to close that gap. One is to count near-coincident arrivals
in the routed simulation and rescale the measured bound by that fraction. The
other is to add a coincidence detector to the rig itself, so the board reports
its own contested-event count directly instead of the total event count. The
second option is a rebuild, and a rebuild erases the accumulated exposure —
`arb_prot`'s clock would start over at zero instance-hours.

## Reading the result

| Outcome | What it means for the compiler |
|---|---|
| MTBF ≫ design life | Real arbiters stand. An arbitrated merge becomes a component with a settle-time budget, and the compiler may emit one wherever exclusivity cannot be established structurally. |
| MTBF comparable to design life | Arbitration is expensive. Prefer structural exclusion, and arbitrate only where the program genuinely forces it. |
| No usable MTBF | The arbitrated merge is off the table on this fabric. Every merge must then be provably exclusive by construction, which is a constraint on the frontend, not on this library. |

## The protocol defect is already out of the way

`bd_arbiter` as specified manufactured acknowledges under sustained contention
— see the finding in `rtl/bd_arb.v` and the numbers in `tb_arb`. The cell now
holds `q` on ack unconditionally, so that deterministic defect can no longer
dominate the anomaly counter and bury the metastability signal, which is the
entire point of the experiment. There is no parameter to remember to set.
