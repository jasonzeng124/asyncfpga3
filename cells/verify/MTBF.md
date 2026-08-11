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
question is therefore not "is this correct" but "what is the failure rate at
depth N", and that is a measurement.

## The failure mode to look for

A plain tie — both requests rising together from idle — is not it. Set
(`r1·¬r2`) and reset (`¬r1·r2`) are both false there, so `q` holds and the
previous winner takes it, deterministically. `tb_arb` covers that case.

What remains is a **runt on the set or reset condition**: `r1` and `r2` moving
in opposite senses within one loop delay of each other, driving the loop for
less time than it needs to commit. That is the event to sweep through.

## The experiment

**Stimulus.** Drive `r1` and `r2` from two independent ring oscillators at
slightly different frequencies. The point of the frequency offset is that the
phase relationship sweeps continuously through the decision window instead of
sampling it at one fixed offset — a single offset can sit in a safe part of the
window for hours and prove nothing. Build the rings from `bd_delay` chains of
different lengths so they share the primitive, and hence the PVT behaviour, of
everything else in the library.

**Detection.** An anomaly is either grant asserted together, or neither
asserted within a timeout after a request. Both are cheap to detect
combinationally; latch either into a sticky bit and count it.

**Readout.** Expose the counter to the PS over M_AXI_GP0 and poll it. Run for
hours per configuration — the whole value of the experiment is in the tail.

**Sweep.** Repeat for a range of resolution-stage counts and fit MTBF against
depth. One depth is a data point, not a result; the slope is the result.

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
across builds, and that is worth checking before spending hours on a sweep.

## Reading the result

| Outcome | What it means for the compiler |
|---|---|
| MTBF ≫ design life at modest depth | Real arbiters stand. An arbitrated merge becomes a component with a settle-time budget, and the compiler may emit one wherever exclusivity cannot be established structurally. |
| Acceptable only at large depth | Arbitration is expensive. Prefer structural exclusion, and arbitrate only where the program genuinely forces it. |
| No usable MTBF | The arbitrated merge is off the table on this fabric. Every merge must then be provably exclusive by construction, which is a constraint on the frontend, not on this library. |

## One thing to fix before running it

`bd_arbiter` as specified manufactures acknowledges under sustained contention
— see the finding in `rtl/bd_arb.v` and the numbers in `tb_arb`. Sweep with
`HOLD_ON_ACK(1)`. Otherwise the anomaly counter will be dominated by a
deterministic protocol defect and the metastability signal, which is the entire
point of the experiment, will be buried under it.
