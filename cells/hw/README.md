# `hw/` — the gate that runs on silicon

Seven gates check this library and every one of them is a statement about the
toolchain. That yosys emits the cells. That nextpnr packs and routes them. That
the SDF it writes is self-consistent with itself. **None of them asks whether
the SDF is true of the die**, and every matched delay in the library is sized
against it. If the model were wrong by a factor, every delay would be wrong by
that factor and nothing else here would ever say so.

This is that measurement.

```
hw/build_hw.sh ro_top          # synth, route, bitstream
python3 hw/ro_measure.py       # load, run, compare, verdict
```

Nonzero exit means the readback failed its own checks, a counter overflowed, a
ring ran *slower* than predicted, or a single scale factor does not explain the
error. It never asks anyone to read an LED.

---

## The result, 2026-08-03, `xc7z010clg400-1` on an EBAZ4205

Five ring oscillators, each a `bd_delay` chain of a different length closed
through one inverter, counted over three 8-second windows.

| ring | links | period measured | period from the routed SDF | ratio |
|---|---|---|---|---|
| 0 | 7 | 8 093 ps | 8 290 ps | 0.976 |
| 1 | 15 | 12 204 ps | 13 576 ps | 0.899 |
| 2 | 31 | 22 924 ps | 24 842 ps | 0.923 |
| 3 | 63 | 52 075 ps | 56 784 ps | 0.917 |
| 4 | 127 | 103 094 ps | 103 418 ps | 0.997 |

Reproducibility across the three windows was 0.01–0.02%.

**measured = 0.975 × predicted, across an 18× span of ring length.** Silicon
runs 2.5% faster than nextpnr's routed SDF says it will. Taking that one factor
out leaves 8.5% worst case, and the residual does not trend with length
(+0.1%, −8.5%, −5.7%, −6.3%, +2.2%) — so it is per-route scatter, what nextpnr
charged for *these particular nets* against what they cost, and not a
systematic error in the shape of the model.

> **Superseded — read this before quoting the paragraph above.** 128 rings
> (below, "The population, 2026-08-23 — 128 rings, `ro_many_top`") contradict two of its
> three claims. The residual *does* trend with length, and *not* every ring runs
> faster than predicted — 76 of 128 ran slower. 8.5% is the 52nd percentile of
> the population, i.e. a median, not a worst case. The one claim that survived
> is that the scatter is per-route rather than systematic.

### That table is one route, and a rebuild disagrees with it

`ro_top` was rebuilt on 2026-08-18 and re-measured on 2026-08-23. Same RTL,
same five rings, different nextpnr placement:

| ring | links | period measured | period from the routed SDF | ratio |
|---|---|---|---|---|
| 0 | 7 | 6 293 ps | 4 674 ps | 1.346 |
| 1 | 15 | 12 140 ps | 12 008 ps | 1.011 |
| 2 | 31 | 27 784 ps | 28 228 ps | 0.984 |
| 3 | 63 | 54 772 ps | 55 548 ps | 0.986 |
| 4 | 127 | 103 409 ps | 112 972 ps | 0.915 |

**measured = 0.933 × predicted, worst residual 30.7%**, and this time the
residual *does* trend with length — Spearman rho −0.90 against ring length,
where |rho| ≥ 0.9 is the 5% critical value at n = 5. `ro_measure.py` fails the
run on that, and it should: the docstring calls a length-trending residual the
case a single scale factor cannot fix.

Both the measured periods and the SDF moved, which is what rules temperature
out — a hotter die does not change what nextpnr predicted. Ring 0 is the whole
story: nextpnr predicted its loop would drop 8 290 → 4 674 ps (−44%) while
silicon only delivered 8 093 → 6 293 ps (−22%).

Two consequences, and neither is "the first table was wrong":

- **8.5% was never a measured bound, only a single sample.** It is the number
  `verify/tighten.py` spends as its guardband, so that guardband's provenance
  is one route of one design. Two routes is still n = 2; the honest statement
  is that the scatter is not yet characterised, not that it is 30.7%.
- **The error is worst on the shortest ring**, and short chains are most of
  what `tighten.py` emits — the gcd and collatz sizing logs are full of cells
  at 0→1, 1→2 and 2→3 links. Optimistic there means the built delay is
  *shorter* than the logic it covers, which is the silent direction.

Self-heating is not the confound. Six 8-second windows of continuous toggling
moved every ring by 0.011% or less, with 0 of 5 rings rising consistently —
fabric delay is stable to about one part in 10 000 under this load. That is a
small load for 48 s and says nothing about a warm enclosure.

The wall clock cannot account for it: over an 8-second window the host's timing
uncertainty is under a tenth of a percent, and it would in any case be a scale
factor applied equally to all five.

**Every ring ran faster than its prediction, which is the safe direction.** The
SDF is pessimistic, so a matched delay sized against it is longer than it
strictly needs to be. That costs area, not correctness. The failure that would
matter is the other sign — silicon slower than predicted would mean a delay
shorter than the logic it is meant to cover — and `ro_measure.py` fails on it.

So `tighten.py` rests on ground that has now been checked, and the number to
carry is that its inputs are good to about ten percent and err long.

*That last sentence did not survive n = 128. See below.*

---

## The population, 2026-08-23 — 128 rings, `ro_many_top`

Two routes is n = 2, and the section above says so. `ro_many_top.v` is the
same experiment as a **population**: 128 rings, 32 at each of 7, 15, 31 and 63
links, so the guardband becomes a percentile of a measured distribution instead
of the max of five samples.

```
hw/build_hw.sh ro_many_top      # 4543 LUT sites, 9 BUFGCTRL of 32
python3 hw/ro_many_measure.py   # sweeps 16 groups, judges itself
```

The blocker was global buffers, not LUTs: `ro_top` burns one BUFGCTRL per ring
and 6 of 32 was already at the edge of what this part's clock router manages.
So the counters are **time-multiplexed** — 8 slots, each with its own BUFG and
counter, over 16 groups scanned one at a time, with only the selected group
oscillating. 128 rings for 9 buffers, and the count does not grow with the
population. Ring lengths rotate by *both* group and slot, which decorrelates
length from both, so a slow slot cannot masquerade as a length effect.

| links | n | median ratio | p90 | p99 | max | 8.5% covers |
|---|---|---|---|---|---|---|
| 7 | 32 | 1.176 | 1.438 | 1.470 | 1.470 | **15.6%** |
| 15 | 32 | 0.987 | 1.117 | 1.203 | 1.203 | 56.2% |
| 31 | 32 | 0.959 | 1.085 | 1.142 | 1.142 | 56.2% |
| 63 | 32 | 0.969 | 1.059 | 1.134 | 1.134 | 81.2% |
| **all** | **128** | **0.989** | 1.252 | 1.457 | 1.470 | **52.3%** |

**8.5% is a median, not a guardband.** It covers the 52nd percentile of the
population — 48% of rings need more than it — and on 7-link chains it covers
15.6%. A p99 band would have to be 34.6%. Reproducibility across windows was
0.052%, so this is scatter between routes, not measurement noise.

**Ring 0's 1.346 was never an outlier.** Among 32 seven-link rings the ratio
runs 0.773 to 1.470 with a median of 1.176, and 22% of them are at least as bad
as 1.346. The rebuild that produced it drew an ordinary member of the
short-chain population, and `ro_measure.py` failed the run because five samples
cannot tell an ordinary draw from a defect.

### The length trend is an offset, not a slope

The short-chain effect is real at n = 32 — 7-link and 63-link residuals are
drawn from different distributions, Mann-Whitney p = 5.6 × 10⁻⁵ — but it is
**not a per-link error**:

| model | fit | per-length median residual | 7 vs 63 |
|---|---|---|---|
| one parameter | measured = 0.9616 × predicted | +18.3%, +2.5%, −0.3%, +0.8% | p = 5.6e−5 |
| two parameter | measured = 0.9383 × predicted **+ 988 ps** | +3.6%, −2.4%, −1.3%, +1.4% | p = 0.39 |

One fixed ~1 ns per loop removes the length dependence entirely. A constant is
a large fraction of a short chain and nothing at all of a long one, which is
the whole of the "short chains are worse" effect. **So the per-link cost —
the number `tighten.py` actually spends when it adds or removes a link — is
not what is wrong. What is wrong is a constant the model does not charge**,
and that argues for an additive correction, not a wider percentage.

It does not rescue the band: coverage moves only 52% → 60%, because the
residual scatter that remains is per-route and genuinely wide.

Whether that 988 ps is a property of the fabric, of this route, or partly of
this rig is **not settled**. Each ring node here feeds a mux leg as well as its
own chain, and an under-charged extra sink would be per-loop — exactly the
shape of the offset. `ro_top`'s rings tap a BUFG instead, which is also one
extra sink, so the rigs are alike in kind; but fitting an intercept to five
points where one is short gives an answer that flips sign between `ro_top`'s
two routes (−1596 ps and +2303 ps). Settling it needs a second `ro_many` route,
or a variant with the mux tap off the ring node.

### It is per-route scatter, not a bad region and not a bad slot

Permutation tests on the spread of per-label medians: by slot p = 0.73, by
group p = 0.66. Neither clusters. The worst decile spreads across 6 of 8 slots
and 9 of 16 groups. So the scatter is a property of the individual route —
what nextpnr charged for *these* nets against what they cost — and not of where
on the die a ring sits or which counter read it. That also clears the rig
itself: a slow BUFG or counter would have clustered by slot.

**76 of 128 rings ran *slower* than the scaled model**, which is the direction
a matched delay cannot absorb. On that side alone 8.5% covers 65% of the
population and p99 needs 34.0%. The 2026-08-03 table's "every ring ran faster
than its prediction, which is the safe direction" was a property of five
samples, not of the fabric.

### What this does not measure

A ring runs at its own natural rate with nothing loading it but the next stage
and one buffer tap. It is the delay of a chain, not the delay of a chain doing
anything, and a matched delay in a real cell sits beside logic contending for
the same routing. The agreement above is therefore the easy case. If the SDF
had disagreed *here* it would have been disqualifying; agreeing here is
necessary and not sufficient.

One die, one temperature, one route. The numbers expire the way `tighten.py`'s
do. The ratio is what carries.

---

## Walking a matched delay to failure, 2026-08-23

The 128-ring study above measures how well nextpnr's routed SDF predicts one
loop's ABSOLUTE delay. Rule A guards something else: the DIFFERENCE between a
request path and a data path. This is an attempt to measure that difference
directly, by taking a kernel that works and shortening one matched delay until
silicon breaks.

Target: `xorshift`'s `ucmpi1`, the loop-termination compare, 18 links in the
shipped build and the cell with the most headroom. Method: rewrite one
`BD_SZ_*` define, build with `BD_SIZES=<file> BD_NO_TIGHTEN=1
BD_SIZES_GATE=0`, run the bench. The gate is off because these builds are
MEANT to violate rule A; every bitstream produced here is a broken measurement
artifact and none of them may ever ship.

### It breaks, and it breaks the way the cell means

Two failure modes showed up, both reproducible 3/3 on re-run:

- **Hang.** UNIFORM mode stops mid-batch (run 21/2000 at 8 links, 489/2000 at
  another). The FIXED (48,18) batch still passes, so it is data-dependent --
  only some operand patterns are slow enough to lose the race. A request that
  arrives before its data breaks the 4-phase sequence and the FSM waits
  forever, which is what a hang rather than a wrong answer should look like.
- **Constant output.** At 10 links the kernel returned 4241718536 for every
  input in 4 cycles instead of 70. That is exactly `ucmpi1`'s meaning: sample
  the termination compare before it settles, read "done", exit the loop
  immediately, hand back the input. See the next section for why this one
  matters out of proportion to itself.

### Rule A's margin did not order the outcomes

Each point re-places the whole design, so this is twelve routes rather than
one route twelve times, with `NEXTPNR_SEED` pinned and each build's margins
read from its OWN routed SDF. Board verdict against the rule A slack
(`margin + guard`, i.e. how much the request actually trails the data)
tighten.py computed for `ucmpi1` on that same route:

| links | slack (ps) | board | | links | slack (ps) | board |
|---|---|---|---|---|---|---|
| 18 | +710 | PASS | | 8 | −817 | FAIL |
| 16 | +2557 | PASS | | 7 | **−2444** | **PASS** |
| 14 | +1291 | PASS | | 6 | −663 | PASS |
| 12 | +2091 | PASS | | 5 | −1281 | PASS |
| 10 | **+628** | **FAIL** | | 4 | −3336 | FAIL |
| 9 | **−1505** | **PASS** | | 3 | −3222 | FAIL |

**A build whose request provably trails its data by 628 ps failed every time,
and a build whose request leads its data by 2444 ps passed every time.** The
ordering is not weak, it is absent across roughly ±3 ns. Rule D does not
rescue it either: the FAIL range of worst select margin (−7196..−6288) sits
strictly INSIDE the PASS range (−9139..−6255), and all twelve builds carry
exactly 8 select violations, so it cannot discriminate at all.

That ±3 ns is not a surprise next to the ring study. Per-route SDF error there
was 25.2% at p90, and these data paths are 4–5 ns, so ~1–1.3 ns of model error
per path and two paths per comparison. **The slacks being disputed here are
inside the model's own measured noise floor.** The two rigs agree.

### What this experiment does NOT establish

Read the limits before quoting the table.

- **It does not isolate `ucmpi1`.** Changing a link count re-places
  everything. A failure can belong to any cell on that route.
- **There is no clean control point.** `BD_NO_TIGHTEN=1` strips rule E select
  padding, and the sizes were derived WITH it, so the worst-cell slack never
  exceeded +545 ps in ANY of the twelve builds. Every point is a design that
  is already marginal somewhere. In that regime, which path breaks first is
  close to a lottery, and no single metric should be expected to order it.
  A clean version starts from a fully tightened, fully padded build and
  shortens from there -- at the cost of a full tighten run per point.
- **It does not price rule A's guardband.** `max(0.2*t_data, 200 ps)` was
  never derived from any of this, and nothing here says what it should be.

The defensible claim is narrow and still worth having: **in a design carrying
unguarded select violations, rule A's per-route margin has no demonstrated
power to predict whether the circuit works on silicon.** Which is also an
argument about `BD_SKIP_RULE_E=1`, the flag `gcd` still ships with.

### The bench could not see a wrong answer

The 10-link build passed the 200-run FIXED repeatability check. It was
returning the same wrong number 200 times, and repeatability is all that check
tests. The deliberate-corruption exercise then failed for a revealing reason:
no operand pair it tried changed the output, because nothing changed the
output. Only that accident flagged it.

No kernel but `gcd` has an oracle in `hw/xsdb_bench_gen.tcl`. So the fix is a
cheap one -- assert the result fold:

- `hw/xsdb_bench_gen.tcl` takes an optional 5th argument, the expected SIG.
- `hw/golden_sig.txt` records it per kernel; `hw/run_all_bench.sh` looks it up
  and says so loudly when a kernel has none.
- SIG is `{sig[30:0],sig[31]} ^ o_data_capture` folded over the batch -- pure
  result, no timing -- so it survives a change of route, seed, clock or
  matched-delay size, and moves only when the kernel computes differently.

Controlled both ways on hardware: the good build passes the assertion, and the
10-link build fails it at check (a) with
`SIG ORACLE FAILED: ... folded to 0x1a9a2cac, expected 0x03dba483`.

## How often are sizes and route NOT a pair? 2 rebuilds in 8

`hw/tighten_loop.sh` already says it: "Sizes and route are a pair and this
pairing was never validated, so it is not shippable." It rejects such a build
rather than shipping it. What was never measured is how OFTEN the pairing
fails.

Method (`hw/rebuild_stability.sh`, raw data in
`hw/rebuild_stability_results.tsv`): take the converged, board-validated
`xorshift` and its own shipped `_sizes.vh`, rebuild it eight times changing
nothing but `NEXTPNR_SEED`, and run rule A against each build's own routed SDF.

| seed | rule A violations | worst cell | worst margin |
|---|---|---|---|
| 1 | 2 | ucontrol_merge1 | −567 |
| 2 | 1 | ucmpi0 | −1637 |
| 3 | 0 | umux0 | +207 |
| 4 | 0 | umux0 | +56 |
| 5 | 0 | umux3 | +195 |
| 6 | 0 | ucontrol_merge0 | +301 |
| 7 | 0 | umux1 | +326 |
| 8 | 0 | uxori1 | +11 |

**Two of eight rebuilds of a shipped design are not shippable.** The gate is
doing real work; it is not ceremony. Anyone who rebuilds a released bitstream
and skips the gate has a one-in-four chance of shipping a design whose request
does not trail its data.

**Every passing rebuild is marginal too.** Worst-cell margin lands between +11
and +326 ps, so on every route some cell sits inside ~550 ps of true slack. And
the identity of that cell changes completely from route to route -- `umux0`,
`umux3`, `ucontrol_merge0`, `umux1`, `uxori1`. There is no chronically weak
cell to fix. It is whichever one the router treated worst this time, which is
the same per-route scatter the 128 rings measured, seen through a different
instrument.

A practical consequence for the ratchet: its running maximum over routes is
what makes sizes portable at all, and 8 seeds is evidently not enough
accumulated history for this design. Sizes converged against one route are
roughly a 3-in-4 bet on the next one.

## Why gcd cannot use rule E: the C node is 1.3 ns from its own latch

> **Narrower than the heading says, as of 2026-08-24.** gcd at
> `bdc/emit.py`'s estimate converges rule E on the first iteration -- 118
> select gates, 0 violated, 0 pads. Everything below is about gcd *with
> tightened sizes*, which is the case that does not converge. See "gcd: ten
> tightening attempts failed" above.

`gcd` is the one kernel that ships with `BD_SKIP_RULE_E=1` -- no select
padding. Two results above make that worth revisiting, so here is the actual
blocker, measured rather than asserted (`hw/ctl_latch_reach.py`).

**Padding cannot fix most of it.** Re-running gcd's default path with rule E
enabled, `verify/converge.sh` reports 9 sites that take the request before the
select is stable, and declines to pad 7 of them for a specific reason: the
launch is a `control_merge`'s arbiter state LUT, not a `bd_link` C node, so
there is no DELAY knob attributable to the site. It pads the 2 it can and
never settles. The loop is not failing to find a value; for most sites there
is no value to find.

**The sites it does report are near misses, not blowouts.** `umux19`: request
earliest 3241 ps, select latest 2262 ps -- **+979 ps raw, −110 ps guarded**.
The raw ordering is correct by about a nanosecond. Only the 20% guardband is
short, by 110 ps.

**The cause is placement, and it is 1.3 ns.** Out of gcd's own routed SDF:

| path | n | median | p90 | max |
|---|---|---|---|---|
| C node -> its own latch, **RLOC grouped** | 164 | **150 ps** | 150 | 444 |
| C node -> its own latch, **ungrouped** | 2040 | **1440 ps** | 2085 | 3360 |
| C node -> its own delay chain | 23 | 585 ps | 810 | 810 |

Two LUTs of one cell, a nanosecond and a half apart, on the critical path of
every transfer in the design -- while the same C node reaches its own delay
chain in 585 ps.

**`hw/rloc_stamp.py` already fixes this, 9x, where it applies.** Grouped sinks
sit at a flat 150 ps. It is worth **1290 ps of median routing**. It just
covers **7.4%** of latch sinks.

That coverage is a structural cap, not an oversight -- rloc_stamp.py says so
at its own line 23: "A SLICE on xc7 holds four LUTs." A group is a same-tile
cluster, so a controller can share a tile with about one bit of its bank. For
the 96 banks wider than 2 bits, only the named bit gets grouped and the other
31 float. You cannot put a 32-bit latch bank in a SLICE.

**So the fix is not more padding and not more RLOC.** The enable net has
fanout ~17 per controller here and has to be short to ALL of its sinks. The
lever that does that is replicating the enable driver -- one C node copy per
few bits, each grouped with the bits it drives. That is a change inside
`cells/rtl/`, which is frozen. Worth noting what it would buy: the residual
gap is 110 ps and grouping is worth 1290 ps, so closing the packing would
clear rule E on gcd with an order of magnitude to spare.

### isprime computes correctly and reads back wrong

Deriving the expected SIG for all six kernels from their own C source, rather
than recording what the board said, immediately caught one kernel disagreeing.

`isprime`'s ODATA and SIG report **0x80000000** on every run -- SIG is exactly
`fold(0x80000000)` over 200 runs, so it is stable, not a race. The kernel is
nonetheless **correct**: the corruption exercise reads `isprime(48)=0` and
`isprime(47)=1` off `o_data_pl` directly, and both are right (47 is prime).

The two readings come from different samples of the same signal:

- `mismatch_ref` / `mismatch_val` latch `o_data_pl` **at run completion**.
- `o_data_capture` -- what ODATA returns and what SIG folds -- is a
  free-running mirror in the **AXI clock domain**, read later in `S_NEXT`.

The mirror was deliberate and its comment argues the case: reading in `S_NEXT`
gives the data a long settling window instead of sampling on the single edge
the completion pulse arrives on. That reasoning holds only while the output
bus still carries the result when `S_NEXT` runs. For five of six kernels it
does. For `isprime` it does not, so its SIG describes a released bus rather
than a result.

Consequences, in order of importance:

1. **`isprime`'s ODATA and SIG cannot be trusted**, and no golden SIG is
   recorded for it. Pinning one would freeze the artifact in place.
2. The bench's headline result readback is **kernel-dependent** in a way
   nothing declares. It is right for gcd, ipow, collatz, collatz64 and
   xorshift -- all four recorded oracles were checked against independently
   computed values and matched -- but "it agrees for the kernels we tried" is
   what the 8.5% guardband was too.
3. `ipow` is excluded for an unrelated and much duller reason: `ipow(48,18)`
   is `48^18 mod 2^32 = 0` exactly, so its SIG is `0x00000000` -- a value a
   dead kernel also produces. That needs per-kernel FIXED operands, not a fix
   to the sampling.

Not fixed here. Changing when the bench samples its result touches a harness
five working kernels depend on, and the kernel that exposed it is not wrong --
only its readback is.

## gcd: ten tightening attempts failed, and the estimate converged first try

gcd spent this session without a bitstream. Ten consecutive runs of
`hw/tighten_loop.sh gcd` failed identically -- rule E reporting the same
channel, `ulink_n85__3`, short again after it had already been padded, with the
loop's own message saying why: the margins in question are 76-400 ps and the
build-to-build routing noise on this fabric is larger than that, so no
per-channel constant taken from build N survives to build N+1.

`BD_NO_TIGHTEN=1` did *not* fix it, and the way it failed is worth keeping: it
reuses `build/gen/gcd_bench_gen_sizes.vh`, which was the stale product of those
ten attempts, and the rule A gate caught two cells whose request no longer
trailed their own datapath (`umux9` at -310 ps, `uori4` at -298 ps) and wrote
no bitstream at all. The gate did exactly its job. `BD_SIZES=none` is the flag
that actually falls back to `bdc/emit.py`'s estimate.

And at the estimate, rule E converged on the first iteration:

```
  118 select gates, 118 measured, 0 violated
  CONVERGED after 1 iteration(s)
  final pads: none needed        total added: 0 bd_delay element(s)
```

That reframes the ten failures. It is not that gcd cannot satisfy rule E on
this fabric -- it satisfies it comfortably, untouched. **Tightening is what
creates the select violations**, because shortening the matched delays is what
moves those gates to the edge of their guardband, and once they are at the edge
the routing noise is bigger than the correction. Which is the same conclusion
as "shortening a matched delay is the risky direction", arrived at from the
tooling rather than from a timing argument.

The estimate build closes at 91.58 MHz and is green end to end, including the
new 2000-input UNIFORM oracle:

```
  manual 4-phase pre-check PASS: gcd(12,18)=6, gcd(48,18)=6, gcd(0,5)=5
  FIXED  SIG oracle PASS (0x00000202)          latmin=122 latmax=124
  deliberate corruption PASS (idx=178 val=1 ref=6)
  UNIFORM SIG oracle PASS (0x824df03f over 2000 distinct inputs)
  latency: min=59 p50~=768 p90~=896 p99~=1024 max=1096 cycles  mean=716.4
```

The cost of shipping the estimate is real and unmeasured here: emit.py's
numbers are generous by construction, so this build is slower than a tightened
one would be. It is also the only one that exists.

## The biggest test in the suite was the one asserting nothing

Each kernel's FIXED batch has had an oracle since `hw/golden_sig.txt` existed:
200 runs of one operand pair, folded to a signature, compared against a value
derived from the C. The UNIFORM batch -- `N_UNIFORM` runs, default 3000, every
single input different -- asserted **nothing**. It checked that the bench did
not hang, that the histogram conserved, and reported percentiles. A kernel that
returned a wrong answer for 2999 of 3000 distinct inputs would have passed it.

That was never a necessary state. UNIFORM is not random. It is an LFSR with a
host-supplied seed, and every step of it is written down in `gen_bench.py`:

```verilog
lfsr_n1 = {lfsr[30:0],    lfsr[31]^lfsr[21]^lfsr[1]^lfsr[0]};
lfsr_n2 = {lfsr_n1[30:0], lfsr_n1[31]^lfsr_n1[21]^lfsr_n1[1]^lfsr_n1[0]};
bench_op0 <= mask0(lfsr);  bench_op1 <= mask1(lfsr_n1);  lfsr <= lfsr_n2;
```

So the input sequence is reproducible from the seed, the kernel is a function
of its inputs, and SIG is a fold over results with no timing in it.
`hw/uniform_oracle.py` replays all three -- LFSR, `DOMAIN_RESTRICTIONS` masks,
and the kernel transcribed from its own C -- and derives the value the board
must produce.

Every kernel with a bitstream passed on the first attempt, 64 distinct inputs
each:

```
  xorshift   UNIFORM SIG oracle PASS (0xe73bdcfb)
  ipow       UNIFORM SIG oracle PASS (0x6369040f)
  collatz    UNIFORM SIG oracle PASS (0x0a864e3c)
  collatz64  UNIFORM SIG oracle PASS (0x5038c4ac)
  isprime    UNIFORM SIG oracle PASS (0x00202000)
```

Three details that were not optional:

- The masks are **re-derived here, not imported** from `gen_bench.py`. An
  oracle that shares its implementation with the thing it checks agrees with it
  by construction, including when both are wrong.
- The kernels are transcribed **with their int32 wraparound**, because the
  hardware has it: `isprime`'s `d*d <= n` overflows for `d > 46340` and the
  circuit does not stop to complain. A Python model using unbounded integers
  would disagree with correct hardware.
- Derivation is cheap but not free -- 13 s for isprime at N=3000, 1.6 s for
  xorshift, under 0.1 s for the rest -- so `run_all_bench.sh` computes it
  inline and **downgrades to "not asserted" if derivation fails**. A missing
  oracle must not be able to look like a broken kernel.

The nulls get the same treatment, from the same fold expression their DUT uses.

### State of the suite, 2026-08-24

`hw/run_all_bench.sh 2000`, every target that has a bitstream:

```
  PASS gcd            PASS gcd_null          PASS ipow        PASS ipow_null
  PASS collatz        PASS collatz_null      PASS collatz64   PASS isprime
  PASS isprime_null   PASS xorshift
  SKIP collatz64_null, xorshift_null -- no bitstream (PnR timeout, rebuilding)
```

Ten of ten passing targets asserted **both** oracles: the FIXED 200-run fold
and the UNIFORM 2000-distinct-input fold. Nothing in the suite now reports
timing without also having checked what the circuit computed.

## CYCLES really does exclude the issue gap, and max rate no longer hangs

Every per-run cost in this file is `CYCLES / completed`, and every one of them
rests on `gen_bench.py`'s claim that `CYCLES` excludes the `S_PREP` settling
gap while `PREPCYC` counts it separately. That was documented, not checked.
`hw/rungap_sweep.sh` writes RUNGAP (7'h14) before the batches and sweeps it:

| RUNGAP | cycles/run | prepcyc/run |
|---|---|---|
| 0 | 98.713 | 1.000 |
| 1 | 98.688 | 2.000 |
| 2 | 98.703 | 3.000 |
| 4 | 98.725 | 5.000 |
| 8 | 98.720 | 9.000 |
| 15 | 98.747 | 16.000 |
| 31 | 98.720 | 32.000 |
| 63 | 98.705 | 64.000 |
| 127 | 98.703 | 128.000 |

The gap moves by 128x. `CYCLES` moves by 0.059 cycles -- 600 ppm, which is the
noise floor the repeatability section measured, so it does not move at all.
`PREPCYC` is exactly `gap + 1` at every point. The separation is real, and no
number in this file is carrying a hidden inter-run gap.

### RUNGAP=0 is also the regression test the async-latch fix never got

Maximum issue rate is the regime where batches used to park forever in
`S_WAIT_RES` with `o_req_s=0` -- run 16, 26, 34, 61, a different index every
time on a fixed seed. That was root-caused to an unsynchronised async-SET flop
gating the 3-bit state register and fixed with a synchroniser rather than a
delay, but the fix was verified at the default gap and never re-run at the rate
that exposed it.

All five kernels, three batches of 200 each at `RUNGAP=0`, oracle asserted on
every batch:

```
  xorshift  PASS   98.713 cycles/run
  ipow      PASS   27.000
  collatz   PASS  111.010
  collatz64 PASS  138.933
  isprime   PASS  453.547
```

3000 transactions back-to-back, no hang, and every per-run cost equal to its
gap-15 value inside the noise floor. The rate hypothesis stayed falsified.

## isprime: the kernel whose trip count is not an argument, swept anyway

isprime is the only kernel with nested loops and an early return, and
`loop_cost.sh` could not sweep it because nothing about its work is a knob you
can turn from the host. It does not have to be: the C is deterministic, so
python replays it and *counts* each n's outer trials and inner shift steps, and
the costs are fitted from the measured batches. 24 inputs, 3 batches of 200
runs each, every point asserting its own derived oracle.

Two things about the design, both load-bearing:

- The three natural counts are linearly dependent -- the shift-down loop runs
  exactly one step more per trial than the shift-up loop, so `down = up +
  outer`. Fitting all three would report a decomposition the data does not
  contain. `(outer, inner)` is a full-rank basis for the same span.
- The leverage comes from choosing inputs, not from having many. n = 2 and 3
  leave before the outer loop at all (`outer = inner = 0`) and pin the base;
  1000, 5000 and 60000 are even, so they take exactly **one** outer trial with
  a varying number of inner shifts, which is what separates the two
  coefficients. Primes run the outer loop to sqrt(n).

```
  base (entry + exit + harness)         16.174 +- 0.728 cycles    161.7 ns
  per OUTER trial (d*d<=n, r==0, d+1)   26.949 +- 0.059 cycles    269.5 ns
  per INNER shift step                   8.661 +- 0.003 cycles     86.6 ns
  early-return saving (composite)      -10.095 +- 0.731 cycles   -101.0 ns
  residual RMS 1.407 cycles over 24 points, 20 dof
```

The fourth term was not in the first model, and leaving it out was visible in
the residuals rather than in any number: composites all sat low, primes all
high, and the two loop-skipping inputs sat +9. That is the kernel's own comment
coming true -- its exit block is reached from three different places, and the
`r == 0` return does strictly less work in its last trial than falling out of
`d*d <= n` does. One indicator column drops the residual RMS from 4.46 to 1.41
cycles. **Taking the early exit is 10 cycles cheaper, once, not per trial.**

An outer trial costs 3.1 inner steps: a multiply, two compares, an increment
and the loop control, against one shift and a compare.

### What a loop iteration costs, across every kernel measured

| kernel | what one iteration does | cycles/iter | ns |
|---|---|---|---|
| xorshift | 3 shifts, 3 xors | 4.96 | 49.6 |
| ipow | 2 multiplies (exact, counted) | **6.00** | 60.0 |
| isprime inner | shift, compare, conditional subtract | 8.66 | 86.6 |
| collatz | shift *and* 3n+1, both arms | 9.32 | 93.2 |
| collatz64 | same, 64-bit | 11.77 | 117.7 |
| isprime outer | multiply, 2 compares, increment | 26.95 | 269.5 |

Five of these six sit between 5 and 12 cycles while the arithmetic inside them
ranges from three xors to two 32-bit multiplies. The body is not what a loop
iteration costs; the loop's own critical cycle is, and that is the same
conclusion the loop-cost section reached. The outlier is isprime's outer trial,
and it is an outlier because it is not one loop iteration -- it is a trial that
contains a whole inner loop's entry and exit.

## collatz's two branches cost exactly the same, and that is a backend fact

`hw/loop_cost.sh` measured collatz at n = 2^k, which reaches 1 by halving every
single step. Every number it produced is therefore the cost of the *cheap*
branch; `3n+1` was never executed once. `hw/collatz_branch.sh` fixes that by
decomposing the trip count instead of controlling it: python counts how many
steps of each kind a given n takes, the board measures the batch, and the two
per-step costs are fitted jointly. Powers of two (odd count exactly zero) pin
the even coefficient on their own -- without them the two counts are correlated
(odd ~ 0.53 x even along natural trajectories) and the fit could not separate
them.

19 points, 3 batches of 200 runs each:

```
  base (entry+exit+harness)    8.499 +- 0.094 cycles    85.0 +- 0.9 ns
  per EVEN step (n>>1)         9.320 +- 0.008 cycles    93.2 +- 0.1 ns
  per ODD step (3n+1)          9.322 +- 0.014 cycles    93.2 +- 0.1 ns
  residual RMS 0.126 cycles over 19 points, 16 dof
```

**Ratio 1.00.** A multiply-by-three-and-add costs the same as a shift, to two
parts in a thousand.

That is not a coincidence and it is not a statement about the two operations.
It is visible in the generated netlist. LLVM if-converts the branch long before
the handshake dialect exists, so `bdc/emit.py` receives a `select`, and what it
emits is:

```
    bdc_fused_uaddi0 ... .z_data(n26_u_data));      // shli+addi+addi = 3n+1
    bdc_fused_uselect0 ...                          // andi+cmpi+shrsi+select
        .e3_...(n19__4_...),                        //   the shifted arm
        .e4_...(n26_...),                           //   the 3n+1 arm
```

The select's `bd_join` waits on **both** arms. Both are computed every
iteration. So the loop pays `max(shift, 3n+1) + select` on every step no matter
which way the data goes, and the measurement is reading the structure back out.

Two consequences worth carrying:

- **Data-dependent branch cost in these kernels is zero.** Latency is a
  function of trip count alone, which is why the fits in this file are as clean
  as they are. Predictability is free; average-case speed is not.
- **Cheap arms do not make a loop cheap.** Making one arm of a hot `select`
  cheaper buys nothing unless it was the longer arm. The lever is the arm on
  the critical path, and after that the select itself -- which is the same
  conclusion the loop-cost section reached from the other direction.

Also worth noting against the null floor: the 8.5-cycle base means entering and
leaving collatz's loop costs about 3.5 cycles more than the null's
pass-through, which is the entry/exit structure, not the loop.

### The same sweep at 64 bits prices the datapath separately from the loop

`K=collatz64 hw/collatz_branch.sh` runs the identical 19 points against the
64-bit kernel, which is the same source with a wider type:

```
  base (entry+exit+harness)     8.553 +- 0.120 cycles     85.5 +- 1.2 ns
  per EVEN step (n>>1)         11.857 +- 0.011 cycles    118.6 +- 0.1 ns
  per ODD step (3n+1)          11.841 +- 0.018 cycles    118.4 +- 0.2 ns
  residual RMS 0.161 cycles over 19 points, 16 dof
```

Ratio 1.00 again, for the same structural reason. Against the 32-bit run:

| | 32-bit | 64-bit | change |
|---|---|---|---|
| base | 8.499 +- 0.094 | 8.553 +- 0.120 | **none** (0.4 sigma) |
| per step | 9.320 +- 0.008 | 11.857 +- 0.011 | +2.537 cycles, **+27.2%** |

Doubling the datapath width costs **+25.4 ns per iteration and nothing else**.
Entry and exit do not care about width at all, which is what you would expect
if they are handshake structure rather than arithmetic.

Two points and an assumption of linearity in width give a decomposition worth
holding loosely: `93.2 = F + W` and `118.6 = F + 2W` puts the width-dependent
part at **W = 25.4 ns** and the width-independent part at **F = 67.8 ns**, so
roughly **two thirds of a collatz iteration is loop overhead that no datapath
change can touch**. That is consistent with the cross-kernel table below --
bodies from three xors to two multiplies all landing between 5 and 12 cycles --
but it rests on exactly two widths, and a third would be worth having before
anyone plans against it.

## Every latency here now has an error bar, and it is small

Every number in the sections below was one batch from one programming, quoted
to three or four digits with nothing said about how much it moves. Two noise
terms sit under those digits, and `hw/repeatability.sh` separates them: repeat
the same FIXED batch **without reprogramming** (WITHIN), and reprogram the same
bitstream and measure again (ACROSS). Same route, same sizes, same die --
nothing that could change the answer changes.

4 programmings x 8 batches of 200 runs each, oracle asserted on every batch:

| kernel | cycles/batch | within-prog | | across-prog | | latmin..latmax |
|---|---|---|---|---|---|---|
| | mean | spread | ppm | spread | ppm | |
| xorshift | 19739.3 | 16 | 811 | 2.9 | 146 | 93..95 |
| ipow | 5400.0 | **0** | **0** | **0.0** | **0** | 21..22 |
| collatz | 22189.6 | 34 | 1532 | 12.9 | 580 | 103..105 |
| collatz64 | 27784.8 | 20 | 720 | 9.4 | 337 | 130..132 |
| isprime | 90708.2 | 83 | 915 | 25.1 | 277 | 433..439 |

Worst case: **0.15% within a programming, 0.06% across**. Per run that is 0.08
to 0.42 cycles -- every kernel's per-run timing is stable to a *fraction of one
clock*, so the batch aggregate is where the fraction accumulates, not evidence
that any kernel wanders. It also retroactively supports the clock sweep, which
concluded ns/iter was constant "to 0.1%": that is about twice the
across-programming floor, so the agreement was real and not luck.

There is no trend against repeat index (per-rep deviations are ±0 to ±13
cycles with no ordering), so nothing warms up, settles or drifts over a
session at this duty cycle.

### ipow is bit-exact, and that is structural, not luck

ipow returned **5400 cycles, 32 times, across 4 programmings, zero spread.**
Two explanations fit: its completion happens to land far from an aclk edge *at
these operands*, or its run length is an exact number of cycles by
construction. Operands alone tell them apart -- 8 pairs, 6 batches each:

| e | bits | cycles/batch | cycles/run |
|---|---|---|---|
| 1 | 1 | 3000 | 15.00 |
| 7 | 3 | 5400 | 27.00 |
| 9, 11, 15 | 4 | 6600 | 33.00 |
| 23, 27, 31 | 5 | 7800 | 39.00 |

Every pair exact, and the run length is exactly `9 + 6*bits(e)` cycles. So
ipow costs **6.00 cycles = 60.0 ns per iteration** -- not fitted, counted. The
sweep in the loop-cost section fitted 60.4 ns/iter for the same kernel, which
is that number within its own error bar.

The other four kernels have *fractional* cycles per run (xorshift 98.7), and
that is exactly where their jitter comes from: runs chain, so the phase at
which one run starts is the phase at which the previous one finished, and a
non-integer run length walks that phase. ipow's does not walk.

One thing this kills: **`latmin != latmax` is not by itself evidence of silicon
jitter.** ipow reports latmin=21, latmax=22 while its batch total is exactly
200x27 every time. The runs are identical; the +-1 is the latency counter's own
sampling, and the batch total is the statistic to trust.

## The null controls were the only unchecked thing left in the suite

Every `run_all_bench.sh` log carried lines like *"no expected SIG recorded for
gcd_null_bench_gen -- a deterministically wrong answer would not be caught"*.
The reasoning had been that the null computes "something else entirely" and so
cannot be given the real kernel's signature. True, and beside the point: the
null DUT is not opaque. `gen_bench.py`'s `is_null` branch emits

```verilog
assign out0_data = <arg word> ^ <arg word> ^ ... ;
```

so its expected value is derivable exactly the way a kernel's is -- from the
generator's own fold expression, with the same DOMAIN_RESTRICTIONS applied.
Derived in software, then checked, all four that have a bitstream passing on
the first attempt:

| target | operands | value | why |
|---|---|---|---|
| `gcd_null` | (48,18) | 34 | `48^18`, no mask |
| `ipow_null` | (3,7) | 4 | `3^7`, no mask |
| `collatz_null` | (48,18) | 48 | nargs=1, n masked to 16 bits |
| `isprime_null` | (47,18) | 47 | nargs=1, no mask |

`collatz64_null` and `xorshift_null` are derived and recorded but **not yet
checked** -- neither has routed since the generator changed. The row says so;
a value that has never met silicon should not look like one that has.

### And they give the harness floor directly

All four nulls retire a transaction in **5 cycles = 50 ns** at 100 MHz, with
`latmin == latmax` exactly. That is the floor for any kernel call through this
bench: AXI-side FSM, both synchronisers, one bundled transfer, and the null's
own deliberate `bd_delay #(.N(10))` bundle so that it pays a real handshake
rather than a shorter one.

It is worth comparing against the intercepts fitted from the loop sweeps (4.12,
2.96, 1.64, 0.27 cycles): those are **extrapolations to zero iterations of a
kernel that still has its own entry structure**, and they sit below the
measured 5-cycle floor. The fit intercept is not the harness cost, and the null
is the thing that actually measures it. xorshift at `rounds=0` takes 6 cycles
against the null's 5, so entering and leaving xorshift's loop without executing
it costs one cycle over a pass-through.

## Loop cost does not track total matched delay -- it tracks the critical cycle

`hw/loop_cost.sh` extends the xorshift sweep to every kernel whose trip count
can be driven from an operand, so four loop bodies can be priced on silicon
without rebuilding anything:

| kernel | how the trip count is set | ns/iter | intercept (cyc) | worst residual |
|---|---|---|---|---|
| xorshift | `rounds` is an argument | **49.6** | 4.12 | 1.88 |
| ipow | `e = 2^k - 1` -> k iterations, every bit set | **60.4** | 2.96 | 0.53 |
| collatz | `n = 2^k` -> k steps, all even-branch | **92.7** | 1.64 | 0.38 |
| collatz64 | same, 64-bit | **117.7** | 0.27 | 0.51 |

Every point asserts a derived oracle, and the fits are clean -- worst residual
under 0.6 cycles for three of the four, over sweeps spanning 30x in trip count.

**Two variable-by-variable 32-bit multiplies per iteration are cheaper than
collatz's shift, compare and add.** ipow at 60.4 ns does two real multiplies an
iteration; collatz at 92.7 ns does a right shift. So what an iteration costs on
this backend is not set by the arithmetic in it.

### The sum of matched delays does not predict it either

| kernel | matched delay (all cells) | cells | ns/iter | iter / total |
|---|---|---|---|---|
| xorshift | 33.7 ns | 12 | 49.6 | 1.47 |
| ipow | **75.8 ns** | 11 | **60.4** | **0.80** |
| collatz | 52.3 ns | 10 | 92.7 | 1.77 |
| collatz64 | 69.0 ns | 10 | 117.7 | 1.71 |

ipow carries **more than twice** collatz's matched delay and its iteration is
**35% faster**. And ipow's ratio is below 1: one iteration costs less than the
sum of its own matched delays, which is only possible because those delays are
not in series -- the cells run concurrently and an iteration pays the CRITICAL
CYCLE through the dataflow graph, not the column total.

This matters for what to optimise. `verify/tighten.py` reports and shortens the
sum, and shortening the sum is worth doing (it is the guardband against a
request arriving before its data). But **the sum is not a throughput model**,
and the delay-budget split earlier in this file -- which sums per-cell cones --
answers "what is the matched delay made of", never "what does an iteration
cost". The two questions have different answers here, and the ipow row is the
proof.

The one place the sum does track: within a kernel family, at fixed structure.
collatz64 against collatz is 1.32x the matched delay and 1.27x the iteration
cost -- doubling the datapath width scales both together, because the graph is
the same shape.

### A note on the oracle catching the experimenter

The first collatz sweep failed at k>=16 with `folded to 0x00000000, expected
0x00000ff0`. Not a kernel bug: `gen_bench.py`'s DOMAIN_RESTRICTIONS mask
collatz's `n` to 16 bits (so `3n+1` cannot overflow int32) and the mask applies
in FIXED mode, not only to the uniform generator -- so `n = 2^16` arrives as 0,
is mapped to 1, and the kernel correctly returns 0 steps. **Without the oracle
those four points would have contributed four suspiciously fast rows to the
slope** rather than an error. Sweep inputs are as capable of being wrong as
circuits are.

## What one iteration of a bundled-data loop costs, measured

> Superseded in precision, not in conclusion. The sweeps here fit a single
> slope per kernel from points that vary one operand. The later sections fit
> *separate* coefficients for each kind of step, report standard errors, and
> carry a measured noise floor -- collatz's 92.7 ns/iter below is 93.2 +- 0.1
> there. Use the later numbers; this section is where the method came from.

`xorshift(seed, rounds)` is the only kernel in the suite whose TRIP COUNT is a
runtime operand, so its loop cost can be measured by sweeping an input instead
of rebuilding anything. `hw/trip_sweep.sh` drives a FIXED-mode N=200 batch per
point and **asserts a derived oracle at every point** -- the expected value is
computed from `kernels/xorshift/xorshift.c` and folded the way the RTL folds
it, because a loop that exits early otherwise reads as a fast loop, which is
precisely how an under-delayed build once passed every check in this bench.

| rounds | 0 | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 |
|---|---|---|---|---|---|---|---|---|---|---|
| latency (cycles) | 6 | 9 | 14 | 24 | 44 | 83 | 162 | 321 | 639 | 1275 |

```
latency_cycles = 4.12 + 4.9625 * rounds        (residuals < 1 cycle, rounds >= 1)

  per iteration    4.963 cycles = 49.6 ns @ 100 MHz
  fixed overhead   ~3.8 aclk cycles  -- harness, not kernel; see the clock sweep
```

The fit holds across three orders of magnitude with residuals under one cycle
-- at 256 rounds the model is off by 0.5 of 1275. `rounds=0` is the only point
off the line (+1.9), which is the degenerate case where the loop body never
runs.

**Control: it is data-independent.** Re-running the whole sweep from
`seed=1` -- a completely different value sequence -- reproduces every point to
within one cycle. That is what the C promises (shifts and xors, no branching on
data) and it is worth having measured rather than assumed, since it is the
assumption that makes a single seed's slope mean anything.

### How much of an iteration is matched delay

This build carries **33.7 ns of matched delay** across 12 delay-bearing cells
(87 links, `verify/tighten.py` on its own routed SDF). An iteration measures
49.6 ns.

Those two numbers are NOT directly a ratio, and the gap is worth stating
carefully. The 33.7 ns is a SUM OVER ALL CELLS; a loop iteration traverses one
cycle through the dataflow graph, not every cell's chain added together. Cutting
the other way, a 4-phase handshake pays each matched delay TWICE per
transaction -- the delay element delays the return-to-zero as well as the
request. Taken together, 49.6 ns per iteration implies **at most ~25 ns of
matched delay on the loop's critical cycle**, i.e. matched delay plausibly
dominates the iteration but the exact share needs the critical cycle
identified rather than the column summed. That identification has not been
done, and no number here should be quoted as if it had.

### Control: sweep the measurement clock

Every bench bitstream here closes between 88 and 97 MHz (`Max frequency for
clock 'fclk0_bufg'`), and `run_all_bench.sh` measures at **100 MHz** by
default. That is above the closed frequency of every one of them, so "is the
bridge corrupting its own measurement?" is a fair question and the answer
should be measured, not assumed.

The DUT is self-timed and does not run on `fclk0` at all, so a sound
measurement must return the same NANOSECONDS whatever this clock is set to.
Re-running the whole sweep at three clocks:

| FPGA0_CLK_CTRL | MHz | cycles/iter | **ns/iter** | intercept (ns) |
|---|---|---|---|---|
| 0x00100A00 | 100.00 | 4.9644 | **49.64** | 38.0 |
| 0x00100C00 | 83.33 | 4.1326 | **49.59** | 44.3 |
| 0x00101400 | 50.00 | 2.4797 | **49.59** | 77.5 |

The per-iteration cost agrees to **0.1% over a 2x change in the measurement
clock**, including at 100 MHz where the bridge is running past its own closed
88.92 MHz. The kernel term is clock-independent, as a self-timed circuit must
be.

**The intercept behaves the opposite way, and that is the stronger result.**
In nanoseconds it moves by a factor of two; in CYCLES it is nearly constant at
3.80 / 3.69 / 3.88. So the fixed overhead is HARNESS work -- FSM states,
synchronisers, the `S_PREP` handoff -- billed in clock cycles, while the
per-iteration term is kernel work billed in real time. The two halves of the
fit separate exactly along the line their physical origin predicts, which is a
much better check on the model than either number alone. It also means the
41.2 ns quoted above as "fixed overhead" is not kernel time in any sense; at
50 MHz the same overhead is 77.5 ns.

A null variant (same harness, pass-through kernel) would pin the harness term
down directly -- one more reason `xorshift_null` failing to route matters.

## A saturating counter reported a 24% optimistic throughput

The bench's batch CYCLES register is 32 bits and SATURATES rather than wraps
(`gen_bench.py`: `cycles != 32'hFFFFFFFF`). That is the right choice in the
RTL -- a wrapped total is indistinguishable from a small one -- and it was a
trap for the host script, which divided it by the run count and printed the
result as a mean and a throughput.

isprime at N=20000 read `cycles=4294967295` exactly and the log said
`mean=214748.4 cycles, 465.7 tx/s`. Every digit of that came from the
saturation, and it was wrong in the flattering direction: the counter can only
UNDERstate a total, so the mean is the largest expressible and the throughput
the smallest overstatement of speed.

Measured against smaller batches that do not saturate:

| N | cycles | mean (cycles) | throughput |
|---|---|---|---|
| 20000 | 4294967295 (saturated) | *reported* 214748 | *reported* 465.7 tx/s |
| 2000 | valid | 265993 | ~376 tx/s |
| 500 | valid | 268144 | ~373 tx/s |

So isprime's real per-run mean is about **266k cycles (2.66 ms)** and the
saturated run overstated throughput by **24%**. The two unsaturated batches
agree with each other to 0.8%, which is what makes the third number's
disagreement a defect rather than scatter.

`xsdb_bench_gen.tcl` now tests for `0xFFFFFFFF` and WITHHOLDS the mean and
throughput, printing what the batch can still support -- `latmin`/`latmax` and
the histogram are per-run and unaffected, and `lat_ctr` never came close to its
own limit. It also prints how many runs the counter holds at that batch's
worst-case per-run latency, so the next N is a calculation and not a guess.
Only isprime is anywhere near the limit; at 100 MHz the counter covers 43
seconds of batch, which every other kernel clears by orders of magnitude.

## isprime read 0x80000000 for a year because "later" was read as "safer"

isprime was the one kernel with no result oracle. ODATA and SIG returned
`0x80000000` on every run while the kernel was computing correctly the whole
time -- the corruption exercise read `isprime(48)=0` and `isprime(47)=1`
straight off `o_data_pl`, both right.

Two readers of "the result" disagreed:

| reader | where it sampled | when |
|---|---|---|
| repeatability latch (`mismatch_*`) | raw `o_data_pl` | `S_WAIT_RES`, the completion edge |
| SIG and the host's ODATA | `o_data_capture`, a free-running mirror | `S_NEXT`, several cycles later |

The later read was deliberate. A real mid-settle race on gcd (`hw/run_gcd_sig_check.sh`)
had been bisected down to the `S_WAIT_RES` read, and moving SIG to `S_NEXT`
bought clock edges without adding a state. **The reasoning was wrong.** By
`S_NEXT` the harness has already asserted `bench_o_ack`, and 4-phase bundled
data promises the result is valid from `o_req` high only until the sender sees
the acknowledge and returns to zero. A read past the acknowledge is outside
the window; it worked for five kernels because their output bus happens to
keep holding, and isprime's does not. **Late is not safe. Inside the valid
window is safe.**

### One capture, three readers

`gen_bench.py` now loads `result_hold` in `S_WAIT_RES` on the last edge before
`bench_o_ack` rises (the ack is assigned on that same edge, so it goes high
after it). SIG folds it, the repeatability latch moved to `S_NEXT` and compares
it, and ODATA returns it once a batch has captured anything -- so the three can
no longer disagree about what the kernel returned. Before any batch, ODATA
still returns the free-running mirror, which is all the manual 4-phase smoke
path has to read.

`S_WAIT_RES` also now waits for the `o_req` LEVEL, not only the async edge
latch. `o_req_latched` is SET asynchronously by any rise on `o_req`, including
a transient that never becomes a completion; `o_req_s` is a 2-flop sample of
the level, which a sub-cycle transient does not survive. For a genuine
completion both are the same 2-flop delay off the same rise, so this costs 0-1
cycles per run. `res_wait` bounds the disagreeing case at 255 cycles and
captures anyway, setting a `hold_fallback` sticky (`MISM_ST[2]`) -- **a harness
made stricter must not be able to turn a wrong answer into a hang.**

### Measured

Sim could not see this bug at all: iverilog holds the bus, so an ad-hoc
isprime FIXED-mode testbench read the correct value through the OLD path too.
`tb_gcd_bench_gen` passes in full either way. The board is the only witness:

```
=== (a) FIXED-mode repeatability: op0=47 op1=18, N=200 ===
  completed=200 latmin=433 latmax=439 cyc  odata=1 sig=0x000000ff mism_st=2
SIG oracle PASS (0x000000ff matches the expected result fold)
  corruption chosen: (47,18)->1  vs  (48,18)->0
  ... MISM_ST=3 MISM_IDX=37 MISM_VAL=0 MISM_REF=1
```

`odata=1` where it read `0x80000000` before, `sig` exactly the fold derived in
software, and `mism_st=2` is `hold_valid` set with `hold_fallback` clear -- the
level gate never had to time out. **All six kernels now assert a derived result
oracle on silicon.**

## ipow's oracle was degenerate; the fix was the vector, not the kernel

`hw/golden_sig.txt` deliberately had no entry for ipow, because the bench ran
every kernel at a hardcoded FIXED (48,18) and `ipow(48,18)` is `48**18 mod
2**32 == 0` exactly. Its SIG folded to `0x00000000` -- which is also what a
dead kernel, a kernel held in reset, and a kernel whose output bus reads zero
all fold to. An oracle that green kernels and dead kernels both satisfy cannot
fail in the direction that matters.

The FIXED operand pair is now a per-kernel column in `golden_sig.txt`
(`kernel sig op0 op1`), passed through `run_all_bench.sh` to
`xsdb_bench_gen.tcl` argv 5/6, defaulting to (48,18) when omitted. ipow runs at
(3,7) -> 2187, which is the vector its own `main()` uses. Derived in software
first, then checked:

```
=== (a) FIXED-mode repeatability: op0=3 op1=7, N=200 ===
  completed=200 latmin=30 latmax=31 cyc  odata=2187 sig=0x00078179 mism_st=0
SIG oracle PASS (0x00078179 matches the expected result fold)
  corruption chosen: (3,7)->2187  vs  (3,8)->6561
```

The negative control got better for free. The corruption search used to have to
hunt past several candidate pairs ipow is blind to at (48,18); at (3,7) the
first candidate it tries -- the base pair with op1+1 -- already diverges, so
the search now leads with `(op0, op1+1)` and `(op0+1, op1)` before the old
fixed list.

**Five of six kernels now assert a derived result oracle on hardware**: gcd
`0x00000202`, collatz and collatz64 `0x000006f9`, xorshift `0x03dba483`, ipow
`0x00078179`. isprime still has none, for the separate and still-unfixed reason
recorded in `golden_sig.txt` -- its kernel is correct but ODATA/SIG sample a
released output bus.

## Where xorshift's matched delay actually goes

An earlier note in this project claimed narrowing xorshift's induction variable
was worth ~20% and was "a lowering change". The first half survives
measurement; **the second half does not, and the fix is not available to the
backend.**

Current default-path build, per-cell matched delay from its own routed SDF
(`verify/tighten.py`), 87 links / 33 379 ps total:

| group | ps | share |
|---|---|---|
| loop control (`uaddi0` + `ucmpi0` + `ucmpi1`) | 18 310 | **54.9%** |
| xor arithmetic (`uxori0..2`) | 9 682 | 29.0% |
| mux / merge | 5 387 | 16.1% |

So the circuit spends more matched delay counting iterations than doing the
work the kernel exists to do, and the two comparators alone are 15 023 ps --
45% of the budget.

### It is routing, not logic, and that changes what the fix is

`hw/delay_budget.py` splits each cell's cone into interconnect and cell arcs.
(These are sums over every arc in the cone, not a critical path -- read them as
what the delay is MADE OF.)

| cell | routing | logic | routing share |
|---|---|---|---|
| `ucmpi1` | 192 369 ps | 38 455 ps | **83.3%** |
| `ucmpi0` | 247 969 ps | 32 656 ps | **88.4%** |
| `uaddi0` | 10 595 ps | 80 511 ps | **11.6%** |
| `uxori0..2` | -- | -- | ~83% |

The adder is the odd one out because a CARRY4 chain is dedicated intra-slice
interconnect, counted as a cell arc: its cost is intrinsic and already cheap.
The comparators are ~85% wire.

**bdc does not lower a comparator badly.** `bdc/emit.py` emits behavioural
`xa > xb` / `xa == xb` (with a sign-flip for signed predicates) and lets yosys
pick the structure, which is a CARRY4 chain -- well under 2 ns of logic for 32
bits against a measured 8.25 ns of matched delay on `ucmpi1`. A cleverer
comparator structure has almost nothing to win.

**And narrowing the induction variable is not a backend change.** `rounds` is a
runtime `i32` argument to the kernel, so nothing downstream of the frontend may
assume a bound on the trip count. Narrowing is a SOURCE-level or frontend
change (`bdc/` is a backend; it consumes the handshake dialect and may not
invent width facts). What narrowing would actually buy is a shorter ROUTED
SPAN -- fewer bits to scatter -- not shallower logic.

### Which makes it the same problem gcd has

Both findings point at one lever: wide bundled channels whose bits the placer
scatters, with `hw/rloc_stamp.py` able to group only about one bit per bank.
gcd cannot use rule E for that reason (see above); xorshift spends 55% of its
matched delay on loop control for that reason. **The packing work is not just
gcd's select-padding blocker -- it is also the main throughput lever measured
so far**, which is worth knowing before pricing it.

## Two things about this board that cost real time

**`hw_server` polls the JTAG chain, and a poll lands in your design.** The PL
TAP's USER1 instruction stays selected between scans, so a background chain
rescan that shifts DR shifts it straight through this design's shift register —
and the same Update-DR commits it. An unrelated poll therefore writes a random
control word. Bit 5 of a random word is the *clear* bit, so roughly half of
them wipe every counter, and the symptom is not noise: it is a clean,
plausible, entirely wrong zero. All five counters read exactly 0 across a
one-second window in which the rings were provably turning. `jtag lock` before
the first scan and `jtag unlock` after the last one is the fix, and it is not a
precaution.

**Test-Logic-Reset must not clear anything you need to survive a scan.** The
first version reset the control register from BSCANE2's `RESET` output, which
is the natural place to put it — an aborted run then cannot leave the counters
running. But every chain rescan passes through Test-Logic-Reset, so that reset
fires on somebody else's schedule and drops the run bit mid-window. Power-up
`INIT` already gives a safe start; the asynchronous reset bought nothing and
cost that.

Neither of these is visible in simulation, and neither produces an error
message.

## Why raw JTAG through `xsdb` and not the SVF route in `hw-docs`

`hw-docs/02` §6 documents a working BSCANE2 path: hand-generated SVF played by
openFPGALoader, with the cascaded chain's ARM DAP padding inlined into every
vector and a measured one-bit asymmetry between the read and write directions.
It works, and it was silicon-validated.

It also cannot read a number it does not already know. SVF's `TDO`+`MASK` is a
*comparison*: the player passes or fails. Recovering an unknown counter value
means expecting zero and parsing the mismatch text back out, which is a real
technique and a fragile one.

`hw_server` plus `xsdb`'s `jtag sequence` shifts arbitrary IR and DR and hands
back the captured TDO as a value, and it pads the DAP itself — so none of the
chain encoding in §6 has to be reproduced. openFPGALoader's own XVC server
would have been better still, but it rejects this cable (`--xvc` reports
"unknown cable type" for `xilinxPlatformCableUsb`, though `--detect` and
bitstream loading work fine).

Two details of `jtag sequence` are load-bearing:

- **`-capture`** on the shift, or `run` returns nothing at all.
- **`-state IDLE`, never `-state IRPAUSE`/`DRPAUSE`.** Pause does not pass
  through Update, so a scan that parks there captures correctly and then
  silently discards the word it was supposed to commit. An IDCODE read still
  works from Pause — because Test-Logic-Reset loads IDCODE into IR by itself —
  which makes it exactly the wrong thing to prove the path with.

## Cable bring-up, WSL2

Two steps need root and there is no udev here, so they cannot be automated from
this side:

```
usbipd.exe attach --wsl --busid 3-2          # no root needed
sudo /usr/sbin/fxload -v -t fx2 -I ~/dev2/lib/jtag/fw/xusb_xp2.hex \
     -D /dev/bus/usb/001/<N>                 # only while PID is 03fd:0013
sudo chmod 666 /dev/bus/usb/001/*            # after every re-attach
```

The cable enumerates as `03fd:0013` with no firmware and re-enumerates as
`03fd:0008` after `fxload`, which detaches it from usbip — so attach, load
firmware, attach again, then `chmod`. `xc3sprog -c xpc -j` should show
`0x4ba00477` and `0x13722093`.

## Files

| File | What it is |
|---|---|
| `ro_top.v` | five rings, five counters, a BSCANE2 readback register |
| `ro_many_top.v` | 128 rings time-multiplexed onto 8 counters and 8 BUFGs, 16 groups |
| `ro_many_measure.py` | sweeps the 16 groups one lock at a time, per-group raw logs, judges |
| `arb_mtbf.v` | `bd_arbcell`'s MTBF, on silicon — see `verify/MTBF.md` and the file's own header |
| `build_hw.sh` | synth → route → FASM → frames → `.bit`, for any `hw/*.v` |
| `ro_measure.py` | walks the SDF for the prediction, drives the board, judges |
| `arb_mtbf_measure.py` | polls `arb_mtbf`'s sticky bits, rate-calibrates exposure, judges |
| `check_fracture.py` | `arb_mtbf`'s placement precondition: one fractured site per channel, stable across builds |

`build_hw.sh` deliberately drops two of `flow.sh`'s checks. The
no-global-buffer rule is inverted here: in the library a `BUFG` on a
manufactured clock is a two-nanosecond error hiding under a matched delay, but
here the buffers *are* the instrument, because a ring has to reach a counter's
clock pin and nothing else on this part will carry it. And nothing here is
fractured in `ro_top`, so the packing check has nothing to say there —
`arb_mtbf` fractures on purpose (see above) and gets its own separate check
instead. `--ignore-loops` carries over unchanged — a ring oscillator is a
combinational loop and so is every C-element in the library.

### `arb_mtbf` specifically: synthesis and seed are both pinned, and both for documented reasons

`build_hw.sh`'s synthesis step for every design hand-splices `synth_xilinx`'s
`map_luts` stage to skip `xilinx_dffopt`. That pass folds any flip-flop bit
whose D input is constant under some condition (arb_mtbf's capture-mux has
several, e.g. cap_word's compile-time-constant TAG field) into a per-bit
synchronous set/reset, rather than leaving the bit on the register's own
uniform clock enable. On `arb_mtbf` that fragmented the 48-bit BSCANE2 shift
register into two different CE nets, and nextpnr-xilinx's packer does not
discover the resulting half-slice control-set clash until AFTER a full route
("control-set contention in the placement") — expensive to hit and, on this
design, common enough (roughly half of seeds) to matter. Skipping the pass
does not eliminate the clash entirely — the fixed BSCANE2 site plus
`arb_mtbf`'s six channels is still dense enough that placement is seed
sensitive — but it materially improves the odds, and `ro_top` still builds
cleanly without the pass, so the change applies to both designs rather than
forking the flow.

`arb_mtbf`'s place-and-route seed defaults to 3, checked for determinism
(three clean rebuilds, three identical passes, `check_fracture.py` confirming
the same six sites every time). `NEXTPNR_SEED=N bash hw/build_hw.sh arb_mtbf`
overrides it — needed again if the RTL changes enough to shift the netlist,
in which case re-sweep seeds and update the default rather than trusting the
old one blind. History: 0, broken by the `ctrl_sticky` control-channel
addition; re-swept to 1; broken again by the `por_sr` power-on-reset
generator (every sticky latch widened from `LUT2` to `LUT3` — see
`arb_mtbf.v`'s header for why that generator exists), re-swept to 3.

### `arb_mtbf` specifically: the sticky latches need their own power-on reset

A bare `LUT2` self-OR feedback loop (`O = I0 | I1`, fed back) has no GSR
guarantee the way a real flip-flop's `INIT` does — confirmed on real
hardware, not just argued: a diagnostic control channel wired so nothing can
ever set it (`ctrl_sticky`, still present as a permanent regression check,
readback bit `CTRL`) read `1` on three separate fresh `--program` loads,
meaning the latch raced itself high during configuration. That invalidated
an entire first measurement run, which had reported all twelve sticky bits
firing on the very first poll.

The fix (`arb_mtbf.v`, right before the anomaly-channel generate block)
widens every sticky latch from `LUT2` to `LUT3` and gates it with `por_done`,
a one-way 0→1 signal from a 4-bit shift register (`por_sr`) that starts at
`4'h0` (GSR-guaranteed) and unconditionally shifts in a constant 1 every
cycle until it saturates at `4'hF` and stays there — an idiom borrowed
directly from `rtl/bd_latch.v`'s `bd_latch_rst` ("reset folds into the
feedback loop, widen the LUT"). It is deliberately not a live/host-reachable
clear — it cannot be re-armed or hit by a stray `hw_server` poll — so it does
not reopen the class of bug documented above under "Test-Logic-Reset must
not clear anything you need to survive a scan." The first draft used an
implicit-CE counter (`if (!por_done) por_cnt <= por_cnt+1`) and failed PnR on
every seed 0-9 with `Failed to route ... to CEUSEDMUX_OUT` — the same
wide-fanout-control-net failure already fought once on the liveness sampler
elsewhere in this file. The unconditional shift register has no CE at all
and avoids it.
