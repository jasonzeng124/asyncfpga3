# Tooling and infrastructure

Every path in this document is relative to `cells/`. Every script can be run
from anywhere — each one `cd`s to its own location first — so `./check.sh` and
`cells/check.sh` are the same command.

This is the operating manual for the checking machinery: what each tool is,
how to run it, what its output means, and what it is silent about. The cell
library itself is documented in `README.md`; the silicon results are in
`hw/README.md`. This file is about the tools.

---

## 1. What has to be installed

Everything but the board comes out of one tree, pointed at by `TC`
(default `/home/jayjay/dev2/lib/fpgatoolchain`). `flow.sh`, `hw/build_hw.sh`
and `verify/lutcost.py` all read it, and `flow.sh` and `build_hw.sh` check
every binary exists before doing anything, so a missing tool is an immediate
`exit 2` rather than a confusing failure ten minutes in.

| What | Where | Used by |
|---|---|---|
| yosys | `$TC/openxc7/bin/yosys` | `flow.sh`, `lutcost.py`, `build_hw.sh` |
| nextpnr-xilinx | `$TC/openxc7/bin/nextpnr-xilinx` | `flow.sh`, `build_hw.sh` |
| chipdb | `$TC/openxc7/xc7z010clg400.bin` | `flow.sh`, `build_hw.sh` |
| `cells_sim.v` | `$TC/openxc7/share/yosys/xilinx/` | all three |
| `cells_xtra.v` | `$TC/openxc7/share/yosys/xilinx/` | `build_hw.sh` only — it carries `BSCANE2` as a blackbox, `cells_sim.v` does not |
| prjxray db + `fasm2frames.py` | `$TC/openxc7/share/nextpnr/prjxray-db/zynq7`, `$TC/openxc7-src/prjxray` | `build_hw.sh` |
| `xc7frames2bit` | `$TC/openxc7/bin/` | `build_hw.sh` |
| `iverilog` (with `-gspecify`) | on `PATH` | `run_sim.sh`, `verify/probes/run.sh` |
| `xsdb`, `hw_server` | `$VIVADO_LAB/bin/` (default `/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab`) | `ro_measure.py`, `arb_mtbf_measure.py` |

**The installed `nextpnr-xilinx` must carry the `split_lut6_2` packer patch.**
This is not optional and there is no source-side workaround: a stock build
fails on the first fractured cell with *no wire found for port O5*, and half
the cost model in this library rests on two five-input functions sharing one
site. `flow.sh` is the gate that proves the installed binary has it.

### Environment variables

| Variable | Default | Effect |
|---|---|---|
| `TC` | `/home/jayjay/dev2/lib/fpgatoolchain` | toolchain root |
| `BD_ROUTE_PS` | `0` | per-arc routing figure added to the simulation models |
| `BD_SIZES` | unset | file of measured delay lengths for `flow.sh`; opt-in, never automatic |
| `NEXTPNR_SEED` | unset (`arb_mtbf` pins its own) | place-and-route seed for `build_hw.sh` |
| `PART` | `xc7z010clg400-1` | part name for `fasm2frames` / `xc7frames2bit` |
| `VIVADO_LAB` | `/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab` | where `xsdb` and `hw_server` live |
| `RO_WINDOW_MS`, `RO_REPEATS` | `8000`, `3` | ring-oscillator counting window |
| `ARB_WINDOW_MS`, `ARB_REPEATS` | `8000`, `3` | arbiter exposure calibration window |

---

## 2. The gate hierarchy

`./check.sh` runs seven gates in a fixed order. They are ordered
weakest-claim to strongest-claim, and no two of them overlap — each one exists
precisely because the one before it cannot say what it says.

```
python3 verify/inits.py --check-rtl     # the constants
./run_sim.sh                            # the protocol, arc-only timing
BD_ROUTE_PS=354 ./run_sim.sh            # the protocol, routed-estimate timing
python3 verify/lutcost.py               # the cost
./flow.sh                               # packing, placement, routing
python3 verify/tighten.py               # the bundling constraint, as routed
./verify/teeth.sh                       # and that that gate can fail
```

`check.sh` does not stop at the first failure. It runs all seven, banners each
one, marks failures with `>>> FAILED`, and finishes with `ALL GATES PASS` or
`SOME GATES FAILED`; the exit status is 1 if any gate failed. Running the whole
set is not cheap — `teeth.sh` alone is two full place-and-route runs — so during
development it is normal to run one gate directly and `check.sh` before
believing a result.

The order is also a dependency order in one place that matters: `tighten.py`
reads `build/pnr/soak.sdf`, which `flow.sh` writes. Running `tighten.py`
against a stale SDF is a real hazard, which is why `teeth.sh` re-runs
`flow.sh` on the way out (see §3.7).

### What each gate does not prove

This is the part worth internalising. Each gate has a precise, narrow claim,
and the interesting failures live in the gaps between them.

**`verify/inits.py`** proves that every LUT constant in the library is the
constant somebody derived, and that no number nobody derived can reach a LUT.
It does not prove that a cell built from those constants does anything useful.

**`run_sim.sh`** proves the logic and the handshake sequencing are right,
against models carrying real prjxray silicon arcs. It proves nothing about
routed silicon. Simulation drives the protocol perfectly and cannot show you a
bundling failure — with exactly one exception, `tb_mem`, where the RAM model
enforces the vendor setup windows and an undersized matched delay prints a
violation.

**`verify/lutcost.py`** proves yosys keeps every feedback loop, does not
duplicate a fractured pair into two sites, and emits the cell count the review
budgets. It does not prove the design places or routes, and it says nothing
about timing.

**`flow.sh`** proves the design packs, places and routes on the real chipdb,
and that three load-bearing toolchain properties hold. It does not prove
timing — but it writes the SDF that does.

**`verify/tighten.py`** proves the bundling constraint holds on the route that
was actually produced, using real routed interconnect delays. It does not prove
silicon timing. **Nothing in the seven does.** Interconnect delays are real,
but the cell arcs in the SDF are nextpnr's flat 124 ps model, not the per-pin
prjxray arcs the simulation uses.

**`verify/teeth.sh`** proves that the sizing gate can fail. A gate that has
never failed is decoration.

**`hw/`** is outside the seven and above them. Every gate above is a statement
about the toolchain; none of them asks whether the SDF is *true of the die*,
and every matched delay in this library is sized against it. That question is
answered by `hw/ro_measure.py` and by nothing else here.

---

## 3. The tools

### 3.1 `verify/inits.py` — the constants

```
python3 verify/inits.py                 # derive and prove
python3 verify/inits.py --check-rtl     # and audit rtl/ against the result
```

Every LUT function in the library is stated here as a Python lambda plus a pin
order, and the INIT is *computed* from that spec rather than transcribed. Three
things are then checked: each computed INIT reproduces its spec on all 2⁶ rows
(exhaustive, not sampled); the constants the design review fixed independently
agree with the computed ones; and, under `--check-rtl`, every hexadecimal
literal in `rtl/` is one of the proved constants.

Output is a table of `cell / kind / INIT / pins I0..I5`, with `<- review`
marking the constants the review states independently, then a row count
(1560 rows across 30 cells at the time of writing) and the audit result. A
constant that is derived but not currently instantiated is listed and is not an
error — it is a documented variant. Exit status is 1 on a mismatch, an
underivable literal in `rtl/`, or an `.INIT()` written in a base other than
hex. That last rule is deliberate: the scanner only sees hexadecimal, so INITs
are *required* to be hex rather than the scanner being taught every literal
base. A check that silently covers less than it claims is worse than no check.

The audit direction that matters is RTL → spec. A spec entry nothing uses costs
nothing; a LUT constant this file cannot derive is a number somebody typed.

### 3.2 `run_sim.sh` — the protocol

```
./run_sim.sh                       # all benches in tb/
./run_sim.sh tb_merge              # one bench
BD_ROUTE_PS=354 ./run_sim.sh       # routed-estimate regime
```

Compiles each `tb/tb_*.v` with `iverilog -g2012 -gspecify` against
`sim/bd_prims_sim.v`, `sim/bd_env.v`, all of `rtl/` and all of
`verify/attempts/`, runs it, and greps the log for `<tb> PASS`. Per-bench logs
land in `build/sim/<tb>.log`. On failure it prints the first matching
`FAIL|PROTOCOL|error` lines; the log has the rest.

`verify/attempts/` is compiled in on purpose. Nothing there is a library cell —
it is recorded negative results, kept because a bench that reproduces a defect
is the only thing that keeps the write-up true. Unused modules cost nothing.

Every channel in every bench carries a `bd_monitor` asserting the four-phase
order, that no new request precedes the acknowledge falling, and that data is
stable across the whole hold window `req↑ → ack↓`.

### 3.3 The two timing regimes

`sim/bd_prims_sim.v` models each primitive with real silicon arcs from
prjxray's characterised SDF, not with guesses and not with abc9's cost model:
`CLBLL_L.sdf` gives the 6LUT `A1..A6 → O6` arc as 56 ps rising and 124 ps
falling, and the 5LUT `→ O5` arcs per pin (55–60 rise, 118–152 fall);
`BRAM_L.sdf` gives t_su 566/737/532 ps on address/write-data/write-enable and
t_co 2454 ps. Rise and fall differ by more than a factor of two on this fabric,
so they are modelled separately — a uniform per-cell delay would hide every
asymmetric hazard in the library.

`BD_ROUTE_PS` adds a uniform interconnect figure to every arc.

**`BD_ROUTE_PS=0` (the default) is the arc-only regime.** These are cell arcs
and nothing else. Routing is about 74% of a real hop and the routed per-hop
median is ~478 ps, so a chain of N LUTs here runs roughly 3.7× faster than the
same chain on silicon. Every cell in the library is at its most fragile in this
regime, because the relative ordering of two paths that differ by one arc is
decided by tens of picoseconds.

**`BD_ROUTE_PS=354` is the routed-hop estimate.** It scales every arc together,
so it tests the delay-insensitivity of the control network — not the bundling
constraint, which no simulation of this library can test.

**Both must be green, and they are not the same test.** They disagree in both
directions and the benches assert the disagreement rather than papering over
it:

- `bd_arbcell`'s grant exclusion is an arc ordering, not a structure. During
  handover the falling grant travels one fall arc (124 ps) and the rising grant
  two rise arcs (56 + 52), so with zero routing the rise wins by 16 ps and both
  grants are briefly high. Routing puts a full hop in the `q` feedback and
  restores the order with roughly twenty times the margin. `tb_arb` counts 1
  such instant at `BD_ROUTE_PS=0` and 0 at 354.
- The semi-decoupled controller attempt fails 18/20 on its upstream trigger at
  arc-only and 0/20 at 354 — a race routing removes — while its downstream
  trigger fails 9/20 at arc-only and gets *worse* at 354, 15/20. One is a
  post-route check; the other is structural and is why the cell cannot ship.

A green run in one regime and not the other is information, not a flake.

What no simulation here can show, stated plainly in the model's own header:
bundling violations (except at the RAM boundary), the ~2 ns global clock buffer
yosys inserts unasked — `BUFG` is modelled as zero delay *on purpose*, because
modelling it would hide the hazard rather than reproduce it — and metastability
in `bd_arbcell`, where a LUT resolves in one arc, always.

### 3.4 `verify/lutcost.py` — the cost

```
python3 verify/lutcost.py               # all 29 cases
python3 verify/lutcost.py merge8        # named cases only
```

Synthesises each cell alone in a generated wrapper and compares the LUT count
against the review's packing and cost tables. Output is one line per case:
expected, got, and the primitive breakdown (`LUT6x4 LUT6_2x1`), with
`<-- MISMATCH` on a disagreement. Exit 2 if yosys is not where `TC` says.

A `LUT6_2` counts **once**, because it is one site. That is the claim the whole
cost model rests on, and it is a property of the toolchain rather than of the
source, which is why it is measured rather than asserted. Cases where a cell
takes a matched delay pin the depth to 4, so the delay's own links are a known
constant and the rest of the number is the cell.

### 3.5 `flow.sh` — packing, placement, routing

```
./flow.sh                                        # placeholder delays
BD_SIZES=build/resize/sizes.vh ./flow.sh         # measured delays
```

One design (`verify/soak_top.v`, one of everything) through yosys and
`nextpnr-xilinx` onto the real `xc7z010clg400` chipdb. It stops at FASM: the
place-and-route gate does not need a bitstream, it needs the routed SDF.

Three toolchain properties are load-bearing and this is the only gate that
exercises them:

- **the `split_lut6_2` packer patch**, without which the library is simply
  unbuildable;
- **`--ignore-loops`**, because every C-element and every latch here is a LUT
  feedback loop and the loop *is* the storage element — there is nothing to
  restructure;
- **`-noclkbuf`**, because yosys inserts a global buffer on anything reaching a
  clock pin and `bd_mem`'s manufactured edge reaches one. That is roughly two
  nanoseconds landing on a path a matched delay was sized against, and nothing
  in simulation shows it. The RTL also marks the net `clkbuf_inhibit`; both are
  required and neither is sufficient.

Two assertions are made against the FASM, which is the netlist as the bitstream
sees it. prjxray writes one 64-bit `xLUT.INIT` per *occupied site* — O6 in the
upper half, O5 in the lower — so `LUT.INIT` lines are occupied sites, and if
the packer had split each fractured cell into two sites the count would run
ahead of the yosys cell count instead of tracking it (the tolerance is +4).
Second, any `BUFGCTRL`/`BUFG_` line in the FASM fails the build, which is the
`-noclkbuf` rule actually enforced rather than hoped for.

Do not try to match FASM INITs against `verify/inits.py`. The packer permutes
LUT input pins freely and rewrites INIT to match, so the bits are a different —
equivalent — constant. What is checked here is the site count; the constants
are proved at the source, where they mean something.

Outputs land in `build/pnr/`: `soak.json`, `soak_routed.json`, `soak.sdf`,
`soak.fasm`, `synth.log`, `pnr.log`.

**`BD_SIZES` is opt-in and nothing picks it up automatically.** A bare
`./flow.sh` is always the placeholder build. Reading a `sizes.vh` that happened
to be lying in the build directory would mean `./flow.sh` silently stopped
being the placeholder build after one resize run, and the whole point of the
gates is that you know which design you just checked.

### 3.6 `verify/tighten.py` — the bundling audit and delay sizing

```
./flow.sh
python3 verify/tighten.py                          # reads build/pnr/soak.sdf
python3 verify/tighten.py path/to/other.sdf        # explicit SDF
python3 verify/tighten.py --emit sizes.vh          # write the recommendation
```

Every `DELAY`, `DSETUP` and `DCO` in `rtl/` is a placeholder. The number that
belongs there is not derivable from the source, from a synthesis estimate, or
from abc9's timing model — it is a property of where the router happened to put
things. So sizing is a pass over a routed design, and it **tightens**. A line
that comes out needing to grow is not a sizing result, it is a bundling
violation, and the tool says so in those words.

Three rules are checked:

**A. The request is the last thing its cell emits.** For a cell with a matched
delay on its outgoing request, that request must arrive later than every other
output the same cell produces from the same source, by the review's guardband
`max(0.2·t_data, 200 ps)`. This is the general form of `z_req = Δ(…)`.

**B. The RAM boundary is a real setup check.** It is the one edge-sampled
boundary in the library. The guardband is not a percentage but the vendor's own
numbers out of prjxray's `BRAM_L.sdf` — 566 ps address, 737 write data, 532
write enable — the same constants `sim/bd_prims_sim.v` enforces, so the
simulation gate and this gate cannot drift apart.

**C. Clock-to-out.** The acknowledge tapped off the RAM clock must trail it by
at least t_co = 2454 ps, or the read data is announced before it exists.

A setup check needs the late signal on its **shortest** path and the early one
on its **longest**, both from a **common start point confined to the cell**. A
matched delay covers logic inside one cell's own datapath; measuring from a
distant state node inflates `t_data`, inflates `0.2·t_data` with it, and turns
every line in the design into a false violation. The netlist is not a DAG, so
any pin on a cycle is a **state node** and traversal starts and stops there —
which is exactly the four-phase model, one hop per phase, and makes every path
considered acyclic by construction.

One subtlety in the output worth understanding. The tool prunes **false arcs**
before analysing: the SDF gives every physical LUT input an arc to the output
because the silicon propagates every pin, but the *function* need not. On a
shared `LUT6_2` site this is not conservative, it is wrong in the direction
that matters — `bd_dr2bd`'s decode shares its site with the request OR, and the
SDF shows a path from the payload into the request, which is the bundling
constraint running backwards. A pin is proved dead exhaustively from the INIT.
Reading the INIT requires nextpnr's `X_ORIG_PORT_A<k>` attributes, because
`connections` are physical (`A1..A6`) while `INIT` stays in the cell's original
order — so the tool needs `<stem>_routed.json` beside the SDF. If it is missing
you get a warning and no pruning. If pruning ever changes the feedback-loop
count, the tool **aborts** with exit 2 rather than analysing a netlist with
storage it can no longer see.

Output is a header (`routed SDF … cell arcs, … routed nets`, state-node count,
delay-line count), then a section per rule, then a verdict. Exit 0 means every
boundary meets its constraint on this route; exit 1 means at least one does
not, and the tool tells you to re-place or shorten the datapath — padding a
delay line is the last resort, never the first. Exit 2 is a broken analysis
(missing SDF, aborted pruning).

On the current build it reports `bd_merge`'s `DELAY(4)` as already exact, with
213 ps of margin over a 342 ps guardband, while `bd_mux`'s and `bd_dr2bd`'s
want tightening; the RAM boundary clears address setup by 1615 ps and
clock-to-out by 1674 ps. Those numbers are one build's answer and expire with
the build.

### 3.7 `verify/teeth.sh` — does the sizing gate have teeth?

Rebuilds the soak design with `bd_merge`'s matched delay set to `DELAY(0)` —
which `bd_delay` renders as a bare wire, so there is not even a chain left in
the netlist to find — routes it, and **requires `tighten.py` to fail**. It does,
at −1133 ps.

That zero-length case is the one that matters. An earlier version of the sizing
pass discovered its work by looking for delay chains and silently skipped any
cell that had none, so the one configuration guaranteed to violate the bundling
constraint was the one configuration it could not see. This script exists so
that cannot come back.

The override goes through the same `BD_SIZES` mechanism `resize.sh` uses, not
by editing the source. An earlier version rewrote `soak_top.v` with `sed` and
stopped working the moment the parameter was written differently — a check that
silently turns into a no-op is worse than no check.

Two operational notes. `teeth.sh` writes to `build/pnr/`, i.e. it clobbers the
real design's SDF, and re-runs `./flow.sh` on the way out to restore it — but
that restore is best-effort (`|| true`). If `teeth.sh` was interrupted, re-run
`./flow.sh` before trusting anything in `build/pnr/`. Exit 1 means the sizing
gate passed a design it should have caught; exit 2 means the sabotaged design
would not build, which is a different failure and not a result.

### 3.8 `verify/resize.sh` — not a gate

```
./verify/resize.sh
```

This is a design activity, not a check. It closes the loop: route, measure,
apply one change, re-route, and keep the change only if the design still passes
every constraint. Coordinate descent with verification, terminating because
lengths only decrease and are bounded below by zero.

The obvious version — apply `tighten.py`'s answer and stop — does not work, and
the reason is the useful part. The recommendation is the *smallest* length
meeting the guardband, so applying it leaves essentially zero margin by
construction, and applying it also changes the netlist, which moves the
placement, which changes the routing the recommendation was measured against.
Run naively on this design, round 1 proposes `UMUX 4→0` and `UMEM_UCO 12→8`;
round 2 then reports umux at −485 ps and the memory's clock-to-out at −59 ps.
The proposal was right about the route it saw and wrong about the route it
caused.

On this design it settles at `UDEC=16 UMERGE=4 UMUX=2 UMEM_USETUP=2
UMEM_UCO=9` after 4 sweeps and 25 place-and-route runs. **Four of five lines
could be tightened at all; seventeen of twenty-four proposals were reverted.** That
is the result worth keeping: on this fabric and this router a matched delay
cannot be shaved close to its measured requirement, because shaving it perturbs
placement by more than the margin the measurement claimed. Budget matched
delays conservatively and do not expect the toolchain to recover the slack.

The answer is written to `build/resize/sizes.vh` and every intermediate
proposal and log is kept beside it. It is valid for **this** design on **this**
toolchain and expires the moment anything upstream of place-and-route changes.

### 3.9 `verify/probes/run.sh` — not a gate either

Re-derives the picosecond figures the cell headers quote (`arb_handover`,
`link_skew`, `pipe_skew`). Run it after touching anything timing-related, or
those write-ups quietly stop being true. It honours `BD_ROUTE_PS` the same way
`run_sim.sh` does and writes to `build/probes/`. It prints numbers; it does not
judge them — that is what the comments in `rtl/` are for.

---

## 4. The hardware flow

### 4.1 `hw/build_hw.sh` — all the way to a bitstream

```
hw/build_hw.sh ro_top
hw/build_hw.sh arb_mtbf
NEXTPNR_SEED=7 hw/build_hw.sh arb_mtbf
```

Takes any `hw/<TOP>.v` through synth → route → FASM → frames → `.bit`, writing
everything under `build/hw/<TOP>/`. The pin constraints are the board's only
two broken-out PL pins (`W14` red, `W13` green); nothing here is measured by
looking at an LED, but a design with no ports gives the packer nothing to
anchor.

Two of `flow.sh`'s rules are deliberately **not** carried over. The
no-global-buffer check is *inverted* here: in the library a `BUFG` on a
manufactured clock is a two-nanosecond error hiding under a matched delay, but
in these designs the buffers are the instrument, because a ring has to reach a
counter's clock pin and nothing else on this part will carry it. They are
counted and printed, and if the number moves the design changed. The
fractured-pair site check is dropped too, because nothing in `ro_top` is
fractured — `arb_mtbf` fractures on purpose and gets its own separate check
(`hw/check_fracture.py`, §4.4). `--ignore-loops` carries over unchanged: a ring
oscillator is a combinational loop and so is every C-element in the library.

### 4.2 `xilinx_dffopt` is skipped, on purpose

The synthesis step does not run `synth_xilinx` end to end. It runs
`begin:map_luts`, then hand-splices the rest of the `map_luts` sequence
(`opt_expr -mux_undef -noclkinv`, `abc -luts 2:2,3,6:5,10,20`, `clean`,
`techmap` with `ff_map.v` / `lut_map.v` / `cells_map.v`, `opt_lut_ins -tech
xilinx`), then `finalize:`. The one pass that is left out is `xilinx_dffopt`.

That pass folds any flip-flop bit whose D input is constant under some
condition — `arb_mtbf`'s capture mux has several, e.g. a compile-time-constant
`TAG` nibble — into a per-bit synchronous set/reset on that condition, rather
than leaving the bit on the register's own uniform clock enable. It is a
legitimate area optimisation in general. On `arb_mtbf` it fragmented a single
logical register, the 48-bit BSCANE2 shift register `sr`, into two different CE
nets, and **nextpnr-xilinx's packer does not discover the resulting half-slice
control-set clash until post-route legalisation** — after paying for a full
route — reporting *disagrees with its half-slice on 'is_ceused' — control-set
contention in the placement*. This was confirmed by diffing a pre-route netlist
dump against `ro_top`'s own, which has the same pattern and still routes.
Skipping the one pass took `sr` from 5 distinct CE nets to 1 and raised the
seed pass rate from roughly 1-in-8 to roughly 1-in-2. Real, not incidental, and
not sufficient alone.

`ro_top` builds cleanly without the pass too, so the splice applies to every
design rather than forking the flow.

### 4.3 The seed must be pinned per design, and re-swept after any RTL change

`arb_mtbf` pins `--seed 12` in `build_hw.sh`; every other design takes
whatever `NEXTPNR_SEED` says, or nextpnr's default. (`hw/README.md`'s prose
still says the default is 3 — it is stale. `build_hw.sh` is authoritative.)

Placement scatter decides whether the clock router can reach every counter from
its BUFG, and six global buffers on this part is close enough to the limit that
some placements simply do not route. Seed iteration is the accepted cost of the
xc7 flow. For `arb_mtbf` specifically, the dense fixed-location BSCANE2 control
logic — `sr`, hold, and the liveness sampler, all in the `tck` domain competing
for the same handful of half-slices — routes on roughly half of seeds even with
`xilinx_dffopt` gone.

**Any RTL change invalidates the pin.** The netlist shifts enough to change
which seeds route, and the history in `build_hw.sh` is a long record of exactly
that: seed 0 broken by the `ctrl_sticky` control channel; seed 1 broken by the
`por_sr` power-on-reset generator (which widened every sticky latch from LUT2
to LUT3); seeds 3 and 7 broken by widening `por_sr` from 4 to 24 bits; seed 0
broken again by the Phase 1 population and Phase 2 windowed counters, which
roughly doubled LUT usage from 348 to 837 sites and moved the failure from
`is_ceused` to plain `tck` congestion; and so on through the depth-16 and
depth-8 diagnostics to the current seed 12.

Two lessons from that history are worth stating separately.

**Routing successfully is not enough.** Seed 4 passed place-and-route, passed a
determinism check, and looked fine — and its routed SDF had a **non-monotonic
depth ladder**: depth 2's delay chain measured *longer* than depth 4's. That is
a placement-dependent failure mode entirely distinct from routability, and it
is only visible by **computing the delays against the SDF**, not by PnR
succeeding. A later sweep found the same thing on the *threshold* ladder — seed
0 measured width 6 shorter than width 4 — which is why both ladders
(`depth_ps` and `floor_ps`, the quantities `arb_mtbf_measure.py` derives) are
now checked on every candidate seed, not just the depth one. A ladder whose
rungs are out of order makes every conclusion drawn from it meaningless, and
nothing in the build reports it.

**A seed is only pinned after a determinism check**: three clean rebuilds,
three identical passes, byte-identical FASM. The `.bit` md5 *does* differ
between runs — that is a timestamp in the bitstream header, not placement drift.
The FASM is the thing that must be stable, and it is.

The practical procedure after an RTL change to a hardware design is therefore:
sweep `NEXTPNR_SEED` over a range (0–9 has usually been enough; one change
needed 0–17), keep the seeds that route, compute both delay ladders against
each candidate's SDF and discard the non-monotonic ones, then rebuild the
survivor three times and compare FASM. Then update the default in
`build_hw.sh` and append to the comment — the history is load-bearing
documentation, not chatter.

There is also a routing *limit*, not just seed luck. When the width
discriminator was added, every seed 0–5 failed identically on `tck` — plain
congestion. The fix was to drop a filtered twin of the Phase 2 window counters
(~162 extra flip-flops in the `tck` domain) and keep only filtered sticky bits,
which answer the same question on their own. That brought the design back under
the limit at 1005 LUT sites. When every seed fails the same way, the design is
too big; when half fail, it is a seed.

### 4.4 JTAG bring-up under WSL2

Two steps need root and there is no udev here, so they cannot be automated from
the Linux side:

```
usbipd.exe attach --wsl --busid 3-2                        # no root needed
sudo /usr/sbin/fxload -v -t fx2 -I ~/dev2/lib/jtag/fw/xusb_xp2.hex \
     -D /dev/bus/usb/001/<N>                               # only while PID is 03fd:0013
sudo chmod 666 /dev/bus/usb/001/*                          # after every re-attach
```

The cable enumerates as `03fd:0013` with no firmware and re-enumerates as
`03fd:0008` after `fxload`, **which detaches it from usbip**. So the sequence is
attach, load firmware, attach again, then `chmod`. The device number `<N>` under
`/dev/bus/usb/001/` **changes on every re-attach**, which is why the `chmod`
uses a glob and why the `fxload` `-D` path has to be re-read each time rather
than remembered from the last session. `xc3sprog -c xpc -j` should show
`0x4ba00477` and `0x13722093`.

`hw_server` itself is started automatically by both measurement scripts if
nothing is listening on `tcp:3121`; they poll for up to 30 seconds and exit 2 if
it never comes up.

Two board-level hazards, both measured rather than theorised, and neither
visible in simulation nor accompanied by an error message:

**`hw_server` polls the JTAG chain, and a poll lands in your design.** The PL
TAP's USER1 instruction stays selected between scans, so a background rescan
that shifts DR shifts straight through the design's shift register, and the same
Update-DR commits it — an unrelated poll writes a random control word. In
`ro_top` bit 5 of a random word is the clear bit, so roughly half of those polls
wipe every counter, and the symptom is not noise: it is a clean, plausible,
entirely wrong zero. All five counters read exactly 0 across a one-second window
in which the rings were provably turning. `jtag lock` before the first scan and
`jtag unlock` after the last is the fix, and it is not a precaution. Both TCL
scripts do it.

**Test-Logic-Reset must not clear anything you need to survive a scan.** The
first version of `ro_top` reset the control register from BSCANE2's `RESET`
output, which is the natural place to put it. But every chain rescan passes
through Test-Logic-Reset, so that reset fired on somebody else's schedule and
dropped the run bit mid-window. Power-up `INIT` gives a safe start; the
asynchronous reset bought nothing and cost that.

Two details of `xsdb`'s `jtag sequence` are load-bearing: `-capture` on the
shift, or `run` returns nothing at all; and `-state IDLE`, never
`-state IRPAUSE`/`DRPAUSE`, because Pause does not pass through Update, so a
scan that parks there captures correctly and then silently discards the word it
was supposed to commit. An IDCODE read still works from Pause — Test-Logic-Reset
loads IDCODE into IR by itself — which makes it exactly the wrong thing to prove
the path with.

### 4.5 `hw/ro_measure.py` — is the SDF true of the die?

```
hw/build_hw.sh ro_top
python3 hw/ro_measure.py
```

Five ring oscillators of different lengths (7, 15, 31, 63, 127 `bd_delay`
links), each closed through one inverter and tapped into its own counter. For
each ring the routed SDF gives an exact predicted loop delay — sum the IOPATH
arc of every LUT and the INTERCONNECT delay of every net, once around, using
`tighten.py`'s own SDF parser — and the predicted period is twice that. The
measured period is the window divided by the count.

The comparison is per ring against that ring's own prediction. A straight line
through (links, period) was tried first and is the wrong model: the points miss
it by up to a quarter, because nextpnr does not place two rings the same way and
the routed cost of a link is not constant across them. The slope fit is still
printed, explicitly labelled as context and not as the claim.

Reading the verdict: a ratio near one says the SDF predicts silicon. A ratio
that is **constant but not one** says the model is wrong by a scale factor,
which is recoverable — every delay is off by the same factor in the same
direction. A ratio that **drifts with ring length** is the bad case: the
per-link and per-net parts of the model are wrong by different amounts and no
single correction fixes it. The script also flags the *sign*: rings running
slower than predicted is the dangerous side, because a delay sized from that SDF
would be shorter than the logic it covers.

Measured 2026-08-03 on `xc7z010clg400-1`: **measured = 0.975 × predicted across
an 18× span of ring length**, every ring faster than predicted, residual 8.5%
worst case with no trend in length. So `tighten.py` rests on a model good to
about a tenth that errs long — which costs area, not correctness.

Exit status is nonzero if the readback path fails its own constant checks, a
counter overflowed (lower `RO_WINDOW_MS`), a ring came back out of length order,
or the rings ran slower than predicted. It never asks anyone to read a scope or
an LED.

What it does not measure: a ring runs at its own natural rate with nothing
loading it but the next stage and one buffer tap. A matched delay in a real cell
sits beside logic contending for the same routing. Agreement here is necessary
and not sufficient — disagreement here would have been disqualifying.

### 4.6 `hw/check_fracture.py` — `arb_mtbf`'s placement precondition

```
python3 hw/check_fracture.py [build/hw/arb_mtbf/arb_mtbf_routed.json]
```

`verify/MTBF.md` is explicit: both grants of an arb channel must land in **one**
fractured `LUT6_2` site. Two separate LUTs have identical intrinsic delay but
different, build-dependent routing, and an asymmetry that moves between builds
makes a measured MTBF worthless the moment anything is rebuilt.

nextpnr's routed JSON splits a fractured pair into `ch[N].ugrant$LUT6` and
`ch[N].ugrant$LUT5` (and `pop[N].ugrant$…` since the Phase 1 population was
added), each carrying a `NEXTPNR_BEL` like `SLICE_X36Y45/A6LUT`.
Fractured-together means the two strings agree on everything except the 5/6
digit. The check runs before a single hour is spent measuring.

Placement **stability** across builds is the second half of the precondition and
is not visible from one build. The first run records every channel's site into
`grant_bels.json` beside the routed JSON; every later run compares and fails if
a channel moved. Delete the baseline to accept a new placement deliberately —
which is what you do after an intentional RTL change, and only then.

Exit 1 on a failed or moved channel, exit 2 if the routed JSON is missing or
contains no `ugrant` pair at all.

### 4.7 `hw/arb_mtbf_measure.py` — the long experiment

```
hw/build_hw.sh arb_mtbf
python3 hw/check_fracture.py                 # must pass first
python3 hw/arb_mtbf_measure.py --program     # once: load, baseline, start the clock
python3 hw/arb_mtbf_measure.py               # every later poll: read only
```

**`--program` is not the default and must not become one.** `xsdb`'s `fpga -f`
reconfigures the device, and reconfiguration clears every flip-flop back to its
power-up value — which would wipe the sticky anomaly bits this experiment exists
to accumulate, on every single poll. The point of running this from a recurring,
hours-apart loop is that the silicon keeps counting between invocations with
nobody watching. `--program` starts that clock; everything after it only reads.
The script refuses `--program` if `state.json` already exists, and refuses a
plain poll if it does not.

It calls `check_fracture.py` itself and refuses to run if it fails.

A poll does, in order: bring-up (three readback constants plus the async
liveness sampler — a sticky bit that never fires proves nothing if the readback
path is not proven first); the `ctrl_sticky` negative control, a sticky latch
wired so nothing can ever set it, which reading 1 invalidates every other sticky
result on the die; the liveness variance check, where `r1`, `r2` and `ring3`
*must* toggle and the per-channel signals are merely reported; the detector
floor, from the six threshold probes of known pulse width, converted to
picoseconds from **this build's own routed SDF** and scaled by the 0.975
silicon-versus-SDF factor `ro_measure.py` established; a short rate calibration
(default 3 × 8 s) on the r1/r2 exposure counters; and then the sticky bits,
window counters, and chain snapshots.

The rate calibration is not incidental. A 32-bit counter at these rates wraps in
about a minute, so what is measured is a *rate*, and total exposure between two
polls — possibly hours apart — is that rate times the host's wall clock,
accumulated in `state.json`. The three repeats double as an **injection-lock
check**: if r1's and r2's periods sit on a suspiciously clean small-integer
ratio (within 1e-4), the two rings may have locked and parked at a fixed
relative phase, which is exactly the "safe part of the window for hours" failure
the two-independent-oscillator design exists to avoid. That is a hard failure,
because the exposure figure would otherwise be a lie.

`state.json` accumulates cumulative exposure, first-seen wall time for every bit
that turned on since the previous poll, and the previous counter values so a
delta can be printed.

**Exit status is nonzero only for a broken measurement** — bring-up failure, a
stuck stimulus ring, a counter overflow, a suspected frequency lock, a nonzero
negative control, or `check_fracture.py` failing. A channel's sticky bit being 1
is a *result*, not a script failure, and never changes the exit code by itself.
This is the same rule as everywhere else in the tree: the tool judges the
measurement, never the outcome.

---

## 5. Where things land

| Directory | Written by | Contents |
|---|---|---|
| `build/sim/` | `run_sim.sh` | `<tb>.vvp`, `<tb>.log` |
| `build/pnr/` | `flow.sh` | `soak.json`, `soak_routed.json`, `soak.sdf`, `soak.fasm`, `soak.xdc`, `synth.log`, `pnr.log`, and `sizes.vh` when `BD_SIZES` is used |
| `build/teeth/` | `verify/teeth.sh` | the sabotaged `sizes.vh` and its logs (the design itself goes through `build/pnr/`) |
| `build/resize/` | `verify/resize.sh` | `sizes.vh` (the verified assignment), every proposal, every log |
| `build/probes/` | `verify/probes/run.sh` | probe `.vvp`s |
| `build/hw/<TOP>/` | `hw/build_hw.sh` | `.json`, `_routed.json`, `.sdf`, `.fasm`, `.frames`, `.bit`, `.xdc`, logs; plus `grant_bels.json`, `state.json` and `measure.tcl` from the measurement scripts |

Two files under `build/hw/arb_mtbf/` are **live experiment state, not build
output**: `grant_bels.json` is the placement baseline, and `state.json` is the
accumulated exposure history of a run that may have been going for days. Do not
clear that directory to force a rebuild without deciding, explicitly, that the
run is over.
