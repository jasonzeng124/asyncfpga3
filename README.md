# asyncfpga3

An asynchronous backend for Dynamatic. It takes dataflow programs and emits
FPGA circuits with **no clock in the datapath**, built entirely on an open
toolchain and measured on real silicon.

The short version of the result: it works, and it is about 3.7x slower than the
clocked backend it replaces. Most of that gap is the FPGA fabric, not the
protocol, and the sections below break it down term by term.

---

## The idea

A synchronous circuit shares one clock, so its period is set by the slowest
path in the whole design under the worst voltage, temperature and silicon.
Every fast operation waits out the difference.

An asynchronous circuit replaces the clock with local agreement: each block
says "here is your data" and waits to hear "got it". Nothing budgets for a
worst case it does not have.

This uses **four-phase bundled data**. Data travels on ordinary wires; two
control wires run alongside it — `req` ("data is ready") and `ack`
("received"). A transaction is four events: req up, ack up, req down, ack down.

The whole correctness problem is one race: `req` must arrive *after* its data
has settled. It is made true by physically delaying `req` through a chain of
gates sized to lose that race — a **matched delay**. That delay is the only
deliberate delay permitted anywhere in the design, and it is the entire cost
model.

- Too short: silent data corruption, at some voltages, on some chips, that
  simulation cannot reproduce.
- Too long: you have re-invented a slow clock, one link at a time.

Delays get a first-pass estimate from the netlist, then each one is
individually shortened after place-and-route to the tightest value its own
routed path justifies. Per delay element, never one global number. That
tightening pass is worth **2.1x to 2.7x** on measured silicon.

---

## What is here

```
C  ->  Dynamatic  ->  [ bdc ]  ->  [ cells/rtl ]  ->  yosys -> nextpnr -> prjxray  ->  EBAZ4205
       upstream       ~8.3k Py     ~1.3k Verilog        openXC7, no vendor tools      Zynq 7010
```

| Path | What it is |
|---|---|
| `bdc/` | The backend. Consumes `handshake`-dialect MLIR and emits bundled-data Verilog. Cuts in immediately above Dynamatic's `--handshake-place-buffers`, because buffer placement optimises against a clock period and there is no clock. |
| `cells/rtl/` | The frozen primitive library — links, latches, joins, merges, muxes, arbiters, a memory port. Every cell carries its own cost argument in its header. |
| `cells/hw/` | Board harnesses and measurement rigs (PS7 + AXI3). |
| `kernels/` | The test kernels, in C. |
| `patches/` | Fixes to `nextpnr-xilinx`, two of them upstream. |
| `hw-docs/` | Board and part reference. |

Entry points: `bdc/frontend.sh` (C through Dynamatic to MLIR),
`cells/flow.sh` (MLIR to bitstream), `cells/check.sh` (the gate suite).

`dynamatic/` and `circt/` are consumed as data and never edited. They are not
tracked here — see Building.

---

## Building

Two large trees are **not tracked** and must be supplied yourself:

| tree | what | note |
|---|---|---|
| `dynamatic/` | [Dynamatic](https://github.com/EPFL-LAP/dynamatic), built | Provides the frontend. Consumed as data; never patched. |
| `circt/` | CIRCT, as Dynamatic requires it | Same. |

Plus the FPGA toolchain — [openXC7](https://github.com/openXC7) (yosys,
`nextpnr-xilinx`, prjxray). **Apply the patches in `patches/` before using it**;
two of them fix bitstream-level bugs that produce silently wrong hardware, and
one of those was this project's longest debugging session.

Point the scripts at your installs:

```sh
export TC=/path/to/fpgatoolchain      # yosys, nextpnr-xilinx, prjxray
export VIVADO_LAB=/path/to/Vivado_Lab # board access only -- see below
```

Then:

```sh
bdc/frontend.sh xorshift    # C -> Dynamatic -> handshake-dialect MLIR
cells/flow.sh   xorshift    # MLIR -> Verilog -> bitstream
cells/check.sh              # the gate suite
python3 -m pytest bdc/      # backend unit tests
```

**On "no vendor tooling":** that claim is about the *build path*, which is
open end to end — nothing from Xilinx synthesises, places, routes or packs a
bitstream here. Talking to the board over JTAG does use `xsdb` and `hw_server`
from Vivado Lab (a free download). Everything under `cells/hw/` is therefore
board tooling, not build tooling. `cells/docs/TOOLING.md` lists every external
dependency and which scripts need it.

Board work also needs an EBAZ4205 (or another Zynq 7010 carrier) and a JTAG
cable. Nothing else in the repo requires hardware.

---

## What runs

Six kernels compile end to end and run on the board with checked results —
`gcd`, `xorshift`, `collatz`, `collatz64`, `ipow`, `isprime`. Correctness is
checked against an oracle derived independently from the C source, so a test
cannot pass by agreeing with a hardware bug. Memory loads lower through the
backend; stores do not (see Open).

Measured per-iteration cost on silicon:

| kernel | ns/iter | sum of matched delays | ratio |
|---|---|---|---|
| xorshift | 49.6 | 33.7 ns | 1.47 |
| ipow | **60.4** | **75.8 ns** | **0.80** |
| collatz | 92.7 | 52.3 ns | 1.77 |
| collatz64 | 117.7 | 69.0 ns | 1.71 |

The interesting row is `ipow`. It does two 32-bit multiplies per iteration and
is 35% *faster* than `collatz`, whose body is a shift, a compare and an add.
Its ratio is below 1 — an iteration costs less than the sum of its own delays.
That is only possible because the delays are not in series: cells run
concurrently and a loop pays for its **critical cycle**, not for the work
inside it. Optimising the delay column is not a throughput model.

`gcd` shows the other half of the argument: measured latency spans **310 ns to
6.34 us** on operands alone, an 11.6x spread against a 20 ns noise floor.

---

## What it costs

Against Dynamatic's own output, both arms built for the same part with the same
toolchain. Dynamatic's buffer placement puts one slot per ring, so its
per-iteration cost is its closed clock period — the whole loop recurrence as a
single combinational cone.

| kernel | Dynamatic | async, untightened | async, tightened | gap |
|---|---|---|---|---|
| xorshift | 12.73 | 99.18 | 47.66 | 3.7x |
| collatz | 14.05 | 199.53 | 91.96 | 6.5x |
| collatz64 | 17.84 | 308.25 | 112.71 | 6.3x |

### Where the gap comes from

Modelling a ring as `E x [ L x (1 + g + d) + N x t_latch ] + N x t_hs`:

| term | value | measured? |
|---|---|---|
| `E` — both edges (return-to-zero) | x1.5 | yes, 76% of full serialisation |
| `g` — guardband on covered logic | x1.18 – 1.35 | yes, 128-ring scatter study |
| `t_hs` — handshake per stage | 0.547 ns | yes |
| `t_latch` — latch arc per stage | 0.152 ns | yes |
| `N` — storage stages per cycle | 3 minimum | structural floor |
| `d` — decomposition penalty | ~0.15–0.20 | estimated |

Note that `g x L` is independent of `N`: the guardband is a fraction of the
logic covered, and the total logic is fixed. **Fusing stages does not buy
guardband back.** It buys latch arcs, handshake cost, and some of `d`.

Filling it in gives a floor of **~1.8x** for this four-phase design and a
realistic best of **~2.6–2.8x**. See the note on two-phase below: that floor is
protocol-dependent, and the protocol was a choice.

### Attribution

The floor is two multiplicands, and neither is the handshake:

- **x1.5, return-to-zero.** Every matched delay is traversed twice per
  transaction. Two-phase signalling pays it once. → **protocol choice, see
  below**
- **x1.18–1.35, guardband.** The delay line is a LUT chain; the datapath is
  mostly interconnect. They do not track. On an ASIC both are the same gates in
  the same region and track to a few percent. → **fabric**
- **x1.06, the protocol itself.** 1.6 ns out of ~23. → **async**

So the guardband is the fabric's bill, return-to-zero is this design's own,
and the handshaking — the thing people mean when they say async has overhead —
is the smallest term in the model by an order of magnitude.

**On two-phase.** This backend is four-phase throughout, and the x1.5 above is
the price. Two-phase does not require dual-edge-triggered storage, which is
what an earlier version of this file claimed: the Mousetrap style holds a
normally-transparent latch open with `en = XNOR(req, ack_next)`, so a
transition in either direction on either wire produces the correct *level* and
nothing ever samples an edge. Rise/fall asymmetry does buy part of it back,
and an earlier version of this paragraph was wrong to say otherwise: at a
transparent-latch consumer the falling request guards nothing (no data can
move between the consumer's node rising and falling), so only the rising edge
has to be matched. `bd_delay #(.FASTFALL(1))` — every stage an
`AND(prev, input)` — keeps the rise at N hops and flushes the fall in one, and
the compute cells use it. Measured on the routed `xorshift_round` ring it
recovers ~7% of the interval (17.70 → 16.43 ns), not the x1.5: the chains
in a tightened design are short (6–9 links at 274 ps, ~1.6–2.5 ns), so
their return-to-zero is a small share of a 16 ns cycle; the rest of the
cycle is handshake and interconnect, which the fast fall does not touch.

The real cost of two-phase is elsewhere. It is cheap for a linear pipeline,
which is all Mousetrap is, and expensive for everything else. Four-phase has a
rest state, so a C-element naturally means "both operands arrived"; two-phase
has none, so joins become phase comparators and merges, muxes and arbiters lose
the level they read. `bd_mux`'s correctness argument — the select is valid
because control holds it "from ctl_req-rise until ctl_ack-fall" — has no
two-phase translation. Switching would mean rewriting `cells/rtl/` rather than
patching it. That is a real reason to have stayed, and a better one than the
one previously given here.

The fabric is not badly built; it is *specialised for exactly the thing being
competed against*. Free flops in every slice, dedicated low-skew clock trees,
carry chains, block RAM with a clock pin — every one of those is a subsidy the
synchronous baseline collects and this backend cannot. The clearest example is
in `cells/rtl/bd_latch.v`: storage is built from LUTs rather than the slice's
own latch primitive, because that primitive's enable lands on the slice clock
pin, reachable only through two clock wires per interconnect tile — and a
self-timed pipeline wants one locally generated enable per stage. A 32-bit
storage stage therefore costs 16 LUTs where the synchronous baseline gets 32
flops for free.

Removing the remaining fabric handicaps — an ASIC, delay lines that track —
and switching protocol lands at roughly **parity**, not a win. Dynamatic is *dynamically*
scheduled, so it already harvests the variable-trip-count advantage that async
is usually sold on, and bundled data uses worst-case matched delays by
construction so it does not recover per-operation variance either. Only
dual-rail with completion detection would, at roughly twice the wires.

---

## Open

- **Stores are refused, deliberately.** Dynamatic signals write completion with
  a counter of outstanding stores. A counter needs an edge to count on, and
  there is no clock. `emit.py` raises rather than fake it, because faking it
  would report a program complete while a write is in flight. This needs a
  design decision, not more code.
- **The guardband is a median, not a bound.** Across 128 ring oscillators on
  one die, the margin in use covers about half the population; 76 of 128 ran
  slower than the model predicted, which is the direction a matched delay
  cannot absorb. The scatter is per-route and does not cancel. This is the top
  correctness risk and it is quantified, not fixed.
- **One stability rule blocks tightening on most rebuilds.** A conservative
  check on mux control inputs means tightening converges on roughly one rebuild
  in three. The cause is measured — a link's control node sits ~1.4 ns from the
  latch it drives, so the select is still moving when the mux has fired. The
  fix is enable replication inside the frozen cell library, which breaks that
  cell's LUT-sharing cost argument and so needs the argument re-derived.

---

## Toolchain

Built with openXC7 — yosys, `nextpnr-xilinx`, prjxray. No vendor tooling in the
path, which means every result is reproducible from source, and also that the
toolchain itself was a live suspect whenever hardware misbehaved. It turned out
to be responsible three times, in each case writing a correct design into an
incorrect bitstream — invisible to every file-based check and visible only on
the die. Fixes are in `patches/`, two of them upstream.

The general lesson, and the one that cost the most: **a lookup that silently
defaults is worse than one that crashes**, and when simulation and silicon
disagree, suspect the translators before the design.

Every reported number is stamped with the toolchain revision that produced it,
because that revision has changed underneath a measurement before.

---

## Related work

Bundled-data on commercial FPGAs is not new ground, though it is filed under
low-power and NoC design rather than under HLS, which makes it easy to miss.

- [Bhardwaj et al., *Towards a Complete Methodology for Synthesizing
  Bundled-Data Asynchronous Circuits on FPGAs*, ISLPED
  2019](http://www.cs.columbia.edu/~luca/research/bhardwaj_ISLPED19.pdf) —
  two-phase Mousetrap pipelines on Virtex 7 through Vivado, NoC switches, with
  matched delays controlled by manual LUT placement constraints. Reports 47%
  lower energy-per-packet and 75% lower idle power against a synchronous
  switch, at 28% more LUTs.
- [*EDA-oriented FPGA Circuit Design Method for Four-phase Bundled-data*, IPSJ
  JIP 31](https://www.jstage.jst.go.jp/article/ipsjjip/31/0/31_495/_pdf) —
  four-phase on commercial FPGAs with automated constraint generation and delay
  adjustment; the closest published relative of the tightening pass here.
- [Moreira et al., *A Bundled-Data Asynchronous Circuit Synthesis Flow Using a
  Commercial EDA Framework*, DSD
  2015](https://www.inf.pucrs.br/~calazans/publications/2015-DSD_ACSD.pdf) —
  ASIC rather than FPGA, but the relative-timing-constraint machinery is the
  same problem.
- [*Yak: An Asynchronous Bundled Data Pipeline Description
  Language*](https://arxiv.org/pdf/2308.04189).

What is different here: the input is a **dataflow IR** rather than hand-written
HDL, the toolchain is **fully open** rather than Vivado, there are **no manual
placement constraints**, delay sizing is **automated per element after
place-and-route**, and the baseline is a **dynamically scheduled** HLS compiler
rather than a fixed-schedule one. That last point matters for reading the
results: a dynamically scheduled baseline has already collected the
variable-latency advantage async is usually measured against.

---

## What this establishes

Bundled-data asynchronous logic can be generated automatically from a dataflow
IR and run correctly on a commodity FPGA through a fully open toolchain. That
much works and is reproducible.

It also establishes, with the terms separated, why you would not do it for
speed on this platform: the win case is empty on a fabric this heavily
optimised for synchronous design, and on ideal silicon the ceiling against a
dynamically-scheduled baseline is parity. That is a negative result, but a
clean one — every contributing term is named, measured where possible, and
attributed to fabric, protocol or implementation.
