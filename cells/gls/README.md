# `gls/` — gate-level simulation of the routed design, with the routed delays

Every other simulation in this project runs on the RTL with zero wire delay.
On this part that is not a small idealisation: **the median routed wire is
720 ps against a flat 124 ps for the logic itself**, so a zero-delay run is
throwing away most of every path. A whole class of bug is invisible to it by
construction, and in August 2026 that class cost days — RTL simulation passed
all sixteen gcd vectors at both corners while the board deadlocked seven.

This directory simulates what the router actually built, with what the router
actually measured.

```
cells/hw/build_hw.sh gcd_hw      # produces the routed JSON + SDF
cells/gls/build.sh   gcd_hw      # ~7 min: netlist, annotation, two vvp images
cells/gls/run.sh     gcd_hw      # ~2 min: all 16 vectors
```

Sources live here; everything generated lands in `build/gls/<design>/`, which is
gitignored — it is ~900 MB per design and all of it is a function of two files.

## The two traps, because both are silent

**1. iverilog accepts `(INTERCONNECT …)` and applies none of it.** Verified
directly: a 5000 ps interconnect on a two-inverter probe changes the output time
by zero. No warning, no error. Take the obvious path and you get a simulation
that reports itself fully annotated, runs, produces plausible numbers, and has
discarded ~85% of every path.

`gen.py` turns each one into a real cell instead. The routed JSON has exactly
one interconnect per connected input pin — 45569 entries, 45569 distinct
destinations, zero connected input pins without one — so every sink pin gets its
own private net driven by an `ICBUF` and the SDF entry becomes an `IOPATH` on
it. That is exact, not an approximation, and it preserves the thing an
asynchronous design actually depends on: a driver's fanout arriving at each of
its sinks at *its own* routed time, which one shared net cannot express.

**2. nextpnr escapes individual characters** inside instance paths
(`\$abc\$8577\$auto\$blifparse.cc\:557\:parse_blif\$8578`). iverilog 11's SDF
lexer rejects that and then discards the **whole** delayfile. Since `gen.py`
generates the netlist it also owns the names: every cell becomes `c_NNNNNN` and
the SDF is rewritten through the same bijection. `names.map` records both
directions, so a failing cell always traces back to `urig.udut.ucond_br10`.

## The acceptance gate — run it before believing any behaviour

```
vvp gate.vvp        # must print ANNOTATE_DONE and no SDF WARNING/ERROR lines
```

Everything is an `IOPATH` after the rewrite, so the gate is one number: iverilog
either matched all of them or it names the ones it did not. It does report every
failure mode — unmatched ModPath, missing instance, wrong celltype — so silence
is proof rather than absence of evidence.

At the time of writing: **86517 claimed, 86517 accepted; 896 SETUPHOLD claimed,
896 accepted; zero warnings.** Cross-checked by diffing a full run of the
annotated build against one with the same numbers baked in as parameters —
every event timestamp identical.

`gate.vvp` costs ~6 minutes of annotator time before time 0, because iverilog
rescans the scope tree per entry over 58k instances. `run_baked.vvp` is the same
numbers from the same parse, baked in, and starts in seconds. Use the baked one
for work and the gate to prove the numbers.

## Reading a result honestly

**This simulation is more pessimistic than silicon.** nextpnr's cell arcs are a
flat 124 ps on O6 and 116–153 ps on O5, where the part's own are 56–152 ps and
both pin- and edge-dependent; `verify/tighten.py`'s header calls these "the
weaker half of every number". On 2026-08-17 it failed 11 of 16 gcd vectors where
the board failed 7 — so **four of its failures were its own pessimism.** A
failure here that the board gets right is not a bug report. Check against
hardware before acting on it.

It is also delay-sensitive in the direction that makes it worth having: the same
netlist re-run with routing removed passes only 2 of 16 rather than 5. Vectors 4,
9 and 10 pass *only* when the real routed delays are present. That is precisely
what a zero-delay run cannot show.

## Telling a wedge from a spin

The distinction matters more than it sounds. A **deadlock** is frozen —
everything stops. A **livelock** is busy — the circuit runs happily and never
finishes. They have opposite causes and nearly identical symptoms from outside,
and on gcd the answer was livelock after two days of assuming deadlock.

- `gen_probe.py <prefix>` → `probe.vh`, last-transition time for every cell
  output under that prefix. Anything still transitioning at the cutoff is busy.
- `gen_chan.py` → `chan.vh`, per-handshake-channel activity. On the gcd
  livelock this reported 149 of 525 wires still cycling and 376 frozen, which
  localised the fault to one loop.
- `tb_wedge.v`, `tb_chan.v`, `tb_trace.v` drive those.

## Files

| | |
|---|---|
| `gen.py` | routed JSON + SDF → `netlist.v`, `netlist_baked.v`, `annot.sdf`, `names.map`, `nets.map` |
| `prims.v` | the ten bel models plus `ICBUF`; all timing in parameterised `specify` paths |
| `tb_gate.v` | the acceptance gate |
| `tb_run.v` | the driver — `+VEC` `+TEND` `+QUIET` |
| `gen_probe.py`, `tb_wedge.v` | last-transition probe |
| `gen_chan.py`, `tb_chan.v` | per-channel wedge-vs-spin |
| `tb_trace.v` | loop trace |
| `match.py` | SDF ↔ routed-netlist name check (12796/12796 at time of writing) |
| `build.sh`, `run.sh` | build one design; sweep all sixteen vectors |

## Modelling notes, and one caveat

`CARRY4` carries a `PRECYINIT_CONST` parameter that nextpnr uses *instead of*
routing the CI pin, and both of gcd's subtractors have it set. Modelling it as 0
makes every `a-b` one too small — which held the pass rate at 2/16 and is
invisible to the two vectors that never enter the loop. 20 of the 247 flops are
`FDSE`, not `FDRE`, and `rst_sr` is built from them; modelled as FDRE the rig's
reset never asserts at all.

Both were found by running it, and both are the same kind of defect: a parameter
that changes behaviour and is easy not to read. A parameter census over every
cell type turned up nothing else unread — but the fact that two existed is the
reason to treat a surprising result here as a question about the model first.

The housekeeping ring oscillator has no defined initial state and stays `x`
forever in simulation. `tb_run.v` forces one node in it low for 50 ns and
releases before anything is measured. That is a simulation-setup issue, not a
design bug — a real ring starts from noise.
