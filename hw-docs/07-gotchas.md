# 07 — Failure modes

## Hardware

| Failure | Detail |
|---|---|
| 4-phase RTZ not completed | holding `i_req` high after `i_ack` freezes the entry chain and deadlocks every loop after one traversal. Same for `o_ack` — mirror `o_req`, don't latch it high. Generated TBs return to zero correctly, so **simulation never sees it**. |
| Host-paced handshake wedge | any ms-cadence host (JTAG/AXI) violates the above; needs an async-clearing pulse adapter (`02` §5) |
| AXI3 IDs tied to 0 | hangs every CPU access and wedges the DAP; sim stays green if the TB drives ID 0 |
| `memmap` on the wrong context or too late | must be declared on the **APU** (the A9s inherit it) and **before** `fpga -f`. On a single `ARM*#0`, or after programming, it does not take and every access returns "Blocked address 0x40000000 ... has not been added to the memory map" — which reads like the `02` §8 "address not declared" entry even though it *was* declared. Both working scripts in `ref/zynq/` do it on APU before `fpga -f`. Nothing to simulate, so it fails only on hardware. |
| JTAG device-node perms | reset on every USB re-enumeration; needs user sudo |
| Board/cable state | not knowable remotely. Probe with `xc3sprog -c xpc -j` or xsdb `targets`. Ask the user for physical actions, not observations. |

**Hardware fails / sim passes ⇒ suspect the environment first.** Generated
TBs drive the protocol perfectly; real harnesses are where contract
violations hide.

## Netlist / synthesis

| Failure | Detail |
|---|---|
| Hierarchical refs into a flattened core | `dut.c3_req` becomes a phantom undriven wire. Export debug taps as real ports. A hand-edited generated file is then source, not an artifact — regenerating silently drops the taps. |
| `cell` as an instance name | reserved Verilog word |
| Post-route pin views | lie under fracturable-LUT packing (`04` §5b). Resolve via the pre-place JSON by net name; **raise** on unresolved probes, never score zero. |
| Implicit buffer insertion | yosys `clkbufmap` inserts a BUFG on clock pins unasked. A matched delay timing a response from the *pre*-buffer signal can be exceeded by BUFG insertion (~2 ns) ⇒ capture happens after "done" on silicon. Sim never sees it (no BUFG in the sim model); the structural audit passes vacuously if BUFG is a depth-0 source truncating the cone. Instantiate explicitly; keep capture clock and timing tap downstream of the same buffer. |
| `--timing-allow-fail` | silences failures beyond the waived class. Always pair with a narrow checker. |
| Placer tears a logical macro in half | a wirelength-minimising placer with no timing constraint puts two cells of one macro nanoseconds apart when one of them has heavy downstream fanout: the macro's internal net is one net among thousands and loses the vote. Measured on `bd_link` — C node to its OWN latch enable, median 1920 ps, p90 3405, while the same C node reaches its own delay chain in 639 ps, because the chain is a string of single-load nets and the latch's output is not. Invisible in the netlist and in simulation; visible only in routed SDF, and only if you go looking for an *intra-cell* delay. Fixed by relative placement (`patches/nextpnr-xilinx-rloc-group.patch`), not by padding the other path. |
| Inferred DSP48E1 computed the wrong product — FIXED | openXC7 on xc7z010: a design whose whole datapath was `a * b` returned 25 of 430 correct with DSP inference on. Cause: several DSP48E1 site pins (`INMODE0..4`, `ALUMODE2/3`, `OPMODE6`) have no interconnect path into the site — prjxray gives them a value only through a tile-local constant bit — and nextpnr-xilinx left three of those pin groups unwired, so no FASM bit was ever emitted and they came up at the tile default (`INMODE`=`11111` gates the multiply's A operand to zero per UG479). Source, post-synthesis netlist and routed timing were all clean; nothing before the bitstream showed it. Fixed by `patches/nextpnr-xilinx-dsp-constpins.patch`; `BD_DSP=1` is now `cells/flow.sh`'s default. **General lesson: openXC7 can silently emit no FASM bit for a site pin that has no routing path, leaving it at the tile default — this generalises past DSPs, to any const-only pin nextpnr's packer doesn't enumerate.** |

## Simulation

| Failure | Detail |
|---|---|
| `%0t` units | iverilog prints picoseconds under `timescale 1ns/1ps` |
| "Failure" with no timeout line | wall-clock kill, not a deadlock — raise the sim timeout |
| Missing log file entirely | something deleted the build dir mid-run, usually a concurrent `rm -rf`. Rerun that design in isolation first. |
| Concurrent writers to one build dir | one script's regenerate-or-`rm -rf` deletes files another is mid-read on; surfaces as a spurious FAIL with no log. Partition by design name. |
| Zero-delay datapath assigns | hide mispriced logic — a wrong depth estimate is invisible until routed. Found only by routed signoff: unary minus priced at 1 LUT when it lowers to a carry chain; a steer gate one hop thinner than every latch consumer (a sibling design passed by routing luck). |

## Toolchain

| Failure | Detail |
|---|---|
| Bare `yosys` fails | not on `$PATH` (`01`) |
| Wrong yosys | two binaries exist — ice40 build vs. openXC7 build with `synth_xilinx` |
| `fasm2frames` in `~/.local/bin` | broken (missing `utils` import); call the prjxray source copy with `PYTHONPATH` set |
| `ninja` not installed | relevant for LLVM-based builds defaulting to it |
| `nextpnr-xilinx.bak` | same version string, lacks the timing-model fix — use the non-`.bak` |
| chipdb rebuild | slow; `xc7z010clg400` already exists |

## Debugging method

- **Deadlocks are stuck phases.** Trace the token: find the channel whose
  handshake never completed and ask which side reneged. Data values are
  almost never the story.
- **Prove transitions, not states.** A truth table over stable states can
  look airtight while an edge mid-return-to-zero breaks everything.
- **Simulate, don't argue.** Handshake logic is where plausible reasoning
  fails silently.
- **One route is a sample, not a measurement.** The same design at four
  placer seeds gave 0, 6, 5 and 3 rule-E violations with nothing changed
  but the seed. Margins here are 76–400 ps and routing scatter is larger,
  so a single-route count reads as a pass or a bug and is neither. Sweep
  seeds and report the spread; `cells/verify/rloc_sweep.sh` shows the shape.
- **Root cause, then minimal fix.** A constant that doesn't fix a race is
  evidence the mechanism is misunderstood, not grounds for a bigger
  constant.
- **Prefer structural exclusion over arbitration.** Arbitration between
  uncoordinated requesters is analog — any decision element can
  metastabilize and LUT fabric has no mutex cell. Guarantee exclusion by
  construction; treat a real arbiter as a component with a settle-time
  budget.
- **A primitive needing a paragraph of caveats is a redesign candidate.**
