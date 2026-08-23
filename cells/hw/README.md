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
