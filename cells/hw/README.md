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
