# Toolchain patches

Patches this project applies to its ONE installed toolchain
(`/home/jayjay/dev2/lib/fpgatoolchain`).  There is no second toolchain and no
parallel build: apply, rebuild, reinstall over `openxc7/bin/`, and record which
nextpnr produced a given route.

## nextpnr-xilinx-lut-pinmap.patch

Base: `nextpnr-xilinx` at `bfdeaf7c`.  Applies to `xilinx/fasm.cc`.

**A LUT whose physical pin carries more than one logical input was encoded into
the bitstream as a different function than the netlist says.**  Silent, and
visible only on the die.

`X_ORIG_PORT_A<n>` records which logical inputs the packer put on each physical
A-pin.  It is not consistently delimited -- the same routed design contains both

    'I0 I3'   'I2 I3 I4'      space separated
    'I1I3 '   'I3I1 '         run together, with a trailing space

`fasm.cc` split on `" "`, so the second form yielded the single token `I1I3`,
which is not a logical input name.  The lookup was
`unordered_map::operator[]`, which **inserts a missing key with value 0** and
returns it -- so the pin was encoded as if it drove `I0`, and the LUT got a
truth table that is not its function.  No error, no warning.

On gcd_hw this hit **131 LUTs, 33 of them inside `ucmpi11`** alone (the
`sgt(diff, -1)` that turns `a - b` into `|a - b|`).  Everything upstream of the
bitstream stayed correct -- the JSON, the SDF, and every simulation of them --
so the design failed on silicon and nowhere else, as an ABSENT result rather
than a wrong one: a comparator that answers wrongly makes gcd's abs skip the
negation, `a` goes negative, `while (a != 0)` never terminates, and the rig
reports `errs=0` with no answer at all.

The fix matches `I<digits>` by name instead of trusting the separator, and uses
`find()` so an unrecognised name is a `log_error` rather than a vote for `I0`.

Effect on the gcd hardware rig, same source, same seed:

| | result |
|---|---|
| before | 7/16, nine vectors never completing |
| after  | **16/16**, `err_sticky=0x0000`, `ok_sticky=0xFFFF` |

`cells/gls/gen.py` had the same bug independently, in its own reimplementation
of `get_lut_init()` -- which is why gate-level simulation insisted gcd's
comparator answered 0 for ordinary positive numbers while the same bitstream on
the die was getting 31-iteration vectors right.  Both readers are fixed; the
writer is left alone, because a reader that depends on the separator is the
defect.

## nextpnr-xilinx-dsp-constpins.patch

Base: `nextpnr-xilinx` at `bfdeaf7c`.  Applies to `xilinx/pack_dsp_xc7.cc` and
`xilinx/fasm.cc`.

**An inferred DSP48E1 multiplier ignored its A operand and returned
near-constant junk.**  Correct netlist, correct post-synthesis simulation,
clean timing -- wrong on the die only.

prjxray gives some DSP48E1 site pins no interconnect path into the site at
all: they appear in `segbits_dsp_{l,r}.db` only as `<PIN>.DSP_GND_*` /
`<PIN>.DSP_VCC_*`, in no ppips/pips list, so a tile-local constant bit is the
*only* way to give them a value. The full set, for every 7-series part in the
db:

    D0..D24  RSTD  CARRYINSEL2  CED  CEAD  CEINMODE  CEALUMODE
    INMODE0..4  ALUMODE2  ALUMODE3  OPMODE6

`pack_dsps()` in `pack_dsp_xc7.cc` converted the first seven groups and left
`INMODE0..4`, `ALUMODE2`, `ALUMODE3` and `OPMODE6` commented out with `//
TODO: these seem to be inverted for unknown reasons`. Those pins stayed on
`$PACKER_VCC_NET`/`$PACKER_GND_NET`, the router had nowhere to take them, no
bit was ever emitted, and each pin came up on silicon as the tile default --
the complement of what a VCC/GND net implies. For a plain inferred `a * b`
that turns `INMODE` `00000` into `11111`: per UG479 Table 1-11,
`INMODE[1]=1` gates the multiplier's A input to zero. `OPMODE[6:4]` also
went `000` &rarr; `100` (P fed back into the Z mux instead of zero) and
`ALUMODE[3:2]` `00` &rarr; `11`.

Just uncommenting those three lines makes it worse (board goes fully inert),
which is the "seem to be inverted" TODO talking about something real: these
pins bypass the site's optional input inverter, so `ZIS_*_INVERTED` -- which
`fasm.cc` applies to every *routed* pin -- never touches them. The constant
chosen for a const-only pin has to already carry the logical value.
`write_const_pins()` in `fasm.cc` tried to do exactly that, but
`boost::erase_all(pin_basename, "0123456789")` strips every digit out of the
pin name, turning `INMODE1` into `INMODE` and looking up
`IS_INMODE_INVERTED` -- a parameter yosys never emits, since it writes the
per-bit `IS_INMODE[1]_INVERTED`. The lookup silently returned false for
every bussed pin, every time.

The fix keeps the trailing digit as a bus index instead of discarding it,
and checks `IS_<name>[<idx>]_INVERTED` (plus the plain and integer-bitmask
forms, for whichever encoding a given yosys version emits) rather than a
digit-stripped name that never existed as a parameter.

Measured on an EBAZ4205 (xc7z010clg400), reading results back over JTAG:

| test | before | after |
|---|---|---|
| bit-walk, all 16 A bits x 2 DSPs | A had zero effect | all correct |
| `mult2_ps`, two lone 16x16 | 1/315 and 315/315 | 415/415 and 415/415 |
| `mult_ps`, 32x32 three-DSP cascade | 25/430 | 430/430 |
| `ipow_ps`, real kernel | 965/2016 | 516/516 |

Ruled out along the way: timing (a 10 MHz run was bit-identical to the 100 MHz
one, which is what pointed at the bitstream rather than a race), the
`fasm.cc:449` DSP ppip drop (those ppips are `always` with no bits, so
dropping them is correct and harmless), synthesis (the post-yosys netlist for
a bare 32x32 multiply matches `cells_sim.v` on 4007/4007 vectors, including
every operand the board got wrong), and the bdc compiler.

## nextpnr-xilinx-rloc-group.patch

Base: `nextpnr-xilinx` at `bfdeaf7c`.  Applies to `xilinx/pack.cc`,
`xilinx/pack.h` and `xilinx/arch_place.cc`.  The `arch_place.cc` hunk is
the fork's post-placement repair (`fixupPlacement`, which moves a cluster
whose root the placer left on a 5LUT slot) learning that a cluster's children
carry x/y offsets too: computing every member's bel from the root's tile
alone put two members of a column on one bel and tripped `bindBel`'s
assertion on the first multi-tile group.

**Relative placement from a netlist attribute.**  Not a bug fix -- a missing
feature, and upstream-able as it stands because nothing in it knows what this
project's cells are.

Cells carrying the same string value for the `RLOC_GROUP` attribute are tied
into one cluster: same tile, consecutive logic slots.  The cluster as a whole
is unconstrained and floats over the whole device, so this is Vivado's
`RLOC`/`H_SET` idea and **not** a `LOC` or a pinned BEL.  Four logic slots on
xc7 (one SLICE; eight on xcup) fill one tile, a fractured `LUT6_2` pair
counting as one; a group naming more is laid out as a **column**, one row of
slots per tile, the rows stacked alternately above and below the root's
(dy = 0, +1, -1, +2, -2, ...) so the root sits mid-column, up to as many
tiles as the tallest unbroken run of logic tiles in the device's grid (25 on
xc7z010, a clock region; it was a constant nine until 2026-09-20, which cut a
pipeline of more than three W=32 stages into separately floating segments).  A group needing more than that, or containing a BEL-pinned or
absolutely-z-constrained cell, is dropped **whole** with a warning -- a
half-applied relative-placement constraint measures as a success on the
members that did get it.  The column is what lets `rloc_stamp.py`'s `v3`/`v4`
name a whole W=32 latch bank (17 slots, 5 tiles) or a matched delay chain.

Why it is needed.  A wirelength-minimising placer with no timing constraint to
contradict it puts two cells of one logical macro nanoseconds apart when one of
them has heavy downstream fanout: the macro's internal net is one net among
thousands and loses the vote.  Carry chains already get relative placement
(`pack_carries`), by hardcoding what a carry chain is.  This lets a front end
say "these belong together" for a macro nextpnr has never heard of.

Measured on `bd_link`, this project's storage primitive, whose C-element drives
both a matched delay chain and a transparent latch.  The attribute is stamped
by `cells/hw/rloc_stamp.py` on the post-synthesis JSON (`cells/rtl/` is frozen,
so it cannot come from the RTL); `cells/verify/rloc_sweep.sh` reproduces the
numbers.  Four seeds, two designs, `verify/skew.py` rule E:

| | rule-E violations, 4 seeds | worst guarded margin |
|---|---|---|
| unclustered | gcd 0/6/5/3, ipow 2/2/2/0 | -801 ps |
| C node + one latch LUT (v1) | **0 in all 8 routes** | +396 ps |
| + the consuming bd_mux's joins (v2) | **0 in all 8 routes** | +594 ps |

The C node to its own grouped latch bit falls from a mean 1529 ps of
interconnect to 162 ps on gcd, and the *rest* of that link's latch bank
improves too (2142 -> 1742 ps) because the controller is now anchored inside
its own bank instead of wherever fanout dragged it.  Packing is untouched --
the routed netlist's cell set is byte-identical across all three variants, only
the placement moves -- so LUT sites are unchanged (6635 on gcd, 1449 on ipow),
CLB tiles spread by about 1%, and place-and-route wall time varies less between
variants than it does between runs of the same variant.

**Slot-ordered and multi-column groups** (`RLOC_SLOT`, `RLOC_COL`).  A member
carrying an integer `RLOC_SLOT` is laid at that slot -- row `slot/8`, logic
slot `slot%8` on xc7 -- instead of in name order, so a front end can lay a
group out in the order its transitions travel and leave gaps.  `RLOC_COL`
(default 0) puts a member in a neighbouring logic column of the same rows.
Logic columns are not evenly spaced on the die (CLB pairs sit back to back,
interconnect and BRAM/DSP columns come between), so the grid offset of column
`c` is read from the device: the spacing pattern the most consecutive logic
columns share (the log line `RLOC_COL offsets {...} hold at N of M logic
columns`), and anchors where it does not hold are illegal for the cluster
exactly as a column straddling a row without logic is.  Duplicate slots in one
column are a front-end bug and are warned about, that column then packing
densely rather than the group being dropped.  All three attributes are copied
from a `LUT6_2` to both halves the packer splits it into, so a fractured pair
still spends one slot.  This is what `rloc_stamp.py` `v5`..`v9` build their
control spine and side columns from; `cells/hw/README.md` has the measurements.

Fingerprints for `cells/verify/toolchain.sh`, each checked BOTH ways (present
in the patched binary, 0x unpatched; the second also 0x in a binary carrying
only the single-tile revision of this patch, the third 0x in one carrying only
the column revision) -- add them when the binary is installed, not before:

    "Packing RLOC_GROUP relative-placement clusters|nextpnr-xilinx-rloc-group.patch|RLOC_GROUP relative placement (bd_link C node next to its latch)"
    "tallest logic column on this device|nextpnr-xilinx-rloc-group.patch|RLOC_GROUP columns as tall as the device (whole latch bank, delay chain, a whole pipeline)"
    "RLOC_COL offsets|nextpnr-xilinx-rloc-group.patch|RLOC_SLOT/RLOC_COL slot-ordered, multi-column groups (spine v5+)"

## nextpnr-xilinx-place-weight.patch

Base: `nextpnr-xilinx` at `bfdeaf7c`.  Applies to `common/place_common.{cc,h}`,
`common/placer1.cc` and `common/placer_heap.cc`.  Independent of the rloc
patch; nothing in it is specific to this project.

**Per-net placement weight from a netlist attribute.**  A net carrying an
integer `PLACE_WEIGHT` (clamped to 1..1000, 1 when absent) has its wirelength
term multiplied by it in both placers: HeAP's solver weights and its HPWL
report, and placer1's per-net bounding-box cost.  Why: classic STA sees a
handshake ring as a combinational loop and `--ignore-loops` cuts it, so no net
in the ring is ever critical and every one of them is placed by the same
wirelength objective as a data bit with thirty siblings.  The weight is how
`cells/flow.sh` (`BD_PLACE_WEIGHT`, via `rloc_stamp.py weight_control_nets`)
tells the placer which nets are the cycle: req/ack/C-node nets, not reset and
not the bundled data.  The stamper decides what a control net is; the patch
only reads the number.

Fingerprint, 0x in every binary without this patch (the string is new):

    "carry PLACE_WEIGHT|nextpnr-xilinx-place-weight.patch|PLACE_WEIGHT net weighting in both placers"

## nextpnr-xilinx-ff-timing.patch

Base: `nextpnr-xilinx` at `bfdeaf7c`.  Applies to `xilinx/python/parse_sdf.py`,
`xilinx/python/nextpnr_structs.py`, `xilinx/arch.{h,cc}`.  Independent of the
other patches; nothing in it is specific to this project.  **Needs the chipdb
regenerated** (`bbaexport.py` + `bbasm`) as well as the binary rebuilt -- the
checks live in the `.bin`.

**Slice flip-flops had placeholder timing: 100 ps clock-to-Q, 100 ps setup,
100 ps hold, for every FF on every device.**  `getPortClockingInfo` never read
the chipdb.  Two halves to the fix:

1. The chipdb importer only understood `(SETUPHOLD ...)` records, and prjxray
   emits `(SETUP ...)` and `(HOLD ...)` separately, so no FF check ever reached
   the `.bin` (the SETUPHOLD/WIDTH branches were also dead code that would have
   appended a *list* to the check table).  The importer now keeps both forms.
2. `getPortClockingInfo` looks the FF up in the slice's timing instance:
   variant `REG_INIT_FF` for AFF..DFF (`BEL_FF`), `FF_INIT` for the 5FFs
   (`BEL_FF2`); `CLK->Q` from the IOPATH, `DIN`/`CE` setup and hold from the
   checks.  On xc7z010-1 that is CK->Q 303..362 ps, setup -45..-60 ps (yes,
   negative, at the FF's own pin), hold 225..262 ps.

Why it matters here: every routed number for a design with FFs -- the
synchronous reference in `cells/verify/sync_ref/`, the two-phase FF link (`rtl/bd_mlink.v`) -- used to be
2.5x optimistic on CK->Q and 2.5x optimistic on hold.  The sync reference's
`Fmax` moved from 467 to 434 MHz on the same route; the FF link's hold audit
had 100 ps where the device wants 241.

Fingerprint, 0x in every binary without this patch (the string is new to the
binary; it already existed in the chipdb as a variant name):

    "REG_INIT_FF|nextpnr-xilinx-ff-timing.patch|slice FF CK->Q/setup/hold from the chipdb, not 100 ps placeholders"

Stale chipdb: a `.bin` built before the importer fix still routes and still
writes an SDF, but every FF `SETUPHOLD` in it reads `(100:100:100)`.
`cells/flow.sh` fails the route when it sees that.

## nextpnr-xilinx-lut-perm-sink.patch

Base: `nextpnr-xilinx` at `bfdeaf7c`.  Applies to `xilinx/arch_place.cc`
(`fixupRouting`).  Independent of the other patches; nothing in it is specific
to this project.

**Every SDF `INTERCONNECT` into a LUT input that the router reached through a
permutation pip was the placer's distance estimate, not the routed delay.  On
this project's routes that was 6 arcs in 10, and 0 ps for every same-slice
arc -- C-element feedback, latch feedback, the hop between two links of a
matched delay chain.**

The arch models the LUT input crossbar as `PIP_LUT_PERMUTATION` pseudo-pips
(tile pin `D5` -> site wire `D3`, say), so the router may bring a net in on
any pin and the INIT is permuted to match.  `fixupRouting` then renames the
cell's ports after the tile pins the nets actually arrived on, so the JSON
and the bitstream agree.  What it did not do is tell the timing side: after
the rename, `getNetinfoSinkWire()` maps port `A5` to bel pin `A5` to site wire
`D5`, and the routed net never visits `D5` -- it ends on `D3`.
`Context::getNetinfoRouteDelay` walks the route back from the sink wire it is
given, fails to find it in the net, and quietly returns `predictDelay()`:

    same slice, same LUT pair       0 ps
    same tile, other pair         150 ps
    other tile                    450 + 90*|dy| + 45*|dx| ps

which is exactly the histogram of the old SDF (375 of 1637 arcs at 0, then
540, 630, 585, 900, 495 ...).  Identity-pin sinks got the real routed sum;
the other 658 pins got the estimate.  The router itself was fine -- during
routing the ports still had their logical names and the sinks were the right
site wires -- so the routes are good and only their reported delays were
wrong.  Post-route STA and the SDF both read through the same call, so the
sync reference's `Fmax` and every routed-GLS number were built on it.

The fix is one line per LUT half: when `fixupRouting` renames a port for the
tile pin, record the site pin it actually landed on in `cell->pins`, which is
the map `getNetinfoSinkWire()` already consults.  Nothing else reads that map
for LUTs (a checksum does), and the JSON/FASM writers are untouched.  The
routed count is logged (`Recorded N permuted LUT input pins as routed sink
wires`, N counting a fractured LUT6_2 twice).

Same route (`fb-gated2-v9r25`, fusion on cap 4), same JSON, SDF regenerated
by the two binaries:

| | before | after |
|---|---|---|
| arcs at 0 ps | 375 | 1 (the OBUF pad) |
| same-slice O6 -> A hop | 0 | 295 |
| next-tile hop (dy=1) | 540 | 426..444, 576 |
| `stage[0].ctl.u.u/O6 -> A5` (C-element feedback) | 0 | 295 |

Consequence for this project: every routed latency/interval reported before
this patch was optimistic, and the matched delays were sized against an SDF
that undercounted the very hops the chains are made of.  `cells/flow.sh`
refuses an SDF with a zero-delay inter-cell arc; `README.md` has the
re-measured numbers.

Fingerprint, 0x in every binary without this patch (the string is new):

    "permuted LUT input pins as routed sink wires|nextpnr-xilinx-lut-perm-sink.patch|SDF INTERCONNECT to a permuted LUT pin was the placer's estimate (0 ps in-slice), not the route"
