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
