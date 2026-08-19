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
