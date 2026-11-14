#!/usr/bin/env python3
"""ffmux_scan.py FASM... -- flops nextpnr placed (ZINI/ZRST written) whose D-input mux (xFFMUX / x5FFMUX) has no bit.

The nextpnr-xilinx FASM gap of JOURNAL 2026-11-08 08:21 (a constant-D flop, $auto$dfflegalize emulate_split_set_clr,
gets no FFMUX because site routing never picks a pip for a constant D): on silicon that D comes from an unconfigured
mux.  Seen in a 5FF (collatz64 T4 bench seed 4) and in an AFF (xorshift p8+fastfall+merge link bench seed 2,
2026-11-12).  fasm_equiv catches it in the full stack (NOT EQUIVALENT: cell not configured by the bits); this is the
cheap check on a FASM alone.  Exit 1 if any file has one.
"""
import sys, re
bad_any = False
for f in sys.argv[1:]:
    ff, mux = set(), set()
    for l in open(f):
        m = re.match(r"(\S+\.SLICE[LM]_X\d)\.([A-D]5?FF)\.(ZINI|ZRST)", l)
        if m: ff.add((m.group(1), m.group(2)))
        m = re.match(r"(\S+\.SLICE[LM]_X\d)\.([A-D]5?FF)MUX\.", l)
        if m: mux.add((m.group(1), m.group(2)))
    bad = sorted(ff - mux)
    if bad:
        bad_any = True
        print("%s: %s" % (f, ", ".join("%s.%s" % b for b in bad)))
sys.exit(1 if bad_any else 0)
