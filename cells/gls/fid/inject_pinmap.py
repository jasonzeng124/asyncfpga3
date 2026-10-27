#!/usr/bin/env python3
"""
inject_pinmap.py -- negative control for the FASM-built GLS: the August
lut-pinmap bug's mechanism, applied to LIVE LUT pins.

    inject_pinmap.py ROUTED.json GOOD.fasm OUT.fasm [--prefix REGEX]

The bug (patches/nextpnr-xilinx-lut-pinmap.patch): fasm.cc split
X_ORIG_PORT_A<n> on ' ' and looked each token up with operator[], so a token
that was not a logical input name ('I1I3', or '' after a trailing space)
counted as I0.  The LUT's physical truth table was then computed as if that
physical pin carried I0 -- a different function, in the bitstream only.

Why an injection and not the plain re-encoding.  `verify/fasm_audit.py
--write-unpatched pinmap` re-encodes a route exactly as the unpatched writer
would.  On the current flow that changes 58 LUT sites of gcd_hw, but EVERY
run-together pin on this route (and on the other 19 distinct gcd_hw routes in
the scratch area) is tied to GND, where the corrupted half of the table is
never addressed: fasm_equiv.py proves all 58 functionally identical.  In
August the pins carried live nets (33 LUTs inside the comparator ucmpi11).  So
this script reproduces the August SIGNATURE: for every LUT under --prefix, one
physical pin that carries a single live logical input I<k> (k >= 1) gets the
unpatched writer's treatment -- its name is made unrecognisable, and the
emulated writer (fasm_audit.unpatched_lut_names, written line for line from
the unpatched fasm.cc) attributes it to I0.  Everything else in the FASM is
left byte-identical.
"""
import argparse, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), "verify"))
import fasm_audit as FA  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("routed")
    ap.add_argument("fasm_in")
    ap.add_argument("fasm_out")
    ap.add_argument("--prefix", default=r"(urig\.udut\.|uut\.)ucmpi",
                    help="regex matched at the start of the cell name (default: the comparators, "
                         "in the gcd rig or a fusion_bench soak harness)")
    a = ap.parse_args()
    cells = FA.top_cells(a.routed)
    sites = FA.load_sites()
    drv = {}
    for c in cells.values():
        for p, bl in c["connections"].items():
            if c.get("port_directions", {}).get(p) == "output" and bl:
                drv[bl[0]] = c["type"]
    slots = {}
    for cn, c in cells.items():
        m = FA.RE_BEL.match(c["attributes"].get("NEXTPNR_BEL", "")) if c["type"] == "SLICE_LUTX" else None
        if m:
            slots.setdefault((m.group(1), m.group(2)), {})[m.group(3)] = (cn, c)
    repl, hit = {}, []
    for (site, letter), slot in sorted(slots.items()):
        touched = False
        bad = {}
        for which, (cn, c) in slot.items():
            if not re.match(a.prefix, cn):
                continue
            attrs = dict(c["attributes"])
            for k in range(1, 7):
                v = attrs.get("X_ORIG_PORT_A%d" % k, "")
                bl = c["connections"].get("A%d" % k)
                if re.fullmatch(r"I([1-9]\d*)", v) and bl and \
                        drv.get(bl[0]) not in ("PSEUDO_GND", "PSEUDO_VCC"):
                    attrs["X_ORIG_PORT_A%d" % k] = v + "?"     # a token the writer cannot name
                    hit.append("%s/%s%sLUT A%d (%s -> read as I0)  %s" % (site, letter, which, k, v, cn))
                    touched = True
                    break
            bad[which] = dict(c, attributes=attrs)
        if not touched:
            continue
        good6 = slot.get("6", (None, None))[1]
        good5 = slot.get("5", (None, None))[1]
        lut6 = bad.get("6", good6)
        lut5 = bad.get("5", good5)
        feat = "%s.%sLUT.INIT[63:0]" % (FA.slice_prefix(site, sites), letter)
        repl[feat] = FA.expected_lut_bits(lut6, lut5, FA.unpatched_lut_names)
        if repl[feat] == FA.expected_lut_bits(good6, good5):
            del repl[feat]            # the corruption happens not to change the bits
    out, changed = [], 0
    for ln in open(a.fasm_in).read().splitlines():
        name = ln.split("=", 1)[0].strip()
        if name in repl:
            new = "%s = 64'b%s" % (name, format(repl[name], "064b"))
            changed += new != ln
            ln = new
        out.append(ln)
    open(a.fasm_out, "w").write("\n".join(out) + "\n")
    print("inject_pinmap: %d LUT pins mis-mapped under %r, %d LUT sites' INIT changed"
          % (len(hit), a.prefix, changed))
    for h in hit:
        print("  " + h)
    if changed == 0:
        sys.exit("inject_pinmap: nothing changed -- the control would be vacuous")


if __name__ == "__main__":
    main()
