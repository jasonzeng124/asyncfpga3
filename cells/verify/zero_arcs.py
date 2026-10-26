#!/usr/bin/env python3
"""Fail on any 0 ps INTERCONNECT in a routed SDF that is not a real 0 ps wire.

    python3 verify/zero_arcs.py build/pnr/soak.sdf build/pnr/soak_routed.json

Every routed arc between two sites crosses at least one pip, so 0 ps there
means the SDF writer was handed a sink wire that is not in the net
(patches/nextpnr-xilinx-lut-perm-sink.patch) and the number is a placement
estimate.  Two kinds of arc are legitimately 0 ps and pass:

  * into a PAD pin: the pad wire is the pin;
  * into data input 0/1 of an F7/F8 mux (SELMUX2_1) from a cell in the SAME
    SLICE: LUT O6 -> F7MUX and F7MUX -> F8MUX are dedicated wires inside the
    site, with no pip.  Their delay is the mux's own IOPATH (217-223 ps on
    the chipdb), which the SDF carries.  yosys 0.62 maps soak_top's two
    8-input functions this way; the select input S0 is routed and still has
    to be nonzero;
  * into select input S<k> of a CARRY4 from the O6 of LUT "ABCD"[k] in the
    SAME SLICE: the carry chain's propagate inputs are hardwired to the
    slice's own LUT O6 outputs, again with no pip.  Their delay is the
    CARRY4's S->O/CO IOPATH (210-472 ps on the chipdb), which the SDF
    carries.  First met on collatz (bdc/fusion_bench.py --mlir): all 64
    S arcs of its two 32-bit adders, on every one of three seeds, were
    same-site, letter-matched and 0 ps.  DI, CIN and CYINIT stay checked.

Anything else at 0 ps fails, including a mux data input fed from another
site, which would be a broken route rather than a site wire.
"""
import json
import re
import sys

ARC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+(.*)")


def unescape(name):
    return re.sub(r"\\(.)", r"\1", name)


def split_pin(ref):
    cell, _, pin = unescape(ref).rpartition("/")
    return cell, pin


def main(sdf_path, json_path):
    with open(json_path) as f:
        mods = json.load(f)["modules"]
    cells = {}
    for m in mods.values():
        cells.update(m.get("cells", {}))

    def site(cell):
        bel = cells.get(cell, {}).get("attributes", {}).get("NEXTPNR_BEL", "")
        return bel.split("/")[0] if "/" in bel else None

    bad, wires = [], 0
    with open(sdf_path) as f:
        for line in f:
            m = ARC.search(line)
            if not m or "(0:0:0)" not in m.group(3):
                continue
            src, snk = split_pin(m.group(1)), split_pin(m.group(2))
            if snk[1] == "PAD":
                continue
            c = cells.get(snk[0], {})
            if (c.get("type") == "SELMUX2_1" and snk[1] in ("0", "1")
                    and site(snk[0]) is not None and site(snk[0]) == site(src[0])):
                wires += 1
                continue
            bel = cells.get(src[0], {}).get("attributes", {}).get("NEXTPNR_BEL", "")
            if (c.get("type") == "CARRY4" and snk[1] in ("S0", "S1", "S2", "S3")
                    and src[1] == "O6"
                    and cells.get(src[0], {}).get("type") == "SLICE_LUTX"
                    and site(snk[0]) is not None and site(snk[0]) == site(src[0])
                    and bel.split("/")[-1][:1] == "ABCD"[int(snk[1][1])]):
                wires += 1
                continue
            bad.append(line.strip())
    if bad:
        print("FAIL: zero-delay INTERCONNECT arcs in the SDF -- the sink wire is not in")
        print("      the routed net (nextpnr-xilinx-lut-perm-sink.patch, patches/README.md)")
        for b in bad[:5]:
            print("        " + b)
        print(f"      {len(bad)} such arc(s)")
        return 1
    print(f"no zero-delay routed arc ({wires} in-site F7/F8 mux / CARRY4 S input wire(s) are 0 ps by construction)")
    return 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:3]))
