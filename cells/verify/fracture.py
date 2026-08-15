#!/usr/bin/env python3
"""Did every fractured LUT6_2 land in ONE site?

    python3 verify/fracture.py [routed.json]

flow.sh used to answer this by counting FASM `LUT.INIT` lines and requiring
the total to track the yosys cell count, on the reasoning that a split pair
turns one site into two and the count runs ahead.  That proxy held for every
design this project had until gcd, where it reported

    FAIL: 5604 sites for 5014 cells -- fractured pairs were split

and every single one of the 1859 pairs had in fact held.  The 590 extra sites
were 736 LUTs NEXTPNR ITSELF inserted -- 589 `$PACKER_GND_NET$LUT$*` and 147
`$PACKER_VCC_NET$LUT$*` -- to drive constant nets.  Excluding them the design
occupied 4905 sites for 5014 cells, comfortably under.

So the proxy measured "sites" when the claim was about "pairs", and the gap
between the two is filled by something the packer is entitled to do.  This
checks the claim itself: for every cell that came out of a fractured pair,
the two halves must name the same SLICE and the same letter, differing only
in the 5/6 digit.  That is the same comparison hw/check_fracture.py makes for
the hardware rig, for the same reason -- two halves in different sites have
build-dependent routing between them.

The FASM count is still reported, because a site count that runs far ahead of
the design for a reason NOT accounted for here is worth seeing even when the
pairs are intact.
"""

import collections
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
JSON = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 \
    else ROOT / "build/pnr/soak_routed.json"

# nextpnr splits a fractured cell into <base>$LUT6 (the O6 function) and
# <base>$LUT5 (the O5 function), each carrying its own NEXTPNR_BEL.
HALF_RE = re.compile(r"^(.*)\$LUT([56])$")
BEL_RE = re.compile(r"^(SLICE_X\d+Y\d+)/([A-D])([56])LUT$")


def main():
    if not JSON.exists():
        print(f"no routed netlist at {JSON} -- run ./flow.sh first",
              file=sys.stderr)
        return 2

    cells = next(iter(json.load(open(JSON))["modules"].values()))["cells"]

    halves = collections.defaultdict(dict)
    packer = 0
    for name, cell in cells.items():
        bel = cell.get("attributes", {}).get("NEXTPNR_BEL", "")
        if not BEL_RE.match(bel):
            continue
        if "PACKER" in name:
            packer += 1
            continue
        m = HALF_RE.match(name)
        if m:
            halves[m.group(1)][m.group(2)] = bel

    pairs = {b: d for b, d in halves.items() if len(d) == 2}
    split = []
    for base, d in sorted(pairs.items()):
        m5, m6 = BEL_RE.match(d["5"]), BEL_RE.match(d["6"])
        # Same slice, same letter, and the 5/6 digit is the only difference.
        if (m5.group(1), m5.group(2)) != (m6.group(1), m6.group(2)):
            split.append((base, d["5"], d["6"]))

    if split:
        print(f"FAIL: {len(split)} of {len(pairs)} fractured pair(s) were "
              f"split across sites.")
        print("      Two halves in separate sites have identical intrinsic")
        print("      delay but different, build-dependent routing between")
        print("      them -- which is the precondition verify/MTBF.md needs.")
        for base, s5, s6 in split[:10]:
            print(f"        {base}: O5 at {s5}, O6 at {s6}")
        if len(split) > 10:
            print(f"        ... and {len(split) - 10} more")
        return 1

    note = f", {packer} packer-inserted constant driver(s) ignored" \
        if packer else ""
    print(f"fractured pairs held one site each "
          f"({len(pairs)} pair(s) checked{note})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
