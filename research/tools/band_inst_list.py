#!/usr/bin/env python3
"""band_inst_list.py ROUTED_JSON REGEX BAND OUT -- a GLS_SDF_BAND_INST file: the BEL of every cell whose name
matches REGEX, at BAND.

    python3 research/tools/band_inst_list.py gcd_hw_routed.json '\\.chain\\.g\\[\\d+\\]\\.u$' 0.21 chains.band

The SDF a full-stack GLS reads names instances by BEL (the netlist is decoded from the bits), so cells are mapped
through nextpnr's NEXTPNR_BEL.  The default regex is every bd_delay chain LUT (the matched delays: compute udly,
link rdly, uack, ...).  A cell without a placed BEL is an error, not a silent omission.
"""
import json, re, sys


def main():
    rj, rx, band, out = sys.argv[1:5]
    m = list(json.load(open(rj))["modules"].values())[0]
    r = re.compile(rx)
    rows = []
    for n, c in m["cells"].items():
        if r.search(n):
            bel = c["attributes"].get("NEXTPNR_BEL")
            if not bel:
                sys.exit("band_inst_list: %s has no NEXTPNR_BEL" % n)
            rows.append(bel)
    if not rows:
        sys.exit("band_inst_list: no cell matches %r" % rx)
    with open(out, "w") as f:
        f.write("# %d cells matching %s in %s, band %s\n" % (len(rows), rx, rj, band))
        for b in sorted(set(rows)):
            f.write("%s %s\n" % (b, band))
    print("%d cells (%d BELs) -> %s" % (len(rows), len(set(rows)), out))


if __name__ == "__main__":
    main()
