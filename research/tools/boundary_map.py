#!/usr/bin/env python3
"""boundary_map.py ROUTED_JSON PREFIX OUT.tsv -- the nets that cross a kernel's hierarchy boundary in one route.

    python3 research/tools/boundary_map.py build/hw/gcd_ps/gcd_ps_routed.json bridge_i.udut. out.tsv

A kernel inside a harness (gcd_ps: bridge_i.udut) has no pins in the bitstream: its ports are ordinary nets.
Whoever decodes the bitstream (fasm2net here, formal's decoder there) has to be told which site pins they
are.  This lists every net with a driver on one side of PREFIX and a sink on the other: direction (in =
driven outside, read inside), the driver's BEL and pin (fasm2net names nets <bel>/<pin>), every name the
routed JSON gives the net, and the inside/outside sink counts.  Constant nets ($PACKER_GND/VCC, incl. legalised constant LUTs) are counted, not listed.  Everything comes
from nextpnr's routed JSON (NEXTPNR_BEL); nothing is inferred from names.
"""
import json, sys
from collections import defaultdict


def main():
    rj, pre, out = sys.argv[1:4]
    m = list(json.load(open(rj))["modules"].values())[0]
    names = defaultdict(list)
    for n, v in m["netnames"].items():
        for b in v["bits"]:
            if isinstance(b, int):
                names[b].append(n)
    drv, snk = {}, defaultdict(list)
    for cn, c in m["cells"].items():
        bel = c["attributes"].get("NEXTPNR_BEL", "?")
        for p, d in c.get("port_directions", {}).items():
            for b in c["connections"].get(p, []):
                if not isinstance(b, int):
                    continue
                if d == "output":
                    drv[b] = (cn, c["type"], bel, p)
                elif d == "input" and not cn.startswith("$PACKER_"):
                    snk[b].append(cn)     # packer-made constant/route-through LUTs are not logic
    rows = []
    nconst = 0
    for b, sinks in snk.items():
        if b not in drv:
            continue
        cn, typ, bel, pin = drv[b]
        d_in = cn.startswith(pre)
        s_in = [s for s in sinks if s.startswith(pre)]
        s_out = [s for s in sinks if not s.startswith(pre)]
        if d_in and s_out:
            direction = "out"
        elif not d_in and s_in:
            direction = "in"
        else:
            continue
        nm = sorted(names.get(b, []), key=lambda n: (not n.startswith(pre.split(".")[0]), len(n)))
        if nm and all(n.startswith(("$PACKER_GND", "$PACKER_VCC")) for n in nm):
            nconst += 1          # a constant (or a packer-legalised constant LUT): not a port
            continue
        rows.append((direction, bel + "/" + pin, typ, len(s_in), len(s_out), " ".join(nm[:4])))
    rows.sort(key=lambda r: (r[0], r[5], r[1]))
    with open(out, "w") as f:
        f.write("# nets crossing %s in %s (driver bel/pin = fasm2net's net name); %d constant nets omitted\n"
                % (pre, rj, nconst))
        f.write("dir\tdriver_pin\tdriver_type\tsinks_inside\tsinks_outside\tnames\n")
        for r in rows:
            f.write("\t".join(str(x) for x in r) + "\n")
    print("%d in, %d out -> %s" % (sum(r[0] == "in" for r in rows), sum(r[0] == "out" for r in rows), out))


if __name__ == "__main__":
    main()
