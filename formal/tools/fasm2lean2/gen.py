#!/usr/bin/env python3
"""C-11c: generate Formal/Net/FasmLink/S<n>.lean for one routed seed.

    python3 gen.py FASM BELS NS OUT.lean [--json OUT.json]

1. runs fasm2lean2.py on FASM (the FASM read back from the .bit): the
   physical netlist (`luts`, `net`, `ports`, route data), from the bits and
   prjxray-db only;
2. appends `rho`, the proposed renaming "state net j of instance k is
   physical LUT output (.lut i .o)", made from the placement HINT `BELS`
   (cell -> BEL, extracted from nextpnr's routed JSON by route.sh) and the
   state nets / driver cells of the yosys-imported netlists in
   formal/lean/Formal/Net/Import/Cells.lean.  The hint is not trusted: the
   Lean proof (`Design.check`) fails if it is wrong.

INSTANCES must match formal/lean/Formal/Net/FasmLink/LinkArb.lean (`insts`).
"""
import argparse
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "../../.."))
CELLS = os.path.join(REPO, "formal/lean/Formal/Net/Import/Cells.lean")

# (instance path in link_arb.v, Gen netlist in Cells.lean)
INSTANCES = [("lnk.ctl.u", "bd_c2n"), ("lnk.lat", "bd_latch_W3"), ("arb", "bd_arbiter")]


def parse_cells(path):
    """Gen netlist name -> (state net ids, {net id: (cell name, out pin)})."""
    src = open(path).read()
    out = {}
    for m in re.finditer(r"^def (\w+) : Netlist where\n(.*?)(?=^def |^end )", src, re.S | re.M):
        name, body = m.groups()
        state = [int(x) for x in re.search(r"state := \[([^\]]*)\]", body).group(1).replace(" ", "").split(",") if x]
        drv = {}
        for c in re.finditer(r'name := "([^"]+)", kind := \.(\w+).*?conn := \[(.*?)\] \}', body, re.S):
            cname, kind, conn = c.groups()
            for pin, net in re.findall(r"\(\.(O5|O6|O), \.net (\d+)\)", conn):
                if kind in ("ibuf", "obuf"):
                    continue
                drv[int(net)] = (cname, {"O": "O6"}.get(pin, pin))
        out[name] = (state, drv)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("fasm")
    ap.add_argument("bels")
    ap.add_argument("ns")
    ap.add_argument("out")
    ap.add_argument("--json")
    a = ap.parse_args()
    js = a.json or a.out + ".json"
    r = subprocess.run([sys.executable, os.path.join(HERE, "fasm2lean2.py"), a.fasm,
                        os.path.join(HERE, "link_arb.xdc"), "--ns", a.ns, "--json", js, "--out", a.out],
                       stderr=subprocess.PIPE, text=True)
    sys.stderr.write(r.stderr)
    if r.returncode:
        sys.exit(r.returncode)
    res = json.load(open(js))
    phys = {(l["site"], l["lut"]): i for i, l in enumerate(res["luts"])}
    hint = {}
    for line in open(a.bels):
        cell, o, site, letter = line.split()
        hint[(cell, o)] = (site, letter)
    cells = parse_cells(CELLS)
    rho = []
    for inst, gen in INSTANCES:
        state, drv = cells[gen]
        row = []
        for n in state:
            cname, o = drv[n]
            key = ("%s.%s" % (inst, cname), o)
            if key not in hint:
                sys.exit("gen: no placement hint for %s %s" % key)
            if hint[key] not in phys:
                sys.exit("gen: hint %s -> %s is not a LUT site in the bits" % (key, hint[key]))
            row.append("(.lut %d .%s)" % (phys[hint[key]], o.lower()))
        rho.append("[%s]" % ", ".join(row))
    lean = open(a.out).read()
    endl = "end %s\n" % a.ns
    assert lean.endswith(endl)
    lean = lean[:-len(endl)] + (
        "/-- Proposed renaming (from the placement hint; checked, not trusted):\n"
        "    `rho[k][j]` = physical source of state net j of instance k, instances\n"
        "    %s. -/\n"
        "def rho : List (List Src) := [%s]\n\n" % (", ".join("%s (%s)" % x for x in INSTANCES), ", ".join(rho))) + endl
    open(a.out, "w").write(lean)


if __name__ == "__main__":
    main()
