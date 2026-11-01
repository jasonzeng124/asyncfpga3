#!/usr/bin/env python3
"""muxf.py (audit T4): decoded MUXF7/F8 gates vs nextpnr's SELMUX2_1 cells (own code).

    python3 -I muxf.py NET.json ROUTED.json

For every SELMUX2_1 cell at an F7AMUX/F7BMUX/F8MUX BEL: the decoded muxf gate exists, and the drivers
of nextpnr's ports 0 / 1 / S0 are the decoded I0 / I1 / S sources (S compared at the site pin AX/CX/BX:
the decoded S node must be driven, through pips, from nextpnr's S0 driver).
"""
import json
import re
import sys


def main():
    N = json.load(open(sys.argv[1]))
    R = json.load(open(sys.argv[2]))["modules"]["top"]
    names = N["nodes"]
    drv = {g["out"]: g for g in N["gates"]}
    mux = {g["name"]: g for g in N["gates"] if g["kind"] == "muxf"}
    bitdrv = {}
    for cn, c in R["cells"].items():
        for p, d in c["port_directions"].items():
            if d == "output":
                for b in c["connections"].get(p, []):
                    bitdrv[b] = (cn, c, p)

    def src_of(n):
        while True:
            g = drv.get(n)
            if g is None or g["kind"] not in ("pip", "hop"):
                return names[n] if g is None or g["kind"] != "const" else "CONST%d" % g["init"]
            n = g["ins"][0]

    def nx(b):
        d = bitdrv.get(b)
        if not d:
            return None
        cn, c, p = d
        s, be = c["attributes"]["NEXTPNR_BEL"].split("/")
        if c["type"] == "SLICE_LUTX":
            return "%s.%s%s" % (s, be[0], be[1])
        if c["type"] == "SLICE_FFX":
            return "%s.%s%sQ" % (s, be[0], "5" if be[1] == "5" else "")
        if c["type"] == "SELMUX2_1":
            return "%s.%s" % (s, {"F7AMUX": "F7A", "F7BMUX": "F7B", "F8MUX": "F8"}[be])
        if c["type"] == "CARRY4":
            return "%s.%s%s" % (s, "CO" if p.startswith("CO") else "XOR", p[-1])
        return c["type"]

    ok = bad = missing = 0
    for cn, c in R["cells"].items():
        if c["type"] != "SELMUX2_1":
            continue
        s, be = c["attributes"]["NEXTPNR_BEL"].split("/")
        nm = "%s.%s" % (s, {"F7AMUX": "F7A", "F7BMUX": "F7B", "F8MUX": "F8"}[be])
        g = mux.get(nm)
        out = c["connections"].get("OUT", [None])[0]
        if g is None:
            missing += 1
            # is its output used by anything?
            users = [(cn2, p) for cn2, c2 in R["cells"].items() for p, bits in c2["connections"].items()
                     if c2["port_directions"].get(p) == "input" and out in bits]
            print("not decoded: %s %s output users %s" % (nm, cn[:80], users[:5]))
            continue
        want = [nx(c["connections"][p][0]) for p in ("0", "1", "S0")]
        got = [names[g["ins"][0]], names[g["ins"][1]], src_of(g["ins"][2])]
        if want == got:
            ok += 1
        else:
            bad += 1
            print("MISMATCH %s: nextpnr %s decoded %s" % (nm, want, got))
    print("muxf: %d SELMUX2_1 cells agree, %d disagree, %d not decoded; decoded muxf gates %d" % (ok, bad, missing, len(mux)))


if __name__ == "__main__":
    main()
