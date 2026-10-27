#!/usr/bin/env python3
"""C-11c: check the hand-written composition `LinkArb.insts` (Lean) against
yosys's own flattening of link_arb.

    python3 compose.py fixture/link_arb.synth.json

The Lean logical design is 11a's per-cell netlists (synthesized as top
modules, formal/tools/import/json/*.json) wired by `BINDING` below, which must
be the same text as `insts` in formal/lean/Formal/Net/FasmLink/LinkArb.lean
(checked here by parsing that file).  This script resolves every LUT input
pin and every top-level output, on both sides, to a canonical source
("port:P", "cell:<path>.<O5|O6>", "const:0|1"), seeing through IBUF/OBUF,
and requires: the same LUT cells (by hierarchical name), the same type and
INIT, the same canonical source on every pin, the same source for every
output port.  Exit 1 on any difference.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "../../.."))
IMP = os.path.join(REPO, "formal/tools/import/json")
LEAN = os.environ.get("LINKARB_LEAN", os.path.join(REPO, "formal/lean/Formal/Net/FasmLink/LinkArb.lean"))
# instance path in link_arb, 11a JSON, Lean Gen name
INST = [("lnk.ctl.u", "bd_c2n", "bd_c2n"), ("lnk.lat", "bd_latch_W3", "bd_latch_W3"),
        ("arb", "bd_arbiter", "bd_arbiter")]
LUTS = ("LUT1", "LUT2", "LUT3", "LUT4", "LUT5", "LUT6", "LUT6_2")


def parse_insts():
    src = open(LEAN).read()
    body = src[src.index("def insts : List Inst := ["):src.index("theorem c2n_iface")]
    out = []
    for m in re.finditer(r'⟨"([^"]+)", Gen\.(\w+), \[(.*?)\],\s*\[(.*?)\]⟩', body, re.S):
        name, gen, ins, outs = m.groups()
        sig = []
        for s in re.findall(r'\.port "[^"]+"|\.st \d+ \d+', ins):
            mm = re.match(r'\.port "([^"]+)"', s)
            sig.append(("port", mm.group(1)) if mm else ("st",) + tuple(int(x) for x in s.split()[1:]))
        outl = [(int(i), p) for i, p in re.findall(r'\((\d+), "([^"]+)"\)', outs)]
        out.append((name, gen, sig, outl))
    return out


def bits_of(m):
    """port name (bit-blasted 'x[i]' if wide) -> (direction, bit)."""
    r = []
    for n, p in m["ports"].items():
        for i, b in enumerate(p["bits"]):
            r.append(("%s[%d]" % (n, i) if len(p["bits"]) > 1 else n, p["direction"], b))
    return r


def drivers(cells):
    d = {}
    for n, c in cells.items():
        for pin, bs in c["connections"].items():
            if c["port_directions"][pin] == "output":
                for b in bs:
                    if b in d:
                        sys.exit("compose: net %s multiply driven" % b)
                    d[b] = (n, pin)
    return d


def canon_factory(cells, port_of_bit, prefix, bind):
    drv = drivers(cells)

    def canon(b):
        if b in ("0", "1"):
            return "const:" + b
        if b in port_of_bit:
            return bind(port_of_bit[b])
        n, pin = drv[b]
        c = cells[n]
        if c["type"] in ("IBUF", "OBUF"):
            return canon(c["connections"]["I"][0])
        return "cell:%s%s.%s" % (prefix, n, {"O": "O6"}.get(pin, pin))
    return canon


def main():
    flat = json.load(open(sys.argv[1]))
    fports = {b: n for n, d, b in bits_of(flat) if d == "input"}
    fc = canon_factory(flat["cells"], fports, "", lambda p: "port:" + p)
    want = {}
    for n, c in flat["cells"].items():
        if c["type"] in LUTS:
            want[n] = (c["type"], int(c["parameters"]["INIT"], 2),
                       {p: fc(c["connections"][p][0]) for p, d in c["port_directions"].items() if d == "input"})
    wout = {n: fc(b) for n, d, b in bits_of(flat) if d == "output"}

    insts = parse_insts()
    if [(a, b) for a, b, _, _ in insts] != [(a, c) for a, _, c in INST]:
        sys.exit("compose: LinkArb.insts does not list %s" % INST)
    mods = []
    for (path, js, _), (_, _, sig, outl) in zip(INST, insts):
        m = list(json.load(open(os.path.join(IMP, js + ".json")))["modules"].values())[0]
        mods.append((path, m, sig, outl))
    # state j of instance k -> canonical cell output: 11a's state nets are the
    # LUT outputs routed back to their own LUT (Cells.lean `state`, same order
    # as yosys2lean's DFS); here: the driver of the OBUF/feedback net.
    cells_lean = open(os.path.join(REPO, "formal/lean/Formal/Net/Import/Cells.lean")).read()
    state = {}
    for k, (path, m, sig, outl) in enumerate(mods):
        gen = INST[k][2]
        blk = cells_lean[cells_lean.index("def %s : Netlist where" % gen):]
        st = [int(x) for x in re.search(r"state := \[([^\]]*)\]", blk).group(1).split(",")]
        drv = drivers(m["cells"])
        for j, b in enumerate(st):
            n, pin = drv[b]
            state[(k, j)] = "cell:%s.%s.%s" % (path, n, {"O": "O6"}.get(pin, pin))
    got, gout = {}, {}
    for k, (path, m, sig, outl) in enumerate(mods):
        ins = [(n, b) for n, d, b in bits_of(m) if d == "input"]
        if len(ins) != len(sig):
            sys.exit("compose: %s has %d inputs, binding gives %d" % (path, len(ins), len(sig)))
        pb = {b: s for (n, b), s in zip(ins, sig)}

        def bind(s, pb=pb):
            return "port:" + s[1] if s[0] == "port" else state[(s[1], s[2])]
        lc = canon_factory(m["cells"], {b: pb[b] for b in pb}, path + ".", bind)
        for n, c in m["cells"].items():
            if c["type"] in LUTS:
                got["%s.%s" % (path, n)] = (c["type"], int(c["parameters"]["INIT"], 2),
                                            {p: lc(c["connections"][p][0])
                                             for p, d in c["port_directions"].items() if d == "input"})
        outs = [b for n, d, b in bits_of(m) if d == "output"]
        for i, p in outl:
            if p in gout:
                sys.exit("compose: port %s bound twice" % p)
            gout[p] = lc(outs[i])
    bad = 0
    for n in sorted(set(want) | set(got)):
        if want.get(n) != got.get(n):
            print("  DIFF %s\n    yosys flat: %s\n    composed:   %s" % (n, want.get(n), got.get(n)))
            bad = 1
    if wout != gout:
        print("  DIFF outputs\n    yosys flat: %s\n    composed:   %s" % (wout, gout))
        bad = 1
    if bad:
        sys.exit(1)
    print("compose: LinkArb.insts = yosys flattening of link_arb (%d LUT cells, %d outputs, same INITs and pin sources)"
          % (len(got), len(gout)))


if __name__ == "__main__":
    main()
