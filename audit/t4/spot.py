#!/usr/bin/env python3
"""spot.py (audit T4): spot-check decoded LUT gates against the read-back bits and nextpnr's routed JSON.

    python3 -I spot.py NET.json BND.json CANON_READBACK.fasm ROUTED.json LEANDIR [N] [SEED]

Auditor's own code (no formal/ import). For N LUT sites in the kernel cone (random, seeded, plus every
kernel LUT site whose nextpnr site wiring permutes the LUT pins, up to N/3 of them):
 (a) INIT: the decoded lut6 gate's INIT == the 64 INIT bits read from the canonical read-back FASM
     (own parse) == the INIT of the gate of that name in the generated Lean data (LEANDIR/G*.lean);
 (b) function: the physical INIT implied by nextpnr's cells (logical INIT of the 6LUT/5LUT cells, the
     BEL-pin -> logical-input map X_ORIG_PORT_*, and the tile-wire -> BEL-pin site wiring in ROUTING)
     equals the decoded INIT on every address consistent with the physical pins tied to a constant;
 (c) connections: for every physical pin, the decoded driver chain (pip/hop gates back from the pin's
     node) ends at the site net that nextpnr's net driver names (LUT O6/O5, FF Q, CARRY4, MUXF, const),
     and every decoded pip on that chain is a pip of that nextpnr net (compared as (src node, dst node)
     with xnode's own node resolution).
"""
import glob
import json
import os
import random
import re
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xnode import XDB  # noqa: E402


def lean_gates(d):
    """name -> (k, init, [in node names], out name) from the generated Lean files."""
    names = []
    for m in re.finditer(r'def n\d+ : List String := \[(.*?)\]\n', open(os.path.join(d, "Nodes.lean")).read(), re.S):
        names += json.loads("[" + m.group(1) + "]")
    out = {}
    for f in sorted(glob.glob(os.path.join(d, "G*.lean"))):
        for line in open(f):
            m = re.match(r'^\s*⟨("(?:[^"\\]|\\.)*"), (\d+), (\d+), \[([\d, ]*)\], \[.*\], (\d+)⟩,?\]?$', line)
            if m:
                ins = [names[int(x)] for x in m.group(4).split(",") if x.strip()]
                out[json.loads(m.group(1))] = (int(m.group(2)), int(m.group(3)), ins, names[int(m.group(5))])
    return out


def main():
    netp, bndp, canon, routedp, leand = sys.argv[1:6]
    NS = int(sys.argv[6]) if len(sys.argv) > 6 else 30
    seed = int(sys.argv[7]) if len(sys.argv) > 7 else 4
    N = json.load(open(netp))
    B = json.load(open(bndp))
    names = N["nodes"]
    idx = {n: i for i, n in enumerate(names)}
    gates = N["gates"]
    drv = {}
    for gi, g in enumerate(gates):
        drv[g["out"]] = gi
    X = XDB()
    # own INIT parse
    inits = defaultdict(int)
    for line in open(canon):
        t = line.split("#")[0].strip()
        m = re.match(r"^(\S+)\.(SLICE[LM]_X[01])\.([A-D])LUT\.INIT(?:\[(\d+)\])?$", t)
        if m:
            inits[(m.group(1), m.group(2), m.group(3))] |= 1 << int(m.group(4) or 0)
    RJ = json.load(open(routedp))["modules"]["top"]
    belcell = {}
    for cn, c in RJ["cells"].items():
        b = c["attributes"].get("NEXTPNR_BEL")
        if b:
            belcell[b] = (cn, c)
    bitdrv = {}
    for cn, c in RJ["cells"].items():
        for p, d in c["port_directions"].items():
            if d == "output":
                for b in c["connections"].get(p, []):
                    bitdrv[b] = (cn, c, p)
    bitnet = {}
    for n, v in RJ["netnames"].items():
        for b in v["bits"]:
            if b not in bitnet or n.startswith("$") is False:
                bitnet.setdefault(b, n)
    netrouting = {}
    for n, v in RJ["netnames"].items():
        if v["attributes"].get("ROUTING"):
            netrouting[v["bits"][0]] = v["attributes"]["ROUTING"]

    _pr = {}

    def parse_routing(r):
        if r in _pr:
            return _pr[r]
        _pr[r] = _parse_routing(r)
        return _pr[r]

    def _parse_routing(r):
        parts = r.split(";")
        pips, s2b = set(), {}
        for i in range(0, len(parts) - 2, 3):
            pip = parts[i + 1]
            if "->" not in pip:
                continue
            a, b = pip.split("->")
            if a.startswith("SITEWIRE") or a.startswith("SITEPIP"):
                continue
            ta, wa = a.split("/", 1)
            if b.startswith("SITEWIRE/"):
                _, site, pin = b.split("/")
                s2b[(ta, wa)] = (site, pin)         # tile wire -> BEL pin (site wire)
                continue
            tb, wb = b.split("/", 1)
            pips.add((cn_(ta, wa), cn_(tb, wb)))
        return pips, s2b

    def cn_(t, w):
        # nextpnr names every VCC/GND tie by one global wire; prjxray has one per tile
        if w in ("VCC_WIRE", "GND_WIRE"):
            return w
        return X.nname(t, w)

    def cnn(n):
        return n.split("/", 1)[1] if n.endswith("/VCC_WIRE") or n.endswith("/GND_WIRE") else n

    # kernel cone (own BFS, as in ctx.py)
    env = set(idx[x] for x in B["env"])
    bb = B["boundary"]
    outs = [idx[bb[k]] for k in ("a_ack", "b_ack", "start_ack", "out0_req")] + [idx[x] for x in bb["out0_data"]]
    seen, todo, cone = set(outs), list(outs), set()
    while todo:
        n = todo.pop()
        gi = drv.get(n)
        if gi is None or n in env:
            continue
        cone.add(gi)
        for i in gates[gi]["ins"]:
            if i not in seen and i not in env:
                seen.add(i)
                todo.append(i)
    cand = sorted({(g["name"].split(".")[0], g["name"].split(".")[1][0]) for gi, g in enumerate(gates)
                   if gi in cone and g["kind"] in ("lut6", "lut5")})
    g6 = {(g["name"].split(".")[0], g["name"].split(".")[1][0]): g for g in gates if g["kind"] == "lut6"}

    def kernel(site, L):
        cs = [belcell.get("%s/%s%dLUT" % (site, L, w)) for w in (6, 5)]
        return any(c and "udut" in c[0] for c in cs)

    cand = [x for x in cand if kernel(*x)]

    def site_map(site, L):
        """physical pin p (1..6) -> BEL pin name (e.g. 'A3'), from ROUTING of the nets on the LUT's BEL pins."""
        tile, sx, ts = X.slice_prefix(site)
        pmap = {}
        sw = set()
        for w in (6, 5):
            c = belcell.get("%s/%s%dLUT" % (site, L, w))
            if not c:
                continue
            for bp, bits in c[1]["connections"].items():
                if re.match(r"^[A-D][1-6]$", bp) and bits and bits[0] in netrouting:
                    _, s2b = parse_routing(netrouting[bits[0]])
                    for (tw, ww), (s, pin) in s2b.items():
                        # the net on cell port bp enters this LUT at tile wire ww (physical pin p)
                        if s == site and pin[0] == L and tw == tile:
                            m = [p for p in range(1, 7) if ts["site_pins"]["%s%d" % (L, p)]["wire"] == ww]
                            if m and (m[0] not in pmap or int(bp[1]) == m[0]):
                                pmap[m[0]] = bp
                            if m and pin[1:] != str(m[0]):
                                sw.add(m[0])     # nextpnr site wire index differs from the tile pin
        return pmap, sw

    perm = [x for x in cand if site_map(*x)[1]]
    rnd = random.Random(seed)
    pick = rnd.sample(perm, min(len(perm), NS // 3))
    rest = [x for x in cand if x not in pick]
    pick += rnd.sample(rest, NS - len(pick))
    LG = lean_gates(leand)
    print("spot: %d kernel-cone LUT sites (with a udut nextpnr cell), %d with permuted site pins; checking %d"
          % (len(cand), len(perm), len(pick)))
    allok = True
    rows = []
    for site, L in sorted(pick):
        tile, sx, ts = X.slice_prefix(site)
        g = g6[(site, L)]
        bits_init = inits.get((tile, sx, L), 0)
        lg = LG.get(g["name"])
        ok_a = (g["init"] == bits_init) and lg is not None and lg[1] == bits_init and \
            lg[2] == [names[i] for i in g["ins"]] and lg[3] == names[g["out"]]
        # decoded source of each physical pin
        def chain(n):
            pips = []
            while True:
                gi = drv.get(n)
                if gi is None:
                    return names[n], pips
                h = gates[gi]
                if h["kind"] in ("pip", "hop"):
                    if h["kind"] == "pip":
                        pips.append((names[h["ins"][0]], names[h["out"]], h["name"]))
                    n = h["ins"][0]
                elif h["kind"] == "const":
                    return "CONST%d" % h["init"], pips
                else:
                    return names[n], pips
        src = {}
        for p in range(1, 7):
            src[p] = chain(g["ins"][p - 1])
        # nextpnr view
        pmap, swp = site_map(site, L)
        cells = {w: belcell.get("%s/%s%dLUT" % (site, L, w)) for w in (6, 5)}
        exp_src = {}
        route_ok = True
        notes = []
        for p, bp in pmap.items():
            for w in (6, 5):
                c = cells[w]
                if not c or bp not in c[1]["connections"]:
                    continue
                b = c[1]["connections"][bp][0]
                d = bitdrv.get(b)
                if d is None:
                    e = "none"
                else:
                    cn, dc, port = d
                    bel = dc["attributes"].get("NEXTPNR_BEL", "")
                    s2, be = bel.split("/") if "/" in bel else ("", bel)
                    ty = dc["type"]
                    if ty == "SLICE_LUTX":
                        e = "%s.%s%s" % (s2, be[0], be[1])
                    elif ty == "SLICE_FFX":
                        e = "%s.%s%sQ" % (s2, be[0], "5" if be[1] == "5" else "")
                    elif ty == "CARRY4":
                        i = port[-1]
                        e = "%s.%s%s" % (s2, "CO" if port.startswith("CO") else "XOR", i)
                    elif ty == "SELMUX2_1":
                        e = "%s.%s" % (s2, {"F7AMUX": "F7A", "F7BMUX": "F7B", "F8MUX": "F8"}[be])
                    elif ty == "PSEUDO_VCC":
                        e = "CONST1"
                    elif ty == "PSEUDO_GND":
                        e = "CONST0"
                    else:
                        e = "%s:%s" % (ty, bel)
                exp_src[p] = e
                if b in netrouting:
                    npips, _ = parse_routing(netrouting[b])
                    for (s_, d_, nm) in src[p][1]:
                        if (cnn(s_), cnn(d_)) not in npips:
                            route_ok = False
                            notes.append("pin %d: decoded pip %s not in nextpnr net" % (p, nm))
        conn_ok = True
        for p in range(1, 7):
            got = src[p][0]
            if p in exp_src:
                e = exp_src[p]
                if e.startswith("CONST"):
                    good = got.startswith("CONST") and got[-1] == e[-1] or got.endswith("VCC_WIRE") and e == "CONST1" \
                        or got.endswith("GND_WIRE") and e == "CONST0"
                else:
                    good = got == e
                if not good:
                    conn_ok = False
                    notes.append("pin %d: decoded %s, nextpnr %s" % (p, got, e))
            else:
                # unconnected in nextpnr: the bits must tie it to a constant
                if not (got.startswith("CONST") or got.endswith("VCC_WIRE") or got.endswith("GND_WIRE")):
                    conn_ok = False
                    notes.append("pin %d: no nextpnr net, decoded %s" % (p, got))
        # expected physical function
        const_pin = {}
        for p in range(1, 7):
            got = src[p][0]
            if got.startswith("CONST"):
                const_pin[p] = int(got[-1])
            elif got.endswith("VCC_WIRE"):
                const_pin[p] = 1
            elif got.endswith("GND_WIRE"):
                const_pin[p] = 0
        fn_ok = True
        nchk = 0
        for a in range(64):
            if any(((a >> (p - 1)) & 1) != v for p, v in const_pin.items()):
                continue
            a6 = (a >> 5) & 1
            for w in ((6,) if a6 else (5, 6)):
                c = cells[w]
                if not c:
                    continue
                if w == 6 and not a6 and cells[5]:
                    continue            # fractured: lower half belongs to O5
                cc = c[1]
                linit = int(cc["parameters"]["INIT"], 2)
                la = 0
                for p in range(1, 7):
                    bp = pmap.get(p)
                    lin = cc["attributes"].get("X_ORIG_PORT_" + bp) if bp else None
                    for li in re.findall(r"I(\d)", lin or ""):   # "I3 I4" / "I3I4": two logical inputs on one pin
                        la |= ((a >> (p - 1)) & 1) << int(li)
                if w == 5 and a6:
                    continue
                want = (linit >> la) & 1
                if ((g["init"] >> a) & 1) != want:
                    fn_ok = False
                nchk += 1
                break
        ok = ok_a and fn_ok and conn_ok and route_ok
        allok &= ok
        permuted = bool(swp) or any(int(b[1]) != p for p, b in pmap.items())
        rows.append((site, L, tile, sx, "%016x" % g["init"], ok_a, fn_ok, nchk, conn_ok, route_ok, permuted,
                     {p: src[p][0] for p in range(1, 7)}, notes,
                     [cells[w][0][:60] if cells[w] else None for w in (6, 5)]))
        print("%s %s (%s.%s) INIT %016x  bits/Lean %s  fn %s (%d addr)  conn %s  route %s  permuted %s %s"
              % (site, L, tile, sx, g["init"], ok_a, fn_ok, nchk, conn_ok, route_ok, permuted, notes[:3]))
        print("    pins:", {p: src[p][0] for p in range(1, 7)}, " pmap:", pmap)
    print("spot: ALL OK" if allok else "spot: MISMATCHES")
    json.dump(rows, open("spot_out.json", "w"), indent=0)


if __name__ == "__main__":
    main()
