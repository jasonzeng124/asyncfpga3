#!/usr/bin/env python3
"""ctx.py (audit T4): context for the round-trip leftovers (auditor's own code; no formal/ import).

    python3 -I ctx.py NET.json BND.json CANON_READBACK.fasm ROUTED.json

1. unused-CARRY4 leftovers: no read-back feature of such a slice selects XOR/CY, and no active pip
   leaves its COUT.
2. the leftover DOUTMUX.O6: does any active pip read that slice's DMUX node? what does nextpnr place there?
3. FF config leftovers: which FFs (free output nodes in the decoded net) lie in the kernel cone
   (cone of a_ack, b_ack, start_ack, out0_req, out0_data, cut at the env nodes), and what the routed
   JSON says they are.
4. other free (undriven, non-env) nodes in the kernel cone.
"""
import json
import os
import re
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xnode import XDB  # noqa: E402


def main():
    netp, bndp, canon, routedp = sys.argv[1:5]
    N = json.load(open(netp))
    B = json.load(open(bndp))
    names = N["nodes"]
    idx = {n: i for i, n in enumerate(names)}
    R = set(l.split("#")[0].strip() for l in open(canon)) - {""}
    X = XDB()
    gates = N["gates"]
    carry_sites = {g["name"].split(".")[0] for g in gates if g["kind"] == "carry"}

    # 1. unused carries
    pre_site = {}
    for g in X.grid.values():
        pass
    sf = defaultdict(set)
    for f in R:
        p = f.split(".")
        if len(p) >= 3 and re.match(r"SLICE[LM]_X[01]$", p[1]):
            sf["%s.%s" % (p[0], p[1])].add(".".join(p[2:]))
    site_of_pre = {}
    for s, (t, st) in X.site_tile.items():
        if st.startswith("SLICE"):
            tile, sx, _ = X.slice_prefix(s)
            site_of_pre["%s.%s" % (tile, sx)] = s
    bad1 = []
    nunused = 0
    rpips_by_src = defaultdict(list)
    for f in R:
        p = f.split(".")
        if len(p) == 3 and p[0] in X.grid and (p[1], p[2]) in X.tt(X.ttype(p[0]))["_pip"]:
            rpips_by_src[X.nname(p[0], p[2])].append(f)
    for pre, fs in sf.items():
        site = site_of_pre[pre]
        if site in carry_sites:
            continue
        if "PRECYINIT.C0" in fs:
            nunused += 1
        if any(re.search(r"(FFMUX\.(XOR|CY)|OUTMUX\.(XOR|CY)|CARRY4|PRECYINIT\.(AX|C1|CIN))", x) for x in fs):
            bad1.append((pre, sorted(fs)))
        tile, sx, ts = X.slice_prefix(site)
        cout = X.nname(tile, ts["site_pins"]["COUT"]["wire"])
        if rpips_by_src.get(cout):
            bad1.append((pre, "COUT read by " + str(rpips_by_src[cout][:3])))
    print("1. slices with no decoded CARRY4: %d with PRECYINIT.C0; problems: %d %s" % (nunused, len(bad1), bad1[:5]))

    # 2. DOUTMUX.O6 leftover
    tile = "CLBLM_L_X20Y86"
    site = site_of_pre[tile + ".SLICEL_X1"]
    _, _, ts = X.slice_prefix(site)
    dm = X.nname(tile, ts["site_pins"]["DMUX"]["wire"])
    print("2. %s.SLICEL_X1 = %s; DMUX node %s; active pips reading it: %s; node in decoded net: %s"
          % (tile, site, dm, rpips_by_src.get(dm), dm in idx))
    print("   slice features:", sorted(sf[tile + ".SLICEL_X1"]))
    RJ = json.load(open(routedp))["modules"]["top"]
    for cn, c in RJ["cells"].items():
        bel = c["attributes"].get("NEXTPNR_BEL", "")
        if bel.startswith(site + "/D") or bel.startswith(site + "/F"):
            outs = {p: c["connections"][p] for p, d in c["port_directions"].items() if d == "output"}
            print("   nextpnr cell at %s: %s %s outs %s" % (bel, cn, c["type"], outs))
    bitname = {}
    for n, v in RJ["netnames"].items():
        for b in v["bits"]:
            bitname.setdefault(b, n)
    # 3/4. kernel cone
    env = set(idx[x] for x in B["env"])
    bb = B["boundary"]
    drv = {}
    for gi, g in enumerate(gates):
        if g["out"] not in env:
            drv[g["out"]] = gi
    outs = [idx[bb[k]] for k in ("a_ack", "b_ack", "start_ack", "out0_req")] + [idx[x] for x in bb["out0_data"]]
    seen = set(outs)
    todo = list(outs)
    cone = set()
    free = set()
    while todo:
        n = todo.pop()
        gi = drv.get(n)
        if gi is None:
            if n not in env:
                free.add(n)
            continue
        cone.add(gi)
        for i in gates[gi]["ins"]:
            if i not in seen and i not in env:
                seen.add(i)
                todo.append(i)
    print("3. kernel cone: %d gates, %d nodes; free (undriven, non-env) nodes in cone: %d" % (len(cone), len(seen), len(free)))
    fc = Counter()
    ffs = []
    for n in sorted(free, key=lambda n: names[n]):
        nm = names[n]
        m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])(5?)Q$", nm)
        if m:
            fc["FF Q"] += 1
            ffs.append(nm)
        else:
            fc[re.sub(r"\d+", "#", nm)] += 1
    print("   free node kinds:", dict(fc))
    # what are these FFs in nextpnr
    belcell = {}
    for cn, c in RJ["cells"].items():
        belcell[c["attributes"].get("NEXTPNR_BEL", "")] = (cn, c)
    kinds = Counter()
    for nm in ffs:
        m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])(5?)Q$", nm)
        bel = "%s/%s%sFF" % (m.group(1), m.group(2), m.group(3))
        cn, c = belcell.get(bel, ("?", {}))
        kinds[re.sub(r"\[\d+\]", "[]", cn.split("$")[0])[:70]] += 1
    print("   cone FFs by nextpnr cell name (first 40):")
    for k, v in kinds.most_common(40):
        print("     %4d  %s" % (v, k))
    print("   example cone FFs:", ffs[:10])
    # FF cells overall in routed json
    allff = Counter(re.sub(r"\[\d+\]", "[]", cn.split("$")[0])[:70] for cn, c in RJ["cells"].items() if c["type"] == "SLICE_FFX")
    print("   all %d FF cells by name:" % sum(allff.values()))
    for k, v in allff.most_common(30):
        print("     %4d  %s" % (v, k))
    json.dump({"cone_gates": len(cone), "free_in_cone": [names[n] for n in sorted(free)], "cone_ffs": ffs},
              open("ctx_out.json", "w"), indent=0)


if __name__ == "__main__":
    main()
