#!/usr/bin/env python3
"""margin/bram/hostrace.py MEMTASK_OUT [--array a] [--band b] (shard C, UNTRUSTED static path sums): the host-write race of a
memory route in picoseconds (PROGRAM "the race in picoseconds"). The host's request flop (<array>_host_req) launches both
sides of each RAM's setup check (research's ifloop.md): the RAM CLOCK (m_req -> DSETUP line -> ubuf -> CLKARDCLK) and the
PAYLOAD it gates (m_we -> WEA, m_addr -> ADDR, m_wdata -> DIADI). For every RAM of that port, the latest and earliest
arrival of the request's edge at each pin, through the decoded netlist (decoded arcs, every arc at FAST_MIN + b (SLOW_MAX
- FAST_MIN), b = --band, default 0.255 = the middle of research's U[.20, .31]; cells (CARRY4 / F7 / F8) at --xband, default
0.6), no scatter: setup slack = earliest clock arrival - latest payload arrival - prjxray's widest setup; the two paths
named LUT by LUT (routed yosys instance), cells and routing apart. A static bound on the paths, not a simulation: it
ignores which path a given edge really takes (a LUT the edge does not toggle still counts)."""
import argparse, heapq, json, os, re, sys
ap = argparse.ArgumentParser(); ap.add_argument("out"); ap.add_argument("--array", default=None)
ap.add_argument("--band", type=float, default=0.255); ap.add_argument("--xband", type=float, default=0.6)
a = ap.parse_args()
M = os.path.join(os.path.abspath(a.out), "w", "m")
N = json.load(open(os.path.join(M, "net.json"))); BJ = json.load(open(os.path.join(M, "bnd.json")))["boundary"]
cells = json.load(open(os.path.join(M, "routed.json")))["modules"]["top"]["cells"]
bel = {c["attributes"].get("NEXTPNR_BEL"): n for n, c in cells.items() if c.get("attributes", {}).get("NEXTPNR_BEL")}
names = N["nodes"]; G = N["gates"]; idx = {n: i for i, n in enumerate(names)}
def cname(nd):
    m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])(?:LUT\.O)?([56])$", nd)
    return bel.get("%s/%s%sLUT" % m.groups(), nd) if m else nd
hosts = BJ.get("hosts", [])
if a.array: hosts = [h for h in hosts if h["name"] == a.array]
if not hosts: sys.exit("hostrace: no host port")
rd = {}
for gi, g in enumerate(G):
    for p, i in enumerate(g["ins"]): rd.setdefault(i, []).append((gi, p))
def arc(g, p):
    e = g["arcs"][p]; b = a.xband if g["kind"] in ("carry", "muxf", "ram") else a.band
    return e["fmin"] + b * (e["smax"] - e["fmin"])
def selfloop(gi):   # a storage LUT (reads its own output through copies): the edge stops there
    g = G[gi]; out = g["out"]
    if not g["kind"].startswith("lut"): return False
    for i in g["ins"]:
        u = i
        for _ in range(300):
            if u == out: return True
            d = drvo.get(u)
            if d is None or G[d]["kind"].startswith("lut") or G[d]["k"] != 1: break
            u = G[d]["ins"][0]
    return False
drvo = {g["out"]: gi for gi, g in enumerate(G)}
def sweep(src, longest):
    """earliest (or latest) arrival from src's edge at every node reachable through non-storage gates, with the path."""
    best = {src: (0.0, None)}
    order = [src]; seen = {src}
    # topological-ish relaxation (Bellman-Ford limited): the cone of a request is acyclic once storage LUTs are cut
    frontier = [src]
    for _ in range(4000):
        nxt = []
        for n in frontier:
            for gi, p in rd.get(n, []):
                g = G[gi]
                if g["kind"] == "ram" or selfloop(gi): continue
                t = best[n][0] + arc(g, p); o = g["out"]
                if o not in best or (t > best[o][0] if longest else t < best[o][0]):
                    best[o] = (t, (n, gi)); nxt.append(o)
        if not nxt: break
        frontier = list(set(nxt))
    return best
def path(best, n):
    out = []
    while best[n][1] is not None:
        prev, gi = best[n][1]; g = G[gi]
        out.append((names[g["out"]], g["kind"], best[n][0] - best[prev][0])); n = prev
    return list(reversed(out))
SU = {"ADDR": 566, "WE": 532, "DI": 737}
for h in hosts:
    src = idx[h["req"]]
    lo, hi = sweep(src, False), sweep(src, True)
    for gi, g in enumerate(G):
        if g["kind"] != "ram" or g["ram"]["obit"] != min(x["ram"]["obit"] for x in G if x["kind"] == "ram" and x["ram"]["id"] == g["ram"]["id"]): continue
        r = g["ram"]; roles = r["roles"]
        clkn = g["ins"][roles.index(1)]; dclk = arc(g, roles.index(1))
        if clkn not in lo: continue
        tclk = lo[clkn][0] + dclk
        rows = []
        for cls, rr in (("WE", (2, 3)), ("ADDR", range(16, 26)), ("DI", range(32, 48))):
            for ro in rr:
                if ro not in roles: continue
                n = g["ins"][roles.index(ro)]
                if n not in hi: continue
                tp = hi[n][0] + arc(g, roles.index(ro))
                rows.append((tclk - tp - SU[cls], cls, ro, n, tp))
        if not rows: continue
        rows.sort()
        sl, cls, ro, n, tp = rows[0]
        print("%s %s (%s): host request %s -> CLKARDCLK earliest %.0f ps; worst payload %s pin role %d latest %.0f ps; setup %d -> slack %+.0f ps  [band %.3f, cells %.2f]"
              % (h["name"], r["site"], r.get("json_cell"), cname(names[src]), tclk, cls, ro, tp, SU[cls], sl, a.band, a.xband))
        for lab, b, nn in (("clock", lo, clkn), ("payload", hi, n)):
            pp = path(b, nn)
            luts = [(cname(x[0]), x[2]) for x in pp if x[1].startswith("lut")]
            route = sum(x[2] for x in pp if not x[1].startswith("lut")); cell = sum(x[2] for x in pp if x[1].startswith("lut"))
            print("   %s path: %d LUTs %.0f ps + routing %.0f ps: %s" % (lab, len(luts), cell, route, " -> ".join("%s(%.0f)" % l for l in luts)))
