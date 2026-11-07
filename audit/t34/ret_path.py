#!/usr/bin/env python3
"""Independent return-path / loop calculator (auditor's own, not research's ce_return.py).

usage: ret_path.py ROUTED_JSON SDF [--col 0]   (col 0 = first number of each triple = FAST_MIN in xray SDF)

Graph: SDF INTERCONNECT arcs (src pin -> dst pin) + IOPATH arcs (cell/in -> cell/out), except arcs out of CK.
Extra arc: req_core flop SR -> Q = 0 ps (prjxray has none). Optionally (--all-ff-sr) SR->Q=0 on every SLICE_FFX.
Source: O6 of the kernel's ufork0 C-element LUT (it drives start_ack).
Reports: Dijkstra min arrival at (a) every sink pin of the bench net i_req_pl inside the kernel (= start_req pins),
(b) every ufork0 data pin, + IOPATH(pin->O6); hop-by-hop breakdown; ufork0 loop = IOPATH(fb->O6)+IC(O6->fb).
"""
import json, re, sys, heapq, argparse
from collections import defaultdict

ap = argparse.ArgumentParser()
ap.add_argument("routed"); ap.add_argument("sdf")
ap.add_argument("--col", type=int, default=0)
ap.add_argument("--rc-line", default="179")
ap.add_argument("--all-ff-sr", action="store_true")
ap.add_argument("--keep-ck", action="store_true", help="keep CK->Q arcs (global clock still cut at BUFGCTRL)")
ap.add_argument("--allowed-only", action="store_true",
                help="restrict walk to the named chain cells (ufork0 LUT, bench ufork LUT, req_clr LUT, req_core FF, upsnk)")
a = ap.parse_args()
RC_LINE = a.rc_line

# ---------------- SDF (own parser) ----------------
txt = open(a.sdf).read()
ic = {}                       # dst -> (src, d)
io = defaultdict(dict)        # cell -> {(i,o): d}
ctype = {}
trip = r"\(\s*([-\d.]*)\s*:\s*([-\d.]*)\s*:\s*([-\d.]*)\s*\)"
cur = None
for blk in re.split(r"\(CELL\b", txt)[1:]:
    m = re.search(r'\(CELLTYPE\s+"([^"]+)"\)', blk); ct = m.group(1) if m else None
    m = re.search(r"\(INSTANCE\s*([^)]*)\)", blk); inst = m.group(1).strip().replace("\\", "") if m else ""
    ctype[inst] = ct
    for m in re.finditer(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+" + trip, blk):
        s, d = m.group(1).replace("\\", ""), m.group(2).replace("\\", "")
        v = float(m.group(3 + a.col))
        if d in ic and ic[d][0] != s:
            print("WARN two drivers for", d, file=sys.stderr)
        ic[d] = (s, v)
    for m in re.finditer(r"\(IOPATH\s+(\S+)\s+(\S+)\s+" + trip, blk):
        io[inst][(m.group(1), m.group(2))] = float(m.group(3 + a.col))

# ---------------- routed JSON ----------------
J = json.load(open(a.routed))
mods = J["modules"]; top = mods[[k for k in mods if "cells" in mods[k] and len(mods[k]["cells"]) > 100][0]]
cells = top["cells"]
netname = {}
for n, v in top["netnames"].items():
    for b in v["bits"]:
        if b not in netname or len(n) < len(netname[b]):
            netname[b] = n
names_of = defaultdict(list)
for n, v in top["netnames"].items():
    for b in v["bits"]:
        names_of[b].append(n)
drv, snk = {}, defaultdict(list)
for cn, c in cells.items():
    for p, bl in c["connections"].items():
        if not bl or isinstance(bl[0], str):
            continue
        if c["port_directions"].get(p) == "output":
            drv[bl[0]] = (cn, p)
        else:
            snk[bl[0]].append((cn, p))

def bit_of(name):
    v = top["netnames"].get(name)
    return v["bits"][0] if v else None

# locate cells
uf0 = [cn for cn in cells if re.search(r"udut\.ufork0\.", cn) and cells[cn]["type"] == "SLICE_LUTX"]
ufb = [cn for cn in cells if re.match(r"bridge_i\.ufork\.", cn) and cells[cn]["type"] == "SLICE_LUTX"]
# req_core: yosys renames it; identify it by its source line (gen_bench's `always @(posedge aclk or posedge req_clr)`)
rc = [cn for cn in cells if cells[cn]["type"] == "SLICE_FFX" and re.search(r"isprime_bench_gen\.v:%s\." % RC_LINE, cells[cn]["attributes"].get("src", ""))]
print("ufork0 LUTs:", uf0); print("bench ufork LUTs:", ufb); print("req_core FFs:", rc)
assert len(uf0) == 1 and len(rc) == 1
U0 = uf0[0]; RC = rc[0]
c0 = cells[U0]
q0 = c0["connections"]["O6"][0]
print("ufork0 O6 net names:", names_of[q0])
fb = [p for p, b in c0["connections"].items() if p.startswith("A") and b and b[0] == q0]
print("ufork0 feedback pin(s):", fb, " INIT", c0["parameters"].get("INIT"))
for p, b in sorted(c0["connections"].items()):
    print("   %s %s <- %s  (%s)" % (p, c0["attributes"].get("X_ORIG_PORT_" + p, ""), names_of.get(b[0], [b[0]])[:3] if b else "",
                                   drv.get(b[0]) if b else ""))
# i_req_pl net = req_core Q
qrc = cells[RC]["connections"]["Q"][0]
print("req_core Q net names:", names_of[qrc][:8])
sr=cells[RC]["connections"]["SR"][0]; d=drv.get(sr); print("req_clr LUT:", d, cells[d[0]]["parameters"].get("INIT"), {p:(cells[d[0]]["attributes"].get("X_ORIG_PORT_"+p), names_of[b[0]][:2]) for p,b in cells[d[0]]["connections"].items() if b})
print("req_core FF:", RC, cells[RC]["attributes"].get("src"), cells[RC]["attributes"].get("NEXTPNR_BEL"), {p: names_of[b[0]][:2] for p,b in cells[RC]["connections"].items() if b})
print("req_core SR net:", names_of[cells[RC]["connections"]["SR"][0]][:5], "driver", drv.get(cells[RC]["connections"]["SR"][0]))
start_sinks = [(cn, p) for cn, p in snk[qrc]]
print("i_req_pl sinks (%d):" % len(start_sinks))
for s in start_sinks:
    print("   ", s, cells[s[0]]["type"])

# ---------------- graph ----------------
adj = defaultdict(list)
for d, (s, v) in ic.items():
    adj[s].append((d, v, "IC"))
for cell, arcs in io.items():
    if ctype.get(cell) in ("BUFGCTRL", "BSCAN"):
        continue
    for (i, o), v in arcs.items():
        if i in ("CK", "CLK") and not a.keep_ck:
            continue
        adj[cell + "/" + i].append((cell + "/" + o, v, "IOPATH"))
srff = [cn for cn, c in cells.items() if c["type"] == "SLICE_FFX" and c["connections"].get("SR")] if a.all_ff_sr else [RC]
for cn in srff:
    adj[cn + "/SR"].append((cn + "/Q", 0.0, "SR->Q(assumed 0)"))
# sanity: does SDF have any arc for req_core?
print("SDF IOPATHs on req_core:", io.get(RC))

src = U0 + "/O6"
targets = {s[0] + "/" + s[1] for s in start_sinks}
data_pins = [p for p, b in c0["connections"].items() if p.startswith("A") and b and b[0] != q0
             and (p, "O6") in io.get(U0, {})]
dist, pred = {src: 0.0}, {}
pq = [(0.0, src)]
while pq:
    d, u = heapq.heappop(pq)
    if d > dist[u] or d > 20000:
        continue
    if u.startswith(U0 + "/") and u != src:
        continue                               # do not pass back through ufork0 itself
    for v, w, k in adj.get(u, ()):
        if dist.get(v, 1e18) > d + w:
            dist[v] = d + w; pred[v] = (u, w, k); heapq.heappush(pq, (d + w, v))

def trace(t):
    out = []
    x = t
    while x != src:
        u, w, k = pred[x]; out.append((u, x, w, k)); x = u
    return out[::-1]

def show(t):
    for u, v, w, k in trace(t):
        print("   %-8s %7.0f  %s -> %s" % (k, w, u, v))

print("\n== arrival at start_req (i_req_pl) sink pins inside the kernel ==")
best = None
for t in sorted(targets, key=lambda t: dist.get(t, 1e18)):
    print("  %s : %s" % (t, dist.get(t)))
    if best is None and t in dist:
        best = t
print("MIN to a start_req pin:", dist.get(best), best); show(best)
print("\n== full return to ufork0 data pins ==")
loop = io[U0][(fb[0], "O6")] + ic[U0 + "/" + fb[0]][1]
print("ufork0 LOOP = IOPATH(%s->O6) %.0f + IC(O6->%s) %.0f = %.0f" % (fb[0], io[U0][(fb[0], "O6")], fb[0], ic[U0 + "/" + fb[0]][1], loop))
print("   IC O6->fb src:", ic[U0 + "/" + fb[0]][0])
for p in data_pins:
    t = U0 + "/" + p
    if t in dist:
        r = dist[t] + io[U0][(p, "O6")]
        print("pin %s (%s): arrival %.0f + IOPATH %.0f = return %.0f  margin %.0f" % (
            p, names_of[c0["connections"][p][0]][:2], dist[t], io[U0][(p, "O6")], r, r - loop))
        show(t)
    else:
        print("pin %s unreachable" % p)
