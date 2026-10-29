#!/usr/bin/env python3
"""audit r21: own re-computation of research's arbiter near-tie margin on a routed gcd_hw.
usage: arbmargin.py ROUTED_JSON XRAY_SDF
Reads all three SDF columns (0 FAST_MIN, 1 SLOW_MIN, 2 SLOW_MAX) and prints, per ack C-element:
  same-corner margins (col0, col2 with trp fixed, col2 with trp scaled by the LUT-arc ratio),
  and the race-correct bound: early side (RT, a, R0 branch of skew) at FAST_MIN,
  late side (GP, c, q branch of skew) at SLOW_MAX, trp 647 fixed.
Skew candidates: each request pin (r->R0 minus r->q) AND the runt path via the q feedback pin
(q -> LUT5 pin + O5 arc - (q -> LUT6 pin + O6 arc), the R0 rise caused by q's own runt with p -> TLOOP).
RT: Dijkstra from R0 over wires+arcs; C(g,A0) of other arbiters and FASTFALL LUT2-AND links need both
inputs (research's rule, re-implemented); --naive drops it.
"""
import sys, re, json, heapq, collections
TRP = 647
naive = "--naive" in sys.argv
J, S = [a for a in sys.argv[1:] if not a.startswith("--")]
cells = json.load(open(J))["modules"]["top"]["cells"]
IC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)")
IN = re.compile(r"\(INSTANCE\s+(\S*?)\)")
IO = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)")
W, A = {}, {}          # (src,dst)->(c0,c1,c2) ; (inst,in,out)->(c0,c1,c2)
inst = None
for ln in open(S):
    m = IC.search(ln)
    if m:
        s, d = m.group(1).replace("\\", ""), m.group(2).replace("\\", "")
        if "$PACKER_GND" in s or "$PACKER_VCC" in s: continue
        W[(s, d)] = tuple(int(m.group(i)) for i in (3, 4, 5)); continue
    m = IN.search(ln)
    if m: inst = m.group(1).replace("\\", ""); continue
    m = IO.search(ln)
    if m and inst: A[(inst, m.group(1), m.group(2))] = tuple(int(m.group(i)) for i in (3, 4, 5))
wsrc = collections.defaultdict(list)
for (s, d) in W: wsrc[d].append(s)

def lpin(c, lg):
    for k, v in cells[c]["attributes"].items():
        if k.startswith("X_ORIG_PORT_A") and lg in v.split(): return k[len("X_ORIG_PORT_"):]
    raise KeyError((c, lg))
def pins_on(c, net):
    return [p for p, b in cells[c]["connections"].items() if b == [net] and p.startswith("A")]
def w(s, d, col): return W[(s, d)][col]
def a(c, i, o, col): return A[(c, i, o)][col]

# graph at column 0 for RT
adj = collections.defaultdict(list)
for (s, d), v in W.items(): adj[s].append((d, v[0]))
for (c, i, o), v in A.items(): adj[c + "/" + i].append((c + "/" + o, v[0]))
dsts = set(d for (s, d) in W)
arbs = sorted(c[:-12] for c in cells if c.endswith(".ustate$LUT6"))
both = {}
for p in arbs:
    st6 = p + ".ustate$LUT6"; a0n = cells[st6]["connections"][lpin(st6, "I4")][0]
    for k, (gc, go) in ((1, (p + ".ugrant$LUT5", "O5")), (2, (p + ".ugrant$LUT6", "O6"))):
        u = p + ".ua%d.u" % k; gn = cells[gc]["connections"][go][0]
        both[u + "/O6"] = (p, [u + "/" + x for x in pins_on(u, a0n) + pins_on(u, gn)])
for n, c in cells.items():
    if c["type"] == "SLICE_LUTX" and c["attributes"].get("X_ORIG_TYPE") == "LUT2" and \
            str(c["parameters"].get("INIT", "")).lstrip("0") == "1000":
        o = "O6" if c["connections"].get("O6") else "O5"
        ins = [n + "/" + q for q, b in c["connections"].items() if q.startswith("A") and b and n + "/" + q in dsts]
        if len(ins) == 2: both[n + "/" + o] = (None, ins)

def rt(src, tgt, own):
    cn = {} if naive else {o: v[1] for o, v in both.items() if v[0] != own}
    need = collections.defaultdict(list)
    for o, ins in cn.items():
        for i in ins: need[i].append(o)
    got = collections.defaultdict(dict); dist = {src: 0}; pq = [(0, src)]
    while pq:
        d, x = heapq.heappop(pq)
        if d > dist[x]: continue
        if x == tgt: return d
        for o in need.get(x, ()):
            c = o.rsplit("/", 1)[0]
            got[o][x] = d + A.get((c, x.rsplit("/", 1)[1], "O6"), (0,))[0]
            if len(got[o]) == len(cn[o]):
                t = max(got[o].values())
                if t < dist.get(o, 1e18): dist[o] = t; heapq.heappush(pq, (t, o))
        for y, wt in adj.get(x, ()):
            if y in cn: continue
            if d + wt < dist.get(y, 1e18): dist[y] = d + wt; heapq.heappush(pq, (d + wt, y))
    return None

rows = []
for p in arbs:
    st6, st5, g6, g5 = p + ".ustate$LUT6", p + ".ustate$LUT5", p + ".ugrant$LUT6", p + ".ugrant$LUT5"
    a0n = cells[st6]["connections"][lpin(st6, "I4")][0]
    R0 = st5 + "/O5"
    # skew branches: (R0 side, q side) per column
    br = []
    for lg in ("I0", "I1"):
        p6, p5 = lpin(st6, lg), lpin(st5, lg)
        s = wsrc[st6 + "/" + p6][0]
        br.append(("req" + lg, lambda col, s=s, p6=p6, p5=p5: w(s, st5 + "/" + p5, col) + a(st5, p5, "O5", col),
                   lambda col, s=s, p6=p6: w(s, st6 + "/" + p6, col) + a(st6, p6, "O6", col)))
    fb6 = [d for (s, d) in W if s == st6 + "/O6" and d.startswith(st6 + "/")]
    fb5 = [d for (s, d) in W if s == st6 + "/O6" and d.startswith(st5 + "/")]
    if fb6 and fb5:
        f6, f5 = fb6[0].split("/")[-1], fb5[0].split("/")[-1]
        # R0 rise from q's own runt start, relative to the runt end p = TLOOP - 1 (worst):
        # R0 lag = [w(q->f5) + arc5] - p, p < TLOOP = w(q->f6) + arc6(f6)
        br.append(("runt", lambda col, f5=f5: w(st6 + "/O6", st5 + "/" + f5, col) + a(st5, f5, "O5", col) + 1,
                   lambda col, f6=f6: w(st6 + "/O6", st6 + "/" + f6, col) + a(st6, f6, "O6", col)))
    for k, (gc, go) in ((1, (g5, "O5")), (2, (g6, "O6"))):
        u = p + ".ua%d.u" % k; gn = cells[gc]["connections"][go][0]
        ap, gp = pins_on(u, a0n)[0], pins_on(u, gn)[0]
        qp = lpin(gc, "I2")
        GP = lambda col: w(st6 + "/O6", gc + "/" + qp, col) + a(gc, qp, go, col) + w(gc + "/" + go, u + "/" + gp, col)
        c = lambda col: a(u, gp, "O6", col)
        ak = lambda col: a(u, ap, "O6", col)
        RT = rt(R0, u + "/" + ap, p)
        sk_req0 = min(e(0) - l(0) for n, e, l in br if n != "runt")
        sk_all0 = min(e(0) - l(0) for n, e, l in br)
        sk_mix = min(e(0) - l(2) for n, e, l in br)
        sk2 = min(e(2) - l(2) for n, e, l in br if n != "runt")
        m0 = RT + ak(0) + sk_req0 - TRP - GP(0) - c(0)              # research's number
        m0r = RT + ak(0) + sk_all0 - TRP - GP(0) - c(0)             # + runt skew branch
        ratio = a(u, gp, "O6", 2) / max(1, a(u, gp, "O6", 0))
        mmix = RT + ak(0) + sk_mix - TRP - GP(2) - c(2)             # race-correct mixed corner
        mmix_s = RT + ak(0) + sk_mix - TRP * ratio - GP(2) - c(2)   # + trp scaled to slow LUT
        rows.append((p.replace("urig.udut.", ""), k, RT, ak(0), GP(0), GP(2), c(0), c(2), sk_req0, sk_all0, sk_mix,
                     m0, m0r, mmix, mmix_s, ratio))
print("mode:", "naive" if naive else "max-rule", " trp", TRP)
print("%-26s k %6s %4s %5s %5s %4s %4s %5s %5s %5s | %6s %6s %7s %8s" % (
    "arbiter", "RT0", "a0", "GP0", "GP2", "c0", "c2", "sk0", "sk0r", "skmx", "m0", "m0runt", "m_mixed", "mix+trpS"))
for r in rows:
    print("%-26s %d %6d %4d %5d %5d %4d %4d %5d %5d %5d | %6d %6d %7d %8.0f  (LUT ratio %.2f)" % r)
for i, name in ((11, "same-corner FAST_MIN (research)"), (12, "FAST_MIN + runt skew"), (13, "mixed corner"),
                (14, "mixed + trp scaled")):
    worst = min(rows, key=lambda r: r[i])
    print("worst %-32s %6.0f  %s ua%d ; below 0: %d of %d" % (name, worst[i], worst[0], worst[1],
          sum(r[i] < 0 for r in rows), len(rows)))

# ---- OCV-style derate tolerance (shared request wire cancels: r -> LUT6 pin and LUT5 pin are one physical pin)
print("\nwire r->LUT6 pin == r->LUT5 pin in SDF for every arbiter:", all(
    W[(wsrc[p + ".ustate$LUT6/" + lpin(p + ".ustate$LUT6", lg)][0], p + ".ustate$LUT6/" + lpin(p + ".ustate$LUT6", lg))] ==
    W[(wsrc[p + ".ustate$LUT6/" + lpin(p + ".ustate$LUT6", lg)][0], p + ".ustate$LUT5/" + lpin(p + ".ustate$LUT5", lg))]
    for p in arbs for lg in ("I0", "I1")))
print("break-even derate d: early*(1-d) - late*(1+d) - trp = 0 (early = RT+a+arc5, late = GP+c+arc6, arcs on the req pin)")
for col, trps in ((0, False), (2, False), (2, True)):
    res = []
    for p in arbs:
        st6, st5 = p + ".ustate$LUT6", p + ".ustate$LUT5"
        a0n = cells[st6]["connections"][lpin(st6, "I4")][0]
        for k, (gc, go) in ((1, (p + ".ugrant$LUT5", "O5")), (2, (p + ".ugrant$LUT6", "O6"))):
            u = p + ".ua%d.u" % k; gn = cells[gc]["connections"][go][0]
            ap, gp = pins_on(u, a0n)[0], pins_on(u, gn)[0]; qp = lpin(gc, "I2")
            if col == 0: RTc = rt(p + ".ustate$LUT5/O5", u + "/" + ap, p)
            else:
                adj.clear()
                for (s, d), v in W.items(): adj[s].append((d, v[col]))
                for (c, i, o), v in A.items(): adj[c + "/" + i].append((c + "/" + o, v[col]))
                RTc = rt(p + ".ustate$LUT5/O5", u + "/" + ap, p)
                adj.clear()
                for (s, d), v in W.items(): adj[s].append((d, v[0]))
                for (c, i, o), v in A.items(): adj[c + "/" + i].append((c + "/" + o, v[0]))
            best = None
            for lg in ("I0", "I1"):
                p6, p5 = lpin(st6, lg), lpin(st5, lg)
                E = RTc + a(u, ap, "O6", col) + a(st5, p5, "O5", col)
                L = (w(st6 + "/O6", gc + "/" + qp, col) + a(gc, qp, go, col) + w(gc + "/" + go, u + "/" + gp, col)
                     + a(u, gp, "O6", col) + a(st6, p6, "O6", col))
                t = TRP * (a(u, gp, "O6", 2) / a(u, gp, "O6", 0) if trps else 1)
                d = (E - L - t) / (E + L)
                best = d if best is None else min(best, d)
            res.append((best, p.replace("urig.udut.", ""), k))
    res.sort()
    print("col %d trp %s: worst break-even derate %.1f%% (%s ua%d); next %s" % (
        col, "scaled" if trps else "647", 100 * res[0][0], res[0][1], res[0][2],
        ", ".join("%.1f%% %s ua%d" % (100 * r[0], r[1], r[2]) for r in res[1:4])))

# ---- mixed corner with the shared request wire cancelled (physically one pin)
out = []
for p in arbs:
    st6, st5 = p + ".ustate$LUT6", p + ".ustate$LUT5"
    a0n = cells[st6]["connections"][lpin(st6, "I4")][0]
    skx = min(a(st5, lpin(st5, lg), "O5", 0) - a(st6, lpin(st6, lg), "O6", 2) for lg in ("I0", "I1"))
    for k, (gc, go) in ((1, (p + ".ugrant$LUT5", "O5")), (2, (p + ".ugrant$LUT6", "O6"))):
        u = p + ".ua%d.u" % k; gn = cells[gc]["connections"][go][0]
        ap, gp = pins_on(u, a0n)[0], pins_on(u, gn)[0]; qp = lpin(gc, "I2")
        RTc = rt(p + ".ustate$LUT5/O5", u + "/" + ap, p)
        GP2 = w(st6 + "/O6", gc + "/" + qp, 2) + a(gc, qp, go, 2) + w(gc + "/" + go, u + "/" + gp, 2)
        m = RTc + a(u, ap, "O6", 0) + skx - TRP - GP2 - a(u, gp, "O6", 2)
        out.append((m, p.replace("urig.udut.", ""), k))
out.sort()
print("mixed corner, wire-cancelled skew: worst %.0f (%s ua%d); below 0: %d of %d; next %s" % (
    out[0][0], out[0][1], out[0][2], sum(o[0] < 0 for o in out), len(out),
    ", ".join("%.0f %s ua%d" % o for o in out[1:4])))
