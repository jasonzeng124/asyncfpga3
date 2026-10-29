#!/usr/bin/env python3
"""arb_roundtrip.py -- static check of every bd_arbiter in a routed design
against the near-tie requirement of research/data/fid/arbtie.md.

    python3 -I arb_roundtrip.py ROUTED_JSON SDF [--col 0|1|2] [--scale F]

The requirement (fid model, confirmed by tb_f3_arbtie to < 10 ps):
for each ack C-element ua_k (k = 1, 2), the server's acknowledge must reach
ua_k after the grant g_k has settled following the latest possible commit of
q, i.e.

    RT_k + a_k  >=  trp_max + GP_k + c_k - skew

  RT_k    R0 output (ustate O5) -> A0 at ua_k's pin: the server round trip
  a_k     ua_k's arc from that A0 pin
  GP_k    q (ustate O6) -> ugrant pin -> g_k output -> ua_k's g pin
  c_k     ua_k's arc from the g pin
  skew    R0's lag behind q for the same request edge
          (min over r1, r2 of [wire + O5 arc] - [wire + O6 arc])
  trp_max TAU ln(WIN/2) = 647 ps at TAU = WIN = 150 (the model's ceiling;
          silicon has none: the slack only buys exp(-slack/TAU) per event)

RT_k is a STATIC SHORTEST PATH over every routed wire and every annotated
cell arc (Dijkstra, no sensitisation), except that the ack C-elements
C(g, A0) of the OTHER arbiters fire only when both inputs have arrived (a
cascaded merge's downstream arbiter cannot acknowledge before its own server
has), and the AND links of a bd_delay FASTFALL line pass a rise only down the
chain (the input's direct taps flush the fall, not the rise).  --naive drops that rule (a looser bound).  Every other cell is
treated as passing its earliest input: a lower bound on any real round trip.
GP_k is the one fixed path.  All numbers come from ONE column of the SDF
(--col: 0 = FAST_MIN on an xray_delay.py SDF, 2 = SLOW_MAX), optionally
scaled; mixing columns is not a PVT point.  Prints one row per arbiter
and the worst path, and exits 1 if any margin is negative.
"""
import collections
import heapq
import json
import re
import sys

TRP_MAX = 647

RE_IC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)")
RE_INST = re.compile(r"\(INSTANCE\s+(\S*?)\)")
RE_IO = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)")


def unesc(s):
    return s.replace("\\", "")


def main():
    args = sys.argv[1:]
    col, scale = 0, 1.0
    if "--col" in args:
        i = args.index("--col"); col = int(args[i + 1]); del args[i:i + 2]
    if "--scale" in args:
        i = args.index("--scale"); scale = float(args[i + 1]); del args[i:i + 2]
    global CAWARE
    CAWARE = "--naive" not in args
    args = [a for a in args if a != "--naive"]
    jpath, sdf = args
    cells = json.load(open(jpath))["modules"]["top"]["cells"]

    adj = collections.defaultdict(list)       # node "cell/pin" -> [(node, ps)]
    arc = {}                                    # (cell, in, out) -> ps
    wire = {}                                   # (src, dst) -> ps
    inst = None
    for line in open(sdf):
        m = RE_IC.search(line)
        if m:
            s, d = unesc(m.group(1)), unesc(m.group(2))
            ps = int(m.group(3 + col)) * scale
            if s.startswith("$PACKER_GND") or s.startswith("$PACKER_VCC"):
                continue                        # constants never switch
            adj[s].append((d, ps)); wire[(s, d)] = ps
            continue
        m = RE_INST.search(line)
        if m:
            inst = unesc(m.group(1)); continue
        m = RE_IO.search(line)
        if m and inst:
            ps = int(m.group(3 + col)) * scale
            arc[(inst, m.group(1), m.group(2))] = ps
            adj["%s/%s" % (inst, m.group(1))].append(("%s/%s" % (inst, m.group(2)), ps))

    radj = set(d for lst in adj.values() for d, _ in lst)

    def dijkstra(src, targets, cnodes=None):
        """earliest arrival from src.  cnodes: {output node: [input pins]} of
        C-elements C(g, A0) whose output needs BOTH inputs (max, not min)"""
        cnodes = cnodes or {}
        need = collections.defaultdict(list)      # input pin -> c output
        for o, ins in cnodes.items():
            for i in ins:
                need[i].append(o)
        got = collections.defaultdict(dict)
        dist, prev = {src: 0}, {}
        pq, left = [(0, src)], set(targets)
        while pq and left:
            d, u = heapq.heappop(pq)
            if d > dist.get(u, 1e18):
                continue
            left.discard(u)
            for o in need.get(u, ()):
                c = o.rsplit("/", 1)[0]
                got[o][u] = d + arc.get((c, u.rsplit("/", 1)[1], "O6"), 0)
                if len(got[o]) == len(cnodes[o]):
                    t = max(got[o].values())
                    if t < dist.get(o, 1e18):
                        dist[o] = t; prev[o] = max(got[o], key=got[o].get)
                        heapq.heappush(pq, (t, o))
            for v, w in adj.get(u, ()):
                if v in cnodes:
                    continue                    # reached only through the max rule
                if d + w < dist.get(v, 1e18):
                    dist[v] = d + w; prev[v] = u; heapq.heappush(pq, (d + w, v))
        return dist, prev

    def pin_of(cname, logical):
        """physical pin carrying logical input `logical` (I0..I5)"""
        a = cells[cname]["attributes"]
        for k, v in a.items():
            if k.startswith("X_ORIG_PORT_A") and logical in v.split():
                return k[len("X_ORIG_PORT_"):]
        raise KeyError((cname, logical))

    def sink_on(cname, net):
        return [p for p, b in cells[cname]["connections"].items()
                if b == [net] and p.startswith("A")]

    arbs = sorted(c[:-len(".ustate$LUT6")] for c in cells if c.endswith(".ustate$LUT6"))
    cnodes_all = {}
    for p in arbs:
        st6 = p + ".ustate$LUT6"
        a0net = cells[st6]["connections"][pin_of(st6, "I4")][0]
        for k, (grc, gout) in {1: (p + ".ugrant$LUT5", "O5"), 2: (p + ".ugrant$LUT6", "O6")}.items():
            u = p + ".ua%d.u" % k
            gnet = cells[grc]["connections"][gout][0]
            cnodes_all[u + "/O6"] = [u + "/" + x for x in sink_on(u, a0net) + sink_on(u, gnet)]
    # bd_delay FASTFALL links: LUT2 AND (INIT 1000) of the previous link and
    # the line's input.  From idle (all 0) a RISING edge has to come down the
    # chain; the input's direct tap only flushes the fall.  So their output
    # needs both inputs too.
    for n, c in cells.items():
        if (c["type"] == "SLICE_LUTX" and c["attributes"].get("X_ORIG_TYPE") == "LUT2"
                and str(c["parameters"].get("INIT", "")).lstrip("0") == "1000"):
            out = "O6" if c["connections"].get("O6") else "O5"
            ins = [n + "/" + q for q, b in c["connections"].items()
                   if q.startswith("A") and b and ("%s/%s" % (n, q)) in radj]
            if len(ins) == 2:
                cnodes_all[n + "/" + out] = ins
    rows, bad, worst = [], 0, None
    for st6 in sorted(c for c in cells if c.endswith(".ustate$LUT6")):
        p = st6[:-len(".ustate$LUT6")]
        st5, gr6, gr5 = p + ".ustate$LUT5", p + ".ugrant$LUT6", p + ".ugrant$LUT5"
        ua = {1: p + ".ua1.u", 2: p + ".ua2.u"}
        if not all(x in cells for x in (st5, gr6, gr5, ua[1], ua[2])):
            continue
        a0net = cells[st6]["connections"][pin_of(st6, "I4")][0]
        R0 = st5 + "/O5"
        # skew: R0 lag behind q for one request edge
        skew = None
        for lg in ("I0", "I1"):
            pin6, pin5 = pin_of(st6, lg), pin_of(st5, lg)
            net = cells[st6]["connections"][pin6][0]
            srcs = [s for (s, d) in wire if d == st6 + "/" + pin6]
            w6 = wire[(srcs[0], st6 + "/" + pin6)]
            w5 = wire[(srcs[0], st5 + "/" + pin5)]
            sk = (w5 + arc.get((st5, pin5, "O5"), 0)) - (w6 + arc.get((st6, pin6, "O6"), 0))
            skew = sk if skew is None else min(skew, sk)
        tl = None
        qfb = [d for (s, d) in wire if s == st6 + "/O6" and d.startswith(st6 + "/")]
        if qfb:
            fbp = qfb[0].split("/")[-1]
            tl = wire[(st6 + "/O6", qfb[0])] + arc.get((st6, fbp, "O6"), 124)
        for k, (grc, gout) in {1: (gr5, "O5"), 2: (gr6, "O6")}.items():
            u = ua[k]
            a0p = sink_on(u, a0net)
            gnet = cells[grc]["connections"][gout][0]
            gp_pin = sink_on(u, gnet)
            if len(a0p) != 1 or len(gp_pin) != 1:
                sys.exit("arb_roundtrip: %s: cannot find A0/g pins (%s %s)" % (u, a0p, gp_pin))
            qpin = pin_of(grc, "I2")
            gp = (wire[(st6 + "/O6", grc + "/" + qpin)] + arc[(grc, qpin, gout)]
                  + wire[(grc + "/" + gout, u + "/" + gp_pin[0])])
            ck = arc.get((u, gp_pin[0], "O6"), 0)
            ak = arc.get((u, a0p[0], "O6"), 0)
            tgt = u + "/" + a0p[0]
            cn = {o: v for o, v in cnodes_all.items() if not o.startswith(p + ".ua")} if CAWARE else {}
            dist, prev = dijkstra(R0, [tgt], cn)
            rt = dist.get(tgt)
            if rt is None:
                sys.exit("arb_roundtrip: no path %s -> %s" % (R0, tgt))
            req = TRP_MAX + gp + ck - skew - ak
            margin = rt - req
            path, n = [], tgt
            while n != R0:
                path.append(n); n = prev[n]
            path.append(R0)
            rows.append((p, k, tl, rt, gp, skew, req, margin, len(path)))
            if margin < 0:
                bad += 1
            if worst is None or margin < worst[0]:
                worst = (margin, p, k, list(reversed(path)), dist)
    print("SDF %s, column %d, scale %g, trp_max %d, %s" % (sdf, col, scale, TRP_MAX,
          "other arbiters' C(g, A0) need both inputs" if CAWARE else "naive shortest path"))
    print("%-34s %2s %6s %7s %6s %5s %7s %7s %6s" % ("arbiter", "k", "TLOOP", "RT_min", "GP", "skew",
                                                     "RTreq", "margin", "hops"))
    for p, k, tl, rt, gp, sk, req, mg, h in rows:
        print("%-34s %2d %6s %7.0f %6.0f %5.0f %7.0f %7.0f %6d" % (
            p.replace("urig.udut.", ""), k, "%.0f" % tl if tl else "-", rt, gp, sk, req, mg, h))
    if worst:
        mg, p, k, path, dist = worst
        print("worst: %s ua%d margin %.0f ps; shortest R0 -> A0 path:" % (p, k, mg))
        for n in path:
            print("  %7.0f  %s" % (dist[n], n.replace("urig.udut.", "")))
    print("%d of %d ack C-elements below the requirement" % (bad, len(rows)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
