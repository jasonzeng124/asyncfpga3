"""crosscheck.py -- independent (UNTRUSTED) recomputation of xselhold's hold rows.

    python3 -I crosscheck.py SKEL.json BANDS.json CERT.json MAP.json

Probe E8SelC.  Rebuilds the gate bands the way Parse.buildDesign does (LUT gate band from
"cells" or the default "lut"; one route gate per LUT pin, band from "arcs" or the default
"route" / "feedback"; ps -> steps with unit 1: lo = max 1 lo, hi = max lo hi), then per map
literal: lo(rg), selLo (Events8BridgeSel.selLo), hiC per copy (phi(full) - 1), the shortest
low-end path D from the acknowledge wire down to the source's output (Dijkstra), and the
margin D + selLo + lo(rg) - hiC - 1.  Prints one line per literal and the minimum, in the
same form as xselhold, so the two outputs can be compared row by row (cmp.sh).
"""
import heapq
import json
import sys


def steps(b):
    lo = max(1, b[0])
    return lo, max(lo, b[1])


def main(skelp, bandp, certp, mapp):
    sk = json.load(open(skelp))["modules"]["gcd_ctl"]
    B = json.load(open(bandp))
    cert = json.load(open(certp))
    mp = json.load(open(mapp))
    dlut = tuple(B.get("lut", [1, 1]))
    droute = tuple(B.get("route", [1, 1]))
    dfb = tuple(B["feedback"]) if B.get("feedback") else droute
    band, ins, outw, isbuf = {}, {}, {}, {}
    drv_net = {}
    for cn, c in sk["cells"].items():
        drv_net[c["connections"]["O"][0]] = cn
    for cn, c in sk["cells"].items():
        k = int(c["type"][3])
        o = c["connections"]["O"][0]
        g = f"{cn}/O"
        band[g] = steps(tuple(B["cells"].get(cn, dlut)))
        isbuf[g] = k == 1 and int(c["parameters"]["INIT"], 2) % 4 == 2
        outw[g] = ("net", o)
        gi = []
        for i in range(k):
            bit = c["connections"][f"I{i}"][0]
            if not isinstance(bit, int):
                gi.append(("const", bit))
                continue
            r = f"{cn}/I{i}"
            own = drv_net.get(bit) == cn
            band[r] = steps(tuple(B["arcs"].get(r, dfb if own else droute)))
            isbuf[r] = True
            outw[r] = ("pin", cn, i)
            ins[r] = [("net", bit)]
            gi.append(("pin", cn, i))
        ins[g] = gi
    drv = {w: g for g, w in outw.items()}
    lo = lambda g: band[g][0]
    hi = lambda g: band[g][1]

    def plo(path):
        return sum(lo(g) for g, _ in path)

    def phi(path):
        return sum(hi(g) for g, _ in path)

    def dijkstra(top):
        dist = {top: 0}
        pq = [(0, top)]
        while pq:
            dd, w = heapq.heappop(pq)
            if dd > dist.get(w, 1 << 60):
                continue
            g = drv.get(w)
            if g is None:
                continue
            for v in ins[g]:
                nd = dd + lo(g)
                if nd < dist.get(v, 1 << 60):
                    dist[v] = nd
                    heapq.heappush(pq, (nd, v))
        return dist

    nodes = cert["nodes"]
    cache = {}
    mins = None
    smin = None
    n = 0
    for e in mp["entries"]:
        nj = nodes[e["node"]]
        p = nj["pins"][e["pin"]]
        lut = nj["lut"]
        st = p["st"]
        if st:
            selLo = lo(p["sg"]) + plo(p["top"]) + (lo(lut) - 1)
            sgate = p["sg"]
            copies = [p["top"] + [[p["sg"], p["sci"]]] + p["bot"]]
        else:
            selLo = lo(lut) - 1
            sgate = lut
            copies = p["paths"]
        hiCs = [phi([[lut, p["ip"]]] + c) - 1 for c in copies]
        sw = ins[sgate][e["lit"]]
        rg = drv[sw]
        src = nodes[p["src"]]
        srcw = outw[src["lut"]]
        ak = outw[e["ak"]]
        if ak not in cache:
            cache[ak] = dijkstra(ak)
        D = cache[ak].get(srcw)
        if D is None:
            print(f"  NOPATH {nj['name']} pin{e['pin']} lit{e['lit']}")
            continue
        m = min(D + selLo + lo(rg) - h - 1 for h in hiCs)
        n += 1
        mins = m if mins is None else min(mins, m)
        # split rows: best junction per copy, bottom a buffer chain
        sm = None
        for c in copies:
            full = [[lut, p["ip"]]] + c
            best = None
            for k in range(len(full)):
                if all(isbuf[g] for g, _ in full[k + 1:]):
                    g, i = full[k]
                    w = ins[g][i]
                    if w in cache[ak]:
                        mg = cache[ak][w] + selLo + lo(rg) - (phi(full[:k + 1]) - 1) - 1
                        best = mg if best is None else max(best, mg)
            sm = best if sm is None or best is None else min(sm, best)
        smin = sm if smin is None or sm is None else min(smin, sm)
        print(f"  {nj['name']} pin{e['pin']} lit{e['lit']} D {D} selLo {selLo} rglo {lo(rg)} hiC {max(hiCs)} margin {m} split {sm}")
    print(f"[crosscheck] literals {n}, min margin {mins}, min split margin {smin}")


if __name__ == "__main__":
    main(*sys.argv[1:5])
