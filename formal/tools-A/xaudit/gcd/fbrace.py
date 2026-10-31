#!/usr/bin/env python3
"""fbrace.py -- static own-feedback-vs-neighbour-response check on an xaudit netlist.

    python3 -I fbrace.py NET.json BANDS.json [--list N]

For every LUT whose output is routed back to one of its own pins (a storage node,
xaudit's definition), compare
    FB  = hi of its own-feedback arc (the latest the LUT sees its own new value)
    RSP = the shortest path, by lo, from its output net back to ANY OTHER of its
          pins (arc lo + LUT lo + arc lo + ... + final arc lo)
If RSP < FB there is a delay assignment inside the bands in which another input
changes in response to the output (only pins the INIT depends on count; a LUT5 of a
fractured pair has pins it ignores) before the LUT has seen its own new value: the
LUT then evaluates a stale hold value and can emit a runt (the pipe3 C-element
race of formal/notes/A-xaudit.md).  The path is structural (not checked to be
sensitisable), so a hit is a CANDIDATE race; a miss excludes this race class for
that node under these bands.  Bands are taken in ps, unrounded.
"""
import argparse
import heapq
import json


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("net")
    ap.add_argument("bands")
    ap.add_argument("--list", type=int, default=20)
    a = ap.parse_args()
    m = next(iter(json.load(open(a.net))["modules"].values()))
    B = json.load(open(a.bands))
    cells = m["cells"]
    nn = {v["bits"][0]: k for k, v in m["netnames"].items()}
    out = {cn: c["connections"]["O"][0] for cn, c in cells.items()}
    sinks = {}
    for cn, c in cells.items():
        for p, bb in c["connections"].items():
            if p != "O" and not isinstance(bb[0], str):
                sinks.setdefault(bb[0], []).append((cn, p, B["arcs"]["%s/%s" % (cn, p)][0]))
    def depends(c, p):
        k = int(c["type"][3:])
        i = int(p[1:])
        t = int(c["parameters"]["INIT"], 2)
        return any(((t >> x) & 1) != ((t >> (x ^ (1 << i))) & 1) for x in range(1 << k))

    rows = []
    for cn, c in cells.items():
        o = out[cn]
        own = [p for p, bb in c["connections"].items() if p != "O" and bb[0] == o]
        if not own:
            continue
        fb = max(B["arcs"]["%s/%s" % (cn, p)][1] for p in own)
        # Dijkstra from o (time 0 = output change), bounded by fb
        best = None
        dist = {o: 0}
        pq = [(0, o)]
        while pq:
            d, net = heapq.heappop(pq)
            if d > dist.get(net, 1 << 60) or d >= fb:
                continue
            for (sc, sp, alo) in sinks.get(net, []):
                t = d + alo
                if sc == cn:
                    if sp not in own and depends(c, sp) and (best is None or t < best[0]):
                        best = (t, sp, net)
                    continue
                t2 = t + B["cells"][sc][0]
                on = out[sc]
                if t2 < dist.get(on, 1 << 60) and t2 < fb:
                    dist[on] = t2
                    heapq.heappush(pq, (t2, on))
        rows.append((cn, nn.get(o, o), fb, best))
    hits = sorted([r for r in rows if r[3] is not None and r[3][0] < r[2]], key=lambda r: r[3][0] - r[2])
    print("%s with %s: %d storage nodes, %d with a structural response path faster than own-feedback hi"
          % (a.net, a.bands, len(rows), len(hits)))
    for cn, net, fb, (t, sp, via) in hits[:a.list]:
        print("  %-75s FB hi %5d ps, response lo %5d ps to pin %s (margin %d ps)" % (cn[-75:], fb, t, sp, t - fb))


if __name__ == "__main__":
    main()
