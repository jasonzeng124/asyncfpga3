#!/usr/bin/env python3
"""Shard C helper (UNTRUSTED): certificate from one simulated run (hist_c<c>.pkl): events of exact nodes,
causes, vector clocks (L), delays per (gate, source).  Imported by check.py.
Cause modes: 'all' = for each exact source w of gate v, the latest event of w whose READ time (event time +
mid delay of v's pin) lies in (time of v's previous event (or t0), time of this event]; plus (v, k-1).
'trig' = only source events read exactly at this event's time; plus (v, k-1).
Env nodes: latest events of the env rule's read set in (prev, t-1]; rst has none."""
import sys, pickle, collections
import numpy as np
from bisect import bisect_right, bisect_left
sys.path.insert(0, "/tmp/claude-0/arbh")
from classify import load, lut

ENVREAD = {"req": ("a_ack", "b_ack", "start_ack"),
           "pend_ack": ("req",), "out0_ack": ("out0_req",), "rst": ()}

def build(c, mode="all"):
    C = load(); gates = C["gates"]; EX = C["EXACT"]; bs = C["bs"]
    H = pickle.load(open("/tmp/claude-0/arbh/hist_c%d.pkl" % c, "rb")); R = H["R"]; t0 = R - 1
    hist = H["hist"]
    def v0(n): return hist[n][0] if n in hist else False
    def valat(n, t):
        if n not in hist: return False
        b, ts = hist[n]; return b ^ (bisect_right(ts, t) % 2 == 1)
    s0 = {}
    ev = {}
    for n in EX:
        s0[n] = valat(n, t0)
        ev[n] = [x for x in (hist[n][1] if n in hist else []) if x > t0]
    envnode = {bs[k]: k for k in ENVREAD}
    # delays: per (v, w) for exact gate v and live source w
    dl = {}   # (v,w) -> (lo, hi, mid)
    for v in EX:
        if v in envnode: continue
        for p in C["live"][v]:
            w = p["src"]
            if (v, w) in dl:
                o = dl[(v, w)]; print("WARN two pins", v, w)
            dl[(v, w)] = p["win"][c]
    # event ids
    eid = {}; elist = []
    for n in sorted(EX):
        for k, t in enumerate(ev[n]):
            eid[(n, k)] = len(elist); elist.append((n, k, t))
    causes = {}
    for n in EX:
        ts = ev[n]
        for k, t in enumerate(ts):
            tp = ts[k - 1] if k else t0
            cs = []
            if n in envnode:
                for key in ENVREAD[envnode[n]]:
                    w = bs[key]; tw = ev[w]
                    i = bisect_right(tw, t - 1) - 1
                    if i >= 0 and tw[i] > tp: cs.append((w, i))
            else:
                for p in C["live"][n]:
                    w = p["src"]
                    if w == n or w not in EX: continue
                    d = p["win"][c][2]; tw = ev[w]
                    if mode == "all":
                        i = bisect_right(tw, t - d) - 1
                        if i >= 0 and tw[i] + d > tp: cs.append((w, i))
                    else:
                        i = bisect_right(tw, t - d) - 1
                        if i >= 0 and tw[i] + d == t: cs.append((w, i))
            if k: cs.append((n, k - 1))
            causes[(n, k)] = cs
    # vector clocks over exact nodes (int8 counts; max len small)
    xs = sorted(EX); xi = {n: i for i, n in enumerate(xs)}
    order = sorted(range(len(elist)), key=lambda e: (elist[e][2], e))
    VC = np.zeros((len(elist), len(xs)), dtype=np.int8)
    for e in order:
        n, k, t = elist[e]
        row = VC[e]
        for (w, i) in causes[(n, k)]:
            np.maximum(row, VC[eid[(w, i)]], out=row)
        row[xi[n]] = k + 1
    return dict(C=C, H=H, c=c, t0=t0, s0=s0, ev=ev, dl=dl, eid=eid, elist=elist, causes=causes, VC=VC, xi=xi,
                envnode=envnode, valat=valat, mode=mode)

def L(K, a, k, b):
    if a == b: return 0       # diagonal excluded (see report: TO with L(a,k,a)=k+1 is unsatisfiable)
    return int(K["VC"][K["eid"][(a, k)], K["xi"][b]])

if __name__ == "__main__":
    import time
    t = time.time(); K = build(int(sys.argv[1]), sys.argv[2] if len(sys.argv) > 2 else "all")
    print("events %d, built in %.1fs" % (len(K["elist"]), time.time() - t))
    nc = collections.Counter(len(v) for v in K["causes"].values()); print("causes per event", sorted(nc.items()))
