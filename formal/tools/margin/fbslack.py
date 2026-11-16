#!/usr/bin/env python3
"""margin/fbslack.py (shard C, UNTRUSTED static screen): every feedback race of a build, from nextpnr's SDF alone.

    python3 fbslack.py BUILD.sdf [--top 40] [--grep ctl] [--err 0.085] [--err7 0.47]

A LUT that reads its own output (a C-element, a latch: an INTERCONNECT from cell/O6 to an input pin of the same cell)
must see its own new value through that feedback route before any OTHER consequence of the same output change comes
back to another of its pins (FOR-RESEARCH C13: `ulink_n_falseResult_7` stage 0's controller, where the return is the
next stage's acknowledge). Per such cell q, at the SDF's (typical) values:
  A = INTERCONNECT(q/O -> q/A_f) + IOPATH(q, A_f -> O)            the feedback
  B = min over the other pins j of q: the shortest SDF path q/O -> ... -> q/A_j (cells by IOPATH, nets by
      INTERCONNECT; never through q itself; clocked cells end a path) + IOPATH(q, A_j -> O)
  slack = B - A, also as a multiple of the 8.5 % median and 47 % worst short-ring delay error of B.
B is the FASTEST structural return, which may not be a live one (a path through a mux or OR that never fires in this
order would give a pessimistic slack, like a static OR-join row). So a small slack here is a race to check with the
dynamic tool (run.sh / explain.py), not a failure; a large one is a race that cannot be tight at the SDF.
"""
import argparse, heapq, re, sys
ap = argparse.ArgumentParser(); ap.add_argument("sdf"); ap.add_argument("--top", type=int, default=40)
ap.add_argument("--grep", default=None, help="only cells whose name contains this"); ap.add_argument("--err", type=float, default=0.085)
ap.add_argument("--err7", type=float, default=0.47)
a = ap.parse_args()
IC = {}; IO = {}; inst = None
for l in open(a.sdf):
    if "(INSTANCE" in l: inst = l.split("(INSTANCE", 1)[1].strip().rstrip(")").strip().replace("\\", "")
    elif "(IOPATH" in l:
        f = l.split(); IO[(inst, f[1], f[2])] = int(f[3].strip("(").split(":")[1])
    elif "(INTERCONNECT" in l:
        f = l.split(); IC[(f[1].replace("\\", ""), f[2].replace("\\", ""))] = int(f[3].strip("(").split(":")[1])
adj = {}
for (s, d), v in IC.items(): adj.setdefault(s, []).append((d, v, "net"))
for (c, i, o), v in IO.items(): adj.setdefault(c + "/" + i, []).append((c + "/" + o, v, "cell"))
def cell(p): return p.rsplit("/", 1)[0]
def port(p): return p.rsplit("/", 1)[1]
rows = []
for (s, d), v in IC.items():
    q = cell(s)
    if cell(d) != q: continue
    if a.grep and a.grep not in q: continue
    o, f = port(s), port(d)
    if (q, f, o) not in IO: continue
    A = v + IO[(q, f, o)]
    targets = {q + "/" + i: IO[(q, i, o)] for (c, i, oo) in IO if c == q and oo == o and i != f}
    if not targets: continue
    lim = A + 20000
    dist = {s: 0}; prev = {}; pq = [(0, s)]; best = None
    while pq:
        dd, u = heapq.heappop(pq)
        if dd > dist.get(u, 1 << 60) or dd > lim: continue
        if u in targets and u != s:
            tot = dd + targets[u]
            if best is None or tot < best[0]: best = (tot, u)
            continue
        for w, c, kind in adj.get(u, []):
            if cell(w) == q and w not in targets: continue          # never through q itself
            if kind == "cell" and cell(u) == q: continue
            nd = dd + c
            if nd < dist.get(w, 1 << 60): dist[w] = nd; prev[w] = u; heapq.heappush(pq, (nd, w))
    if best is None: continue
    B, t = best; path = []; x = t
    while x in prev:
        if cell(x) != cell(prev[x]) or x == t: pass
        x = prev[x]
        if x != s and cell(x) != q and (not path or path[-1] != cell(x)): path.append(cell(x))
    rows.append((B - A, q, f, A, B, port(t), list(reversed(path))))
rows.sort()
print("# feedback races at nextpnr's SDF: slack = B (fastest structural return to another pin) - A (own feedback); %d cells" % len(rows))
print("# slack_ps  x8.5%%  x47%%  A_ps  B_ps  cell  fb_pin  return_pin  return path (cells)")
for sl, q, f, A, B, tp, path in rows[:a.top]:
    print("%+6d  %+5.1f  %+5.2f  %5d  %5d  %s  %s  %s  %s" % (sl, sl / (a.err * B), sl / (a.err7 * B), A, B, q, f, tp, " -> ".join(path[:8]) + (" ..." if len(path) > 8 else "")))
