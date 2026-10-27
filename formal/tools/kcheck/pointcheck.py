#!/usr/bin/env python3
"""Probe C-10n diagnostic (UNTRUSTED, explanation only; not a verdict).
    python3 pointcheck.py KERNEL        (reads results/KERNEL/disagree.tsv and each seed's
                                         build/KERNEL/s<seed>/check/obl.tc.gz)
For every disagreeing row whose tcheck instances are plain DAG instances (req/data/arc;
rules A, E, I, F, J, H -- not the certificate late sides Hc/Fc), recompute the margin with
EVERY arc at ONE fixed point of its prjxray interval: all at fast_min ("fast@lo"), all at
fast_max, slow_min, slow_max.  tcheck's own fast/slow variants let each arc take any value
in [min, max] independently (no on-die correlation inside a corner), so a row that fails
tcheck's unguarded corner but passes at every fixed point needs request arcs at the low end
AND data arcs at the high end of the SAME corner: whether that happens on silicon is the
local-scatter (kappa) question of the corner model, not a routing defect.  Margin = earliest
request change - latest data change - setup, min over the row's instances.
-> results/KERNEL/pointcheck.tsv"""
import gzip, heapq, pathlib, sys
from collections import defaultdict
H = pathlib.Path(__file__).resolve().parent
k = sys.argv[1]
R = H / "results" / k
dis = [l.rstrip("\n").split("\t") for l in open(R / "disagree.tsv")][1:]
want = defaultdict(set)              # seed -> {(rule-as-in-tc, row)}
for d in dis:
    seed, rule, fl, row = d[:4]
    if fl in ("Hc", "Fc"):
        continue
    want[seed].add((fl, row))


def margins(arcs, req, data, setup, pick):
    adj = defaultdict(list)
    for a, b, lo, hi in arcs:
        adj[a].append((b, lo if pick == 0 else hi))
    # shortest (earliest) to req, longest to data: DAG (unrolled), node 0 = launch
    dist = {0: 0}; pq = [(0, 0)]
    while pq:
        t, u = heapq.heappop(pq)
        if t > dist.get(u, 1 << 60):
            continue
        for v, w in adj[u]:
            if t + w < dist.get(v, 1 << 60):
                dist[v] = t + w; heapq.heappush(pq, (t + w, v))
    order, seen, st = [], set(), [(0, 0)]
    while st:                      # iterative topological order from 0
        u, i = st.pop()
        if i == 0:
            if u in seen:
                continue
            seen.add(u)
        if i < len(adj[u]):
            st.append((u, i + 1)); v = adj[u][i][0]
            if v not in seen:
                st.append((v, 0))
        else:
            order.append(u)
    far = {0: 0}
    for u in reversed(order):
        if u in far:
            for v, w in adj[u]:
                far[v] = max(far.get(v, -1), far[u] + w)
    r = min((dist[x] for x in req if x in dist), default=None)
    dl = max((far[x] for x in data if x in far), default=None)
    if r is None or dl is None:
        return None
    return r - dl - setup


out = ["seed\trule\trow\tfast@min\tfast@max\tslow@min\tslow@max\tinstances"]
for seed, rows in sorted(want.items()):
    f = H / "build" / k / f"s{seed}" / "check" / "obl.tc.gz"
    res = defaultdict(lambda: defaultdict(list))
    cur = None
    for line in gzip.open(f, "rt"):
        w = line.split()
        if not w:
            continue
        if w[0] == "inst":
            cur = None
            if len(w) >= 4 and (w[1], w[2]) in rows and w[-2] in ("fast", "slow"):
                cur = dict(key=(w[1], w[2]), var=w[-2], arcs=[], req=[], data=[], setup=0, cert=False)
        elif cur is None:
            continue
        elif w[0] == "arc":
            cur["arcs"].append(tuple(map(int, w[1:5])))
        elif w[0] == "req":
            cur["req"] += [int(x) for x in w[1:]]
        elif w[0] == "data":
            cur["data"] += [int(x) for x in w[1:]]
        elif w[0] == "setup":
            cur["setup"] = int(w[1])
        elif w[0] in ("late", "pot", "target", "cap"):
            cur["cert"] = True
        elif w[0] == "end":
            if not cur["cert"] and cur["req"]:
                for p in (0, 1):
                    m = margins(cur["arcs"], cur["req"], cur["data"], cur["setup"], p)
                    if m is not None:
                        res[cur["key"]][(cur["var"], p)].append(m)
            cur = None
    for key in sorted(rows):
        d = res.get(key)
        if not d:
            out.append(f"{seed}\t{key[0]}\t{key[1]}\t-\t-\t-\t-\tno plain DAG instance")
            continue
        vals = [min(d[(v, p)]) if d.get((v, p)) else "-" for v in ("fast", "slow") for p in (0, 1)]
        out.append("\t".join(map(str, (seed, *key, *vals, len(d[("fast", 0)])))))
(R / "pointcheck.tsv").write_text("\n".join(out) + "\n")
print("\n".join(out))
