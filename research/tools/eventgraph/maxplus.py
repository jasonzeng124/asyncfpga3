"""maxplus.py -- maximum cycle ratio of a timed event graph by running its max-plus recursion.

Arcs are dicts with u, v (node ids), w (delay, ps) and o (iteration offset >= 0, the tokens on the arc).
T[v, k] = max over arcs (u -> v) of T[u, k - o] + w, with T[., k < 0] = 0.  After the transient, the growth per
iteration is the maximum cycle ratio (sum w / sum o over the worst cycle) of the part of the graph upstream of the
node watched; the critical cycle is read back by following the argmax arcs.  Offset-0 arcs must form a DAG (a cycle
with no token is a combinational loop: an error).
"""
import collections
import numpy as np

NEG = -1e18


def _levels(n, arcs):
    zero = [i for i, e in enumerate(arcs) if e["o"] == 0]
    indeg = [0] * n; out = collections.defaultdict(list)
    for i in zero:
        indeg[arcs[i]["v"]] += 1; out[arcs[i]["u"]].append(i)
    lev = [0] * n; q = collections.deque(x for x in range(n) if indeg[x] == 0); seen = 0
    while q:
        x = q.popleft(); seen += 1
        for i in out[x]:
            y = arcs[i]["v"]; lev[y] = max(lev[y], lev[x] + 1); indeg[y] -= 1
            if indeg[y] == 0: q.append(y)
    if seen != n:
        raise ValueError("offset-0 arcs form a cycle (%d nodes on or behind it)" % (n - seen))
    by = collections.defaultdict(list)
    for i in zero: by[lev[arcs[i]["v"]]].append(i)
    return [np.array(by[l], dtype=np.int64) for l in sorted(by)]


def normalize(n, arcs):
    """Shift node labels so every offset is >= 0 (offsets on a cycle sum to its tokens whatever the labels; edits may
    label new events loosely).  Difference constraints p(v) - p(u) >= -o(u,v), solved by Bellman-Ford."""
    if all(e["o"] >= 0 for e in arcs): return arcs
    d = [0] * n
    for it in range(n + 1):
        ch = False
        for e in arcs:
            if d[e["u"]] + e["o"] < d[e["v"]]:
                d[e["v"]] = d[e["u"]] + e["o"]; ch = True
        if not ch: break
    else:
        raise ValueError("a cycle with a negative token count")
    out = []
    for e in arcs:
        e2 = dict(e); e2["o"] = e["o"] + d[e["u"]] - d[e["v"]]; out.append(e2)
    return out


def simulate(n, arcs, K=600):
    if not arcs:
        raise ValueError("no arcs")
    arcs = normalize(n, arcs)
    u = np.array([e["u"] for e in arcs], dtype=np.int64); v = np.array([e["v"] for e in arcs], dtype=np.int64)
    w = np.array([e["w"] for e in arcs], dtype=np.float64); o = np.array([e["o"] for e in arcs], dtype=np.int64)
    if (o < 0).any(): raise ValueError("negative offset")
    levels = _levels(n, arcs)
    pos = np.nonzero(o > 0)[0]
    T = np.full((K, n), NEG)
    for k in range(K):
        Tk = T[k]
        if len(pos):
            kk = k - o[pos]
            src = np.where(kk >= 0, T[np.maximum(kk, 0), u[pos]], 0.0)
            np.maximum.at(Tk, v[pos], src + w[pos])
        for idx in levels:
            np.maximum.at(Tk, v[idx], Tk[u[idx]] + w[idx])
    return T, (u, v, w, o)


def critical(T, uvwo, start, back=400):
    """Follow argmax arcs back from (start, last iteration); return the arc ids of the first closed cycle met."""
    u, v, w, o = uvwo
    K = T.shape[0]
    into = collections.defaultdict(list)
    for i in range(len(u)): into[int(v[i])].append(i)
    x, k = start, K - 1; path = []; seen = {}
    while k > K - 1 - back:
        best = None
        for i in into[x]:
            kk = k - int(o[i])
            val = (T[kk, u[i]] if kk >= 0 else 0.0) + w[i]
            if abs(val - T[k, x]) < 1e-6:
                best = i; break
        if best is None:
            return None
        if x in seen:
            j = seen[x]
            return list(reversed(path[j:]))
        seen[x] = len(path); path.append(best)
        x, k = int(u[best]), k - int(o[best])
    return None


def mcr(n, arcs, watch=None, K=600):
    """(ratio, cycle arc ids) of the worst cycle upstream of node `watch` (None: the worst cycle of the graph)."""
    arcs = normalize(n, arcs)
    T, uvwo = simulate(n, arcs, K)
    if watch is None:
        g = (T[K - 1] - T[K - 121]) / 120
        g[T[K - 1] < -1e17] = -1
        watch = int(np.argmax(g))
    cyc = critical(T, uvwo, watch)
    if not cyc:
        return float("nan"), []
    ws = sum(arcs[i]["w"] for i in cyc); os_ = sum(arcs[i]["o"] for i in cyc)
    M = 120
    growth = (T[K - 1, watch] - T[K - 1 - M, watch]) / M
    if abs(growth - ws / os_) > 0.5:
        raise ValueError("cycle read back (%.1f ps) is not the growth rate (%.1f ps)" % (ws / os_, growth))
    return ws / os_, cyc
