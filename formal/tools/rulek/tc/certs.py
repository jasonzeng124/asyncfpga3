#!/usr/bin/env python3
"""Probe C-10h front end (UNTRUSTED, but no longer trusted for the minimum): late sides on
the CYCLIC routed graph, checked by tcheck's `Tcheck.cverdict` (proved: `cverdict_sound`,
via `Formal.Timing.pot_sound`).

The whole routed graph (every arc of extract.py's graph, 6 corner intervals each, the
FASTRISE-side flag) and the storage set are written ONCE per .tc file (`graph`, `g`,
`stor` lines).  A cert obligation then carries
  * its data side as a DAG (10a/10d, unchanged: must be early),
  * its late side as a phase rule (`late`, `sw`, `blocked`, `target`: Tcheck.Late, the
    modelling content, stated in Lean), and
  * a potential (`cap`, `pot`): Python's Dijkstra distances on the SAME product graph
    Lean builds (`expand` below mirrors `Tcheck.expand` line by line).  tcheck checks
    the potential on every product arc; a wrong potential is reported CERTBAD, never a
    PASS.  pot = min(dist, C) with C = the least target distance; listed = every node
    with dist < C, default C (a valid potential: Formal/Timing/Unroll.lean doc).

Node numbering: Lean needs every zero-lo arc to go forward in node order (well-founded
induction for zero-delay arcs), so pins are numbered in a topological order of the arcs
whose lo is 0 in ANY variant.
"""
import heapq
import math
from collections import defaultdict

INF = 10 ** 12


class CertGraph:
    def __init__(self, c):
        self.c = c
        T, edges, ivl, V = c["T"], c["edges"], c["ivl"], c["VARIANTS"]
        self.V = V
        self.arcs = []                  # (s, d, ivl dict)
        pins = set(edges)
        for s, lst in edges.items():
            for d, w in lst:
                iv, _fb = ivl(s, d, w)
                self.arcs.append((s, d, iv))
                pins.add(d)
        # topological order of the zero-lo arcs (union over variants)
        zs, indeg = defaultdict(list), defaultdict(int)
        for s, d, iv in self.arcs:
            if any(iv[v][0] == 0 for v in V):
                zs[s].append(d); indeg[d] += 1
        order, ready = [], sorted(p for p in pins if indeg[p] == 0)
        while ready:
            p = ready.pop(); order.append(p)
            for q in zs[p]:
                indeg[q] -= 1
                if indeg[q] == 0:
                    ready.append(q)
        if len(order) != len(pins):
            raise RuntimeError(f"zero-delay cycle among {len(pins) - len(order)} pins")
        self.id = {p: i for i, p in enumerate(order)}
        self.n = len(order)
        self.succ = defaultdict(list)    # pin -> [(dst, ivl)]
        for s, d, iv in self.arcs:
            self.succ[s].append((d, iv))
        self.fr = c["fr"]
        self.stops = c["stops"]
        self.written = set()
        self.nzero = sum(len(v) for v in zs.values())

    def write(self, f):
        if id(f) in self.written:
            return
        self.written.add(id(f))
        f.write(f"graph {self.n}\n")
        for s, d, iv in self.arcs:
            fr = 1 if (s, d) in self.fr else 0
            f.write(f"g {self.id[s]} {self.id[d]} {fr} " +
                    " ".join(f"{iv[v][0]} {iv[v][1]}" for v in self.V) + "\n")
        st = sorted(self.id[p] for p in self.stops if p in self.id)
        for i in range(0, len(st), 64):
            f.write("stor " + " ".join(map(str, st[i:i + 64])) + "\n")

    # ---- the product graph, exactly as Tcheck.expand / Tcheck.switches
    def out_arcs(self, spec, p, ph, v):
        s = spec["s"]
        res = []
        if ph == 0 and p in spec["sw"]:
            res.append(((p, 1), 0))
        if p in spec["blocked"]:
            return res
        st = p in self.stops and p != s
        cut = spec.get("cut", ())
        for d, iv in self.succ.get(p, ()):
            if (p, d) in cut:           # C-10k: Tcheck.Late.cut (both phases)
                continue
            lo = iv[v][0]
            if ph == 0:
                if (spec["noFr0"] and (p, d) in self.fr and not (spec["swStor"] and st)) \
                        or (spec["stop0"] and st) or p in spec.get("blocked0", ()):
                    continue
                res.append(((d, 1 if (spec["swStor"] and st) else 0), lo))
            elif spec["two"]:
                res.append(((d, 1), lo))
        return res

    def pots(self, spec, v):
        """-> (cap, [(pin_id, ph, value)], settled count)"""
        s = spec["s"]
        tg = set(spec["targets"])
        best = {(s, 0): 0}
        heap = [(0, 0, s, 0)]
        cnt = 0
        C = None
        while heap:
            t, _, p, ph = heapq.heappop(heap)
            if t > best.get((p, ph), math.inf):
                continue
            if (p, ph) in tg and (p, ph) != (s, 0):
                C = t
                break
            for (q, qh), lo in self.out_arcs(spec, p, ph, v):
                if (q, qh) == (s, 0):
                    continue
                nt = t + lo
                if nt < best.get((q, qh), math.inf):
                    best[(q, qh)] = nt
                    cnt += 1
                    heapq.heappush(heap, (nt, cnt, q, qh))
        if C is None:
            C = INF
        lst = [(self.id[p], ph, d) for (p, ph), d in best.items() if d < C and (p, ph) != (s, 0)]
        return C, lst


def emit_cert(c, I, L, spec, meta):
    """I: an extract.Inst holding the DATA side (launch L = node 0, I.data); spec: the
    late phase rule over pins.  Writes one cert instance per variant."""
    G = c.get("_certG")
    if G is None:
        G = c["_certG"] = CertGraph(c)
    f = c["out"]
    G.write(f)
    if not I.data:
        meta["skip"] = "no data node"
        c["meta"].append(meta)
        return False
    succ, indeg, nodes = defaultdict(list), defaultdict(int), {L}
    for a, b, _, _ in I.arcs:
        succ[a].append(b); indeg[b] += 1; nodes |= {a, b}
    order, ready = [], [L]
    while ready:
        n = ready.pop(); order.append(n)
        for m in succ[n]:
            indeg[m] -= 1
            if indeg[m] == 0:
                ready.append(m)
    if len(order) != len(nodes):
        raise RuntimeError(f"{I.label}: data side not a DAG")
    idx = {n: i for i, n in enumerate(order)}
    nfb = sum(fb for *_, fb in I.arcs)
    sizes = {}
    for vi, v in enumerate(c["VARIANTS"]):
        cap, lst = G.pots(spec, v)
        sizes[v] = len(lst)
        f.write(f"inst {I.label} {v} fallback={nfb}/{len(I.arcs)}\n")
        f.write(f"setup 0\n")
        f.write("data " + " ".join(str(idx[d]) for d in sorted(I.data, key=idx.get)) + "\n")
        for a, b, ivd, _ in sorted(I.arcs, key=lambda x: (idx[x[0]], idx[x[1]])):
            lo, hi = ivd[v]
            f.write(f"arc {idx[a]} {idx[b]} {lo} {hi}\n")
        f.write("late %d %d %d %d %d %d\n" % (vi, G.id[spec["s"]], spec["two"], spec["noFr0"],
                                              spec["stop0"], spec["swStor"]))
        if spec["sw"]:
            f.write("sw " + " ".join(str(G.id[p]) for p in sorted(spec["sw"])) + "\n")
        if spec["blocked"]:
            f.write("blocked " + " ".join(str(G.id[p]) for p in sorted(spec["blocked"])) + "\n")
        for p, ph in sorted(spec["targets"]):
            f.write(f"target {G.id[p]} {ph}\n")
        f.write(f"cap {cap}\n")
        for i in range(0, len(lst), 40):
            f.write("pot " + " ".join(f"{a} {b} {d}" for a, b, d in lst[i:i + 40]) + "\n")
        f.write("end\n")
    meta["label"] = I.label
    meta["pot_sizes"] = sizes
    c["meta"].append(meta)
    return True


def spec(s, targets, two=0, noFr0=0, stop0=0, swStor=0, sw=(), blocked=()):
    return dict(s=s, targets=list(targets), two=two, noFr0=noFr0, stop0=stop0, swStor=swStor,
                sw=set(sw), blocked=set(blocked))
