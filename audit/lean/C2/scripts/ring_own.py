"""Auditor: rebuild collatz's ring_depths graph straight from bdc and compare with
the committed Lean cert graph; own min-cycle via Bellman-Ford-per-source."""
import sys, re, os
BDC = '/home/user/wt-formal2/bdc'; sys.path.insert(0, BDC)
import emit, slack
from hs import parse
from map import Table
mlir, leanf, name = sys.argv[1:4]
func = parse.parse_module(open(mlir).read(), filename=mlir)[0]
em = emit.Emitter(func, Table())
E, _ = slack.build_node_graph(func)
E = [e for e in E if e.value not in em.mem_absorbed]
rd = emit.ring_depths(func, em.linked, exclude=em.mem_absorbed)
mine = [(e.producer, e.consumer, rd.get(e.value, 0)) for e in E]
L = open(leanf).read()
g = re.search(r'def %s : Graph := \[(.*?)\]\n' % name, L).group(1)
theirs = [tuple(map(int, t)) for t in re.findall(r'⟨(\d+), (\d+), (\d+)⟩', g)]
print('edges mine', len(mine), 'lean', len(theirs), 'equal(list)', mine == theirs, 'equal(multiset)', sorted(mine) == sorted(theirs))
n = len(func.nodes)
def mincyc(edges):
    best = None; bestc = None
    import heapq
    for s in range(n):
        dist = {}; pq = [(w, v, [(u, v, w)]) for (u, v, w) in edges if u == s]
        heapq.heapify(pq)
        while pq:
            d, v, p = heapq.heappop(pq)
            if v in dist: continue
            dist[v] = (d, p)
            for (a, b, w) in edges:
                if a == v and b not in dist: heapq.heappush(pq, (d + w, b, p + [(a, b, w)]))
        if s in dist and (best is None or dist[s][0] < best): best, bestc = dist[s]
    return best, bestc
b, c = mincyc(mine); print('own min cycle', b, 'example', c)
pre = [(e.producer, e.consumer, 1 if e.value in em.linked else 0) for e in E]
print('own min cycle pre', mincyc(pre)[0])
