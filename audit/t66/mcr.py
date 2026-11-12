# T66: own max-cycle-ratio (Lawler binary search + Bellman-Ford positive-cycle test) over research's committed event graphs
# (research/data/eventgraph/graphs/<run>/arcs.tsv), no research code. For each graph: own period vs check.txt's period;
# slack consistency: slack == phase_v - phase_u - w + offset*P (P from check.txt) for every arc; zero-slack in-arc per node
# (if every node has one, the max cycle ratio EQUALS P by construction: the step-1 "period equal" check is then structural).
import sys, os, re, csv
def load(d):
    arcs = [r for r in csv.DictReader(open(os.path.join(d, 'arcs.tsv')), delimiter='\t')]
    nodes = {int(r['id']): r for r in csv.DictReader(open(os.path.join(d, 'nodes.tsv')), delimiter='\t')}
    P = float(re.search(r'period P = (\d+) ps', open(os.path.join(d, 'check.txt')).read())[1])
    cl = float(re.search(r'graph period \(max cycle ratio\): ([\d.]+)', open(os.path.join(d, 'check.txt')).read())[1])
    return arcs, nodes, P, cl
def poscycle(n, E, lam):
    # E: (u, v, w, tok); is there a cycle with sum(w - lam*tok) > 0 ?  longest-path Bellman-Ford from a virtual source
    d = [0.0] * n
    for it in range(n + 1):
        ch = False
        for u, v, w, t in E:
            x = d[u] + w - lam * t
            if x > d[v] + 1e-9: d[v] = x; ch = True
        if not ch: return False
    return True
def mcr(n, E):
    lo, hi = 0.0, sum(max(w, 0) for _, _, w, _ in E) + 1
    if not poscycle(n, E, lo): return None
    for _ in range(80):
        mid = (lo + hi) / 2
        if poscycle(n, E, mid): lo = mid
        else: hi = mid
    return lo
root = sys.argv[1]
print("run\tnodes\tarcs\tP_trace\tP_research_graph\tP_own\tslack_mismatch\tnodes_without_zero_slack_in_arc\ttoken0_cycle")
for run in sorted(os.listdir(root)):
    d = os.path.join(root, run)
    if not os.path.exists(os.path.join(d, 'arcs.tsv')): continue
    arcs, nodes, P, cl = load(d)
    ids = sorted(nodes); idx = {k: i for i, k in enumerate(ids)}
    E = [(idx[int(a['u'])], idx[int(a['v'])], float(a['w_ps']), int(a['offset'])) for a in arcs]
    own = mcr(len(ids), E)
    # zero-token cycle would make the ratio infinite: test positive cycle with tokens ignored on token-0 subgraph
    E0 = [(u, v, w, 0) for u, v, w, t in E if t == 0]
    tok0 = poscycle(len(ids), [(u, v, max(w, 1e-6), 0) for u, v, w, _ in E0], 0.0) if E0 else False
    mism = 0
    for a in arcs:
        pu, pv = float(nodes[int(a['u'])]['phase_ps']), float(nodes[int(a['v'])]['phase_ps'])
        s = pv - pu - float(a['w_ps']) + int(a['offset']) * P
        if abs(s - float(a['slack_ps'])) > 1.5: mism += 1
    z = {int(a['v']) for a in arcs if abs(float(a['slack_ps'])) <= 1.5}
    print(f"{run}\t{len(ids)}\t{len(arcs)}\t{P:.0f}\t{cl:.3f}\t{own:.3f}\t{mism}\t{len(set(ids) - z)}\t{tok0}")
