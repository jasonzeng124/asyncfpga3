# T66: research step 2 "every falling arc at 0" on its committed graphs, own solver (t66/mcr.py's): arcs whose target
# edge (nodes.tsv 'edge') is F get weight 0; report the max cycle ratio.
import sys, os, csv, importlib.util
spec = importlib.util.spec_from_file_location('mcr', os.path.join(os.path.dirname(__file__), 'mcr.py'))
src = open(spec.origin).read().split('root = sys.argv[1]')[0]; ns = {}; exec(src, ns)
for run in sys.argv[2:]:
    d = os.path.join(sys.argv[1], run)
    arcs, nodes, P, cl = ns['load'](d)
    ids = sorted(nodes); idx = {k: i for i, k in enumerate(ids)}
    E = [(idx[int(a['u'])], idx[int(a['v'])], 0.0 if nodes[int(a['v'])]['edge'] == 'F' else float(a['w_ps']), int(a['offset'])) for a in arcs]
    print(run, f"P {P/1000:.2f} ns, falls at 0: {ns['mcr'](len(ids), E)/1000:.2f} ns")
