# T67: research's committed gate oracles (research/data/eventgraph/gate/*.exp) vs the audit's own oracles (t40/t46/t48).
import importlib.util, sys
def load(p):
    s = importlib.util.spec_from_file_location(p.replace('/', '_'), p); m = importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
A = '/home/user/asyncfpga3/audit/'
fx = {'xor17': (load(A + 't40/oracle.py'), 'xs'), 'ipow17': (load(A + 't46/oracle.py'), sys.argv[2]), 'col13': (load(A + 't48/oracle.py'), sys.argv[3])}
for k, (m, fn) in fx.items():
    f = getattr(m, fn)
    vec = [tuple(int(w, 16) for w in l.split()) for l in open(f'/root/t66/{k}.hex') if l.strip()]
    exp = [int(l, 16) for l in open(f'/root/t66/{k}.exp') if l.strip()]
    bad = [(i, v, e, f(*v)) for i, (v, e) in enumerate(zip(vec, exp)) if f(*v) != e]
    print(f"{k}: {len(vec)} vectors, {len(exp)} expected; own-oracle mismatches {len(bad)} {bad[:3]}")
