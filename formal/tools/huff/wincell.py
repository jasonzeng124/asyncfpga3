#!/usr/bin/env python3
"""Shard C (UNTRUSTED prototype): winfix.py with one window per bdc CELL INSTANCE (its control nodes and
all their supports) instead of one per node, so a window holds the joint state of a cell's handshake.
Same moves and BO_f guard as winfix.py (a frontier flip needs every reader in the window insensitive),
same Cartesian join with the mover's own (cell) window. Optional relative-timing orders (--rt FILE: b
may not fire while c is excited; checked only where c and b share a window, else ignored = weaker).
usage: wincell.py huff.txt init.txt bel2cell.json [--seed-obs obs.txt] [--rt rt.txt] [--export win.txt]"""
import sys, collections, json, re
argv = sys.argv
src = open(__file__.replace("wincell.py", "winfix.py")).read()
src = src.split("ENVVARS = {REQ, PACK, OACK, W_ENV}")[0]
sys.argv = [argv[0], argv[1], argv[2]]
g = {"__name__": "winfix_pre"}
exec(compile(src, "winfix", "exec"), g)
sys.argv = argv
CTL, Ftab, spc, FRONT, names, env_moves, W_ENV = g["CTL"], g["Ftab"], g["spc"], g["FRONT"], g["names"], g["env_moves"], g["W_ENV"]
REQ, PACK, OACK = g["REQ"], g["PACK"], g["OACK"]
ENVVARS = {REQ, PACK, OACK, W_ENV}
initval = g["initval"]; envwin = g["windows"]["env"]
bel = json.load(open(argv[3]))
def cellof(c): return bel.get(names[c], names[c]).replace("bridge_i.udut.", "").split(".")[0]
cells = collections.defaultdict(list)
for c in CTL: cells[cellof(c)].append(c)
windows = {}
for k, cs in cells.items(): windows[k] = tuple(sorted(set(v for c in cs for v in spc[c])))
windows["env"] = envwin
wof = {c: cellof(c) for c in CTL}
pos = {k: {v: p for p, v in enumerate(W)} for k, W in windows.items()}
sp = {c: [pos[wof[c]][v] for v in spc[c]] for c in CTL}       # positions of c's support in its window
selfp = {c: pos[wof[c]][c] for c in CTL}
def key(t, ps):
    r = 0
    for i, p in enumerate(ps):
        if (t >> p) & 1: r |= 1 << i
    return r
def exc(c, t):  # t: tuple on c's window
    return Ftab[c][key(t, sp[c])] != bool((t >> selfp[c]) & 1)
print("cell windows", len(windows) - 1, "max size", max(len(W) for W in windows.values()), file=sys.stderr)
if "--export" in argv:
    with open(argv[argv.index("--export") + 1], "w") as f:
        f.write("%d\n" % len(windows))
        for k, W in windows.items(): f.write("%s %d %s\n" % (k, len(W), " ".join(str(v) for v in W)))
    sys.exit(0)
R = {k: {sum((1 << p) for p, v in enumerate(W) if initval(v))} for k, W in windows.items()}
if "--seed-obs" in argv:
    for ln in open(argv[argv.index("--seed-obs") + 1]):
        k, *ts = ln.split(); R[k] |= set(int(t) for t in ts)
RT = collections.defaultdict(list)   # b -> [c]
if "--rt" in argv:
    idx = {n: i for i, n in enumerate(names)}
    for ln in open(argv[argv.index("--rt") + 1]):
        a, b = ln.split(); RT[idx[b]].append(idx[a])
readers_in = {k: collections.defaultdict(list) for k in windows}
for k, cs in cells.items():
    for c in cs:
        for v in spc[c]:
            if v in FRONT: readers_in[k][v].append(c)
movers = {}
for k, W in windows.items():
    ms = [("ctl", v) for v in W if isinstance(v, int) and v in wof]
    if k != "env": ms += [("fr", v) for v in W if v in readers_in[k]]
    if any(v in ENVVARS for v in W): ms.append(("env", None))
    movers[k] = ms
KF = {}
def kf(A, B):
    if (A, B) not in KF:
        sh = [v for v in windows[A] if v in pos[B]]
        KF[(A, B)] = ([pos[A][v] for v in sh], [pos[B][v] for v in sh])
    return KF[(A, B)]
def asg(W, t): return {v: bool((t >> p) & 1) for p, v in enumerate(W)}
def out_of(u, d):
    return g["evalnode"](u, d, {}) if u not in d else d[u]
def blocked(b, t, K):
    """RT: b blocked if some c with order (c before b) in the same window K is excited in t"""
    for c in RT.get(b, ()):
        if wof.get(c) == K and exc(c, t): return True
    return False
def mover_keys(m, K):
    """keys (on K ∩ W_m) of tuples of m's window where m is enabled (excited and not RT-blocked)"""
    mk = wof[m]; pa, pb = kf(K, mk)
    return pa, set(key(t, pb) for t in R[mk] if exc(m, t) and not blocked(m, t, mk))
def env_keys(K):
    pa, pb = kf(K, "env"); out = collections.defaultdict(set); effs = {}
    for t in R["env"]:
        d = asg(windows["env"], t)
        for nm_, eff in env_moves(d): out[nm_].add(key(t, pb)); effs[nm_] = eff
    return pa, out, effs
changed = True; sweep = 0
while changed:
    changed = False; sweep += 1; added = 0
    for K, W in windows.items():
        new = set()
        for kind, m in movers[K]:
            if kind == "ctl":
                b = 1 << pos[K][m]
                if wof[m] == K:
                    for t in R[K]:
                        if exc(m, t) and not blocked(m, t, K): new.add(t ^ b)
                else:
                    pa, EK = mover_keys(m, K)
                    for t in R[K]:
                        if key(t, pa) in EK: new.add(t ^ b)
            elif kind == "fr":
                b = 1 << pos[K][m]
                for t in R[K]:
                    if all(Ftab[c][key(t, sp[c])] == Ftab[c][key(t ^ b, sp[c])] for c in readers_in[K][m]): new.add(t ^ b)
            else:
                pa, EKs, effs = env_keys(K)
                for nm_, ks in EKs.items():
                    for t in R[K]:
                        if key(t, pa) in ks:
                            t2 = t
                            for v, bb in effs[nm_].items():
                                if v in pos[K]:
                                    p = pos[K][v]; t2 = (t2 | (1 << p)) if bb else (t2 & ~(1 << p))
                            new.add(t2)
        n0 = len(R[K]); R[K] |= new
        if len(R[K]) != n0: changed = True; added += len(R[K]) - n0
    print("sweep", sweep, "added", added, "total", sum(len(r) for r in R.values()), file=sys.stderr)
# persistence check
viol = collections.Counter()
for K, cs in cells.items():
    for c in cs:
        for kind, m in movers[K]:
            if kind != "ctl" or m == c: continue
            b = 1 << pos[K][m]
            if wof[m] == K:
                for t in R[K]:
                    if exc(c, t) and exc(m, t) and not blocked(m, t, K) and not blocked(c, t, K) and not exc(c, t ^ b): viol[(c, m)] += 1
            else:
                pa, EK = mover_keys(m, K)
                for t in R[K]:
                    if exc(c, t) and not blocked(c, t, K) and key(t, pa) in EK and not exc(c, t ^ b): viol[(c, m)] += 1
nmf = lambda v: bel.get(names[v], names[v]).replace("bridge_i.udut.", "")
print("R total", sum(len(r) for r in R.values()), "max", max(len(r) for r in R.values()))
print("flagged (node, mover) pairs:", len(viol), "on", len(set(c for c, _ in viol)), "nodes")
for (c, m), n in viol.most_common(40): print("  ", n, nmf(c), "disabled by", nmf(m))
