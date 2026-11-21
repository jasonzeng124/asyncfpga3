import sys, pickle, collections
c = sys.argv[1]; extra = sys.argv[2:]
sys.argv = ["ao.py", c, "0", "--prevanc"] + extra
src = open("/tmp/claude-0/r1c/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
suf = "_prevanc" + ("_cyc" if CYC else "") + ("_causeanc" if CAUSEANC else "")
Q = pickle.load(open("/tmp/claude-0/r1c/q2_c%s%s.pkl" % (c, suf), "rb")); resid = Q["resid"]
P = pickle.load(open("/tmp/claude-0/r1c/ao_c%s%s.pkl" % (c, suf), "rb")); rt = P["rt"]
VC = vclock(rt)
cat = collections.Counter(); ex = collections.defaultdict(list)
for (v, kind, n, D) in resid:
    rstin = bs["rst"] in D
    # sources whose counted events exceed what v had read when its counted/next event fired
    nv = n[0]
    info = []
    for j, u in enumerate(D[1:], 1):
        if u == bs["rst"]: continue
        if (v, u) not in dl: continue
        # events of u read by v by the time of v's next event (or end)
        tnext = ev[v][nv] if nv < len(ev[v]) else 10**12
        tlast = ev[v][nv - 1] if nv else t0
        rd_at_last = sum(1 for t in ev[u] if t + dl[(v, u)][2] <= tlast)
        info.append((nm[u], n[j], rd_at_last))
    ahead = [x for x in info if x[1] > x[2] + 1]
    key = (kind, "CTRL" if v in C["CTRL"] else "comb", "rst in D" if rstin else "no rst",
           "source >=2 events ahead of v's last read" if ahead else "within one event")
    cat[key] += 1; ex[key].append((v, n, D, info))
print("[c=%s %s] residual %d" % (c, suf, len(resid)))
for k, n_ in cat.most_common(): print("  %3d %s" % (n_, k))
def detail(v, n, D):
    print("  NODE %s %s init %x n=%s" % (nm[v], "CTRL" if v in C["CTRL"] else "comb", g[v]["init"], n))
    for j, u in enumerate(D):
        print("    %-16s n=%d s0=%d ev=%s dly=%s" % (nm[u], n[j], s0[u], ev[u], dl.get((v, u), "")))
    for k in range(len(ev[v])):
        e = eid[(v, k)]
        print("    event %d t=%d alts %s" % (k, ev[v][k], [[(nm[el[p][0]], el[p][1]) for p in a] for a in alts[e]]))
shown = 0
for k in cat:
    for (v, n, D, info) in ex[k][:3]:
        if shown < 0: print(" example of", k); detail(v, n, D); shown += 1
