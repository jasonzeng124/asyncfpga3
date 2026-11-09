import sys, os, pickle, collections
c_ = sys.argv[1]
sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/arbh/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
PS = os.environ.get("PAIR", "")
D = pickle.load(open("/tmp/claude-0/arbh/datal_c%s%s.pkl" % (c_, PS), "rb"))
def mid_(v, w): return dl[(v, w)][2] if (v, w) in dl else 1
# registers (latches) in z's data cone, with their exact enables
def cone_latches(z):
    seen = set(); todo = [z]; L = set()
    while todo:
        u = todo.pop()
        if u in seen: continue
        seen.add(u)
        if u in C["LATCH"]: L.add(u); continue
        if u in g and u not in EX:
            for p in C["live"][u]:
                if p["src"] not in EX and p["src"] not in C["const"]: todo.append(p["src"])
    return L
cat = collections.Counter(); ex = []; edges = {}
for x in D["G"]:
    if len(x) != 7: continue
    v, z, ms, me, cz, st, en_ = x
    if min(ms, me) >= 0 or en_ is None: continue
    E = eid[en_]; tE = et[E]; S = eid[st]
    # first re-opening (after S) of each register enable in z's cone
    ens_ = set()
    for l in cone_latches(z):
        for p, val_ in C["LATCH"][l][1]:
            s_ = g[l]["pins"][p]["src"]
            if s_ in EX: ens_.add((s_, val_, g[l]["pins"][p]["win"][c][0]))
    worst = None
    for (e_, val_, elo) in ens_:
        # opening event: enable becomes val_; first such event after S
        for k, t in enumerate(ev[e_]):
            if t > et[S] and (bool(s0[e_]) ^ ((k + 1) % 2 == 1)) == bool(val_):
                B = eid[(e_, k)]
                s = sepAny(E, B)[0]
                need = hi_(v, en_[0]) - pwin_ if False else None
                gap = t - tE
                key = (e_, k)
                if worst is None or (s if s > -INF else -10**9) < (worst[0] if worst[0] > -INF else -10**9): worst = (s, nm[e_], k, gap)
                break
    if worst is None: cat["no register reopen after S in the run"] += 1; continue
    s, en_name, k, gap = worst
    kind = "reopen before E (gap %s)" % ("<0") if gap < 0 else ("reopen after E, Sep %s" % ("none" if s == -INF else ">= 0"))
    cat[kind] += 1
    edges[(en_name, k)] = (s, gap, nm[v], nm[z])
print("[c=%s%s] failing guards: worst register re-open in z's cone relative to E:" % (c_, PS), dict(cat))
for k_, (s, gap, vn, zn) in sorted(edges.items(), key=lambda x: x[1][1])[:12]:
    print("   reopen %s(%d): Sep(E -> reopen) %s, sim gap %d ps, e.g. reader %s z %s" % (k_[0], k_[1], s, gap, vn, zn))
