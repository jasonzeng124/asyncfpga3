"""leaves of the bank latches' D cones that change near each opening (in a run)"""
import sys, pickle, collections
from bisect import bisect_right
sys.path.insert(0, "/tmp/claude-0/bsub1/tocc")
from classify import load
C = load(); g = C["gates"]; nm = C["names"]; idx = {n: i for i, n in enumerate(nm)}; EX = C["EXACT"]
H = pickle.load(open(sys.argv[1], "rb")); c = int(sys.argv[2]); hist = H["hist"]; t0 = H["R"] - 1
EN = idx["SLICE_X30Y76.A6"]
bank = [q for q, (fb, en) in C["LATCH"].items() if any(g[q]["pins"][p]["src"] == EN for p, v in en)]
def leaves(u):
    out = set(); st = [u]; seen = set(); comb = set()
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x)
        if x in C["LATCH"] or x in EX or x not in g or x in C["const"] or g[x]["k"] == 0: out.add(x); continue
        comb.add(x)
        for p in g[x]["pins"]:
            if p["live"]: st.append(p["src"])
    return out, comb
evs = [x for x in hist[EN][1] if x > t0]
L = set(); CB = set()
for q in bank:
    fb, en = C["LATCH"][q]; pe = [p for p, v in en][0]
    for j, p in enumerate(g[q]["pins"]):
        if p["live"] and j not in fb and j != pe and p["src"] not in C["const"]:
            l, cb = leaves(p["src"]); L |= l; CB |= cb
print("bank D cones: %d comb gates, %d leaves (%d bank latches, %d exact, %d other latches, %d env/other)" % (len(CB), len(L), len(L & set(bank)), len(L & EX), len((L & set(C['LATCH'])) - set(bank)), len(L - EX - set(C['LATCH']))))
for k, te in enumerate(evs):
    if k % 2: continue
    ch = collections.defaultdict(list)
    for n in L | CB:
        for x in hist.get(n, (0, []))[1]:
            if te - 15000 <= x <= te + 15000: ch[n].append(x - te)
    lv = {nm[n]: v for n, v in ch.items() if n in L}; cb = {nm[n]: v for n, v in ch.items() if n in CB}
    print("open k=%d @%d: changing leaves %s" % (k, te, sorted(lv.items(), key=lambda x: x[1][0])))
    print("   changing comb cone gates (%d): %s" % (len(cb), sorted(cb.items(), key=lambda x: x[1][0])[:12]))
