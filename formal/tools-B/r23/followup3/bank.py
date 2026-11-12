"""bank latches opened by SLICE_X30Y76.A6: per open event, Q old/new, D at the open read, D flips near the open,
and changing inputs of D's comb cone (to the first latch/exact node) in the window.  usage: bank.py HIST.pkl c"""
import sys, pickle, json
from bisect import bisect_right
sys.path.insert(0, "/tmp/claude-0/bsub1/tocc")
from classify import load
C = load(); g = C["gates"]; nm = C["names"]; idx = {n: i for i, n in enumerate(nm)}; EX = C["EXACT"]
H = pickle.load(open(sys.argv[1], "rb")); c = int(sys.argv[2]); hist = H["hist"]; t0 = H["R"] - 1
DS = H.get("DS")
def dly(v, j): return DS[v][j] if DS else g[v]["pins"][j]["win"][c][2]
def val(n, t):
    if n not in hist: return False
    b, ts = hist[n]; return b ^ (bisect_right(ts, t) % 2 == 1)
EN = idx["SLICE_X30Y76.A6"]
bank = [q for q, (fb, en) in C["LATCH"].items() if any(g[q]["pins"][p]["src"] == EN for p, v in en)]
print("latches enabled by X30Y76.A6:", len(bank), sorted(nm[q] for q in bank)[:40])
evs = [x for x in hist[EN][1] if x > t0]
print("X30Y76.A6 events:", evs)
def cone(u, depth=6):
    out = set(); st = [(u, 0)]
    while st:
        x, d = st.pop()
        if x in out: continue
        out.add(x)
        if x in EX or x in C["LATCH"] or x not in g or d >= depth: continue
        for p in g[x]["pins"]:
            if p["live"]: st.append((p["src"], d + 1))
    return out
res = []
for k, te in enumerate(evs):
    for q in sorted(bank, key=lambda q: nm[q]):
        fb, en = C["LATCH"][q]; pe, act = [(p, v) for p, v in en if g[q]["pins"][p]["src"] == EN][0]
        if val(EN, te) != bool(act): continue            # only openings
        de = dly(q, pe); topen = te + de
        nxt = [x for x in evs if x > te]; tclose = (nxt[0] + de) if nxt else 10**12
        qold = val(q, topen - 1); qnew = val(q, min(tclose, topen + 30000))
        qfl = [x for x in hist.get(q, (0, []))[1] if topen - 2000 <= x <= tclose]
        Dp = [j for j, p in enumerate(g[q]["pins"]) if p["live"] and j not in fb and j != pe and p["src"] not in C["const"]]
        rows = []
        for j in Dp:
            u = g[q]["pins"][j]["src"]; dd = dly(q, j)
            dfl = [x + dd for x in hist.get(u, (0, []))[1] if topen - 5000 <= x + dd <= topen + 15000]
            ins = []
            for w in cone(u):
                if w == u: continue
                f = [x for x in hist.get(w, (0, []))[1] if topen - 8000 <= x <= topen + 15000]
                if f: ins.append((nm[w], "EX" if w in EX else ("L" if w in C["LATCH"] else "d"), f[:4]))
            rows.append(dict(D=nm[u], D_at_open=int(val(u, topen - dd)), D_flips_at_pin_rel_open=[x - topen for x in dfl], cone_changes=ins[:8]))
        res.append(dict(k=k, open_event_t=te, latch=nm[q], Qold=int(qold), Qnew=int(qnew), Q_flips_rel=[x - topen for x in qfl], D=rows))
json.dump(res, open("/tmp/claude-0/bsub1/bank_c%d.json" % c, "w"), indent=1)
import collections
for k in sorted(set(r["k"] for r in res)):
    R = [r for r in res if r["k"] == k]
    same = sum(1 for r in R if r["Qold"] == r["Qnew"] and not r["Q_flips_rel"])
    dgl = sum(1 for r in R if any(len(d["D_flips_at_pin_rel_open"]) for d in r["D"]))
    print("open k=%d @%d: %d latches, Q unchanged %d, D flips within [-5,+15] ns of open read: %d" % (k, R[0]["open_event_t"], len(R), same, dgl))
    for r in R[:40]:
        if any(d["D_flips_at_pin_rel_open"] for d in r["D"]) or r["Q_flips_rel"]:
            print("   %s Q %d->%d Qflips %s  D %s" % (r["latch"], r["Qold"], r["Qnew"], r["Q_flips_rel"], [(d["D"], d["D_at_open"], d["D_flips_at_pin_rel_open"]) for d in r["D"]]))
