"""ternary check at each bank opening: with the bank latches that change at this open set to X (and, variant 2, ALL
bank latches X), is each unchanged bank latch's D definite and equal to its held value?  leaves = latches, exact,
env, const; leaves outside the bank take their run value at the open read time.  usage: tern.py HIST.pkl c"""
import sys, pickle, itertools, functools
from bisect import bisect_right
sys.path.insert(0, "/tmp/claude-0/bsub1/tocc")
from classify import load, lut
C = load(); g = C["gates"]; nm = C["names"]; idx = {n: i for i, n in enumerate(nm)}; EX = C["EXACT"]
H = pickle.load(open(sys.argv[1], "rb")); c = int(sys.argv[2]); hist = H["hist"]; t0 = H["R"] - 1
def val(n, t):
    if n not in hist: return False
    b, ts = hist[n]; return b ^ (bisect_right(ts, t) % 2 == 1)
EN = idx["SLICE_X30Y76.A6"]
bank = [q for q, (fb, en) in C["LATCH"].items() if any(g[q]["pins"][p]["src"] == EN for p, v in en)]
evs = [x for x in hist[EN][1] if x > t0]
def run(te, Xset, tag):
    memo = {}
    def ev(n, t):
        key = n
        if key in memo: return memo[key]
        if n in Xset: r = None
        elif n in C["LATCH"] or n in EX or n not in g or n in C["const"] or g[n]["k"] == 0: r = val(n, t)
        else:
            G = g[n]; ins = []
            for p in G["pins"]:
                ins.append(ev(p["src"], t) if p["live"] else False)
            xs_ = [j for j, v in enumerate(ins) if v is None]; outs = set()
            for bits in itertools.product([False, True], repeat=len(xs_)):
                f = list(ins)
                for j, b in zip(xs_, bits): f[j] = b
                outs.add(bool(lut(G["init"], G["k"], f)))
                if len(outs) == 2: break
            r = outs.pop() if len(outs) == 1 else None
        memo[key] = r; return r
    ok = bad = und = 0; ex = []
    for q in bank:
        if q in Xset and tag == "changing": continue
        fb, en = C["LATCH"][q]; pe = [p for p, v in en][0]
        Dp = [j for j, p in enumerate(g[q]["pins"]) if p["live"] and j not in fb and j != pe and p["src"] not in C["const"]]
        qv = val(q, te - 1)
        # latch output with en open, fb = held value, D ternary
        G = g[q]; ins = []
        for j, p in enumerate(G["pins"]):
            if not p["live"]: ins.append(False)
            elif j == pe: ins.append(None)          # enable X (U' phase)
            elif j in fb: ins.append(qv)
            else: ins.append(ev(p["src"], te))
        xs_ = [j for j, v in enumerate(ins) if v is None]; outs = set()
        for bits in itertools.product([False, True], repeat=len(xs_)):
            f = list(ins)
            for j, b in zip(xs_, bits): f[j] = b
            outs.add(bool(lut(G["init"], G["k"], f)))
        if outs == {qv}: ok += 1
        elif len(outs) == 2: und += 1; ex.append(nm[q])
        else: bad += 1
    return ok, und, bad, ex
for k, te in enumerate(evs):
    if k % 2: continue
    tr = te + 300
    chg = set(q for q in bank if val(q, te - 1) != val(q, te + 20000))
    for tag, X in (("changing", chg), ("all-bank", set(bank))):
        ok, und, bad, ex = run(tr, X, tag)
        print("c=%d open k=%d @%d: X = %s (%d latches): Q held by U' (en X, fb=Q, D ternary) ok %d, undetermined %d %s, wrong %d" % (c, k, te, tag, len(X), ok, und, ex[:6], bad))
