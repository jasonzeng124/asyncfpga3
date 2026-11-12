"""Shard C (UNTRUSTED): one run of the latches-first machine (huffx semantics, one operand pair, the RT orders
applied STRICTLY), recording every node change as an event.
usage: run.py prep.txt init.txt a b rt.txt seed out.events
out.events: header lines, then one line per event: node move round   (round -1 = the move itself)"""
import sys, random, math
sys.path.insert(0, "/tmp/claude-0/occ")
from net import Net
prep, initf, A, B, rtf, seed, outf = sys.argv[1:8]; A = int(A); B = int(B); seed = int(seed)
N = Net(prep)
s0 = open(initf).read().strip(); N.val = [int(c) for c in s0]
val = N.val
# sanity: comb consistent with init
bad = sum(1 for g in N.comb if N.ev(g) != val[g[0]]); assert bad == 0, bad
latches = [s for s, g in enumerate(N.stor) if g[4]]; ctl = [s for s, g in enumerate(N.stor) if not g[4]]
assert not any(N.excited(s) for s in latches), "initial state not latch-stable"
byName = {N.names[g[0]]: s for s, g in enumerate(N.stor)}
rt = [(byName[a], byName[b]) for a, b in (l.split() for l in open(rtf) if l.strip())]
blockers = {}
for c, b in rt: blockers.setdefault(b, []).append(c)
want = math.gcd(A, B)
k = kout = 0; NP = 1
events = []  # (node, move, round)
def setn(n, v, mv, rd):
    if val[n] != v: val[n] = v; events.append((n, mv, rd)); return True
    return False
def moves():
    m = [s for s in ctl if N.excited(s)]
    req, pa, oa, orq = val[N.REQ], val[N.PACK], val[N.OACK], val[N.OREQ]
    if not req and not val[N.AACK] and not val[N.BACK] and not val[N.SACK] and not pa and k < NP and k <= kout and not orq and not oa: m.append(-1)
    if req and val[N.AACK] and val[N.BACK] and val[N.SACK] and pa: m.append(-2)
    if req and not pa: m.append(-3)
    if not req and pa: m.append(-4)
    if orq and not oa: m.append(-5)
    if not orq and oa: m.append(-6)
    return m
rng = random.Random(seed); nmv = 0; fallback = 0; wrong = 0; maxround = 0
while True:
    ms = moves()
    if not ms: break
    ms2 = [m for m in ms if not (m >= 0 and any(N.excited(c) for c in blockers.get(m, ())))]
    if not ms2: fallback += 1; ms2 = ms
    mv = rng.choice(ms2); ch = []
    if mv >= 0:
        o = N.stor[mv][0]; setn(o, val[o] ^ 1, nmv, -1); ch = [o]
    elif mv == -1:
        for i, x in enumerate(N.AD):
            if setn(x, (A >> i) & 1, nmv, -1): ch.append(x)
        for i, x in enumerate(N.BD):
            if setn(x, (B >> i) & 1, nmv, -1): ch.append(x)
        setn(N.REQ, 1, nmv, -1); ch.append(N.REQ); k += 1
    elif mv == -2: setn(N.REQ, 0, nmv, -1); ch = [N.REQ]
    elif mv == -3: setn(N.PACK, 1, nmv, -1); ch = [N.PACK]
    elif mv == -4: setn(N.PACK, 0, nmv, -1); ch = [N.PACK]
    elif mv == -5:
        got = sum(val[x] << i for i, x in enumerate(N.OD))
        if got != want: wrong += 1
        setn(N.OACK, 1, nmv, -1); ch = [N.OACK]; kout += 1
    elif mv == -6: setn(N.OACK, 0, nmv, -1); ch = [N.OACK]
    N.settle(ch)
    rd = 0
    while True:
        cand = set()
        for n in ch:
            for s in N.fanStor[n]:
                if N.stor[s][4]: cand.add(s)
        # comb nodes changed are not tracked: recompute candidates from all latches reading any comb change
        ex = [s for s in latches if N.excited(s)] if True else []
        if not ex: break
        ch = []
        for s in ex:
            o = N.stor[s][0]; setn(o, val[o] ^ 1, nmv, rd); ch.append(o)
        N.settle(ch); rd += 1; maxround = max(maxround, rd)
        assert rd < 10000
    nmv += 1
fin = k == NP and kout == NP and not val[N.REQ] and not val[N.PACK] and not val[N.OACK] and not val[N.OREQ]
print("run %d,%d seed %d: moves %d events %d final %s wrong %d rt-fallbacks %d maxround %d" % (A, B, seed, nmv, len(events), fin, wrong, fallback, maxround))
with open(outf, "w") as f:
    f.write("# pair %d %d seed %d moves %d final %d wrong %d fallback %d\n" % (A, B, seed, nmv, fin, wrong, fallback))
    for n, mv, rd in events: f.write("%d %d %d\n" % (n, mv, rd))
