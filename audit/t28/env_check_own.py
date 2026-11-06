# T28: own check of Spec.Env (R, su, Δo), SeqEnv, ArbOK T and Correct on shard C's k84b dump, against the Lean
# boundary/arbiters of Formal/Target/NetPS/All.lean (parsed here), with the behaviour extended CONSTANT after tend
# (the simulator reported an empty queue). All signals are piecewise constant, so every condition is evaluated at every
# change time of the signals it involves (and at R, and in the final state for the liveness clauses).
# usage: env_check_own.py ALL.lean DUMP.json R su Δo T va0,va1 vb0,vb1
import json, re, sys, bisect
src = open(sys.argv[1]).read(); dump = json.load(open(sys.argv[2]))
R, su, Do, T = map(int, sys.argv[3:7]); va = list(map(int, sys.argv[7].split(","))); vb = list(map(int, sys.argv[8].split(",")))
n = len(va)
D = {int(k): (v[0], v[1]) for k, v in dump["nodes"].items()}; tend = dump["tend"]
def V(nd, t): v0, fl = D.get(nd, (False, [])); return v0 ^ (bisect.bisect_right(fl, t) % 2 == 1)
def flips(nd): return D.get(nd, (False, []))[1]
b = re.search(r"def boundary : Boundary :=(.*?)\n\nend", src, re.S).group(1)
def ch(name):
    m = re.search(name + r" := ⟨(\d+), (\d+), \[([\d, ]*)\]⟩", b); return int(m.group(1)), int(m.group(2)), [int(x) for x in m.group(3).split(",") if x.strip()]
rst = int(re.search(r"rst := (\d+)", b).group(1))
A, B_, S, O, P = ch("a"), ch("b"), ch("start"), ch("out0"), ch("pend")
arbs = [(int(q), [int(x) for x in ins.split(",")]) for q, ins in re.findall(r"⟨(\d+), \[([\d, ]+)\]⟩", re.search(r"def arbs : List ArbNodes := \[(.*?)\]\n", src, re.S).group(1))]
def bus(d, t): return sum((1 << i) for i, nd in enumerate(d) if V(nd, t))
def rises(nd, t): return sum(1 for f in flips(nd) if R <= f - 1 and f <= t and V(nd, f) and not V(nd, f - 1))
def times(*nds): return sorted(set([R] + [f for nd in nds for f in flips(nd) if f >= R] + [f - 1 for nd in nds for f in flips(nd) if f - 1 >= R]))
bad = []
# reset
if any(not V(rst, t) for t in [0] + [f - 1 for f in flips(rst) if f - 1 < R]): bad.append("rst not high on [0,R)")
if any(V(rst, t) for t in [R] + [f for f in flips(rst) if f >= R]): bad.append("rst not low from R")
if any(x >= 2 ** 31 for x in va + vb): bad.append("value >= 2^31")
off = lambda k: k < n
def envin(name, c, vals):
    r, a, d = c
    if any(V(r, t) for t in [0] + [f - 1 for f in flips(r) if f - 1 <= R] if t <= R): bad.append(name + ": req high in [0,R]")
    for f in flips(r):                                   # ReqMoves: r(t+1) != r(t) -> r(t) = a(t)
        if f - 1 >= R and V(r, f - 1) != V(a, f - 1): bad.append(name + ": ReqMoves at %d" % f)
    for t in times(r, a, *d):
        if V(r, t) and not off(rises(r, t) - 1): bad.append(name + ": req high beyond offered at %d" % t)
        if (V(r, t) or V(a, t)) and rises(r, t) >= 1 and bus(d, t) != vals[rises(r, t) - 1]: bad.append(name + ": data wrong at %d" % t)
    for f in flips(r):
        if f - 1 >= R and V(r, f) and not V(r, f - 1):
            k = rises(r, f) - 1
            for s in sorted(set([max(0, f - su), f] + [x for nd in d for x in flips(nd) if f - su <= x <= f])):
                if bus(d, s) != vals[k]: bad.append(name + ": setup data wrong before rise %d at %d" % (f, s))
    rf, af = V(r, tend + 10 ** 6), V(a, tend + 10 ** 6)  # final (constant) state
    if rf == af and (rf or off(rises(r, tend + 10 ** 6))): bad.append(name + ": ReqLive owed in final state")
def envout(name, c):
    r, a, d = c
    if any(V(a, t) for t in [0] + [f - 1 for f in flips(a) if f - 1 <= R] if t <= R): bad.append(name + ": ack high in [0,R]")
    for f in flips(a):
        if f - 1 >= R and V(a, f - 1) == V(r, f - 1): bad.append(name + ": AckMoves at %d" % f)
        if f - 1 >= R and V(a, f) and not V(a, f - 1):
            for s in [max(0, f - Do), f] + [x for x in flips(r) if f - Do <= x <= f]:
                if not V(r, s): bad.append(name + ": ack rose < Δo after req at %d" % f)
    if V(a, tend + 10 ** 6) != V(r, tend + 10 ** 6): bad.append(name + ": AckLive owed in final state")
envin("a", A, va); envin("b", B_, vb); envin("start", S, [0] * n); envout("out0", O); envout("pend", P)
seqbad = []
for nm, c in (("a", A), ("b", B_), ("start", S)):
    for f in flips(c[0]):
        t = f - 1
        if t >= R and V(c[0], f) and not V(c[0], t):
            if not (rises(c[0], t) <= rises(O[1], t) and not V(O[0], t) and not V(O[1], t)): seqbad.append((nm, f))
# ArbOK T: every q flip at tau needs an input flip at >= tau - T (inputs constant on [tau-1-T, tau] would forbid it)
arbbad = []; minT = 0
for q, ins in arbs:
    fi = sorted(f for nd in ins for f in flips(nd))
    for tau in flips(q):
        j = bisect.bisect_right(fi, tau) - 1
        last = fi[j] if j >= 0 else -10 ** 9
        minT = max(minT, tau - last)
        if last < tau - T: arbbad.append((q, tau, last))
print("Env violations:", len(bad), bad[:6]); print("SeqEnv violations:", len(seqbad), seqbad[:4])
print("ArbOK(T=%d) violations:" % T, len(arbbad), arbbad[:4], "; smallest T it holds for:", minT)
outs = [(f, bus(O[2], f + Do)) for f in flips(O[0]) if V(O[0], f)]
print("out0 rises (time, data at +Δo):", outs, " rises(out0.req) final:", rises(O[0], tend + 10 ** 6), "of", n)
print("Correct's out0 liveness: final out0 req/ack =", V(O[0], tend + 10 ** 6), V(O[1], tend + 10 ** 6), "-> owed rise" if not V(O[0], tend + 10 ** 6) and rises(O[0], tend + 10 ** 6) < n else "")
