#!/usr/bin/env python3
"""C-8r: test H_WALK (Formal/Net/CapstoneCutSpine.lean `WalkOK`) on concrete inputs.

For each (a, b): run the GcdHw token graph (C-8i's importer, bdc's fusion plan) from
init a b to quiescence with a concrete interpreter (deterministic; the graph is
confluent), record every channel's history H (= init ++ produced), then walk the control
token over the CIRCUIT spine exactly as `walk` does (nxt: link/forkG/bjoin/steerC/amerge,
steer select = sel2 of the stream solution = H(cond) periodic, the CIRCUIT network parsed
from CapstoneNet.lean) and check WalkOK at every arrival at an arbiter stage: the stage's
oracle (W.om from tab.om: lab2/hi3/lo3 over H) at the stage's output count must name the
input the walk arrives on. Also checks the walk ends (reaches a sink) and that the walk's
visit count of every GcdHw spine channel's first segment equals that channel's history length.
Usage: walkcheck.py [N_random]
"""
import os, re, sys, random
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "formal", "tools", "dfimport"))
import mlir2lean  # noqa: E402

M = lambda w: 1 << w
def flip(w, a): return (a % M(w) + (M(w - 1) if w >= 1 else 0)) % M(w)
def cmpi(p, w, a, b):
    x, y = a % M(w), b % M(w); sx, sy = flip(w, a), flip(w, b)
    return 1 if {"eq": x == y, "ne": x != y, "ult": x < y, "ule": x <= y, "ugt": y < x, "uge": y <= x,
                 "slt": sx < sy, "sle": sx <= sy, "sgt": sy < sx, "sge": sy <= sx}[p] else 0
def shrsi(w, a, b):
    if a % M(w) < M(w - 1): return (a % M(w)) >> b
    return (M(w) - 1) - ((M(w) - 1 - a % M(w)) >> b)
def ev(e, env):
    t = e[0]
    if t == "var": return env[e[1]] if e[1] < len(env) else 0
    if t == "lit": return e[1]
    if t == "un":
        o, w, a = e[1], e[2], ev(e[3], env)
        if o in ("trunci", "extui"): return a % M(w)
        dw = o[1]
        return a % M(w) if a % M(w) < M(w - 1) else a % M(w) + M(dw) - M(w)
    if t == "bin":
        o, w, a, b = e[1], e[2], ev(e[3], env), ev(e[4], env)
        if isinstance(o, tuple): return cmpi(o[1], w, a, b)
        return {"addi": lambda: (a + b) % M(w), "subi": lambda: (a % M(w) + M(w) - b % M(w)) % M(w),
                "muli": lambda: (a * b) % M(w), "andi": lambda: (a & b) % M(w),
                "ori": lambda: (a | b) % M(w), "xori": lambda: (a ^ b) % M(w),
                "shli": lambda: (a << b) % M(w), "shrui": lambda: (a % M(w)) >> b,
                "shrsi": lambda: shrsi(w, a, b)}[o]()
    s = ev(e[1], env)
    return ev(e[2], env) if s % 2 == 1 else ev(e[3], env)

g = mlir2lean.Graph(mlir2lean.default_mlir())
rules = list(g.rules)
NG = g.N

def token_run(a, b):
    st = [[] for _ in range(NG)]
    st[0], st[1], st[2] = [a], [b], [0]
    H = [list(x) for x in st]
    steps = 0
    while True:
        fired = False
        for r in rules:
            k = r[0]
            if k == "mux":
                s, ds, o, iw = r[1], r[2], r[3], r[4]
                if not st[s]: continue
                d = ds[st[s][0] % M(iw)]
                if not st[d]: continue
                v = st[d][0]; st[s] = st[s][1:]; st[d] = st[d][1:]
                st[o].append(v); H[o].append(v); fired = True
            else:
                ins = mlir2lean.Graph.rule_ins(r)
                if any(not st[c] for c in ins): continue
                vs = [st[c][0] for c in ins]
                for c in ins: st[c] = st[c][1:]
                out = []
                if k == "comp": out = [(r[2], ev(r[3], vs))]
                elif k == "fork": out = [(c, vs[0]) for c in r[2]]
                elif k == "branch": out = [((r[3] if vs[0] % 2 == 1 else r[4]), vs[1])]
                elif k == "cm": out = [(r[2], vs[0]), (r[3], r[4])]
                for c, v in out: st[c].append(v); H[c].append(v)
                fired = True
            if fired: break
        if not fired: break
        steps += 1
        assert steps < 10 ** 6
    return st, H

# ---- the circuit network
net = open(os.path.join(ROOT, "formal", "lean", "Formal", "Net", "CapstoneNet.lean")).read()
names = re.findall(r'"([^"]*)"', re.search(r"def chanNames : List String := \[(.*?)\]\n", net).group(1))
NC = len(names)
opsL = re.search(r"def ops : List \(K NC\) := \[\n(.*?)\n\]", net, re.S).group(1).split("\n")
consT = [int(x) for x in re.search(r"def consT : List \(Fin NO\) := \[(.*?)\]", net).group(1).split(",")]
descs = re.search(r"desc := \[(.*?)\]\n", net).group(1)
descL = re.findall(r"\.(hist \d+ \d+|copy \d+|zero|cmz \d+ \d+ \d+|bj .*?\[[\d, ]*\])", descs)
assert len(descL) == NC, (len(descL), NC)
omL = re.findall(r"\.(lab2|hi3|lo3) (\d+)", re.search(r"om := \[(.*?)\]", net).group(1))
spL = eval(open(os.path.join(HERE, "spL.txt")).read().replace("true", "True").replace("false", "False")) \
    if os.path.exists(os.path.join(HERE, "spL.txt")) else None
spine = {int(x) for x in re.search(r"def spine : List Nat := \[(.*?)\]",
         open(os.path.join(ROOT, "formal", "lean", "Formal", "Net", "GcdHw.lean")).read()).group(1).split(",")}
if spL is None:
    spL = [False] * NC
    bj = {}
    for o in opsL:
        m = re.match(r"\s*K\.bjoin \[(\d+), (\d+)\] (\d+)", o)
        if m: bj[int(m.group(3))] = int(m.group(2))
    for c, n in enumerate(names):
        m = re.fullmatch(r"g(\d+)\.\d+", n)
        if (m and int(m.group(1)) in spine) or n.startswith("z") or n.startswith("acc"): spL[c] = True
    for c, n in enumerate(names):
        if n.startswith("j") and spL[bj[c]]: spL[c] = True

def parse_op(s):
    s = s.strip().rstrip(",")
    k = re.match(r"K\.(\w+)", s).group(1)
    if k == "link":
        i, o = map(int, re.match(r"K\.link (\d+) (\d+)", s).groups()); return (k, i, o)
    if k == "forkG":
        m = re.match(r"K\.forkG (\d+) \[([\d, ]*)\]", s); return (k, int(m.group(1)), [int(x) for x in m.group(2).split(",")])
    if k == "bjoin":
        m = re.match(r"K\.bjoin \[([\d, ]*)\] (\d+) (.*)$", s); return (k, [int(x) for x in m.group(1).split(",")], int(m.group(2)), m.group(3))
    if k == "steerC":
        return (k,) + tuple(map(int, re.match(r"K\.steerC (\d+) (\d+) (\d+)", s).groups()))
    if k == "amerge":
        return (k,) + tuple(map(int, re.match(r"K\.amerge (\d+) (\d+) (\d+) (\d+)", s).groups()))
    return (k,)
ops = [parse_op(s) for s in opsL]

def perL(Lst, d, k): return d if not Lst else Lst[k % len(Lst)]
def refT(H, c, k, depth=0):
    assert depth < 64
    d = descL[c]
    if d.startswith("hist"):
        _, h, dd = d.split(); return perL(H[int(h)], int(dd), k)
    if d.startswith("copy"): return refT(H, int(d.split()[1]), k, depth + 1)
    if d == "zero": return 0
    raise ValueError(("refT", names[c], d))
def selj(H, j, k):
    o = ops[[n for n, op in enumerate(ops) if op[0] == "bjoin" and op[2] == j][0]]
    assert o[3].startswith("(.var 0) "), o
    return (refT(H, o[1][0], k) % 2 == 1) != (NEG == "2")
NEG = os.environ.get("NEG")  # negative control: NEG=1 inverts stage 0's oracle; NEG=2 inverts every steer select
def om(H, w, k):
    if NEG == "1" and w == 0: return not om0(H, w, k)
    return om0(H, w, k)
def om0(H, w, k):
    kind, gi = omL[w]; L = H[int(gi)]
    if kind == "lab2": return perL(L, 0, k) % 2 == 1
    if kind == "hi3": return perL(L, 0, k) % 4 == 2
    return perL([v for v in L if v % 4 != 2], 0, k) % 4 == 1

def walk(H):
    W = [0] * NC
    cur, steps, arrivals = 2, 0, 0
    while cur is not None:
        k = W[cur]; o = ops[consT[cur]]; kind = o[0]
        nxt = None
        if kind == "link": nxt = o[2] if spL[o[2]] else None
        elif kind == "forkG":
            f = [x for x in o[2] if spL[x]]; nxt = f[0] if f else None
        elif kind == "bjoin": nxt = o[2] if spL[o[2]] else None
        elif kind == "steerC":
            nxt = (o[2] if selj(H, cur, k) else o[3]) if spL[o[2]] else None
        elif kind == "amerge":
            x, y, z, w = o[1:]
            want = (cur == y)
            if om(H, w, W[z]) != want:
                return False, f"WalkOK fails at step {steps}: {names[cur]} -> {names[z]} index {W[z]}"
            arrivals += 1
            nxt = z
        W[cur] += 1
        cur = nxt; steps += 1
        if steps > 10 ** 6: return False, "walk does not end"
    for c, n in enumerate(names):
        m = re.fullmatch(r"g(\d+)\.0", n)
        if m and int(m.group(1)) in spine and int(m.group(1)) != 2:
            if W[c] != len(H[int(m.group(1))]):
                return False, f"visit count of {n} = {W[c]} but history length {len(H[int(m.group(1))])}"
    return True, f"{steps} steps, {arrivals} arbiter arrivals"

if __name__ == "__main__":
    nrand = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    rnd = random.Random(8)
    vecs = [(0, 0), (0, 5), (5, 0), (1, 1), (12, 18), (18, 12), (7, 7), (64, 48), (1, 2 ** 31 - 1),
            (2 ** 31 - 1, 2 ** 31 - 2), (2 ** 30, 2 ** 20), (3 * 2 ** 10, 9 * 2 ** 7)]
    vecs += [(rnd.randrange(2 ** 31), rnd.randrange(2 ** 31)) for _ in range(nrand)]
    vecs += [(rnd.randrange(1 << rnd.randrange(1, 31)) << rnd.randrange(8),
              rnd.randrange(1 << rnd.randrange(1, 31)) << rnd.randrange(8)) for _ in range(nrand)]
    bad = 0
    for a, b in vecs:
        a %= 2 ** 31; b %= 2 ** 31
        st, H = token_run(a, b)
        import math
        ok_out = H[250] == [math.gcd(a, b)]
        ok, msg = walk(H)
        if not (ok and ok_out): bad += 1
        print(f"a={a} b={b}: run out0={H[250]} ({'ok' if ok_out else 'WRONG'}); walk: {'ok' if ok else 'FAIL'} {msg}")
    print("walkcheck:", "ok" if bad == 0 else f"{bad} FAILURES", f"({len(vecs)} vectors)")
    sys.exit(1 if bad else 0)
