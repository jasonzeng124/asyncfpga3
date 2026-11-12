#!/usr/bin/env python3
"""Token-level (Kahn) simulator of an imported bdc graph (Formal/Net/GcdHw.lean `rules`),
with SEVERAL input pairs offered at once (pipelined environment), to ask whether outputs
can leave out of order.  Semantics transcribed from Formal/Net/GcdHwLib.lean (Rule.fire,
natVI, Ops).  Exploratory tool: its findings are re-checked in Lean (Formal/Net/Pipe*).

usage: toksim.py [--lean F] a1,b1 a2,b2 ... [--runs N] [--seed S] [--policy random|young]
"""
import re, sys, random, argparse

def parse_rules(path):
    src = open(path).read()
    body = src[src.index("def rules : List Rule := ["):]
    lines = [l for l in body.splitlines()[1:] if l.strip().startswith(".")]
    return [parse_expr(l.split("--")[0].strip().rstrip(","))[0] for l in lines]

TOK = re.compile(r"\s*(\(|\)|\[|\]|,|\.[A-Za-z_]+|\d+)")
def tokens(s):
    pos, out = 0, []
    while pos < len(s):
        m = TOK.match(s, pos)
        if not m:
            if s[pos:].strip() == "": break
            raise ValueError(s[pos:])
        out.append(m.group(1)); pos = m.end()
    return out

def parse_expr(s):
    t = tokens(s); v, i = term(t, 0); return v, i

def term(t, i):
    x = t[i]
    if x == "(":
        args, i = seq(t, i + 1, ")")
        return (args[0] if len(args) == 1 else tuple(args)), i
    if x == "[":
        args, i = list_(t, i + 1); return args, i
    if x.isdigit(): return int(x), i + 1
    # constructor applied to exactly ARITY[name] following terms
    name = x[1:]; i += 1; args = []
    for _ in range(ARITY.get(name, 0)):
        a, i = term(t, i); args.append(a)
    return (name, *args), i

ARITY = dict(var=1, lit=1, un=3, bin=4, sel=3, cmpi=1, extsi=1,
             comp=3, fork=2, branch=4, mux=4, cm=4, sink=1)

def seq(t, i, close):
    args = []
    while t[i] != close:
        a, i = term(t, i); args.append(a)
    return args, i + 1

def list_(t, i):
    args = []
    while t[i] != "]":
        if t[i] == ",": i += 1; continue
        a, i = term(t, i); args.append(a)
    return args, i + 1

M = lambda w: 1 << w
def flip(w, a): return (a % M(w) + (M(w - 1) if w >= 1 else 0)) % M(w)
def cmpi(p, w, a, b):
    x, y, sx, sy = a % M(w), b % M(w), flip(w, a), flip(w, b)
    return int({"eq": x == y, "ne": x != y, "ult": x < y, "ule": x <= y, "ugt": y < x, "uge": y <= x,
                "slt": sx < sy, "sle": sx <= sy, "sgt": sy < sx, "sge": sy <= sx}[p])
def shrsi(w, a, b):
    a %= M(w)
    return a >> b if a < M(w - 1) else (M(w) - 1) - ((M(w) - 1 - a) >> b)

def ev(e, env):
    k = e[0]
    if k == "var": return env[e[1]] if e[1] < len(env) else 0
    if k == "lit": return e[1]
    if k == "un":
        o, w, a = e[1], e[2], ev(e[3], env); on = o[0]
        if on in ("trunci", "extui"): return a % M(w)
        raise ValueError(o)
    if k == "bin":
        o, w, a, b = e[1], e[2], ev(e[3], env), ev(e[4], env); on = o[0]
        if on == "cmpi": return cmpi(o[1][0], w, a, b)
        return {"addi": lambda: (a + b) % M(w), "subi": lambda: (a % M(w) + M(w) - b % M(w)) % M(w),
                "muli": lambda: (a * b) % M(w), "andi": lambda: (a & b) % M(w), "ori": lambda: (a | b) % M(w),
                "xori": lambda: (a ^ b) % M(w), "shli": lambda: (a << b) % M(w), "shrsi": lambda: shrsi(w, a, b),
                "shrui": lambda: (a % M(w)) >> b}[on]()
    if k == "sel":
        return ev(e[2], env) if ev(e[1], env) % 2 == 1 else ev(e[3], env)
    raise ValueError(e)

def fire(r, st):
    """Returns (pops: dict chan->n, pushes: list (chan, val)) or None."""
    k = r[0]
    if k == "mux":
        s, ds, o, iw = r[1], r[2], r[3], r[4]
        if not st[s]: return None
        j = st[s][0] % M(iw)
        if j >= len(ds): return None
        d = ds[j]
        if d == s or not st[d]: return None
        return {s: 1, d: 1}, [(o, st[d][0])]
    ins = {"comp": lambda: r[1], "fork": lambda: [r[1]], "branch": lambda: [r[1], r[2]],
           "cm": lambda: [r[1]], "sink": lambda: [r[1]]}[k]()
    if any(not st[c] for c in ins): return None
    vs = [st[c][0] for c in ins]
    pops = {}
    for c in ins: pops[c] = pops.get(c, 0) + 1
    if k == "comp": return pops, [(r[2], ev(r[3], vs))]
    if k == "fork": return pops, [(c, vs[0]) for c in r[2]]
    if k == "branch": return pops, [((r[3] if vs[0] % 2 == 1 else r[4]), vs[1])]
    if k == "cm": return pops, [(r[2], vs[0]), (r[3], r[4])]
    if k == "sink": return pops, []

def run(rules, N, pairs, rng, out_ch, maxsteps=10 ** 6):
    st = [[] for _ in range(N)]
    for a, b in pairs:
        st[0].append(a); st[1].append(b); st[2].append(0)
    outs, n = [], 0
    while n < maxsteps:
        en = [i for i, r in enumerate(rules) if fire(r, st) is not None]
        if not en: break
        i = rng.choice(en)
        pops, pushes = fire(rules[i], st)
        for c, m in pops.items(): del st[c][:m]
        for c, v in pushes: st[c].append(v)
        n += 1
    return st, n

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("pairs", nargs="+")
    ap.add_argument("--lean", default=__import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)), "..", "..", "lean", "Formal", "Net", "GcdHw.lean"))
    ap.add_argument("--runs", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", type=int, default=None, help="output channel (default: name '170')")
    args = ap.parse_args()
    rules = parse_rules(args.lean)
    src = open(args.lean).read()
    names = eval(re.search(r"def chanNames : List String := (\[.*\])", src).group(1))
    N = len(names)
    out_ch = args.out if args.out is not None else names.index("170")
    pairs = [tuple(int(x, 0) for x in p.split(",")) for p in args.pairs]
    rng = random.Random(args.seed)
    seen = {}
    for k in range(args.runs):
        st, n = run(rules, N, pairs, rng, out_ch)
        key = tuple(st[out_ch])
        left = sum(len(q) for i, q in enumerate(st) if i != out_ch)
        seen.setdefault((key, left), 0); seen[(key, left)] += 1
    for (key, left), cnt in sorted(seen.items(), key=lambda x: -x[1]):
        print(f"{cnt:4d} runs: out0 = {list(key)}  other tokens left = {left}")

if __name__ == "__main__":
    main()
