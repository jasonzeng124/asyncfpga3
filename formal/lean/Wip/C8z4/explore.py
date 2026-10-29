#!/usr/bin/env python3
"""C-8z4: exhaustive deadlock search for the gcd_hw gate network, interleaving semantics,
with stubborn-set (partial-order) reduction.  UNTRUSTED evidence, proves nothing in Lean.

Model (mirrors Lean's `gatesE` = 8u's `gatesK ++ grantsK`; the gate list is 8z2's `gates2`
from Wip/C8z2/persim.py, re-encoded with read sets):
  * state = every req/ack bit, every used internal node (mux joins, 3-way joins, grants, link C),
    the link latches, and (abstract mode) one stored bit per `join` output;
  * one step = one excited gate takes its target value (SI interleaving);
  * `start`'s LUT offers once (a flag) and may release; a/b sources are free-running;
  * links capture their input bus when `c` rises (equivalent to a transparent latch on runs
    meeting H_BUNDLE);
  * out0's sink never lowers its acknowledge: a run reaching that point has closed out0's first
    token, and the search stops there.  A DEADLOCK is a reachable state with no enabled step in
    which out0's first token has not closed.
Modes:
  --abstract   every `join` output value is a fresh nondeterministic bit chosen when its request
               rises (all other buses are then 0 or small): this OVER-approximates every input
               a, b (steer/mux selects depend on data only through join outputs), including
               non-terminating loop paths.  Covers all inputs at once.
  a b          concrete data, the sources carry a, b.
Stubborn sets (Valmari): seed = one enabled transition; enabled members pull in every
transition that writes what they read or reads/writes what they write; disabled members pull
in the writers of one necessary-enabling variable set.  This preserves every reachable deadlock.

Usage: python3 -I explore.py --abstract [--maxstates N]
       python3 -I explore.py 12 18
"""
import os, sys, time, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "formal", "tools", "capwit"))
import sim  # noqa: E402
from sim import ev, jval, sel2, selD, outs_of, NINT  # noqa: E402


def build(names, ops, out0, abstract, a=0, b=0):
    NC = len(names)
    prod = {}
    for n, o in enumerate(ops):
        for c in outs_of(o): prod[c] = n
    V = 2 * NC
    itv = {}
    for n, o in enumerate(ops):
        k = NINT.get(o["k"], 0)
        itv[n] = list(range(V, V + k)); V += k
    latv = {}
    for n, o in enumerate(ops):
        if o["k"] == "link": latv[o["o"]] = V; V += 1
    jbv = {}
    if abstract:
        for n, o in enumerate(ops):
            if o["k"] == "join": jbv[o["o"]] = V; V += 1
    STARTED = V; V += 1
    R = lambda c: c
    A = lambda c: NC + c
    pstart = prod[2]
    srcv = lambda w: a if w == 0 else (b if w == 1 else 0)

    # static data support of every channel bus
    supp = {}
    def sp(c):
        if c in supp: return supp[c]
        o = ops[prod[c]]; k = o["k"]
        if k in ("forkG", "forkH"): s = sp(o["i"])
        elif k == "join": s = {jbv[c]} if abstract else set().union(*[sp(i) for i in o["ins"]])
        elif k == "bjoin": s = set().union(*[sp(i) for i in o["ins"]])
        elif k == "steerC": s = set()
        elif k == "steerD": s = sp(o["j"])
        elif k == "mux": s = sp(o["c"]) | sp(o["x"]) | sp(o["y"])
        elif k == "muxn": s = sp(o["c"]) | set().union(*[sp(x) for x in o["xs"]])
        elif k == "amerge": s = {itv[prod[c]][1], A(o["y"])} | sp(o["x"]) | sp(o["y"])
        elif k == "link": s = {latv[c]}
        elif k == "src": s = set()
        supp[c] = frozenset(s)
        return supp[c]
    for c in range(NC): sp(c)

    def dats(s):
        memo = {}
        def d(c):
            v = memo.get(c)
            if v is not None: return v
            o = ops[prod[c]]; k = o["k"]
            if k in ("forkG", "forkH"): v = d(o["i"])
            elif k == "join":
                v = s[jbv[c]] if abstract else ev(o["e"], [jval(j, [d(i) for i in o["ins"]]) for j in o["js"]])
            elif k == "bjoin":
                vs = [d(i) for i in o["ins"]]; v = 2 * ev(o["ed"], vs) + ev(o["ec"], vs) % 2
            elif k == "steerC": v = 0
            elif k == "steerD": v = ev(o["fd"], [d(o["j"]) // 2])
            elif k == "mux": v = d(o["y"]) if sel2(d(o["c"])) else d(o["x"])
            elif k == "muxn": v = d(o["xs"][selD(d(o["c"]))])
            elif k == "amerge":
                won = s[itv[prod[c]][1]] or s[A(o["y"])]
                v = 2 * (d(o["y"]) if won else d(o["x"])) + (1 if won else 0)
            elif k == "link": v = s[latv[c]]
            elif k == "src": v = srcv(o["which"])
            memo[c] = v
            return v
        return d

    # gates: dict(out, reads, eT, eF, nesT, nesF, extra)  (nes*: state -> set of vars)
    G = []
    def gate(out, reads, eT, eF, nesT=None, nesF=None, kind=None, n=None):
        rd = frozenset(reads)
        G.append(dict(out=out, reads=rd, eT=eT, eF=eF,
                      nesT=nesT or (lambda s: rd), nesF=nesF or (lambda s: rd), kind=kind, n=n))
    def celC(out, ins, kind=None, n=None):   # C-element over input vars
        gate(out, ins, lambda s: all(s[i] for i in ins), lambda s: not any(s[i] for i in ins),
             lambda s: {next(i for i in ins if not s[i])}, lambda s: {next(i for i in ins if s[i])}, kind, n)
    def wire(out, var, kind=None, n=None):
        gate(out, [var], lambda s: s[var], lambda s: not s[var], kind=kind, n=n)

    for n, o in enumerate(ops):
        k = o["k"]
        if k in ("forkG", "forkH"):
            for c in o["os"]: wire(R(c), R(o["i"]))
            celC(A(o["i"]), [A(c) for c in o["os"]])
        elif k in ("join", "bjoin"):
            celC(R(o["o"]), [R(i) for i in o["ins"]], kind=("join" if (k == "join" and abstract) else None), n=n)
            for i in o["ins"]: wire(A(i), A(o["o"]))
        elif k in ("steerC", "steerD"):
            j, tc, fc = o["j"], o["t"], o["f"]
            for oc, want in ((tc, True), (fc, False)):
                rd = {R(j)} | supp[j]
                def eT(s, j=j, want=want): return s[R(j)] and sel2(DD[0](j)) == want
                def nT(s, j=j): return {R(j)} if not s[R(j)] else set(supp[j])
                gate(R(oc), rd, eT, lambda s, eT=eT: not eT(s), nT, lambda s, rd=rd: rd)
            gate(A(j), [A(tc), A(fc)], lambda s, tc=tc, fc=fc: s[A(tc)] or s[A(fc)],
                 lambda s, tc=tc, fc=fc: not (s[A(tc)] or s[A(fc)]))
        elif k in ("mux", "muxn"):
            c, z = o["c"], o["z"]
            xs = [o["x"], o["y"]] if k == "mux" else o["xs"]
            for m, x in enumerate(xs):
                jv = itv[n][m]
                if k == "mux": selm = (lambda s, c=c, m=m: sel2(DD[0](c)) == (m == 1))
                else: selm = (lambda s, c=c, m=m: selD(DD[0](c)) == m)
                rd = {R(x), R(c)} | supp[c]
                def eT(s, x=x, c=c, selm=selm): return s[R(x)] and s[R(c)] and selm(s)
                def eF(s, x=x, c=c, selm=selm): return (not s[R(x)]) and not (s[R(c)] and selm(s))
                def nT(s, x=x, c=c, rd=rd): return {R(x)} if not s[R(x)] else ({R(c)} if not s[R(c)] else set(supp[c]))
                def nF(s, x=x, c=c, rd=rd): return {R(x)} if s[R(x)] else rd
                gate(jv, rd, eT, eF, nT, nF)
            js = itv[n]
            gate(R(z), js, lambda s, js=js: any(s[v] for v in js), lambda s, js=js: not any(s[v] for v in js),
                 lambda s, js=js: set(js), lambda s, js=js: {next(v for v in js if s[v])})
            for m, x in enumerate(xs): celC(A(x), [itv[n][m], A(z)])
            wire(A(c), A(z))
        elif k == "amerge":
            x, y, z = o["x"], o["y"], o["z"]; g1, g2 = itv[n]
            def eT(s, x=x, y=y, g1=g1, g2=g2): return (s[g1] or s[g2]) and not s[A(x)] and not s[A(y)]
            def nT(s, x=x, y=y, g1=g1, g2=g2):
                return {g1, g2} if not (s[g1] or s[g2]) else ({A(x)} if s[A(x)] else {A(y)})
            gate(R(z), [g1, g2, A(x), A(y)], eT, lambda s, g1=g1, g2=g2: not (s[g1] or s[g2]), nT,
                 lambda s, g1=g1, g2=g2: {g1, g2})
            celC(A(x), [g1, A(z)]); celC(A(y), [g2, A(z)])
            for (me, oth, rq) in ((g1, g2, x), (g2, g1, y)):
                def eT(s, me=me, oth=oth, rq=rq, z=z): return s[R(rq)] and not s[oth] and not s[A(z)]
                def nT(s, oth=oth, rq=rq, z=z): return {R(rq)} if not s[R(rq)] else ({oth} if s[oth] else {A(z)})
                gate(me, [R(rq), oth, A(z)], eT, lambda s, rq=rq: not s[R(rq)], nT, lambda s, rq=rq: {R(rq)})
        elif k == "link":
            i, oo = o["i"], o["o"]; cv = itv[n][0]
            def eT(s, i=i, oo=oo): return s[R(i)] and not s[A(oo)]
            def eF(s, i=i, oo=oo): return (not s[R(i)]) and s[A(oo)]
            def nT(s, i=i, oo=oo): return {R(i)} if not s[R(i)] else {A(oo)}
            def nF(s, i=i, oo=oo): return {R(i)} if s[R(i)] else {A(oo)}
            gate(cv, {R(i), A(oo)} | supp[i] | {cv}, eT, eF, nT, nF, kind="link", n=n)
            wire(A(i), cv); wire(R(oo), cv)
        elif k == "src":
            z = o["z"]
            if n == pstart:
                gate(R(z), [A(z), STARTED], lambda s, z=z: (not s[A(z)]) and not s[STARTED],
                     (lambda s: False) if HOLD else (lambda s, z=z: s[A(z)]),
                     lambda s, z=z: (set() if s[STARTED] else {A(z)}),
                     lambda s, z=z: {A(z)}, kind="start", n=n)
            else:
                gate(R(z), [A(z)], lambda s, z=z: not s[A(z)], lambda s, z=z: s[A(z)])
        elif k == "sink":
            i = o["i"]
            if i == out0:
                gate(A(i), [R(i)], lambda s, i=i: s[R(i)], lambda s: False, None, lambda s: set())
            else:
                wire(A(i), R(i))

    DD = [None]
    # transitions: gate index, writes
    writes = []
    for gi, g in enumerate(G):
        w = {g["out"]}
        if g["kind"] == "link": w.add(latv[ops[g["n"]]["o"]])
        if g["kind"] == "join": w.add(jbv[ops[g["n"]]["o"]])
        if g["kind"] == "start": w.add(STARTED)
        writes.append(frozenset(w))
    readers = {}; writers = {}
    for gi, g in enumerate(G):
        for v in g["reads"]: readers.setdefault(v, set()).add(gi)
        for v in writes[gi]: writers.setdefault(v, set()).add(gi)
    # conflict neighbours of an enabled transition (static)
    conf = []
    for gi, g in enumerate(G):
        s_ = set()
        for v in writes[gi]: s_ |= readers.get(v, set()); s_ |= writers.get(v, set())
        for v in g["reads"]: s_ |= writers.get(v, set())
        s_.discard(gi); conf.append(frozenset(s_))
    return dict(G=G, V=V, NC=NC, writes=writes, writers=writers, conf=conf, dats=dats, DD=DD,
                latv=latv, jbv=jbv, STARTED=STARTED, itv=itv, prod=prod, pstart=pstart, abstract=abstract)


SEEDS = 12
HOLD = '--hold' in sys.argv   # negative control: start never released (8z2's counterexample)

def explore(M, ops, out0, maxstates, names):
    G, V, NC = M["G"], M["V"], M["NC"]
    dats, DD, writers, conf = M["dats"], M["DD"], M["writers"], M["conf"]
    latv, jbv = M["latv"], M["jbv"]
    abstract = M["abstract"]

    def enabled(s):
        DD[0] = dats(s)
        en = {}
        for gi, g in enumerate(G):
            cur = s[g["out"]]
            if cur:
                if g["eF"](s): en[gi] = 0
            else:
                if g["eT"](s): en[gi] = 1
        return en

    def stubborn(s, en, seed):
        T = {seed}; work = [seed]; k = 1
        while work:
            t = work.pop()
            if t in en:
                nb = conf[t]
            else:
                g = G[t]
                vs = g["nesF"](s) if s[g["out"]] else g["nesT"](s)
                nb = set()
                for v in vs: nb |= writers.get(v, set())
            for u in nb:
                if u not in T:
                    T.add(u); work.append(u)
                    if u in en:
                        k += 1
                        if k >= best[0]: return None
        return T

    def succs(s, gi, v):
        g = G[gi]
        outs = []
        base = bytearray(s); base[g["out"]] = v
        if g["kind"] == "link" and v == 1:
            o = ops[g["n"]]
            val = DD[0](o["i"]); assert val < 256, val
            base[latv[o["o"]]] = val
        if g["kind"] == "start" and v == 1:
            base[M["STARTED"]] = 1
        if g["kind"] == "join" and v == 1:
            o = ops[g["n"]]
            for bit in (0, 1):
                b2 = bytearray(base); b2[jbv[o["o"]]] = bit; outs.append(bytes(b2))
            return outs
        return [bytes(base)]

    s0 = bytes(V)
    H = lambda x: hashlib.blake2b(x, digest_size=16).digest()
    seen = {H(s0): None}
    stack = [s0]
    dead = []; nst = 0; t0 = time.time(); maxen = 0; contested = 0
    while stack:
        s = stack.pop(); nst += 1
        en = enabled(s)
        if not en:
            # out0's first token closed? (req low, ack high: the sink would now lower ack)
            if not (s[NC + out0] and not s[out0]):
                dead.append(s)
                if len(dead) >= 3: break
            continue
        maxen = max(maxen, len(en))
        best = [len(en) + 1]
        bestT = None
        for seed in sorted(en, key=lambda gi: len(conf[gi]))[:SEEDS]:
            T = stubborn(s, en, seed)
            if T is not None:
                k = len([x for x in T if x in en])
                if k < best[0]: best[0] = k; bestT = T
                if k == 1: break
        for gi in bestT:
            if gi in en:
                hs = H(s)
                for ci, s2 in enumerate(succs(s, gi, en[gi])):
                    h2 = H(s2)
                    if h2 not in seen:
                        seen[h2] = (hs, gi, ci); stack.append(s2)
        if nst % 1000 == 0:
            print(f"  {nst} expanded, {len(seen)} seen, stack {len(stack)}, maxen {maxen}, "
                  f"{time.time() - t0:.0f}s", flush=True)
        if len(seen) > maxstates:
            print("STATE LIMIT"); return dict(complete=False, seen=len(seen), dead=dead, seenmap=seen)
    return dict(complete=not stack, seen=len(seen), dead=dead, seenmap=seen, expanded=nst, H=H)


def path_of(M, r, s):
    H = r["H"]; seen = r["seenmap"]; h = H(s); out = []
    while seen[h] is not None:
        ph, gi, ci = seen[h]; out.append((gi, ci)); h = ph
    out.reverse(); return out


def keys_of(M, path):
    NC = M["NC"]; inv = {}
    for n, vs in M["itv"].items():
        for m, v in enumerate(vs): inv[v] = ("i", n, m)
    def key(v): return ("r", v) if v < NC else (("a", v - NC) if v < 2 * NC else inv[v])
    return [key(M["G"][gi]["out"]) for gi, ci in path]


def main():
    names, ops, out0 = sim.load_net()
    abstract = "--abstract" in sys.argv
    maxstates = 20_000_000
    if "--maxstates" in sys.argv: maxstates = int(sys.argv[sys.argv.index("--maxstates") + 1])
    args = [x for x in sys.argv[1:] if not x.startswith("--") and not x.isdigit() or False]
    nums = [int(x) for x in sys.argv[1:] if x.isdigit()]
    if "--maxstates" in sys.argv: nums = nums[:-1]
    a, b = (nums + [0, 0])[:2] if not abstract else (0, 0)
    M = build(names, ops, out0, abstract, a, b)
    print(f"mode={'abstract' if abstract else f'concrete a={a} b={b}'} vars={M['V']} gates={len(M['G'])}", flush=True)
    t0 = time.time()
    r = explore(M, ops, out0, maxstates, names)
    print(f"done: expanded={r.get('expanded')} seen={r['seen']} deadlocks={len(r['dead'])} "
          f"complete={r['complete']} time={time.time() - t0:.0f}s", flush=True)
    for s in r["dead"]:
        hi = [names[c] for c in range(M['NC']) if s[c]]
        ha = [names[c] for c in range(M['NC']) if s[M['NC'] + c]]
        print("DEADLOCK req-high:", hi[:40]); print("  ack-high:", ha[:40])
        import pickle
        p = path_of(M, r, s)
        fn = os.path.join(HERE, f"dead_{'abs' if abstract else f'{a}_{b}'}.pkl")
        pickle.dump(dict(path=p, keys=keys_of(M, p)), open(fn, "wb"))
        print("  path length", len(p), "saved", fn)
    return 0


if __name__ == "__main__":
    sys.exit(main())
