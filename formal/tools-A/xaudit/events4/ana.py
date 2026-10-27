"""ana.py -- event-count (counter) domain analysis of the gcd_hw control skeleton (UNTRUSTED).

    python3 ana.py NET.json BANDS.json [--label L] [--json OUT.json]

Applies the rules of formal/lean/Formal/Core/XAudit/Events4*.lean (see the notes for which
rule is proved in Lean and which is not) to the model built by model.py:

  Back (per C-element pin): a walk upstream from the pin's source back to the stage, at most
       1 - off tokens, whose fastest traversal d covers the own feedback:
       margin = lo(pin) + d - hiQ.  Steps: through a stage pin (R1); through a merge whose
       arms are distinct branches of one steer source S (R3: merge count <= count of S);
       and, in a walk that starts at a steer arm (filtered pin of group g, branch b, source S),
       one SUB step at a merge: filt_b(M_S) <= (the arm-b tap) + k, the other arms being
       bounded by the other branches of S (U-bounds, conservation filt_add).
  Guarded pins (mux acks C(j_b, z_ack), arbiter A_b = C(g_b, A0)): a pin whose source counts
       every transaction while the stage fires only in branch b.  Not a counter pin; two
       timing conditions: ENTRY hi(src->j) <= fastest src->S->...->guard pin,
       EXIT  hi(src->j) - lo(src->j) + hiF + hiQ <= W(src) (min event spacing of src).
  Merge exclusivity (sum count): arms are distinct branches of S + a walk S -> merge with <= 1
       token (proved by induction in Events4: no timing condition).
  Multi-tap pins (FASTFALL/FASTRISE delay lines, same source): tap skew <= W(src).
  W(x): fastest closed walk x -> x with exactly 1 token: x fires at most once per W window.
"""
import argparse
import collections
import json
import sys
from model import Model, Pin

DEPTH = 14


class Ana:
    def __init__(self, M):
        self.M = M
        self.N = M.nodes
        self.U = collections.defaultdict(set)
        self.compute_U()
        self.r3 = {x: self.reconv(x) for x, nd in self.N.items() if nd["kind"] == "merge"}
        # U through merges that reconverge (U3), iterate
        for _ in range(6):
            ch = self.compute_U()
            self.r3 = {x: self.reconv(x) for x, nd in self.N.items() if nd["kind"] == "merge"}
            if not ch:
                break

    # -- reset values / tokens
    def v(self, x):
        return self.N[x]["v"]

    def off(self, j, p):
        return int((self.v(p.src) ^ p.inv ^ p.pol) != self.v(j))

    def group(self, p):
        """(group key, branch) of a filtered pin."""
        sel, pat = p.filt
        if sel and sel[0] == "arb":
            return (p.src, sel), tuple(pat)
        pairs = sorted(zip(sel, pat))
        return (p.src, tuple(a for a, _ in pairs)), tuple(b for _, b in pairs)

    def tapU(self, p):
        s = set()
        if p.filt and p.inv == 0 and self.v(p.src) == 0:
            g, b = self.group(p)
            s.add((g, b))
        if p.inv == 0:
            s |= self.U[p.src]
        return s

    def compute_U(self):
        ch = False
        for _ in range(50):
            changed = False
            for x, nd in self.N.items():
                if not nd["pins"]:
                    continue
                new = set()
                if nd["kind"] == "cel":
                    for p in nd["pins"]:
                        if self.off(x, p) == 0:
                            new |= self.tapU(p)
                else:
                    r = getattr(self, "r3", {}).get(x)
                    if r:
                        new |= self.U[r[0]]
                if not new <= self.U[x]:
                    self.U[x] |= new
                    changed = ch = True
            if not changed:
                break
        return ch

    def reconv(self, x):
        """R3: all arms of merge x are distinct branches of one group -> (S, group)."""
        pins = self.N[x]["pins"]
        cands = None
        for p in pins:
            gs = collections.defaultdict(set)
            for (g, b) in self.tapU(p):
                gs[g].add(b)
            cands = gs if cands is None else {g: cands[g] | gs[g] for g in cands if g in gs}
            if cands is None:
                return None
        for g in cands or {}:
            # choose one branch per arm, pairwise distinct
            opts = [sorted(b for (gg, b) in self.tapU(p) if gg == g) for p in pins]
            if self.distinct(opts):
                return (g[0], g)
        return None

    @staticmethod
    def distinct(opts, used=()):
        if not opts:
            return True
        return any(Ana.distinct(opts[1:], used + (o,)) for o in opts[0] if o not in used)

    def sub_ok(self, x, ti, g, b):
        """SUB at merge x, target arm ti, context (g, b): the other arms are distinct branches of g, != b."""
        pins = self.N[x]["pins"]
        opts = [sorted(bb for (gg, bb) in self.tapU(p) if gg == g and bb != b)
                for k, p in enumerate(pins) if k != ti]
        return self.distinct(opts)

    # -- walk search: maximise d of a walk from `a` upstream to `goal`
    def walk(self, a, goal, budget, ctx=None, closed=False):
        best = [None]
        bestat = {}

        def go(x, d, tok, ctx, depth, path):
            if x == goal and (path or not closed):
                if best[0] is None or d > best[0][0]:
                    best[0] = (d, tok, list(path))
                if not closed:
                    return
            if depth > DEPTH:
                return
            key = (x, ctx, tok)
            if bestat.get(key, -1) >= d:
                return
            bestat[key] = d
            nd = self.N[x]
            if not nd["pins"]:
                return
            F = nd["F"][0]
            if nd["kind"] == "cel":
                for p in nd["pins"]:
                    o = self.off(x, p)
                    if tok + o > budget:
                        continue
                    nctx = self.group(p) if (p.filt and p.inv == 0 and self.v(p.src) == 0) else ctx
                    go(p.src, d + F + p.lo, tok + o, nctx, depth + 1,
                       path + [(x, "fpin" if p.filt else "pin", p.src)])
            else:
                r = self.r3.get(x)
                if r:
                    go(r[0], d + F + min(p.lo for p in nd["pins"]), tok, ctx, depth + 1,
                       path + [(x, "R3", r[0])])
                if ctx is not None:
                    g, b = ctx
                    for ti, p in enumerate(nd["pins"]):
                        if p.filt:
                            continue
                        if self.sub_ok(x, ti, g, b):
                            go(p.src, d + F + p.lo, tok, None, depth + 1, path + [(x, "SUB", p.src)])
        go(a, 0, 0, ctx, 0, [])
        return best[0]

    def W(self, x, cache={}):
        if x not in cache:
            r = self.walk(x, x, 1, closed=True)
            cache[x] = r[0] if r else None
        return cache[x]

    def guard_info(self, j, p):
        """Is p a guarded pin of j?  j fires only in a branch (g,b) of S, and S reads ~src(p)."""
        for (g, b) in self.U[j]:
            S = g[0]
            nS = self.N.get(S)
            if not nS or nS["kind"] != "cel":
                continue
            for q in nS["pins"]:
                if q.src == p.src and (q.inv ^ q.pol) == 1:
                    return (S, g, b, q)
        return None

    def fastest(self, a, goal):
        """Minimal-lo upstream walk a -> goal (Dijkstra over pins, any tokens)."""
        import heapq
        h = [(0, a)]
        seen = {}
        while h:
            d, x = heapq.heappop(h)
            if x in seen:
                continue
            seen[x] = d
            if x == goal:
                return d
            nd = self.N[x]
            if not nd["pins"]:
                continue
            for p in nd["pins"]:
                heapq.heappush(h, (d + nd["F"][0] + p.lo, p.src))
        return None

    def multi(self, j, k, p):
        """Multi-tap pin: CONTIGUITY of the tap counts.  Taps sorted by lo; every consecutive
        pair's window max(hi) - min(lo) must be <= W(src) (the source fires at most once in it),
        so consecutive tap counts differ by <= 1 and the set of counts has no gap
        (Events4.and_cnt_val / or_cnt_val)."""
        Wc = self.W(p.src)
        t = sorted(p.taps)
        pair = p.win  # largest local window between representatives (model.leaf)
        return dict(stage=j, pin=k, src=p.src, op=p.op, ntaps=len(t), skew=p.hi - p.lo, pair=pair, W=Wc,
                    margin=(Wc - pair) if Wc is not None else None)

    def run(self):
        res = dict(stages=[], merges=[], multis=[], guards=[], unproved=[])
        for j, nd in sorted(self.N.items()):
            if nd["kind"] != "cel" or not nd["pins"]:
                continue
            virt = nd.get("virtual", False)
            hiQ = nd["Q"][1]
            for k, p in enumerate(nd["pins"]):
                o = self.off(j, p)
                ctx = self.group(p) if p.filt else None
                w = self.walk(p.src, j, 1 - o, ctx=ctx) if o <= 1 else None
                ent = dict(stage=j, pin=k, src=p.src, kind=p.kind, filt=bool(p.filt), off=o,
                           lo=p.lo, hi=p.hi, hiQ=hiQ, virtual=virt)
                if w:
                    ent.update(rule="Back", d=w[0], margin=p.lo + w[0] - hiQ,
                               path=[s[1] for s in w[2]])
                else:
                    gi = self.guard_info(j, p)
                    if gi:
                        S, g, b, q = gi
                        # entry: fastest S -> ... -> guard pins of j (the pins of j in branch b)
                        gp = [pp for pp in nd["pins"] if (g, b) in self.tapU(pp)]
                        fw = [self.fastest(pp.src, S) for pp in gp]
                        fw = [x + pp.lo for x, pp in zip(fw, gp) if x is not None]
                        entry = (q.lo + nS_F(self, S) + min(fw) - p.hi) if fw else None
                        Wc = self.W(p.src)
                        exitm = (Wc + p.lo - p.hi - nd["F"][1] - hiQ) if Wc is not None else None
                        ent.update(rule="Guard", S=S, entry=entry, exit=exitm, W=Wc)
                    else:
                        ent.update(rule="NONE")
                res["stages"].append(ent)
                if p.kind == "multi":
                    res["multis"].append(self.multi(j, k, p))
        for x, nd in sorted(self.N.items()):
            if nd["kind"] != "merge":
                continue
            r = self.r3.get(x)
            ent = dict(merge=x, virtual=nd.get("virtual", False), arms=len(nd["pins"]))
            if r:
                S = r[0]
                w = self.walk(S, x, 1)
                ent.update(S=S, walk=(w[0] if w else None), ok=bool(w))
            else:
                ent.update(S=None, ok=False)
            res["merges"].append(ent)
            for k, p in enumerate(nd["pins"]):
                if p.kind == "multi":
                    res["multis"].append(self.multi(x, k, p))
        # per-window rate bound: W of every real stage
        res["W"] = {j: self.W(j) for j, nd in self.N.items() if nd["kind"] == "cel" and not nd.get("virtual")}
        return res


def nS_F(a, S):
    return a.N[S]["F"][0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("net")
    ap.add_argument("bands")
    ap.add_argument("--label", default="")
    ap.add_argument("--json")
    a = ap.parse_args()
    M = Model(a.net, a.bands)
    A = Ana(M)
    r = A.run()
    r["unrec"] = M.unrec
    r["arbs"] = M.arbs
    if a.json:
        json.dump(r, open(a.json, "w"), indent=1, default=str)
    st = r["stages"]
    real = [e for e in st if not e["virtual"]]
    rules = collections.Counter(e["rule"] for e in real)
    print(f"[{a.label}] stages {len({e['stage'] for e in real})}, pins {len(real)}: {dict(rules)}")
    neg = [e for e in real if e["rule"] == "Back" and e["margin"] < 0]
    print(f"  Back: min margin {min(e['margin'] for e in real if e['rule']=='Back')} ps; negative: {len(neg)}")
    for e in sorted(neg, key=lambda e: e["margin"])[:40]:
        print(f"    {e['margin']:6d}  {e['stage']} pin{e['pin']} <- {e['src']} lo {e['lo']} d {e['d']} hiQ {e['hiQ']} {e['path']}")
    g = [e for e in real if e["rule"] == "Guard"]
    print(f"  Guard pins {len(g)}: min entry {min((e['entry'] for e in g if e['entry'] is not None), default=None)}, "
          f"min exit {min((e['exit'] for e in g if e['exit'] is not None), default=None)}")
    for e in sorted(g, key=lambda e: min(e['entry'] or 0, e['exit'] or 0))[:8]:
        print(f"    entry {e['entry']} exit {e['exit']} W {e['W']}  {e['stage']} <- {e['src']}")
    nn = [e for e in real if e["rule"] == "NONE"]
    print(f"  NONE (no certificate) {len(nn)}")
    for e in nn[:20]:
        print(f"    {e['stage']} pin{e['pin']} <- {e['src']} off {e['off']} filt {e['filt']}")
    mg = r["merges"]
    print(f"  merges {len(mg)}: certified {sum(m['ok'] for m in mg)}; not: {[m['merge'] for m in mg if not m['ok']][:10]}")
    mu = r["multis"]
    bad = [m for m in mu if m["margin"] is None or m["margin"] < 0]
    print(f"  multi-tap pins {len(mu)}: min margin {min((m['margin'] for m in mu if m['margin'] is not None), default=None)}; failing {len(bad)}")
    for m in bad[:10]:
        print(f"    {m}")
    Ws = [w for w in r["W"].values() if w is not None]
    print(f"  per-window bound W (ps): min {min(Ws)}, median {sorted(Ws)[len(Ws)//2]}, none {sum(1 for w in r['W'].values() if w is None)}")


if __name__ == "__main__":
    main()
