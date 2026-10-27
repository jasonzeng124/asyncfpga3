"""cert8.py -- emit the CERTIFICATE that xevents8 (Events8Main.lean) checks (UNTRUSTED).

    python3 cert8.py SKEL.json BANDS.json OUT.json [--no-u3] [--no-nary] [--no-gline] [--no-guard]

Probe WE4g: a copy of events7/cert7.py (A-events7, unchanged below except where marked WE4g)
plus the GUARD certificates of Events8Cert.GuardOK8.  Per guarded pin p of stage j (source D,
guard pin g = gp with source Gs, guard label (grp, br) from ana's guard_info, label source S):
the pin's grp/br are set to the guard's label, and a `guards` entry "j/p" gives S and six log
lines: iD (walk D -> S, no token), iB (BACK-G: walk S -> j in the label, <= 1 token), iU
(U-bound Gs -> S in the label), iW (walk S -> D, <= 1 token), iX (closed walk D -> D, 1 token),
iG (walk S -> Gs in the label, no token).  The labelled walks start at S because the Events7
SUB rule's walk starts at the label's source.  --no-guard emits none of them (then every guarded pin is residual).
Original cert7 docstring follows.


A-events7.  Same nodes / recognition data as events6/cert6.py, with three changes:

* guarded pins whose guarded input arrives through a delay line (bd_mux z_ack, umux3/4/5) are
  emitted as GUARD pins with all their copies (Net4.OK7 / Beh7), not as `multi` pins;
* walk derivations are a flat LOG (Events7Cert.Ln): each line derives one judgement from
  earlier lines.  U-bounds are log lines too (`uT`, `uW`), so a merge arm's U-label may come
  THROUGH another merge's R3 line (U3);
* R3 / SUB / exclusivity at merges of any arity: arms carry pairwise exclusive labels
  (1-bit group: different branches; multi-bit select: different patterns, which are their
  own groups listed together in a select PARTITION -- the SelPart hypothesis).
  Every R3 candidate (source, group) of a merge is tried, not only ana's first one.

Flags --no-u3 / --no-nary / --no-gline switch the three extensions off (for the comparison
with events6 and as controls).
Everything here is search; the Lean checker re-checks every line and every item.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "events4"))
sys.path.insert(0, os.path.join(HERE, "..", "events6"))
from cert6 import Cert, Unsup  # noqa: E402
from ana import DEPTH  # noqa: E402

sys.setrecursionlimit(20000)


class Cert7(Cert):
    def __init__(self, netp, bandp, u3=True, nary=True, gline=True, guard=True):
        super().__init__(netp, bandp)
        self.u3, self.nary, self.gline, self.guardc = u3, nary, gline, guard
        self.log, self.memo = [], {}
        self.hyp = []  # WE4g: hypothesis lines (Events8Cert.HLn)
        self.parts = {}
        self._ucache = {}
        self._r3c = {}

    # ---------------- labels -------------------------------------------------------------
    def lab(self, g, b):
        if len(b) == 1:
            return (self.gid(g), bool(b[0]))
        gi = self.gid((g, b))
        self.parts.setdefault(g, set()).add(gi)
        return (gi, True)

    def lx(self, l1, l2):
        if l1[0] == l2[0]:
            return l1[1] != l2[1]
        if not (l1[1] and l2[1]):
            return False
        return any(l1[0] in P and l2[0] in P for P in self.parts.values())

    # ---------------- log --------------------------------------------------------------
    def line(self, ln):
        key = json.dumps(ln, sort_keys=True)
        if key not in self.memo:
            self.memo[key] = len(self.log)
            self.log.append(ln)
        return self.memo[key]

    def filt_ok(self, x, p):
        return p.filt and p.inv == 0 and self.A.v(p.src) == 0 and self.A.off(x, p) == 0

    # ---------------- U-bounds as log lines ----------------------------------------------
    def uline(self, a, g, b, seen=frozenset()):
        """Log line of a U-bound (true, a, some lab(g,b), g[0], d, 0), maximising d; None if
        none is found.  Returns (line, d)."""
        key = (a, g, b)
        if key in self._ucache:
            return self._ucache[key]
        if a in seen or len(seen) > 40:
            return None
        seen = seen | {a}
        A, nd = self.A, self.M.nodes.get(a)
        best = None
        if nd and nd["pins"]:
            F = nd["F"][0]
            if nd["kind"] == "cel":
                for k, p in enumerate(nd["pins"]):
                    if self.filt_ok(a, p) and A.group(p) == (g, b):
                        c = (self.line({"k": "uT", "T": self.idx[a], "q": k}), F + p.lo)
                        if best is None or c[1] > best[1]:
                            best = c
                for k, p in enumerate(nd["pins"]):
                    if A.off(a, p) == 0 and p.inv == 0 and not self.is_guard(a, k) and (g, b) in A.U[p.src]:
                        r = self.uline(p.src, g, b, seen)
                        if r:
                            w = self.line({"k": "r1", "n": self.idx[a], "p": k,
                                           "r": self.line({"k": "refl", "a": self.idx[p.src]})})
                            c = (self.line({"k": "uW", "w": w, "u": r[0]}), F + p.lo + r[1])
                            if best is None or c[1] > best[1]:
                                best = c
            elif self.u3:
                for cand in self.r3cands(a, seen):
                    S, gg, arms, dmin = cand
                    if (g, b) in A.U[S]:
                        r = self.uline(S, g, b, seen)
                        if r:
                            w = self.r3line(a, cand, self.line({"k": "refl", "a": self.idx[S]}))
                            c = (self.line({"k": "uW", "w": w, "u": r[0]}), F + dmin + r[1])
                            if best is None or c[1] > best[1]:
                                best = c
        if not seen - {a}:
            self._ucache[key] = best
        return best

    # ---------------- arms of a merge ----------------------------------------------------
    def arm_bound(self, x, i, g, b, seen=frozenset()):
        """(arm dict, delay) for arm i of merge x under label (g, b), or None."""
        p = self.M.nodes[x]["pins"][i]
        L = self.lab(g, b)
        if self.filt_ok(x, p) and self.A.group(p) == (g, b):
            return dict(g=L[0], b=L[1], dir=True, ref=0), p.lo
        if p.inv != 0:
            return None
        r = self.uline(p.src, g, b, seen | {x})
        if r is None:
            return None
        return dict(g=L[0], b=L[1], dir=False, ref=r[0]), p.lo + r[1]

    def r3cands(self, x, seen=frozenset()):
        """All (S, g, arms, dmin) R3 candidates of merge x: one label of group g per arm,
        pairwise exclusive, every arm U-bounded."""
        if x in self._r3c and not seen:
            return self._r3c[x]
        pins = self.M.nodes[x]["pins"]
        if not self.nary and len(pins) != 2:
            return []
        groups = None
        for p in pins:
            gs = {}
            for (g, b) in self.A.tapU(p):
                gs.setdefault(g, set()).add(b)
            groups = gs if groups is None else {g: groups[g] | gs[g] for g in groups if g in gs}
        out = []
        for g in sorted(groups or {}, key=str):
            if not self.nary and any(len(b) != 1 for b in groups[g]):
                continue
            opts = [sorted(b for (gg, b) in self.A.tapU(p) if gg == g) for p in pins]
            for assign in self.assignments(opts):
                arms, ds, ok = [], [], True
                for i, b in enumerate(assign):
                    r = self.arm_bound(x, i, g, b, seen)
                    if r is None:
                        ok = False
                        break
                    arms.append(r[0])
                    ds.append(r[1])
                if ok:
                    labs = [(a["g"], a["b"]) for a in arms]
                    if all(self.lx(labs[i], labs[j]) for i in range(len(labs)) for j in range(len(labs)) if i != j):
                        out.append((g[0], g, arms, min(ds)))
                        break
        if not seen:
            self._r3c[x] = out
        return out

    @staticmethod
    def assignments(opts, used=()):
        if not opts:
            yield ()
            return
        for o in opts[0]:
            if o not in used:
                for rest in Cert7.assignments(opts[1:], used + (o,)):
                    yield (o,) + rest

    def r3line(self, x, cand, rest):
        S, g, arms, _ = cand
        return self.line({"k": "r3", "x": self.idx[x], "S": self.idx[S], "arms": arms, "r": rest})

    def subcands(self, x, ti, g, b):
        """SUB at merge x into arm ti under context (g, b): the other arms U-bounded by labels of
        g other than b, pairwise exclusive (and exclusive with b)."""
        pins = self.M.nodes[x]["pins"]
        if not self.nary and (len(pins) != 2 or len(b) != 1):
            return None
        Lb = self.lab(g, b)
        opts = [sorted(bb for (gg, bb) in self.A.tapU(p) if gg == g and bb != b) if k != ti else [b]
                for k, p in enumerate(pins)]
        for assign in self.assignments(opts):
            arms, ok = [], True
            for i, bb in enumerate(assign):
                if i == ti:
                    arms.append(dict(g=Lb[0], b=Lb[1], dir=True, ref=0))
                    continue
                r = self.arm_bound(x, i, g, bb)
                if r is None:
                    ok = False
                    break
                arms.append(r[0])
            if ok:
                labs = [(a["g"], a["b"]) for a in arms]
                if all(self.lx(labs[i], labs[j]) for i in range(len(labs)) for j in range(len(labs)) if i != j):
                    return arms
        return None

    # ---------------- walk search ----------------------------------------------------------
    def walk(self, a, goal, budget, ctx=None, closed=False):
        best = None
        for rev in (False, True):
            r = self.walk1(a, goal, budget, ctx, closed, rev)
            if r is not None and (best is None or r[0] > best[0]):
                best = r
        return best

    def walk1(self, a, goal, budget, ctx, closed, rev):
        A, N = self.A, self.M.nodes
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
            nd = N[x]
            if not nd["pins"]:
                return
            F = nd["F"][0]
            if nd["kind"] == "cel":
                ks = list(range(len(nd["pins"])))
                for k in (ks[::-1] if rev else ks):
                    p = nd["pins"][k]
                    if self.is_guard(x, k):
                        continue
                    o = A.off(x, p)
                    if tok + o > budget:
                        continue
                    filt = p.filt and p.inv == 0 and A.v(p.src) == 0
                    if filt and not self.nary and len(A.group(p)[1]) != 1:
                        continue
                    nctx = A.group(p) if filt else ctx
                    go(p.src, d + F + p.lo, tok + o, nctx, depth + 1,
                       path + [("fpin" if filt else "pin", x, k)])
            else:
                for cand in self.r3cands(x):
                    go(cand[0], d + F + cand[3], tok, ctx, depth + 1, path + [("R3", x, cand)])
                if ctx is not None:
                    g, b = ctx
                    for ti, p in enumerate(nd["pins"]):
                        if p.filt:
                            continue
                        arms = self.subcands(x, ti, g, b)
                        if arms is not None and g[0] in N:
                            go(p.src, d + F + p.lo, tok, None, depth + 1, path + [("SUB", x, (ti, arms))])
        go(a, 0, 0, ctx, 0, [])
        return best[0]

    # ---------------- walk -> log lines ------------------------------------------------------
    def chain(self, steps, start):
        if not steps:
            return self.line({"k": "refl", "a": self.idx[start]})
        kind, x, info = steps[0]
        rest = steps[1:]
        if kind == "pin":
            p = self.M.nodes[x]["pins"][info]
            return self.line({"k": "r1", "n": self.idx[x], "p": info, "r": self.chain(rest, p.src)})
        if kind == "fpin":
            p = self.M.nodes[x]["pins"][info]
            return self.line({"k": "fpin", "n": self.idx[x], "p": info,
                              "r": self.build(rest, p.src, self.A.group(p))})
        if kind == "R3":
            return self.r3line(x, info, self.chain(rest, info[0]))
        raise Unsup("SUB without a branch context")

    def build(self, steps, start, ctx):
        if ctx is None:
            return self.chain(steps, start)
        g, b = ctx
        L = self.lab(g, b)
        for i, (kind, x, info) in enumerate(steps):
            if kind == "fpin":
                break
            if kind == "SUB":
                ti, arms = info
                pins = self.M.nodes[x]["pins"]
                w1 = self.chain(steps[:i], start)
                w2 = self.chain(steps[i + 1:], pins[ti].src)
                return self.line({"k": "sub", "x": self.idx[x], "S": self.idx[start], "ab": ti, "arms": arms,
                                  "w1": w1, "w2": w2})
        return self.line({"k": "lift", "g": L[0], "b": L[1], "r": self.chain(steps, start)})

    def dbuild(self, steps, start, ctx):
        """WE4g: a labelled walk from `start` (a guarded source D, not the label's source S) as a
        HYPOTHESIS line: `copy` of a valid log line when the walk enters its label by `lift` or
        `fpin` before any SUB; else `dsub` (the SUB conclusion started at D, Events8Cert.HDsub).
        Never puts an invalid line into the log."""
        g, b = ctx
        for i, (kind, x, info) in enumerate(steps):
            if kind == "fpin":
                break
            if kind == "SUB":
                ti, arms = info
                pins = self.M.nodes[x]["pins"]
                w1 = self.chain(steps[:i], start)
                w2 = self.chain(steps[i + 1:], pins[ti].src)
                self.hyp.append({"k": "dsub", "a": self.idx[start], "x": self.idx[x], "S": self.idx[g[0]],
                                 "ab": ti, "arms": arms, "w1": w1, "w2": w2})
                return len(self.hyp) - 1
        self.hyp.append({"k": "copy", "i": self.build(steps, start, ctx)})
        return len(self.hyp) - 1

    # ---------------- assembly ---------------------------------------------------------------
    def run7(self):
        M, A = self.M, self.A
        # cert6's nodes (recognition data) and rank; its walk search is switched off here
        aw = A.walk
        self.walk = lambda *a_, **k_: None
        A.walk = lambda *a_, **k_: None
        base = self.run()
        del self.walk
        A.walk = aw
        self.log, self.memo = [], {}
        nodes, errs = base["nodes"], []
        # guarded delay lines: guard pins with all their copies
        for e, x in zip(nodes, self.names):
            nd = M.nodes[x]
            for k, (pe, p) in enumerate(zip(e["pins"], nd["pins"] or [])):
                if self.is_guard(x, k) and p.kind == "multi":
                    if self.gline:
                        pe["pk"] = "guard"
                        gi = A.guard_info(x, p)
                        if gi:
                            S, g, b, q = gi
                            cands = [kk for kk, pp in enumerate(nd["pins"]) if (g, b) in A.tapU(pp) and not self.is_guard(x, kk)]
                            pe["gp"] = cands[0] if cands else 0
        back, lines, excl = {}, {}, {}
        for j, nd in M.nodes.items():
            if not nd["pins"]:
                continue
            if nd["kind"] == "cel":
                for k, p in enumerate(nd["pins"]):
                    if self.is_guard(j, k) and (self.gline or p.kind != "multi"):
                        continue
                    o = A.off(j, p)
                    filt = p.filt and p.inv == 0 and A.v(p.src) == 0
                    ctx = A.group(p) if p.filt else None
                    try:
                        w = self.walk(p.src, j, 1 - o, ctx=ctx) if o <= 1 else None
                        if not w:
                            errs.append(f"back {j} pin{k}: no walk")
                            continue
                        back[f"{self.idx[j]}/{k}"] = self.build(w[2], p.src, ctx)
                    except Unsup as ex:
                        errs.append(f"back {j} pin{k}: {ex}")
            for k, p in enumerate(nd["pins"]):
                if p.kind == "multi" and not (self.gline and nd["kind"] == "cel" and self.is_guard(j, k)):
                    try:
                        w = self.walk(p.src, p.src, 1, closed=True)
                        if not w:
                            errs.append(f"line {j} pin{k}: no cycle")
                            continue
                        lines[f"{self.idx[j]}/{k}"] = self.build(w[2], p.src, None)
                    except Unsup as ex:
                        errs.append(f"line {j} pin{k}: {ex}")
            if nd["kind"] == "merge" and len(nd["pins"]) > 1:
                done = False
                for cand in self.r3cands(j):
                    S, g, arms, _ = cand
                    w = self.walk(S, j, 1)
                    if w:
                        try:
                            excl[str(self.idx[j])] = dict(S=self.idx[S], arms=arms, w=self.build(w[2], S, None))
                            done = True
                            break
                        except Unsup:
                            pass
                if not done:
                    errs.append(f"excl {j}: no R3 candidate with a walk S -> merge")
        # WE4g: guard certificates (Events8Cert.GuardOK8)
        guards = {}
        for e, x in zip(nodes, self.names):
            nd = M.nodes[x]
            if nd["kind"] != "cel":
                continue
            for k, (pe, p) in enumerate(zip(e["pins"], nd["pins"] or [])):
                if pe["pk"] != "guard":
                    continue
                gi = A.guard_info(x, p)
                if gi is None:
                    errs.append(f"guard {x} pin{k}: no guard label")
                    continue
                S, g, b, q = gi
                L = self.lab(g, b)
                pe["grp"], pe["br"] = L[0], L[1]
                if not self.guardc:
                    continue
                gk = pe["gp"]
                gpin = nd["pins"][gk]
                D, Gs = p.src, gpin.src
                try:
                    wB = self.walk(D, x, 1, ctx=(g, b))
                    u = self.uline(Gs, g, b)
                    wW = self.walk(S, D, 1)
                    wX = self.walk(D, D, 1, closed=True)
                    wG = self.walk(D, Gs, 0, ctx=(g, b))
                    miss = [n for n, w in (("B", wB), ("U", u), ("W", wW), ("X", wX), ("G", wG)) if not w]
                    if miss:
                        errs.append(f"guard {x} pin{k}: no walk {miss}")
                        continue
                    guards[f"{self.idx[x]}/{k}"] = dict(
                        S=self.idx[S], iB=self.dbuild(wB[2], D, (g, b)), iU=u[0],
                        iW=self.build(wW[2], S, None), iX=self.build(wX[2], D, None),
                        iG=self.dbuild(wG[2], D, (g, b)))
                except Unsup as ex:
                    errs.append(f"guard {x} pin{k}: {ex}")
        parts = [sorted(P) for P in self.parts.values() if len(P) > 1]
        log = [self.enc(ln) for ln in self.log]
        return dict(nodes=nodes, rank=base["rank"], log=log, parts=parts, back=back, lines=lines, excl=excl,
                    guards=guards, hyp=self.hyp, errors=errs, groups=len(self.grp))

    @staticmethod
    def enc(ln):
        return ln


def main():
    os.environ.setdefault("PYTHONHASHSEED", "0")
    a = [x for x in sys.argv[1:] if not x.startswith("--")]
    C = Cert7(a[0], a[1], u3="--no-u3" not in sys.argv, nary="--no-nary" not in sys.argv,
              gline="--no-gline" not in sys.argv, guard="--no-guard" not in sys.argv)
    out = C.run7()
    json.dump(out, open(a[2], "w"))
    print(f"cert8: {len(out['nodes'])} nodes, log {len(out['log'])} lines, back {len(out['back'])}, "
          f"lines {len(out['lines'])}, excl {len(out['excl'])}, guards {len(out['guards'])}, groups {out['groups']}, parts {out['parts']}, "
          f"errors {len(out['errors'])}")
    for e in out["errors"]:
        print("  UNCERTIFIED", e)


if __name__ == "__main__":
    main()
