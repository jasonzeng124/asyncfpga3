"""cert9p.py -- emit the CERTIFICATE that xevents9par (Events9ParMain.lean) checks (UNTRUSTED).

    python3 cert9p.py SKEL.json BANDS.json OUT.json [--no-par] [--neg-lag=K] [--neg-pair] [--neg-rc] [cert9 flags]

Probe E9Par: events9/cert9.py (cert8's Cert7 + first-reach wS) plus walks through PARALLEL pairs
(Events9Par.ParOK / par_fact).  For every arbiter of the corrected core (events4/model.py
build_arb_fix) the grant arb:g_b and its shadow vsh:R0/b read the same request and the same ctl
(filtered, label (ctl, b)) through different pin bands; each ordered pair z -> y gets a lag

    e = max(hiF y - loF z, max_{q, copy i} (hiF y + hiC y q i - loF z - loC z (pm q) i))

(pm = the pin of z with the same source; tp = max(0, off z p - off y q)), the smallest e that
ParOK accepts.  The walk search may then step z -> y with delay -e (only outside a label
context); it is tried only for an item whose walk search WITHOUT such steps fails, so every
item certified by cert9 keeps its walk.  A walk with parallel steps is emitted as a left fold of
`par` log lines (w1 = the walk so far, w2 = the next segment, e <= d1 + d2 checked here); a
labelled walk from a guarded source that enters its label by SUB and then crosses a pair is
emitted as a `dsub9` LOG line (with its first-reach walk wS) continued by `par` lines, and the
hypothesis line is a `copy` of the result.

Controls: --no-par (no parallel steps: the cert9 certificate, 54 structural residuals);
--neg-lag=K (every par line claims a lag K ps smaller than computed: ParOK must fail, every par
line degrades); --neg-pair (pair grant b with the shadow of the OTHER branch: different source
and label, ParOK must fail); --neg-rc (the shadows get reset classes of their own: ParOK must
fail).  Every node of an arbiter's four readers gets the field "rc" = its reset class (arbiter
k -> k + 1), the premise of the hypothesis HRst.
Everything here is search; the Lean checker re-checks every line and every item.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "events8"))
sys.path.insert(0, os.path.join(HERE, "..", "events9"))
sys.path.insert(0, os.path.join(HERE, "..", "events4"))
from cert8 import Cert7, Unsup  # noqa: E402
from cert9 import add_ws  # noqa: E402
from ana import DEPTH  # noqa: E402

NEG_INF = float("-inf")


class CertP(Cert7):
    def __init__(self, netp, bandp, par=True, neg_lag=0, neg_pair=False, neg_rc=False, **kw):
        super().__init__(netp, bandp, **kw)
        self.par_enabled, self.neg_lag, self.neg_pair, self.neg_rc = par, neg_lag, neg_pair, neg_rc
        self._par_on = False
        self.pairs = {}        # z -> list of (y, e, tp, pm)
        self.rclass = {}       # node -> reset class (Events9Par.HRst): arbiter k -> k + 1
        self.npar_steps = 0
        self.par_err = []
        self._mk_pairs()

    # ---------------- parallel pairs ------------------------------------------------------
    def pk(self, x, k, p):
        if p.kind == "multi":
            return "multi"
        if p.filt:
            return "filt"
        if self.is_guard(x, k):
            return "guard"
        return "plain"

    def lag(self, z, y, pm):
        """(e, tp) for the ordered pair z -> y with pin map pm, or None if the pins are not
        parallel (Events9Par.PinPar: same source, kind, label, operator, number of copies).
        Copy i of y's pin is compared with copy i of z's pin (Events9Par.ParOK)."""
        A, N = self.A, self.M.nodes
        nz, ny = N[z], N[y]
        Fz, Fy = nz["F"], ny["F"]
        e, tp = Fy[1] - Fz[0], 0
        for q, py in enumerate(ny["pins"]):
            p = pm[q]
            pz = nz["pins"][p]
            if pz.src != py.src:
                return None
            kz, ky = self.pk(z, p, pz), self.pk(y, q, py)
            if kz != ky or ky == "guard" or len(pz.taps) != len(py.taps):
                return None
            if ky == "filt" and A.group(pz) != A.group(py):
                return None
            if ky == "multi" and (pz.op != "or") != (py.op != "or"):
                return None
            tp = max(tp, A.off(z, pz) - A.off(y, py))
            for (lz, _), (_, hy) in zip(pz.taps, py.taps):
                e = max(e, Fy[1] + hy - Fz[0] - lz)
        return max(e, 0), tp

    def _mk_pairs(self):
        N = self.M.nodes
        for k, (qc, a) in enumerate(sorted(getattr(self.M, "arbs", {}).items())):
            if a.get("mode") != "fix":
                continue
            R = a["R0"]
            for g in a["grants"]:
                if "arb:" + g in N:
                    self.rclass["arb:" + g] = k + 1
            for sh in a["shadows"]:
                # control --neg-rc: the shadows get a class of their own (HRst then says nothing
                # about grant vs shadow, and ParOK must fail)
                self.rclass[sh] = (k + 1 + 1000) if self.neg_rc else (k + 1)
            byb = {}
            for g in a["grants"]:
                v = "arb:" + g
                if v in N:
                    byb[N[v]["grant"]] = v
            for b, v in byb.items():
                sb = (1 - b) if self.neg_pair else b
                sh = f"vsh:{R}/{sb}"
                if sh not in N:
                    continue
                for z, y in ((v, sh), (sh, v)):
                    pm = list(range(len(N[y]["pins"])))
                    if len(N[z]["pins"]) != len(pm):
                        continue
                    r = self.lag(z, y, pm)
                    if r is None:
                        if not self.neg_pair:
                            self.par_err.append(f"pair {z} -> {y}: pins do not match")
                            continue
                        # control: claim the pair anyway with the lag of the matching shadow
                        r = (0, 0)
                    e, tp = r
                    self.pairs.setdefault(z, []).append((y, max(0, e - self.neg_lag), tp, pm))

    # ---------------- walk search (cert8's, plus PAR steps) -------------------------------
    def walk(self, a, goal, budget, ctx=None, closed=False):
        self._par_on = False
        r = super().walk(a, goal, budget, ctx, closed)
        if r is None and self.par_enabled and self.pairs:
            self._par_on = True
            try:
                r = super().walk(a, goal, budget, ctx, closed)
            finally:
                self._par_on = False
        return r

    def walk1(self, a, goal, budget, ctx, closed, rev):
        A, N = self.A, self.M.nodes
        best = [None]
        bestat = {}
        par_on = self._par_on

        def go(x, d, tok, ctx, depth, path):
            if x == goal and (path or not closed):
                if best[0] is None or d > best[0][0]:
                    best[0] = (d, tok, list(path))
                if not closed:
                    return
            if depth > DEPTH:
                return
            key = (x, ctx, tok)
            if bestat.get(key, NEG_INF) >= d:
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
                if par_on and ctx is None:
                    for (y, e, tp, pm) in self.pairs.get(x, ()):
                        if tok + tp <= budget:
                            go(y, d - e, tok + tp, None, depth + 1, path + [("PAR", x, (y, e, tp, pm))])
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

    # ---------------- walk -> log lines ---------------------------------------------------
    def sdelay(self, steps):
        """The search's delay of a step list (what the Lean conclusion computes, if the model's
        bands are the checker's)."""
        N, d = self.M.nodes, 0
        for kind, x, info in steps:
            nd = N[x]
            F = nd["F"][0]
            if kind in ("pin", "fpin"):
                d += F + nd["pins"][info].lo
            elif kind == "R3":
                d += F + info[3]
            elif kind == "SUB":
                d += F + nd["pins"][info[0]].lo
            elif kind == "PAR":
                d -= info[1]
        return d

    @staticmethod
    def pars(steps):
        return [i for i, s in enumerate(steps) if s[0] == "PAR"]

    def fold(self, L, dL, steps, ps):
        """Continue line L (delay dL, ending at the first PAR's source) through the PAR steps at
        indices ps of steps: one `par` line per step."""
        for n, i in enumerate(ps):
            kind, z, (y, e, tp, pm) = steps[i]
            seg = steps[i + 1:(ps[n + 1] if n + 1 < len(ps) else len(steps))]
            w2 = self.chain(seg, y)
            d2 = self.sdelay(seg)
            if e > dL + d2:
                raise Unsup(f"parallel step {z} -> {y}: lag {e} > walk delay {dL + d2}")
            L = self.line({"k": "par", "w1": L, "w2": w2, "z": self.idx[z], "y": self.idx[y],
                           "e": e, "tp": tp, "pm": pm})
            dL = dL + d2 - e
            self.npar_steps += 1
        return L

    def chain(self, steps, start):
        ps = self.pars(steps)
        if not ps:
            return super().chain(steps, start)
        pre = steps[:ps[0]]
        return self.fold(super().chain(pre, start), self.sdelay(pre), steps, ps)

    def build(self, steps, start, ctx):
        ps = self.pars(steps)
        if not ps:
            return super().build(steps, start, ctx)
        pre = steps[:ps[0]]
        return self.fold(super().build(pre, start, ctx), self.sdelay(pre), steps, ps)

    def dbuild(self, steps, start, ctx):
        ps = self.pars(steps)
        if not ps:
            return super().dbuild(steps, start, ctx)
        g, b = ctx
        for i, (kind, x, info) in enumerate(steps):
            if kind == "fpin":
                break
            if kind == "SUB":
                rest = [k for k in ps if k > i]
                if not rest:
                    break   # every PAR before the SUB: w1 (chain) carries them, cert8's dsub line
                ti, arms = info
                pins = self.M.nodes[x]["pins"]
                k0 = rest[0]
                w1 = self.chain(steps[:i], start)
                w2 = self.chain(steps[i + 1:k0], pins[ti].src)
                wW = self.walk(g[0], start, 1)
                if not wW:
                    raise Unsup("no first-reach walk S -> D")
                wS = self.build(wW[2], g[0], None)
                L = self.line({"k": "dsub9", "a": self.idx[start], "x": self.idx[x], "S": self.idx[g[0]],
                               "ab": ti, "arms": arms, "w1": w1, "w2": w2, "wS": wS})
                L = self.fold(L, self.sdelay(steps[:k0]), steps, rest)
                self.hyp.append({"k": "copy", "i": L})
                return len(self.hyp) - 1
        return super().dbuild(steps, start, ctx)


def main():
    os.environ.setdefault("PYTHONHASHSEED", "0")
    a = [x for x in sys.argv[1:] if not x.startswith("--")]
    neg_lag = 0
    for f in sys.argv[1:]:
        if f.startswith("--neg-lag="):
            neg_lag = int(f.split("=", 1)[1])
    C = CertP(a[0], a[1], par="--no-par" not in sys.argv, neg_lag=neg_lag, neg_pair="--neg-pair" in sys.argv,
              neg_rc="--neg-rc" in sys.argv,
              u3="--no-u3" not in sys.argv, nary="--no-nary" not in sys.argv,
              gline="--no-gline" not in sys.argv, guard="--no-guard" not in sys.argv)
    out = C.run7()
    for e in out["nodes"]:
        if e["name"] in C.rclass:
            e["rc"] = C.rclass[e["name"]]
    nws, bad = (0, []) if "--no-ws" in sys.argv else add_ws(out)
    out["errors"] += bad + C.par_err
    out["pairs"] = {C.idx[z]: [[C.idx[y], e, tp] for (y, e, tp, pm) in v] for z, v in C.pairs.items()}
    json.dump(out, open(a[2], "w"))
    nd = sum(1 for h in out["hyp"] if h["k"] == "dsub")
    npar = sum(1 for ln in out["log"] if ln["k"] == "par")
    nd9 = sum(1 for ln in out["log"] if ln["k"] == "dsub9")
    es = sorted(e for v in C.pairs.values() for (_, e, _, _) in v)
    print(f"model: virtual arbiter core = {out.get('arb_core')}, parallel pairs {sum(len(v) for v in C.pairs.values())} "
          f"(lag e min {es[0] if es else '-'} max {es[-1] if es else '-'} ps){' NEG-LAG ' + str(neg_lag) if neg_lag else ''}"
          f"{' NEG-PAIR' if C.neg_pair else ''}{' NEG-RC' if C.neg_rc else ''}{' NO-PAR' if not C.par_enabled else ''}")
    print(f"cert9p: {len(out['nodes'])} nodes, log {len(out['log'])} lines ({npar} par, {nd9} dsub9), back {len(out['back'])}, "
          f"lines {len(out['lines'])}, excl {len(out['excl'])}, guards {len(out['guards'])}, groups {out['groups']}, "
          f"parts {out['parts']}, dsub {nd} (wS given {nws}), errors {len(out['errors'])}")
    for e in out["errors"]:
        print("  UNCERTIFIED", e)


if __name__ == "__main__":
    main()
