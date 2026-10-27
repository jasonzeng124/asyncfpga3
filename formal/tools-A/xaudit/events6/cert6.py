"""cert6.py -- emit the CERTIFICATE that xevents5 (Events5Main.lean) checks (UNTRUSTED).

    python3 cert6.py SKEL.json BANDS.json OUT.json

Everything here is untrusted search: the Lean checker re-verifies the recognition
(Recog6: every INIT, every tree / steer / feedback / reset path) and every walk
derivation.  Output (JSON):
  nodes[]  one per Net4 node (real C-element stages, real merges = OR gates of different
           sources, and the H_ARB virtual nodes vctl / grants / R0): Net4 fields, RNode data
           (LUT gate, feedback/reset paths, per pin: LUT input, folded select, tree paths or
           steer split), and for virtual nodes their bands.
  rank[]   merge rank (acyclic OR gates)
  back     per stage pin: a DW derivation (R1/fpin/R3/SUB/lift), or absent
  lines    per line pin: a closed DW derivation of the source, or absent
  excl     per merge: S-walk DW + U-arm witnesses, or absent
Paths are lists of [gate name, input index]; gate names are Parse's: "<cell>/O" for a LUT,
"<cell>/I<k>" for the routed arc into pin k of <cell>.
Uses events4's Model / Ana (H_ARB virtual core, U sets, R3) unchanged.
"""
import collections
import itertools
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "events4"))
from model import Model  # noqa: E402
from ana import Ana, DEPTH  # noqa: E402
from classify import live_pins, gate_fn  # noqa: E402

sys.setrecursionlimit(10000)


class Unsup(Exception):
    pass


class Cert:
    def __init__(self, netp, bandp):
        self.M = M = Model(netp, bandp)
        self.A = A = Ana(M)
        self.n = M.n
        self.names = list(M.nodes)
        self.idx = {x: i for i, x in enumerate(self.names)}
        self.grp = {}
        self.res = A.run()
        self._ok = {}
        self.rule = {}
        for e in self.res["stages"]:
            self.rule[(e["stage"], e["pin"])] = e["rule"]

    # ---------------- groups -------------------------------------------------
    def gid(self, key):
        if key not in self.grp:
            self.grp[key] = len(self.grp)
        return self.grp[key]

    def grp_br(self, p):
        g, b = self.A.group(p)
        if len(b) == 1:
            return self.gid(g), bool(b[0])
        return self.gid((g, b)), True

    # ---------------- netlist paths -------------------------------------------
    def src_of_net(self, net):
        n, s, M = self.n, self.M.s, self.M
        cn = n.drv.get(net)
        if cn is None:
            return None
        if cn in s.kind and s.kind[cn]["kind"] == "cel":
            return cn
        if cn in M.arbout:
            return "arb:" + cn
        if "merge:" + cn in M.nodes:
            return "merge:" + cn
        return None

    def below(self, net):
        """Paths from `net` (a gate output wire) down to its source node's output wire.
        Returns (src, parity, op, [paths]) where a path is a list of [gate, idx] and may
        contain one ['STEER', ...] marker element."""
        r = self.src_of_net(net)
        if r is not None:
            return (r, 0, None, [[]])
        n = self.n
        cn = n.drv[net]
        c = n.cells[cn]
        live = live_pins(n, cn)
        tt = gate_fn(n, cn, live)
        ctl = [k for k in live if self.M.s.ctl_net(c["ins"][k])]
        sel = [k for k in live if k not in ctl]
        if len(ctl) == 1 and not sel:
            k = ctl[0]
            sub = self.below(c["ins"][k])
            if tt == (0, 1):
                inv = 0
            elif tt == (1, 0):
                inv = 1
            else:
                raise Unsup(f"1-input gate {cn}")
            return (sub[0], sub[1] ^ inv, sub[2],
                    [[[cn + "/O", k], [f"{cn}/I{k}", 0]] + p for p in sub[3]])
        if len(ctl) == 1 and sel:
            k = ctl[0]
            sub = self.below(c["ins"][k])
            if sub[1] != 0 or len(sub[3]) != 1:
                raise Unsup(f"steer {cn} on a non-plain tap")
            for pat in itertools.product([0, 1], repeat=len(sel)):
                ok = all(
                    gate_fn_eval(n, cn, live, vals) == (vals[live.index(k)] & int(all(vals[live.index(s)] == b for s, b in zip(sel, pat))))
                    for vals in itertools.product([0, 1], repeat=len(live)))
                if ok:
                    mark = ["STEER", cn + "/O", k, [[s, bool(b)] for s, b in zip(sel, pat)]]
                    return (sub[0], 0, None, [[mark, [f"{cn}/I{k}", 0]] + sub[3][0]])
            raise Unsup(f"gate {cn} not a steer")
        if sel:
            raise Unsup(f"gate {cn} mixes control and select")
        if all(v == int(all(vals)) for v, vals in zip(tt, itertools.product([0, 1], repeat=len(live)))):
            op = True
        elif all(v == int(any(vals)) for v, vals in zip(tt, itertools.product([0, 1], repeat=len(live)))):
            op = False
        else:
            raise Unsup(f"gate {cn} not AND/OR")
        subs = [self.below(c["ins"][k]) for k in live]
        srcs = {s_[0] for s_ in subs}
        if len(srcs) != 1:
            raise Unsup(f"gate {cn}: several sources but not a merge node")
        lists = []
        for k, s_ in zip(live, subs):
            if s_[1] != 0 or (s_[2] is not None and s_[2] != op and len(s_[3]) > 1):
                raise Unsup(f"gate {cn}: inverted or mixed sub-line")
            if any(e[0] == "STEER" for p in s_[3] for e in p):
                raise Unsup(f"gate {cn}: steer inside a line")
            lists.append([[[cn + "/O", k], [f"{cn}/I{k}", 0]] + p for p in s_[3]])
        # order the copies so that consecutive copies meet with a small window (Beh4.hskew is
        # stated for consecutive copies): orient each child's list at the boundary greedily
        res = lists[0]
        for L in lists[1:]:
            best = None
            for A_ in (res, res[::-1]):
                for B_ in (L, L[::-1]):
                    w = self.pairw(A_[-1], B_[0])
                    if best is None or w < best[0]:
                        best = (w, A_ + B_)
            res = best[1]
        return (subs[0][0], 0, op, res)

    def eband(self, e):
        nm, i = e
        n = self.n
        b = n.lutband(nm[:-2]) if nm.endswith("/O") else n.arc.get(nm)
        return (max(1, b[0]), max(1, b[0], b[1]))

    def pairw(self, P, Q):
        """Events6Gate.pairW (python mirror, for ordering only; Lean recomputes)."""
        c = 0
        while c < min(len(P), len(Q)) and P[c] == Q[c]:
            c += 1
        a, a2 = P[c:], Q[c:]
        z = 0
        while z < min(len(a), len(a2)) and a[len(a) - 1 - z] == a2[len(a2) - 1 - z]:
            z += 1
        m, m2, zz = a[:len(a) - z], a2[:len(a2) - z], a[len(a) - z:]
        lo = lambda S: sum(self.eband(e)[0] for e in S)
        hi = lambda S: sum(self.eband(e)[1] for e in S)
        return max(hi(m) - lo(m2), hi(m2) - lo(m), 0) + hi(zz) - lo(zz)

    def pin_data(self, cn, ip):
        """Pin entering LUT cn at input ip."""
        net = self.n.cells[cn]["ins"][ip]
        src, par, op, paths = self.below(net)
        paths = [[[f"{cn}/I{ip}", 0]] + p for p in paths]
        d = dict(ip=ip, src=src, inv=bool(par), op=True if op is None else op)
        st = [p for p in paths if any(e[0] == "STEER" for e in p)]
        if st:
            p = st[0]
            i = [k for k, e in enumerate(p) if e[0] == "STEER"][0]
            m = p[i]
            d.update(st=True, top=p[:i], sg=m[1], sci=m[2], ssel=m[3], bot=p[i + 1:], ncopies=1)
        else:
            d.update(st=False, paths=paths, ncopies=len(paths))
        return d

    # ---------------- U witnesses ---------------------------------------------
    def is_guard(self, x, k):
        return self.rule.get((x, k)) == "Guard"

    def uwit(self, a, g, b, depth=0, seen=None):
        """UArmD witness: token-free R1 walk from node a to a stage T whose filtered pin q is
        (group g, branch b). Returns (T, q, walk) with walk = [(node, pin)], or None."""
        A = self.A
        seen = seen or set()
        if a in seen or depth > 30:
            return None
        nd = self.M.nodes.get(a)
        if not nd or nd["kind"] != "cel" or not nd["pins"]:
            return None
        seen = seen | {a}
        for k, p in enumerate(nd["pins"]):
            if A.off(a, p) == 0 and p.filt and p.inv == 0 and A.v(p.src) == 0 and A.group(p) == (g, b):
                return (a, k, [])
        for k, p in enumerate(nd["pins"]):
            if A.off(a, p) == 0 and p.inv == 0 and not self.is_guard(a, k) and (g, b) in A.U[p.src]:
                r = self.uwit(p.src, g, b, depth + 1, seen)
                if r:
                    return (r[0], r[1], [(a, k)] + r[2])
        return None

    def ua(self, x, arm, g, b):
        """U-arm certificate of arm `arm` of merge x: direct when the arm is itself a filtered
        pin of (g, b) (UArmX's second case), else a UArmD walk."""
        A = self.A
        p = self.M.nodes[x]["pins"][arm]
        if p.filt and p.inv == 0 and A.v(p.src) == 0 and A.off(x, p) == 0 and A.group(p) == (g, b):
            return dict(T=0, q=0, w=[], dir=True)
        arm_src = p.src
        r = self.uwit(arm_src, g, b)
        if r is None:
            raise Unsup(f"no U witness from {arm_src} for {g} {b}")
        T, q, w = r
        return dict(T=self.idx[T], q=q, w=[[self.idx[x], k] for x, k in w])

    # ---------------- walks -> DW ---------------------------------------------
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
                    nctx = A.group(p) if filt else ctx
                    go(p.src, d + F + p.lo, tok + o, nctx, depth + 1,
                       path + [("fpin" if filt else "pin", x, k)])
            else:
                r = A.r3.get(x)
                if r and self.r3ok(x, r):
                    go(r[0], d + F + min(p.lo for p in nd["pins"]), tok, ctx, depth + 1, path + [("R3", x, r)])
                if ctx is not None:
                    g, b = ctx
                    for ti, p in enumerate(nd["pins"]):
                        if p.filt:
                            continue
                        if A.sub_ok(x, ti, g, b) and self.subok(x, ti, g, b):
                            go(p.src, d + F + p.lo, tok, None, depth + 1, path + [("SUB", x, (ti, g, b))])
        go(a, 0, 0, ctx, 0, [])
        return best[0]

    def r3ok(self, x, r):
        """Only use R3 steps the Lean derivation can express (binary, 1-bit group, U-arms
        certifiable without U3)."""
        key = ("r3", x)
        if key not in self._ok:
            try:
                self.r3_arms(x, r)
                self._ok[key] = True
            except Unsup:
                self._ok[key] = False
        return self._ok[key]

    def subok(self, x, ti, g, b):
        key = ("sub", x, ti, g, b)
        if key not in self._ok:
            try:
                pins = self.M.nodes[x]["pins"]
                if len(pins) != 2 or len(b) != 1:
                    raise Unsup("x")
                self.ua(x, 1 - ti, g, (1 - b[0],))
                self._ok[key] = True
            except Unsup:
                self._ok[key] = False
        return self._ok[key]

    def r3_arms(self, x, r):
        """(S, g, a0, a1, u0, u1) for a binary merge with R3 over a 1-bit group."""
        S, g = r
        pins = self.M.nodes[x]["pins"]
        if len(pins) != 2:
            raise Unsup(f"R3 at a {len(pins)}-arm merge {x}")
        opts = [sorted(bb for (gg, bb) in self.A.tapU(p) if gg == g) for p in pins]
        for b0 in opts[0]:
            for b1 in opts[1]:
                if b0 != b1 and len(b0) == 1 and len(b1) == 1:
                    a0, a1 = (0, 1) if b0 == (0,) else (1, 0)
                    u0 = self.ua(x, a0, g, (0,))
                    u1 = self.ua(x, a1, g, (1,))
                    return S, self.gid(g), a0, a1, u0, u1
        raise Unsup(f"R3 at {x}: arms not two branches of a 1-bit group")

    def chain(self, steps, start):
        if not steps:
            return {"k": "refl", "a": self.idx[start]}
        kind, x, info = steps[0]
        rest = steps[1:]
        if kind == "pin":
            p = self.M.nodes[x]["pins"][info]
            return {"k": "r1", "n": self.idx[x], "p": info, "r": self.chain(rest, p.src)}
        if kind == "fpin":
            p = self.M.nodes[x]["pins"][info]
            g, br = self.grp_br(p)
            return {"k": "fpin", "n": self.idx[x], "p": info, "r": self.build(rest, p.src, self.A.group(p))}
        if kind == "R3":
            S, g, a0, a1, u0, u1 = self.r3_arms(x, info)
            return {"k": "r3", "x": self.idx[x], "S": self.idx[S], "g": g, "a0": a0, "a1": a1,
                    "u0": u0, "u1": u1, "r": self.chain(rest, S)}
        raise Unsup("SUB without a branch context")

    def build(self, steps, start, ctx):
        if ctx is None:
            return self.chain(steps, start)
        g, b = ctx
        if len(b) != 1:
            raise Unsup("branch context of a multi-bit group")
        gi, beta = self.gid(g), bool(b[0])
        for i, (kind, x, info) in enumerate(steps):
            if kind == "fpin":
                break
            if kind == "SUB":
                ti, g2, b2 = info
                if (g2, b2) != ctx:
                    raise Unsup("SUB in another context")
                pins = self.M.nodes[x]["pins"]
                if len(pins) != 2:
                    raise Unsup("SUB at a non-binary merge")
                anu = 1 - ti
                w1 = self.chain(steps[:i], start)
                u = self.ua(x, anu, g, (1 - b[0],))
                w2 = self.chain(steps[i + 1:], pins[ti].src) if all(s[0] != "fpin" for s in steps[i + 1:]) \
                    else self.build(steps[i + 1:], pins[ti].src, None)
                return {"k": "sub", "x": self.idx[x], "g": gi, "b": beta, "ab": ti, "an": anu,
                        "w1": w1, "u": u, "w2": w2}
        return {"k": "lift", "g": gi, "b": beta, "r": self.chain(steps, start)}

    # ---------------- assembly ------------------------------------------------
    def run(self):
        M, A, n = self.M, self.A, self.n
        nodes, errs = [], []
        for x in self.names:
            nd = M.nodes[x]
            virt = bool(nd.get("virtual"))
            mg = nd["kind"] == "merge"
            e = dict(name=x, virt=virt, mg=mg, v=bool(nd["v"]), pins=[])
            pins = nd["pins"] or []
            cn = x[len("merge:"):] if x.startswith("merge:") else x
            if not virt:
                e["lut"] = cn + "/O"
                if not mg:
                    m = M.s.kind[cn]
                    e.update(qi=m["q"], ri=m["r"], qp=[[f"{cn}/I{m['q']}", 0]], rp=[[f"{cn}/I{m['r']}", 0]])
                    ips = m["reqs"]
                else:
                    ips = live_pins(n, cn)
            else:
                e["F"] = list(nd["F"])
                e["Q"] = [max(1, nd["Q"][0]), max(1, nd["Q"][1])] if nd["Q"] else [1, 1]
                if x.startswith("arb:"):
                    e["ow"] = n.cells[x[4:]]["out"]
                    e["owname"] = x[4:] + "/O"
            for k, p in enumerate(pins):
                pe = dict(src=self.idx[p.src], inv=bool(p.inv), neg=bool(p.pol), op=(p.op != "or"),
                          pk="multi" if p.kind == "multi" else ("filt" if p.filt else
                                                                 ("guard" if self.is_guard(x, k) else "plain")))
                if p.filt:
                    pe["grp"], pe["br"] = self.grp_br(p)
                else:
                    pe["grp"], pe["br"] = 0, False
                pe["gp"] = 0
                if pe["pk"] == "guard":
                    gi = A.guard_info(x, p)
                    if gi:
                        S, g, b, q = gi
                        cands = [kk for kk, pp in enumerate(pins) if (g, b) in A.tapU(pp) and not self.is_guard(x, kk)]
                        pe["gp"] = cands[0] if cands else 0
                if not virt:
                    try:
                        pd = self.pin_data(cn, ips[k])
                        if pd["src"] != p.src:
                            raise Unsup(f"pin source {pd['src']} != model {p.src}")
                        if not mg:
                            m = M.s.kind[cn]
                            if m["filt"] is not None and m["filt"][0] == ips[k]:
                                pd["fold"] = [[s, bool(b)] for s, b in zip(m["sel"], m["filt"][1])]
                        pe.update(pd)
                        pe["src"] = self.idx[p.src]
                    except Unsup as ex:
                        errs.append(f"{x} pin{k}: {ex}")
                else:
                    pe["lo"] = [t[0] for t in p.taps]
                    pe["hi"] = [t[1] for t in p.taps]
                    pe["ncopies"] = len(p.taps)
                    pe["dw"] = 0
                e["pins"].append(pe)
            nodes.append(e)
        # virtual line windows: contig5's per-pin window (H_ARB carries them)
        for m in self.res.get("multis", []):
            pass
        # rank of merges
        rank = {}

        def rk(x, stack=()):
            if x in rank:
                return rank[x]
            if x in stack:
                raise Unsup("merge cycle")
            nd = M.nodes[x]
            r = 0
            if nd["kind"] == "merge" and not nd.get("virtual"):
                for p in nd["pins"]:
                    s = M.nodes[p.src]
                    if s["kind"] == "merge" and not s.get("virtual"):
                        r = max(r, rk(p.src, stack + (x,)) + 1)
            rank[x] = r
            return r
        for x in self.names:
            rk(x)
        # certificates
        back, lines, excl = {}, {}, {}
        for j, nd in M.nodes.items():
            if not nd["pins"]:
                continue
            if nd["kind"] == "cel":
                for k, p in enumerate(nd["pins"]):
                    if self.is_guard(j, k):
                        continue
                    o = A.off(j, p)
                    filt = p.filt and p.inv == 0 and A.v(p.src) == 0
                    ctx = A.group(p) if p.filt else None
                    w = self.walk(p.src, j, 1 - o, ctx=ctx) if o <= 1 else None
                    if not w:
                        wa = A.walk(p.src, j, 1 - o, ctx=ctx) if o <= 1 else None
                        errs.append(f"back {j} pin{k}: " + ("no walk without an R3/SUB step Lean cannot express "
                                                            "(U3 / W-E4x)" if wa else "no walk"))
                        continue
                    try:
                        back[f"{self.idx[j]}/{k}"] = self.build(w[2], p.src, ctx)
                    except Unsup as ex:
                        errs.append(f"back {j} pin{k}: {ex}")
            for k, p in enumerate(nd["pins"]):
                if p.kind == "multi":
                    w = self.walk(p.src, p.src, 1, closed=True)
                    if not w:
                        wa = A.walk(p.src, p.src, 1, closed=True)
                        errs.append(f"line {j} pin{k}: " + ("no cycle without an R3/SUB step Lean cannot express "
                                                            "(U3 / W-E4x)" if wa else "no cycle"))
                        continue
                    try:
                        lines[f"{self.idx[j]}/{k}"] = self.build(w[2], p.src, None)
                    except Unsup as ex:
                        errs.append(f"line {j} pin{k}: {ex}")
            if nd["kind"] == "merge":
                r = A.r3.get(j)
                if not r:
                    errs.append(f"excl {j}: no R3")
                    continue
                try:
                    S, g, a0, a1, u0, u1 = self.r3_arms(j, r)
                    w = self.walk(S, j, 1)
                    if not w:
                        raise Unsup("no walk S -> merge")
                    excl[str(self.idx[j])] = dict(g=g, a0=a0, a1=a1, D=self.build(w[2], S, None), u0=u0, u1=u1)
                except Unsup as ex:
                    errs.append(f"excl {j}: {ex}")
        return dict(nodes=nodes, rank=[rank[x] for x in self.names], back=back, lines=lines, excl=excl,
                    errors=errs, groups=len(self.grp))


def gate_fn_eval(n, cn, live, vals):
    from classify import evalf
    return evalf(n, cn, dict(zip(live, vals)))


def main():
    os.environ.setdefault("PYTHONHASHSEED", "0")
    C = Cert(sys.argv[1], sys.argv[2])
    out = C.run()
    json.dump(out, open(sys.argv[3], "w"))
    print(f"cert6: {len(out['nodes'])} nodes, back {len(out['back'])}, lines {len(out['lines'])}, "
          f"excl {len(out['excl'])}, groups {out['groups']}, errors {len(out['errors'])}")
    for e in out["errors"]:
        print("  UNCERTIFIED", e)


if __name__ == "__main__":
    main()
