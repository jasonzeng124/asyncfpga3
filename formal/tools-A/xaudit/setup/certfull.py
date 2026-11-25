"""certfull.py -- the certificate that xevents9par AND xfull (Events9FullMain.lean) check (UNTRUSTED).

    XA_ARB=fix python3 certfull.py SKEL.json BANDS.json MAP.json OUT.json [--ref CERT.json] [--no-junction]
                                   [--neg-ack K] [--neg-tok K] [--neg-su K] [--neg-form K]

Probe E9Setup (copy of selrun/certsel.py).  Builds the certificate exactly as par/cert9p.py (E9Par:
CORRECTED virtual arbiter core, parallel-pair lines, reset classes "rc", first-reach wS), checked
against --ref (E9Par's cert of the same seed/corner: same node list, so the map is valid), then
APPENDS to its derivation log the walk lines the select rows cite, and adds a "sel" section:

  sel.entries[]  one per map entry (real filtered pin, select literal):
     ta     the acknowledge wire's positive gate tree, ONE leaf (Events9SelL.AT; JSON
            {"leaf": n} or {"g": gate, "ch": [[input, tree], ...]})
     tq     the request wire's positive gate tree (an AND delay line: one leaf per element)
     na     the ack leaf node; ka its path (gate names)
     wq     per request leaf (in AT.leaves order) the log line of a walk leaf -> na, <= 1 token
     wa     the log line of a walk na -> src, no token (source-anchored AckLineT / AckLine)
     nq, kq E8Causal's ackOK data (first request leaf and its path), for the selL column only
     jc     per copy: the junction row {cut, blk, jw} (Events9SelJ), or null
     su     the setup row's data (Events9Setup.SU): {fw} (wire form) or {fw: false, jq, tl, lc} (stage form)
     scut   per copy: the setup cut (wire form: the copy path minus the request leaf's path; stage
            form: the source, bot = [])
  sel.blocks[]   junction logs {S, bot (path), lines (Events9SelJ.JLn)}

Everything here is search; the Lean executable re-checks every tree, line and row.
--no-junction omits jc.  --neg-ack K replaces the acknowledge of map entry K by its request wire
and --neg-tok K replaces wq of entry K by a 2-token walk (negative controls).  --neg-su K shifts the
setup cut of entry K by one hop toward the stage (wire form: the cut no longer is the request wire,
so suOK must fail); --neg-form K claims the other form for entry K.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "events8"))
sys.path.insert(0, os.path.join(HERE, "..", "events9"))
sys.path.insert(0, os.path.join(HERE, "..", "par"))
sys.path.insert(0, HERE)
from cert9 import add_ws  # noqa: E402
from cert9p import CertP  # noqa: E402
from gates import Gates  # noqa: E402


def initbit(G, sk, g, a):
    cn = g[:-2]
    c = sk["cells"][cn]
    return (int(c["parameters"]["INIT"], 2) >> a) & 1


def arg(flag):
    return sys.argv[sys.argv.index(flag) + 1] if flag in sys.argv else None


class SelCert:
    def __init__(self, skelp, bandp, top="gcd_ctl"):
        # exactly cert9p.py's main with its default flags
        self.C = C = CertP(skelp, bandp, par=True, u3=True, nary=True, gline=True, guard=True)
        self.out = out = C.run7()
        for e in out["nodes"]:
            if e["name"] in C.rclass:
                e["rc"] = C.rclass[e["name"]]
        self.nws, bad = add_ws(out)
        out["errors"] += bad + C.par_err
        out["pairs"] = {C.idx[z]: [[C.idx[y], e, tp] for (y, e, tp, pm) in v] for z, v in C.pairs.items()}
        self.G = Gates(skelp, bandp, top)
        self.sk = json.load(open(skelp))["modules"][top]
        self.nodes = out["nodes"]
        self.lut = {n["lut"]: i for i, n in enumerate(self.nodes) if not n["virt"]}
        self.parts = out["parts"]

    # ---------------- gates --------------------------------------------------------------
    def kof(self, g):
        return len(self.G.ins.get(g, []))

    def lut_init_all(self, g, idx):
        """INIT is 1 on every address with the bits idx set (Events9SelL.initAll)."""
        if g.endswith("/O"):
            k = self.kof(g)
            return all(initbit(self.G, self.sk, g, a) for a in range(2 ** k) if all((a >> i) & 1 for i in idx))
        return True  # a routed arc is a 1-input buffer

    def child(self, g, i):
        """The gate driving input i of gate g, or None (constant)."""
        w = self.G.ins[g][i]
        if w[0] == "const":
            return None
        if g.endswith("/O"):
            return f"{g[:-2]}/I{i}"
        return self.G.drv.get(w)

    def leaf_ok(self, n):
        nd = self.nodes[n]
        return not nd["virt"] and not nd["v"]

    def up_tree(self, g, depth=0):
        """Candidates (tree, leaf, path) for a ONE-leaf positive tree rooted at gate g."""
        if g in self.lut:
            n = self.lut[g]
            return [({"leaf": n}, n, [])] if self.leaf_ok(n) else []
        if depth > 80 or g not in self.G.ins:
            return []
        out = []
        for i in range(self.kof(g)):
            if not self.lut_init_all(g, [i]):
                continue
            c = self.child(g, i)
            if c is None:
                continue
            for t, n, p in self.up_tree(c, depth + 1):
                out.append(({"g": g, "ch": [[i, t]]}, n, [[g, i]] + p))
        return out

    def and_tree(self, g, depth=0):
        """A positive tree rooted at gate g listing ALL its (non-constant) inputs, down to nodes."""
        if g in self.lut:
            n = self.lut[g]
            return {"leaf": n} if self.leaf_ok(n) else None
        if depth > 200 or g not in self.G.ins:
            return None
        idx = [i for i in range(self.kof(g)) if self.child(g, i) is not None]
        if not idx or not self.lut_init_all(g, idx):
            return None
        ch = []
        for i in idx:
            t = self.and_tree(self.child(g, i), depth + 1)
            if t is None:
                return None
            ch.append([i, t])
        return {"g": g, "ch": ch}

    @staticmethod
    def leaves(t, path=()):
        if "leaf" in t:
            return [(t["leaf"], list(path))]
        out = []
        for i, s in t["ch"]:
            out += SelCert.leaves(s, path + ([t["g"], i],))
        return out

    # ---------------- copies -----------------------------------------------------------------
    def copies(self, n, k):
        nd = self.nodes[n]
        p = nd["pins"][k]
        if p.get("st"):
            cs = [p["top"] + [[p["sg"], p["sci"]]] + p["bot"]]
        else:
            cs = p["paths"]
        return [[[nd["lut"], p["ip"]]] + c for c in cs]

    def off(self, n, k):
        nd = self.nodes[n]
        p = nd["pins"][k]
        return int((bool(self.nodes[p["src"]]["v"]) ^ bool(p["inv"]) ^ bool(p["neg"])) != bool(nd["v"]))

    def loP(self, n, k):
        return min(self.G.plo(f) for f in self.copies(n, k)) - 1

    # ---------------- main-log walks -----------------------------------------------------------
    def wline(self, a, goal, budget):
        """(line, d) of a walk a -> goal with <= budget tokens (d as estimated by the search)."""
        C = self.C
        an, gn = C.names[a], C.names[goal]
        if a == goal:
            return C.line({"k": "refl", "a": a}), 0
        w = C.walk(an, gn, budget)
        if w is None:
            return None
        return C.build(w[2], an, None), w[0]

    # ---------------- labels -------------------------------------------------------------
    def lx(self, l1, l2):
        if l1[0] == l2[0]:
            return l1[1] != l2[1]
        if not (l1[1] and l2[1]):
            return False
        return any(l1[0] in P and l2[0] in P for P in self.parts)


class Block:
    """One junction log (Events9SelJ.JLn) for a source S and a lower part bot."""

    def __init__(self, sc, S, bot):
        self.sc, self.S, self.bot = sc, S, bot
        self.lines, self.memo = [], {}
        self.jud = []  # (u, a, lab, d) per line

    def add(self, ln, jud):
        key = json.dumps(ln, sort_keys=True)
        if key not in self.memo:
            self.memo[key] = len(self.lines)
            self.lines.append(ln)
            self.jud.append(jud)
        return self.memo[key]

    def fac(self, n, k):
        """The largest e with facOK(bot, n, k, e) (Events9SelJ), or None: per copy, through the
        junction (the copy path ends with bot: e = plo(top) - 1) or lifted from the source
        (e = loC - phi bot)."""
        sc, bot = self.sc, self.bot
        if sc.nodes[n]["virt"]:
            return None
        phb = sc.G.phi(bot)
        es = []
        for f in sc.copies(n, k):
            c = []
            if len(bot) < len(f) and f[len(f) - len(bot):] == bot:
                c.append(sc.G.plo(f[:len(f) - len(bot)]) - 1)
            if sc.G.plo(f) - 1 >= phb:
                c.append(sc.G.plo(f) - 1 - phb)
            if not c:
                return None
            es.append(max(c))
        return min(es)

    def judgements(self):
        """All junction lines derivable for nodes reading S: jpin / juT, then jr3 at merges."""
        sc, S = self.sc, self.S
        walk = {}  # node -> best (line, d) walk judgement
        ub = {}    # (node, lab) -> best (line, d) U-bound
        for n, nd in enumerate(sc.nodes):
            if nd["virt"]:
                continue
            for k, p in enumerate(nd["pins"]):
                if p["src"] != S or sc.off(n, k):
                    continue
                e = self.fac(n, k)
                if e is None:
                    continue
                if not nd["mg"] and p["pk"] != "guard":
                    d = 1 + e
                    i = self.add({"k": "jpin", "n": n, "p": k, "e": e}, (False, n, None, d))
                    if n not in walk or walk[n][1] < d:
                        walk[n] = (i, d)
                    if p["pk"] == "filt":
                        lab = (p["grp"], p["br"])
                        i = self.add({"k": "juT", "n": n, "p": k, "e": e}, (True, n, lab, d))
                        if (n, lab) not in ub or ub[(n, lab)][1] < d:
                            ub[(n, lab)] = (i, d)
        # arms that do not pass the junction: the main log's uT line of a filtered pin of S, lifted
        # (jlift: lag d - phi bot)
        phb = sc.G.phi(self.bot)
        for n, nd in enumerate(sc.nodes):
            if nd["virt"] or nd["mg"]:
                continue
            for k, p in enumerate(nd["pins"]):
                if p["src"] != S or p["pk"] != "filt" or sc.off(n, k):
                    continue
                d = 1 + sc.loP(n, k)
                if d < phb:
                    continue
                w = sc.C.line({"k": "uT", "T": n, "q": k})
                lab = (p["grp"], p["br"])
                i = self.add({"k": "jlift", "w": w}, (True, n, lab, d - phb))
                if (n, lab) not in ub or ub[(n, lab)][1] < d - phb:
                    ub[(n, lab)] = (i, d - phb)
        # merges: every arm a filtered pin through the junction or a U-bound of its source
        for xm, nd in enumerate(sc.nodes):
            if nd["virt"] or not nd["mg"]:
                continue
            arms, ds = [], []
            for k, p in enumerate(nd["pins"]):
                best = None
                if p["pk"] == "filt" and p["src"] == S and not sc.off(xm, k):
                    e = self.fac(xm, k)
                    if e is not None:
                        best = (dict(g=p["grp"], b=p["br"], dir=True, e=e, ref=0), e)
                for (t, lab), (i, d) in ub.items():
                    if t == p["src"]:
                        c = (dict(g=lab[0], b=lab[1], dir=False, e=0, ref=i), sc.loP(xm, k) + d)
                        if best is None or c[1] > best[1]:
                            best = c
                if best is None:
                    break
                arms.append(best[0])
                ds.append(best[1])
            if len(arms) != len(nd["pins"]) or len(arms) < 1:
                continue
            labs = [(a["g"], a["b"]) for a in arms]
            if not all(sc.lx(labs[i], labs[j]) for i in range(len(labs)) for j in range(len(labs)) if i != j):
                continue
            d = 1 + min(ds)
            i = self.add({"k": "jr3", "xm": xm, "arms": arms}, (False, xm, None, d))
            if xm not in walk or walk[xm][1] < d:
                walk[xm] = (i, d)
        if not self.bot:
            i = self.add({"k": "jrefl"}, (False, S, None, 0))
            if S not in walk:
                walk[S] = (i, 0)
        self.walk = walk

    def lag(self, na):
        """(jw line, dj) of the best token-free walk judgement of na, or None."""
        best = None
        for X, (r, dX) in self.walk.items():
            w = self.sc.wline(na, X, 0)
            if w is None:
                continue
            wl, dw = w
            dj = dw + dX
            if best is None or dj > best[2]:
                best = (wl, r, dj)
        if best is None:
            return None
        wl, r, dj = best
        jw = self.add({"k": "jwalk", "w": wl, "r": r}, (False, na, None, dj))
        return jw, dj


def setup_data(sc, n, k, S, rqg, tq, flip=False):
    """(su, scut) for Events9Setup.suOK, or (None, None).  Wire form: the request tree is ONE leaf
    (S, pi) and every copy path of the pin ends with pi (scut = len(copy) - len(pi) - 1).  Stage
    form: S is a real non-merge node with a pin q (offset 0, AND line or 1-copy plain) whose copies
    are topJ ++ pi_l for the request leaves (topJ = the part above the request gate rqg); every copy
    cut at the source (scut = len(copy) - 1).  flip: claim the other form (negative control)."""
    if tq is None:
        return None, None
    lv = SelCert.leaves(tq)
    cps = sc.copies(n, k)
    N = sc.nodes
    wire = None
    if len(lv) == 1 and lv[0][0] == S:
        pi = lv[0][1]
        if all(len(f) > len(pi) and f[len(f) - len(pi):] == pi for f in cps):
            wire = (dict(fw=True), [len(f) - len(pi) - 1 for f in cps])
    stage = None
    if not N[S]["virt"] and not N[S]["mg"] and lv:
        for q, pq in enumerate(N[S]["pins"]):
            if sc.off(S, q):
                continue
            if not ((pq["pk"] == "multi" and pq.get("op", True)) or (pq["pk"] == "plain" and pq["ncopies"] == 1)):
                continue
            cj = sc.copies(S, q)
            tops, ok = None, True
            lc = []
            for (ln, lp) in lv:
                if ln != pq["src"]:
                    ok = False
                    break
                hit = None
                for ci, f in enumerate(cj):
                    if len(f) >= len(lp) and f[len(f) - len(lp):] == lp:
                        t = f[:len(f) - len(lp)]
                        if tops is None or t == tops:
                            hit = ci
                            tops = t
                            break
                if hit is None:
                    ok = False
                    break
                lc.append(hit)
            if ok and tops is not None:
                # Lean takes topJ = (full of copy lc[0]).take tl
                stage = (dict(fw=False, jq=q, tl=len(tops), lc=lc), [len(f) - 1 for f in cps])
                break
    if flip:
        if wire:
            return stage or (dict(fw=False, jq=0, tl=0, lc=[0] * len(lv)), [len(f) - 1 for f in cps])
        return dict(fw=True), [len(f) - 1 for f in cps]
    return wire or stage or (None, None)


def main():
    os.environ.setdefault("PYTHONHASHSEED", "0")
    a = [x for x in sys.argv[1:] if not x.startswith("--")]
    for f in ("--ref", "--neg-ack", "--neg-tok", "--neg-su", "--neg-form"):
        v = arg(f)
        if v in a:
            a.remove(v)
    skelp, bandp, mapp, outp = a[:4]
    sc = SelCert(skelp, bandp)
    out, G = sc.out, sc.G
    ref = arg("--ref")
    if ref:
        rn = [n["name"] for n in json.load(open(ref))["nodes"]]
        if rn != [n["name"] for n in sc.nodes]:
            print("certsel: node list differs from --ref; map not valid")
            sys.exit(3)
    mp = json.load(open(mapp))
    negack = int(arg("--neg-ack")) if arg("--neg-ack") else None
    negtok = int(arg("--neg-tok")) if arg("--neg-tok") else None
    negsu = int(arg("--neg-su")) if arg("--neg-su") else None
    negform = int(arg("--neg-form")) if arg("--neg-form") else None
    blocks, bidx = [], {}
    ents, probs = [], []
    stats = dict(ta=0, tq=0, wq=0, wa=0, jc=0, copies=0, suw=0, sus=0, sun=0)
    for ei, e in enumerate(mp["entries"]):
        n, k, lit = e["node"], e["pin"], e["lit"]
        p = sc.nodes[n]["pins"][k]
        S = p["src"]
        ak = e["rq"] if ei == negack else e["ak"]
        ent = dict(node=n, pin=k, lit=lit)
        cand = sc.up_tree(ak)
        if not cand:
            probs.append(f"entry {ei} {sc.nodes[n]['name']} pin{k} lit{lit}: no one-leaf ack tree from {ak}")
            ents.append(ent)
            continue
        tq = sc.and_tree(e["rq"])

        def feasible(c):
            # every request leaf has a walk to the ack leaf whose (estimated) delay covers
            # phi(ka) - plo(leaf path) (Events9SelL.ReqLineT)
            if tq is None:
                return False
            for (q, pth) in SelCert.leaves(tq):
                w = sc.wline(q, c[1], 1)
                if w is None or w[1] < G.phi(c[2]) - G.plo(pth):
                    return False
            return True
        ok = [c for c in cand if feasible(c)]
        ta, na, ka = max(ok or cand, key=lambda c: G.plo(c[2]))
        stats["ta"] += 1
        ent.update(ta=ta, na=na, ka=ka)
        if tq is None:
            probs.append(f"entry {ei}: no request tree from {e['rq']}")
        else:
            stats["tq"] += 1
            ent["tq"] = tq
            lv = SelCert.leaves(tq)
            ent["nq"], ent["kq"] = lv[0]
            wq = []
            for (q, pth) in lv:
                w = sc.wline(q, na, 2 if ei == negtok else 1)
                if ei == negtok:
                    # a 2-token walk (q -> na -> q -> na): the protocol line must reject it
                    w1 = sc.wline(q, na, 1)
                    w2 = sc.wline(na, q, 1)
                    w = None
                    if w1 and w2:
                        C = sc.C
                        st = C.walk(C.names[q], C.names[na], 1)[2] + C.walk(C.names[na], C.names[q], 1)[2] + \
                            C.walk(C.names[q], C.names[na], 1)[2]
                        w = (C.build(st, C.names[q], None), 0)
                wq.append(w[0] if w else 1000000000)
            ent["wq"] = wq
            if all(x < 1000000000 for x in wq):
                stats["wq"] += 1
            else:
                probs.append(f"entry {ei}: no walk from a request leaf to the ack leaf")
        w = sc.wline(na, S, 0)
        if w:
            ent["wa"] = w[0]
            stats["wa"] += 1
        else:
            probs.append(f"entry {ei}: no token-free walk ack leaf -> src")
        if "--no-junction" not in sys.argv:
            jcs = []
            for f in sc.copies(n, k):
                stats["copies"] += 1
                best = None
                for cut in range(len(f)):
                    bot = f[cut + 1:]
                    key = (S, json.dumps(bot))
                    if key not in bidx:
                        B = Block(sc, S, bot)
                        B.judgements()
                        bidx[key] = len(blocks)
                        blocks.append(B)
                    B = blocks[bidx[key]]
                    r = B.lag(na)
                    if r is None:
                        continue
                    jw, dj = r
                    Dl = dj + G.plo(ka) + 1
                    mg = Dl - G.phi(f[:cut + 1])
                    if best is None or mg > best[0]:
                        best = (mg, dict(cut=cut, blk=bidx[key], jw=jw))
                jcs.append(best[1] if best else None)
                if best:
                    stats["jc"] += 1
            ent["jc"] = jcs
        su, scut = setup_data(sc, n, k, S, e["rq"], tq, negform == ei)
        if su is None:
            stats["sun"] += 1
            probs.append(f"entry {ei}: no setup form")
            su, scut = dict(fw=True), [0] * len(sc.copies(n, k))
        elif su["fw"]:
            stats["suw"] += 1
        else:
            stats["sus"] += 1
        if negsu == ei:
            scut = [c - 1 if c > 0 else c + 1 for c in scut]
        ent["su"], ent["scut"] = su, scut
        ents.append(ent)
    used = sorted({jc["blk"] for e in ents for jc in e.get("jc", []) if jc})
    remap = {b: i for i, b in enumerate(used)}
    for e in ents:
        for jc in e.get("jc", []):
            if jc:
                jc["blk"] = remap[jc["blk"]]
    out["log"] = list(sc.C.log)
    out["sel"] = dict(entries=ents, blocks=[dict(S=blocks[b].S, bot=blocks[b].bot, lines=blocks[b].lines) for b in used])
    json.dump(out, open(outp, "w"))
    print(f"certsel: {len(sc.nodes)} nodes, log {len(out['log'])} lines (wS {sc.nws}), map entries {len(ents)}: "
          f"ack trees {stats['ta']}, request trees {stats['tq']}, request walks {stats['wq']}, ack walks {stats['wa']}, "
          f"junction rows {stats['jc']}/{stats['copies']} copies, blocks {len(used)}, setup forms wire {stats['suw']} "
          f"stage {stats['sus']} none {stats['sun']}, errors {len(out['errors'])}; model: virtual arbiter core = {out.get('arb_core')}")
    for x in probs:
        print("  PROBLEM", x)


if __name__ == "__main__":
    main()
