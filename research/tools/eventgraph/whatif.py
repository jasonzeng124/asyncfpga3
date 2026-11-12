#!/usr/bin/env python3
"""whatif.py -- edit a timed event graph (eventgraph.py's nodes.tsv / arcs.tsv) instead of the design, and predict
the period (PROGRAM.md FIRST item, steps 2-3).  Library + CLI:

    whatif.py GRAPHDIR report                          period, critical cycle by stage, floor, next cycles
    whatif.py GRAPHDIR period EDIT [EDIT ...]           predicted period after the edits

EDITs (instances are bdc kernel instance names, e.g. ulink_n_trueResult_8):
    stage:PROD:CONS:SDELAY[:DACK[:fastrise]]   one bd_link stage on the channel PROD -> CONS (its C-element, a
                                               forward rdly of SDELAY chain elements, an ack delay of DACK)
    depth:LINK:SDELAY[:DACK]                   BDC_LINK_DEPTHS +1 on LINK (a stage on LINK's input channel)
    fastfall:INST                              every falling chain of INST falls in one element (bd_delay FASTFALL)
    nofall                                     every falling arc costs 0 (an upper bound on two-phase signalling)
Weights of the things an edit adds come from the same graph: a chain element is the median measured element of the
graph's chains (rise / fall separately), a C-element input is the arc it replaces.  Nothing is fitted.
"""
import sys, os, re, statistics as st, collections, copy
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import maxplus  # noqa: E402

CHAIN = re.compile(r"\.(udly|rdly|uack|us)\.chain\.g\[(\d+)\]")


def inst_of(cell):
    if not cell.startswith("bridge_i.udut."): return cell
    return cell[len("bridge_i.udut."):].split(".")[0].split("$")[0]


class G:
    def __init__(self, d):
        self.dir = d
        rows = [l.rstrip("\n").split("\t") for l in open(d + "/nodes.tsv")]
        h = rows[0]
        self.nodes = [dict(zip(h, r)) for r in rows[1:]]
        for n in self.nodes:
            n["id"] = int(n["id"]); n["phase"] = int(n["phase_ps"]); n["inst"] = inst_of(n.get("cell", ""))
        rows = [l.rstrip("\n").split("\t") for l in open(d + "/arcs.tsv")]
        h = rows[0]
        self.arcs = []
        for r in rows[1:]:
            a = dict(zip(h, r))
            self.arcs.append(dict(u=int(a["u"]), v=int(a["v"]), w=int(a["w_ps"]), o=int(a["offset"]),
                                  slack=int(a["slack_ps"]), kind=a["kind"], pin=a["pin"]))
        m = re.search(r"period P = (\d+)", open(d + "/check.txt").read())
        self.P = int(m.group(1))

    def copy(self):
        g = copy.copy(self); g.nodes = [dict(n) for n in self.nodes]; g.arcs = [dict(a) for a in self.arcs]
        return g

    def period(self):
        lam, cyc = maxplus.mcr(len(self.nodes), self.arcs)
        return lam, cyc

    # ---- measured element weights ------------------------------------------------------------------------------
    def elem(self):
        r, f = [], []
        for a in self.arcs:
            nu, nv = self.nodes[a["u"]], self.nodes[a["v"]]
            if CHAIN.search(nv.get("cell", "")) and CHAIN.search(nu.get("cell", "")) and nu["inst"] == nv["inst"]:
                (r if nv["edge"] == "R" else f).append(a["w"])
        return st.median(r), st.median(f)

    # ---- edits -------------------------------------------------------------------------------------------------
    def label_after(self, t, node):
        """iteration label of the first occurrence of node strictly after time t (t measured from t0)."""
        ph = self.nodes[node]["phase"]
        k = (t - ph) // self.P + 1
        return k, k * self.P + ph

    def stage(self, prod, cons, sdelay, dack=0, fastrise=False):
        """one bd_link stage S on the channel prod -> cons."""
        F = [i for i, a in enumerate(self.arcs) if self.nodes[a["u"]]["inst"] == prod and self.nodes[a["v"]]["inst"] == cons]
        B = [i for i, a in enumerate(self.arcs) if self.nodes[a["u"]]["inst"] == cons and self.nodes[a["v"]]["inst"] == prod]
        rn = {self.nodes[self.arcs[i]["u"]]["edge"]: self.arcs[i]["u"] for i in F}
        an = {self.nodes[self.arcs[i]["u"]]["edge"]: self.arcs[i]["u"] for i in B}
        if set(rn) != {"R", "F"} or set(an) != {"R", "F"} or \
                len({self.arcs[i]["u"] for i in F}) != 2 or len({self.arcs[i]["u"] for i in B}) != 2:
            raise ValueError("channel %s -> %s: req %s ack %s (need one req and one ack net, both edges)" % (
                prod, cons, sorted({self.nodes[self.arcs[i]["u"]]["name"] for i in F}),
                sorted({self.nodes[self.arcs[i]["u"]]["name"] for i in B})))
        eR, eF = self.elem()
        P = self.P
        # token m: r.R at its phase (label 0); then a.R, r.F, a.F in 4-phase order
        trR = self.nodes[rn["R"]]["phase"]
        l_aR, t_aR = self.label_after(trR, an["R"])
        l_rF, t_rF = self.label_after(t_aR, rn["F"])
        l_aF, t_aF = self.label_after(t_rF, an["F"])
        l_aFp = self.label_after(trR - P, an["F"])[0]
        if self.label_after(trR - P, an["F"])[1] >= trR:
            raise ValueError("channel %s -> %s is not 4-phase in the trace" % (prod, cons))
        sR, sF = len(self.nodes), len(self.nodes) + 1
        tag = "S[%s>%s]" % (prod, cons)
        self.nodes.append(dict(id=sR, name=tag + ".c", edge="R", phase=trR, inst=tag, cell=tag))
        self.nodes.append(dict(id=sF, name=tag + ".c", edge="F", phase=self.nodes[rn["F"]]["phase"], inst=tag, cell=tag))
        S = {"R": sR, "F": sF}
        fwd = {"R": sdelay * eR, "F": sdelay * eF}
        ack = {"R": (1 if fastrise and dack else dack) * eR, "F": dack * eF}
        cin = {}
        for i in F:
            a = self.arcs[i]; e = self.nodes[a["u"]]["edge"]
            cin.setdefault(e, a["w"])
            a["u"] = S[e]; a["w"] += fwd[e]
        cack = {}
        shift = {"R": l_aR - 0, "F": l_aF - l_rF}
        for i in B:
            a = self.arcs[i]; e = self.nodes[a["u"]]["edge"]
            cack.setdefault(e, a["w"])
            a["u"] = S[e]; a["w"] += ack[e]; a["o"] += shift[e]
        new = [dict(u=rn["R"], v=sR, w=cin["R"], o=0), dict(u=rn["F"], v=sF, w=cin["F"], o=0),
               dict(u=an["F"], v=sR, w=cack["F"], o=0 - l_aFp), dict(u=an["R"], v=sF, w=cack["R"], o=l_rF - l_aR)]
        for a in new:
            a.update(slack=0, kind="edit", pin="")
            if a["o"] < 0: raise ValueError("negative offset in the inserted stage: %s" % a)
        self.arcs += new
        return self

    def depth(self, link, sdelay, dack=0):
        """BDC_LINK_DEPTHS +1 on LINK: bd_pipe adds the new stage at the INPUT side (stage 0 takes SDELAY, the last
        stage keeps DELAY), so it is one stage on the channel (LINK's producer) -> LINK."""
        prods = {self.nodes[a["u"]]["inst"] for a in self.arcs
                 if self.nodes[a["v"]]["inst"] == link and self.nodes[a["u"]]["inst"] != link
                 and self.nodes[a["u"]]["edge"] == self.nodes[a["v"]]["edge"]
                 and not re.search(r"many\.stage\[[1-9]", self.nodes[a["v"]].get("cell", ""))}
        if len(prods) != 1: raise ValueError("depth %s: producer not unique: %s" % (link, prods))
        return self.stage(prods.pop(), link, sdelay, dack)

    def fastfall(self, inst):
        """chains of inst fall in one element: each falling chain element after the first follows the chain input."""
        eR, eF = self.elem(); n = 0
        for a in self.arcs:
            nu, nv = self.nodes[a["u"]], self.nodes[a["v"]]
            m = CHAIN.search(nv.get("cell", ""))
            if nv["inst"] == inst and m and nv["edge"] == "F" and CHAIN.search(nu.get("cell", "")) and nu["inst"] == inst:
                a["w"] = 0; n += 1      # the element follows the input's fall in parallel; the first element keeps its cost
        if not n: raise ValueError("fastfall: no chain of %s in the graph" % inst)
        return self

    def nofall(self):
        for a in self.arcs:
            if self.nodes[a["v"]]["edge"] == "F": a["w"] = 0
        return self

    def apply(self, ed):
        p = ed.split(":")
        if p[0] == "stage":
            return self.stage(p[1], p[2], int(p[3]), int(p[4]) if len(p) > 4 else 0, len(p) > 5 and p[5] == "fastrise")
        if p[0] == "depth": return self.depth(p[1], int(p[2]), int(p[3]) if len(p) > 3 else 0)
        if p[0] == "fastfall": return self.fastfall(p[1])
        if p[0] == "nofall": return self.nofall()
        raise ValueError(ed)

    # ---- reading a cycle -----------------------------------------------------------------------------------------
    def describe(self, cyc):
        by = collections.OrderedDict(); flips = []
        for i in cyc:
            a = i if isinstance(i, dict) else self.arcs[i]; v = self.nodes[a["v"]]; u = self.nodes[a["u"]]
            by.setdefault(v["inst"], [0, 0])
            by[v["inst"]][0 if v["edge"] == "R" else 1] += a["w"]
            if u["edge"] != v["edge"]: flips.append("%s%s->%s%s" % (u["inst"], u["edge"], v["inst"], v["edge"]))
        return by, flips


def polarity_floor(g):
    """worst cycle that never changes polarity: the rising-only and the falling-only subgraphs."""
    out = {}
    for e in ("R", "F"):
        keep = [a for a in g.arcs if g.nodes[a["u"]]["edge"] == e and g.nodes[a["v"]]["edge"] == e]
        try:
            lam, cyc = maxplus.mcr(len(g.nodes), keep)
        except ValueError as x:
            lam, cyc = float("nan"), []
        out[e] = (lam, [keep[i] for i in cyc])
    return out


def next_cycles(g, cyc, top=6):
    """the best cycle that avoids each arc of the critical cycle in turn: the cycles that bind next."""
    seen = {}
    for i in cyc:
        arcs = [a for j, a in enumerate(g.arcs) if j != i]
        lam, c2 = maxplus.mcr(len(g.nodes), arcs)
        if not c2: continue
        key = frozenset((arcs[j]["u"], arcs[j]["v"]) for j in c2)
        if key not in seen:
            seen[key] = (lam, [arcs[j] for j in c2], i)
    return sorted(seen.values(), key=lambda x: -x[0])[:top]


def main():
    d, cmd = sys.argv[1], sys.argv[2]
    g = G(d)
    if cmd == "period":
        base, _ = g.period()
        g2 = g.copy()
        for ed in sys.argv[3:]: g2.apply(ed)
        lam, cyc = g2.period()
        by, flips = g2.describe(cyc)
        print("base %.0f ps  edited %.0f ps  delta %+.0f ps  (%s)" % (base, lam, lam - base, " ".join(sys.argv[3:])))
        print("  cycle stages: %s" % ", ".join(by))
        print("  polarity changes: %s" % ", ".join(flips))
        return
    if cmd == "report":
        lam, cyc = g.period()
        by, flips = g.describe(cyc)
        print("period %.0f ps (trace %d); critical cycle %d arcs" % (lam, g.P, len(cyc)))
        for k, (r, f) in by.items(): print("  %-34s rise %6d  fall %6d" % (k, r, f))
        print("  polarity changes: %s" % ", ".join(flips))
        fl = polarity_floor(g)
        for e in ("R", "F"):
            l, c = fl[e]
            print("floor, %s-only cycles: %.0f ps (%d arcs: %s)" % (e, l, len(c), ", ".join(dict.fromkeys(g.nodes[a["v"]]["inst"] for a in c))))
        g0 = g.copy().nofall(); l0, c0 = g0.period()
        print("every falling arc 0 (two-phase bound): %.0f ps" % l0)
        for lam2, c2, i in next_cycles(g, cyc):
            b2, f2 = g.describe(c2)
            print("next: %.0f ps (slack %.0f) avoiding %s%s->%s%s: %s; flips %s" % (lam2, g.P - lam2,
                  g.nodes[g.arcs[i]["u"]]["inst"], g.nodes[g.arcs[i]["u"]]["edge"], g.nodes[g.arcs[i]["v"]]["inst"],
                  g.nodes[g.arcs[i]["v"]]["edge"], ", ".join(b2), ", ".join(f2)))


if __name__ == "__main__":
    main()
