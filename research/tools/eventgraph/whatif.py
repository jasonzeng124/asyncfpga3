#!/usr/bin/env python3
"""whatif.py -- edit a timed event graph (eventgraph.py's nodes.tsv / arcs.tsv) instead of the design, and predict
the period (PROGRAM.md FIRST item, steps 2-3).  Library + CLI:

    whatif.py GRAPHDIR report                          period, critical cycle by stage, floor, next cycles
    whatif.py GRAPHDIR period EDIT [EDIT ...]           predicted period after the edits

EDITs (instances are bdc kernel instance names, e.g. ulink_n_trueResult_8):
    stage:REQ:ACK:SDELAY[:DACK[:fastrise]]     one bd_link stage on the channel (REQ, ACK) (kernel Verilog nets): its
                                               C-element, a forward rdly of SDELAY elements, an ack delay of DACK
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
        self.elem()

    def copy(self):
        g = copy.copy(self); g.nodes = [dict(n) for n in self.nodes]; g.arcs = [dict(a) for a in self.arcs]
        return g

    def period(self):
        lam, cyc = maxplus.mcr(len(self.nodes), self.arcs)
        return lam, cyc

    # ---- measured element weights ------------------------------------------------------------------------------
    def elem(self):
        """median measured chain element (rise, fall) of the BASE graph (cached before any edit)."""
        if getattr(self, "_elem", None): return self._elem
        r, f = [], []
        for a in self.arcs:
            nu, nv = self.nodes[a["u"]], self.nodes[a["v"]]
            if CHAIN.search(nv.get("cell", "")) and CHAIN.search(nu.get("cell", "")) and nu["inst"] == nv["inst"]:
                (r if nv["edge"] == "R" else f).append(a["w"])
        self._elem = (st.median(r), st.median(f))
        return self._elem

    # ---- edits -------------------------------------------------------------------------------------------------
    def label_after(self, t, node):
        """iteration label of the first occurrence of node strictly after time t (t measured from t0)."""
        ph = self.nodes[node]["phase"]
        k = (t - ph) // self.P + 1
        return k, k * self.P + ph

    # ---- the kernel Verilog: instances, ports, fork aliases ------------------------------------------------------
    def verilog(self):
        if hasattr(self, "_vl"): return self._vl
        src = open(self.dir + "/kernel.v").read()
        insts = {}
        for m in re.finditer(r"^\s*(\w+)\s*(?:#\((.*?)\))?\s+(u\w+)\s*\((.*?)\);", src, re.S | re.M):
            typ, par, inst, body = m.groups()
            ports = {}
            for p, x in re.findall(r"\.(\w+)\(((?:[^()]|\([^()]*\))*)\)", body):
                ports[p] = [t for t in re.findall(r"[A-Za-z_]\w*", x) if not re.match(r"^\d", t)]
            insts[inst] = (typ, par or "", ports)
        self._vl = insts
        return insts

    def listing(self, net):
        return {i for i, (t, p, ports) in self.verilog().items() if any(net in v for v in ports.values())}

    def downstream(self, net):
        """net plus every fork output it fans out to (a bd_fork passes its request through as a wire)."""
        out, todo = set(), [net]
        while todo:
            n = todo.pop()
            if n in out: continue
            out.add(n)
            for i, (t, p, ports) in self.verilog().items():
                if t == "bd_fork" and n in ports.get("req", []):
                    todo += ports.get("req_out", [])
        return out

    def node_of(self, net, exclude=()):
        """the graph nodes {edge: id} of a Verilog net (its physical net may carry an alias's name)."""
        names = {"bridge_i.udut." + n for n in self.downstream(net)}
        # upstream through a fork too: a fork output is the fork input
        for i, (t, p, ports) in self.verilog().items():
            if t == "bd_fork" and net in ports.get("req_out", []):
                names |= {"bridge_i.udut." + n for n in self.downstream(ports["req"][0])}
        got = {}
        for n in self.nodes:
            if n["name"] in names: got.setdefault(n["edge"], set()).add(n["id"])
        if not got:
            # a link whose DACK (DELAY) is 0 has no net of its own for ack_in (req_out): it is the C-element's output,
            # which the netlist names after the other alias
            for i, (t, p, ports) in self.verilog().items():
                if t not in ("bd_link", "bd_pipe"): continue
                cells = []
                if net in ports.get("ack_in", []):
                    cells = [i + ".ctl.u.u", i + ".many.stage[0].u.ctl.u.u"]
                elif net in ports.get("req_out", []):
                    nst = int(re.search(r"\.N\((\d+)\)", p).group(1)) if ".N(" in p else 1
                    cells = [i + ".ctl.u.u", i + ".many.stage[%d].u.ctl.u.u" % (nst - 1)]
                for n in self.nodes:
                    if n.get("cell", "")[len("bridge_i.udut."):] in cells:
                        got.setdefault(n["edge"], set()).add(n["id"])
        if set(got) != {"R", "F"} or any(len(v) != 1 for v in got.values()):
            raise ValueError("net %s: graph nodes %s" % (net, got))
        return {e: v.pop() for e, v in got.items()}

    def stage(self, req, ack, sdelay, dack=0, fastrise=False):
        """one bd_link stage S on the channel (req, ack) (Verilog net names): S takes the request from its producer
        and acknowledges it; every consumer of the request (through forks) now sees S's request after S's forward
        delay; every user of the acknowledge now sees S's acknowledge after S's ack delay."""
        rn, an = self.node_of(req), self.node_of(ack)
        cons = set()
        for n in self.downstream(req): cons |= self.listing(n)
        prod = self.nodes[rn["R"]]["inst"]; adrv = self.nodes[an["R"]]["inst"]
        cons -= {prod}; cons = {c for c in cons if self.verilog()[c][0] != "bd_fork"}
        users = self.listing(ack) - {adrv}
        F = [i for i, a in enumerate(self.arcs) if a["u"] in rn.values() and self.nodes[a["v"]]["inst"] in cons]
        B = [i for i, a in enumerate(self.arcs) if a["u"] in an.values() and self.nodes[a["v"]]["inst"] in users]
        if not F or not B:
            raise ValueError("channel %s/%s: %d request arcs into %s, %d ack arcs into %s" % (req, ack, len(F), cons,
                                                                                            len(B), users))
        return self._insert(rn, an, F, B, sdelay, dack, fastrise, "S[%s]" % req)

    def _insert(self, rn, an, F, B, sdelay, dack, fastrise, tag):
        req = ack = tag
        eR, eF = self.elem()
        P = self.P
        # token m: r.R at its phase (label 0); then a.R, r.F, a.F in 4-phase order
        trR = self.nodes[rn["R"]]["phase"]
        l_aR, t_aR = self.label_after(trR, an["R"])
        l_rF, t_rF = self.label_after(t_aR, rn["F"])
        l_aF, t_aF = self.label_after(t_rF, an["F"])
        l_aFp, t_aFp = self.label_after(trR - P, an["F"])
        if t_aFp >= trR:
            raise ValueError("channel %s/%s is not 4-phase in the trace" % (req, ack))
        sR, sF = len(self.nodes), len(self.nodes) + 1
        self.nodes.append(dict(id=sR, name=tag + ".c", edge="R", phase=trR, inst=tag, cell=tag))
        self.nodes.append(dict(id=sF, name=tag + ".c", edge="F", phase=self.nodes[rn["F"]]["phase"], inst=tag, cell=tag))
        S = {"R": sR, "F": sF}
        fwd = {"R": sdelay * eR, "F": sdelay * eF}
        ackd = {"R": (1 if fastrise and dack else dack) * eR, "F": dack * eF}
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
            a["u"] = S[e]; a["w"] += ackd[e]; a["o"] += shift[e]
        x = getattr(self, "stage_wire", 0)   # extra wire per inserted stage, on every input arc of it (both edges)
        new = [dict(u=rn["R"], v=sR, w=cin["R"] + x, o=0), dict(u=rn["F"], v=sF, w=cin["F"] + x, o=0),
               dict(u=an["F"], v=sR, w=cack["F"] + x, o=0 - l_aFp), dict(u=an["R"], v=sF, w=cack["R"] + x, o=l_rF - l_aR)]
        for a in new:
            a.update(slack=0, kind="edit", pin="")
            if a["o"] < 0: raise ValueError("negative offset in the inserted stage: %s" % a)
        self.arcs += new
        return self

    def depth(self, link, sdelay, dack=0):
        """BDC_LINK_DEPTHS +1 on LINK: bd_pipe adds the new stage at the INPUT side (stage 0 takes SDELAY, the last
        stage keeps DELAY), so it is one stage on LINK's input channel (req_in, ack_in)."""
        t, par, ports = self.verilog()[link]
        c0 = {link + ".ctl.u.u", link + ".many.stage[0].u.ctl.u.u"}
        cn = {n["edge"]: n["id"] for n in self.nodes if n.get("cell", "")[len("bridge_i.udut."):] in c0}
        F = [i for i, a in enumerate(self.arcs) if a["v"] in cn.values() and self.nodes[a["u"]]["inst"] != link
             and self.nodes[a["u"]]["edge"] == self.nodes[a["v"]]["edge"]]
        rn = {self.nodes[self.arcs[i]["u"]]["edge"]: self.arcs[i]["u"] for i in F}
        if len({self.arcs[i]["u"] for i in F}) != 2 or set(rn) != {"R", "F"}:
            raise ValueError("depth %s: request into stage 0 not one net: %s" % (link, F))
        users = self.listing(ports["ack_in"][0]) - {link}
        B = [i for i, a in enumerate(self.arcs) if a["u"] in cn.values() and self.nodes[a["v"]]["inst"] in users]
        if not B:
            # the producer side may itself have been replaced by an inserted stage (its instance is S[...])
            B = [i for i, a in enumerate(self.arcs) if a["u"] in cn.values()
                 and self.nodes[a["v"]]["inst"] == self.nodes[rn["R"]]["inst"]]
        if not B: raise ValueError("depth %s: no acknowledge users" % link)
        self.deepened = getattr(self, "deepened", set()) | {link}
        return self._insert(rn, cn, F, B, sdelay, dack, False, "S[%s]" % link)

    def stage_cells(self):
        """{ctl cell name: (link instance, stage k, n stages)} for every link stage C-element in the graph."""
        out = {}
        for inst, (t, par, ports) in self.verilog().items():
            if t == "bd_link": out["bridge_i.udut.%s.ctl.u.u" % inst] = (inst, 0, 1)
            if t == "bd_pipe":
                n = int(re.search(r"\.N\((\d+)\)", par).group(1))
                for k in range(n):
                    out["bridge_i.udut.%s.many.stage[%d].u.ctl.u.u" % (inst, k)] = (inst, k, n)
        return out

    def deco(self, cell):
        """Replace one link stage's C-element (bd_c2n) by the decoupled controller of
        cells/verify/attempts/bd_deco_attempt.v (one token a stage):
            L = Rin.(L + ~F.~Aout)   latch enable = Ain      F = ~Aout.(Rin + F)      R = ~Aout.(R + F.~L)
        so Ain follows Rin both ways while the stage is free, the latch closes on Rin's fall, and the outgoing
        request rises only after that (F high, L low).  Arc weights are the replaced C-element's: Rin's and Aout's
        arcs keep their wire + arc, the controller's internal arcs (F->L, F/L->R) take one C-element arc each."""
        sc = self.stage_cells()
        if cell not in sc: raise ValueError("deco: %s is not a link stage" % cell)
        inst, k, nst = sc[cell]
        cn = {n["edge"]: n["id"] for n in self.nodes if n.get("cell") == cell}
        if set(cn) != {"R", "F"}: raise ValueError("deco: %s not in the graph" % cell)
        ins = [a for a in self.arcs if a["v"] in cn.values()]
        same = [a for a in ins if self.nodes[a["u"]]["edge"] == self.nodes[a["v"]]["edge"]]
        opp = [a for a in ins if self.nodes[a["u"]]["edge"] != self.nodes[a["v"]]["edge"]]
        rin = {self.nodes[a["v"]]["edge"]: a for a in same}       # c.R <- Rin.R, c.F <- Rin.F
        aout = {self.nodes[a["v"]]["edge"]: a for a in opp}       # c.R <- Aout.F, c.F <- Aout.R
        if set(rin) != {"R", "F"} or set(aout) != {"R", "F"} or len(same) != 2 or len(opp) != 2:
            raise ValueError("deco: %s inputs are not (Rin, Aout): %d same %d opposite" % (cell, len(same), len(opp)))
        # forward targets of c: its own rdly, the next stage, or (rdly bypassed) the consumer; the rest are ack users
        t, par, ports = self.verilog()[inst]
        own = "bridge_i.udut.%s." % inst + ("" if nst == 1 else "many.stage[%d].u." % k)
        nxt = "bridge_i.udut.%s.many.stage[%d].u.ctl" % (inst, k + 1)
        cons = set()
        if k == nst - 1:
            for n in self.downstream(ports["req_out"][0]): cons |= self.listing(n)
            cons = {c for c in cons - {inst} if self.verilog()[c][0] != "bd_fork"}
        outs = [a for a in self.arcs if a["u"] in cn.values()]
        def fwd(a):
            v = self.nodes[a["v"]]; c = v.get("cell", "")
            return c.startswith(own + "rdly") or c.startswith(nxt) or v["inst"] in cons
        # labels of token m: c.R_m = 0, c.F_m = lF (from the base trace's phases)
        ph = {e: self.nodes[cn[e]]["phase"] for e in "RF"}
        lF = 1 if ph["F"] < ph["R"] else 0
        lab = {"R": 0, "F": lF}
        base = len(self.nodes); ids = {}
        for nm in ("L", "Fs", "Ro"):
            for e in "RF":
                ids[(nm, e)] = len(self.nodes)
                self.nodes.append(dict(id=len(self.nodes), name="%s.deco.%s" % (cell, nm), edge=e,
                                       phase=ph[e], inst=inst, cell="%s.deco.%s" % (cell, nm)))
        wint = st.median([rin["R"]["w"], rin["F"]["w"], aout["R"]["w"], aout["F"]["w"]])
        L, Fs, Ro = (lambda e: ids[("L", e)]), (lambda e: ids[("Fs", e)]), (lambda e: ids[("Ro", e)])
        new = []
        def add(u, v, w, o): new.append(dict(u=u, v=v, w=w, o=o, slack=0, kind="deco", pin=""))
        # token m labels: L.R, Fs.R, Ro.R, at 0; L.F, Fs.F, Ro.F at lF.  Source events keep their base offsets.
        oRR, oRF = rin["R"]["o"], rin["F"]["o"]          # c.R_m <- Rin.R_m (offset), c.F_m <- Rin.F_m
        oAF, oAR = aout["R"]["o"], aout["F"]["o"]        # c.R_m <- Aout.F_{m-1}, c.F_m <- Aout.R_m
        add(rin["R"]["u"], L("R"), rin["R"]["w"], oRR)               # L rises on Rin ...
        add(aout["R"]["u"], L("R"), aout["R"]["w"], oAF)             # ... with Aout low (previous token released)
        add(Fs("F"), L("R"), wint, 1 - lF)                           # ... and F low (stage empty)
        add(rin["R"]["u"], Fs("R"), rin["R"]["w"] + wint, oRR)       # F sets on Rin (after L, one arc)
        add(aout["R"]["u"], Fs("R"), aout["R"]["w"], oAF)
        add(rin["F"]["u"], L("F"), rin["F"]["w"], oRF)               # the latch closes on Rin's fall alone
        add(Fs("R"), Ro("R"), wint, lF)                              # R rises: F high ...
        add(L("F"), Ro("R"), wint, 0 - 0)                            # ... and L low (label of L.F_m is lF: R.R_m too)
        add(aout["R"]["u"], Ro("R"), aout["R"]["w"], oAF + lF)       # ... and Aout low
        add(aout["F"]["u"], Ro("F"), aout["F"]["w"], oAR)            # R falls on Aout's rise
        add(aout["F"]["u"], Fs("F"), aout["F"]["w"] + wint, oAR)     # F clears on Aout's rise (Rin already low)
        # Ro.R_m carries label lF; fix the L.F -> Ro.R offset accordingly (both lF)
        # outputs: forward targets read Ro, ack users read L
        for a in outs:
            e = self.nodes[a["u"]]["edge"]
            if fwd(a):
                a["u"] = Ro(e); a["o"] = a["o"] - (lF if e == "R" else 0)
            else:
                a["u"] = L(e)
        self.arcs = [a for a in self.arcs if a["v"] not in cn.values()] + new
        # the old c nodes stay (isolated): ids remain stable
        return self

    def fastfall(self, inst, strict=True):
        """chains of inst fall in one element: each falling chain element after the first follows the chain input."""
        eR, eF = self.elem(); n = 0
        for a in self.arcs:
            nu, nv = self.nodes[a["u"]], self.nodes[a["v"]]
            m = CHAIN.search(nv.get("cell", ""))
            if nv["inst"] == inst and m and nv["edge"] == "F" and CHAIN.search(nu.get("cell", "")) and nu["inst"] == inst:
                a["w"] = 0; n += 1      # the element follows the input's fall in parallel; the first element keeps its cost
        if not n and strict: raise ValueError("fastfall: no chain of %s in the graph" % inst)
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
        if p[0] == "deco": return self.deco("bridge_i.udut." + p[1] if not p[1].startswith("bridge_i") else p[1])
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


def next_cycles(g, cyc, top=8):
    """for each stage (kernel instance) on the critical cycle: the worst cycle that does not pass through it (all
    arcs into that stage's edges removed).  Distinct cycles, worst first: what binds next, and its slack."""
    seen = {}
    insts = list(dict.fromkeys(g.nodes[g.arcs[i]["v"]]["inst"] for i in cyc))
    for x in insts:
        arcs = [a for a in g.arcs if g.nodes[a["v"]]["inst"] != x]
        lam, c2 = maxplus.mcr(len(g.nodes), arcs)
        if not c2: continue
        key = frozenset((arcs[j]["u"], arcs[j]["v"]) for j in c2)
        seen.setdefault(key, (lam, [arcs[j] for j in c2], []))[2].append(x)
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
        for lam2, c2, xs in next_cycles(g, cyc):
            b2, f2 = g.describe(c2)
            print("next: %.0f ps (slack %.0f) without %s: %s; polarity changes %d" % (lam2, g.P - lam2, "/".join(xs),
                  ", ".join(b2), len(f2)))


if __name__ == "__main__":
    main()
