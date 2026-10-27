"""model.py -- build the counter-domain model of the control skeleton (UNTRUSTED).

Nodes (each a LUT output, or a VIRTUAL arbiter node -- see H_ARB):
  cel    C-element stage (classify.cel_match): reset value v, LUT band F, own-feedback arc Q,
         pins = Pin objects
  merge  a stateless OR of taps from DIFFERENT sources (cond_br ack OR, mux z OR, nested):
         count = sum of tap counts (exclusivity certified separately)
  vctl / vg / vR0   the arbiter core replaced by the virtual mux core of H_ARB
Pins (what a node reads; delays are summed along the path: routed arcs + stateless LUTs):
  Pin.kind 'tap'   one source, plain (parity inv) or FILTERED (steer literal: sel nets, pattern)
           'multi' one source, several taps combined by AND or OR (FASTFALL / FASTRISE delay lines)
All delays in ps from the routed2x band file (per arc, per LUT).
"""
import itertools
from netlib import Net
from classify import Skel, gate_fn, live_pins, evalf


class Pin:
    def __init__(self, kind, src, taps, op=None, inv=0, filt=None, pol=0):
        self.kind, self.src, self.taps, self.op = kind, src, taps, op
        self.inv, self.filt, self.pol = inv, filt, pol  # pol: LUT bubble on this pin
        self.guard = None

    @property
    def lo(self):
        return min(t[0] for t in self.taps)

    @property
    def hi(self):
        return max(t[1] for t in self.taps)

    def __repr__(self):
        f = f" filt={self.filt}" if self.filt else ""
        return f"<{self.kind} {self.src} inv={self.inv}{f} taps={self.taps} op={self.op}>"


class Unrec(Exception):
    pass


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


class Model:
    def __init__(self, netp, bandp):
        self.n = n = Net(netp, bandp)
        self.s = s = Skel(n)
        self.nodes = {}
        self.unrec = []
        self.arbs = {}
        self.arbq = {n.cells[c]["out"]: c for c, m in s.kind.items() if m["kind"] == "arb"}
        self.arbout = {}  # stateless LUT reading an arbiter q: name -> arbiter state cell
        for cn, c in n.cells.items():
            for b in c["ins"]:
                if b in self.arbq and cn not in s.kind:
                    self.arbout[cn] = self.arbq[b]
        # stage nodes
        for cn, m in s.kind.items():
            if m["kind"] == "cel":
                self.nodes[cn] = dict(kind="cel", v=m["v"], F=n.lutband(cn),
                                      Q=n.arcband(cn, m["q"]), pins=None, m=m)
        for cn, m in s.kind.items():
            if m["kind"] == "cel":
                self.build_cel(cn, m)
        self.build_arbs()

    # ---- expression -> pin -------------------------------------------------
    def leaf(self, net, band):
        """Normalise the control net `net` read through an arc of band `band`.
        Returns ('tap', src, inv, filt, band) | ('multi', op, src, inv, [bands]) | ('sel', net)."""
        n, s = self.n, self.s
        if net not in n.drv:
            raise Unrec(f"net {net} has no driver (free input {n.inputs.get(net)})")
        cn = n.drv[net]
        if cn in s.kind:
            if s.kind[cn]["kind"] == "cel":
                return ("tap", cn, 0, None, band)
            raise Unrec(f"reads arbiter state {cn} directly")
        if cn in self.arbout:
            return ("tap", "arb:" + cn, 0, None, band)
        if not s.ctl_net(net):
            return ("sel", net)
        c = n.cells[cn]
        live = live_pins(n, cn)
        F = n.lutband(cn)
        subs = [self.leaf(c["ins"][i], add(band, add(F, n.arcband(cn, i)))) for i in live]
        # careful: band of a sub = arc into this gate + this gate's LUT + downstream band
        ctl = [k for k, x in enumerate(subs) if x[0] != "sel"]
        sel = [k for k, x in enumerate(subs) if x[0] == "sel"]
        tt = gate_fn(n, cn, live)
        if len(ctl) == 1 and not sel:
            x = subs[0]
            if tt == (0, 1):
                return x
            if tt == (1, 0):
                if x[0] == "tap":
                    return ("tap", x[1], x[2] ^ 1, x[3], x[4])
                return ("multi", x[1], x[2], x[3] ^ 1, x[4], x[5], x[6])
            raise Unrec(f"1-input gate {cn} constant")
        if len(ctl) == 1 and sel:
            # steer: out = (ctl ^ p) & [sel == pat] ?
            x = subs[ctl[0]]
            if x[0] != "tap" or x[3] is not None:
                raise Unrec(f"steer {cn} on a non-plain tap")
            k = ctl[0]
            for p in (0, 1):
                for pat in itertools.product([0, 1], repeat=len(sel)):
                    ok = all(
                        tt[sum(b << (len(live) - 1 - i) for i, b in enumerate(vals))] ==
                        ((vals[k] ^ p) & int(all(vals[j] == q for j, q in zip(sel, pat))))
                        for vals in itertools.product([0, 1], repeat=len(live)))
                    if ok:
                        if (x[2] ^ p) != 0:
                            raise Unrec(f"steer {cn} on an inverted request")
                        selnets = tuple(subs[j][1] for j in sel)
                        return ("tap", x[1], 0, (selnets, pat), x[4])
            raise Unrec(f"gate {cn}: control+select function not a steer AND")
        if sel:
            raise Unrec(f"gate {cn} mixes several control inputs with select inputs")
        # all inputs control: AND / OR of literals
        kind = None
        for op in ("and", "or"):
            for pols in itertools.product([0, 1], repeat=len(live)):
                ok = True
                for vals in itertools.product([0, 1], repeat=len(live)):
                    lits = [v ^ p for v, p in zip(vals, pols)]
                    want = int(all(lits)) if op == "and" else int(any(lits))
                    idx = sum(b << (len(live) - 1 - i) for i, b in enumerate(vals))
                    if tt[idx] != want:
                        ok = False
                        break
                if ok:
                    kind = (op, pols)
                    break
            if kind:
                break
        if not kind:
            raise Unrec(f"gate {cn}: function {tt} over {len(live)} control inputs is not AND/OR")
        op, pols = kind
        if any(pols):
            raise Unrec(f"gate {cn}: {op} with inverted inputs")
        srcof = lambda x: x[1] if x[0] == "tap" else x[2]
        srcs = {srcof(x) for x in subs}
        if len(srcs) == 1:
            # same-source multi-tap (delay line)
            invs = {x[2] if x[0] == "tap" else x[3] for x in subs}
            if len(invs) != 1 or any(x[0] == "tap" and x[3] for x in subs):
                raise Unrec(f"gate {cn}: same-source {op} with mixed parity/filters")
            bands = []
            reps, win = [], 0
            for x in subs:
                if x[0] == "tap":
                    bands.append(x[4])
                    reps.append(x[4])
                else:
                    if x[1] != op:
                        raise Unrec(f"gate {cn}: mixed AND/OR delay line")
                    bands.extend(x[4])
                    reps.append(x[6])
                    win = max(win, x[5])
            # contiguity, locally: the fastest copy of each input (a representative of its
            # contiguous count set) must lie within one event of the next one: window between
            # consecutive representatives (shared downstream path cancels)
            rs = sorted(reps)
            for a_, b_ in zip(rs, rs[1:]):
                win = max(win, max(a_[1], b_[1]) - min(a_[0], b_[0]))
            return ("multi", op, srcof(subs[0]), invs.pop(), bands, win, rs[0])
        if op != "or":
            raise Unrec(f"gate {cn}: AND of different sources")
        # merge node at this OR gate
        name = "merge:" + cn
        if name not in self.nodes:
            taps = []
            for i, x in zip(live, subs):
                # recompute the tap band as seen at this gate's input (arc only, upstream)
                xs = self.leaf(c["ins"][i], n.arcband(cn, i))
                if xs[0] == "sel" or (xs[2] if xs[0] == "tap" else xs[3]) != 0:
                    raise Unrec(f"merge {cn}: arm {i} is inverted or a select")
                taps.append(self.mkpin(xs, 0))
            self.nodes[name] = dict(kind="merge", v=0, F=F, Q=None, pins=taps)
        return ("tap", name, 0, None, band)

    def mkpin(self, x, pol):
        if x[0] == "tap":
            return Pin("tap", x[1], [x[4]], inv=x[2], filt=x[3], pol=pol)
        if x[0] == "multi":
            pn = Pin("multi", x[2], list(x[4]), op=x[1], inv=x[3], pol=pol)
            pn.win = x[5]
            return pn
        raise Unrec("select net as a request")

    def build_cel(self, cn, m):
        n = self.n
        c = n.cells[cn]
        pins = []
        try:
            for ri, pol in zip(m["reqs"], m["pols"]):
                x = self.leaf(c["ins"][ri], n.arcband(cn, ri))
                p = self.mkpin(x, pol)
                if m["filt"] is not None and m["filt"][0] == ri:
                    if p.kind != "tap" or p.filt is not None:
                        raise Unrec("folded steer on a non-plain tap")
                    p.filt = (tuple(c["ins"][j] for j in m["sel"]), m["filt"][1])
                pins.append(p)
        except Unrec as e:
            self.unrec.append((cn, str(e)))
            self.nodes[cn]["pins"] = None
            return
        self.nodes[cn]["pins"] = pins

    # ---- H_ARB: the arbiter core as a virtual mux core ----------------------
    def build_arbs(self):
        n = self.n
        for qc in self.arbq.values():
            outs = [c for c, a in self.arbout.items() if a == qc]
            st = n.cells[qc]
            # A0 = the pin of the state LUT that is neither r1, r2, q, rst: identify from ugrant pins
            gr = [c for c in outs if "ugrant" in c]
            r0 = [c for c in outs if "ustate" in c]
            if len(gr) != 2 or len(r0) != 1:
                self.unrec.append((qc, f"arbiter outputs not recognised: {outs}"))
                continue
            q = st["out"]
            reqnets = [b for b in n.cells[gr[0]]["ins"] if isinstance(b, int) and b != q]
            a0 = [b for b in st["ins"] if isinstance(b, int) and b not in reqnets and b != q and b != n.rst]
            if len(reqnets) != 2 or len(a0) != 1:
                self.unrec.append((qc, "arbiter pins not recognised"))
                continue
            a0 = a0[0]
            # which grant reads which request: g_b = r_b & (q ...): find the request whose
            # rise alone (other low) raises the grant for some q
            gmap = {}
            for g in gr:
                live = live_pins(n, g)
                for r in reqnets:
                    hits = 0
                    for qv in (0, 1):
                        vals = {}
                        for i in live:
                            b = n.cells[g]["ins"][i]
                            vals[i] = 1 if b == r else (qv if b == q else 0)
                        hits += evalf(n, g, vals)
                    if hits:
                        gmap[g] = r
            if len(set(gmap.values())) != 2:
                self.unrec.append((qc, "arbiter grants not one per request"))
                continue
            ctl = "vctl:" + qc
            # ctl reads ~A0 through A0 -> state LUT arc + state LUT + q -> grant arc (H_ARB);
            # it may wait arbitrarily long (contention): hi unbounded
            i_a0 = st["ins"].index(a0)
            g0 = gr[0]
            i_q = n.cells[g0]["ins"].index(q)
            lo = n.arcband(qc, i_a0)[0] + n.lutband(qc)[0] + n.arcband(g0, i_q)[0]
            a0src = n.drv.get(a0)
            if a0src not in self.nodes:
                self.unrec.append((qc, "arbiter A0 not a stage output"))
                continue
            self.nodes[ctl] = dict(kind="cel", v=0, F=(1, 1), Q=(0, 0), virtual=True,
                                   pins=[Pin("tap", a0src, [(lo, 10 ** 12)], inv=1)])
            for b, g in enumerate(sorted(gmap, key=lambda g: gr.index(g))):
                r = gmap[g]
                i_r = n.cells[g]["ins"].index(r)
                try:
                    x = self.leaf(r, n.arcband(g, i_r))
                    pr = self.mkpin(x, 0)
                except Unrec as e:
                    self.unrec.append((g, f"arbiter request: {e}"))
                    continue
                pc = Pin("tap", ctl, [(1, 1)], filt=(("arb", qc), (b,)))
                self.nodes["arb:" + g] = dict(kind="cel", v=0, F=n.lutband(g), Q=(0, 0), virtual=True,
                                              pins=[pr, pc], grant=b)
            # R0 = merge of the two grants; tap band = real (r -> R0) minus real (r -> g)
            R = r0[0]
            taps = []
            for g, r in gmap.items():
                i_r = n.cells[R]["ins"].index(r)
                j_r = n.cells[g]["ins"].index(r)
                lo = max(1, n.arcband(R, i_r)[0] - n.arcband(g, j_r)[1] - n.lutband(g)[1])
                hi = max(lo, n.arcband(R, i_r)[1] - n.arcband(g, j_r)[0] - n.lutband(g)[0])
                taps.append(Pin("tap", "arb:" + g, [(lo, hi)]))
            self.nodes["arb:" + R] = dict(kind="merge", v=0, F=n.lutband(R), Q=None, pins=taps,
                                          virtual=True, mutex=True)
            self.arbs[qc] = dict(ctl=ctl, grants=list(gmap), R0=R, A0=a0src)
