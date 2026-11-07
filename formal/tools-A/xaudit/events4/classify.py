"""classify.py -- recognise the control skeleton of a routed xaudit netlist (UNTRUSTED).

Stage kinds, from the real INIT over the PHYSICAL pins (no cell-name table):
  cel   a LUT with its own output routed back to a pin and a reset pin, whose function is
        rst ? v : C(lit_1 .. lit_n, q), lit_i = pin, ~pin, or (pin & [select bits = pattern])
        (a mux join folds its steer into the C-element LUT)
  arb   a LUT with own feedback + reset that is NOT a C-element (the bd_arbiter state LUT)
Stateless control gates (between stages) are classified by function:
  buf / inv (one live pin), and / or (all live pins control, monotone AND/OR of literals),
  steer (control pin AND a literal of select pins).
Select (data) pins: pins whose net does not reach a control stage through stateless gates.
"""
import itertools
import sys
from netlib import Net


def live_pins(n, cn):
    c = n.cells[cn]
    return [i for i, b in enumerate(c["ins"]) if isinstance(b, int)]


def const_bits(n, cn):
    c = n.cells[cn]
    return {i: int(b) for i, b in enumerate(c["ins"]) if not isinstance(b, int)}


def evalf(n, cn, assign):
    """assign: dict pin->bit for live pins; constants filled in."""
    c = n.cells[cn]
    bits = []
    for i, b in enumerate(c["ins"]):
        bits.append(assign[i] if isinstance(b, int) else int(b))
    return n.f(cn, bits)


def cel_match(n, cn, selpins):
    """Try to read storage LUT cn as a C-element. Returns dict or None."""
    c = n.cells[cn]
    live = live_pins(n, cn)
    rpins = [i for i in live if c["ins"][i] == n.rst]
    qpins = [i for i in live if c["ins"][i] == c["out"]]
    if len(rpins) != 1 or len(qpins) != 1:
        return None
    r, q = rpins[0], qpins[0]
    others = [i for i in live if i not in (r, q)]
    sp = [i for i in others if i in selpins]
    reqs = [i for i in others if i not in selpins]
    if not reqs:
        return None
    allp = live
    rows = []
    for vals in itertools.product([0, 1], repeat=len(allp)):
        a = dict(zip(allp, vals))
        rows.append((a, evalf(n, cn, a)))
    # reset value
    vs = {o for a, o in rows if a[r] == 1}
    if len(vs) != 1:
        return None
    v = vs.pop()
    # candidate roles: polarity per req; if select pins, one filtered req with a pattern
    filt_choices = [None] if not sp else [(fi, pat) for fi in reqs
                                          for pat in itertools.product([0, 1], repeat=len(sp))]
    for pols in itertools.product([0, 1], repeat=len(reqs)):
        for fc in filt_choices:
            ok = True
            for a, o in rows:
                if a[r] == 1:
                    continue
                lits = []
                for ri, pol in zip(reqs, pols):
                    x = a[ri] ^ pol
                    if fc is not None and fc[0] == ri:
                        x = x & int(all(a[s] == b for s, b in zip(sp, fc[1])))
                    lits.append(x)
                if all(lits):
                    e = 1
                elif not any(lits):
                    e = 0
                else:
                    e = a[q]
                if e != o:
                    ok = False
                    break
            if ok:
                return dict(kind="cel", v=v, r=r, q=q, reqs=reqs, pols=list(pols),
                            filt=fc, sel=sp)
    return None


class Skel:
    def __init__(self, n):
        self.n = n
        c = n.cells
        self.storage = {cn for cn, x in c.items() if x["out"] in x["ins"]}
        # first pass: cel with no select pins, arb = remaining storage with reset (not latches)
        self.kind = {}
        for cn in self.storage:
            if n.rst not in c[cn]["ins"]:
                continue  # latch bits (no reset pin) -- data storage
            m = cel_match(n, cn, set())
            self.kind[cn] = m if m else {"kind": "arb?"}
        # control reachability of a net (through stateless gates only)
        self.memo = {}
        # second pass: storage that failed: try with select pins = pins whose net is data
        for cn, m in list(self.kind.items()):
            if m["kind"] == "arb?":
                sel = {i for i in live_pins(n, cn) if c[cn]["ins"][i] not in (n.rst, c[cn]["out"])
                       and not self.ctl_net(c[cn]["ins"][i])}
                m2 = cel_match(n, cn, sel) if sel else None
                self.kind[cn] = m2 if m2 else {"kind": "arb"}
                self.memo = {}

    def ctl_net(self, net, seen=None):
        """True iff `net` reaches a reset-carrying storage LUT through stateless gates."""
        if net in self.memo:
            return self.memo[net]
        if net == self.n.rst or net not in self.n.drv:
            return False
        cn = self.n.drv[net]
        if cn in self.kind:
            self.memo[net] = True
            return True
        if cn in self.storage:
            self.memo[net] = False
            return False
        self.memo[net] = False  # cycle guard (stateless cycles do not exist; be safe)
        r = any(self.ctl_net(b) for b in self.n.cells[cn]["ins"] if isinstance(b, int))
        self.memo[net] = r
        return r

    def expr(self, net, depth=0):
        """Expression of a control net in terms of stage outputs and select nets."""
        n = self.n
        if net == n.rst:
            return ("rst",)
        if net not in n.drv:
            return ("in", n.inputs.get(net, net))
        cn = n.drv[net]
        if cn in self.kind:
            return ("node", cn)
        if not self.ctl_net(net):
            return ("sel", net)
        live = live_pins(n, cn)
        subs = [self.expr(n.cells[cn]["ins"][i], depth + 1) for i in live]
        return ("gate", cn, tuple(live), tuple(subs))


def gate_fn(n, cn, live):
    """Truth table of a stateless gate over its live pins, as a tuple."""
    out = []
    for vals in itertools.product([0, 1], repeat=len(live)):
        out.append(evalf(n, cn, dict(zip(live, vals))))
    return tuple(out)


if __name__ == "__main__":
    n = Net(sys.argv[1])
    s = Skel(n)
    import collections
    kc = collections.Counter(m["kind"] for m in s.kind.values())
    print("storage with reset:", kc)
    for cn, m in sorted(s.kind.items()):
        if m["kind"] != "cel" or m.get("sel"):
            print(" ", m["kind"], cn, {k: v for k, v in m.items() if k != "kind"})
