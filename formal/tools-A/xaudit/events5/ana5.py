"""ana5.py -- events4's analysis with STRICT margins and a corrected delay-line contiguity check
(UNTRUSTED).

    python3 ana5.py NET.json BANDS.json [--label L] [--json OUT.json]

Differences from events4/ana.py (which it imports unchanged):

1. STRICT margins.  A margin of exactly 0 is a FAIL (Back, guard ENTRY/EXIT, contiguity), to
   agree with the strict race convention of the parallel probe (A-contradictions).

2. Delay-line contiguity, corrected ("contig5").  events4/model.py gives every tap of a FASTFALL /
   FASTRISE line its WHOLE path band, source -> ... -> stage pin, and takes the pair window
   max(hi) - min(lo) between consecutive taps.  Two taps of one line share the chain suffix
   (from the gate where they meet to the stage pin) and the prefix (source -> fanout point).
   In the warp model a shared element has ONE warp, so it cancels from the difference of the
   two sample times; the events4 window instead counts the shared part's full band width,
   which grows with the line's length (26 taps x ~560 ps of fast-min/slow-max width ~ 14.5 ns).
   contig5 walks the gate tree of each line pin and, at every AND/OR gate of the line, takes the
   two inputs' tap paths as SETS OF ELEMENTS (routed arcs keyed cell/I<k>, LUTs keyed by cell);
   the window of a pair of taps (P, Q) is over the symmetric difference only:
       win(P, Q) = max(hi(P\\Q) - lo(Q\\P), hi(Q\\P) - lo(P\\Q)),
   and the gate is certified if some pair (one tap from each input subtree, a bottleneck
   spanning tree for gates with more than 2 inputs) has win < W(src) (strict).  Soundness of
   this per-gate certificate: Events5.line_contig / Events5.hop_window (Lean), contig_union.
   The gate's own LUT is shared by both inputs (one warp per LUT in the Events model), so it
   cancels; a per-pin IOPATH difference is a fidelity item (A-events5 notes), reported by
   --lutpin as the conservative variant that adds the gate LUT's full band width.
"""
import argparse
import collections
import itertools
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "events4"))
from model import Model  # noqa: E402
from ana import Ana  # noqa: E402
from classify import live_pins, gate_fn  # noqa: E402


class Contig5:
    def __init__(self, A, lutpin=False, fixed=False):
        self.A, self.M, self.n, self.s = A, A.M, A.M.n, A.M.s
        self.fixed = fixed
        self.lutpin = lutpin
        self.memo = {}

    def band(self, e):
        if e[0] == "arc":
            return self.n.arcband(e[1], e[2])
        return self.n.lutband(e[1])

    def root(self, net):
        """Model source name of a net that is NOT a line gate output, or None."""
        n, s, M = self.n, self.s, self.M
        cn = n.drv.get(net)
        if cn is None:
            return None
        if cn in s.kind:
            return cn
        if cn in M.arbout:
            return "arb:" + cn
        if "merge:" + cn in M.nodes:
            return "merge:" + cn
        return None

    def taps(self, net):
        """All tap paths of `net` back to its single source: (src, [frozenset(elements)]).
        Element sets run from the source's output to `net` (the driver LUT included)."""
        if net in self.memo:
            return self.memo[net]
        r = self.root(net)
        if r is not None:
            res = (r, [frozenset()])
        else:
            n = self.n
            cn = n.drv[net]
            c = n.cells[cn]
            srcs, paths = set(), []
            for i in live_pins(n, cn):
                sub = self.taps(c["ins"][i])
                if sub is None:
                    res = None
                    break
                srcs.add(sub[0])
                for p in sub[1]:
                    paths.append(p | {("arc", cn, i), ("lut", cn)})
            else:
                res = (srcs.pop(), paths) if len(srcs) == 1 else None
        self.memo[net] = res
        return res

    def win(self, P, Q):
        """Window of two tap paths to one gate's input pins (Events5Line.hop_skew), plus the
        band width of their SHARED prefix (prefix_skew: a shared element does not cancel in
        the warp model; it would with fixed delays, --fixed)."""
        a, b = P - Q, Q - P
        lo = lambda S: sum(self.band(e)[0] for e in S)
        hi = lambda S: sum(self.band(e)[1] for e in S)
        w = max(hi(a) - lo(b), hi(b) - lo(a))
        if not self.fixed:
            sh = P & Q
            w += hi(sh) - lo(sh)
        return w

    def gates(self, net, out):
        """Collect every multi-input line gate in the tree of `net`."""
        r = self.root(net)
        if r is not None:
            return
        n = self.n
        cn = n.drv[net]
        lv = live_pins(n, cn)
        if len(lv) >= 2:
            out.append(cn)
        for i in lv:
            self.gates(n.cells[cn]["ins"][i], out)

    def check_gate(self, cn, W):
        n = self.n
        c = n.cells[cn]
        lv = live_pins(n, cn)
        subs = [[p | {("arc", cn, i)} for p in self.taps(c["ins"][i])[1]] for i in lv]
        # bottleneck spanning tree over the inputs: edge (a, b) = best pair window
        k = len(subs)
        edge = {}
        for a, b in itertools.combinations(range(k), 2):
            best = None
            for P in subs[a]:
                for Q in subs[b]:
                    w = self.win(P, Q)
                    if best is None or w < best:
                        best = w
            edge[(a, b)] = best
        # Prim on bottleneck
        inT, worst = {0}, 0
        while len(inT) < k:
            e = min(((w, a, b) for (a, b), w in edge.items() if (a in inT) != (b in inT)))
            worst = max(worst, e[0])
            inT |= {e[1], e[2]}
        if self.lutpin:
            lb = n.lutband(cn)
            worst += lb[1] - lb[0]
        return worst

    def pin(self, j, k, net, src):
        if isinstance(net, tuple):
            g = net[1]
            cands = [self.n.cells[g]["ins"][i] for i in live_pins(self.n, g)]
            cands = [x for x in cands if self.taps(x) is not None and self.taps(x)[0] == src
                     and len(self.taps(x)[1]) > 1]
            if len(cands) != 1:
                return dict(stage=j, pin=k, src=src, err="arbiter request line not found")
            net = cands[0]
        W = self.A.W(src)
        t = self.taps(net)
        if t is None:
            return dict(stage=j, pin=k, src=src, err="taps not single-source")
        gs = []
        self.gates(net, gs)
        ws = [(self.check_gate(g, W), g) for g in gs]
        worst = max(ws) if ws else (0, None)
        return dict(stage=j, pin=k, src=src, ntaps=len(t[1]), gates=len(gs), W=W,
                    window=worst[0], at=worst[1],
                    margin=(W - worst[0]) if W is not None else None)


def stage_net(M, j, k):
    """Net read by pin k of model node j (a cel stage or a merge)."""
    n = M.n
    if j.startswith("merge:"):
        cn = j[len("merge:"):]
        return n.cells[cn]["ins"][live_pins(n, cn)[k]]
    if j.startswith("arb:"):
        # virtual grant node: pin 0 is the grant LUT's own request input (the one that is a
        # line of the model's source); found by trying the grant LUT's live inputs
        return ("arbreq", j[len("arb:"):])
    m = M.s.kind[j]
    return n.cells[j]["ins"][m["reqs"][k]]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("net")
    ap.add_argument("bands")
    ap.add_argument("--label", default="")
    ap.add_argument("--json")
    ap.add_argument("--lutpin", action="store_true")
    ap.add_argument("--fixed", action="store_true", help="fixed delays: shared prefix cancels")
    a = ap.parse_args()
    M = Model(a.net, a.bands)
    A = Ana(M)
    r = A.run()
    r["unrec"] = M.unrec
    C = Contig5(A, a.lutpin, a.fixed)
    r["contig5"] = [C.pin(m["stage"], m["pin"], stage_net(M, m["stage"], m["pin"]), m["src"])
                    for m in r["multis"]]
    if a.json:
        json.dump(r, open(a.json, "w"), indent=1, default=str)
    st = r["stages"]
    real = [e for e in st if not e["virtual"]]
    stg = {e["stage"] for e in real}
    bad = collections.defaultdict(set)
    for e in real:
        if e["rule"] == "Back" and e["margin"] <= 0:
            bad[e["stage"]].add("Back")
        if e["rule"] == "Guard" and (e["entry"] is None or e["entry"] <= 0):
            bad[e["stage"]].add("GuardEntry")
        if e["rule"] == "Guard" and (e["exit"] is None or e["exit"] <= 0):
            bad[e["stage"]].add("GuardExit")
        if e["rule"] == "NONE":
            bad[e["stage"]].add("NONE")
    for m in r["multis"]:
        if m["stage"] in stg and (m["margin"] is None or m["margin"] <= 0):
            bad[m["stage"]].add("Contig4")
    for m in r["contig5"]:
        if m["stage"] in stg and (m.get("margin") is None or m["margin"] <= 0):
            bad[m["stage"]].add("Contig5")
    lab = a.label
    backs = [e for e in real if e["rule"] == "Back"]
    gs = [e for e in real if e["rule"] == "Guard"]
    c4 = [m["margin"] for m in r["multis"] if m["margin"] is not None]
    c5 = [m["margin"] for m in r["contig5"] if m.get("margin") is not None]
    mg = r["merges"]
    print(f"[{lab}] stages {len(stg)}, pins {len(real)}")
    print(f"  Back pins {len(backs)}: min {min(e['margin'] for e in backs)}; <=0: {sum(e['margin'] <= 0 for e in backs)}")
    for e in sorted(backs, key=lambda e: e["margin"]):
        if e["margin"] <= 0:
            print(f"    Back {e['margin']:6d}  {e['stage']} pin{e['pin']} <- {e['src']} (lo {e['lo']} d {e['d']} hiQ {e['hiQ']})")
    ent = [e["entry"] for e in gs if e["entry"] is not None]
    ext = [e["exit"] for e in gs if e["exit"] is not None]
    print(f"  Guard pins {len(gs)}: min entry {min(ent)}, min exit {min(ext) if ext else None}; "
          f"entry<=0 {sum(x <= 0 for x in ent)}, exit<=0 {sum(x <= 0 for x in ext)}, "
          f"no exit bound {sum(e['exit'] is None for e in gs)}")
    for e in gs:
        if (e["entry"] is None or e["entry"] <= 0 or e["exit"] is None or e["exit"] <= 0):
            print(f"    Guard entry {e['entry']} exit {e['exit']} W {e['W']}  {e['stage']} <- {e['src']}")
    print(f"  NONE {sum(e['rule'] == 'NONE' for e in real)}: " +
          ", ".join(f"{e['stage']} pin{e['pin']}" for e in real if e["rule"] == "NONE"))
    print(f"  merges {len(mg)}: certified {sum(m['ok'] for m in mg)}; not: {[m['merge'] for m in mg if not m['ok']]}")
    print(f"  delay-line pins {len(r['multis'])}")
    print(f"    events4 window (shared path counted): min margin {min(c4)}, fail(<=0) {sum(x <= 0 for x in c4)}")
    print(f"    contig5 (shared path cancelled{', +gate LUT width' if a.lutpin else ''}): min margin {min(c5)}, "
          f"median {sorted(c5)[len(c5)//2]}, fail(<=0) {sum(x <= 0 for x in c5)}")
    for m in sorted(r["contig5"], key=lambda m: m.get("margin") if m.get("margin") is not None else -10**9)[:5]:
        print(f"      {m.get('margin')}  {m['stage']} pin{m['pin']} <- {m['src']} taps {m.get('ntaps')} "
              f"window {m.get('window')} at {m.get('at')} W {m.get('W')}")
    Ws = sorted(w for w in r["W"].values() if w is not None)
    print(f"  W: min {Ws[0]}, median {Ws[len(Ws)//2]}")
    fam = collections.Counter()
    for s_ in bad.values():
        for k in s_:
            fam[k] += 1
    clean4 = len(stg) - sum(1 for s_ in bad.values() if s_ - {"Contig5"})
    clean5 = len(stg) - sum(1 for s_ in bad.values() if s_ - {"Contig4"})
    print(f"  stages clean: {clean5}/{len(stg)} (contig5), {clean4}/{len(stg)} (events4 contiguity); "
          f"failing stages by rule: {dict(fam)}")
    print(f"VERDICT [{lab}] (strict, contig5): " + ("ALL CONDITIONS MET" if clean5 == len(stg) and all(m['ok'] for m in mg)
                                                  else f"NOT MET ({len(stg) - clean5} stages)"))


if __name__ == "__main__":
    main()
