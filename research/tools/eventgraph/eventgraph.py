#!/usr/bin/env python3
"""eventgraph.py WORK MARKER [--out DIR] -- the timed event graph of one full-stack run (PROGRAM.md FIRST item, step 1).

WORK: a fullstack_dump.sh run dir (netlist_baked.v, nets.map, dump.vcd).  MARKER: a net (e.g. n8_u_req, in nets.map
names; or an n* net) whose rises mark iterations.

The fid model makes every primitive a TRANSPORT delay per (input pin, output) arc (trace.py).  So for an output edge
at t, each input pin p sees its source net's edges shifted by D(wire) + arc(p); its delayed value at t is known.
1. Steady state: the longest run of marker intervals all equal to the mode P; a window of K iterations in its middle.
   A net is PERIODIC if its edges in every iteration of the window are the same (offset, value) list; each such
   edge is one NODE (net, phase j).  Nets whose edges differ from iteration to iteration (data; anything clocked by
   the harness clock) are APERIODIC: not nodes.
2. Arcs: for each node's edge in a reference iteration and each input pin of its driver whose source has an edge
   before (t - D - arc): the pin is ENABLING if putting it back to its value before that edge (all other pins at
   their delayed values at t) would leave the output at its old value (LUT INIT / F7-F8 / latch function).  Each
   enabling pin from a periodic net is an arc (w = D + arc, offset = iterations between the two edges, slack =
   t - t_src - w >= 0).  An edge with no single enabling pin (OR-causality) gets one arc, from the binding cause
   (trace.py's cause(), slack 0), marked 'or'; so does an edge of a cell the tool cannot evaluate (CARRY4, FF).
   Enabling pins from aperiodic nets are not arcs; their slack is reported (one at 0 slack is an error).
3. The period of the graph is its maximum cycle ratio, computed by running the max-plus recursion
   T[v,k] = max_arcs(T[u,k-o] + w) for many iterations; the critical cycle is read back by argmax.
   Check: it must equal P to the ps and the cycle must be trace.py's (the marker back-walk), hop for hop.
Writes DIR/nodes.tsv, DIR/arcs.tsv, DIR/check.txt.  The graph files are what whatif.py edits (no VCD needed).
"""
import sys, os, collections, bisect, re
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../itercost"))
from trace import Net, load_vcd, Trace, OUTS  # noqa: E402
import maxplus  # noqa: E402

PRIMS = os.path.join(HERE, "../../../cells/gls/prims.v")
LUTPINS = ("A1", "A2", "A3", "A4", "A5", "A6")


def const_val(x):
    m = re.match(r"\d*'[bB]([01])$", x.strip())
    return m.group(1) if m else None


def evaluate(typ, pd, port, v):
    """v: pin -> '0'/'1'.  Returns '0'/'1' or None (cannot evaluate)."""
    if any(x not in "01" for x in v.values()):
        return None
    if typ == "SLICE_LUTX":
        init = int(re.sub(r"^\d*'[hH]", "", pd.get("INIT", "0")).replace("_", ""), 16) if "'" in pd.get("INIT", "0") \
            else int(pd.get("INIT", "0"))
        pins = LUTPINS if port == "O6" else LUTPINS[:5]
        idx = sum((1 << i) for i, p in enumerate(pins) if v.get(p, "0") == "1")
        return str((init >> idx) & 1)
    if typ == "SELMUX2_1":
        return v.get("D1") if v.get("S0") == "1" else v.get("D0")
    return None


class Graph:
    def __init__(self):
        self.nodes, self.arcs = [], []        # nodes: dict(net, name, phase, edge, t); arcs: dict(u, v, w, o, ...)


def build(work, marker, K=10):
    N = Net(work, PRIMS)
    ev = load_vcd(work + "/dump.vcd")
    T = Trace(N, ev)
    mk = marker if marker in ev else N.inv.get(marker)
    if mk not in ev:
        mk = next((k for k, v in N.name.items() if v.endswith("." + marker) or v == marker), None)
    if mk not in ev:
        sys.exit("marker %s not found" % marker)
    rises = [t for t, c in ev[mk] if c == "1"]
    iv = [b - a for a, b in zip(rises, rises[1:])]
    P = collections.Counter(iv).most_common(1)[0][0]
    # longest run of intervals == P
    best, cur, start = (0, 0), 0, 0
    for i, d in enumerate(iv):
        if d == P:
            if cur == 0: start = i
            cur += 1
            if cur > best[0]: best = (cur, start)
        else:
            cur = 0
    run, s0 = best
    if run < K + 6:
        sys.exit("steady state too short: %d intervals of %d ps" % (run, P))
    i0 = s0 + run // 2 - K // 2
    t0 = rises[i0]
    lo, hi = t0 - 2 * P, t0 + K * P
    # ---- periodic nets -> nodes ----------------------------------------------------------------------------------
    node_of = {}                     # (net, phase_ps, val) -> node index
    G = Graph(); aper = set()
    for n, e in ev.items():
        times = T.times[n]
        a, b = bisect.bisect_left(times, lo), bisect.bisect_left(times, hi)
        if a == b:
            continue
        per = collections.defaultdict(list)
        for t, c in e[a:b]:
            k = (t - t0) // P
            per[k].append((t - t0 - k * P, c))
        sig = [tuple(per.get(k, ())) for k in range(-2, K)]
        if all(s == sig[0] for s in sig) and sig[0]:
            for j, (ph, c) in enumerate(sig[0]):
                node_of[(n, ph)] = len(G.nodes)
                G.nodes.append(dict(net=n, name=N.name.get(n, n), phase=ph, edge="R" if c == "1" else "F" if c == "0"
                                    else c, j=j))
        else:
            aper.add(n)

    def node_iter(n, t):
        k = (t - t0) // P
        ph = t - t0 - k * P
        return node_of.get((n, ph)), k

    # ---- arcs ------------------------------------------------------------------------------------------------------
    kref = K // 2
    stats = collections.Counter(); datadep = []
    for vi, nd in enumerate(G.nodes):
        n = nd["net"]; t = t0 + kref * P + nd["phase"]
        newv = {"R": "1", "F": "0"}.get(nd["edge"], nd["edge"])
        if n not in N.drv:
            stats["no_driver"] += 1; continue
        cell, port = N.drv[n]; typ, pd, cd = N.cells[cell]
        pins = {}
        for p, x in cd.items():
            if p in OUTS.get(typ, ()): continue
            src, D = N.icbuf[x] if x.startswith("w") else (x, 0)
            a = N.arc(typ, pd, p, port)
            if not src.startswith("n"):
                cv = const_val(src)
                pins[p] = dict(src=None, D=D, a=a, cur=cv or "0", te=None, prev=None)
                continue
            tt = T.times.get(src, [])
            i = bisect.bisect_right(tt, t - D - a)
            cur = T.ev[src][i - 1][1] if i else None
            prev = T.ev[src][i - 2][1] if i >= 2 else None
            pins[p] = dict(src=src, D=D, a=a, cur=cur, te=tt[i - 1] if i else None, prev=prev)
        if typ == "SLICE_LUTX":
            use = LUTPINS if port == "O6" else LUTPINS[:5]
            pins = {p: d for p, d in pins.items() if p in use}
        v = {p: d["cur"] for p, d in pins.items()}
        out = evaluate(typ, pd, port, v)
        enab = []
        if out is not None and out == newv:
            for p, d in pins.items():
                if d["te"] is None or d["prev"] is None: continue
                v2 = dict(v); v2[p] = d["prev"]
                o2 = evaluate(typ, pd, port, v2)
                if o2 is not None and o2 != newv:
                    enab.append(p)
            kind = "and" if enab else "or"
        else:
            kind = "bind" if out is None else "mismatch"
            stats["eval_" + kind] += 1
        if not enab:
            c = T.cause(n, t)
            if c is None:
                stats["no_cause"] += 1; continue
            enab = [c["pin"]]
        stats[kind] += 1
        for p in enab:
            d = pins[p]
            w = d["D"] + d["a"]; slack = t - d["te"] - w
            u, ku = node_iter(d["src"], d["te"])
            if u is None:
                datadep.append((nd["name"], p, N.name.get(d["src"], d["src"]), slack))
                if slack == 0:
                    stats["binding_from_aperiodic"] += 1
                continue
            G.arcs.append(dict(u=u, v=vi, w=w, o=kref - ku, slack=slack, kind=kind, pin=p, cell=cell, typ=typ,
                               wire=d["D"], arc=d["a"]))
    return G, P, t0, mk, N, T, stats, datadep, aper


def trace_cycle(T, mk, t_rise):
    """trace.py's walk: from the marker rise back to its previous rise (the itercost critical cycle)."""
    hops, end = T.chain(mk, t_rise, lambda n, t: n == mk and t < t_rise and T.val_at(n, t) == "1")
    return hops, end


def main():
    a = [x for x in sys.argv[1:] if not x.startswith("--")]
    W, MK = a[:2]
    OUT = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else W + "/eventgraph"
    os.makedirs(OUT, exist_ok=True)
    G, P, t0, mk, N, T, stats, datadep, aper = build(W, MK)
    # ---- write the graph -------------------------------------------------------------------------------------------
    with open(OUT + "/nodes.tsv", "w") as f:
        f.write("id\tnet\tname\tedge\tphase_ps\n")
        for i, nd in enumerate(G.nodes):
            f.write("%d\t%s\t%s\t%s\t%d\n" % (i, nd["net"], nd["name"], nd["edge"], nd["phase"]))
    with open(OUT + "/arcs.tsv", "w") as f:
        f.write("u\tv\tw_ps\toffset\tslack_ps\tkind\tpin\tcell\ttyp\twire_ps\tarc_ps\n")
        for e in G.arcs:
            f.write("%d\t%d\t%d\t%d\t%d\t%s\t%s\t%s\t%s\t%d\t%d\n" % (e["u"], e["v"], e["w"], e["o"], e["slack"], e["kind"],
                    e["pin"], e["cell"], e["typ"], e["wire"], e["arc"]))
    # ---- the graph's period and critical cycle -------------------------------------------------------------------
    mnode = next(i for i, nd in enumerate(G.nodes) if nd["net"] == mk and nd["edge"] == "R")
    lam, cyc = maxplus.mcr(len(G.nodes), G.arcs, mnode)
    neg = sum(1 for e in G.arcs if e["slack"] < 0)
    # trace.py's walk, from an edge of the graph's critical cycle back to that net's previous same edge
    cn = G.nodes[G.arcs[cyc[0]]["v"]]
    ce = "1" if cn["edge"] == "R" else "0"
    tr = t0 + (10 // 2) * P + cn["phase"]
    hops, end = T.chain(cn["net"], tr, lambda n, t: n == cn["net"] and t < tr and T.val_at(n, t) == ce)
    tcyc = [(h["out"], h["edge"]) for h in hops]
    gcyc = [(G.nodes[G.arcs[i]["v"]]["net"], "1" if G.nodes[G.arcs[i]["v"]]["edge"] == "R" else "0") for i in cyc]
    same = sorted(tcyc) == sorted(gcyc) and len(tcyc) == len(gcyc)
    ref = None
    if "--ref" in sys.argv:          # the committed itercost cycle (cycle_hops.tsv: edge and net per hop)
        rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[sys.argv.index("--ref") + 1])][1:]
        rc = sorted((r[-1], "1" if r[5] == "R" else "0") for r in rows)
        gn = sorted((N.name.get(n, n), e) for n, e in gcyc)
        ref = (rc == gn, len(rc))
    wsum = sum(G.arcs[i]["w"] for i in cyc); osum = sum(G.arcs[i]["o"] for i in cyc)
    lines = [
        "work %s marker %s (%s) period P = %d ps; window t0 = %d" % (W, MK, mk, P, t0),
        "nodes %d (periodic net edges), aperiodic nets %d, arcs %d (negative slack: %d)" % (len(G.nodes), len(aper),
                                                                                       len(G.arcs), neg),
        "edge kinds: %s" % dict(stats),
        "enabling pins from aperiodic nets: %d, min slack %s" % (len(datadep), min((d[3] for d in datadep), default="-")),
        "graph period (max cycle ratio): %.3f ps; critical cycle %d arcs, weight %d ps, tokens %d" % (lam, len(cyc), wsum,
                                                                                                      osum),
        "trace.py cycle: %d hops, ends %s" % (len(hops), end[0]),
        "CHECK period equal: %s; cycle equal to trace.py's (same %d edges): %s" % (
            "PASS" if abs(lam - P) < 1e-6 and wsum == P * osum else "FAIL", len(gcyc), "PASS" if same else "FAIL"),
    ]
    if ref is not None:
        lines.append("CHECK cycle equal to the committed itercost cycle (%d hops): %s" % (ref[1], "PASS" if ref[0] else "FAIL"))
    if not same:
        st, sg = set(tcyc), set(gcyc)
        lines.append("  in trace only: %s" % [N.name.get(n, n) + e for n, e in st - sg][:12])
        lines.append("  in graph only: %s" % [N.name.get(n, n) + e for n, e in sg - st][:12])
    open(OUT + "/check.txt", "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
