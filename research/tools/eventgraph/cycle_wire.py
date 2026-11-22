#!/usr/bin/env python3
"""cycle_wire.py GRAPHDIR [GRAPHDIR ...] [--hops] -- the routed wire share of a timed event graph's critical cycle.

Reads eventgraph.py's nodes.tsv / arcs.tsv (each arc: w_ps = wire_ps + arc_ps, the interconnect into the pin and the
cell arc), finds the critical cycle again (maxplus.mcr over the whole graph, as whatif.py's G.period()), and splits
its weight into cell arcs and wire, the wire by hop kind:
  chain   both ends are links of one matched delay (`.chain.g[i]`, same kernel instance): the delay's own wiring
  intra   both ends in one kernel instance otherwise (C node -> its own chain, a join inside a mux, ...)
  inter   the ends are in different kernel instances: the handshake hops between units, which a placement
          constraint on the ring is meant to shorten
One line per graph:  NAME P_ps arcs wire_ps cell_ps wire% chain/intra/inter wire_ps (n hops each).
--hops also lists the cycle's arcs.  The cycle found here is checked against check.txt's period (same weight / tokens).
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import maxplus  # noqa: E402

CHAIN = re.compile(r"\.chain\.g\[\d+\]")


def inst_of(cell):
    if not cell.startswith("bridge_i.udut."):
        return cell
    return cell[len("bridge_i.udut."):].split(".")[0].split("$")[0]


def load(d):
    rows = [l.rstrip("\n").split("\t") for l in open(os.path.join(d, "nodes.tsv"))]
    nodes = [dict(zip(rows[0], r)) for r in rows[1:]]
    rows = [l.rstrip("\n").split("\t") for l in open(os.path.join(d, "arcs.tsv"))]
    arcs = []
    for r in rows[1:]:
        a = dict(zip(rows[0], r))
        arcs.append(dict(u=int(a["u"]), v=int(a["v"]), w=int(a["w_ps"]), o=int(a["offset"]),
                         wire=int(a["wire_ps"]), arc=int(a["arc_ps"])))
    ck = os.path.join(d, "check.txt")
    m = re.search(r"period P = (\d+)", open(ck).read()) if os.path.exists(ck) else None
    return nodes, arcs, int(m.group(1)) if m else None


def analyse(d):
    nodes, arcs, P = load(d)
    lam, cyc = maxplus.mcr(len(nodes), arcs)
    if not cyc:
        return None
    tok = sum(arcs[i]["o"] for i in cyc)
    out = dict(P=P, lam=lam, n=len(cyc), tokens=tok, wire=0, cell=0,
               kind={"chain": [0, 0], "intra": [0, 0], "inter": [0, 0]}, hops=[])
    for i in cyc:
        a = arcs[i]
        cu, cv = nodes[a["u"]]["cell"], nodes[a["v"]]["cell"]
        iu, iv = inst_of(cu), inst_of(cv)
        k = "inter" if iu != iv else ("chain" if CHAIN.search(cu) and CHAIN.search(cv) else "intra")
        out["wire"] += a["wire"]; out["cell"] += a["arc"]
        out["kind"][k][0] += a["wire"]; out["kind"][k][1] += 1
        out["hops"].append((k, a["wire"], a["arc"], nodes[a["u"]]["name"] + nodes[a["u"]]["edge"],
                            nodes[a["v"]]["name"] + nodes[a["v"]]["edge"], iu, iv))
    return out


def main():
    av = sys.argv[1:]
    hops = "--hops" in av
    for d in [x for x in av if not x.startswith("--")]:
        name = os.path.basename(os.path.normpath(d))
        if not os.path.exists(os.path.join(d, "arcs.tsv")):
            print(f"{name} NO-GRAPH")
            continue
        r = analyse(d)
        name = os.path.basename(os.path.normpath(d))
        if r is None:
            print(f"{name} NO-CYCLE")
            continue
        per = r["lam"] * r["tokens"]
        ok = "" if r["P"] is None or abs(per - r["P"] * r["tokens"]) < 1 else f" (CHECK: cycle {per:.0f} != P {r['P']})"
        k = r["kind"]
        print(f"{name} P={r['P']} arcs={r['n']} wire={r['wire']} cell={r['cell']} "
              f"wire%={100.0 * r['wire'] / (r['wire'] + r['cell']):.1f} "
              f"chain={k['chain'][0]}({k['chain'][1]}) intra={k['intra'][0]}({k['intra'][1]}) "
              f"inter={k['inter'][0]}({k['inter'][1]}){ok}")
        if hops:
            for h in r["hops"]:
                print("   %-5s wire %5d cell %4d  %s -> %s" % h[:5])


if __name__ == "__main__":
    main()
