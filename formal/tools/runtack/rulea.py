#!/usr/bin/env python3
"""C-10j item 4: does tighten.py's rule A walk for a bdc_amerge cell start at q, and
what does it measure there?  Re-runs rule A's own pairing (cells/verify/tighten.py,
imported read-only, same false-arc pruning, same peers, same confinement) for every
amerge cell of the gcd_hw routes, and reports, per cell:
  * whether ustate's q (O6) is in rule A's source set (cell_boundary),
  * the from-q pairing: early(q -> z_req tail) - late(q -> every g2 reader output) - guard
    (nextpnr SDF numbers, rule A's req_guard), i.e. the rule-A form of H_RUNT_IDX,
  * the worst pairing over all sources (what tighten prints), and its source.
    python3 -I rulea.py      -> build/rulea.tsv
"""
import importlib.util
import pathlib
import sys
from collections import defaultdict

HERE = pathlib.Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("grantfork_extract", HERE.parent / "grantfork/extract.py")
G = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(G)
E = G.E


def main():
    sys.argv = [sys.argv[0]]
    T, _R, _F = E.load_rules(G.CELLS)
    out = ["design\tcell\tq_in_srcs\tfromq_margin\tfromq_req\tfromq_late\tfromq_guard\tfromq_pin"
           "\tworst_margin\tworst_src\tworst_pin"]
    for label, odir, top in G.DESIGNS:
        if not label.startswith("gcd"):
            continue
        sdf = odir / f"{top}.sdf"
        edges, *_ = T.parse_sdf(sdf)
        dead, _j = T.false_arcs(edges, sdf)
        for src in list(edges):
            edges[src] = [(d, w) for d, w in edges[src] if (src, d) not in dead]
        back = defaultdict(set)
        for src, lst in edges.items():
            for dst, _ in lst:
                back[dst].add(src)
        stops = T.storage_nodes(edges)
        timing = T.Timing(edges, stops)
        chains = T.find_chains(edges)
        for parent, head, tail, links in T.request_sites(edges, back, chains):
            q = f"{parent}.uarb1.ustate$LUT6/O6"
            if q not in edges:
                continue                       # not an amerge
            downstream = T.reaches(edges, tail, stops)
            upstream = {p for p in edges if T.is_output(p) and head in T.reaches(edges, p, stops)}
            own = set(links)
            peers = sorted({p for p in edges if T.is_output(p)
                            and T.pin_split(p)[0].startswith(parent + ".")
                            and T.pin_split(p)[0] not in own
                            and p not in downstream and p not in upstream})
            parent_srcs = T.cell_boundary(edges, back, stops, parent)
            ups = T.upstream_bd_links(parent_srcs)
            region = (parent,) + ups
            srcs = T.cell_boundary(edges, back, stops, region)
            confine = region if ups else parent
            worst = T.check(timing, srcs, peers, tail, T.req_guard, confine=confine)
            # g2 readers among the peers (every LUT output inside the cell fed by a g2 net)
            g2s = [f"{parent}.uarb{k}.ugrant$LUT6/O6" for k in (1, 2, 3)]
            rd = sorted({p for g in g2s for d, _ in edges.get(g, ())
                         for p in edges if T.pin_split(p)[0] == T.pin_split(d)[0] and T.is_output(p)} & set(peers))
            for qq in [f"{parent}.uarb{k}.ustate$LUT6/O6" for k in (1, 2, 3)]:
                if qq not in edges:
                    continue
                fq = T.check(timing, [qq], rd, tail, T.req_guard, confine=confine) if rd else None
                cell = qq.rsplit(".ustate", 1)[0]
                if fq is None:
                    out.append(f"{label}\t{cell}\t{qq in srcs}\t-\t\t\t\t\t{worst[0]}\t{worst[5]}\t{worst[4]}")
                else:
                    m, g, te, tl, pin, _s = fq
                    out.append(f"{label}\t{cell}\t{qq in srcs}\t{m}\t{te}\t{tl}\t{g}\t{pin}"
                               f"\t{worst[0]}\t{worst[5]}\t{worst[4]}")
    (HERE / "build").mkdir(exist_ok=True)
    (HERE / "build/rulea.tsv").write_text("\n".join(out) + "\n")
    print("\n".join(out))


if __name__ == "__main__":
    main()
