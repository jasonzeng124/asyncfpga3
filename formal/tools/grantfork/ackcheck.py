#!/usr/bin/env python3
"""C-10i, consequence of a grant-fork runt (EVIDENCE, not proved): does the runt on
g_k end at ua_k = C(g_k, A0) before A0 can rise there?  (H_RUNT_ACK)

Both sides are measured from q's output edge T (the edge that opened the window).
  late  (runt end at ua_k's g pin) = q -> ugrant q pin + ugrant arc q -> g_k
                                      + g_k -> ua_k g pin            (prjxray, column c)
  early (A0 rise at ua_k's A0 pin) = q -> ustate's O5 q pin + ustate O5 arc (R0)
                                      + SHORTEST SDF path R0 -> ua_k's A0 pin, x 0.772
The server leg is nextpnr's SDF (Dijkstra, every node crossed as a pass-through:
a lower bound on the real response, sound for the side that must be late) under
rule E's GUARD_LO; the arbiter legs are prjxray at the same column c.
    python3 -I ackcheck.py     -> build/ackcheck.tsv
"""
import heapq
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
import importlib.util  # noqa: E402
_spec = importlib.util.spec_from_file_location("grantfork_extract", HERE / "extract.py")
G = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(G)   # this probe's extractor (it imports tcheck's extract as E)
E = G.E


def dijkstra(adj, src, dst):
    """-> (SDF distance, path as node list) or None."""
    dist = {src: 0}
    prev = {}
    pq = [(0, src)]
    while pq:
        d, u = heapq.heappop(pq)
        if u == dst:
            path = [u]
            while path[-1] != src:
                path.append(prev[path[-1]])
            return d, path[::-1]
        if d > dist.get(u, 1e18):
            continue
        for v, w in adj.get(u, ()):
            nd = d + w
            if nd < dist.get(v, 1e18):
                dist[v] = nd
                prev[v] = u
                heapq.heappush(pq, (nd, v))
    return None


def main():
    if len(sys.argv) == 1:      # driver: one design per process (see extract.py --part)
        import subprocess
        allr, worst = [], None
        for label, _o, _t in G.DESIGNS:
            subprocess.run([sys.executable, "-I", __file__, label], check=True)
            allr += (HERE / f"build/ack_{label}.tsv").read_text().splitlines()[1:]
        hdr = (HERE / f"build/ack_{G.DESIGNS[0][0]}.tsv").read_text().splitlines()[0]
        (HERE / "build/ackcheck.tsv").write_text("\n".join([hdr] + allr) + "\n")
        ms = [(float(r.split("\t")[9]), r) for r in allr if "NOT" not in r]
        print("worst prjx-priced margin:", min(ms)[1])
        ms = [(float(r.split("\t")[7]), r) for r in allr if "NOT" not in r]
        print("worst mixed margin:", min(ms)[1])
        return
    only = sys.argv[1]
    sys.argv = [sys.argv[0]]
    T, R, F = E.load_rules(G.CELLS)
    out = ["design\tinst\tclient\tcol\tlate_runt_end\tearly_A0(sdf.772)\tserver_sdf_min\tmargin_mixed"
           "\tearly_A0(prjx path)\tmargin_prjx\tpath arcs/fallback"]
    worst = None
    for label, odir, top in G.DESIGNS:
        if label != only:
            continue
        edges, *_ = T.parse_sdf(odir / f"{top}.sdf")
        P = E.Prjx(R, F, odir / f"{top}.fasm", odir / f"{top}_routed.json")
        cells = P.cells
        arbs = sorted(cn[:-len(".ustate$LUT6")] for cn in cells if cn.endswith(".ustate$LUT6"))
        for a in arbs:
            st6, st5 = a + ".ustate$LUT6", a + ".ustate$LUT5"
            qsrc = f"{st6}/O6"
            for k, gc, o in ((1, a + ".ugrant$LUT5", "O5"), (2, a + ".ugrant$LUT6", "O6")):
                ua = a + f".ua{k}.u"
                gq, sq = G.phys(cells[gc], "I2"), G.phys(cells[st5], "I2")
                ug, ua0 = G.phys(cells[ua], "I0"), G.phys(cells[ua], "I1")
                legs = [P.interconnect(qsrc, f"{gc}/{gq}"), P.iopath(f"{gc}/{gq}", f"{gc}/{o}"),
                        P.interconnect(f"{gc}/{o}", f"{ua}/{ug}")]
                elegs = [P.interconnect(qsrc, f"{st5}/{sq}"), P.iopath(f"{st5}/{sq}", f"{st5}/O5")]
                dj = dijkstra(edges, f"{st5}/O5", f"{ua}/{ua0}")
                if any(x is None for x in legs + elegs) or dj is None:
                    out.append(f"{label}\t{a}\t{k}\t-\tNOT RESOLVED\t\t\t")
                    continue
                srv, path = dj
                w = {(u, v): x for u, l in edges.items() for v, x in l}
                # the SDF-shortest server path priced arc by arc with prjxray (column c);
                # an arc prjxray does not price keeps GUARD_LO x its SDF number
                pr, nfb = [0.0] * 4, 0
                for u, v in zip(path, path[1:]):
                    x = P.iopath(u, v) if u.rsplit("/", 1)[0] == v.rsplit("/", 1)[0] else P.interconnect(u, v)
                    if x is None:
                        x, nfb = [G.GLO * w[(u, v)]] * 4, nfb + 1
                    pr = [p_ + x_ for p_, x_ in zip(pr, x)]
                for col, c in G.COLS.items():
                    late = sum(x[c] for x in legs)
                    early = sum(x[c] for x in elegs) + G.GLO * srv
                    early_p = sum(x[c] for x in elegs) + pr[c]
                    m = early - late
                    out.append(f"{label}\t{a}\t{k}\t{col}\t{late:.0f}\t{early:.0f}\t{srv}\t{m:+.0f}"
                               f"\t{early_p:.0f}\t{early_p - late:+.0f}\t{len(path) - 1}/{nfb}")
                    if worst is None or m < worst[0]:
                        worst = (m, label, a, k, col)
    (HERE / "build").mkdir(exist_ok=True)
    (HERE / f"build/ack_{only}.tsv").write_text("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
