"""gen.py -- emit the ARBITER DATA that xarbnet (Events9ArbNetMain.lean) checks (UNTRUSTED).

    python3 gen.py SKEL.json BANDS.json CERT.json OUT.json

Probe E9ArbNet.  For every arbiter of the corrected core (events4/model.py build_arb_fix, mode fix)
it names, by gate and node NAME (the Lean side resolves and checks everything):
  * the six virtual nodes of the certificate CERT.json (cert9p.py output): vctl, arb:g_b (b = the
    grant's label value, 0 first), vsh:R0/b, arb:R0, and the real node driving A0;
  * the four LUT gates of bd_arbiter's core in the parsed design: ugrant O5/O6 (the grant cells,
    g_0 first), ustate O5 (R0), ustate O6 (q) -- as "<cell>/O";
  * per read the LUT input index and the route path below it ([["<cell>/I<i>", 0]]);
  * per request: the route buffer of grant b's request pin (its input wire is the request net)
    and the tree / steer below that net down to the request's source node (cert6.Cert.below).
Nothing here is trusted: Events9ArbNet.ArbOK re-derives every function from the INITs and every
band from the band file.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "events4"))
sys.path.insert(0, os.path.join(HERE, "..", "events6"))
os.environ.setdefault("XA_ARB", "fix")
from cert6 import Cert  # noqa: E402
from classify import live_pins  # noqa: E402
from model import evalf  # noqa: E402


def rpin(below):
    src, par, op, paths = below
    st = [p for p in paths if any(e[0] == "STEER" for e in p)]
    d = dict(src=src, inv=bool(par), op=True if op is None else op)
    if st:
        p = st[0]
        i = [k for k, e in enumerate(p) if e[0] == "STEER"][0]
        m = p[i]
        d.update(st=True, top=p[:i], sg=m[1], sci=m[2], ssel=m[3], bot=p[i + 1:], paths=[])
    else:
        d.update(st=False, paths=paths, top=[], bot=[], sg="", sci=0, ssel=[])
    return d


def sp_lo(n, src, dst):
    """Least lower delay (ps) of any LUT path from net src to net dst (arc lo + LUT lo per hop):
    an UNTRUSTED lower bound for an edge of dst caused by an edge of src (rows B2a / C-lo)."""
    import heapq
    dist = {src: 0}
    h = [(0, src)]
    while h:
        du, u = heapq.heappop(h)
        if u == dst:
            return du
        if du > dist.get(u, 1 << 60):
            continue
        for (cn, i) in n.readers.get(u, []):
            c = n.cells[cn]
            v = c["out"]
            dv = du + max(1, n.arcband(cn, i)[0]) + max(1, n.lutband(cn)[0])
            if dv < dist.get(v, 1 << 60):
                dist[v] = dv
                heapq.heappush(h, (dv, v))
    return None


def main():
    skel, bands, certp, outp = sys.argv[1:5]
    C = Cert(skel, bands)
    n, M = C.n, C.M
    names = [e["name"] for e in json.load(open(certp))["nodes"]]
    idx = {x: i for i, x in enumerate(names)}
    out = []
    for qc, a in M.arbs.items():
        if a.get("mode") != "fix":
            continue
        q = n.cells[qc]["out"]
        gs = sorted(a["grants"], key=lambda g: M.nodes["arb:" + g]["grant"])
        # request of each grant (as model.py: the request whose rise alone raises the grant)
        reqnets = [b for b in n.cells[gs[0]]["ins"] if isinstance(b, int) and b != q]
        gmap = {}
        for g in gs:
            for r in reqnets:
                hits = 0
                for qv in (0, 1):
                    vals = {i: (1 if n.cells[g]["ins"][i] == r else (qv if n.cells[g]["ins"][i] == q else 0))
                            for i in live_pins(n, g)}
                    hits += evalf(n, g, vals)
                if hits:
                    gmap[g] = r
        r1, r2 = gmap[gs[0]], gmap[gs[1]]
        R = a["R0"]
        a0 = [b for b in n.cells[qc]["ins"] if isinstance(b, int) and b not in (r1, r2, q, n.rst)][0]
        ix = lambda X, net: n.cells[X]["ins"].index(net)  # noqa: E731
        pth = lambda X, i: [[f"{X}/I{i}", 0]]  # noqa: E731
        e = dict(name=qc,
                 jc=idx[a["ctl"]], jg1=idx["arb:" + gs[0]], jg2=idx["arb:" + gs[1]],
                 js1=idx[a["shadows"][0]], js2=idx[a["shadows"][1]], jR=idx["arb:" + R], jA=idx[a["A0"]],
                 gG1=gs[0] + "/O", gG2=gs[1] + "/O", gR=R + "/O", gQ=qc + "/O")
        for key, X, net in (("1g1", gs[0], r1), ("qg1", gs[0], q), ("2g2", gs[1], r2), ("qg2", gs[1], q),
                            ("1R", R, r1), ("2R", R, r2), ("qR", R, q),
                            ("1Q", qc, r1), ("2Q", qc, r2), ("qQ", qc, q), ("rQ", qc, n.rst), ("A", qc, a0)):
            i = ix(X, net)
            e["i" + key] = i
            e["p" + key] = pth(X, i)
        cn = json.load(open(certp))["nodes"] if not hasattr(main, "_cn") else main._cn
        main._cn = cn
        for b, (g, r) in enumerate(((gs[0], r1), (gs[1], r2))):
            d = rpin(C.below(r))
            # copy order: the certificate's (model.py leaf order), matched by band (Lean re-checks)
            vp = cn[e["jg1" if b == 0 else "jg2"]]["pins"][0]
            if not d["st"] and len(d["paths"]) > 1:
                lo = lambda P: sum(C.eband(x)[0] for x in P)  # noqa: E731
                hi = lambda P: sum(C.eband(x)[1] for x in P)  # noqa: E731
                best = None
                for P0 in d["paths"]:
                    c0, c1 = vp["lo"][0] - lo(P0), vp["hi"][0] - hi(P0)
                    left, order = list(d["paths"]), []
                    for i in range(len(vp["lo"])):
                        m = [P for P in left if lo(P) + c0 == vp["lo"][i] and hi(P) + c1 == vp["hi"][i]]
                        if not m:
                            break
                        order.append(m[0]); left.remove(m[0])
                    if len(order) == len(d["paths"]):
                        best = order
                        break
                if best is None:
                    print(f"  {qc} request {b + 1}: no copy order matches the certificate's bands")
                else:
                    d["paths"] = best
            d["wbuf"] = f"{g}/I{ix(g, r)}"
            d["w_env"] = sp_lo(n, a0, r)
            d["srcname"] = d.pop("src")
            e[f"rq{b + 1}"] = d
        e["w_r0a0"] = sp_lo(n, n.cells[R]["out"], a0)
        out.append(e)
    json.dump({"arbs": out}, open(outp, "w"), indent=1)
    print(f"gen.py: {len(out)} arbiters ({len(M.arbs)} in the model)")


if __name__ == "__main__":
    main()
