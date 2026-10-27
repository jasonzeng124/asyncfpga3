#!/usr/bin/env python3
"""Probe C-10j front end (UNTRUSTED extraction): per routed bd_arbiter instance and
client, the routed quantities that decide H_RUNT_ACK (does the grant-fork runt reach
an acknowledge or the amerge index?), plus, per instance and corner, a potential
certificate that lower-bounds the server path R0 -> A0 in the routed timing graph.
The kernel checks every certificate and every verdict (Formal/Timing/RuntAckInst.lean).

    python3 -I extract.py                 # all designs -> build/runtack.json
    python3 -I extract.py --lean PATH     # also write the Lean instance file

Reuses (imports, never edits) 10i's extractor formal/tools/grantfork/extract.py for
the eight H_GRANT_FORK quantities (dqg dqs drg drs agq agr asq asr, with the shared
prefixes cq, cr split off exactly) and tcheck's Prjx for every other number.

Extra quantities (client k; times measured from q's output edge minus the q prefix cq):
    dqs5, drs5   q / r_k net suffix to ustate$LUT5's pin (R0 half; same site pin as
                 the O6 half on every instance seen, the extractor reports any difference)
    aRq, aRr     ustate arc q pin -> O5 (R0), r_k pin -> O5
    gw, ga       g_k net, ugrant output -> ua_k's g pin; ua_k arc g pin -> O6
    aa           ua_k arc A0 pin -> O6
    P            min path in the routed timing graph from ustate O5 (R0) to ua_k's A0 pin
                 (certificate), so the earliest A0 at ua_k's core is R0 + P + aa
    readers      every other LUT reading g_k: (route + arc) to its output, and Pz = min
                 path R0 -> the cell's z_req output (the matched-delay chain tail)
Edge prices in the server graph: prjxray at the corner's column where Prjx prices the
arc (LUT arcs, CLB interconnect, CARRY4), else GUARD_LO x nextpnr's SDF number
(H_FALLBACK_BAND; counted). Every SDF arc is kept (no false-arc pruning): more arcs
can only shorten a minimum, so this is conservative.
"""
import argparse
import heapq
import importlib.util
import json
import math
import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("grantfork_extract", HERE.parent / "grantfork/extract.py")
G = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(G)
E = G.E
COLS = G.COLS
GLO = G.GLO


def fl(x):
    return int(math.floor(x))


def ce(x):
    return int(math.ceil(x))


class Graph:
    """The routed SDF timing graph with lazily prjxray-priced edges."""

    def __init__(self, edges, P):
        self.edges, self.P = edges, P
        self.price, self.nfb = {}, 0

    def w(self, u, v, sdfw):
        k = (u, v)
        if k not in self.price:
            x = None
            try:
                if u.rsplit("/", 1)[0] == v.rsplit("/", 1)[0]:
                    x = self.P.iopath(u, v)
                else:
                    x = self.P.interconnect(u, v)
            except Exception:   # noqa: BLE001  Prjx raises on exotic sites; fall back
                x = None
            fb = x is None
            if fb:
                x = [GLO * sdfw] * 4
                self.nfb += 1
            self.price[k] = ([max(0, fl(y)) for y in x], fb)
        return self.price[k]

    def dist(self, src, targets, c, excl=frozenset()):
        """Exact Dijkstra distances at column c, run until every target is settled
        (None = unreachable)."""
        dist, done = {src: 0}, set()
        pq, left = [(0, src)], set(targets)
        while pq and left:
            d, u = heapq.heappop(pq)
            if u in done:
                continue
            done.add(u)
            left.discard(u)
            for v, sw in self.edges.get(u, ()):
                if (u, v) in excl:
                    continue
                nd = d + self.w(u, v, sw)[0][c]
                if nd < dist.get(v, 1 << 62):
                    dist[v] = nd
                    heapq.heappush(pq, (nd, v))
        return {t: (dist[t] if t in done else None) for t in targets}

    def cert(self, src, M, c, excl=frozenset()):
        """Truncated potential certificate: p(v) = min(dist(v), M); the cone is every
        node with dist < M, and every arc leaving it is listed."""
        dist, done = {src: 0}, set()
        pq = [(0, src)]
        while pq:
            d, u = heapq.heappop(pq)
            if u in done:
                continue
            if d >= M:
                break
            done.add(u)
            for v, sw in self.edges.get(u, ()):
                if (u, v) in excl:
                    continue
                nd = d + self.w(u, v, sw)[0][c]
                if nd < dist.get(v, 1 << 62):
                    dist[v] = nd
                    heapq.heappush(pq, (nd, v))
        pot = {u: dist[u] for u in done}
        cone, fb = [], 0
        for u in pot:
            for v, sw in self.edges.get(u, ()):
                if (u, v) in excl:
                    continue
                ws, f = self.w(u, v, sw)
                cone.append((u, v, ws[c]))
                fb += f
        return pot, cone, fb


def run_design(label, odir, top, T, R, F):
    rows10 = G.run_design(label, odir, top, T, R, F)
    edges, *_ = T.parse_sdf(odir / f"{top}.sdf")
    P = E.Prjx(R, F, odir / f"{top}.fasm", odir / f"{top}_routed.json")
    cells = P.cells
    gr = Graph(edges, P)
    ff = frozenset(T.fastfall_side_arcs(edges))     # H_FF_DRAINED: rise graph excludes these
    driver, readers = {}, {}
    for cn, c in cells.items():
        for p, d in c.get("port_directions", {}).items():
            for b in c["connections"].get(p, []):
                if d == "output":
                    driver[b] = f"{cn}/{p}"
                else:
                    readers.setdefault(b, []).append((cn, p))
    out_rows, certs = [], []
    arbs = sorted({r["inst"] for r in rows10})
    for a in arbs:
        st6, st5 = a + ".ustate$LUT6", a + ".ustate$LUT5"
        r0src = f"{st5}/O5"
        parent = a.rsplit(".", 1)[0] if "." in a else ""
        chain = sorted((int(cn[len(parent) + len(".udly.chain.g["):].split("]")[0]), cn)
                       for cn in cells if parent and cn.startswith(parent + ".udly.chain.g[") and cn.endswith("].u"))
        if chain:
            tail = f"{chain[-1][1]}/O6"
        elif parent and parent + ".uor" in cells:
            tail = f"{parent}.uor/O6"
        else:
            tail = None
        ua = {k: a + f".ua{k}.u" for k in (1, 2)}
        a0pin = {k: f"{ua[k]}/{G.phys(cells[ua[k]], 'I1')}" for k in (1, 2)}
        a0st = f"{st6}/{G.phys(cells[st6], 'I4')}"
        inst_rows = []
        for r in [x for x in rows10 if x["inst"] == a]:
            k = r["client"]
            gc, o = (a + ".ugrant$LUT5", "O5") if k == 1 else (a + ".ugrant$LUT6", "O6")
            qsrc = f"{st6}/O6"
            qp5, rp5 = G.phys(cells[st5], "I2"), G.phys(cells[st5], f"I{k - 1}")
            qp6, rp6 = r["pins"]["ustate_q"], r["pins"]["ustate_r"]
            rsrc = r["rsrc"]
            c4 = r["c4"]
            x = {}
            x["q5_total"] = P.interconnect(qsrc, f"{st5}/{qp5}")
            x["r5_total"] = P.interconnect(rsrc, f"{st5}/{rp5}")
            x["q6_total"] = P.interconnect(qsrc, f"{st6}/{qp6}")
            x["r6_total"] = P.interconnect(rsrc, f"{st6}/{rp6}")
            x["aRq"] = P.iopath(f"{st5}/{qp5}", f"{st5}/O5")
            x["aRr"] = P.iopath(f"{st5}/{rp5}", f"{st5}/O5")
            gpin = G.phys(cells[ua[k]], "I0")
            x["gw"] = P.interconnect(f"{gc}/{o}", f"{ua[k]}/{gpin}")
            x["ga"] = P.iopath(f"{ua[k]}/{gpin}", f"{ua[k]}/O6")
            x["aa"] = P.iopath(a0pin[k], f"{ua[k]}/O6")
            x["aSa"] = P.iopath(a0st, f"{st6}/O6")
            gnet = cells[gc]["connections"][o][0]
            rd = []
            for cn, p in readers.get(gnet, []):
                if cn == ua[k] or cells[cn]["type"] != "SLICE_LUTX":
                    if cn != ua[k]:
                        rd.append(dict(cell=cn, pin=p, kind="nonlut"))
                    continue
                for oo in ("O6", "O5"):
                    if oo in cells[cn]["connections"] and cells[cn]["connections"][oo]:
                        rw = P.interconnect(f"{gc}/{o}", f"{cn}/{p}")
                        ra = P.iopath(f"{cn}/{p}", f"{cn}/{oo}")
                        rd.append(dict(cell=cn, pin=p, out=oo, rw=rw, ra=ra))
            missing = [kk for kk, v in x.items() if v is None]
            fbr = r["fallback"]
            row = dict(design=label, inst=a, client=k, pins=r["pins"], pins5=dict(q=qp5, r=rp5),
                       fallback10=fbr, missing=missing, readers=rd, tail=tail,
                       a0pin=a0pin[k], a0st=a0st, c4=c4,
                       x={kk: (None if v is None else [round(y, 1) for y in v]) for kk, v in x.items()})
            out_rows.append(row)
            inst_rows.append(row)
        certs.append(dict(make_certs(gr, ff, a, r0src, a0pin, a0st, tail, inst_rows), design=label))
    print(f"{label}: {len(out_rows)} arbiter-clients, {gr.nfb} fallback-priced graph arcs", file=sys.stderr)
    return out_rows, certs


def need_rows(r, col):
    """(ack row without P, [index rows without P]) at a corner, or None."""
    b = corner_row(r, col)
    if b is None:
        return None
    ack = {k: b[k] for k in ("dqg", "dqs", "drg", "drs", "agq", "agr", "asq", "asr", "dqs5", "drs5", "aRq", "aRr", "gw", "ga", "aa")}
    idx = []
    for rd in r["readers"]:
        if rd.get("kind") == "nonlut" or rd["rw"] is None or rd["ra"] is None:
            continue
        c = COLS[col]
        z = dict(ack, gw=ce(rd["rw"][c]), ga=ce(rd["ra"][c]), aa=0)
        z["reader"] = f"{rd['cell']}/{rd['pin']}->{rd['out']}"
        idx.append(z)
    return ack, idx, b


def W(x):
    return (x["dqg"] + x["agq"]) - (x["dqs"] + x["asq"]) - ((x["drg"] + x["agr"]) - (x["drs"] + x["asr"]))


def late(x):
    return x["dqg"] + x["agq"] + x["gw"] + x["ga"]


def early0(x):
    """early without P"""
    return min(x["dqs5"] + x["aRq"], x["dqs"] + x["asq"] - (x["drs"] + x["asr"]) + (x["drs5"] + x["aRr"])) + x["aa"]


def make_certs(gr, ff, a, r0src, a0pin, a0st, tail, inst_rows):
    """Per corner: exact distances, the P each verdict needs, and two truncated
    certificates ('full' graph for A0, 'rise' graph for z_req)."""
    out = dict(inst=a, src=r0src, a0pin=a0pin, a0st=a0st, tail=tail, C={})
    for col, c in COLS.items():
        tf = [a0pin[1], a0pin[2], a0st]
        dfull = gr.dist(r0src, tf, c)
        drise = gr.dist(r0src, [tail], c, ff) if tail else {}
        dfull_t = gr.dist(r0src, [tail], c) if tail else {}
        needF, needR = 1, 1
        for r in inst_rows:
            nr = need_rows(r, col)
            if nr is None:
                continue
            ack, idx, _b = nr
            needF = max(needF, late(ack) - early0(ack) + 1 if W(ack) > 0 else 1)
            for z in idx:
                needR = max(needR, late(z) - early0(z) + 1 if W(z) > 0 else 1)
        reach = [v for v in dfull.values() if v is not None]
        MF = max(1, min(needF, max(reach) if reach else needF))
        potF, coneF, fbF = gr.cert(r0src, MF, c)
        ent = dict(dist_full=dfull, dist_tail_rise=drise, dist_tail_full=dfull_t,
                   full=dict(M=MF, pot=potF, cone=coneF, fb=fbF))
        if tail and drise.get(tail) is not None:
            MR = max(1, min(needR, drise[tail]))
            potR, coneR, fbR = gr.cert(r0src, MR, c, ff)
            ent["rise"] = dict(M=MR, pot=potR, cone=coneR, fb=fbR)
        out["C"][col] = ent
    return out


def corner_row(r, col):
    """Integer quantities of one row at one consistent corner (point values), or None
    if anything is missing.  Late-side quantities are rounded up, early-side down."""
    c = COLS[col]
    c4, x = r["c4"], r["x"]
    need = ("dqg", "dqs", "drg", "drs", "agq", "agr", "asq", "asr", "cq", "cr")
    if any(k not in c4 for k in need) or r["missing"]:
        return None
    v = {k: c4[k][c] for k in need}
    q5 = x["q5_total"][c] - v["cq"]
    r5 = x["r5_total"][c] - v["cr"]
    return dict(
        dqg=ce(v["dqg"]), dqs=fl(v["dqs"]), drg=fl(v["drg"]), drs=ce(v["drs"]),
        agq=ce(v["agq"]), agr=fl(v["agr"]), asq=fl(v["asq"]), asr=ce(v["asr"]),
        dqs5=fl(q5), drs5=fl(r5), aRq=fl(x["aRq"][c]), aRr=fl(x["aRr"][c]),
        gw=ce(x["gw"][c]), ga=ce(x["ga"][c]), aa=fl(x["aa"][c]), aSa=fl(x["aSa"][c]),
        # exact (unrounded) corner values for the side conditions / report
        raw=dict(v, q5=q5, r5=r5))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean")
    ap.add_argument("--part")
    a = ap.parse_args()
    sys.argv = [sys.argv[0]]
    (HERE / "build").mkdir(exist_ok=True)
    if a.part:          # one design per process (10i: Prjx caches leak across designs)
        T, R, F = E.load_rules(G.CELLS)
        label, odir, top = next(d for d in G.DESIGNS if d[0] == a.part)
        rows, certs = run_design(label, odir, top, T, R, F)
        json.dump(dict(rows=rows, certs=certs), open(HERE / f"build/part_{label}.json", "w"))
        return
    rows, certs = [], []
    for label, _o, _t in G.DESIGNS:
        subprocess.run([sys.executable, "-I", str(HERE / "extract.py"), "--part", label], check=True)
        d = json.load(open(HERE / f"build/part_{label}.json"))
        rows += d["rows"]
        certs += d["certs"]
    json.dump(dict(rows=rows, certs=certs), open(HERE / "build/runtack.json", "w"))
    if a.lean:
        subprocess.run([sys.executable, "-I", str(HERE / "emit.py"), a.lean], check=True)


if __name__ == "__main__":
    sys.path.insert(0, str(HERE))
    main()
