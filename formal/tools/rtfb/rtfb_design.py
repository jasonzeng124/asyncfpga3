#!/usr/bin/env python3
"""Probe C-10f: RT_FB for every C-element of a WHOLE routed design (FFs, carry, F7
muxes, BUFGs allowed elsewhere), read from the FASM read back from the bits.

    python3 -I formal/tools/rtfb/rtfb_design.py FASM --routed R.json [--sdf S.sdf]
        [--ns NAME --lean F.lean] [--report F.txt] [--json F.json] [--variants v,v]

What it reuses, unchanged (imported, not copied): 11b's fasm2lean `Fabric`,
`Extract.walk` (backwards over the ACTIVE pips of the FASM to a site output pin),
`read_fasm`, `corners`; 10d's routed2lean `lut_arcs`, `parse_sdf`.  fasm2lean itself
stops on any LUT pin whose source is not a LUT/IOB/tie (FF Q, carry, F7/F8 mux):
here such a source is an OPAQUE node (its pin is environment, it never responds to
a C-element edge inside the window: hypothesis H_OPAQUE_CUT below).  The Elmore
code is fasm2lean's, transcribed (it is a closure inside its main()).

C-elements: cells of nextpnr's routed JSON whose `src` attribute is a LUT6 line of
cells/rtl/bd_ce.v (bd_c2, bd_c2_set, bd_c2n, bd_c2n_set, bd_c3, bd_c4, *_norst).
The logical feedback input of each module (I2 / I3 / I4) is mapped to its physical
pin by the cell's X_ORIG_PORT attributes and CROSS-CHECKED against the bits: the
physical pin the bits wire from the LUT's own output must be that pin (exit 1 if not).

RT_FB(i), as in 10d's rt_all.py but with the WHOLE responding environment instead of
one LUT hop: i's feedback route reaches its own pin before ANY response to i's O6
edge reaches any other pin of i.  A response is any simple path of LUTs
i.O6 -> route -> pin of j1 -> j1 (O6/O5) -> ... -> route -> pin p != fb of i
(i itself not re-entered).  The DAG is that set of paths UNROLLED AS A TREE (every
path its own node copies), so request and data cones share only the launch
(`sepOne`) and no simple path is lost to unrolling.  Paths are pruned by a bound:
a prefix ending at LUT output x is dropped when lo(prefix) + dist(x -> any pin of i)
>= hi(feedback), with lo/dist the H_INDEP lower bounds (fast_min, RC 0) and hi the
H_INDEP upper bound (slow_max, RC ceil E) -- every dropped path arrives at or after
the latest feedback in EVERY bound variant (each variant's lo >= indep lo and hi <=
indep hi), so pruning cannot hide a violation (H_CONE: Python-checked, not in Lean).
"""
import argparse
import heapq
import json
import math
import os
import re
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "formal", "tools", "fasm2lean"))
sys.path.insert(0, os.path.join(REPO, "formal", "tools", "routed2lean"))
import fasm2lean as F  # noqa: E402
import routed2lean as R  # noqa: E402

VARIANTS = ["indep", "fast", "slow", "fastE", "slowE", "sdf"]
BD_CE = os.path.join(REPO, "cells", "rtl", "bd_ce.v")
# logical feedback input per C-element module (cells/rtl/bd_ce.v)
FB_PORT = {"bd_c2": "I2", "bd_c2_set": "I2", "bd_c2n": "I2", "bd_c2n_set": "I2",
           "bd_c3": "I3", "bd_c4": "I4", "bd_c2_norst": "I2", "bd_c3_norst": "I3"}


class SysExitCatch(Exception):
    pass


def ce_lines():
    """bd_ce.v line number of each LUT6 instance -> module name."""
    mod, out = None, {}
    for n, line in enumerate(open(BD_CE), 1):
        m = re.match(r"\s*module\s+(\w+)", line)
        if m:
            mod = m.group(1)
        if "LUT6" in line and "(* keep *)" in line and mod in FB_PORT:
            out[n] = mod
    return out


class Ex(F.Extract):
    def source_pin(self, node):
        s = super().source_pin(node)
        if s:
            return s
        # any other site OUTPUT pin (BSCAN, BUFG, DSP, PS7 ...) is an opaque source
        for t, w in node:
            j = self.fab.tt(self.fab.ttype(t))
            sp = j["_sitepin"].get(w)
            if sp and "res" in sp[2]:  # driver pins carry R, input pins C
                return ("opaque", t, sp[0], sp[1])
        return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("fasm")
    ap.add_argument("--routed", required=True)
    ap.add_argument("--sdf")
    ap.add_argument("--db", default=F.DB)
    ap.add_argument("--ns")
    ap.add_argument("--lean")
    ap.add_argument("--report")
    ap.add_argument("--json")
    ap.add_argument("--variants", default=",".join(VARIANTS))
    ap.add_argument("--max-paths", type=int, default=4000)
    a = ap.parse_args()
    variants = a.variants.split(",")

    feats, vecs = F.read_fasm(a.fasm)
    fab = F.Fabric(a.db)
    ex = Ex(fab, feats, vecs, {})

    lut_sites = []
    for name, val in vecs.items():
        m = F.RE_LUT.match(name)
        if m:
            lut_sites.append((m.group(1), m.group(2), m.group(3), val))
    lut_sites.sort()
    lut_index = {("%s.%s" % (t, s), L): i for i, (t, s, L, _) in enumerate(lut_sites)}

    def classify(src):
        if src[0] == "const":
            return {"k": "const", "v": src[1]}
        if src[0] == "iob":
            return {"k": "opaque", "what": "IOB %s" % fab.site_name(src[1], src[2])}
        if src[0] == "opaque":
            return {"k": "opaque", "what": "%s %s.%s" % (src[2]["type"], src[1], src[3])}
        _, tile, site, pin = src
        pre = "%s.%s_X%d" % (tile, site["type"], site["x_coord"])
        if pin in ("A", "B", "C", "D"):
            i = lut_index.get((pre, pin))
            return {"k": "lut", "i": i, "out": "O6"} if i is not None else {"k": "opaque", "what": pre + "." + pin}
        if pin.endswith("MUX"):
            L = pin[0]
            for o in ("O6", "O5"):
                if "%s.%sOUTMUX.%s" % (pre, L, o) in feats:
                    i = lut_index.get((pre, L))
                    if i is not None:
                        return {"k": "lut", "i": i, "out": o}
        return {"k": "opaque", "what": "%s.%s" % (pre, pin)}

    def pipdata(t, p, pseudo, _node=None):
        s2d = p.get("src_to_dst") or {}
        return {"tile": t, "dst": p["dst_wire"], "src": p["src_wire"],
                "pass": bool(p["is_pass_transistor"]), "pseudo": pseudo,
                "delay_ps": F.corners(s2d.get("delay")),
                "res": s2d.get("res"), "in_cap": s2d.get("in_cap")}

    # ---- extraction of every LUT pin (fasm2lean's walk; a failure is recorded, not fatal)
    real_die = F.die

    def soft_die(msg, code=1):
        raise SysExitCatch(msg)
    F.die = soft_die
    luts, errors = [], []
    pathinfo = {}
    for i, (tile, sl, L, init) in enumerate(lut_sites):
        j = fab.tt(fab.ttype(tile))
        x = int(sl[-1])
        site = [s for s in j["sites"] if s["type"].startswith("SLICE") and s["x_coord"] == x][0]
        pins = []
        for k in range(1, 7):
            v = site["site_pins"]["%s%d" % (L, k)]
            what = "%s.%s.%sLUT pin %s%d" % (tile, sl, L, L, k)
            try:
                src, path = ex.walk(tile, v["wire"], what)
                pins.append({"pin": "%s%d" % (L, k), "src": classify(src),
                             "sitepin_delay_ps": F.corners(v.get("delay")),
                             "pips": [pipdata(*q) for q in reversed(path)]})
                pathinfo[(i, k)] = ex.paths[-1]
            except SysExitCatch as e:
                errors.append((i, k, str(e)))
                pins.append({"pin": "%s%d" % (L, k), "src": {"k": "opaque", "what": "ERR " + str(e)},
                             "sitepin_delay_ps": F.corners(v.get("delay")), "pips": []})
        luts.append({"tile": tile, "slice": sl, "lut": L, "site": fab.site_name(tile, site),
                     "init": init, "pins": pins})
    F.die = real_die

    # ---- Elmore per routed sink: fasm2lean main()'s closures, transcribed verbatim
    on = defaultdict(set)
    for t, ds in ex.active.items():
        for d, sw in ds:
            on[(t, sw)].add((t, d))
    for t, d, sw in ex.used_pips:
        on[(t, sw)].add((t, d))

    def node_rc(node):
        r = c = 0.0
        for t, w in node:
            rc = fab.tt(fab.ttype(t))["wires"].get(w)
            if rc:
                r += float(rc["res"]); c += float(rc["cap"])
        return r, c

    def node_load(node):
        c = 0.0
        for t, w in node:
            j = fab.tt(fab.ttype(t))
            for (_t, d) in on.get((t, w), ()):
                p = j["_by_name"].get((d, w))
                if p and not p["is_pass_transistor"]:
                    c += float((p.get("src_to_dst") or {}).get("in_cap") or 0)
            sp = j["_sitepin"].get(w)
            if sp and "cap" in sp[2]:
                c += float(sp[2]["cap"])
        return c

    def elmore(pips, src_node, src):
        seq = list(reversed(pips))
        nodes = [src_node] + [q[3] for q in seq]
        if src[0] in ("slice", "iob"):
            v = src[2]["site_pins"][src[3]]
            r_drv = float(v.get("res") or 0)
        else:
            r_drv = 0.0
        total = 0.0
        k = 0
        while k < len(nodes):
            stage = [nodes[k]]
            m = k
            while m < len(seq) and seq[m][1]["is_pass_transistor"]:
                stage.append(nodes[m + 1]); m += 1
            caps = [node_rc(n)[1] + node_load(n) for n in stage]
            for idx, n in enumerate(stage):
                rw, cw = node_rc(n)
                down = sum(caps[idx + 1:])
                total += rw * (cw / 2 + node_load(n) + down)
            total += r_drv * sum(caps)
            if m < len(seq):
                r_drv = float((seq[m][1].get("src_to_dst") or {}).get("res") or 0)
            k = m + 1
        return total * 1e-3

    emc = {}

    def elm(i, k):
        if (i, k) not in emc:
            pips, sn, src = pathinfo[(i, k)]
            emc[(i, k)] = round(elmore(pips, sn, src), 1) if src[0] != "const" else 0.0
        return emc[(i, k)]

    # ---- C-elements from the routed JSON, cross-checked against the bits
    rj = json.load(open(a.routed))
    cells = rj["modules"]["top"]["cells"]
    lines = ce_lines()
    ces = []
    nonce_fb = []
    by_bel = {}
    for n, c in cells.items():
        bel = c["attributes"].get("NEXTPNR_BEL", "")
        by_bel[bel] = (n, c)
    for i, l in enumerate(luts):
        fbs = [k for k, p in enumerate(l["pins"], 1) if p["src"]["k"] == "lut" and p["src"]["i"] == i
               and p["src"]["out"] == "O6"]
        n, c = by_bel.get("%s/%s6LUT" % (l["site"], l["lut"]), (None, None))
        mod = None
        if c is not None:
            m = re.search(r"bd_ce\.v:(\d+)\.", c["attributes"].get("src", ""))
            if m and int(m.group(1)) in lines:
                mod = lines[int(m.group(1))]
        if mod is None:
            if fbs:
                nonce_fb.append((i, n))
            continue
        want = None
        for k in range(1, 7):
            if c["attributes"].get("X_ORIG_PORT_A%d" % k) == FB_PORT[mod]:
                want = k
        if fbs != [want]:
            real_die("%s (%s, %s): feedback pin in the bits %s, X_ORIG_PORT says A%s" % (
                n, mod, l["site"], fbs, want))
        ces.append({"i": i, "cell": n, "mod": mod, "fb": want})

    # net name of a physical LUT pin, from nextpnr's routed JSON (diagnostics only)
    bit2net = {}
    for nn_, v in rj["modules"]["top"]["netnames"].items():
        for b in v["bits"]:
            if isinstance(b, int) and (b not in bit2net or len(nn_) < len(bit2net[b])):
                bit2net[b] = nn_

    def net_of(i, k):
        l = luts[i]
        for L in ("6", "5"):
            n, c = by_bel.get("%s/%s%sLUT" % (l["site"], l["lut"], L), (None, None))
            if c is None:
                continue
            port = c["attributes"].get("X_ORIG_PORT_A%d" % k)
            if port and port in c["connections"]:
                b = c["connections"][port][0]
                return bit2net.get(b, str(b))
        return "?"
    errors = [(i, k, "%s [net %s]" % (msg, net_of(i, k))) for i, k, msg in errors]
    err_pins = {(i, k) for i, k, _ in errors}

    # ---- LUT-level graph: (j, out) -> [(i, k)]
    sinks = defaultdict(list)
    for i, l in enumerate(luts):
        for k, p in enumerate(l["pins"], 1):
            s = p["src"]
            if s["k"] == "lut":
                sinks[(s["i"], s["out"])].append((i, k))
    larc6 = {}
    larc5 = {}

    def lutarc(i, k, out):
        """prjxray LUT arc pin k -> out, 4 corners ps (None: no arc, A6 into O5)."""
        l = luts[i]
        if i not in larc6:
            larc6[i] = R.lut_arcs(a.db, l["tile"], l["slice"], l["lut"])
            larc5[i] = lut5_arcs(a.db, l["tile"], l["slice"], l["lut"])
        if out == "O6":
            return larc6[i][k]
        return larc5[i].get(k)

    def route_elems(i, k):
        """element list of the route into LUT i pin k: (label, corners | ('rc', E))."""
        p = luts[i]["pins"][k - 1]
        el = [("pip %s.%s->%s" % (q["tile"], q["src"], q["dst"]), q["delay_ps"]) for q in p["pips"]]
        el.append(("wire RC", ("rc", elm(i, k))))
        el.append(("site pin %s" % p["pin"], p["sitepin_delay_ps"]))
        return el

    def ivl(c, var):
        if isinstance(c, tuple):
            E = c[1]
            return (int(math.floor(E)) if var in ("fastE", "slowE") else 0, int(math.ceil(E)))
        fm, fM, sm, sM = c
        return {"indep": (fm, sM), "fast": (fm, fM), "fastE": (fm, fM),
                "slow": (sm, sM), "slowE": (sm, sM)}[var]

    def lo(el):
        return sum(ivl(c, "indep")[0] for _, c in el)

    def hi(el):
        return sum(ivl(c, "indep")[1] for _, c in el)

    sdf_ic, sdf_io = R.parse_sdf(a.sdf, a.routed) if a.sdf else ({}, {})

    def sdf_route(srckey, i, k):
        l = luts[i]
        s = luts[srckey[0]]
        return sdf_ic.get((("lut", s["site"], s["lut"]), ("lut", l["site"], l["lut"]),
                           "A%d" % k))

    def sdf_lut(i, k, out):
        if out != "O6":
            return None
        l = luts[i]
        return sdf_io.get((("lut", l["site"], l["lut"]), k))

    # backward lower-bound distance (H_INDEP lo) from every LUT output to "any pin of ce"
    def back_dist(ce, targets):
        dist = {}
        pq = []
        for k in targets:
            # entering i's pin k from its source's output
            src = luts[ce]["pins"][k - 1]["src"]
            d = lo(route_elems(ce, k))
            key = (src["i"], src["out"])
            if d < dist.get(key, 1 << 60):
                dist[key] = d; heapq.heappush(pq, (d, key))
        # predecessor map: output (j,out) is reached from pin (j,k') whose source is (x,o)
        while pq:
            d, (j, o) = heapq.heappop(pq)
            if d > dist.get((j, o), 1 << 60):
                continue
            if j == ce:
                continue
            for k, p in enumerate(luts[j]["pins"], 1):
                s = p["src"]
                if s["k"] != "lut":
                    continue
                c = lutarc(j, k, o)
                if c is None:
                    continue
                nd = d + ivl(c, "indep")[0] + lo(route_elems(j, k))
                key = (s["i"], s["out"])
                if nd < dist.get(key, 1 << 60):
                    dist[key] = nd; heapq.heappush(pq, (nd, key))
        return dist

    report = []
    entries = []
    n_env_opaque = 0
    for ce in ces:
        i, fbk = ce["i"], ce["fb"]
        l = luts[i]
        fb_el = route_elems(i, fbk)
        fb_hi = hi(fb_el)
        targets = [k for k, p in enumerate(l["pins"], 1) if k != fbk and p["src"]["k"] == "lut"]
        opaque_pins = ["%s:%s%s" % (p["pin"], net_of(i, k), " (WALK ERROR)" if (i, k) in err_pins else "")
                       for k, p in enumerate(l["pins"], 1) if k != fbk and p["src"]["k"] == "opaque"]
        n_env_opaque += len(opaque_pins)
        dist = back_dist(i, targets)
        # tree of simple response paths
        paths = []   # list of element lists, each tagged with (labels..., end pin)
        overflow = False
        tgt_set = set(targets)

        def grow(key, prefix, plo, visited, desc):
            nonlocal overflow
            if overflow:
                return
            for (j, k) in sinks.get(key, ()):
                el = route_elems(j, k)
                sd = sdf_route(key, j, k)
                step = [(lab, c, sd if lab == "wire RC" else 0) for lab, c in el]
                if j == i:
                    if k in tgt_set and plo + lo(el) < fb_hi:
                        paths.append((prefix + step, desc + ["%s.%s" % (l["site"], l["pins"][k - 1]["pin"])], k))
                        if len(paths) > a.max_paths:
                            overflow = True
                            return
                    continue
                for out in ("O6", "O5"):
                    if (j, out) not in sinks:
                        continue
                    if (j, out) in visited:
                        continue
                    c = lutarc(j, k, out)
                    if c is None:
                        continue
                    nlo = plo + lo(el) + ivl(c, "indep")[0]
                    if nlo + dist.get((j, out), 1 << 60) >= fb_hi:
                        continue
                    grow((j, out), prefix + step + [("LUT %s.%sLUT A%d->%s" % (luts[j]["site"], luts[j]["lut"], k, out),
                                                     c, sdf_lut(j, k, out) or 0)],
                         nlo, visited | {(j, out)}, desc + ["%s.%sLUT.%s(A%d)" % (luts[j]["site"], luts[j]["lut"], out, k)])
        grow((i, "O6"), [], 0, {(i, "O6")}, [])
        # build tree DAG: node 0 = launch; fb chain; one chain per path
        arcs = {v: [] for v in variants}
        nn = [1]

        def chain(elems):
            prev = 0
            for lab, c, sd in elems:
                d = nn[0]; nn[0] += 1
                for v in variants:
                    lo_, hi_ = (sd or 0, sd or 0) if v == "sdf" else ivl(c, v)
                    arcs[v].append((prev, d, lo_, hi_))
                prev = d
            return prev
        fb_sd = sdf_route((i, "O6"), i, fbk)
        fbn = chain([(lab, c, fb_sd if lab == "wire RC" else 0) for lab, c in fb_el])
        part = list(range(1, nn[0]))
        reqs = [chain(p[0]) for p in paths]
        W = {}
        for v in variants:
            win = {0: (0, 0)}
            for s, d, lo_, hi_ in arcs[v]:
                win[d] = (win[s][0] + lo_, win[s][1] + hi_)
            sl = min((win[r][0] for r in reqs), default=None)
            W[v] = None if sl is None else sl - win[fbn][1]
        worst_path = None
        if paths:
            k = min(range(len(paths)), key=lambda q: sum(ivl(c, "slowE")[0] for _, c, _ in paths[q][0]))
            worst_path = paths[k][1]
        entries.append({"ce": ce, "site": "%s.%sLUT" % (l["site"], l["lut"]), "fb": l["pins"][fbk - 1]["pin"],
                        "nodes": nn[0], "arcs": arcs, "reqs": reqs, "fbn": fbn, "part": part,
                        "slack": W, "npaths": len(paths), "overflow": overflow, "opaque": opaque_pins,
                        "resp_pins": sorted({luts[i]["pins"][p[2] - 1]["pin"] for p in paths}),
                        "worst_path": worst_path,
                        "fb_route": [lab for lab, _ in fb_el]})

    # ---- report
    rep = ["RT_FB per C-element, whole design (slack ps = earliest response at a non-feedback pin - "
           "latest feedback arrival; '-' = no response path inside the bound: holds in every variant)",
           "source: %s" % os.path.abspath(a.fasm),
           "LUT sites %d, C-elements %d, other self-feedback LUTs %d, walk errors %d, "
           "C-element pins driven by opaque sources (FF/carry/IOB/...): %d" % (
               len(luts), len(ces), len(nonce_fb), len(errors), n_env_opaque),
           "%-22s %-10s %-4s %-12s %5s %6s  %s" % ("LUT", "module", "fb", "resp_pins", "paths", "arcs",
                                                 "  ".join("%7s" % v for v in variants))]
    for e in entries:
        rep.append("%-22s %-10s %-4s %-12s %5d %6d  %s%s" % (
            e["site"], e["ce"]["mod"], e["fb"], ",".join(e["resp_pins"]) or "-", e["npaths"],
            len(e["arcs"][variants[0]]),
            "  ".join("%7s" % ("-" if e["slack"][v] is None else e["slack"][v]) for v in variants),
            "  OVERFLOW" if e["overflow"] else ""))
    ntab = len(rep)
    rep.append("C-elements with no response path inside the bound: %d (hold in every variant); "
               "response paths per C-element max %d; overflow %d" % (
                   sum(1 for e in entries if not e["reqs"]), max([e["npaths"] for e in entries] or [0]),
                   sum(1 for e in entries if e["overflow"])))
    hops = defaultdict(int)
    for e in entries:
        if e["worst_path"]:
            hops[len(e["worst_path"]) - 1] += 1
    rep.append("LUT hops on the earliest (slowE lo) response path: %s" % dict(sorted(hops.items())))
    for v in variants:
        sl = [(e["slack"][v], e["site"]) for e in entries if e["slack"][v] is not None]
        nf = sum(1 for s, _ in sl if s < 0)
        w = min(sl) if sl else None
        rep.append("%-6s failing %d/%d   worst %s" % (v, nf, len(entries), w))
    rep.append("worst slowE paths:")
    for e in sorted(entries, key=lambda e: (e["slack"].get("slowE") is None, e["slack"].get("slowE") or 0))[:12]:
        if e["slack"].get("slowE") is None:
            break
        rep.append("  %s (%s) slack %s: fb route %d elems via %s;  earliest response %s" % (
            e["site"], e["ce"]["cell"], e["slack"]["slowE"], len(e["fb_route"]), e["fb"],
            " -> ".join(e["worst_path"] or [])))
    if errors:
        rep.append("walk errors (pins treated as opaque):")
        ce_idx = {ce["i"] for ce in ces}
        rep.append("  on C-element LUTs: %d" % sum(1 for i, _, _ in errors if i in ce_idx))
        nets = defaultdict(int)
        for _, _, x in errors:
            nets[x.split("[net ")[-1].rstrip("]")] += 1
        rep.append("  by net: " + ", ".join("%s x%d" % kv for kv in sorted(nets.items(), key=lambda kv: -kv[1])))
        rep += ["  %s" % x for _, _, x in errors[:20]]
    txt = "\n".join(rep) + "\n"
    if a.report:
        open(a.report, "w").write(txt)
    sys.stdout.write("\n".join(rep[:3] + rep[ntab:ntab + len(variants) + 15]) + "\n")
    if a.json:
        json.dump({"luts": len(luts), "ces": [{k: e[k] for k in ("site", "fb", "npaths", "slack", "resp_pins",
                                                                 "worst_path", "opaque")} | {"cell": e["ce"]["cell"],
                                                                                            "mod": e["ce"]["mod"]}
                                              for e in entries],
                   "nonce_fb": [n for _, n in nonce_fb], "errors": [x for _, _, x in errors]}, open(a.json, "w"), indent=1)

    # ---- Lean
    if a.lean:
        out = ["import Formal.Timing.WinArrayB", "",
               "/-! Generated by formal/tools/rtfb/rtfb_design.py; do not edit, regenerate.",
               "    source: %s (FASM read back from the bits)" % os.path.basename(a.fasm),
               "    One entry per C-element that has at least one response path inside the bound:",
               "    (in-arc buckets of the TREE of its feedback route and every simple response path,",
               "     the response end-pin nodes, the feedback pin node, the feedback chain = data part).",
               "    Entries, in order:"]
        lean_entries = [e for e in entries if e["reqs"]]
        for e in lean_entries:
            out.append("      %s %s (%s) fb %s, %d response paths, %d nodes" % (
                e["site"], e["ce"]["mod"], e["ce"]["cell"], e["fb"], e["npaths"], e["nodes"]))
        out += ["-/", "", "namespace Formal.Timing.Routed.%s" % a.ns, "open Formal.Timing", ""]
        for v in variants:
            out.append("/-- RT_FB instances, variant `%s`. -/" % v)
            out.append("def %s : List RTEntry := [" % v)
            ents = []
            for e in lean_entries:
                bk = [[] for _ in range(e["nodes"])]
                for x in e["arcs"][v]:
                    bk[x[1]].append(x)
                ents.append("  ([%s],\n   [%s], %d, [%s])" % (
                    ",".join("[%s]" % ", ".join("⟨%d, %d, %d, %d⟩" % tuple(x) for x in b) for b in bk),
                    ", ".join(map(str, e["reqs"])), e["fbn"], ", ".join(map(str, e["part"]))))
            out.append(",\n".join(ents))
            out.append("]")
            out.append("")
        out.append("def nEntries : Nat := %d" % len(lean_entries))
        out.append("")
        out.append("end Formal.Timing.Routed.%s" % a.ns)
        open(a.lean, "w").write("\n".join(out) + "\n")


def lut5_arcs(db, tile, slice_, lut):
    """prjxray LUT5 cell arcs Ak -> O5 (k = 1..5), ps."""
    ttype = re.sub(r"_X\d+Y\d+$", "", tile)
    key = (db, ttype)
    if key not in _SDF:
        _SDF[key] = open(os.path.join(db, "timings", ttype + ".sdf")).read()
    sdf = _SDF[key]
    kind = slice_.split("_")[0]
    m = re.search(r'\(CELLTYPE "(?:LUT5|LUT_OR_MEM5LRAM)"\)\s*\(INSTANCE %s/%s5LUT\)(.*?)\(CELL' % (kind, lut), sdf, re.S)
    if not m:
        raise SystemExit("no LUT5 arcs for %s/%s5LUT in %s.sdf" % (kind, lut, ttype))
    out = {}
    for k, a, b, c, d in re.findall(r"\(IOPATH A(\d) O5 \(([\d.]+)::([\d.]+)\)\(([\d.]+)::([\d.]+)\)\)", m.group(1)):
        out[int(k)] = [int(round(float(x) * 1000)) for x in (a, b, c, d)]
    return out


_SDF = {}

if __name__ == "__main__":
    main()
