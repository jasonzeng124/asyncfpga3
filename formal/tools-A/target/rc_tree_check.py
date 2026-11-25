#!/usr/bin/env python3
"""rc_tree_check.py (shard A, 2026-11-17): build_net's routing vs research's per-sink INTERCONNECT.

    python3 rc_tree_check.py D0.JSON ROUTED.JSON XRAY.SDF NET.json [NET2.json ...]

For every INTERCONNECT src/pin -> dst/pin of research's xray_delay.py SDF (same route), finds
the formal sink node (d0 route of the dst pin), walks the pip/hop gates of NET.json back to the
site output hop, and checks that the hop's input net is the research source cell's output (else
the sink is counted 'unmapped'). Compared value: formal routing sum (pip + hop arcs, fmin and
smax) + the sink's prjxray site-pin delay (build_net puts that inside the LUT/muxf/carry arc, and
nowhere for FFs) minus research's INTERCONNECT (FAST_MIN, SLOW_MAX). Groups:
  (a) dst SLICE_LUTX A1..A6 of a cell named *lring*, src SLICE_LUTX
  (b) dst SELMUX2_1 S0 of a cell named *fring*
  (c) every other mapped sink (by dst type/port)
Untrusted helper: it reports, it proves nothing.
"""
import json
import os
import re
import sys
from collections import defaultdict

TC = os.environ.get("TC", os.path.expanduser("~/dev2/lib/fpgatoolchain"))
DB = os.path.join(TC, "openxc7/share/nextpnr/prjxray-db/zynq7")
_tt = {}
_grid = json.load(open(os.path.join(DB, "xc7z010", "tilegrid.json")))


def sitepin_delay(tile, wire):
    t = _grid[tile]["type"]
    if t not in _tt:
        j = json.load(open(os.path.join(DB, "tile_type_%s.json" % t)))
        _tt[t] = {v["wire"]: v for s in j["sites"] for v in s["site_pins"].values() if v and v.get("wire")}
    v = _tt[t].get(wire)
    return [int(round(float(x) * 1000)) for x in v["delay"]] if v and v.get("delay") else [0, 0, 0, 0]


def q(xs, f):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(f * len(xs)))] if xs else None


def main():
    d0, routed, sdf = sys.argv[1:4]
    nets = sys.argv[4:]
    D = json.load(open(d0))
    cells = json.load(open(routed))["modules"]["top"]["cells"]
    dcell = {c["name"]: c for c in D["cells"]}

    def d0pin(cname, port):
        """research dst cell/port -> d0 conn value."""
        c = cells.get(cname)
        if not c:
            return None
        bel = c["attributes"].get("NEXTPNR_BEL", "")
        if "/" not in bel:
            return None
        site, b = bel.split("/")[:2]
        ty = c["type"]
        if ty == "SLICE_LUTX" and re.match(r"^A[1-6]$", port):
            dc, p = "%s.%sLUT" % (site, b[0]), "I%d" % (int(port[1]) - 1)
        elif ty == "SELMUX2_1":
            dc = "%s.%s" % (site, {"F7AMUX": "F7A", "F7BMUX": "F7B", "F8MUX": "F8"}[b])
            p = {"S0": "S", "I0": "I0", "I1": "I1"}.get(port)
        elif ty == "CARRY4":
            dc, p = "%s.CARRY4" % site, {"CIN": "CI"}.get(port, port)
        elif ty == "SLICE_FFX":
            dc = "%s.%s" % (site, b)
            p = {"CK": "C", "SR": "S" if "S" in dcell.get(dc, {}).get("conn", {}) else "R"}.get(port, port)
        else:
            return None
        v = dcell.get(dc, {}).get("conn", {}).get(p)
        return v if isinstance(v, dict) and "_route" in v else None

    def src_net(cname, port):
        c = cells.get(cname)
        if not c:
            return None
        bel = c["attributes"].get("NEXTPNR_BEL", "")
        if "/" not in bel:
            return None
        site, b = bel.split("/")[:2]
        ty = c["type"]
        if ty == "SLICE_LUTX":
            return "%s.%s%s" % (site, b[0], port[1])
        if ty == "SELMUX2_1":
            return "%s.%s" % (site, {"F7AMUX": "F7A", "F7BMUX": "F7B", "F8MUX": "F8"}[b])
        if ty == "SLICE_FFX":
            return "%s.%sQ" % (site, b[:-2])
        if ty == "CARRY4":
            m = re.match(r"^(CO|O)(\d)$", port)
            return m and "%s.%s%s" % (site, "CO" if m.group(1) == "CO" else "XOR", m.group(2))
        return None

    rows = []
    for line in open(sdf):
        m = re.search(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)", line)
        if not m:
            continue
        s, d = m.group(1).replace("\\", ""), m.group(2).replace("\\", "")
        sc, _, sp = s.rpartition("/")
        dc, _, dp = d.rpartition("/")
        rows.append((sc, sp, dc, dp, int(m.group(3)), int(m.group(5))))

    for np in nets:
        N = json.load(open(np))
        names = N["nodes"]
        idx = {n: i for i, n in enumerate(names)}
        drv = {}
        for g in N["gates"]:
            if g["kind"] in ("pip", "hop", "const"):
                drv[g["out"]] = g
        groups = defaultdict(lambda: ([], []))
        skip = defaultdict(int)
        for sc, sp, dc, dp, rf, rs in rows:
            cs, cd = cells.get(sc, {}), cells.get(dc, {})
            if cs.get("type") in ("PSEUDO_GND", "PSEUDO_VCC", None) or sc.startswith("$PACKER_"):
                skip["const/unknown source"] += 1
                continue
            v = d0pin(dc, dp)
            if v is None:
                skip["dst not mapped (%s)" % cd.get("type")] += 1
                continue
            r = v["_route"]
            n = idx.get(r["sink"])
            f = s_ = 0
            ok = None
            for _ in range(500):
                g = drv.get(n)
                if g is None or g["kind"] == "const":
                    break
                f += g["arcs"][0]["fmin"]
                s_ += g["arcs"][0]["smax"]
                if g["kind"] == "hop":
                    ok = names[g["ins"][0]]
                    break
                n = g["ins"][0]
            want = src_net(sc, sp)
            if ok is None or want is None or ok != want:
                skip["source mismatch/unwalkable (%s->%s)" % (cs.get("type"), cd.get("type"))] += 1
                continue
            spd = sitepin_delay(*r["sinkwire"])
            df, ds = f + spd[0] - rf, s_ + spd[3] - rs
            ty = cd.get("type")
            if ty == "SLICE_LUTX" and "lring" in dc and cs.get("type") == "SLICE_LUTX":
                k = "(a) lring LUT->LUT A1..A6"
            elif ty == "SELMUX2_1" and dp == "S0" and "fring" in dc:
                k = "(b) fring F7/F8 S0 (src %s)" % cs.get("type")
            else:
                k = "(c) %s %s <- %s" % (ty, re.sub(r"\d+$", "", dp), cs.get("type"))
            groups[k][0].append(df)
            groups[k][1].append(ds)
        print("== %s" % np)
        print("  %-44s %6s | %32s | %32s" % ("group", "n", "FAST_MIN med [p05,p95] (min,max)",
                                                "SLOW_MAX med [p05,p95] (min,max)"))
        for k in sorted(groups):
            a, b = groups[k]
            print("  %-44s %6d | %5d [%5d,%5d] (%5d,%5d) | %5d [%5d,%5d] (%5d,%5d)" % (
                k, len(a), q(a, .5), q(a, .05), q(a, .95), min(a), max(a),
                q(b, .5), q(b, .05), q(b, .95), min(b), max(b)))
        for k, c in sorted(skip.items()):
            print("  skipped: %s: %d" % (k, c))


if __name__ == "__main__":
    main()
