#!/usr/bin/env python3
"""Probe C-10d: a ROUTED physical netlist (fasm2lean's JSON, read back from the
bits) + prjxray-db intervals -> a 10a timing `Netlist` (Formal/Timing/Semantics).

    python3 -I formal/tools/routed2lean/routed2lean.py F2L.json --launch L --ns NAME \
        [--sdf NEXTPNR.sdf --routed NEXTPNR_routed.json] [--out F.lean] [--report F.txt]

F2L.json is what `fasm2lean.py --json` writes: every used LUT (physical INIT,
physical pins A1..A6), and for every LUT pin and output port the full source
route: each pip with prjxray's 4-corner intrinsic delay, the site-pin delay,
and an Elmore RC term per sink.  This tool does NOT recompute any of that; it
only re-shapes it into one arc per element:

  * one arc per pip on the route (pass-transistor / zero-delay pips included,
    interval [0,0]),
  * one arc for the route's RC (Elmore) term ("wire" arc),
  * one arc for the LUT site input pin (prjxray site-pin delay),
  * one arc per LUT cell arc  physical pin Ak -> O6  (prjxray-db
    timings/<tile type>.sdf, CELLTYPE LUT6, (fast_min::fast_max)(slow_min::slow_max)).

Each SINK gets its own chain from the driving node (no arc is shared between
two sinks of one net), i.e. the hypothesis is on the delay to each sink, as in
fasm2lean's `pinDelay` / 11b's H_ROUTE.  For a chain any total inside
[sum lo, sum hi] splits into per-arc delays inside the per-arc intervals, so
this is exactly "each sink's route delay lies in its summed interval".

Launch (`--launch`): `lut:I` (output O6 of LUT I switches at t=0), `pin:I:Pk`
(LUT I's physical pin Pk, e.g. `pin:1:B4`), or `port:NAME` (the input IOB's I pin).
The LUT-level graph reachable from the launch is unrolled into a DAG: a DFS from
the launch; an edge back to a LUT output on the DFS stack (a feedback loop)
ends in a terminal LAP node `<lut>.O6@lap` (the loop's next transition) and is
not expanded further.  Pins driven by constants never switch and are dropped.
Nodes are numbered topologically (launch = 0), arcs are emitted sorted by
source, as `Formal.Timing.WinArray.winTable` wants (`sortedSrc` checks it).

Interval variants (one `Netlist` per variant, same nodes and arcs):
  indep  every element independently anywhere in [fast_min, slow_max]
         (H_INDEP: no correlation at all; the RC arc is [0, ceil E])
  fast   every element in [fast_min, fast_max]  (H_ONE_CORNER, fast die)
  slow   every element in [slow_min, slow_max]  (H_ONE_CORNER, slow die)
         RC arc [0, ceil E] in both: prjxray's R and C carry no corner
  fastE  as fast, RC arc [floor E, ceil E]   (H_RC_EXACT: the prjxray Elmore
  slowE  as slow, RC arc [floor E, ceil E]    term is a fixed additive delay,
                                               which is prjxray/timing.py's model)
  sdf    nextpnr's SDF numbers on the same paths, single value [d, d]: the
         INTERCONNECT number on the route's wire arc (0 on the pips and the
         site pin), the IOPATH number on the LUT arc.  For comparison only.
"""
import argparse
import json
import math
import os
import re
import sys
from collections import defaultdict

TC = os.environ.get("TC", os.path.expanduser("~/dev2/lib/fpgatoolchain"))
DB = os.path.join(TC, "openxc7/share/nextpnr/prjxray-db/zynq7")
VARIANTS = ["indep", "fast", "slow", "fastE", "slowE", "sdf"]


def die(msg):
    print("routed2lean: " + msg, file=sys.stderr)
    sys.exit(1)


def lut_arcs(db, tile, slice_, lut):
    """prjxray LUT6 cell arcs Ak -> O6 for this site: {pin index: [fm, fM, sm, sM]} ps."""
    ttype = re.sub(r"_X\d+Y\d+$", "", tile)
    sdf = open(os.path.join(db, "timings", ttype + ".sdf")).read()
    kind = slice_.split("_")[0]  # SLICEM / SLICEL
    m = re.search(r'\(CELLTYPE "(?:LUT6|LUT_OR_MEM6LRAM)"\)\s*\(INSTANCE %s/%s6LUT\)(.*?)\(CELL' % (kind, lut), sdf, re.S)
    if not m:
        die("no LUT6 arcs for %s/%s6LUT in %s.sdf" % (kind, lut, ttype))
    out = {}
    for k, a, b, c, d in re.findall(r"\(IOPATH A(\d) O6 \(([\d.]+)::([\d.]+)\)\(([\d.]+)::([\d.]+)\)\)", m.group(1)):
        out[int(k)] = [int(round(float(x) * 1000)) for x in (a, b, c, d)]
    if sorted(out) != [1, 2, 3, 4, 5, 6]:
        die("incomplete LUT6 arcs for %s %s" % (tile, lut))
    return out


def parse_sdf(path, routed):
    """nextpnr SDF -> {('lut', site, L) or ('port', name): cell name} maps, interconnect and iopath."""
    j = json.load(open(routed))
    # either nextpnr's routed JSON or the small {cell: bel} map run.sh extracts from it
    bels = ({n: c["attributes"].get("NEXTPNR_BEL", "") for n, c in j["modules"]["top"]["cells"].items()}
            if "modules" in j else j)
    inst = {}
    for n, bel in bels.items():
        m = re.match(r"(SLICE_X\d+Y\d+)/([A-D])6LUT$", bel)
        if m:
            inst[n] = ("lut", m.group(1), m.group(2))
        m = re.match(r"\$iopadmap\$\w+\.(\w+)\$intcell\$[IO]BUF$", n)
        if m:
            inst[n] = ("port", m.group(1))
    txt = open(path).read()
    unesc = lambda s: s.replace("\\", "")
    ic = {}
    for a, b, d in re.findall(r"\(INTERCONNECT (\S+) (\S+) \((\d+):\d+:\d+\)", txt):
        a, b = unesc(a), unesc(b)
        ca, pa = a.rsplit("/", 1)
        cb, pb = b.rsplit("/", 1)
        ic[(inst.get(ca, ca), inst.get(cb, cb), pb)] = int(d)
    io = {}
    for blk in re.findall(r'\(CELLTYPE "SLICE_LUTX"\)\s*\(INSTANCE ([^)]*)\)(.*?)\)\s*\)\s*\)', txt, re.S):
        for k, d in re.findall(r"\(IOPATH A(\d) O6 \((\d+):", blk[1]):
            io[(inst[unesc(blk[0])], int(k))] = int(d)
    return ic, io


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("f2l")
    ap.add_argument("--launch", required=True)
    ap.add_argument("--ns", required=True)
    ap.add_argument("--out")
    ap.add_argument("--report")
    ap.add_argument("--sdf")
    ap.add_argument("--routed")
    ap.add_argument("--db", default=DB)
    ap.add_argument("--name", action="append", default=[],
                    help="KEY=NODE: emit `def KEY : Nat` (node index) and `KEY_part : List Nat`")
    ap.add_argument("--belmap", help="write the {cell: bel} map of --routed here")
    a = ap.parse_args()

    res = json.load(open(a.f2l))
    luts = res["luts"]
    lname = lambda i: "%s.%sLUT.O6" % (luts[i]["site"], luts[i]["lut"])
    sdf_ic, sdf_io = parse_sdf(a.sdf, a.routed) if a.sdf else ({}, {})
    if a.belmap:
        j = json.load(open(a.routed))
        json.dump({n: c["attributes"].get("NEXTPNR_BEL", "") for n, c in j["modules"]["top"]["cells"].items()},
                  open(a.belmap, "w"), indent=1, sort_keys=True)

    # sinks of each source: LUT pins and output ports
    def src_key(s):
        if s["k"] == "lut":
            if s["out"] != "O6":
                die("only O6 sources are modelled (got %s)" % s["out"])
            return ("lut", s["i"])
        if s["k"] == "port":
            return ("port", s["name"])
        return None
    sinks = defaultdict(list)
    for i, l in enumerate(luts):
        for k, p in enumerate(l["pins"]):
            key = src_key(p["src"])
            if key:
                sinks[key].append(("pin", i, k, p))
    for o in res["outs"]:
        key = src_key(o["src"])
        if key:
            sinks[key].append(("out", o["port"], None, o))
    larcs = [lut_arcs(a.db, l["tile"], l["slice"], l["lut"]) for l in luts]

    # nodes / arcs (names; numbered later).  An arc: (src, dst, corners4 or ('rc', E), sdfval, label)
    nodes = []
    seen = set()

    def node(n):
        if n not in seen:
            seen.add(n); nodes.append(n)
        return n
    arcs = []

    def site_of(src):
        if src[0] == "lut":
            l = luts[src[1]]
            return (("lut", l["site"], l["lut"]))
        return ("port", src[1])

    def route(srcnode, srckey, kind, i, k, p, sink_name):
        """chain from srcnode over p's pips, RC, site pin -> sink node."""
        prev = srcnode
        for q in p["pips"]:
            n = node("%s/%s.%s" % (sink_name, q["tile"], q["dst"]))
            arcs.append((prev, n, q["delay_ps"], 0, "pip %s.%s->%s%s" % (q["tile"], q["src"], q["dst"],
                                                                         " (pass)" if q["pass"] else "")))
            prev = n
        if kind == "pin":
            l = luts[i]
            sd = sdf_ic.get((site_of(srckey), ("lut", l["site"], l["lut"]), p["pin"].replace(l["lut"], "A", 1)))
        else:
            sd = sdf_ic.get((site_of(srckey), ("port", i), "IN"))
        n = node("%s/rc" % sink_name if kind == "pin" else sink_name)
        arcs.append((prev, n, ("rc", p["elmore_ps"]), sd if sd is not None else 0,
                     "wire RC (Elmore %.1f ps)" % p["elmore_ps"]))
        prev = n
        if kind == "pin":
            n = node(sink_name)
            arcs.append((prev, n, p["sitepin_delay_ps"], 0, "site pin %s" % p["pin"]))
            prev = n
        else:
            # output ports: the route ends at the OLOGIC/IOB O pin; rename the end node
            pass
        return prev, sd

    # launch
    L = a.launch.split(":")
    lap_nodes = []
    if L[0] == "lut":
        root = ("lut", int(L[1])); launch = node(lname(root[1]))
        start = [(root, launch)]
    elif L[0] == "port":
        root = ("port", L[1]); launch = node("port %s (IOB I)" % L[1])
        start = [(root, launch)]
    elif L[0] == "pin":
        i = int(L[1]); pin = L[2]
        k = [p["pin"] for p in luts[i]["pins"]].index(pin)
        launch = node("%s.%s" % (luts[i]["site"], pin))
        o = node(lname(i))
        c = larcs[i][k + 1]
        arcs.append((launch, o, c, sdf_io.get((("lut", luts[i]["site"], luts[i]["lut"]), k + 1), 0),
                     "LUT %s A%d->O6" % (luts[i]["site"], k + 1)))
        root = ("lut", i)
        start = [(root, o)]
    else:
        die("bad --launch")

    sdf_missing = []
    onstack = set()
    done = set()

    def dfs(key, n):
        onstack.add(key)
        for kind, i, k, p in sinks.get(key, []):
            if kind == "pin":
                sname = "%s.%s" % (luts[i]["site"], p["pin"])
            else:
                sname = "port %s (IOB O)" % i
            end, sd = route(n, key, kind, i, k, p, sname)
            if sd is None and a.sdf:
                sdf_missing.append(sname)
            if kind != "pin":
                continue
            tgt = ("lut", i)
            c = larcs[i][k + 1]
            sdv = sdf_io.get((("lut", luts[i]["site"], luts[i]["lut"]), k + 1), 0)
            lab = "LUT %s %s(A%d)->O6" % (luts[i]["site"], p["pin"], k + 1)
            if tgt in onstack:
                ln = node(lname(i) + "@lap")
                arcs.append((end, ln, c, sdv, lab + " [lap]"))
                lap_nodes.append(ln)
            else:
                o = node(lname(i))
                arcs.append((end, o, c, sdv, lab))
                if tgt not in done:
                    dfs(tgt, o)
        onstack.discard(key)
        done.add(key)
    for key, n in start:
        dfs(key, n)

    # topological numbering (Kahn, stable)
    succ = defaultdict(list); indeg = {n: 0 for n in nodes}
    for s, d, *_ in arcs:
        succ[s].append(d); indeg[d] += 1
    if indeg[launch] != 0:
        die("arc into the launch node")
    order, ready = [], [launch]
    while ready:
        n = ready.pop(0); order.append(n)
        for d in succ[n]:
            indeg[d] -= 1
            if indeg[d] == 0:
                ready.append(d)
    if len(order) != len(nodes):
        die("cycle left after unrolling")
    idx = {n: j for j, n in enumerate(order)}

    def ivl(c, var, sd):
        if var == "sdf":
            return (sd, sd)
        if isinstance(c, tuple):  # RC term
            E = c[1]
            hi = int(math.ceil(E))
            lo = int(math.floor(E)) if var in ("fastE", "slowE") else 0
            return (lo, hi)
        fm, fM, sm, sM = c
        return {"indep": (fm, sM), "fast": (fm, fM), "fastE": (fm, fM),
                "slow": (sm, sM), "slowE": (sm, sM)}[var]
    A = sorted(((idx[s], idx[d], c, sd, lab) for s, d, c, sd, lab in arcs), key=lambda x: (x[0], x[1]))
    nets = {v: [(s, d) + ivl(c, v, sd) for s, d, c, sd, lab in A] for v in VARIANTS}
    for v, arr in nets.items():
        for s, d, lo, hi in arr:
            assert s < d and lo <= hi, (v, s, d, lo, hi)

    # windows (Python reimplementation, for the report; Lean recomputes them)
    def windows(arr):
        W = [None] * len(order); W[0] = (0, 0)
        for s, d, lo, hi in arr:
            if W[s] is None:
                continue
            e, l = W[s][0] + lo, W[s][1] + hi
            W[d] = (e, l) if W[d] is None else (min(W[d][0], e), max(W[d][1], l))
        return W
    wins = {v: windows(nets[v]) for v in VARIANTS}

    # ---- Lean
    out = []
    out.append("import Formal.Timing.WinArray")
    out.append("")
    out.append("/-! Generated by formal/tools/routed2lean/routed2lean.py; do not edit, regenerate.")
    out.append("    source: %s (fasm2lean JSON, read back from the bits)" % os.path.basename(a.f2l))
    out.append("    fasm:   %s" % os.path.relpath(res["fasm"], os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../..")))
    out.append("    launch: %s.  %d nodes, %d arcs.  Intervals in ps, per variant (see the tool's docstring):" % (a.launch, len(order), len(A)))
    out.append("    indep = [fast_min, slow_max] per element; fast / slow = one corner, RC in [0, E];")
    out.append("    fastE / slowE = one corner, RC = prjxray's fixed Elmore term; sdf = nextpnr's SDF numbers.")
    out.append("")
    out.append("    Nodes:")
    for j, n in enumerate(order):
        out.append("    %4d  %s" % (j, n))
    out.append("")
    out.append("    Arcs (src -> dst : element : indep / fast / slow / fastE / slowE / sdf):")
    for j, (s, d, c, sd, lab) in enumerate(A):
        out.append("    %4d -> %4d : %s : %s" % (s, d, lab, " ".join("%d..%d" % ivl(c, v, sd) for v in VARIANTS)))
    out.append("-/")
    out.append("")
    out.append("namespace Formal.Timing.Routed.%s" % a.ns)
    out.append("open Formal.Timing")
    out.append("")
    for v in VARIANTS:
        out.append("def %s : Netlist where" % v)
        out.append("  arcs := [")
        out.append(",\n".join("    ⟨%d, %d, %d, %d⟩" % x for x in nets[v]))
        out.append("  ]")
        out.append("")
    pred = defaultdict(set); succ2 = defaultdict(set)
    for s_, d_, *_ in A:
        pred[d_].add(s_); succ2[s_].add(d_)
    for kv in a.name:
        key, nm = kv.split("=", 1)
        if nm not in idx:
            die("--name: no node %r" % nm)
        v = idx[nm]
        # the part of KEY: its backward cone without the launch, closed forward
        part, todo = set(), [v]
        while todo:
            x = todo.pop()
            if x == 0 or x in part:
                continue
            part.add(x); todo.extend(pred[x])
        todo = list(part)
        while todo:
            x = todo.pop()
            for y in succ2[x]:
                if y not in part:
                    part.add(y); todo.append(y)
        out.append("/-- Node `%s`. -/" % nm)
        out.append("def %s : Nat := %d" % (key, v))
        out.append("/-- Nodes behind `%s` (its backward cone minus the launch, closed forward):" % key)
        out.append("    the `P` of 10a's `Separated`. -/")
        out.append("def %s_part : List Nat := [%s]" % (key, ", ".join(str(x) for x in sorted(part))))
        out.append("")
    out.append("/-- Node count. -/")
    out.append("def nNodes : Nat := %d" % len(order))
    out.append("")
    out.append("/-- Node names, by index. -/")
    out.append("def names : List String := [%s]" % ", ".join('"%s"' % n for n in order))
    out.append("")
    out.append("end Formal.Timing.Routed.%s" % a.ns)
    lean = "\n".join(out) + "\n"
    if a.out:
        open(a.out, "w").write(lean)

    # ---- report
    rep = []
    rep.append("launch %s: %d nodes, %d arcs; LAP nodes: %s" % (a.launch, len(order), len(A), lap_nodes))
    if sdf_missing:
        rep.append("no SDF INTERCONNECT for: %s" % sdf_missing)
    rep.append("%-48s %s" % ("node", "  ".join("%13s" % v for v in VARIANTS)))
    for j, n in enumerate(order):
        if "/" in n:
            continue
        rep.append("%4d %-43s %s" % (j, n, "  ".join("%13s" % ("%d..%d" % wins[v][j] if wins[v][j] else "-")
                                                    for v in VARIANTS)))
    txt = "\n".join(rep) + "\n"
    if a.report:
        open(a.report, "w").write(txt)
    sys.stdout.write(txt)


if __name__ == "__main__":
    main()
