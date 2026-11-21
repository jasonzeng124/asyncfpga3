#!/usr/bin/env python3
"""Probe C-10d: the RT_FB relative-timing check for EVERY C-element of a routed
LUT netlist, as Lean data for one kernel `decide`.

    python3 -I formal/tools/routed2lean/rt_all.py F2L.json --ns NAME --out F.lean [--sdf S --routed R]

For each LUT `i` with a self-feedback pin (a C-element: one of its physical pins
is driven by its own O6), `routed2lean.py --launch lut:i --hops 1` builds the
DAG of i's output edge (launch = i's O6 switching), its own feedback route, its
neighbours' input routes, the neighbours' LUT arcs and their routes back.
A NEIGHBOUR pin of i is a pin driven by a LUT j != i that itself has a pin
driven by i (in a Muller pipeline: both the predecessor and the successor).
RT_FB(i): i's feedback reaches its own pin before any neighbour's response to
i's edge reaches one of i's pins (data = the feedback pin node, req = each
neighbour pin node, setup 0).  The LUT arcs that close loops (into `…@lap`) are
dropped (`--no-lap`): they lead only out of both cones, so they change no
window, and keeping them would make the two cones reconverge at the lap node.  This is the hold requirement of a LUT
C-element with fabric feedback (shard B's c2_follow_hold, 11b's 833 ps), with
the environment replaced by the actual routed neighbours.

Emits, per interval variant v, `def v : List RTEntry` (Formal/Timing/WinArrayB:
buckets, request nodes, data node, data part for exactness), one entry per C-element.
"""
import argparse
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
VARIANTS = ["indep", "fast", "slow", "fastE", "slowE", "sdf"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("f2l")
    ap.add_argument("--ns", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--report")
    ap.add_argument("--sdf")
    ap.add_argument("--routed")
    a = ap.parse_args()
    res = json.load(open(a.f2l))
    luts = res["luts"]
    drives = {}  # i -> set of LUTs i drives
    for j, l in enumerate(luts):
        for p in l["pins"]:
            if p["src"]["k"] == "lut":
                drives.setdefault(p["src"]["i"], set()).add(j)
    entries = []
    tmp = tempfile.mkdtemp()
    for i, l in enumerate(luts):
        fb = [p["pin"] for p in l["pins"] if p["src"]["k"] == "lut" and p["src"]["i"] == i]
        if len(fb) != 1:
            continue
        nb = [p["pin"] for p in l["pins"] if p["src"]["k"] == "lut" and p["src"]["i"] != i
              and p["src"]["i"] in drives.get(i, ())]
        if not nb:
            continue
        js = os.path.join(tmp, "s%d.json" % i)
        cmd = [sys.executable, "-I", os.path.join(HERE, "routed2lean.py"), a.f2l, "--launch", "lut:%d" % i,
               "--hops", "1", "--no-lap", "--ns", "X", "--emit-json", js]
        if a.sdf:
            cmd += ["--sdf", a.sdf, "--routed", a.routed]
        subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL)
        d = json.load(open(js))
        idx = {n: k for k, n in enumerate(d["nodes"])}
        dn = idx["%s.%s" % (l["site"], fb[0])]
        rn = [idx["%s.%s" % (l["site"], p)] for p in nb]
        # data part: backward cone of the feedback pin minus the launch, closed forward
        pred, succ = {}, {}
        for x in d["nets"]["indep"]:
            pred.setdefault(x[1], []).append(x[0]); succ.setdefault(x[0], []).append(x[1])
        part, todo = set(), [dn]
        while todo:
            x = todo.pop()
            if x and x not in part:
                part.add(x); todo += pred.get(x, [])
        todo = list(part)
        while todo:
            x = todo.pop()
            for y in succ.get(x, []):
                if y not in part:
                    part.add(y); todo.append(y)
        d["part"] = sorted(part)
        entries.append((i, l["site"], l["lut"], fb[0], nb, d, dn, rn))

    def slack(W, rn, dn):
        return min(W[r][0] - W[dn][1] for r in rn)
    rep = ["RT_FB per C-element (slack ps = earliest neighbour arrival - latest feedback arrival)",
           "%-22s %-4s %-10s %6s  %s" % ("LUT", "fb", "neighbours", "arcs", "  ".join("%7s" % v for v in VARIANTS))]
    worst = {v: None for v in VARIANTS}
    for i, site, L, fb, nb, d, dn, rn in entries:
        sl = {v: slack(d["wins"][v], rn, dn) for v in VARIANTS}
        for v in VARIANTS:
            if worst[v] is None or sl[v] < worst[v][0]:
                worst[v] = (sl[v], "%s.%sLUT" % (site, L))
        rep.append("%-22s %-4s %-10s %6d  %s" % ("%s.%sLUT" % (site, L), fb, ",".join(nb), len(d["nets"]["indep"]),
                                               "  ".join("%7d" % sl[v] for v in VARIANTS)))
    rep.append("worst: " + "  ".join("%s %d (%s)" % (v, worst[v][0], worst[v][1]) for v in VARIANTS))
    rep.append("passing: " + "  ".join("%s %d/%d" % (v, sum(1 for e in entries if slack(e[5]["wins"][v], e[7], e[6]) >= 0),
                                                     len(entries)) for v in VARIANTS))
    txt = "\n".join(rep) + "\n"
    sys.stdout.write(txt)
    if a.report:
        open(a.report, "w").write(txt)

    out = ["import Formal.Timing.WinArrayB", "",
           "/-! Generated by formal/tools/routed2lean/rt_all.py; do not edit, regenerate.",
           "    source: %s (fasm2lean JSON, read back from the bits)" % os.path.basename(a.f2l),
           "    One entry per C-element (LUT with a self-feedback pin): (in-arc buckets of the DAG",
           "    launched at its O6 edge, unrolled one LUT hop, the neighbour pin nodes, the feedback pin node).",
           "    Entries, in order:"]
    for i, site, L, fb, nb, d, dn, rn in entries:
        out.append("      %s.%sLUT  fb %s (node %d), neighbour pins %s (nodes %s), %d nodes, %d arcs"
                   % (site, L, fb, dn, ",".join(nb), rn, len(d["nodes"]), len(d["nets"]["indep"])))
    out += ["-/", "", "namespace Formal.Timing.Routed.%s" % a.ns, "open Formal.Timing", ""]
    for v in VARIANTS:
        out.append("/-- RT_FB instances, variant `%s`. -/" % v)
        out.append("def %s : List RTEntry := [" % v)
        ents = []
        for i, site, L, fb, nb, d, dn, rn in entries:
            bk = [[] for _ in d["nodes"]]
            for x in d["nets"][v]:
                bk[x[1]].append(x)
            ents.append("  ([%s],\n   [%s], %d, [%s])" % (",\n    ".join("[%s]" % ", ".join("⟨%d, %d, %d, %d⟩" % tuple(x) for x in b)
                                                                       for b in bk),
                                                      ", ".join(map(str, rn)), dn, ", ".join(map(str, d["part"]))))
        out.append(",\n".join(ents))
        out.append("]")
        out.append("")
    out.append("def nEntries : Nat := %d" % len(entries))
    out.append("")
    out.append("end Formal.Timing.Routed.%s" % a.ns)
    open(a.out, "w").write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
