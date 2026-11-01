#!/usr/bin/env python3
"""widen.py (audit T4): the "23 unordered prjxray pip records widened" claim, with own reads of prjxray-db.

    python3 -I widen.py NET.json

For every pip gate (feature or pseudo), read the raw src_to_dst (or dst_to_src for a reversed
bidirectional pip) delay record from tile_type_*.json; list the distinct gates whose record is not
ordered (fmin<=fmax, smin<=smax, fmin<=smin, fmax<=smax), check the gate's arc contains every number
of the record at both corners, and count pip gates whose arc is [0,0,0,0] because prjxray has no
delay (side observation for H_DELAY).
"""
import json
import os
import re
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xnode import XDB  # noqa: E402


def main():
    N = json.load(open(sys.argv[1]))
    X = XDB()
    unordered = []
    zero = Counter()
    zero_ex = {}
    for g in N["gates"]:
        if g["kind"] != "pip":
            continue
        nm = g["name"]
        t, dw, sw = re.match(r"^([A-Z0-9_]+_X\d+Y\d+)\.([^.]+)\.([^.]+)$", nm).groups()
        p, rev = X.tt(X.ttype(t))["_pip"][(dw, sw)]
        s2d = (p.get("dst_to_src") if rev else p.get("src_to_dst")) or {}
        d = s2d.get("delay")
        a = g["arcs"][0]
        if d is None:
            if (a["fmin"], a["fmax"], a["smin"], a["smax"]) == (0, 0, 0, 0):
                k = ("pseudo" if nm not in feats else "feature", re.sub(r"_X\d+Y\d+", "", t),
                     re.sub(r"\d+", "#", dw), re.sub(r"\d+", "#", sw), p["is_pass_transistor"])
                zero[k] += 1
                zero_ex.setdefault(k, nm)
            continue
        r = [int(round(float(x) * 1000)) for x in d]
        if not (r[0] <= r[1] and r[2] <= r[3] and r[0] <= r[2] and r[1] <= r[3]):
            m, M = min(r), max(r)
            contains = a["fmin"] <= m and a["smin"] <= m and a["fmax"] >= M and a["smax"] >= M
            unordered.append((nm, r, [a["fmin"], a["fmax"], a["smin"], a["smax"]], contains))
    print("pip gates with an unordered prjxray record: %d (distinct gates)" % len(unordered))
    for u in unordered:
        print("  %-55s record %-22s arc %-22s contains-all %s" % (u[0], u[1], u[2], u[3]))
    print("pip gates with no prjxray delay (arc [0,0,0,0]): %d" % sum(zero.values()))
    for k, v in sorted(zero.items(), key=lambda kv: (kv[0][0] != "feature", -kv[1]))[:40]:
        print("  %6d %s e.g. %s" % (v, k, zero_ex[k]))


feats = set()
if __name__ == "__main__":
    canon = sys.argv[2] if len(sys.argv) > 2 else "/root/tgt/own_readback.fasm"
    feats = set(l.strip() for l in open(canon))
    main()
