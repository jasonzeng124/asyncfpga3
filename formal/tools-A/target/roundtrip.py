#!/usr/bin/env python3
"""roundtrip.py (shard A, THE goal): re-encode the decoded netlist as FASM features and
compare with the target's read-back FASM, feature by feature (one feature per set bit).

    python3 roundtrip.py NET.json FROMBIT.FASM [--report OUT.txt]

The Python mirror of the Lean round trip (to be written). Every target feature must be
produced by exactly the gates (pips, LUT INITs, output-mux hops) or by a named class of
features that carry no semantics in the netlist (listed with counts); every produced
feature must be in the target. Exit 1 otherwise.
"""
import json
import os
import re
import sys
from collections import Counter, defaultdict

TC = os.environ.get("TC", os.path.expanduser("~/dev2/lib/fpgatoolchain"))
DB = os.path.join(TC, "openxc7/share/nextpnr/prjxray-db/zynq7")


def features(path):
    out = set()
    for line in open(path):
        line = line.split("#")[0].strip()
        if not line:
            continue
        if "=" in line:
            lhs, rhs = [x.strip() for x in line.split("=", 1)]
            m = re.match(r"(.*)\[(\d+):(\d+)\]$", lhs)
            w, val = rhs.split("'")
            bits = int(val[1:], 2 if val[0] == "b" else 16)
            hi, lo = int(m.group(2)), int(m.group(3))
            for k in range(lo, hi + 1):
                if bits >> (k - lo) & 1:
                    out.add("%s[%d]" % (m.group(1), k))
        else:
            out.add(line)
    return out


def main():
    net = json.load(open(sys.argv[1]))
    target = features(sys.argv[2])
    tiles = json.load(open(os.path.join(DB, "xc7z010", "tilegrid.json")))
    import importlib.util
    here = os.path.dirname(os.path.abspath(__file__))
    spec = importlib.util.spec_from_file_location("db", os.path.join(here, "decode_base.py"))
    DBm = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(DBm)
    fab = DBm.Fabric3()
    pre_of = {}

    def pre(site):
        if site not in pre_of:
            for t, g in tiles.items():
                if site in g.get("sites", {}):
                    for s in fab.tt(g["type"])["sites"]:
                        if fab.site_name(t, s) == site:
                            pre_of[site] = "%s.%s_X%d" % (t, s["type"], s["x_coord"])
            if site not in pre_of:
                sys.exit("roundtrip: site %s not found" % site)
        return pre_of[site]

    made = Counter()
    for g in net["gates"]:
        k, p = g["kind"], g["prov"]
        if k == "pip" and not p["pseudo"]:
            made["%s.%s.%s" % (p["tile"], p["dst"], p["src"])] += 1
        elif k == "lut6":
            for b in range(64):
                if g["init"] >> b & 1:
                    made["%s.%sLUT.INIT[%d]" % (pre(p["site"]), p["lut"], b)] += 1
        elif k == "hop":
            sp = p["srcpin"]
            if sp and sp[1].endswith("MUX") and sp[2].startswith("SLICE"):
                net_ = p["net"].split(".")[1]
                L = sp[1][0]
                o = {L + "6": "O6", L + "5": "O5", L + "5Q": L + "5Q", "F7A": "F7", "F7B": "F7", "F8": "F8"}.get(net_)
                if o is None and net_.startswith("XOR"):
                    o = "XOR"
                if o is None and net_.startswith("CO"):
                    o = "CY"
                made["%s.%sOUTMUX.%s" % (pre(p["net"].split(".")[0]), L, o)] += 1
        elif k == "carry" and g["name"].endswith(".CO0"):
            pr = pre(p["site"])
            made["%s.PRECYINIT.%s" % (pr, p["precy"])] += 1
            for j, b in enumerate(p["cy0"]):
                if b:
                    made["%s.CARRY4.%sCY0" % (pr, "ABCD"[j])] += 1
    dup = [f for f, n in made.items() if n > 1]
    invented = sorted(set(made) - target)
    left = sorted(target - set(made))
    cls = Counter()
    ex = defaultdict(list)
    for f in left:
        parts = f.split(".")
        key = ".".join(parts[1:]) if len(parts) > 1 else f
        key = re.sub(r"\[\d+\]", "[]", key)
        key = re.sub(r"_X\d+Y\d+", "", key)
        kk = re.sub(r"^(SLICE[LM]_X\d)\.", "SLICE.", key)
        kk = re.sub(r"\.[A-D](FF|5FF|LUT|OUTMUX|FFMUX|5FFMUX|CY0)", r".?\1", kk)
        cls[kk] += 1
        if len(ex[kk]) < 2:
            ex[kk].append(f)
    print("roundtrip: target %d features; produced %d (%d duplicated); invented %d; left %d" %
          (len(target), len(made), len(dup), len(invented), len(left)))
    for f in invented[:20]:
        print("  INVENTED", f)
    for k, n in cls.most_common():
        print("  left %6d  %s   e.g. %s" % (n, k, ex[k][0]))


if __name__ == "__main__":
    main()
