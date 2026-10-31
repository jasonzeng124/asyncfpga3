#!/usr/bin/env python3
"""check_equal.py SCALED.sdf ROUTED_JSON GENWORK -- compare scale_sdf.py's values
(nextpnr names) with gen.py's annot.sdf (through names.map) arc by arc."""
import sys, re, json, collections

scaled, rjson, work = sys.argv[1:4]
cells = json.load(open(rjson))["modules"]["top"]["cells"]
bel = {n: c["attributes"].get("NEXTPNR_BEL", "") for n, c in cells.items()}
newname, icmap = {}, {}
for l in open(work + "/names.map"):
    if l.startswith("#"):
        continue
    p = l.split()
    if p[0].startswith("ic_"):
        icmap[p[0]] = p[4]            # "ic_N INTERCONNECT src -> dst"
    else:
        newname[p[0]] = p[1]
g_io, g_ic = {}, {}
inst = None
occ = collections.Counter()
for l in open(work + "/annot.sdf"):
    m = re.search(r"\(INSTANCE (\S+)\)", l)
    if m:
        inst = m.group(1); occ = collections.Counter()
    for a, z, v in re.findall(r"\(IOPATH (\S+) (\S+) \((\d+):", l):
        if inst.startswith("ic_"):
            g_ic[icmap[inst]] = int(v)
        else:
            b = newname[inst]
            g_io[(b, a, z, occ[(a, z)])] = int(v); occ[(a, z)] += 1
un = lambda s: s.replace("\\", "")
res = collections.Counter(); diffs = []; miss = []
inst = None
for l in open(scaled):
    m = re.search(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):", l)
    if m:
        d = un(m.group(2)); dc, _, dp = d.rpartition("/")
        b = bel.get(dc, "")
        k = "%s/%s" % (b, dp)
        g = g_ic.get(k)
        if g is None and re.search(r"[A-D][56]LUT$", b):
            g = g_ic.get(b[:-4] + ("5LUT" if b.endswith("6LUT") else "6LUT") + "/" + dp)
        kind = "IC"
    else:
        m2 = re.search(r"\(INSTANCE\s*(\S*?)\s*\)", l)
        if m2:
            inst = un(m2.group(1)); occ = collections.Counter(); continue
        m = re.search(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):", l)
        if not m:
            continue
        a, z = {"0": "D0", "1": "D1"}.get(m.group(1), m.group(1)), m.group(2)
        g = g_io.get((bel.get(inst, ""), a, z, occ[(a, z)])); occ[(a, z)] += 1
        kind = "IO"
    v = int(m.group(3))
    if g is None:
        res[kind + " not in annot"] += 1; miss.append(l.strip()[:150])
    elif g == v:
        res[kind + " equal"] += 1
    else:
        res[kind + " differ"] += 1
        if abs(g - v) > 1:
            res[kind + " differ>1ps"] += 1
        diffs.append((kind, l.strip()[:120], v, g))
for k in sorted(res):
    print("%-22s %d" % (k, res[k]))
for d in diffs[:10]:
    print("DIFF", d)
for d in miss[:8]: print("MISS", d)
