#!/usr/bin/env python3
"""Independent check of xray_delay's site routing-BEL charge.
usage: chk_outmux.py ROUTED.json XRAY.sdf XRAY_SITEPIP0.sdf DB_ZYNQ7
For every net whose ROUTING has exactly one source-side SITEPIP (x)OUTMUX and no other SITEPIP,
diff (xray - sitepip0) per sink INTERCONNECT must equal the ROUTING_BEL arc from timings/slicel|slicem.sdf
(FAST_MIN, SLOW_MIN, SLOW_MAX) for (site type, <L>MUX, input).  Parses the db itself."""
import json, re, sys, collections
routed, xs, x0, db = sys.argv[1:5]
# site types from tilegrid
tg = json.load(open(db + "/xc7z010/tilegrid.json"))
stype = {}
for t, v in tg.items():
    for s, ty in v.get("sites", {}).items(): stype[s] = ty
# routing bel arcs, own parser
rb = {}
for st in ("slicel", "slicem"):
    txt = open(db + "/timings/%s.sdf" % st).read()
    for cell in re.split(r"\(CELL\s*\n", txt)[1:]:
        m = re.search(r'\(CELLTYPE "ROUTING_BEL"\)\s*\(INSTANCE (\S+?)/(\S+?)\)', cell)
        if not m: continue
        for a, z, f1, f2, s1, s2 in re.findall(r"\(INTERCONNECT (\S+) (\S+) \(([\d.]+)::([\d.]+)\)\(([\d.]+)::([\d.]+)\)\)", cell):
            rb[(m.group(1), m.group(2), a)] = (float(f1), float(f2), float(s1), float(s2))
def srcname(s):
    m = re.match(r"^([A-D])([56])LUT_O[56]$", s)
    if m: return "%s%slut" % (m.group(1).lower(), m.group(2))
    m = re.match(r"^CARRY4_(C?O)(\d)$", s)
    if m: return "carry4_%s%s" % (m.group(1).lower(), m.group(2))
    return s.lower().replace("_out", "").replace("_q", "")
def load(p):
    d = {}
    for l in open(p):
        m = re.search(r"\(INTERCONNECT (\S+) (\S+) \((\d+):(\d+):(\d+)\)", l)
        if m: d[(m.group(1).replace("\\", ""), m.group(2).replace("\\", ""))] = tuple(map(int, m.group(3, 4, 5)))
    return d
A, B = load(xs), load(x0)
diffs = collections.defaultdict(list)
for (s, k), va in A.items():
    vb = B.get((s, k))
    if vb is None: continue
    diffs[s].append((k, tuple(x - y for x, y in zip(va, vb))))
nets = json.load(open(routed))["modules"]["top"]
cells = nets["cells"]
# driver pin name of each net -> SDF source name "<cell>/<pin>"
drv = {}
for cn, c in cells.items():
    for p, bits in c.get("connections", {}).items():
        if c.get("port_directions", {}).get(p) == "output":
            for b in bits: drv[b] = cn + "/" + p
stat = collections.Counter(); bad = []; shown = collections.Counter()
for nn, v in nets["netnames"].items():
    r = v.get("attributes", {}).get("ROUTING", "")
    sp = re.findall(r"SITEPIP/(SLICE_X\d+Y\d+)/([A-D](?:OUTMUX|FFMUX|5FFMUX))/(\w+)", r)
    allsp = re.findall(r"SITEPIP/", r)
    if len(sp) != 1 or len(allsp) != 1: continue
    site, bel, src = sp[0]
    b = v["bits"][0]
    if b not in drv: continue
    key = drv[b]
    # SDF source name: nextpnr escapes; compare unescaped
    outn = bel[0] + ("MUX" if bel.endswith("OUTMUX") else "5FF" if "5FF" in bel else "FF")
    exp = rb.get((stype[site], outn, srcname(src)))
    if exp is None: stat["no_db_arc_" + src] += 1; continue
    expps = tuple(round(x * 1000) for x in (exp[0], exp[2], exp[3]))
    ds = diffs.get(key.replace("\\", ""))
    if not ds: stat["no_sdf_src"] += 1; continue
    for k, d in ds:
        tag = "%s %s %s" % (stype[site], bel, src)
        if all(abs(x - y) <= 1 for x, y in zip(d, expps)): stat["match " + tag] += 1
        else: stat["MISMATCH " + tag] += 1; bad.append((nn, k, d, expps))
        if shown[tag] < 1:
            shown[tag] += 1; print("example", tag, "net", nn, "sink", k, "diff", d, "db(FAST_MIN,SLOW_MIN,SLOW_MAX)", expps)
for k, n in sorted(stat.items()): print("%6d  %s" % (n, k))
for x in bad[:10]: print("BAD", x)
