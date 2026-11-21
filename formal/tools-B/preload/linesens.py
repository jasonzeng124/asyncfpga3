#!/usr/bin/env python3
"""tools-B/preload/linesens.py SIMX NET.simx NET.json ROUTED.json OUTDIR --cell REGEX -- SIMX_ARGS... (shard B, UNTRUSTED)
Which matched-delay lines set the period on this route: for every delay line (the first LUT of each '...chain.g[0].u'
cell; one line per instance), add DX ps (default 500) to every input arc of that LUT (simx "I" injection) and measure the
per-iteration period of the loop header (period.py's method on --cell, the header's request OR). dP/dX = 1: the line is
on the cycle that sets the period; 0: shortening it buys nothing here (some other cycle is longer by at least DX).
SIMX_ARGS: the simx command line after NET.simx, without --dump (one run per line, plus a reference)."""
import json, os, re, statistics, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
a = sys.argv; k = a.index("--"); simx, netx, netj, routed, out = a[1:6]; opts = a[6:k]; sargs = a[k + 1:]
cellrx = opts[opts.index("--cell") + 1]; DX = int(opts[opts.index("--dx") + 1]) if "--dx" in opts else 500
J = int(opts[opts.index("--jobs") + 1]) if "--jobs" in opts else 4
os.makedirs(out, exist_ok=True)
N = json.load(open(netj)); cells = json.load(open(routed))["modules"]["top"]["cells"]
bel = lambda cn: re.match(r"^(SLICE_X\d+Y\d+)/([A-D])([56])LUT$", cells[cn]["attributes"].get("NEXTPNR_BEL", ""))
byname = {g["name"]: g for g in N["gates"]}; names = N["nodes"]
hc = [c for c in cells if re.search(cellrx, c)]; assert len(hc) == 1, hc
hnode = str(byname["%s.%sLUT.O%s" % bel(hc[0]).groups()]["out"])
lines = {}
for cn in cells:
    m = re.match(r"^(.*)\.chain\.g\[0\]\.u$", cn)
    if m and bel(cn): lines[m.group(1)] = byname["%s.%sLUT.O%s" % bel(cn).groups()]
def period(dump):
    v0, fl = json.load(open(dump))["nodes"][hnode]
    r = [t for i, t in enumerate(fl) if (v0 ^ ((i + 1) & 1)) == 1]; d = [y - x for x, y in zip(r, r[1:])]
    m = statistics.median(d); return statistics.median([x for x in d if x < 4 * m])
def run(item):
    name, g = item
    dump = os.path.join(out, "d_%d.json" % (abs(hash(name)) % 10**9))
    extra = []
    if g is not None:
        cf = dump + ".cls"; json.dump({"S": [], "F": [], "I": [[names[g["out"]], i, DX] for i in range(g["k"])]}, open(cf, "w"))
        extra = ["--classes", cf]
    r = subprocess.run([simx, netx] + sargs + extra + ["--dump", dump], capture_output=True, text=True)
    ok = "RESULT OK" in r.stdout
    try: p = period(dump)
    except Exception: p = None
    for f in (dump, dump + ".cls"):
        if os.path.exists(f): os.remove(f)
    return name, ok, p
ref = run(("(reference)", None))
with ThreadPoolExecutor(J) as ex: rows = list(ex.map(run, sorted(lines.items())))
print("# linesens: +%d ps on each line's first LUT; reference period %s ps (%s)" % (DX, ref[2], "OK" if ref[1] else "WRONG"))
for name, ok, p in sorted(rows, key=lambda r: -(r[2] or 0)):
    print("%-60s dP %6s ps  dP/dX %5s  %s" % (name, (p - ref[2]) if p else "-", ("%.2f" % ((p - ref[2]) / DX)) if p else "-", "OK" if ok else "WRONG/none"))
