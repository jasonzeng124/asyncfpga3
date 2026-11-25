#!/usr/bin/env python3
"""[slice3] one row per slice dir: sim output, control LCheckXA failures (final round), failing guards / total,
failing claim items (obl.py), truncations, lchk up/sep, data passes, data-layer wall time, log-complete flag"""
import sys, re, os
def rd(p):
    try: return open(p).read()
    except Exception: return ""
print("| slice [c1,c2] | dir | sim out (want) | control LCheckXA fails | guards failing | failing claim items | truncations | lchk up/sep | data passes | data min |")
print("|---|---|---|---|---|---|---|---|---|---|")
for N in sys.argv[1:]:
    D = "/tmp/claude-0/slice3/" + N
    b, s, a, d, o = (rd(D + "/" + f) for f in ("build.log", "sim.log", "ao.log", "datal.log", "obl.log"))
    sl = re.search(r"slice \(Fraction\((\d+), (\d+)\), Fraction\((\d+), (\d+)\)\)", b)
    sl = "[%s/%s, %s/%s]" % sl.groups() if sl else "?"
    out = re.search(r"outputs \[(.*?)\] \(want (\d+)\)", s); r = re.findall(r"round \d\].*?LCheckXA:.*?failures (\d+)", a)
    gd = re.search(r"guards (\d+): GuardTime start failed \d+, end failed \d+, guards failed (\d+)", d)
    lc = re.search(r"upFormB failures (\d+), sepFormB failures (\d+)", d)
    fi = sum(int(x) for x in re.findall(r"^    \S.*?\s(\d+) /\s+\d+\s*$", o, re.M))
    tr = sum(int(x) for x in re.findall(r"""latch claim truncated at a failing union \(.*?\)["']: (\d+)""", d))
    ps = len(re.findall(r"^\s+pass \d+:", d, re.M)); done = "relative-clause stats" in d and "[lchk] GuardTime" in d
    try: tm = "%.0f" % ((int(rd(D + "/T1")) - int(rd(D + "/T0"))) / 60)
    except Exception: tm = "?"
    print("| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |" % (sl, N, "%s (%s)" % out.groups() if out else "?", r[-1] if r else "?",
          "%s / %s" % (gd.group(2), gd.group(1)) if gd and done else "n/a", fi if done else "n/a", tr if done else "n/a",
          "%s/%s" % lc.groups() if lc else "n/a", ps if done else "n/a", tm))
