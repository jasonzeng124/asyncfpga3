#!/usr/bin/env python3
"""[slice] one table row per slice dir: control LCheckXA failures (final round) | data: failing guards / 264,
failing claim items (obl.py: ChainOK/JoinAnc/comb links + latch-phase audit + loop covers), lchk up/sep failures,
latch-claim truncations, fixpoint pass count, sim output"""
import sys, re
def rd(p):
    try: return open(p).read()
    except Exception: return ""
print("| slice [c1,c2] | dir | sim out | control LCheckXA fails | guards failing | failing claim items | truncations | lchk up/sep | data passes |")
print("|---|---|---|---|---|---|---|---|---|")
for N in sys.argv[1:]:
    D = "/tmp/claude-0/slice/" + N
    b, s, a, d, o = (rd(D + "/" + f) for f in ("build.log", "sim.log", "ao.log", "datal.log", "obl.log"))
    sl = re.search(r"slice \(Fraction\((\d+), (\d+)\), Fraction\((\d+), (\d+)\)\)", b)
    sl = "[%s/%s, %s/%s]" % sl.groups() if sl else "?"
    out = re.search(r"outputs \[(.*?)\]", s); r = re.findall(r"round \d\].*?LCheckXA:.*?failures (\d+)", a)
    gd = re.search(r"guards failed (\d+)", d); lc = re.search(r"upFormB failures (\d+), sepFormB failures (\d+)", d)
    fi = sum(int(x) for x in re.findall(r"^    \S.*?\s(\d+) /\s+\d+\s*$", o, re.M))
    tr = sum(int(x) for x in re.findall(r"""latch claim truncated at a failing union \(.*?\)["']: (\d+)""", d))
    ps = len(re.findall(r"^\s+pass \d+:", d, re.M)); done = "relative-clause stats" in d
    print("| %s | %s | %s | %s | %s | %s | %s | %s | %s |" % (sl, N, out.group(1) if out else "?", r[-1] if r else "?",
          (gd.group(1) + " / 264") if gd and done else "n/a", fi if done else "n/a", tr if done else "n/a",
          "%s/%s" % lc.groups() if lc else "n/a", ps if done else "n/a"))
