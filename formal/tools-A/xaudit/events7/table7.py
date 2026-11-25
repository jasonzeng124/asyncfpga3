"""table7.py -- per seed x corner: xevents7 (A-events7) against xevents5 (A-events6)."""
import os, re
HERE = os.path.dirname(os.path.abspath(__file__))
E6 = os.path.join(HERE, "..", "events6")
print("A-events7: xevents7 (Lean, per-pin, strict, U3 + n-ary merges + guarded lines) vs xevents5 (A-events6)")
print("seed corner | Recog6 fail, OK7, log accepted | Back cert/total min | line cert/total min | merges | residual e6 -> e7 (e7 by kind) | verdict")
for s in "d 3 4 5".split():
    for c in "slow fast indep gb".split():
        f = os.path.join(HERE, f"xe7_{s}_{c}.txt")
        if not os.path.exists(f):
            continue
        t = open(f).read()
        g = lambda r: (re.search(r, t) or [None, "?"])[1]
        rec = g(r"Recog6 node failures (\d+)")
        ok = g(r"Net4.OK7 (\w+)")
        acc = g(r"accepted by runLog: (\w+)")
        bk = re.search(r"Back pins (\d+)/(\d+) certified \(strict\), min margin (-?\d+)", t)
        ln = re.search(r"line pins (\d+)/(\d+) certified \(strict\), min margin (-?\d+)", t)
        mg = re.search(r"merges (\d+)/(\d+) certified", t)
        res = g(r"RESIDUAL items \(hypotheses of design_verdict7\): (\d+)")
        kinds = {}
        for m in re.finditer(r"  RESIDUAL (\w+) ", t):
            kinds[m.group(1)] = kinds.get(m.group(1), 0) + 1
        t6 = open(os.path.join(E6, f"xe5_{s}_{c}.txt")).read()
        r6 = (re.search(r"RESIDUAL items \(hypotheses of design_verdict\): (\d+)", t6) or [None, "?"])[1]
        v = g(r"VERDICT (\w+)")
        print(f"{s} {c:5} | {rec}, {ok}, {acc} | {bk.group(1)}/{bk.group(2)} min {bk.group(3)} | "
              f"{ln.group(1)}/{ln.group(2)} min {ln.group(3)} | {mg.group(1)}/{mg.group(2)} | {r6} -> {res} {kinds} | {v}")
        for m in re.finditer(r"  RESIDUAL (.*)", t):
            print("      ", m.group(1))
