#!/usr/bin/env python3
# usage: check.py ORACLE LOGDIR [vec ...]
# Compares every delivered value (at lap rise AND at lap fall) to the oracle.
import sys, re, os
orc = {}
for ln in open(sys.argv[1]):
    p = ln.split()
    if len(p) == 4 and p[0].isdigit():
        orc[int(p[0])] = (int(p[1], 16), int(p[2], 16), int(p[3], 16))
d = sys.argv[2]
vecs = [int(v) for v in sys.argv[3:]] or list(range(16))
allok = True
print(f"{'vec':>3} {'a':>10} {'b':>10} {'expect':>10} {'laps':>5} {'bad':>4} {'chg':>4} {'idx@rst':>7} end   verdict")
for v in vecs:
    f = os.path.join(d, f"v{v}.log")
    if not os.path.exists(f):
        print(f"{v:>3} missing log"); allok = False; continue
    rise, fall, chg, idx, end = {}, {}, 0, None, None
    for ln in open(f):
        m = re.match(r"J (RISE|FALL|CHG) (\d+) (\d+) (\S+)", ln)
        if m:
            k, n, val = m.group(1), int(m.group(2)), m.group(4)
            val = int(val, 16) if re.fullmatch(r"[0-9a-fA-F]+", val) else None
            if k == "RISE": rise[n] = val
            elif k == "FALL": fall[n] = val
            else: chg += 1
        m = re.match(r"J RSTREL t=\d+ idx=(\S+)", ln)
        if m and idx is None: idx = m.group(1)
        if ln.startswith("J END"): end = ln.strip()
    a, b, g = orc[v]
    bad = [n for n in rise if rise[n] != g] + [n for n in fall if fall[n] != g]
    laps = len(rise)
    idxok = idx is not None and int(idx, 2) == v if idx and set(idx) <= {"0","1"} else False
    ok = laps > 0 and not bad and end is not None and idxok
    allok &= ok
    vals = sorted({hex(x) if x is not None else 'X' for x in list(rise.values()) + list(fall.values())})
    print(f"{v:>3} {a:>10x} {b:>10x} {g:>10x} {laps:>5} {len(bad):>4} {chg:>4} {str(idx):>7} {'Y' if end else 'N'}   "
          f"{'PASS' if ok else 'FAIL'}  values={','.join(vals)}")
print("ALL PASS" if allok else "NOT ALL PASS")
sys.exit(0 if allok else 1)
