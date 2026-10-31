#!/usr/bin/env python3
"""A_checkenv_ctl.py (auditor P18): own detection controls for glsq/check_env.py on synthetic event logs.
   python3 -I A_checkenv_ctl.py CHECK_ENV.py WORKDIR
One arbiter, bands (lo,hi): Dr1 g1 (500,600), Dq g1 (300,400), R0 bands (600,700); DA=200, DQ1=DQ2=250, reader
point delays Dr 550, Dq 350. Cases:
  A clean: A0 low on [95000,150000), q flips 1->0 at 100000 inside it, r1 low around; r1 rises at 200000 (q=0: no B2
    requirement for g1/s1) and falls at 300000 with A0 high; expect 0 violations.
  B nore: r1 still high 10 ps after q flips away (window [tau-250, tau+400+2-500)) -> expect g1 nore violation.
  C C-pointwise: A0 low at sigma + Dr - Dq - DA = sigma + 0 -> expect g1 C violation.
  D pre-reset: the nore violation of B placed before T_AFTER -> check_env ignores it (Lean field has no time guard)."""
import sys, os, json, subprocess
ce, wd = sys.argv[1], sys.argv[2]
name = "urig.udut.ucontrol_mergeX.uarb1"
xan = (f"[xarbnet] arbiter {name}.ustate$LUT6: ArbOK true; K 100, ctl lo 100; Dq g1/g2/R0 (300, 400)/(300, 400)/(600, 700), "
       f"Dr1 g1/R0 (500, 600)/(600, 700), Dr2 g2/R0 (500, 600)/(600, 700), DA0 (100, 300)\n")
info = {name: dict(q="nq", A0="na", r1="n1", r2="n2", DA=200, DQ1=250, DQ2=250,
                   readers={k: dict(req="n1" if k in ("g1", "s1") else "n2", Dr=550, Dq=350) for k in ("g1", "g2", "s1", "s2")})}
open(f"{wd}/xan.txt", "w").write(xan); json.dump(info, open(f"{wd}/info.json", "w"))
tag = "ucontrol_mergeX.uarb1"
def run(evs, tafter, label, env=None):
    open(f"{wd}/ev.log", "w").write("".join(f"EV {t} {tag} {k} {v}\n" for t, k, v in sorted(evs)))
    out = subprocess.run([sys.executable, "-I", ce, f"{wd}/ev.log", f"{wd}/info.json", f"{wd}/xan.txt", str(tafter)],
                         capture_output=True, text=True, env=env).stdout
    bad = [l for l in out.splitlines() if "violations" in l and not l.rstrip().endswith(" 0 violations")]
    print(f"{label}: {'; '.join(bad) if bad else 'no violations'}")
base = [(0, "q", 1), (0, "A0", 1), (0, "r1", 0), (0, "r2", 0)]
# A: q flips 1->0 (away for g1) at 100000 while A0 high; later r1 pulses with A0 high throughout
A = base + [(95000, "A0", 0), (100000, "q", 0), (150000, "A0", 1), (200000, "r1", 1), (300000, "r1", 0)]
run(A, 1000, "A clean")
# B: r1 high until 100010, q flips away at 100000
B = base + [(90000, "r1", 1), (100000, "q", 0), (100010, "r1", 0)]
run(B, 1000, "B nore")
# C: r1 falls at 300000; A0 low on [299990, 300010)
C = base + [(200000, "r1", 1), (299990, "A0", 0), (300010, "A0", 1), (300000, "r1", 0)]
run(C, 1000, "C pointwise C")
# D: B's pattern shifted before T_AFTER = 200000
run(B, 200000, "D pre-reset nore (T_AFTER after it)")
