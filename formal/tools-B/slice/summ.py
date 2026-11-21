#!/usr/bin/env python3
"""summarise one slice dir: sim gcd, control (ao.py final round), data layer (datal_t final config)"""
import sys, re, os
def rd(p):
    try: return open(p).read()
    except Exception: return ""
for N in sys.argv[1:]:
    D = "/tmp/claude-0/slice/" + N
    b = rd(D + "/build.log"); s = rd(D + "/sim.log"); a = rd(D + "/ao.log"); d = rd(D + "/datal.log")
    sl = re.search(r"slice \((.*)\) mid", b); out = re.search(r"outputs (\[.*?\]) \(want (\d+)\)", s)
    rounds = re.findall(r"\[c=\d round (\d)\] RT edges (\d+) .*?FAIL (\d+) .*?LCheckXA: vectors (\d+), max\|D\| \d+, failures (\d+) (\{.*?\}) at (\d+) nodes", a)
    nojust = re.findall(r"failures with no justified edge: (\d+)", a)
    r = rounds[-1] if rounds else None
    obl = re.findall(r"^\s+(ChainOK.*?)\s+(\d+) /\s+(-?\d+) /", d, re.M)
    gd = re.search(r"guards (\d+): GuardTime start failed (\d+), end failed (\d+), guards failed (\d+)", d)
    dep = re.search(r"guards whose claim depends on a failing claim obligation: (\d+)", d)
    cf = re.search(r"claims failing \(own or inherited\): (\d+) of (\d+)", d)
    au = re.search(r"\[audit\].*failing: (\d+)", d)
    lc = re.search(r"upFormB failures (\d+), sepFormB failures (\d+)", d)
    lg = re.search(r"GuardTime with emitted tables: failed (\d+) of (\d+)", d)
    loopc = re.findall(r"loop covers .*?: (\d+) checked, (\d+) failed CovTime", d)
    tr = re.findall(r"""["']latch claim truncated at a failing union \((.*?)\)["']: (\d+)""", d)
    gm = re.search(r"GuardTime finite margins: smallest (\[.*?\])", d)
    passes = len(re.findall(r"^\s+pass \d+:", d, re.M))
    print("%s slice=%s sim=%s" % (N, sl.group(1) if sl else "?", out.groups() if out else "?"))
    print("  control: last round %s, RT edges %s, LCheckXA failures %s %s at %s nodes; no-justified-edge %s; rounds done %d" % (
        (r[0], r[1], r[4], r[5], r[6], nojust[-1] if nojust else "?", len(rounds)) if r else ("?",) * 6 + (0,)))
    print("  data: passes %d; obligations failed %s; guards dep. on failing obl %s; claims failing %s; guards %s; audit failing %s; loop covers %s; lchk up/sep %s; lchk GuardTime %s; truncations %s; smallest GuardTime margins %s" % (
        passes, sum(int(x[2]) for x in obl) if obl else "?", dep.group(1) if dep else "?", cf.groups() if cf else "?",
        gd.groups() if gd else "?", au.group(1) if au else "?", loopc[-1] if loopc else "?", lc.groups() if lc else "?", lg.groups() if lg else "?", dict(tr), gm.group(1) if gm else "?"))
