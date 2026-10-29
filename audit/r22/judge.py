#!/usr/bin/env python3
"""Independent judge of a run_fid sweep dir: for every vector, every delivered result (R22LAP data, read off
the netlist's result bus by the passive monitor) must equal gcd(a,b) computed here; laps counted from the
R22LAP lines (and cross-checked against the tb's LAP/SUMMARY count); a run must end in 'RESULT timeout' with
laps > 0 (alive at TEND) to count as done. Vector inputs: parsed from gcd_rig.v; expected from math.gcd only."""
import re, sys, math, os
sweep, rig = sys.argv[1], sys.argv[2]
rows = re.findall(r"4'd(\d+):\s+vector = \{32'h([0-9A-F]+), 32'h([0-9A-F]+), 32'h([0-9A-F]+)\}", open(rig).read())
ab = {int(i): (int(a, 16), int(b, 16)) for i, g, b, a in rows}
ok_all = True; laps = {}
for v in range(16):
    p = os.path.join(sweep, f"v{v}.log")
    t = open(p).read() if os.path.exists(p) else ""
    exp = math.gcd(*ab[v])
    data = [int(d, 16) for d in re.findall(r"R22LAP vec=%d n=\d+ t=\d+ data=([0-9a-fxzXZ]+)" % v, t)
            if re.fullmatch(r"[0-9a-f]+", d)]
    nonhex = len(re.findall(r"R22LAP vec=%d n=\d+ t=\d+ data=\S*[xzXZ]" % v, t))
    bad = sum(1 for d in data if d != exp)
    unst = len(re.findall(r"R22UNSTABLE", t))
    m = re.search(r"SUMMARY vec=(\d+) laps=(\d+) errs=(\d+) oks=(\d+)", t)
    r = re.search(r"RESULT (\S+?):", t)
    tbl = int(m.group(2)) if m else None
    n = len(data) + nonhex
    done = bool(r) and r.group(1) == "timeout" and n > 0 and m and int(m.group(1)) == v
    good = done and bad == 0 and nonhex == 0 and unst == 0 and tbl == n
    ok_all &= good; laps[v] = n
    print(f"vec {v:2d} exp {exp:08x} mylaps {n:5d} tb_laps {tbl} wrong {bad} xz {nonhex} unstable {unst} "
          f"tb_errs {m.group(3) if m else '?'} tb_oks {m.group(4) if m else '?'} result {r.group(1) if r else 'NONE'} "
          f"{'OK' if good else 'FAIL'}")
print(f"JUDGE {'PASS' if ok_all else 'FAIL'} laps v6/v12/v13 = {laps[6]}/{laps[12]}/{laps[13]}")
