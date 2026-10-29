#!/usr/bin/env python3
"""Sum a ctrace.py path's delays (pin arc + wire) in the scattered and in the unscattered netlist_baked.v.
usage: pathdelay.py BASE_BAKED SCAT_BAKED CTRACE_TXT STOP_NET"""
import sys, re, json
def load(f):
    icb, cells = {}, {}
    for ln in open(f):
        m = re.match(r"\s*(\w+) #\((.*)\) (\w+) \((.*)\);", ln)
        if not m: continue
        pd = dict(re.findall(r"\.(\w+)\(([^()]*)\)", m.group(2))); cd = dict(re.findall(r"\.(\w+)\(([^()]*)\)", m.group(4)))
        if m.group(1) == "ICBUF": icb[cd["O"]] = int(pd["D"])
        else: cells[m.group(3)] = (m.group(1), pd, cd)
    return icb, cells
B, S = load(sys.argv[1]), load(sys.argv[2])
names = {}
rn = {}
for ln in open(sys.argv[2].replace("netlist_baked.v", "names.map")):
    p = ln.split()
    if len(p) >= 2: rn[p[1]] = p[0]
tb = ts = 0
for ln in open(sys.argv[3]):
    m = re.search(r"^\s*(\d+) (n\d+)\s*=\S+ (\S*)\s+<- (\S+)\s+(\S+)\s+r(\(.*?\)|None) pin (\w+)=\S+@\d+ arc (\d+) slack -?\d+ \| wire (\d+) from (n\d+)", ln)
    if not m: continue
    t, net, nm, typ, cell, rg, pin, arc, wire, src = m.groups()
    c = rn.get(cell, cell)
    typS, pdS, cdS = S[1][c]; typB, pdB, cdB = B[1][c]
    outp = [p for p, x in cdS.items() if x == net][0]
    key = "T%s%s" % (pin, outp)
    aS, aB = int(pdS.get(key, 0)), int(pdB.get(key, 0))
    w = cdS[pin]; wS, wB = S[0].get(w, 0), B[0].get(w, 0)
    tb += aB + wB; ts += aS + wS
    print(f"{nm[:52]:52s} r{rg:7s} arc {aB:>4}->{aS:>4}  wire {wB:>5}->{wS:>5}  cum base {tb:>6} scat {ts:>6}")
    if src == sys.argv[4]: break
print(f"TOTAL base {tb} ps, scattered {ts} ps, ratio {ts/tb:.3f}")
