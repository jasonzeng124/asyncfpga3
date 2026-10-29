#!/usr/bin/env python3
"""Auditor r17 X back-trace on a full VCD ($dumpvars(1,dut)) of a fid GLS run.
usage: xtrace.py WORK VCD NET T   -- follow the X on NET at time T (ps) back to where it was born.
At each step: the driver cell of the X net, which of its input pins (w-nets, after the ICBUF) are X just
before the X arrived, and the latest such X arrival; recurse into that pin's ICBUF source.  Stops at a net
that is X from t=0 and never defined, or at a cell whose inputs were all defined when its output went X."""
import sys, re, bisect, collections
W, VCD, NET, T = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
RE = re.compile(r"^\s*(\w+)\s*(?:#\((.*?)\))?\s+(\w+)\s*\((.*)\);\s*$")
OUTS = {"SLICE_LUTX": ("O5", "O6"), "SELMUX2_1": ("OUT",), "SLICE_FFX": ("Q",),
        "CARRY4": ("O0","O1","O2","O3","CO0","CO1","CO2","CO3"), "IOB33_OUTBUF": ("OUT",),
        "IOB33_INBUF_EN": ("OUT",), "BUFGCTRL": ("O",), "PSEUDO_GND": ("Y",), "PSEUDO_VCC": ("Y",)}
icb, cells, drv = {}, {}, {}
for ln in open(W + "/netlist_baked.v"):
    m = RE.match(ln)
    if not m: continue
    typ, par, name, con = m.groups()
    cd = dict(re.findall(r"\.(\w+)\(([^()]*)\)", con))
    pd = dict(re.findall(r"\.(\w+)\(([^()]*)\)", par or ""))
    if typ == "ICBUF": icb[cd["O"]] = (cd["I"], int(pd.get("D", 0)))
    else:
        cells[name] = (typ, pd, cd)
        for p in OUTS.get(typ, ()):
            if p in cd: drv[cd[p]] = (name, p)
names = {}
for ln in open(W + "/names.map"):
    p = ln.split()
    if len(p) >= 2: names[p[0]] = p[1]
netname = {}
for ln in open(W + "/nets.map"):
    p = ln.split()
    if len(p) >= 2: netname[p[0]] = p[1]
ids, ev = {}, collections.defaultdict(list)
t = 0
with open(VCD) as f:
    for ln in f:
        if ln.startswith("$var"):
            p = ln.split(); ids.setdefault(p[3], []).append(p[4])
        elif ln.startswith("$enddefinitions"): break
    for ln in f:
        if not ln or ln[0] == "$": continue
        c = ln[0]
        if c == "#": t = int(ln[1:]); continue
        if c in "01xz":
            for n in ids.get(ln[1:].strip(), ()):
                e = ev[n]
                if e and e[-1][0] == t: e[-1] = (t, c)
                elif not e or e[-1][1] != c: e.append((t, c))
tim = {n: [x[0] for x in e] for n, e in ev.items()}
def val(n, t):          # value at time t (after events at t)
    i = bisect.bisect_right(tim.get(n, []), t); return ev[n][i-1][1] if i else "?"
def xsince(n, t):       # time the current X run on n (at t) started
    e = ev.get(n, []); i = bisect.bisect_right(tim.get(n, []), t) - 1
    if i < 0 or e[i][1] not in "xz": return None
    return e[i][0]
def defined_ever(n, t):
    return any(v in "01" for tt, v in ev.get(n, []) if tt <= t)
n, t = NET, T
seen = set()
for step in range(400):
    t0 = xsince(n, t)
    if t0 is None: print(f"{n} is {val(n,t)} at {t}, not X"); break
    nm = netname.get(n, "")
    if n not in drv: print(f"END {n} ({nm}) X since {t0}: no driver"); break
    cell, port = drv[n]; typ, pd, cd = cells[cell]
    xin = []
    for p, w in cd.items():
        if p in OUTS.get(typ, ()) or not w.startswith(("w", "n")): continue
        s = xsince(w, t0)
        if s is not None: xin.append((s, p, w))
    born = "never defined" if not defined_ever(n, t0 - 1) else f"was {val(n, t0-1)}"
    print(f"{n:8s} {nm[:60]:60s} X@{t0:>8} ({born}) <- {typ} {names.get(cell, cell)}.{port}  X inputs: "
          + ", ".join(f"{p}@{s}" for s, p, w in sorted(xin)[-6:]))
    if not xin:
        print(f"ORIGIN: {typ} {names.get(cell,cell)} output {port} went X at {t0} with all inputs defined; inputs:",
              {p: val(w, t0) for p, w in cd.items() if w.startswith(('w','n'))}); break
    if born == "never defined":     # follow an input that is itself never defined up to the observation time
        nd = [(p, w) for s, p, w in xin if not defined_ever(icb.get(w, (w, 0))[0], T)]
        print("      never-defined inputs:", ", ".join(f"{p}={icb.get(w,(w,0))[0]}({netname.get(icb.get(w,(w,0))[0],'')[:40]})" for p, w in nd))
        if not nd: print("ORIGIN: every X input was defined at some point before", T); break
        p, w = nd[0]; src = icb.get(w, (w, 0))[0]
        if src in seen: print("LOOP back to", src); break
        seen.add(src); n = src; continue
    s, p, w = max(xin)          # the latest X arrival before the output went X
    src = icb.get(w, (w, 0))[0]
    if (src, s) in seen: print("LOOP at", src, s); break
    seen.add((src, s)); n, t = src, max(s - icb.get(w, (w, 0))[1], 0)
