#!/usr/bin/env python3
"""ev8: every LUT->LUT routed arc in the formal slow bands vs my xrc (--lv2) arc; groups the
difference by the driver's output (O6 direct / O6 via xMUX / O5 via xMUX).
    python3 arcsall.py BUILD_DIR NET.json BANDS_slow.json --lv2"""
import os, re, sys, json, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import entry  # noqa
xrc = entry.xrc
bd, netf, bf = [a for a in sys.argv[1:] if not a.startswith("--")]
R = xrc.Route(bd); C = R.cells
N = list(json.load(open(netf))["modules"].values())[0]
B = json.load(open(bf))
drv = {}
for cn, c in N["cells"].items():
    for p, d in c["port_directions"].items():
        if d == "output":
            for b in c["connections"][p]:
                drv[b] = cn
stat = collections.defaultdict(list); worst = []
for dst, c in N["cells"].items():
    if dst not in C or C[dst]["type"] != "SLICE_LUTX":
        continue
    for p, bb in c["connections"].items():
        if c["port_directions"][p] != "input" or not bb or bb[0] not in drv:
            continue
        src = drv[bb[0]]
        if src not in C or C[src]["type"] != "SLICE_LUTX":
            continue
        fb = B["arcs"].get(f"{dst}/{p}")
        rp = [q for q in C[dst]["connections"] if re.fullmatch(r"A[1-6]", q) and (C[dst]["connections"][q] or [None])[0] is not None and R.driver.get(C[dst]["connections"][q][0], (None,))[0] == src]
        if fb is None or len(rp) != 1:
            continue
        n, s = R.sink_of_cellpin(dst, rp[0])
        if s is None:
            continue
        mine = entry.band(s["d"], "slow")
        kind = ("O5" if C[src]["attributes"]["NEXTPNR_BEL"].endswith("5LUT") else "O6") + ("-mux" if s["outpin"].endswith("MUX") else "")
        dl, dh = mine[0] - fb[0], mine[1] - fb[1]
        stat[kind].append((dl, dh)); worst.append((abs(dh), dh, kind, src, dst))
for k, v in sorted(stat.items()):
    hs = sorted(x[1] for x in v)
    print(f"{k:7s} n={len(v):5d}  hi(mine-formal): min {hs[0]:.0f} median {hs[len(hs)//2]:.0f} max {hs[-1]:.0f};  |d|<=2 ps: {sum(abs(x)<=2 for x in hs)}")
worst.sort(reverse=True)
for w in worst[:8]:
    print("  worst", round(w[1]), w[2], w[3].replace('urig.udut.', ''), '->', w[4].replace('urig.udut.', ''))
