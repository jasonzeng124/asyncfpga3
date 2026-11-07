#!/usr/bin/env python3
"""muxsel.py GLSDIR... : for each bd_mux umuxK, the race between its control
channel's request (link rdly line, shortest path) and its select s (the same
link's latch output, longest path) at the mux's join LUTs uj0/uj1, launched
at every C node of the control link (a bd_pipe fills from empty: stage[0]
launch crosses every latch).  Delays: netlist_baked.v exactly as simulated
(ICBUF routed wire + SLICE_LUTX arc, SDF min column).  m = req - sel, ps;
negative = ctl_req reaches the join before its select (X / mis-select)."""
import re, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from pipefill import load

MUX = {"umux0": "ulink_n12__0", "umux1": "ulink_n12__1",
       "umux2": "ulink_n12__2", "umux3": "ulink_n_index_15"}

def stage_of(n):
    m = re.search(r"\.stage\[(\d+)\]\.", n)
    return int(m.group(1)) if m else 0

def run(g):
    names, ic, cells = load(g)
    byname = {v: k for k, v in names.items()}
    drv = {v[0]: c for c, v in cells.items()}
    out = {}
    for mux, link in MUX.items():
        P = f"uut.{link}."
        inl = [c for c, n in names.items() if n.startswith(P) and c in cells]
        launches = sorted((names[c], c) for c in inl if names[c].endswith(".ctl.u.u"))
        worst = None
        for lname, launch in launches:
            k = stage_of(lname)
            use = [c for c in inl if c != launch and stage_of(names[c]) >= k]
            arrs = {}
            for mode in ("min", "max"):
                arr = {cells[launch][0]: 0}
                for _ in range(60):
                    ch = False
                    for c in use:
                        o, pins = cells[c]
                        for p, w, a in pins:
                            s, d, _ = ic[w]
                            if s == o or s not in arr: continue
                            t = arr[s] + d + a
                            if o not in arr or (t < arr[o] if mode == "min" else t > arr[o]):
                                arr[o] = t; ch = True
                    if not ch: break
                arrs[mode] = arr
            for j in ("uj0", "uj1"):
                req = sel = None
                for p, w, a in cells[byname[f"uut.{mux}.{j}"]][1]:
                    s, d, _ = ic[w]
                    dn = names.get(drv.get(s, ''), '')
                    if not dn.startswith(P): continue
                    if ".lat." in dn and s in arrs["max"]: sel = arrs["max"][s] + d
                    elif ".lat." not in dn and s in arrs["min"]: req = arrs["min"][s] + d
                if req is None or sel is None: continue
                m = req - sel
                if worst is None or m < worst[0]:
                    worst = (m, req, sel, f"L{k}.{j}")
        out[mux] = worst
    return out

if __name__ == "__main__":
    for g in sys.argv[1:]:
        r = run(g)
        print(f"{g.split('/regen/')[-1]:22s} " + "  ".join(
            f"{m}: {v[0]:+5d} ({v[3]} req {v[1]} sel {v[2]})" for m, v in r.items()))
