#!/usr/bin/env python3
"""pipefill.py GLSDIR [GLSDIR...]

Static check, on the exact netlist_baked.v the routed GLS simulated (ICBUF
wire delays + SLICE_LUTX arcs, SDF min column), of umux3's select bundle when
the 2-stage pipe ulink_n_index_15 fills from empty:

  launch L = stage[k] C node (k = 0: fill of the whole pipe; k = 1: last stage)
  req  = shortest L -> ... rdly chain(s) ... -> umux3.uj{0,1} ctl_req pin
  sel  = longest  L -> latch(es) -> umux3.uj{0,1} s pin
margin = req - sel (positive = request after its select, as required).
Walk restricted to cells inside ulink_n_index_15 (no external cells), so it
measures exactly the race GLS showed going X."""
import re, sys, collections

def load(g):
    names = {}
    for line in open(f"{g}/names.map"):
        if line.startswith('#'): continue
        p = line.split(None, 1)
        if len(p) == 2: names[p[0]] = p[1].strip()
    ic = {}       # w-wire -> (src n-net, D, icname)
    cells = {}    # cname -> (outnet, [(pin, wire, arc)])
    for line in open(f"{g}/netlist_baked.v"):
        m = re.search(r"ICBUF #\(\.D\((\d+)\)\) (ic_\d+) \(\.I\((\w+)\), \.O\((\w+)\)\)", line)
        if m:
            ic[m.group(4)] = (m.group(3), int(m.group(1)), m.group(2)); continue
        m = re.search(r"SLICE_LUTX #\((.*?)\) (c_\d+) \((.*)\);", line)
        if m:
            arcs = dict(re.findall(r"\.TA(\d)O6\((\d+)\)", m.group(1)))
            pins = re.findall(r"\.A(\d)\((\w+)\)", m.group(3))
            out = re.search(r"\.O6\((\w+)\)", m.group(3))
            if out:
                cells[m.group(2)] = (out.group(1), [(p, w, int(arcs[p])) for p, w in pins if p in arcs])
    return names, ic, cells

def run(g):
    names, ic, cells = load(g)
    byname = {v: k for k, v in names.items()}
    P = "uut.ulink_n_index_15.many."
    inpipe = {c for c, n in names.items() if n.startswith(P) and c in cells}
    res = {}
    for k in (0, 1):
        launch = byname[f"{P}stage[{k}].u.ctl.u.u"]
        src = cells[launch][0]
        # edges: net -> [(dstnet, delay, cname, pin)]
        best = {}
        for mode in ("min", "max"):
            arr = {src: 0}
            for _ in range(40):
                changed = False
                for c in inpipe:
                    if c == launch: continue
                    if k == 1 and "stage[1]" not in names[c]: continue
                    out, pins = cells[c]
                    for p, w, a in pins:
                        s, d, _ = ic[w]
                        if s == out or s not in arr: continue
                        t = arr[s] + d + a
                        if out not in arr or (t < arr[out] if mode == "min" else t > arr[out]):
                            arr[out] = t; changed = True
                if not changed: break
            best[mode] = arr
        # pins on umux3.uj0/uj1
        out = {}
        for j in ("uj0", "uj1"):
            c = byname[f"uut.umux3.{j}"]
            for p, w, a in cells[c][1]:
                s, d, _ = ic[w]
                drv = names.get(next((cc for cc, v in cells.items() if v[0] == s), ''), '')
                if not drv.startswith(P): continue
                kind = "sel" if ".lat." in drv else "req"
                arr = best["max" if kind == "sel" else "min"]
                if s in arr:
                    out[(j, kind)] = arr[s] + d
        for j in ("uj0", "uj1"):
            if (j, "req") in out and (j, "sel") in out:
                res[(k, j)] = (out[(j, "req")], out[(j, "sel")])
    return res

if __name__ == "__main__":
  for g in sys.argv[1:]:
    r = run(g)
    s = "  ".join(f"L{k}.{j}: req {a} sel {b} m {a-b:+d}" for (k, j), (a, b) in sorted(r.items()))
    worst = min(a - b for a, b in r.values())
    print(f"{g.split('/k4/')[-1]:32s} worst {worst:+5d} | {s}")
