"""Own reproduction of 'SDF low by up to +490 ps on A1': every LUT-input interconnect arc of a route,
SDF number vs own prjxray Elmore (xrc.py), grouped by PHYSICAL pin (CLB tile wire)."""
import sys, statistics, re; sys.path.insert(0, '/home/user/asyncfpga3/audit/tc')
import xrc
R = xrc.Route(sys.argv[1])
by, fails, n_all = {}, 0, 0
perm = 0
for b in R.routes:
    if b not in R.driver: continue
    dc, dp = R.driver[b]
    for cn, p in R.sinks_of[b]:
        if not re.fullmatch(r"A[1-6]", p) or "LUT" not in R.cells[cn]["type"]: continue
        sd = R.ic.get((f"{dc}/{dp}", f"{cn}/{p}"))
        if sd is None: continue
        n_all += 1
        n, s = R.sink_of_cellpin(cn, p)
        if s is None or not n.ok: fails += 1; continue
        if s["pin"][1] != p[1]: perm += 1
        grp = "mux" if "MUX" in s["outpin"] else "dir"
        if len(sys.argv) > 2 and sys.argv[2] == "nomux": s = dict(s, d=[s["d"][j] - s["mux"][j] for j in range(4)])
        if len(sys.argv) > 2 and sys.argv[2] in ("mux", "dir") and grp != sys.argv[2]: continue
        by.setdefault(s["pin"][1], []).append((sd, s["d"], s["sitepin"]))
print(f"arcs {n_all}, unresolved {fails}, cell-port index != physical index: {perm}")
print("pin  n    sdf   fmin  smax  sitepin_smax  d(smax-sdf) mean p10 p90 max   d(fmin-sdf) mean")
for k in sorted(by):
    xs = by[k]; ds = sorted(d[3] - a for a, d, _ in xs); df = [d[0] - a for a, d, _ in xs]
    m = statistics.mean
    print(f"A{k} {len(xs):5d} {m(a for a,_,_ in xs):6.0f} {m(d[0] for _,d,_ in xs):5.0f} {m(d[3] for _,d,_ in xs):5.0f} {m(s[3] for *_,s in xs):6.0f}      "
          f"{m(ds):6.0f} {ds[len(ds)//10]:5.0f} {ds[9*len(ds)//10]:5.0f} {ds[-1]:5.0f}   {m(df):6.0f}")
