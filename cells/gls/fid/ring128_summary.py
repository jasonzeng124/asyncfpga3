#!/usr/bin/env python3
"""ring128_summary.py -- ring128 at the DISTRIBUTION level, on today's routes.

    python3 cells/gls/fid/ring128_summary.py ROUTE [ROUTE ...] [--draws 32]
            [--configs model,no_region,...] [--json out.json] [--tsv out.tsv]

ROUTE is a directory holding one build of hw/ro_many_top.v
(build_hw.sh ro_many_top: ro_many_top_routed.json + ro_many_top.sdf) and
xray.sdf, xray_delay.py's prjxray SDF of that route (written here when it is
missing).

WHAT THE BOARD GAVE.  cells/hw/README.md "The population, 2026-08-23": for
128 rings, ratio = measured / predicted, predicted = 2 x the loop delay in THAT
route's nextpnr SDF, summarised per length (median, p90, p99, max; min for 7
links only) plus "76 of 128 rings ran slower than the scaled model" and the
two-parameter fit.  The per-ring table and that route are gone
(inventory.json ring128 'reproducible').  Those summary numbers are the oracle
here (AUG below, each with its README line); nothing a run of this script
printed is in it.

WHAT THIS COMPUTES.  For every one of the 128 rings of each ROUTE:
  P_np    2 x loop in the route's own nextpnr SDF (ro_many_measure.py's walk,
          via ring_predict.py), the quantity August's "predicted" was;
  P_pre   the same, with every INTERCONNECT into a LUT pin that the route
          reached through a permutation pip replaced by the placer estimate
          the pre-lut-perm-sink nextpnr wrote there (patches/README.md:
          0 ps same LUT site, 150 ps same tile, else 450 + 90|dy| + 45|dx|
          over prjxray tile-grid coordinates).  August's SDF was written by
          that binary (inventory.json ring128 'provenance'), so P_pre, not
          P_np, is the like-for-like denominator.  It is an EMULATION from
          the patch's own description, not a run of the old binary;
  P_model the full-stack delay: xray.sdf read by gen.py's own read_sdf at
          GLS_SDF_FIELD=band (0.38) with GLS_SCATTER_REGION 0.16 over 10x10
          slices + GLS_SCATTER 0.126, GLS_SCATTER_MODE=wire, seeds 1..N --
          exactly what a full-stack GLS run of that seed would annotate
          (fid/f3/ring_scatter.py's periods(), not a re-implementation).
ratio = P_model / P_denominator stands in for measured / predicted, and is
summarised the way hw/ro_many_measure.py summarises the board (its pct(),
its one-parameter fit through the origin, "slower than the scaled model" =
residual (m - k p)/m > 0, its two-parameter least-squares fit).

WHAT IT CAN SHOW.  The August route is gone, so this is ACROSS ROUTES: it
tests the SHAPE of the population (its width per length, its length
dependence, the slow fraction), not any ring.  A model that is right should
put the board's statistics inside the spread its own draws x routes give.

Controls (--configs): wrong models that must be told apart from the model
(CONFIGS below).  Verdict (verdict(), acceptance.py item ring128_summary,
SOFT): every GRADED statistic inside on the P_pre arm.  Results, md5s and
what they do and do not show: research/data/fid/ring128_summary.md.
"""
import argparse
import importlib.util
import json
import os
import statistics
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
CELLS = HERE.parent.parent
LENS = [7, 15, 31, 63]


def _load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


rp = _load(HERE / "ring_predict.py", "ring_predict")


# ------------------------------------------------------------ the oracle
# cells/hw/README.md, "The population, 2026-08-23" (and inventory.json ring128).
AUG = {
    "per_length": {   # README.md:297-300 (median, p90, p99, max); min: README.md:309
        7: {"median": 1.176, "p90": 1.438, "p99": 1.470, "max": 1.470, "min": 0.773},
        15: {"median": 0.987, "p90": 1.117, "p99": 1.203, "max": 1.203},
        31: {"median": 0.959, "p90": 1.085, "p99": 1.142, "max": 1.142},
        63: {"median": 0.969, "p90": 1.059, "p99": 1.134, "max": 1.134},
    },
    "all": {"median": 0.989, "p90": 1.252, "p99": 1.457, "max": 1.470},   # README.md:301
    "kfit": 0.9616,           # README.md:322
    "slower": 76,             # README.md:353, of 128
    "k2": 0.9383, "d2_ps": 988,   # README.md:323
    "cover85": {7: 0.156, 15: 0.562, 31: 0.562, 63: 0.812, "all": 0.523},  # README.md:297-301
}


# ----------------------------------------------- ro_many_measure's statistics

def pct(sorted_vals, p):
    """hw/ro_many_measure.py's pct(): nearest rank on a sorted list."""
    if not sorted_vals:
        return float("nan")
    k = max(0, min(len(sorted_vals) - 1, int(round(p / 100.0 * len(sorted_vals) + 0.5)) - 1))
    return sorted_vals[k]


def summarise(meas, pred, length):
    """meas, pred: {ring: ps}; length: {ring: links}.  The board's summary,
    computed exactly as hw/ro_many_measure.py computes it."""
    have = sorted(k for k in meas if k in pred and meas[k] > 0)
    ratio = {k: meas[k] / pred[k] for k in have}
    kfit = sum(meas[k] * pred[k] for k in have) / sum(pred[k] ** 2 for k in have)
    resid = {k: (meas[k] - kfit * pred[k]) / meas[k] for k in have}
    out = {"n": len(have), "per_length": {}}
    for n in LENS + ["all"]:
        ks = [k for k in have if n == "all" or length[k] == n]
        rr = sorted(ratio[k] for k in ks)
        ar = sorted(abs(resid[k]) for k in ks)
        if not rr:
            continue
        out["per_length"][n] = {
            "n": len(rr), "median": statistics.median(rr), "p90": pct(rr, 90),
            "p99": pct(rr, 99), "max": rr[-1], "min": rr[0],
            "cover85": sum(1 for a in ar if a <= 0.085) / len(ar)}
    out["kfit"] = kfit
    out["slower"] = sum(1 for k in have if resid[k] > 0)
    n_ = len(have)
    mp = sum(pred[k] for k in have) / n_
    mm = sum(meas[k] for k in have) / n_
    sxx = sum((pred[k] - mp) ** 2 for k in have)
    if sxx > 0:
        k2 = sum((pred[k] - mp) * (meas[k] - mm) for k in have) / sxx
        out["k2"], out["d2_ps"] = k2, mm - k2 * mp
    pl = out["per_length"]
    if 7 in pl and 63 in pl:
        out["short_long"] = pl[7]["median"] / pl[63]["median"]
    return out


# ------------------------------------------------- the pre-patch denominator

def tile_grid(xray_db):
    """{site: (tile, grid_x, grid_y)} from prjxray's tilegrid.json."""
    tg = json.load(open(Path(xray_db) / "xc7z010" / "tilegrid.json"))
    out = {}
    for t, v in tg.items():
        for s in v.get("sites", {}):
            out[s] = (t, v["grid_x"], v["grid_y"])
    return out


def predict_delay(src_bel, dst_bel, grid):
    """nextpnr-xilinx's placer estimate, as patches/README.md quotes it."""
    ss, sb = src_bel.split("/")[:2]
    ds, db = dst_bel.split("/")[:2]
    st, sx, sy = grid[ss]
    dt, dx, dy = grid[ds]
    if st == dt:
        return 0 if (ss == ds and sb[0] == db[0]) else 150
    return 450 + 90 * abs(dy - sy) + 45 * abs(dx - sx)


class Route:
    def __init__(self, d, xray_db, grid=None, design="ro_many_top", xray=True):
        self.dir = Path(d)
        self.json = self.dir / f"{design}_routed.json"
        self.sdf = self.dir / f"{design}.sdf"
        self.xray = self.dir / "xray.sdf"
        if xray and not self.xray.exists():
            self.make_xray(xray_db)
        top = json.load(open(self.json))["modules"]["top"]
        self.cells = top["cells"]
        self.routes = {}
        for nn in top["netnames"].values():
            r = nn.get("attributes", {}).get("ROUTING")
            if r and nn["bits"]:
                self.routes.setdefault(nn["bits"][0], r)
        self.grid = grid or tile_grid(xray_db)
        self.length, self.p_np, self.p_pre = {}, {}, {}
        self.n_perm = self.n_ic = 0
        E = rp.parse(self.sdf)
        for name, n, pref, ex in rp.rings(design):
            a, _ = rp.loop(E, pref, ex)
            if not a:
                continue
            self.length[name] = n
            self.p_np[name] = 2 * a[0]
            self.p_pre[name] = 2 * self.loop_pre(E, pref, ex)

    def make_xray(self, xray_db):
        tc = Path(os.environ.get("TC", str(Path.home() / "dev2/lib/fpgatoolchain")))
        env = {**os.environ, "XRAY_DB": str(xray_db),
               "PYTHONPATH": f"{tc / 'openxc7-src/prjxray'}:{tc / 'openxc7/lib/python'}"}
        tmp = self.xray.with_suffix(".part")
        r = subprocess.run([sys.executable, str(HERE / "xray_delay.py"), "--routed", str(self.json),
                            "--sdf", str(self.sdf), "--out", str(tmp)], env=env,
                           capture_output=True, text=True)
        (self.dir / "xray.log").write_text(r.stdout + r.stderr)
        if r.returncode or not tmp.exists():
            raise RuntimeError(f"xray_delay.py failed on {self.dir} (see xray.log)")
        tmp.rename(self.xray)

    def permuted(self, inst, port):
        """True iff the route reaches this LUT input through a permutation pip,
        i.e. never visits SITEWIRE/<site>/<port>: the case the unpatched
        nextpnr answered with predictDelay() instead of the route."""
        c = self.cells[inst]
        if c["type"] != "SLICE_LUTX":
            return False
        site = c["attributes"]["NEXTPNR_BEL"].split("/")[0]
        f = self.routes[c["connections"][port][0]].split(";")
        return f"SITEWIRE/{site}/{port}" not in set(f[i] for i in range(0, len(f) - 2, 3))

    def loop_pre(self, E, pref, exclude=None):
        """rp.loop's walk, with the pre-patch number on permuted LUT sinks."""
        start = pin = pref + "inv/O6"
        tot = 0
        while True:
            (dst, w), = [(d, w) for d, w in E[pin]
                         if rp.inst_of(d).startswith(pref) and rp.inst_of(d) != exclude]
            si, di = rp.inst_of(pin), rp.inst_of(dst)
            if si != di:
                self.n_ic += 1
                if self.permuted(di, dst.rpartition("/")[2]):
                    self.n_perm += 1
                    tot += predict_delay(self.cells[si]["attributes"]["NEXTPNR_BEL"],
                                         self.cells[di]["attributes"]["NEXTPNR_BEL"], self.grid)
                    pin = dst
                    if pin == start:
                        return tot
                    continue
            tot += w[0]
            pin = dst
            if pin == start:
                return tot


# ------------------------------------------------------------- the model

MODEL = {"GLS_SDF_FIELD": "band", "GLS_SDF_BAND": "0.38",
         "GLS_SCATTER_REGION": "0.16", "GLS_REGION_SLICES": "10",
         "GLS_SCATTER": "0.126", "GLS_SCATTER_MODE": "wire"}
CONFIGS = {
    # the full stack as calibrated (f3_model.md section 3, fullstack.md)
    "model": ("xray", MODEL),
    # controls: each one thing wrong
    "no_region": ("xray", {**MODEL, "GLS_SCATTER_REGION": "0"}),
    "no_scatter": ("xray", {**MODEL, "GLS_SCATTER_REGION": "0", "GLS_SCATTER": "0"}),
    # x2, not x3: at sigma_r 0.48 one region in 50 draws a negative factor,
    # gen.py clamps its arcs to 0 ps and whole rings come out at 0 ps
    "scatter_x2": ("xray", {**MODEL, "GLS_SCATTER_REGION": "0.32", "GLS_SCATTER": "0.252"}),
    "fast_min": ("xray", {**MODEL, "GLS_SDF_FIELD": "min"}),
    "slow_max": ("xray", {**MODEL, "GLS_SDF_FIELD": "max"}),
    # POST HOC, fitted to the August level on the P_pre arm (band 0.29 makes
    # the all-ring median ~0.99 there) with the region term dropped: the
    # alternative account in research/data/fid/ring128_summary.md.  Fitted to
    # the oracle, so it is evidence of nothing until a second route exists.
    "posthoc_pre": ("xray", {**MODEL, "GLS_SDF_BAND": "0.29", "GLS_SCATTER_REGION": "0"}),
    # the scatter alone on nextpnr's own SDF (no xray delays)
    "nextpnr_scatter": ("nextpnr", {**MODEL, "GLS_SDF_FIELD": "min"}),
}
_rs = None


def model_periods(route, which, env, seed):
    """{ring: P_model} for one draw: gen.py's read_sdf through ring_scatter.periods."""
    global _rs
    if _rs is None:
        _rs = _load(HERE / "f3" / "ring_scatter.py", "ring_scatter")
    with tempfile.TemporaryDirectory() as w:
        os.symlink(route.json.resolve(), os.path.join(w, "routed.json"))
        os.symlink((route.xray if which == "xray" else route.sdf).resolve(),
                   os.path.join(w, "routed.sdf"))
        for k in [k for k in os.environ if k.startswith("GLS_")]:
            del os.environ[k]
        e = dict(env)
        if float(e.get("GLS_SCATTER", "0")) or float(e.get("GLS_SCATTER_REGION", "0")):
            e["GLS_SCATTER_SEED"] = str(seed)
        out = _rs.periods(w, e)
        for k in e:
            os.environ.pop(k, None)
    return {r: p for r, (_n, p) in out.items()}


def scattered(env):
    return bool(float(env.get("GLS_SCATTER", "0")) or float(env.get("GLS_SCATTER_REGION", "0")))


# --------------------------------------------------------------- compare

def stat_rows(s):
    """flatten a summarise() result into {stat name: value}."""
    r = {}
    for n, d in s["per_length"].items():
        for q in ("median", "p90", "p99", "max", "cover85") + (("min",) if n == 7 else ()):
            r[f"{n}.{q}"] = d[q]
        r[f"{n}.w90"] = d["p90"] / d["median"]
    for q in ("kfit", "slower", "k2", "d2_ps", "short_long"):
        if q in s:
            r[q] = s[q]
    return r


def aug_rows():
    r = {}
    for n, d in list(AUG["per_length"].items()) + [("all", AUG["all"])]:
        for q, v in d.items():
            r[f"{n}.{q}"] = v
    for n, v in AUG["cover85"].items():
        r[f"{n}.cover85"] = v
    for n, d in list(AUG["per_length"].items()) + [("all", AUG["all"])]:
        r[f"{n}.w90"] = d["p90"] / d["median"]
    r.update(kfit=AUG["kfit"], slower=AUG["slower"], k2=AUG["k2"], d2_ps=AUG["d2_ps"],
             short_long=AUG["per_length"][7]["median"] / AUG["per_length"][63]["median"])
    return r


# The graded statistics.  Each is one number the board gave; the model must put
# it inside the 2.5-97.5% spread of its own routes x draws.
#   all.median   the LEVEL (catches a wrong SDF column / band)
#   short_long   median(7) / median(63): the length dependence
#   slower       "N of 128 rings ran slower than the scaled model"
#   n.w90        p90 / median per length: the WIDTH, scale-free
# The per-length medians, p99 and max (one ring each at n = 32) are printed,
# not graded.  The set was fixed after the first single-route look and before
# the 8-route runs and the controls; the level was added after the controls
# showed the scale-free set cannot see a wrong column (fast_min, slow_max).
GRADED = ["all.median", "short_long", "slower", "7.w90", "15.w90", "31.w90", "63.w90"]
# The like-for-like denominator is P_pre: August's "predicted" came from the
# pre-lut-perm-sink binary.  P_np is reported beside it.
PRIMARY = "pre"


def spread(vals, lo=0.025, hi=0.975):
    v = sorted(vals)
    return v[int(lo * (len(v) - 1))], statistics.median(v), v[int(round(hi * (len(v) - 1)))]


def judge(samples, aug=None, graded=GRADED):
    """samples: [stat_rows(...)] over routes x draws.  -> {stat: (lo, med, hi,
    aug, inside)} and the count of graded stats inside [lo, hi]."""
    aug = aug or aug_rows()
    out = {}
    for k in aug:
        vals = [s[k] for s in samples if k in s]
        if not vals:
            continue
        lo, med, hi = spread(vals)
        out[k] = (lo, med, hi, aug[k], lo <= aug[k] <= hi)
    inside = [k for k in graded if k in out and out[k][4]]
    return out, inside


def run_env(routes, which, env, draws, denoms=("pre", "np")):
    """{denom: [stat_rows + route, seed]} over routes x draws (1 draw if unscattered)."""
    res = {}
    nd = draws if scattered(env) else 1
    for rt in routes:
        for seed in range(1, nd + 1):
            pm = model_periods(rt, which, env, seed)
            for dn in denoms:
                pred = rt.p_pre if dn == "pre" else rt.p_np
                s = summarise(pm, pred, rt.length)
                res.setdefault(dn, []).append({"route": str(rt.dir), "seed": seed, **stat_rows(s)})
    return res


def run(routes, configs, draws, denoms=("pre", "np")):
    res = {}
    for cname in configs:
        which, env = CONFIGS[cname]
        for dn, v in run_env(routes, which, env, draws, denoms).items():
            res[(cname, dn)] = v
    return res


def verdict(res):
    """res: run_env()'s result.  -> per-arm tables and graded counts; ok iff
    every graded statistic is inside on the PRIMARY arm."""
    arms = {}
    for dn, samples in res.items():
        tab, inside = judge(samples)
        arms[dn] = {"n_samples": len(samples), "inside": inside,
                    "outside": [k for k in GRADED if k not in inside],
                    "table": {k: [round(x, 4) if isinstance(x, float) else x for x in v]
                              for k, v in tab.items()}}
    ok = len(arms[PRIMARY]["inside"]) == len(GRADED) if PRIMARY in arms else None
    return {"arms": arms, "ok": ok}


def fmt(v):
    return f"{v:.0f}" if abs(v) >= 20 else f"{v:.3f}"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("routes", nargs="+")
    ap.add_argument("--draws", type=int, default=32)
    ap.add_argument("--configs", default="model", help="comma list of " + ",".join(CONFIGS))
    ap.add_argument("--denoms", default="pre,np")
    ap.add_argument("--xray-db", default=os.environ.get("XRAY_DB", "/root/dev2/lib/xray/prjxray-db/zynq7"))
    ap.add_argument("--json", type=Path)
    ap.add_argument("--tsv", type=Path, help="per-ring P_np, P_pre, unscattered P_model per route")
    a = ap.parse_args()
    grid = tile_grid(a.xray_db)
    routes = [Route(d, a.xray_db, grid) for d in a.routes]
    for rt in routes:
        print(f"route {rt.dir}: {len(rt.length)} rings; {rt.n_perm} of {rt.n_ic} in-ring "
              f"interconnect arcs reach a permuted LUT pin (P_pre replaces those)")
    if a.tsv:
        with open(a.tsv, "w") as f:
            f.write("route\tring\tlinks\tP_np_ps\tP_pre_ps\tP_band_ps\n")
            for rt in routes:
                pb = model_periods(rt, "xray", CONFIGS["no_scatter"][1], 1)
                for r in sorted(rt.length, key=lambda r: (rt.length[r], r)):
                    f.write(f"{rt.dir.name}\t{r}\t{rt.length[r]}\t{rt.p_np[r]}\t{rt.p_pre[r]}\t{pb[r]}\n")
    configs = a.configs.split(",")
    res = run(routes, configs, a.draws, a.denoms.split(","))
    report = {}
    for (cname, dn), samples in res.items():
        tab, inside = judge(samples)
        report[f"{cname}/{dn}"] = {"n_samples": len(samples), "inside": inside,
                                   "table": {k: list(v) for k, v in tab.items()}}
        print(f"\n== {cname} vs P_{dn}: {len(samples)} samples ({len(routes)} route(s)) ==")
        print(f"{'stat':>14} {'2.5%':>8} {'median':>8} {'97.5%':>8} {'August':>8}")
        for k, (lo, med, hi, au, ok) in tab.items():
            mark = ("in " if ok else "OUT") if k in GRADED else ("in" if ok else "out").lower()
            print(f"{k:>14} {fmt(lo):>8} {fmt(med):>8} {fmt(hi):>8} {fmt(au):>8}  {mark}")
        print(f"  graded statistics inside the model's 95% spread: {len(inside)} of {len(GRADED)}")
    if a.json:
        a.json.write_text(json.dumps(report, indent=1) + "\n")


if __name__ == "__main__":
    main()
