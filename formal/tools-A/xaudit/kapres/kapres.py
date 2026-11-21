#!/usr/bin/env python3
"""kapres.py -- corner-model sweep of xevents5 (A-events6's checker) over shared-corner cells.

    python3 kapres.py SEED [--init N] [--depth D] [--jobs J]

For one seed and each scatter kappa in KAPPAS (descending), covers the corner interval [0,1] by cells [ca,cb]
(start: N equal cells; a cell whose run has a TIMING residual item -- "margin m" -- has its two
end corners run as point cells; it is bisected, down to width 1/(N*2^D), only if one of its timing
items passes at both end corners).  Each cell run is
    cornerband.py (fast, slow, ca, cb, kappa) -> events4/skel.py -> events6/cert6.py (untrusted)
    -> xe5.sh (xevents5 = committed Events5Main.lean, lean --run, through slot.sh)
At every leaf cell that still has timing items, the two point corners [ca,ca], [cb,cb] are
also run (a point run that fails shows the item fails AT that corner, not only on the cell).
Kappas are taken in DESCENDING order and the cover of one kappa is the start of the next: a cell
that is clean (no timing item) at kappa' is clean at every kappa <= kappa' (its band file contains
ours arc by arc), so it is not re-run (implied_clean; the summary names the run that covers it).
Output: runs/<seed>/k<kappa>_<ca>_<cb>.txt (xevents5 stdout; a<b written a-b for fractions) and
runs/<seed>/summary.json: per kappa the leaf cover, the timing items per leaf, and the point runs.
Inputs: /tmp/kapres/in/<seed>/{net,fast.bands,slow.bands}.json (see run.sh).
"""
import concurrent.futures as cf
import json
import os
import re
import subprocess
import sys
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
IN = "/tmp/kapres/in"
WORK = "/tmp/kapres/work"
RES = re.compile(r"^\s+RESIDUAL (Back|Line|Excl) (.*?): (margin (-?\d+).*|no certificate.*)$")


def fs(q):
    return "%d-%d" % (q.numerator, q.denominator) if q.denominator != 1 else str(q.numerator)


def run_cell(seed, kappa, ca, cb):
    tag = "k%s_%s_%s" % (kappa, fs(ca), fs(cb))
    outd = os.path.join(HERE, "runs", seed)
    os.makedirs(outd, exist_ok=True)
    out = os.path.join(outd, tag + ".txt")
    if not (os.path.exists(out) and "VERDICT" in open(out).read()):
        w = os.path.join(WORK, seed, tag)
        os.makedirs(w, exist_ok=True)
        env = dict(os.environ, PYTHONHASHSEED="0", PYTHONDONTWRITEBYTECODE="1")
        py = lambda *a, **kw: subprocess.run(["python3"] + list(a), check=True, env=env, **kw)
        py(os.path.join(HERE, "cornerband.py"), "%s/%s/fast.bands.json" % (IN, seed),
           "%s/%s/slow.bands.json" % (IN, seed), str(ca), str(cb), kappa, w + "/bands.json")
        py(os.path.join(HERE, "..", "events4", "skel.py"), "%s/%s/net.json" % (IN, seed), w + "/bands.json",
           w + "/skel.json", w + "/skel_bands.json", stdout=subprocess.DEVNULL)
        with open(w + "/cert.txt", "w") as f:
            py(os.path.join(HERE, "..", "events6", "cert6.py"), w + "/skel.json", w + "/skel_bands.json",
               w + "/cert.json", stdout=f, stderr=subprocess.STDOUT)
        for attempt in range(3):     # a run that prints no VERDICT (seen under load) is retried
            with open(out + ".part", "w") as f:
                rc = subprocess.run([os.path.join(HERE, "xe5.sh"), w + "/skel.json", w + "/skel_bands.json",
                                     w + "/cert.json"], stdout=f, stderr=subprocess.STDOUT).returncode
            txt = open(out + ".part").read()
            if "VERDICT" in txt:
                break
            with open(os.path.join(WORK, "failed.log"), "a") as f:
                f.write("%s %s attempt %d rc %d: %r\n" % (seed, tag, attempt, rc, txt[-300:]))
        os.replace(out + ".part", out)
        for fn in ("bands.json", "skel_bands.json", "cert.json"):
            try:
                os.remove(os.path.join(w, fn))
            except OSError:
                pass
    return parse(out)


def parse(path):
    timing, struct, verdict, head = {}, [], None, []
    for ln in open(path):
        m = RES.match(ln)
        if m:
            key = "%s %s" % (m.group(1), m.group(2))
            if m.group(4) is not None:
                timing[key] = int(m.group(4))
            else:
                struct.append(key)
        elif ln.startswith("VERDICT"):
            verdict = ln.strip()
        elif ln.startswith("[xevents5]"):
            head.append(ln.strip())
    return {"timing": timing, "struct": struct, "verdict": verdict, "head": head}


KAPPAS = ["0.10", "0.0906", "0.05", "0.02", "0"]


def implied_clean(seed, kappa, ca, cb):
    """A run at (kappa', [ca',cb']) with kappa' >= kappa and [ca',cb'] containing [ca,cb] and no timing
    item: its bands contain ours arc by arc (cornerband is monotone in kappa and in the cell), so
    the checker's verdict for it covers our behaviours with the same (structural) residual set."""
    d = os.path.join(HERE, "runs", seed)
    for fn in os.listdir(d) if os.path.isdir(d) else []:
        m = re.match(r"k([\d.]+)_([\d-]+)_([\d-]+)\.txt$", fn)
        if not m:
            continue
        rd = lambda s: Q(*map(int, s.split("-"))) if "-" in s else Q(int(s))
        k2, a2, b2 = Q(m.group(1)), rd(m.group(2)), rd(m.group(3))
        if k2 >= Q(kappa) and a2 <= ca and cb <= b2:
            r = parse(os.path.join(d, fn))
            if r["verdict"] and not r["timing"]:
                return fn, r
    return None


def cell(seed, kappa, c):
    ca, cb = c
    imp = implied_clean(seed, kappa, ca, cb)
    if imp:
        fn, r = imp
        return c, dict(r, by=fn)
    r = run_cell(seed, kappa, ca, cb)
    return c, dict(r, by="k%s_%s_%s.txt" % (kappa, fs(ca), fs(cb)))


def main():
    seed = sys.argv[1]
    args = sys.argv[2:]
    opt = lambda k, d: int(args[args.index(k) + 1]) if k in args else d
    N, D, J = opt("--init", 8), opt("--depth", 2), opt("--jobs", 2)
    minw = Q(1, N * 2 ** D)
    cover = [(Q(i, N), Q(i + 1, N)) for i in range(N)]
    allsum = {"seed": seed, "init": N, "depth": D, "kappas": {}}
    with cf.ThreadPoolExecutor(J) as ex:
        for kappa in KAPPAS:
            todo, leaves, points = list(cover), [], {}
            while todo:
                res = list(ex.map(lambda c: cell(seed, kappa, c), todo))
                todo = []
                dirty = [(c, r) for c, r in res if r["timing"] and c[1] - c[0] > minw]
                ends = sorted({x for c, _ in dirty for x in c} - set(points))
                for (x, _), r in ex.map(lambda x: cell(seed, kappa, (x, x)), ends):
                    points[x] = r
                for (ca, cb), r in res:
                    if r["verdict"] is None:
                        sys.exit("no verdict for %s %s %s-%s" % (seed, kappa, ca, cb))
                    # bisect only if some timing item of the cell passes at BOTH end corners (it may
                    # be an artefact of the cell width); an item failing at an end corner fails at
                    # that corner itself, and no refinement of the cover can discharge it at this kappa
                    if r["timing"] and cb - ca > minw and any(
                            k not in points[ca]["timing"] and k not in points[cb]["timing"] for k in r["timing"]):
                        mid = (ca + cb) / 2
                        todo += [(ca, mid), (mid, cb)]
                    else:
                        leaves.append(((ca, cb), r))
            leaves.sort()
            pts = sorted({x for (ca, cb), r in leaves if r["timing"] for x in (ca, cb)})
            for (x, _), r in ex.map(lambda x: cell(seed, kappa, (x, x)), pts):
                points[x] = r
            cover = [c for c, _ in leaves]
            bad = {}
            for (ca, cb), r in leaves:
                for k, m in r["timing"].items():
                    bad.setdefault(k, []).append([str(ca), str(cb), m])
            ptbad = {}
            for x, r in points.items():
                for k, m in r["timing"].items():
                    ptbad.setdefault(k, []).append([str(x), m])
            allsum["kappas"][kappa] = {
                "cover": [{"ca": str(ca), "cb": str(cb), "by": r["by"], "timing": r["timing"],
                           "struct": len(r["struct"])} for (ca, cb), r in leaves],
                "items": bad, "point_fail": ptbad,
                "struct_union": sorted({s for _, r in leaves for s in r["struct"]})}
            print("%s kappa %s: %d leaf cells (%d run here), %d with timing items; items %s; failing at a point corner %s" % (
                seed, kappa, len(leaves), sum(1 for _, r in leaves if r["by"].startswith("k%s_" % kappa)),
                sum(1 for _, r in leaves if r["timing"]),
                {k: min(x[2] for x in v) for k, v in bad.items()},
                {k: [x[0] for x in v] for k, v in ptbad.items()}), flush=True)
            json.dump(allsum, open(os.path.join(HERE, "runs", seed, "summary.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
