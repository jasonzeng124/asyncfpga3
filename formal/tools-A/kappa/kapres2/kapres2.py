#!/usr/bin/env python3
"""kapres2.py -- KapRes2 (2026-10-29): the A-kapres corner-cell sweep with xevents8 (Events8).

    python3 kapres2.py SEED [--init N] [--depth D] [--jobs J] [--tag TAG]

Per seed and each scatter kappa in KAPPAS (DESCENDING), covers the corner interval [0,1] by cells
[ca,cb] (start: N equal cells).  Per cell:
    cornerband2.py (BRKH-corrected fast, slow, ca, cb, kappa)       -> bands.json
    xaudit/events4/skel.py (net, bands)                             -> skel.json, skel_bands.json
    check_bands.check on both band files (lo <= hi, two naturals; Lean mirror BandCheck.jsonBandsOK;
      the Lean check itself is run on every kept skel band file by Wip/KapRes2/BandCheckRun.lean)
    xaudit/events8/cert8.py (UNTRUSTED certificate)                 -> cert.json
    xe8.sh = committed Events8Main (xevents8), native build or lean --run on the private overlay
XA_ARB=old is forced: the virtual arbiter core that Events8 (HARB7) and every committed xevents8 run
used (events4/model.py at 591cd51 defaults to the E8ArbFix "fix" core, made for Events9Arb).  $XA
selects the xaudit tool tree (run.sh: a snapshot of the committed events4/6/7/8 python at 591cd51).
A run is accepted only if its header says Design.WF true, Recog6 node failures 0, Net4.OK7 true and
log accepted by runLog: true (else the script stops).
Refinement rule (A-kapres sec. 2): a cell with a TIMING residual item has its two end corners run
as point cells; it is bisected (down to width 1/(N*2^D)) only if one of its timing items passes at
both end corners; an item failing at an end corner fails AT that corner and no refinement can
discharge it.  Timing items: Back / Line (margin m) and Guard (margin = min of BACK-G, ENTRY,
EXIT1, EXIT2).  Any other residual line is reported as structural.
DEPTHS="0.12:0" overrides D per kappa (finest width 1/(N*2^depth) at that kappa).
implied_clean: a cell inside a cell that had NO residual item at a kappa' >= kappa is not re-run
(CornerCell.cellLo_anti / cellHi_mono: its band file contains ours arc by arc).
Output: runs<TAG>/<seed>/k<kappa>_<ca>_<cb>.txt (xevents8 stdout) and runs<TAG>/<seed>/summary.json.
Inputs: $KR/in<TAG>/<seed>/{net,slow.bands}.json and $KR/fix<TAG>/<seed>/fast.bands.json (run.sh).
"""
import concurrent.futures as cf
import json
import os
import re
import shutil
import subprocess
import sys
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
XA = os.environ.get("XA", os.path.join(HERE, "..", "..", "xaudit"))
KR = os.environ.get("KR", "/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/KapRes2")
RES = re.compile(r"^\s+RESIDUAL (\S+) (.*?): (margin (-?\d+).*|BACK-G (-?\d+) ENTRY (-?\d+) EXIT1 (-?\d+) EXIT2 (-?\d+).*|.*)$")
KAPPAS = ["0.12", "0.10", "0.08", "0.06", "0.04", "0.02", "0"]
sys.path.insert(0, HERE)
from check_bands import check  # noqa: E402

TAG = ""


def fs(q):
    return "%d-%d" % (q.numerator, q.denominator) if q.denominator != 1 else str(q.numerator)


def rd(s):
    return Q(*map(int, s.split("-"))) if "-" in s else Q(int(s))


def run_cell(seed, kappa, ca, cb):
    tag = "k%s_%s_%s" % (kappa, fs(ca), fs(cb))
    outd = os.path.join(HERE, "runs" + TAG, seed)
    os.makedirs(outd, exist_ok=True)
    out = os.path.join(outd, tag + ".txt")
    if not (os.path.exists(out) and "VERDICT" in open(out).read()):
        w = os.path.join(KR, "work" + TAG, seed, tag)
        os.makedirs(w, exist_ok=True)
        env = dict(os.environ, PYTHONHASHSEED="0", PYTHONDONTWRITEBYTECODE="1", XA_ARB="old")
        py = lambda *a, **kw: subprocess.run(["python3"] + list(a), check=True, env=env, **kw)
        py(os.path.join(HERE, "cornerband2.py"), "%s/fix%s/%s/fast.bands.json" % (KR, TAG, seed),
           "%s/in%s/%s/slow.bands.json" % (KR, TAG, seed), str(ca), str(cb), kappa, w + "/bands.json")
        py(os.path.join(XA, "events4", "skel.py"), "%s/in%s/%s/net.json" % (KR, TAG, seed), w + "/bands.json",
           w + "/skel.json", w + "/skel_bands.json", stdout=subprocess.DEVNULL, cwd=os.path.join(XA, "events4"))
        for bp in (w + "/bands.json", w + "/skel_bands.json"):
            if check(bp):
                sys.exit("invalid band in %s" % bp)
        with open(w + "/cert.txt", "w") as f:
            py(os.path.join(XA, "events8", "cert8.py"), w + "/skel.json", w + "/skel_bands.json",
               w + "/cert.json", stdout=f, stderr=subprocess.STDOUT, cwd=os.path.join(XA, "events8"))
        for attempt in range(3):     # a run that prints no VERDICT (seen under load) is retried
            with open(out + ".part", "w") as f:
                rc = subprocess.run([os.path.join(HERE, "xe8.sh"), w + "/skel.json", w + "/skel_bands.json",
                                     w + "/cert.json"], stdout=f, stderr=subprocess.DEVNULL).returncode
            txt = open(out + ".part").read()
            if "VERDICT" in txt:
                if not ("Design.WF true" in txt and "Recog6 node failures 0" in txt and "Net4.OK7 true" in txt
                        and "accepted by runLog: true" in txt):
                    sys.exit("%s %s: run not recognised / log not accepted" % (seed, tag))
                if "nodes (36 virtual, H_ARB)" not in txt:
                    sys.exit("%s %s: unexpected virtual-node count (arbiter core?)" % (seed, tag))
                break
            with open(os.path.join(KR, "failed%s.log" % TAG), "a") as f:
                f.write("%s %s attempt %d rc %d: %r\n" % (seed, tag, attempt, rc, txt[-300:]))
        os.replace(out + ".part", out)
        # keep the skeleton band file (for the Lean BandCheck run), drop the rest
        kb = os.path.join(KR, "skelbands" + TAG, seed)
        os.makedirs(kb, exist_ok=True)
        shutil.copy(w + "/skel_bands.json", os.path.join(kb, tag + ".json"))
        shutil.rmtree(w, ignore_errors=True)
    return parse(out)


def parse(path):
    timing, struct, verdict, head = {}, [], None, []
    for ln in open(path):
        m = RES.match(ln)
        if m:
            key = "%s %s" % (m.group(1), m.group(2))
            if m.group(4) is not None:
                timing[key] = int(m.group(4))
            elif m.group(5) is not None:
                timing[key] = min(int(m.group(i)) for i in (5, 6, 7, 8))
            else:
                struct.append(key)
        elif ln.startswith("VERDICT"):
            verdict = ln.strip()
        elif ln.startswith("[xevents8]"):
            head.append(ln.strip())
    return {"timing": timing, "struct": struct, "verdict": verdict, "head": head}


def implied_clean(seed, kappa, ca, cb):
    d = os.path.join(HERE, "runs" + TAG, seed)
    for fn in os.listdir(d) if os.path.isdir(d) else []:
        m = re.match(r"k([\d.]+)_([\d-]+)_([\d-]+)\.txt$", fn)
        if not m:
            continue
        k2, a2, b2 = Q(m.group(1)), rd(m.group(2)), rd(m.group(3))
        if k2 >= Q(kappa) and a2 <= ca and cb <= b2:
            r = parse(os.path.join(d, fn))
            if r["verdict"] and not r["timing"] and not r["struct"]:
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
    global TAG
    seed = sys.argv[1]
    args = sys.argv[2:]
    opt = lambda k, d: int(args[args.index(k) + 1]) if k in args else d
    N, D, J = opt("--init", 8), opt("--depth", 2), opt("--jobs", 2)
    if "--tag" in args:
        TAG = args[args.index("--tag") + 1]
    kappas = os.environ.get("KAPPAS", " ".join(KAPPAS)).split()
    cover = [(Q(i, N), Q(i + 1, N)) for i in range(N)]
    os.makedirs(os.path.join(HERE, "runs" + TAG, seed), exist_ok=True)
    allsum = {"seed": seed, "init": N, "depth": D, "checker": "xevents8 (Events8Main)", "kappas": {}}
    with cf.ThreadPoolExecutor(J) as ex:
        for kappa in kappas:
            dk = dict(x.split(":") for x in os.environ.get("DEPTHS", "").split() if ":" in x)
            minw = Q(1, N * 2 ** int(dk.get(kappa, D)))
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
                    if r["timing"] and cb - ca > minw and any(
                            k not in points[ca]["timing"] and k not in points[cb]["timing"] for k in r["timing"]):
                        mid = (ca + cb) / 2
                        todo += [(ca, mid), (mid, cb)]
                    else:
                        leaves.append(((ca, cb), r))
            leaves.sort()
            pts = sorted({x for (ca, cb), r in leaves if r["timing"] for x in (ca, cb)} - set(points))
            for (x, _), r in ex.map(lambda x: cell(seed, kappa, (x, x)), pts):
                points[x] = r
            cover = [c for c, _ in leaves]
            bad = {}
            for (ca, cb), r in leaves:
                for k, m in r["timing"].items():
                    bad.setdefault(k, []).append([str(ca), str(cb), m])
            ptbad = {}
            for x, r in sorted(points.items()):
                for k, m in r["timing"].items():
                    ptbad.setdefault(k, []).append([str(x), m])
            allsum["kappas"][kappa] = {"minw": str(minw),
                "cover": [{"ca": str(ca), "cb": str(cb), "by": r["by"], "timing": r["timing"],
                           "struct": r["struct"], "verdict": r["verdict"]} for (ca, cb), r in leaves],
                "points": {str(x): {"by": r["by"], "timing": r["timing"]} for x, r in sorted(points.items())},
                "items": bad, "point_fail": ptbad,
                "struct_union": sorted({s for _, r in leaves for s in r["struct"]})}
            print("%s kappa %s: %d leaf cells (%d run here), %d with timing items; items %s; failing at a point corner %s" % (
                seed, kappa, len(leaves), sum(1 for _, r in leaves if r["by"].startswith("k%s_" % kappa)),
                sum(1 for _, r in leaves if r["timing"]),
                {k: min(x[2] for x in v) for k, v in bad.items()},
                {k: [x[0] for x in v] for k, v in ptbad.items()}), flush=True)
            json.dump(allsum, open(os.path.join(HERE, "runs" + TAG, seed, "summary.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
