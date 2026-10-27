#!/usr/bin/env python3
"""Probe C-10n: per-kernel tables from check.sh's outputs (UNTRUSTED reporting).
    python3 summarize.py KERNEL SEED...
-> results/KERNEL/rows.tsv      every compared row (seed, rule, flavour, row, project, tcheck)
   results/KERNEL/agree.tsv     per rule/flavour and seed: agree / disagree / not comparable
   results/KERNEL/disagree.tsv  every disagreement, classified:
        band-only      project PASS, tcheck FAIL at fastG/slowG, but the unguarded prjxray
                       fast AND slow corners pass (the 0.772/1.155 band on prjxray numbers)
        corner-fail    project PASS, an UNGUARDED prjxray corner fails even at a fixed point, no
                       fallback, no constant source (candidate real failure: read diag.py)
        frontend-gap(const)    rule A row whose data peak is a constant tie-off driver's route
                       (tighten.cell_boundary keeps $PACKER_GND/VCC_DRV: a false path, which
                       tcheck's rule A mirrors; constsrc.py)
        frontend-gap(fallback) the deciding instance has fallback arcs (SDF band in place of
                       prjxray numbers, so a prjxray corner is mixed with nextpnr's slow max)
        spread-only    no fallback, but every fixed point (pointcheck.py: all arcs at fast_min,
                       fast_max, slow_min or slow_max) passes: the failure needs request arcs at
                       the low end and data arcs at the high end of ONE corner (no correlation)
        project-only   project FAIL, tcheck PASS (tcheck's prjxray numbers are kinder)
   results/KERNEL/routes.tsv    per seed: flow.sh exit, gate lines, project violation counts,
                                extract/tcheck summary
   results/KERNEL/summary.txt   the tables above, printed
tcheck verdict = PASS at fastG and slowG (C-10e convention: one prjxray corner at a time,
times the project's own guard band)."""
import pathlib, re, sys
from collections import defaultdict
H = pathlib.Path(__file__).resolve().parent
import os
k, seeds = sys.argv[1], sys.argv[2:]
TAG = os.environ.get("KCHECK_TAG", "")
B, R = H / "build" / k, H / "results" / (k + (f"_{TAG}" if TAG else ""))
CK = "check" + (f"_{TAG}" if TAG else "")
R.mkdir(parents=True, exist_ok=True)
V = ["sdf", "sdfband", "fast", "slow", "fastG", "slowG"]
rows = []
for s in seeds:
    O = B / f"s{s}" / CK
    for fn, tag in (("compare_hi.tsv", None), ("compare_hc.tsv", "Hc"), ("compare2.tsv", "2")):
        f = O / fn
        if not f.exists():
            continue
        ls = [l.rstrip("\n").split("\t") for l in open(f)][1:]
        for r in ls:
            if not r or not r[0]:
                continue
            if tag == "2":
                rule, key, fl, praw, pg, pv = r[:6]; tc = r[6:12]; cv, ag = r[12], r[13]
                note = r[14] if len(r) > 14 else ""
            else:
                rule, key, praw, _g, pg, pv = r[:6]; tc = r[6:12]; cv, ag = r[12], r[13]
                fl = tag or rule; note = "fallback=" + (r[14] if len(r) > 14 else "")
                if tag == "Hc" and rule != "H":
                    continue
            rows.append(dict(seed=s, rule=rule, fl=fl, key=key, praw=praw, pg=pg, pv=pv,
                             tc=dict(zip(V, tc)), cv=cv, ag=ag, note=note))


def num(x):
    try:
        return int(x)
    except ValueError:
        return None


# pointcheck.py (fixed-point margins) and check.sh's constsrc.tsv (rule-A peak taken from a
# constant tie-off driver), when present, refine the classes
PC = {}
if (R / "pointcheck.tsv").exists():
    for l in list(open(R / "pointcheck.tsv"))[1:]:
        f = l.rstrip("\n").split("\t")
        if len(f) >= 7 and f[3] != "-":
            PC[(f[0], f[1], f[2])] = [num(x) for x in f[3:7]]
CONST = set()
for s in seeds:
    f = B / f"s{s}" / CK / "constsrc.tsv"
    if f.exists():
        for l in list(open(f))[1:]:
            x = l.rstrip("\n").split("\t")
            if len(x) >= 7 and "PACKER" in x[6]:
                CONST.add((s, x[0]))


def klass(r):
    """band-only / frontend-gap / spread-only / corner-fail / project-only (see the docstring)"""
    t = r["tc"]
    if r["pv"] == "FAIL" and r["cv"] == "PASS":
        return "project-only"
    f, sl = num(t["fast"]), num(t["slow"])
    if f is not None and sl is not None and f >= 0 and sl >= 0:
        return "band-only"
    m = re.search(r"fallback=([^ ]*)", r["note"])
    fbs = [x for x in (m.group(1).split(",") if m else []) if x]
    if r["rule"] == "A" and (r["seed"], r["key"]) in CONST:
        return "frontend-gap(const)"
    if any(re.match(r"^[1-9]", x) for x in fbs):
        return "frontend-gap(fallback)"
    pc = PC.get((r["seed"], r["fl"], r["key"]))
    if pc and all(x is not None and x >= 0 for x in pc):
        return "spread-only"
    return "corner-fail"


with open(R / "rows.tsv", "w") as o:
    o.write("seed\trule\tflavour\trow\tproj_raw\tproj_guarded\tproj\t" + "\t".join(f"tc_{v}" for v in V)
            + "\ttcheck\tagree\tnote\n")
    for r in rows:
        o.write("\t".join([r["seed"], r["rule"], r["fl"], r["key"], r["praw"], r["pg"], r["pv"],
                           *[r["tc"][v] for v in V], r["cv"], r["ag"], r["note"]]) + "\n")
agree = defaultdict(lambda: defaultdict(int))
for r in rows:
    agree[(r["rule"], r["fl"])][(r["seed"], r["ag"])] += 1
with open(R / "agree.tsv", "w") as o:
    o.write("rule\tflavour\t" + "\t".join(f"s{s} agree/NO/-" for s in seeds) + "\ttotal agree/comparable\n")
    for (rule, fl), d in sorted(agree.items()):
        tot = sum(d[(s, "yes")] for s in seeds); n = tot + sum(d[(s, "NO")] for s in seeds)
        o.write(f"{rule}\t{fl}\t" + "\t".join(f"{d[(s,'yes')]}/{d[(s,'NO')]}/{d[(s,'-')]}" for s in seeds)
                + f"\t{tot}/{n}\n")
with open(R / "disagree.tsv", "w") as o:
    o.write("seed\trule\tflavour\trow\tproj_raw\tproj_guarded\tproj\t" + "\t".join(f"tc_{v}" for v in V)
            + "\ttcheck\tclass\tnote\n")
    for r in rows:
        if r["ag"] == "NO":
            o.write("\t".join([r["seed"], r["rule"], r["fl"], r["key"], r["praw"], r["pg"], r["pv"],
                               *[r["tc"][v] for v in V], r["cv"], klass(r), r["note"]]) + "\n")


def count(path, pat, sections=None):
    """lines matching pat; with `sections`, only inside tighten.py's lettered sections listed
    (rule D is a screen, not one of the compared rules)"""
    try:
        n, sec = 0, None
        for l in open(path):
            m = re.match(r"^([A-Z])\. ", l)
            if m:
                sec = m.group(1)
            if (sections is None or (sec is not None and sec in sections)) and re.search(pat, l):
                n += 1
        return n
    except OSError:
        return "-"


with open(R / "routes.tsv", "w") as o:
    o.write("seed\tflow_rc\tflow_gate_lines\ttighten_rc\ttighten_AHIF_VIOLATION\tskew_VIOLATED\tarbfork_VIOLATED"
            "\textract\ttcheck\tsdf_sha\n")
    for s in seeds:
        O0 = B / f"s{s}"; O = O0 / CK
        rd0 = lambda n: (O0 / n).read_text().strip() if (O0 / n).exists() else "-"   # noqa: E731
        rd = lambda n: (O / n).read_text().strip() if (O / n).exists() else "-"   # noqa: E731
        gates = "; ".join(l.strip() for l in open(O0 / "flow.log")
                          if re.search(r"FAIL|VIOLAT|refus|ABORT|DROPPED", l))[:300] if (O0 / "flow.log").exists() else "-"
        ex = [l.strip() for l in open(O / "extract.log") if l.startswith("extract:")] if (O / "extract.log").exists() else []
        te = rd("t.err").splitlines()[-1:] if (O / "t.err").exists() else []
        sha = rd0("sha.txt").split()[0][:16] if (O0 / "sha.txt").exists() else "NO ROUTE"
        o.write("\t".join(map(str, (s, rd0("flow.rc"), gates or "clean", rd("tighten.rc"),
                                    count(O / "tighten.log", "VIOLATION", "AHIF"), count(O / "skew_v.log", r"^\s+VIOLATED"),
                                    count(O / "arbfork.log", r"^\s+VIOLATED"), ex[-1] if ex else "-",
                                    te[0] if te else "-", sha))) + "\n")
txt = ""
for n in ("routes", "agree", "disagree"):
    txt += f"== {n}\n" + (R / f"{n}.tsv").read_text()
cls = defaultdict(int)
for r in rows:
    if r["ag"] == "NO":
        cls[(r["rule"], r["fl"], klass(r))] += 1
txt += "== disagreement classes (rule flavour class count)\n" + "".join(
    f"{a}\t{b}\t{c}\t{n}\n" for (a, b, c), n in sorted(cls.items()))
(R / "summary.txt").write_text(txt)
print(txt)
