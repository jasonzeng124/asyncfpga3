#!/usr/bin/env python3
"""C-10h: per-rule tables over seeds from run4.sh's outputs ->
results/agree3.tsv, disagree3.tsv, unchecked3.tsv (W, R, Rc), cert3.tsv (old chain vs
cert per rule), fallback3.tsv (fallback census).   python3 summarize3.py [SEED...]"""
import json, pathlib, re, subprocess, sys
from collections import defaultdict
H = pathlib.Path(__file__).resolve().parent
seeds = sys.argv[1:] or ["d", "2", "3", "4"]
V = ["sdf", "sdfband", "fast", "slow", "fastG", "slowG"]
R = H / "results"
agree, dis = defaultdict(lambda: defaultdict(int)), []
for s in seeds:
    f = H / f"build/compare5_{s}.tsv"
    if f.exists():
        for r in [l.rstrip("\n").split("\t") for l in open(f)][1:]:
            rule, key, fl, praw, pg, pv = r[:6]
            tc = dict(zip(V, r[6:12])); ag = r[13]
            agree[(rule, fl)][(s, ag)] += 1
            if ag == "NO":
                num = lambda v: int(tc[v]) if tc[v] not in ("-", "") else None  # noqa: E731
                cls = ("unguarded corner fails" if (num("fast") or 0) < 0 or (num("slow") or 0) < 0
                       else "band on prjxray corner only")
                dis.append((s, rule, fl, key, praw, pg, *[tc[v] for v in V], cls, r[14] if len(r) > 14 else ""))
    for tag, name in (("hi", None), ("hc", "Hc")):
        f = H / f"build/compare5{tag}_{s}.tsv"
        if f.exists():
            for l in list(open(f))[1:]:
                r = l.rstrip("\n").split("\t")
                if name and r[0] != "H":
                    continue
                agree[(r[0], name or r[0])][(s, r[13])] += 1
                if r[13] == "NO":
                    tc = r[6:12]
                    cls = ("unguarded corner fails" if any(x not in ("-", "") and int(x) < 0 for x in tc[2:4])
                           else "band on prjxray corner only")
                    dis.append((s, r[0], name or r[0], r[1], r[2], r[4], *tc, cls, f"fallback={r[14]}"))
with open(R / "agree3.tsv", "w") as o:
    o.write("rule\tflavour\t" + "\t".join(f"{s}:agree/NO/-" for s in seeds) + "\ttotal agree\n")
    for (rule, fl), d in sorted(agree.items()):
        tot = sum(d[(s, 'yes')] for s in seeds); n = sum(d[(s, 'yes')] + d[(s, 'NO')] for s in seeds)
        o.write(f"{rule}\t{fl}\t" + "\t".join(f"{d[(s,'yes')]}/{d[(s,'NO')]}/{d[(s,'-')]}" for s in seeds)
                + f"\t{tot}/{n}\n")
with open(R / "disagree3.tsv", "w") as o:
    o.write("seed\trule\tflavour\trow\tproj_raw\tproj_guarded\t" + "\t".join(f"tc_{v}" for v in V) + "\tclass\tnote\n")
    for x in dis:
        o.write("\t".join(map(str, x)) + "\n")
# W, R, Rc
with open(R / "unchecked3.tsv", "w") as o:
    o.write("seed\trule\trows\tvacuous(no path)\t" + "\t".join(f"min_{v}" for v in V)
            + "\tFAIL_fastG|slowG\tslowG<100ps\tfastG<100ps\tworst_slowG_row\n")
    for s in seeds:
        f = H / f"build/t5_{s}.out"
        if not f.exists():
            continue
        m = defaultdict(dict)
        for l in open(f):
            r = l.rstrip("\n").split("\t")
            lab = r[0].split(); rule, var = lab[0], lab[-2]
            if rule not in ("W", "R", "Rc"):
                continue
            key = " ".join(lab[1:-2])
            m[(rule, key)][var] = int(r[2]) if r[2] != "none" else -10**9
        for rule in ("W", "R", "Rc"):
            ks = [k for k in m if k[0] == rule]
            vac = [k for k in ks if m[k]["sdf"] > 10**11]
            ks = [k for k in ks if k not in vac]
            if not ks:
                continue
            mins = {v: min(m[k].get(v, 10**9) for k in ks) for v in V}
            fails = sum(1 for k in ks if min(m[k]["fastG"], m[k]["slowG"]) < 0)
            thin_s = sum(1 for k in ks if m[k]["slowG"] < 100)
            thin_f = sum(1 for k in ks if m[k]["fastG"] < 100)
            worst = min(ks, key=lambda k: m[k]["slowG"])[1]
            o.write("\t".join(map(str, (s, rule, len(ks), len(vac), *[mins[v] for v in V], fails,
                                         thin_s, thin_f, worst))) + "\n")
with open(R / "cert3.tsv", "w") as o:
    o.write("seed\tcmpcert summary (per rule: variant-rows equal / cert lower / no old instance / verdict flips)\n")
    for s in seeds:
        f = H / f"build/cmpcert5_{s}.log"
        if f.exists():
            for l in open(f):
                o.write(f"{s}\t{l}")
with open(R / "fallback3.tsv", "w") as o:
    o.write("seed\tsummary\tkinds (top)\n")
    for s in seeds:
        lg, js = H / f"build/extract5_{s}.log", H / f"build/obl5_{s}.json"
        if lg.exists() and js.exists():
            last = [l for l in open(lg) if l.startswith("extract:")][-1].strip()
            k = json.load(open(js))["fallback_kinds"]
            o.write(f"{s}\t{last}\t" + "; ".join(f"{n} {x}" for x, n in list(k.items())[:12]) + "\n")
for n in ("agree3", "disagree3", "unchecked3", "cert3", "fallback3"):
    print(f"== {n}"); print(open(R / f"{n}.tsv").read())
