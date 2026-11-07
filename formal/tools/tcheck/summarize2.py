#!/usr/bin/env python3
"""C-10g: per-rule agreement tables over seeds -> results/agree2.tsv, results/disagree2.tsv,
results/unchecked2.tsv (W, R).   python3 summarize2.py [SEED...]"""
import pathlib, sys
from collections import defaultdict
H = pathlib.Path(__file__).resolve().parent
seeds = sys.argv[1:] or ["d", "2", "3", "4"]
V = ["sdf", "sdfband", "fast", "slow", "fastG", "slowG"]
agree, dis = defaultdict(lambda: defaultdict(int)), []
for s in seeds:
    f = H / f"build/compare2_{s}.tsv"
    if not f.exists():
        continue
    rows = [l.rstrip("\n").split("\t") for l in open(f)][1:]
    for r in rows:
        rule, key, fl, praw, pg, pv = r[:6]
        tc = dict(zip(V, r[6:12])); cv, ag = r[12], r[13]
        agree[(rule, fl)][(s, ag)] += 1
        if ag == "NO":
            num = lambda v: int(tc[v]) if tc[v] not in ("-", "") else None  # noqa: E731
            cls = ("unguarded corner fails" if (num("fast") or 0) < 0 or (num("slow") or 0) < 0
                   else "band on prjxray corner only")
            dis.append((s, rule, fl, key, praw, pg, *[tc[v] for v in V], cls, r[14] if len(r) > 14 else ""))
    # H/I from compare2hi
    f = H / f"build/compare2hi_{s}.tsv"
    if f.exists():
        for l in list(open(f))[1:]:
            r = l.rstrip("\n").split("\t")
            agree[(r[0], r[0])][(s, r[13])] += 1
o = open(H / "results/agree2.tsv", "w")
o.write("rule\tflavour\t" + "\t".join(f"{s}:agree/NO/-" for s in seeds) + "\n")
for (rule, fl), d in sorted(agree.items()):
    o.write(f"{rule}\t{fl}\t" + "\t".join(f"{d[(s,'yes')]}/{d[(s,'NO')]}/{d[(s,'-')]}" for s in seeds) + "\n")
o.close()
o = open(H / "results/disagree2.tsv", "w")
o.write("seed\trule\tflavour\trow\tproj_raw\tproj_guarded\t" + "\t".join(f"tc_{v}" for v in V) + "\tclass\tnote\n")
for x in dis:
    o.write("\t".join(map(str, x)) + "\n")
o.close()
# W, R
o = open(H / "results/unchecked2.tsv", "w")
o.write("seed\trule\trows\t" + "\t".join(f"min_{v}" for v in V) + "\tFAIL_fastG|slowG\tslowG<100ps\tfastG<100ps\tworst_slowG_row\n")
for s in seeds:
    f = H / f"build/t3_{s}.out"
    if not f.exists():
        continue
    m = defaultdict(dict)
    for l in open(f):
        r = l.rstrip("\n").split("\t")
        lab = r[0].split(); rule, var = lab[0], lab[-2]
        key = " ".join(lab[1:-2])
        m[(rule, key)][var] = int(r[2]) if r[2] != "none" else -10**9
    for rule in ("W", "R"):
        ks = [k for k in m if k[0] == rule]
        if not ks:
            continue
        mins = {v: min(m[k].get(v, 10**9) for k in ks) for v in V}
        fails = sum(1 for k in ks if min(m[k]["fastG"], m[k]["slowG"]) < 0)
        thin_s = sum(1 for k in ks if m[k]["slowG"] < 100)
        thin_f = sum(1 for k in ks if m[k]["fastG"] < 100)
        worst = min(ks, key=lambda k: m[k]["slowG"])[1]
        o.write("\t".join(map(str, (s, rule, len(ks), *[mins[v] for v in V], fails, thin_s, thin_f, worst))) + "\n")
o.close()
for n in ("agree2", "disagree2", "unchecked2"):
    print(f"== {n}"); print(open(H / f"results/{n}.tsv").read())
