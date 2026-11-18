#!/usr/bin/env python3
"""draws_table.py RESULTS_DIR -- summarise a farm request that ran bench_gate.sh draw:K (draws1, shrink*, draws2):
per (first line of task.txt minus the task number), routes, routes carrying the 5FF-D defect (FFMUX-FLAG, excluded),
draws passing / run on the rest, batches with the run-to-run mismatch latch, period median and range (P= from eval).
    git --work-tree=/tmp/x checkout origin/claude/cluster -- results/shrink5; python3 research/tools/draws_table.py /tmp/x/results/shrink5
A draw counts as passing only on "=> PASS" (the fixed verdict: every run of every batch right) and as failing only on
"=> FAIL" (a wrong answer, a batch that never completed -- the gate's own HANG cutoff -- or runs that disagree).
"=> TIMEOUT/none" means the request's wrapper (`timeout 100m`) killed the simulation before the gate gave a verdict: it
is UNDECIDED, counted apart, never as a fail (2026-11-18: shrink8 ipow x0.55 route 12's three "hung" draws were this;
formal C50 ran the same draws on the same bits through the same gate: PASS, ~380 s each). Until then such draws were
counted as failures here."""
import glob, os, re, statistics as st, sys
R = {}
for t in sorted(glob.glob(os.path.join(sys.argv[1], "*", "task.txt"))):
    d = os.path.dirname(t); s = open(t).read(); head = s.split("\n")[0]
    key = re.sub(r"\s*(task|block) \d+.*$", "", re.sub(r"seed \d+", "", head)).strip()
    P = re.search(r"P=(\d+)", s); ff = "FFMUX-FLAG" in s
    ne = bool(re.search(r"^build .*NOT EQUIVALENT", s, re.M))  # bits differ from the netlist: not a board route (2026-11-17)
    dp = len(re.findall(r"=> PASS", s)); dt = len(re.findall(r"=> TIMEOUT", s))
    dn = len(re.findall(r"^draw ", s, re.M)) - dt   # draws with a verdict
    sims = sum(1 for f in glob.glob(d + "/benchres_*.txt") if os.path.getsize(f) > 0)
    mm = sum(len(re.findall(r"mism_st=[13579bdf]\b", open(f).read())) for f in glob.glob(d + "/benchres_*.txt"))
    seed = re.search(r"seed (\d+)", head)
    R.setdefault(key, []).append(dict(seed=seed.group(1) if seed else "?", P=int(P.group(1)) if P else None, ff=ff,
                                      dp=dp, dn=dn, dt=dt, sims=sims, mm=mm, ne=ne))
for k, rows in sorted(R.items()):
    ok = [r for r in rows if not r["ff"] and not r["ne"] and (r["sims"] or r["dp"])]
    nos = [r["seed"] for r in rows if not r["ff"] and not r["sims"] and not r["dp"] and r["dn"]]
    Ps = sorted({(r["seed"], r["P"]) for r in ok if r["P"]})
    pv = [p for _, p in Ps]
    fails = sorted({r["seed"] for r in ok if r["dp"] < r["dn"]}, key=lambda x: int(x) if x.isdigit() else 0)
    print("%s: routes %d (ffmux %d, NOT EQUIVALENT %d, never simulated %s), draws %d / %d (+ %d undecided: wrapper timeout), mismatch batches %d, P median %s (%s)%s" % (
        k, len({r["seed"] for r in rows}), sum(r["ff"] for r in rows), sum(r["ne"] and not r["ff"] for r in rows), nos or "none",
        sum(r["dp"] for r in ok), sum(r["dn"] for r in ok), sum(r["dt"] for r in ok), sum(r["mm"] for r in ok),
        "%.2f" % (st.median(pv) / 1000) if pv else "-", "%.2f-%.2f" % (min(pv) / 1000, max(pv) / 1000) if pv else "-",
        ", failing routes " + " ".join(fails) if fails else ""))
