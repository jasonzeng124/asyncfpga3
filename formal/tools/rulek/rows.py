#!/usr/bin/env python3
"""C-10l2: per K row and seed, the margin per corner variant from tcheck (PASS/FAIL is tcheck's,
over the pins), and the per-pin-arc corrected margin  m + arc(I2->O6).lo - arc(I1->O6).hi
(B's exact bundled_s_hold charges the join's own pin arcs; this correction is front-end
arithmetic on prjxray/SDF arc numbers, UNVERIFIED).  Also the Knocmax / Kold ablations.
    rows.py SEED...   -> results/k_rows.tsv and a summary on stdout"""
import json
import os
import sys
from collections import defaultdict
V = ["sdf", "sdfband", "fast", "slow", "fastG", "slowG"]
H = os.path.dirname(os.path.abspath(__file__))
rows = []
summ = defaultdict(lambda: defaultdict(list))
for s in sys.argv[1:]:
    res = {}
    for ln in open(f"{H}/build/out/k_{s}.out"):
        f = ln.rstrip("\n").split("\t")
        if len(f) < 3:
            continue
        head = f[0].split(" ")
        res[(head[0], " ".join(head[1:-2]), head[-2])] = (f[1], int(f[2]) if f[2] not in ("none", "") else None)
    meta = {}
    for m in json.load(open(f"{H}/build/out/k_{s}.json"))["obligations"]:
        if isinstance(m, dict) and m.get("rule") == "K" and "label" in m:
            meta[m["label"][2:]] = m
    for (tag, lab, v), (vd, mg) in sorted(res.items()):
        corr = None
        if tag == "K" and lab in meta and mg is not None:
            pa = meta[lab].get("pinarc", {})
            ch = pa.get("ctl_hi", {}).get(v)
            sl = [d.get(v) for d in pa.get("s_lo", {}).values()]
            if ch is not None and sl and None not in sl:
                corr = mg + min(sl) - ch
        rows.append((s, tag, lab.replace("urig.udut.", ""), v, vd, mg, corr))
        summ[(tag, v)][s].append((mg, corr, vd))
os.makedirs(f"{H}/results", exist_ok=True)
with open(f"{H}/results/k_rows.tsv", "w") as o:
    o.write("seed\ttag\tobligation\tvariant\tverdict\tmargin_ps\tpinarc_corrected_ps\n")
    for r in rows:
        o.write("\t".join(str(x) for x in r) + "\n")
for tag in ("K", "Kold", "Knoblk", "Knocmax", "Knolat"):
    for v in V:
        d = summ.get((tag, v))
        if not d:
            continue
        parts = []
        for s, L in sorted(d.items()):
            nf = sum(1 for x in L if x[2] != "PASS")
            mn = min((x[0] for x in L if x[0] is not None), default=None)
            mc = min((x[1] for x in L if x[1] is not None), default=None)
            parts.append(f"s{s}: {nf}/{len(L)} fail min {mn}" + (f" (pin-arc corr min {mc})" if mc is not None else ""))
        print(f"{tag:8s} {v:8s} " + "; ".join(parts))
