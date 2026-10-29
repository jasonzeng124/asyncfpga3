#!/usr/bin/env python3
"""Auditor r15: independent summary of per-ring periods vs the August README table.
Input: TSV with columns route ring links <meas col> <pred col> (or ring128_summary_rings.tsv).
Statistic definitions are taken from cells/hw/README.md / ro_many_measure.py semantics
(nearest-rank p90, median, kfit through origin, slower = residual>0), written from scratch."""
import sys, csv, math, collections
AUG = {"all.median": 0.989, "short_long": 1.176/0.969, "slower": 76,
       "7.w90": 1.438/1.176, "15.w90": 1.117/0.987, "31.w90": 1.085/0.959, "63.w90": 1.059/0.969}
GR = list(AUG)
def med(v):
    v = sorted(v); n = len(v)
    return v[n//2] if n % 2 else 0.5*(v[n//2-1]+v[n//2])
def nr(v, p):  # nearest rank: ceil(p*n) (for n=32 p90 -> rank 29; n=128 -> 116)
    v = sorted(v); n = len(v); k = int(math.floor(p*n + 0.5))  # round(p n) as ro_many_measure's round(p n + .5)-1 ... see note
    # ro_many_measure: idx = int(round(p*n + 0.5)) - 1 ; replicate the RANK it picks, independently checked below
    idx = int(round(p*n + 0.5)) - 1
    return v[max(0, min(n-1, idx))]
def summ(rings):  # rings: list of (links, meas, pred)
    k = sum(m*p for _, m, p in rings)/sum(p*p for _, m, p in rings)
    out = {"kfit": k, "slower": sum(1 for _, m, p in rings if m - k*p > 0)}
    r = [m/p for _, m, p in rings]
    out["all.median"] = med(r)
    for L in (7, 15, 31, 63):
        rl = [m/p for l, m, p in rings if l == L]
        out[f"{L}.median"] = med(rl); out[f"{L}.p90"] = nr(rl, .9)
        out[f"{L}.w90"] = out[f"{L}.p90"]/out[f"{L}.median"]
    out["short_long"] = out["7.median"]/out["63.median"]
    return out
def q(v, p):  # linear-interp quantile for the 2.5/97.5 band (method only matters at the edges)
    v = sorted(v); x = p*(len(v)-1); i = int(x); f = x-i
    return v[i] if i+1 >= len(v) else v[i]*(1-f)+v[i+1]*f
if __name__ == "__main__":
    tsv, mcol, pcol = sys.argv[1], sys.argv[2], sys.argv[3]
    by = collections.defaultdict(list)
    for row in csv.DictReader((l for l in open(tsv) if not l.startswith("#")), delimiter="\t"):
        by[row.get("sample", row["route"])].append((int(row["links"]), float(row[mcol]), float(row[pcol])))
    S = [summ(v) for v in by.values()]
    print(f"{tsv} meas={mcol} pred={pcol} samples={len(S)} rings/sample={[len(v) for v in by.values()][:3]}...")
    nin = 0
    for g in GR:
        vals = [s[g] for s in S]; lo, mi, hi = q(vals, .025), med(vals), q(vals, .975)
        ins = lo <= AUG[g] <= hi; nin += ins
        print(f"  {g:12s} {lo:8.3f} {mi:8.3f} {hi:8.3f}  Aug {AUG[g]:7.3f}  {'in' if ins else 'OUT'}")
    print(f"  graded inside: {nin}/7")

def loo(S):
    """Self-consistency: treat each sample as the 'August' row; is it inside the other samples' 2.5-97.5% band
    on all 7 graded stats?  = pass rate of the criterion when the model IS the truth (same route population)."""
    ok = 0; per = {g: 0 for g in GR}
    for i, s in enumerate(S):
        rest = S[:i] + S[i+1:]; n = 0
        for g in GR:
            v = [r[g] for r in rest]
            if q(v, .025) <= s[g] <= q(v, .975): n += 1; per[g] += 1
        ok += (n == 7)
    return ok / len(S), {g: per[g] / len(S) for g in GR}
