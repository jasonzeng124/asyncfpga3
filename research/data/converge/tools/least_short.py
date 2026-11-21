#!/usr/bin/env python3
"""least_short.py LOOPS.json -- on the farm's NOT CLEAN loops (farm_parse.py), is the route the loop shipped (its last)
the least short one it built?  A route's miss: per short constraint (neg_I.txt, both corners) its worst deficit; summed
= the total miss (auto_size.sh AUTO_SHIP_LEAST's key: total, then the number of constraints, then the later route).
Compared over every route from it 1 and over the finish routes only (it >= P2-1)."""
import json, statistics as st, sys

loops = json.load(open(sys.argv[1]))
def sig(L): return tuple(L["its"][k]["sdf"] for k in sorted(L["its"], key=int))
keep = [L for L in loops if sig(L) and not any(
    M is not L and M["kernel"] == L["kernel"] and M["seed"] == L["seed"] and
    ((len(sig(M)) > len(sig(L)) and sig(M)[:len(sig(L))] == sig(L)) or (sig(M) == sig(L) and (M["req"], M["task"]) < (L["req"], L["task"])))
    for M in loops)]

def score(rows):
    d = {}
    for r in rows:
        d[r["key"]] = min(d.get(r["key"], 0), r["margin"])
    return (-sum(d.values()), len(d), -min(d.values()) if d else 0)    # total miss, constraints, worst

res = []
for L in keep:
    if not L["result"].startswith("NOT CLEAN"):
        continue
    its = {int(k): v for k, v in L["its"].items()}
    have = [i for i in its if i >= 1 and its[i]["neg"] is not None]
    if not have or L["p2"] is None:
        continue
    last = max(have)
    cand = {i: score(its[i]["neg"]) for i in have}
    fin = {i: s for i, s in cand.items() if i >= L["p2"] - 1}
    pick = lambda c: min(c, key=lambda i: (c[i][0], c[i][1], -i))
    res.append(dict(name="%s/%s %s s%s" % (L["req"], L["task"], L["kernel"], L["seed"]), last=last, sl=cand[last],
                    ba=pick(cand), bf=pick(fin), cand=cand, unf=any(x["fix"] == "unfixable" for x in its[last]["neg"])))
print("NOT CLEAN loops with per-route rule rows: %d (%d with an unfixable row on the last route)" % (len(res), sum(r["unf"] for r in res)))
for scope, b in (("every route from it 1", "ba"), ("the finish routes (it >= P2-1)", "bf")):
    ne = [r for r in res if r[b] != r["last"]]
    tl = [r["sl"][0] for r in ne]; tb = [r["cand"][r[b]][0] for r in ne]
    print("least short over %s is not the last route on %d of %d loops; there the last route's total miss median %d ps "
          "(worst row median %d), the least short's %d ps (worst row median %d); last's worst row >= 500 ps and the least "
          "short's < 200 ps on %d" % (scope, len(ne), len(res), st.median(tl), st.median([r["sl"][2] for r in ne]), st.median(tb),
                                      st.median([r["cand"][r[b]][2] for r in ne]),
                                      sum(1 for r in ne if r["sl"][2] >= 500 and r["cand"][r[b]][2] < 200)))
print("per loop (finish routes; total ps / constraints / worst ps):")
for r in sorted(res, key=lambda r: r["name"]):
    s = r["cand"][r["bf"]]
    print("  %-38s last it %d: %5d / %2d / %4d   least it %d: %5d / %2d / %4d%s" % (
        r["name"], r["last"], r["sl"][0], r["sl"][1], r["sl"][2], r["bf"], s[0], s[1], s[2], "" if r["bf"] != r["last"] else "   (the last)"))
