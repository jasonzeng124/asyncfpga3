#!/usr/bin/env python3
"""finish_misses.py LOOPS.json -- the rows short on the sizing loop's finish routes (auto_size.sh phase 2, raise-only),
from the farm's returned loop files (farm_parse.py).  Prints:
  * the per-step clean rate of the finish routes (step 1 / 2 / 3 = it 5 / 6 / 7 at MAXIT 4, AUTO_FINISH 3);
  * every line-fixable short row of a finish route ("miss": one constraint on one route, worst corner), by rule kind and
    size; classified as
      rec_key   the same constraint was short on an earlier route of the finish phase (it P2-1 .. I-1) and raised,
      rec_line  a line it depends on was raised in the finish phase, for another constraint,
      new       neither;
    its size against one element of its line (the line's mean step D/size on that route) and c_lo (the route's cheapest
    link-to-link step); the line's status on the previous route (lines_I_C.txt: "floor" shows no margin at all,
    "bound_kept" a visible "ps left", "bound_shrunk" the margin at a SHORTER size, "pad" short then too);
  * per finish route with no unfixable row: is every miss a recurrence (what more headroom on raised lines could reach)?
Loops are deduplicated: a loop whose sequence of route md5s is a prefix of another's (a resumed request) is dropped."""
import collections, json, re, statistics as st, sys

loops = json.load(open(sys.argv[1]))
def sig(L): return tuple(L["its"][k]["sdf"] for k in sorted(L["its"], key=int))
keep = []
for L in loops:
    s = sig(L)
    if not s: continue
    dom = any(M is not L and M["kernel"] == L["kernel"] and M["seed"] == L["seed"] and
              ((len(sig(M)) > len(s) and sig(M)[:len(s)] == s) or (sig(M) == s and (M["req"], M["task"]) < (L["req"], L["task"])))
              for M in loops)
    if not dom: keep.append(L)
print("loop directories %d, unique loops %d, with a finish phase %d" % (len(loops), len(keep), sum(1 for L in keep if L["p2"] is not None)))
q = lambda a, x: sorted(a)[min(len(a) - 1, int(x * len(a)))]

# per-step clean rate (loops with no unfixable row after it 1: those can never be clean)
haz, tot = collections.Counter(), collections.Counter()
for L in keep:
    its = {int(k): v for k, v in L["its"].items()}
    if L["p2"] is None: continue
    if any(r["fix"] == "unfixable" for i in its for r in (its[i]["neg"] or []) if i >= 2): continue
    for i in sorted(its):
        m = re.search(r"negative (\d+)", its[i]["summ"])
        if not m or i < L["p2"]: continue
        tot[i - L["p2"] + 1] += 1; haz[i - L["p2"] + 1] += m.group(1) == "0"
        if m.group(1) == "0": break
print("finish step k: routes clean / built (loops without unfixable rows): " +
      ", ".join("k=%d %d/%d (%.0f%%)" % (k, haz[k], tot[k], 100.0 * haz[k] / tot[k]) for k in sorted(tot)))

out = []
nodata = 0
for L in keep:
    if L["p2"] is None: continue
    its = {int(k): v for k, v in L["its"].items()}
    p2, last = L["p2"], max(its)
    if any(its[i]["neg"] is None for i in range(p2 - 1, last + 1) if i in its):
        nodata += 1; continue
    raised_fin = collections.defaultdict(list); seen = set()
    for i in range(p2 - 1, last + 1):
        if i not in its: break
        it = its[i]
        nk = {}
        for r in it["neg"]:
            if r["key"] not in nk or r["margin"] < nk[r["key"]]["margin"]: nk[r["key"]] = r
        if i >= p2:
            for k, r in nk.items():
                inst = k.split(" ", 1)[1] if " " in k else k
                deps = set()
                for rr in it["neg"]:
                    if rr["key"] != k: continue
                    ca = it["ca"].get(rr["corner"].replace("rule_", ""))
                    for row in (ca or {}).get("rows", []):
                        if row["margin"] == rr["margin"] and inst in row["text"]: deps |= set(row["deps"])
                pad = None
                for c in ("0.20", "0.31"):
                    for mac, v in (it["lines"].get(c) or {}).items():
                        if ("for %s (" % k) in v["why"]: pad = mac
                lines = {pad} if pad else ((deps & {x[0] for x in it["raised"]}) or deps)
                prev = its.get(i - 1); pst = []
                for mac in lines:
                    for c in ("0.20", "0.31"):
                        v = (prev["lines"].get(c) or {}).get(mac) if prev else None
                        if v: pst.append((v["size"], v["prop"], v["why"]))
                st_ = "unknown"
                for tag, test in (("pad", lambda s, p, w: w.startswith("PAD")), ("bound_kept", lambda s, p, w: w.startswith("bound") and p >= s),
                                  ("bound_shrunk", lambda s, p, w: w.startswith("bound")), ("floor", lambda s, p, w: w.startswith("floor"))):
                    if any(test(*x) for x in pst): st_ = tag; break
                el = [v["D"] / v["size"] for mac in lines for c in ("0.20", "0.31")
                      for v in [(it["lines"].get(c) or {}).get(mac)] if v and v["size"] > 0]
                clo = [it["ca"][c]["clo"] for c in ("0.20", "0.31") if it["ca"].get(c) and it["ca"][c]["clo"]]
                cls = "rec_key" if k in seen else ("rec_line" if any(m in raised_fin for m in lines) else "new")
                out.append(dict(loop=(L["req"], L["task"]), kernel=L["kernel"], it=i, key=k, kind=k.split()[0], margin=r["margin"],
                                fix=r["fix"], cls=cls, prev=st_, el=max(el) if el else None, clo=min(clo) if clo else None))
        seen |= set(nk)
        for mac, a, b in it["raised"]: raised_fin[mac].append((i, a, b))
print("finish loops with a short row on a finish route: %d (%d finish loops lack the per-iteration rule files)" % (len({m['loop'] for m in out}), nodata))
M = [m for m in out if m["fix"] == "line"]
print("line-fixable misses (constraint x finish route): %d" % len(M))
kc = collections.Counter(m["kind"] for m in M)
for k, _ in kc.most_common():
    xs = [-m["margin"] for m in M if m["kind"] == k]
    print("  %-4s n=%4d  miss median %4d  p75 %4d  p90 %4d  max %5d ps" % (k, len(xs), st.median(xs), q(xs, .75), q(xs, .9), max(xs)))
xs = [-m["margin"] for m in M]
print("  all  n=%4d  miss median %4d  p75 %4d  p90 %4d" % (len(xs), st.median(xs), q(xs, .75), q(xs, .9)))
cc = collections.Counter(m["cls"] for m in M)
print("class: " + ", ".join("%s %d (%.1f%%)" % (c, cc[c], 100.0 * cc[c] / len(M)) for c in ("new", "rec_key", "rec_line")))
for c in ("new", "rec_key", "rec_line"):
    xs = [m for m in M if m["cls"] == c and m["el"]]
    print("  %-8s miss <= one element of its line: %d of %d (%.0f%%); <= c_lo: %d" % (
        c, sum(-m["margin"] <= m["el"] for m in xs), len(xs), 100.0 * sum(-m["margin"] <= m["el"] for m in xs) / max(1, len(xs)),
        sum(1 for m in xs if m["clo"] and -m["margin"] <= m["clo"])))
pc = collections.Counter(m["prev"] for m in M if m["cls"] == "new")
print("new misses, their line on the previous route: " + ", ".join("%s %d" % kv for kv in pc.most_common()))
# per route
R = collections.defaultdict(list); U = collections.Counter()
for m in out:
    (R if m["fix"] == "line" else U)[(m["loop"], m["it"])] += [m] if m["fix"] == "line" else 1
fx = [r for r in R if not U.get(r)]
allrec = lambda ms, cap: all(m["cls"] != "new" and (not cap or (m["el"] and -m["margin"] <= m["el"])) for m in ms)
print("finish routes with misses and no unfixable row: %d; every miss a recurrence: %d; and within one element: %d" % (
    len(fx), sum(allrec(R[r], False) for r in fx), sum(allrec(R[r], True) for r in fx)))
last = {}
for (lp, i) in fx:
    if lp not in last or i > last[lp]: last[lp] = i
lr = [(lp, i) for lp, i in last.items()]
nm = [len({m["key"] for m in R[r]}) for r in lr]; mx = [max(-m["margin"] for m in R[r]) for r in lr]
print("last finish route of %d loops: every miss a recurrence %d, within one element %d; short constraints median %d (%d-%d); "
      "worst miss median %d ps (%d-%d); worst < 100 ps: %d, < 200: %d, < 300: %d" % (
          len(lr), sum(allrec(R[r], False) for r in lr), sum(allrec(R[r], True) for r in lr), st.median(nm), min(nm), max(nm),
          st.median(mx), min(mx), max(mx), sum(x < 100 for x in mx), sum(x < 200 for x in mx), sum(x < 300 for x in mx)))
