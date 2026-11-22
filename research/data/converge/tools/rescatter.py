#!/usr/bin/env python3
"""rescatter.py CA_DIR... -- how far a re-route moves each sized constraint's margin, from local sizing loops that kept
every route's corner_audit report ($RUNS/ca/<loop>_<I>/rule_<corner>/report.txt, sizes in seed1/pnr/sizes.vh).
CA_DIR: a $RUNS/ca directory; every <loop>_<I> with a <loop>_<I-1> beside it (I-1 >= 1: the estimates route it 0 is left
out) is a pair.  A constraint is keyed by its rule and site (E: its request pin); its "depends on" lines and their sizes
on both routes say whether the loop changed any of them.  Prints:
  * the margin change of constraints none of whose lines changed size (pure re-route scatter);
  * on RAISE-ONLY pairs (no line lowered anywhere: the finish phase, or a loop's raise-only step), how many constraints
    per route and corner go from >= 0 to short, by their margin on the first route, and what a slack X (every
    constraint below X padded to X, its next margin shifted by X - a) would leave -- a model, not a measurement;
  * every such new short row with its margin before and after."""
import glob, os, re, statistics as st, sys

SIZED = set("AEFHIKLBC")
RW = re.compile(r"^  (\S+)\s+([+-]?\d+)  (.*)$")

def key_of(rule, text):
    if rule == "E":
        m = re.search(r" req (\S+) ", text)
        return "E " + (m.group(1) if m else text.split()[1])
    tag = "joined" if " joined: " in text else ("from" if " from " in text and ": req " in text else ("peak" if " peak " in text else ""))
    return "%s %s %s" % (rule, text.split()[0], tag)

def rd_report(p):
    cons, cur, on = {}, None, False
    for ln in open(p):
        if ln.startswith("every constraint"): on = True; continue
        if not on: continue
        if ln.startswith("gaps the audits"): break
        m = RW.match(ln.rstrip("\n"))
        if m and not ln.startswith("             "):
            rule, mg, text = m.group(1), int(m.group(2)), m.group(3)
            if rule not in SIZED or "bridge_i.udut." not in " ".join(text.split()[:3]):
                cur = None; continue
            k = key_of(rule, text)
            cur = dict(margin=mg, deps={})
            if k in cons and cons[k]["margin"] <= mg: continue     # keep the worst row of a key
            cons[k] = cur; continue
        m = re.match(r"^\s+depends on: (.*)$", ln)
        if m and cur is not None:
            for x in m.group(1).split(", "):
                mm = re.match(r"(\S+)\(-(\S+)\)", x.strip())
                if mm: cur["deps"]["BD_SZ_" + mm.group(1)] = mm.group(2)
    return cons

def rd_sizes(p):
    d = {}
    if os.path.exists(p):
        for ln in open(p):
            m = re.match(r"`define\s+(\S+)\s+(\d+)", ln)
            if m: d[m.group(1)] = int(m.group(2))
    return d

pairs = []
roots = sorted({re.sub(r"_\d+$", "", d) for a in sys.argv[1:] for d in glob.glob(a + "/*_*") if re.search(r"_\d+$", d)})
for root in roots:
    its = sorted(int(d.rsplit("_", 1)[1]) for d in glob.glob(root + "_*") if re.search(r"_\d+$", d))
    for i in its:
        if i - 1 not in its or i - 1 < 1: continue
        sa = rd_sizes("%s_%d/seed1/pnr/sizes.vh" % (root, i - 1)); sb = rd_sizes("%s_%d/seed1/pnr/sizes.vh" % (root, i))
        if not sa or not sb: continue
        lowany = any(sb.get(m, 0) < v for m, v in sa.items())
        for c in ("0.20", "0.31"):
            pa = "%s_%d/rule_%s/report.txt" % (root, i - 1, c); pb = "%s_%d/rule_%s/report.txt" % (root, i, c)
            if not (os.path.exists(pa) and os.path.exists(pb)): continue
            A, B = rd_report(pa), rd_report(pb)
            for k in A:
                if k not in B: continue
                deps = set(A[k]["deps"]) | set(B[k]["deps"])
                pairs.append(dict(root=os.path.basename(root), i=i, c=c, k=k, a=A[k]["margin"], b=B[k]["margin"], nd=len(deps),
                                  changed=any(sa.get(d) != sb.get(d) for d in deps), raised=any(sb.get(d, 0) > sa.get(d, 0) for d in deps),
                                  lowany=lowany))
q = lambda a, x: sorted(a)[min(len(a) - 1, int(x * len(a)))]
print("loops %d, route pairs %d, constraint-corner pairs %d" % (len({p['root'] for p in pairs}), len({(p['root'], p['i']) for p in pairs}), len(pairs)))
un = [p["b"] - p["a"] for p in pairs if not p["changed"] and p["nd"] > 0]
print("margin change, no line of the constraint changed size: n=%d sd %.0f ps, median |d| %d; p5 %d p10 %d p25 %d median %d p75 %d p90 %d p95 %d" % (
    len(un), st.pstdev(un), st.median([abs(x) for x in un]), q(un, .05), q(un, .1), q(un, .25), q(un, .5), q(un, .75), q(un, .9), q(un, .95)))
for k in sorted({p["k"].split()[0] for p in pairs}):
    v = [p["b"] - p["a"] for p in pairs if not p["changed"] and p["nd"] > 0 and p["k"].split()[0] == k]
    if len(v) >= 20: print("  rule %-2s n=%5d sd %4.0f  p5 %5d  p10 %5d  median %4d  p90 %4d" % (k, len(v), st.pstdev(v), q(v, .05), q(v, .1), q(v, .5), q(v, .9)))
ro = [p for p in pairs if not p["lowany"]]
rc = {(p["root"], p["i"], p["c"]) for p in ro}
print("raise-only pairs: %d routes (%s), %d route-corners" % (len({(p['root'], p['i']) for p in ro}),
      " ".join(sorted({"%s:%d" % (p['root'], p['i']) for p in ro})), len(rc)))
for lo, hi in [(0, 100), (100, 200), (200, 300), (300, 500), (500, 1000), (1000, 10 ** 6)]:
    xs = [p for p in ro if lo <= p["a"] < hi]
    print("  margin on route I-1 in [%5d, %7d): %5.1f constraints per route-corner, short on route I: %3d (%.2f)" % (
        lo, hi, len(xs) / len(rc), sum(p["b"] < 0 for p in xs), sum(p["b"] < 0 for p in xs) / max(1, len(xs))))
print("  short on I and already short on I-1: %.2f per route-corner" % (sum(1 for p in ro if p["a"] < 0 and p["b"] < 0) / len(rc)))
for X in (0, 100, 200, 300, 500, 700, 1000):
    print("  model: slack X=%4d -> new short rows per route-corner %.2f" % (X, sum(1 for p in ro if p["a"] >= 0 and p["b"] + max(0, X - p["a"]) < 0) / len(rc)))
ns = [p for p in ro if p["a"] >= 0 and p["b"] < 0]
print("new short rows on raise-only routes: %d; margin before median %d ps (%d-%d), change median %d ps (%d..%d); a line of theirs raised: %d" % (
    len(ns), st.median([p["a"] for p in ns]), min(p["a"] for p in ns), max(p["a"] for p in ns), st.median([p["b"] - p["a"] for p in ns]),
    max(p["b"] - p["a"] for p in ns), min(p["b"] - p["a"] for p in ns), sum(p["raised"] for p in ns)))
for p in sorted(ns, key=lambda p: (p["root"], p["i"], p["c"])):
    print("  %-22s it %-2d %s  %+5d -> %+5d (%+5d)  %s" % (p["root"], p["i"], p["c"], p["a"], p["b"], p["b"] - p["a"], p["k"][:80]))
