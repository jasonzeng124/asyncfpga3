#!/usr/bin/env python3
"""bsub1 (UNTRUSTED): print the claim-end binding chain of every failing guard (base run) and group guards by root.
usage: ana2.py c [pkl]"""
import sys, os, pickle, collections
c_ = sys.argv[1]; PK = sys.argv[2] if len(sys.argv) > 2 else "/tmp/claude-0/bsub1/tocc/datal_t_c%s.pkl" % c_
sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/bsub1/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
NEG = -INF
B0 = pickle.load(open(PK, "rb")); MEMO = B0["MEMO"]
def evs(e):
    if e is None: return None
    n, k, t = el[e]; return "%s(%d)@%d" % (nm[n], k, t)
def chainof(cz):
    out = []; cur = MEMO.get(cz.get("key")) or cz; seen = set()
    while cur is not None and cur.get("key") not in seen:
        seen.add(cur.get("key"))
        tr = cur.get("trunc")
        out.append(dict(node=nm[cur["key"][0]], kind=cur.get("kind"), B=evs(cur.get("B")), b=cur.get("b"),
                        phases="".join(p[0] for p in cur.get("phases", [])) if cur.get("phases") else "",
                        trunc=(tr["kind"], evs(tr["c1"]["B"]), evs(tr["c2"]["A"]), None if tr["margin"] == NEG else tr["margin"]) if tr else None))
        b = cur.get("bind")
        if not b or not isinstance(b, tuple) or len(b) != 3:
            out[-1]["stop"] = str(b)[:60]; break
        cur = MEMO.get(b[2])
    return out
roots = collections.defaultdict(list)
o = open("/tmp/claude-0/bsub1/chains_c%s%s.txt" % (c_, "" if len(PK.split("datal_t_")) > 1 else "_" + os.path.basename(PK)), "w")
for x in B0["G"]:
    if len(x) != 7 or min(x[2], x[3]) >= 0: continue
    v, z, ms, me, cz, st, en_ = x
    ch = chainof(cz)
    trs = [s for s in ch if s["trunc"]]
    root = (trs[-1]["node"], trs[-1]["trunc"][0], trs[-1]["trunc"][1], trs[-1]["trunc"][2], trs[-1]["trunc"][3]) if trs else ("<no truncation>", ch[-1]["node"], ch[-1]["kind"], ch[-1]["B"])
    roots[root].append((nm[v], nm[z], evs(eid[en_]) if en_ else None))
    print("guard v=%s z=%s E=%s me=%s" % (nm[v], nm[z], evs(eid[en_]) if en_ else None, me), file=o)
    for s in ch: print("    ", s, file=o)
print("[c=%s] failing guards %d; roots (deepest truncation on the claim-end chain):" % (c_, sum(len(v) for v in roots.values())))
for r, gs in sorted(roots.items(), key=lambda kv: -len(kv[1])):
    print("  %3d  %s   e.g. %s" % (len(gs), r, gs[0]))
