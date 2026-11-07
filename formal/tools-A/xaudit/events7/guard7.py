"""guard7.py -- ana's guard rules (ENTRY / EXIT, UNTRUSTED, not proved: W-E4g) for every guarded pin,
with W (the guarded source's minimum event spacing) recomputed by cert7's walk search (all R3
candidates, U3, n-ary merges).  GuardOK is a HYPOTHESIS of design_verdict7; this is the evidence
the analysis has for it.   python3 guard7.py SKEL.json BANDS.json LABEL"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cert7 import Cert7  # noqa: E402

C = Cert7(sys.argv[1], sys.argv[2])
M, A = C.M, C.A
rows = []
for e in C.res["stages"]:
    if e["rule"] != "Guard":
        continue
    j, k = e["stage"], e["pin"]
    p = M.nodes[j]["pins"][k]
    w = C.walk(p.src, p.src, 1, closed=True)
    W = w[0] if w else None
    hiQ = M.nodes[j]["Q"][1]
    exitm = (W + p.lo - p.hi - M.nodes[j]["F"][1] - hiQ) if W is not None else None
    rows.append((e["entry"], exitm, W, p.kind == "multi", j, k, p.src))
bad_e = [r for r in rows if r[0] is None or r[0] <= 0]
bad_x = [r for r in rows if r[1] is None or r[1] <= 0]
mn = lambda l: min(l) if l else None
print(f"[{sys.argv[3]}] guarded pins {len(rows)} ({sum(r[3] for r in rows)} delay lines): "
      f"min ENTRY {mn([r[0] for r in rows if r[0] is not None])}, min EXIT {mn([r[1] for r in rows if r[1] is not None])}; "
      f"ENTRY<=0 {len(bad_e)}, EXIT<=0 or none {len(bad_x)}")
for r in rows:
    if r[3]:
        print(f"  line-guard ENTRY {r[0]} EXIT {r[1]} W {r[2]}  {r[4]} pin{r[5]} <- {r[6]}")
for r in bad_e + bad_x:
    print(f"  BAD ENTRY {r[0]} EXIT {r[1]} W {r[2]}  {r[4]} pin{r[5]} <- {r[6]}")
