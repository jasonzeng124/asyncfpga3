#!/usr/bin/env python3
"""bnd_lean_cmp.py (audit T8): Decoded.boundary in the generated Lean (Net/All.lean) vs the auditor's own boundary
(bnd.json from my T4 rerun), by node NAME (Lean indices resolved through Net/Nodes.lean).
    python3 -I bnd_lean_cmp.py LEANDIR BND.json"""
import json, re, sys, os
d, bp = sys.argv[1:3]
names = []
for m in re.finditer(r'def n\d+ : List String := \[(.*?)\]\n', open(os.path.join(d, "Nodes.lean")).read(), re.S):
    names += json.loads("[" + m.group(1) + "]")
B = json.load(open(bp))["boundary"]
b = open(os.path.join(d, "All.lean")).read(); b = b[b.index("def boundary"):]
ok = True
rst = int(re.search(r"rst := (\d+)", b).group(1))
print("rst", names[rst], names[rst] == B["rst"]); ok &= names[rst] == B["rst"]
for f, (rq, ak, dk) in {"a": ("req", "a_ack", "a_data"), "b": ("req", "b_ack", "b_data"), "start": ("req", "start_ack", None),
                        "pend": ("req", "pend_ack", None), "out0": ("out0_req", "out0_ack", "out0_data")}.items():
    m = re.search(f + r" := ⟨(\d+), (\d+), \[([^\]]*)\]⟩", b)
    r, a = int(m.group(1)), int(m.group(2)); dl = [int(x) for x in re.findall(r"\d+", m.group(3))]
    dn = [names[i] for i in dl]; exp = [("CONST0" if x == "const0" else x) for x in B[dk]] if dk else []   # my bnd.json spells the tie "const0"
    good = names[r] == B[rq] and names[a] == B[ak] and dn == exp
    ok &= good
    print(f, "req", names[r], "ack", names[a], "data", len(dn), "match" if good else "DIFF")
    if not good:
        print("   lean data", dn[:6], "... own", exp[:6])
print("BOUNDARY", "EQUAL" if ok else "DIFFERENT")
