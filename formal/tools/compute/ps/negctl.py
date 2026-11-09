#!/usr/bin/env python3
"""Negative controls for check_unit.py (untrusted): mutate net.json and expect FAILs.
 init: flip one INIT bit of uselect1's first CARRY-feeding LUT gate (SLICE of a uselect1 LUT3)
 pip : re-point the source of one copy gate feeding ucmpi0's SLICE_X0Y54.DLUT.O6 pin A1 to the node feeding A2
 ci  : flip CYINIT dependence of one uaddi0 CARRY4 CO0 gate (INIT xor full mask on the CYINIT bit)"""
import json, subprocess, copy, sys
N = json.load(open("net.json")); nid = {n: i for i, n in enumerate(N["nodes"])}
gout = {g["out"]: g for g in N["gates"]}; byname = {g["name"]: g for g in N["gates"]}
def run(net, unit, tag):
    json.dump(net, open(f"net_{tag}.json", "w"))
    r = subprocess.run(["python3", "check_unit.py", "ps.json", "ps.routed.json", f"net_{tag}.json", unit], capture_output=True, text=True)
    fl = [l for l in r.stdout.splitlines() if "FAIL" in l]
    print(f"{tag}: rc={r.returncode}", fl[:2]); return r.returncode
rc = []
# init
M = copy.deepcopy(N); g = next(g for g in M["gates"] if g["name"] == "SLICE_X0Y54.DLUT.O6"); g["init"] ^= 1
rc.append(run(M, "ucmpi0", "init"))
# pip
M = copy.deepcopy(N); g = next(g for g in M["gates"] if g["name"] == "SLICE_X0Y54.DLUT.O6")
a1, a2 = g["ins"][0], g["ins"][1]
cg = next(x for x in M["gates"] if x["out"] == a1); cg2 = next(x for x in M["gates"] if x["out"] == a2)
cg["ins"] = list(cg2["ins"])
rc.append(run(M, "ucmpi0", "pip"))
# carry: uselect1's first CARRY4 CO3 gate, flip the half where CI=1
M = copy.deepcopy(N)
cands = [x for x in M["gates"] if x["name"].endswith("CARRY4.CO3") and x["name"].startswith("SLICE_X30Y88")]
x = cands[0]; x["init"] ^= sum(1 << a for a in range(1 << x["k"]) if a & 1)
rc.append(run(M, "uselect1", "carry"))
print("all negative controls caught:", all(r != 0 for r in rc))
