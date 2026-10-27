import re, sys, os
S, ROOT = sys.argv[1], sys.argv[2]
v = open(os.path.join(S, "k_plain.v")).read()
ver = {}
for m in re.finditer(r"^\s*bd_(link|pipe)\s*#\((.*?)\)\s*ulink_(\w+)\s*\(", v, re.M):
    kind, params, name = m.groups()
    n = 1
    mm = re.search(r"\.N\((\d+)\)", params)
    if mm: n = int(mm.group(1))
    # name n106__1 -> 106#1 ; n114 -> 114
    nm = name[1:]
    ssa = nm.replace("__", "#").lstrip("_")
    ver[ssa] = n
print("verilog link instances", len(ver), "stages", sum(ver.values()))
sys.path.insert(0, os.path.join(ROOT, "formal", "tools", "dfimport"))
import mlir2lean
g = mlir2lean.Graph(mlir2lean.default_mlir())
em = g.em
emd = {str(x): em.depth.get(x, 1) for x in em.linked}
def norm(s): return s.lstrip("%")
emd = {norm(k): d for k, d in emd.items()}
print("emitter linked", len(emd), "stages", sum(emd.values()))
print("ver-not-em", sorted(set(ver) - set(emd))[:10], "em-not-ver", sorted(set(emd) - set(ver))[:10])
diff = [(k, ver[k], emd[k]) for k in ver if k in emd and ver[k] != emd[k]]
print("depth mismatches", diff)
# map verilog to channels
chan = {}
for k, n in ver.items():
    key = None
    for x in em.linked:
        if norm(str(x)) == k: key = x
    a = g.A(key)
    if a in g.chan: chan[g.chan[a]] = chan.get(g.chan[a], 0) + n
lean = open(os.path.join(sys.argv[3])).read()
L = eval(re.search(r"def links : List \(Nat × Nat\) := (\[.*?\])\n", lean).group(1).replace("(", "(").replace(")", ")"))
L = dict(L)
print("channels from verilog", len(chan), "lean", len(L), "equal:", chan == L)
