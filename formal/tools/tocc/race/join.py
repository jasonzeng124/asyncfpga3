import sys
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/race/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[n]: n for n in EX}
def E(n, k): return eid[(N[n], k)]
A = E("SLICE_X22Y87.A6", 0); B = E("SLICE_X27Y80.A6", 2); J = E("SLICE_X27Y80.D6", 0)
print("c=%s J=X27Y80.D6(0)@%d: Sep(A->J) %s Sep(B->J) %s; alts of J: %s" % (cc, el[J][2], sep23(A, J), sep23(B, J), [[ "%s(%d)" % (nm[el[p][0]], el[p][1]) for p in a] for a in alts[J]]))
for o in (E("SLICE_X24Y77.A6", 2), E("SLICE_X26Y85.A6", 2)): print("c=%s Sep(J -> %s(%d)@%d) = %s" % (cc, nm[el[o][0]], el[o][1], el[o][2], sep23(J, o)))
