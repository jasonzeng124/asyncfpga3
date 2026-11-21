# static bounds: for common ancestors e0 of A and B: Up(e0->A) (UpOKA style, ao.up_from) and Sep23(e0->B), and vice versa
import sys
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/race/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[n]: n for n in EX}
def E(n, k): return eid[(N[n], k)]
def s(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
A = E("SLICE_X22Y87.A6", 0); B = E("SLICE_X27Y80.A6", 2)
O = E("SLICE_X24Y77.A6", 2); O2 = E("SLICE_X26Y85.A6", 2)
cands = []
m = np.minimum(VCP[A], VCP[B])
for x in np.nonzero(m)[0]:
    e0 = eid[(xs[x], int(m[x]) - 1)]; cands.append(e0)
for nmx, k in (("SLICE_X42Y97.B6", 2), ("SLICE_X39Y65.B6", 0)): cands.append(E(nmx, k))
cands = sorted(set(cands), key=lambda e: -et[e])
rows = []
for e0 in cands[:40]:
    uA = up_from(e0, int(tm[A])).get(A); uB = up_from(e0, int(tm[B])).get(B)
    sA = sep23(e0, A); sB = sep23(e0, B)
    rows.append((e0, sA, uA, sB, uB))
    if uA is not None or uB is not None or e0 in cands[-2:]:
        print("e0 %-30s Sep->A %s Up->A %s | Sep->B %s Up->B %s" % (s(e0), sA, uA, sB, uB))
print("n cands", len(cands), "with Up->A:", sum(1 for r in rows if r[2] is not None), "with Up->B:", sum(1 for r in rows if r[4] is not None))
print("Sep(A->O)", sep23(A, O), "Sep(B->O)", sep23(B, O), "Sep(A->O2)", sep23(A, O2), "Sep(B->O2)", sep23(B, O2))
