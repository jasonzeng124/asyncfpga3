# the X22Y81.B5 segment join: earliest common causal descendants J of X22Y87.A6(0) and X27Y80.A6(2); Up(X27Y80.A6(2) -> J)
# at depth 0 vs the budget seg1.b (UnionUpOK needs seg2.a + Up <= seg1.b, seg2.a >= 1)
import sys, os
cc = sys.argv[1]; budget = int(sys.argv[2])
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/race/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
os.environ["REL"] = "0"
exec(open("/tmp/claude-0/race/relup.py").read())
N = {nm[n]: n for n in EX}
a = eid[(N["SLICE_X22Y87.A6"], 0)]; b = eid[(N["SLICE_X27Y80.A6"], 2)]
p0 = max(int(tm[a]), int(tm[b])) + 1; idx = ord_arr[p0:p0 + 4000]
m = (VCP[idx, enode[a]] > ek[a]) & (VCP[idx, enode[b]] > ek[b])
for e in idx[m][:8]:
    e = int(e); u = up_get(b, e, 0)
    print(cc, "J %s(%d)@%d: Up(X27Y80.A6(2) -> J) = %s ps vs budget seg1.b = %d ps" % (nm[el[e][0]], el[e][1], el[e][2], u, budget))
