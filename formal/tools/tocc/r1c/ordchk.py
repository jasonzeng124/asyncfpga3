# causal order / Sep between the masking pin's start (X22Y87.A6 k) and X27Y80.A6(2) at corner c
import sys
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/r1c/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[n]: n for n in EX}
def E(n, k): return eid[(N[n], k)]
b = E("SLICE_X27Y80.A6", 2)
for k in range(len(ev[N["SLICE_X22Y87.A6"]])):
    a = E("SLICE_X22Y87.A6", k)
    print(cc, "X22Y87.A6(%d)@%d vs X27Y80.A6(2)@%d: a<=b %s, b<=a %s, sep23(a,b) %s" % (k, el[a][2], el[b][2], bool(leqP(a, b)), bool(leqP(b, a)), sep23(a, b)))
