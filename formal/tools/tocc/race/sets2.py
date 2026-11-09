# race-2 adversary sets: gates of events between {A,B} and the reader opens {O,O2} -> lo; data path X22Y87.D5/X22Y81.B5/X27Y80.B6
# and the readers' D pins -> hi; plus the race-1 sets (A-only hi, B-only lo). Also static margins with kappa.
import sys, json
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/race/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[n]: n for n in EX}
def E(n, k): return eid[(N[n], k)]
A = E("SLICE_X22Y87.A6", 0); B = E("SLICE_X27Y80.A6", 2); O = E("SLICE_X24Y77.A6", 2); O2 = E("SLICE_X26Y85.A6", 2)
lo = set()
for s_ in (A, B):
    for t_ in (O, O2):
        de = VCP[:, enode[s_]] > ek[s_]; an = VCP[t_][enode] > ek
        lo |= set(el[e][0] for e in np.nonzero(de & an)[0])
S1 = json.load(open("/tmp/claude-0/race/sets_c%s.json" % cc))
hiG = sorted(set(S1["hiG"]) - set(nm[n] for n in lo)) + ["SLICE_X22Y87.D5", "SLICE_X22Y81.B5", "SLICE_X27Y80.B6"]
loG = sorted(set(S1["loG"]) | set(nm[n] for n in lo))
sp = [[L, "SLICE_X22Y81.B5"] for L in ("SLICE_X25Y76.B5", "SLICE_X25Y76.B6", "SLICE_X27Y85.A6", "SLICE_X27Y85.A5")]
json.dump(dict(hiG=hiG, loG=loG, slowpins=sp), open("/tmp/claude-0/race/sets2_c%s.json" % cc, "w"))
print("c=%s: lo gates on {A,B}->{O,O2} %d" % (cc, len(lo)))
from classify import load
def w(v, u):
    for p in g[N[v]]["pins"] if N.get(v) else C["gates"][[i for i, x in enumerate(nm) if x == v][0]]["pins"]:
        if nm[p["src"]] == u: return p["win"][c]
idn = {x: i for i, x in enumerate(nm)}
def win(v, u):
    for p in g[idn[v]]["pins"]:
        if nm[p["src"]] == u: return p["win"][c]
for (L, en, Oe, name) in (("SLICE_X25Y76.B5", "SLICE_X24Y77.A6", O, "O"), ("SLICE_X25Y76.B6", "SLICE_X24Y77.A6", O, "O"),
                          ("SLICE_X27Y85.A6", "SLICE_X26Y85.A6", O2, "O2"), ("SLICE_X27Y85.A5", "SLICE_X26Y85.A6", O2, "O2")):
    for (X, path) in ((A, [("SLICE_X22Y87.D5", "SLICE_X22Y87.A6"), ("SLICE_X22Y81.B5", "SLICE_X22Y87.D5"), (L, "SLICE_X22Y81.B5")]),
                      (B, [("SLICE_X27Y80.B6", "SLICE_X27Y80.A6"), ("SLICE_X22Y81.B5", "SLICE_X27Y80.B6"), (L, "SLICE_X22Y81.B5")])):
        sp_ = sep23(X, Oe); enlo = win(L, en)[0]; hsum = sum(win(v, u)[1] for v, u in path)
        lsum = sp_ + enlo; m0 = lsum - hsum; kf = (lsum - hsum) / (lsum + hsum)
        print("  c=%s reader %s from %s: Sep(->%s) %d + en lo %d = %d vs D-path hi %s = %d: margin %d ps, flip kappa %.3f" % (
            cc, L, "A" if X == A else "B", name, sp_, enlo, lsum, [win(v, u)[1] for v, u in path], hsum, m0, kf))
