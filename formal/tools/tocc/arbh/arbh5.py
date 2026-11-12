# arbh5 (UNTRUSTED): adversary specs per corner -> advspec_c<c>.json
#  advH: "D path fast, close path slow": gates of events strictly after a close and up to D's next input event (arbsets) at
#        (1-k)lo, the latches' D pins (1-k)lo, the latches' enable pins (1+k)hi; rest mid.
#  advA: every pin (1-k)lo except the latches' enable pins (1+k)hi (B's "enable route slow, all else fast", with kappa).
#  advO: OR hand-over at D: D<-X38Y53.A6 pin and gate X38Y53.A6 (1+k)hi; gates of events between X38Y53.A6(0) and
#        X38Y51.A6(1) and the D<-X38Y51.A6 pin (1-k)lo.
import sys, json
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/arbh/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[x]: x for x in range(len(nm))}
def E(n, k): return eid[(N[n], k)]
LAT = {"SLICE_X36Y63.B6": "SLICE_X36Y63.A6", "SLICE_X36Y68.B6": "SLICE_X36Y68.A6", "SLICE_X37Y47.B6": "SLICE_X37Y47.A6", "SLICE_X36Y69.B6": "SLICE_X36Y69.A6"}
Dn = "SLICE_X39Y53.B6"
A = json.load(open("/tmp/claude-0/arbh/arbsets_c%s.json" % cc))["loG"]
extra = set()
for en in LAT.values():
    for k in (1, 3):
        x = E(en, k); J = E("SLICE_X37Y55.C6", k)
        de = VCP[:, enode[x]] > ek[x]; an = VCP[J][enode] > ek
        extra |= set(nm[el[e][0]] for e in np.nonzero(de & an)[0])
loH = sorted((set(A) | extra) - set(LAT.values()))
enP = [[q, e] for q, e in LAT.items()]; dP = [[q, Dn] for q in LAT]
a = E("SLICE_X38Y53.A6", 0); b = E("SLICE_X38Y51.A6", 1)
de = VCP[:, enode[a]] > ek[a]; an = VCP[b][enode] > ek
mid_ = set(nm[el[e][0]] for e in np.nonzero(de & an)[0]) - {"SLICE_X38Y53.A6"}
spec = dict(advH=dict(loG=loH, loP=dP, hiP=enP), advA=dict(allfastk=True, hiP=enP),
            advO=dict(hiG=["SLICE_X38Y53.A6"], hiP=[[Dn, "SLICE_X38Y53.A6"]], loG=sorted(mid_), loP=[[Dn, "SLICE_X38Y51.A6"]]))
json.dump(spec, open("/tmp/claude-0/arbh/advspec_c%s.json" % cc, "w"))
print("c=%s advH loG %d gates: %s" % (cc, len(loH), loH)); print("  advO loG %s" % sorted(mid_))
