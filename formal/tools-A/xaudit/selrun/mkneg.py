"""mkneg.py -- inputs of the E9SelRun negative controls (neg.sh), seed d slow.  (UNTRUSTED)

    XA_ARB=old python3 mkneg.py W MAP CERT OUTDIR

W: E8Mux's seed directory (skel.json, skel_slow.bands.json); MAP: E8SelC's map_d.json; CERT: this
probe's certificate sel_d_slow.json (certsel.py on the unmutated inputs).  Writes into OUTDIR:
  map_NEGack.json      E8SelC's NEGack mutation: the acknowledge of map entry 1 replaced by the request
                       wire of an unrelated channel (the last entry with another name and request)
  sel_NEGsib.json      the certificate with ONE junction row rewritten for literal
                       ulink_n_falseResult_77.ctl pin1 lit2 at cut 3/4 (junction = the steer LUT's
                       input arc), where the sibling arm (the merge ucond_br40.uack's direct filtered
                       pin, which does NOT pass that arc) claims the OWN arm's junction lag
                       (E8SelC's split lag; Events9PrefixSel.sibling_lag_neg on the real netlist)
  sel_POSsib.json      the same row with the honest sibling lag (lifted from the source): must pass
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from certsel import SelCert, Block  # noqa: E402

W, MAP, CERT, O = sys.argv[1:5]
m = json.load(open(MAP))
e1 = m["entries"][1]
far = [e for e in m["entries"] if e["name"] != e1["name"] and e["rq"] != e1["rq"]][-1]
print("NEGack", e1["node"], e1["pin"], e1["lit"], e1["ak"], "->", far["rq"])
e1["ak"] = far["rq"]
json.dump(m, open(O + "/map_NEGack.json", "w"))

sc = SelCert(W + "/skel.json", W + "/skel_slow.bands.json")
names = [n["name"] for n in sc.nodes]
cert = json.load(open(CERT))
assert [n["name"] for n in cert["nodes"]] == names
n = names.index("urig.udut.ulink_n_falseResult_77.ctl.u.u")
k, lit = 1, 2
ent = [e for e in cert["sel"]["entries"] if e["node"] == n and e["pin"] == k and e["lit"] == lit][0]
S = sc.nodes[n]["pins"][k]["src"]
f = sc.copies(n, k)[0]
cut = 2
B = Block(sc, S, f[cut + 1:])
B.judgements()
r = B.lag(ent["na"])
assert r is not None
jw, dj = r
# the certificate's log must contain the lines the block cites: sc rebuilt the same log (memo) plus
# possibly new lines; take sc's log
assert sc.C.log[:len(cert["log"])] == cert["log"], "log prefix differs"
own = [ln for ln in B.lines if ln["k"] == "juT" and ln["n"] == n][0]
for tag, lie in (("POSsib", False), ("NEGsib", True)):
    lines = json.loads(json.dumps(B.lines))
    for ln in lines:
        if ln["k"] == "jr3":
            for a in ln["arms"]:
                if a["dir"]:
                    print(tag, "sibling arm", a, "own-arm lag e", own["e"])
                    if lie:
                        a["e"] = own["e"]
    c = json.loads(json.dumps(cert))
    c["log"] = list(sc.C.log)
    c["sel"]["blocks"].append(dict(S=S, bot=f[cut + 1:], lines=lines))
    for e in c["sel"]["entries"]:
        if e["node"] == n and e["pin"] == k and e["lit"] == lit:
            e["jc"] = [dict(cut=cut, blk=len(c["sel"]["blocks"]) - 1, jw=jw)]
    json.dump(c, open(f"{O}/sel_{tag}.json", "w"))
    print(tag, "block lines", lines, "jw", jw, "dj (search)", dj)
