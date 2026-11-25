import sys, json
sys.path.insert(0, "/tmp/claude-0/bsub1/tocc")
from classify import load
C = load(); g = C["gates"]; nm = C["names"]; idx = {n: i for i, n in enumerate(nm)}
def rd(en):
    e = idx[en]; out = [[nm[n], en] for n, G in g.items() if any(p["src"] == e for p in G["pins"])]
    out += [[en, nm[p["src"]]] for p in g[e]["pins"] if p["live"] and p["src"] != e]
    return out
def dpins(q):
    i = idx[q]; fb, en = C["LATCH"][i]; pe = [p for p, v in en][0]
    return [[q, nm[p["src"]]] for j, p in enumerate(g[i]["pins"]) if p["live"] and j not in fb and j != pe and p["src"] not in C["const"]]
P = {}
P["A1_X34Y92C5_hold_allfast"] = {"slowpins": rd("SLICE_X34Y92.A6"), "allfast": True}
P["A1_X34Y92C5_hold_mid"] = {"slowpins": rd("SLICE_X34Y92.A6"), "fastpins": dpins("SLICE_X34Y92.C5")}
grp = open("grp_x22y87.txt").read().strip().split(",")
P["A2_X22Y87grp_reopen_pos1"] = {"fastpins": rd("SLICE_X22Y87.A6"), "pos": 1}
P["A2_X22Y87grp_reopen_mid"] = {"fastpins": rd("SLICE_X22Y87.A6"), "slowpins": sum((dpins(q) for q in grp), [])}
P["A3_X34Y65A5_hold_allfast"] = {"slowpins": rd("SLICE_X34Y66.A6"), "allfast": True}
P["A4_single_hold_allfast"] = {"slowpins": rd("SLICE_X36Y63.A6") + rd("SLICE_X36Y68.A6") + rd("SLICE_X37Y47.A6"), "allfast": True}
P["mid"] = {}
for k, v in P.items(): open("adv_%s.json" % k, "w").write(json.dumps(v))
print({k: (len(v.get("slowpins", [])), len(v.get("fastpins", []))) for k, v in P.items()})
