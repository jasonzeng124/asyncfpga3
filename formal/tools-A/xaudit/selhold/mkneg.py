"""mkneg.py -- inputs of the E8SelC negative controls (neg.sh).  python3 -I mkneg.py W MAP OUTDIR"""
import json
import sys

W, MAP, O = sys.argv[1:4]
cert = json.load(open(W + "/cert_slow.json"))
B = json.load(open(W + "/skel_slow.bands.json"))
# NEGhold: hi of the stage-pin route arc of ulink_n_falseResult_77.ctl pin 1, + 5000 ps
j = [i for i, n in enumerate(cert["nodes"]) if n["name"] == "urig.udut.ulink_n_falseResult_77.ctl.u.u"][0]
p = cert["nodes"][j]["pins"][1]
key = f"urig.udut.ulink_n_falseResult_77.ctl.u.u/I{p['ip']}"
print("NEGhold arc", key, B["arcs"][key], "-> hi + 5000")
B["arcs"][key] = [B["arcs"][key][0], B["arcs"][key][1] + 5000]
json.dump(B, open(O + "/skel_slow_NEGhold.bands.json", "w"))
# NEGmap: bus port of the first entry swapped for another entry's port
m = json.load(open(MAP))
e0 = m["entries"][0]
other = [e for e in m["entries"] if e["ws"] != e0["ws"]][0]
print("NEGmap", e0["node"], e0["pin"], e0["lit"], e0["ws"], "->", other["ws"])
e0["ws"] = other["ws"]
json.dump(m, open(O + "/map_d_NEGmap.json", "w"))
# NEGack: acknowledge of entry 1 replaced by the request wire of an unrelated channel
m = json.load(open(MAP))
e1 = m["entries"][1]
far = [e for e in m["entries"] if e["name"] != e1["name"] and e["rq"] != e1["rq"]][-1]
print("NEGack", e1["node"], e1["pin"], e1["lit"], e1["ak"], "->", far["rq"])
e1["ak"] = far["rq"]
json.dump(m, open(O + "/map_d_NEGack.json", "w"))
