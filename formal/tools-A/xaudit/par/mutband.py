"""mutband.py CERT.json OUT.json NODE_SUBSTR PIN DELTA -- control NEGband (probe E9Par).

Lower the band of pin PIN of the first virtual node whose name contains NODE_SUBSTR by DELTA ps
(lo and hi of every copy, floored at 1) in a cert9p certificate, leaving every log line as it is.
Prints, from the rule (Events9Par.ParOK, recomputed here from the mutated bands), which `par`
lines must now fail: those whose pair reads that pin on the z side (z = the mutated node) and
whose lag no longer covers hiF y + hiC y q i - loF z - loC z p i."""
import json
import sys

c = json.load(open(sys.argv[1]))
sub, pin, delta = sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
nodes = c["nodes"]
k = next(i for i, n in enumerate(nodes) if n.get("virt") and sub in n["name"])
p = nodes[k]["pins"][pin]
p["lo"] = [max(1, v - delta) for v in p["lo"]]
p["hi"] = [max(1, v - delta) for v in p["hi"]]
json.dump(c, open(sys.argv[2], "w"))


def F(n):
    return nodes[n].get("F", [1, 1])


bad = []
for i, ln in enumerate(c["log"]):
    if ln["k"] != "par":
        continue
    z, y, e, pm = ln["z"], ln["y"], ln["e"], ln["pm"]
    ok = F(y)[1] <= e + F(z)[0]
    for q, py in enumerate(nodes[y]["pins"]):
        pz = nodes[z]["pins"][pm[q]]
        for lz, hy in zip(pz["lo"], py["hi"]):
            ok = ok and F(y)[1] + hy <= e + F(z)[0] + lz
    if not ok:
        bad.append(i)
print(f"mutated {nodes[k]['name']} pin{pin} by -{delta} ps; par lines that must fail ParOK: {len(bad)} {bad}")
