# T62: own composite pin delay bound of C's reset island: for each member w (t50/risl_dump.txt) and each pin of its
# driving gate, the summed slow-max delay of the pin arc plus the copy chain behind it (k=1, init=2 buffers), on my own
# decode (T10/T28 net.json). C claims every such sum <= M2 = 4,636 ps. usage: m2_own.py NET.json RISL_DUMP
import json, sys
gates = json.load(open(sys.argv[1]))["gates"]; drv = {g["out"]: g for g in gates}
mem = [int(l.split()[0]) for l in open(sys.argv[2])]
best = (0, None); nodrv = 0; hist = {}
for w in mem:
    g = drv.get(w)
    if g is None: nodrv += 1; continue
    for i, (n, a) in enumerate(zip(g["ins"], g["arcs"])):
        s = a["smax"]
        while n in drv and drv[n]["k"] == 1 and drv[n]["init"] == 2:
            s += drv[n]["arcs"][0]["smax"]; n = drv[n]["ins"][0]
        if s > best[0]: best = (s, (w, i))
print("members", len(mem), "without driver", nodrv, "max composite pin smax", best)
