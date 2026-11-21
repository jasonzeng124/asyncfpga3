#!/usr/bin/env python3
"""Shard B (UNTRUSTED data for shard C): every feedback LUT of the target's kernel cone, its feedback pin, the
copy-gate route of its feedback, the loop band (route + pin arc: sum FAST_MIN .. sum SLOW_MAX), and, from
simulation dumps, the shortest flipping forcing episode followed by a hold (SpecFb.fb_switch needs it >= the
loop's upper bound). usage: fbtable.py NET.json BND.json OUT.json DUMP...  """
import json, sys, subprocess, os, re
NETF, BNDF, OUT = sys.argv[1:4]; dumps = sys.argv[4:]
N = json.load(open(NETF)); g = N["gates"]; names = N["nodes"]; idx = {n: i for i, n in enumerate(names)}
B = json.load(open(BNDF)); ENV = set(idx[x] for x in B["env"]); bd = B["boundary"]
outs = [idx[bd[k]] for k in ("a_ack", "b_ack", "start_ack", "out0_req")] + [idx[x] for x in bd["out0_data"]]
cone, todo, seen = set(), list(outs), set(outs)
while todo:
    n = todo.pop()
    if n in ENV or n >= len(g): continue
    cone.add(n)
    for i in g[n]["ins"]:
        if i not in seen: seen.add(i); todo.append(i)
rows = {}
for gi in sorted(cone):
    G = g[gi]
    if G["k"] < 2: continue
    for j, n in enumerate(G["ins"]):
        m, ch = n, []
        while m < len(g) and g[m]["k"] == 1 and m != gi and len(ch) < 60: ch.append(m); m = g[m]["ins"][0]
        if m == gi:
            lo = G["arcs"][j]["fmin"] + sum(g[x]["arcs"][0]["fmin"] for x in ch)
            hi = G["arcs"][j]["smax"] + sum(g[x]["arcs"][0]["smax"] for x in ch)
            rows[G["name"]] = {"gate": gi, "init": G["init"], "k": G["k"], "fb_pin": j, "route": ch,
                               "loop_fast_min": lo, "loop_slow_max": hi, "min_episode": None}
            break
HERE = os.path.dirname(os.path.abspath(__file__))
for d in dumps:
    out = subprocess.run([sys.executable, "-I", os.path.join(HERE, "fbscan.py"), NETF, d, "0.5", "0.5", "25000"],
                         capture_output=True, text=True).stdout
    for m in re.finditer(r"episode (\d+) ps / sim loop (\d+) ps = [\d.]+\s+\(loop band \d+\.\.\d+ ps\)\s+(\S+)", out):
        e, nm = int(m.group(1)), m.group(3)
        if nm in rows and (rows[nm]["min_episode"] is None or e < rows[nm]["min_episode"]):
            rows[nm]["min_episode"] = e
json.dump({"note": "UNTRUSTED (tools-B/target/fbtable.py): feedback LUTs of the decoded target's kernel cone; "
                   "min_episode = shortest flipping forcing episode followed by a hold over the given simulation dumps "
                   "(sequential env, corner 0.5, mid-window delays); SpecFb.fb_switch needs episode >= loop_slow_max "
                   "(at the corner in use) for a clean switch",
           "nodes": rows}, open(OUT, "w"), indent=1)
act = [r for r in rows.values() if r["min_episode"] is not None]
print("feedback LUTs in the cone:", len(rows), "| with a flipping episode in the dumps:", len(act),
      "| episode < loop SLOW_MAX:", sum(1 for r in act if r["min_episode"] < r["loop_slow_max"]))
