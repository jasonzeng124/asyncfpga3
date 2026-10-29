#!/usr/bin/env python3
"""For each named wire, walk the routed JSON's ROUTING tree (net containing it) upstream to its root and downstream
to its sinks.  usage: trace_json.py ROUTED_JSON WIRE..."""
import json, sys, collections
j = json.load(open(sys.argv[1])); m = list(j['modules'].values())[0]
for w in sys.argv[2:]:
    for n, v in m['netnames'].items():
        r = v.get('attributes', {}).get('ROUTING', '')
        if w not in r: continue
        f = r.split(';'); up = {}; down = collections.defaultdict(list)
        for i in range(0, len(f) - 2, 3):
            dst, pip = f[i], f[i + 1]
            if '->' in pip:
                s, d = pip.split('->'); up[dst] = s; down[s].append(dst)
        if w not in up and w not in down: continue
        path = [w]
        while path[-1] in up: path.append(up[path[-1]])
        sinks, st = [], [w]
        while st:
            x = st.pop()
            if down.get(x): st += down[x]
            else: sinks.append(x)
        print(f"{w}  net {n}\n   upstream: {' <- '.join(path)}\n   sinks: {sinks}")
