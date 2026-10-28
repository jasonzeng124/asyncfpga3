"""Auditor scan: every delay tuple in prjxray-db tile_type_*.json (pips,
wires, site pins, anything with a 4-list 'delay'/'res'-like timing) and every
(FAST_MIN,FAST_MAX,SLOW_MIN,SLOW_MAX)-shaped list; report min>max inversions."""
import json, sys, glob, os, collections
db = sys.argv[1]
inv = collections.Counter(); total = collections.Counter(); ex = {}
def walk(o, path, fn):
    if isinstance(o, dict):
        for k, v in o.items():
            walk(v, path + (k,), fn)
    elif isinstance(o, list) and len(o) == 4 and all(isinstance(x, (str, float, int)) for x in o):
        try: t = [float(x) for x in o]
        except ValueError: return
        key = path[-1]
        total[(fn, key)] += 1
        for a, b, lab in ((0, 1, "FAST"), (2, 3, "SLOW")):
            if t[a] > t[b]:
                inv[(fn, key, lab)] += 1
                ex.setdefault((fn, key, lab), []).append(("/".join(path[1:-1]), o))
files = sorted(glob.glob(os.path.join(db, "*.json")))
for f in files:
    walk(json.load(open(f)), (os.path.basename(f),), os.path.basename(f))
print("files scanned", len(files), "4-tuples", sum(total.values()))
print("4-tuple field names:", sorted({k for _, k in total}))
for k, n in sorted(inv.items()):
    print("INVERTED", k, n)
    for p, o in ex[k][:30]: print("   ", p, o)
