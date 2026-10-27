import gzip, json, sys, collections
d = json.load(gzip.open(sys.argv[1]))
by = collections.defaultdict(list)
for r in d:
    if r["design"].startswith("gcd_hw"): by[(r["design"], r["route"].split("/")[-2])].append(r)
for k, v in sorted(by.items()):
    print(k, "rows", len(v), "min raw", min(x["raw"] for x in v), "min guarded", min(x["g"] for x in v))
