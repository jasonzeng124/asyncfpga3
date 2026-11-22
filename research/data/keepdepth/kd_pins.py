import re, sys
def depths(p):
    v = open(p).read(); out = {}
    for m in re.finditer(r"\n\s*(bd_link|bd_pipe)\s*(#\((.*?)\))?\s*(ulink_\w+)\s*\(", v, re.S):
        n = re.search(r"\.N\((\d+)\)", m.group(3) or "") if m.group(1) == "bd_pipe" else None
        out[m.group(4)] = int(n.group(1)) if n else 1
    return out
base, new = depths(sys.argv[1]), depths(sys.argv[2])
env = dict(x.split("=", 1) for x in sys.argv[3].split() if "=" in x)
have = dict(y.split("=") for y in env.get("BDC_LINK_DEPTHS", "").split(",") if "=" in y)
keep = {l: d for l, d in base.items() if l in new and new[l] < d}
if not keep:
    sys.exit(0)
for l, d in keep.items():
    have[l] = str(max(d, int(have.get(l, 0))))
env["BDC_LINK_DEPTHS"] = ",".join("%s=%s" % kv for kv in sorted(have.items()))
print(" ".join("%s=%s" % kv for kv in env.items()) + "\t" + " ".join("%s:%d->%d" % (l, new[l], d) for l, d in sorted(keep.items())))
