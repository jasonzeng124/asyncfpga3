import gzip, json, sys, statistics as st
d = json.load(gzip.open(sys.argv[1]))
routes = {r["route"] for r in d}
raw = [r["raw"] for r in d]; g = [r["g"] for r in d]
print("rows", len(d), "routes", len(routes))
print("raw min", min(raw), "median", st.median(raw)); print("guarded min", min(g), "violations", sum(r["viol"] for r in d))
mn = min(d, key=lambda r: r["raw"]); print("tightest raw row:", mn)
# early - late includes ua_k arc both sides (cancels). Raw also includes flat LUT arcs.
for r in sorted(d, key=lambda r: r["g"])[:4]: print("lowest guarded:", r["design"], r["arb"], r["client"], r["late"], r["early"], r["shared"], r["raw"], r["g"])
