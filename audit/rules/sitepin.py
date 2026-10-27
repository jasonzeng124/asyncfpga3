# Own extraction of CLB LUT input site-pin delays from prjxray-db (ns: fast_min, fast_max, slow_min, slow_max)
import json, re, sys
D = "/root/audit-tc/openxc7/share/nextpnr/prjxray-db/zynq7"
agg = {}
for t in ["CLBLL_L", "CLBLL_R", "CLBLM_L", "CLBLM_R"]:
    d = json.load(open(f"{D}/tile_type_{t}.json"))
    for s in d["sites"]:
        for p, v in s["site_pins"].items():
            m = re.fullmatch(r"([A-D])([1-6])", p)
            if not m or not v or "delay" not in v: continue
            dl = [float(x) for x in v["delay"]]
            k = int(m.group(2))
            lo, hi = agg.get(k, (9, 0))
            agg[k] = (min(lo, dl[0]), max(hi, dl[3]))
for k in sorted(agg): print(f"A{k}: fast_min {agg[k][0]*1000:.0f} ps  slow_max {agg[k][1]*1000:.0f} ps")
