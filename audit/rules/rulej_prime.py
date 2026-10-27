# Own re-evaluation of rule J survey rows with site-pin delays (prjxray-db, own extraction in sitepin.py)
# and LUT arcs read correctly as (fast)(slow) corners. SDF arcs are flat 124 ps (verified in pnr/ own route).
# early = wires_e + 3*124 (ustate, ugrant, ua_k g-arc); late = wire_a + 124 (ua_k A0-arc).
import gzip, json, sys, collections
d = json.load(gzip.open(sys.argv[1]))
ARC = 124
SP_LO = {1:145, 2:141, 3:88, 4:73, 5:31, 6:0}     # fast_min over CLBLL/CLBLM
SP_HI = {1:540, 2:520, 3:377, 4:317, 5:137, 6:22}  # slow_max over CLBLL/CLBLM
SPs_HI = {1:516, 2:507, 3:344, 4:284, 5:112, 6:5}  # CLBLL slow max (consistent slow corner, CLBLL)
ARC_FMIN = {"O6": 45, "O5": 42}
ARC_SMAX = {"O6": 124, "O5": 157}
assign = {"worst": dict(PS=5, PQ=5, PG=6, PA=1), "identity": dict(PS=5, PQ=3, PG=1, PA=2), "best": dict(PS=1, PQ=1, PG=2, PA=6)}
out = collections.defaultdict(list)
for r in d:
    we = r["early"] - 3*ARC; wa = r["late"] - ARC; c = r["shared"]
    gport = "O6" if r["client"] == 2 else "O5"
    for name, a in assign.items():
        # full box: early at 0.772 x SDF wires + fast-min pins/arcs; late at 1.155 x SDF wire + slow-max pin
        box = 0.772*(we - c) + SP_LO[a["PS"]] + SP_LO[a["PQ"]] + SP_LO[a["PG"]] + 45 + ARC_FMIN[gport] \
              - 1.155*(wa - c) - SP_HI[a["PA"]]
        # consistent slow corner (SDF wires as is, slow-max pins and arcs, CLBLL)
        slow = (we - wa) + SPs_HI[a["PS"]] + SPs_HI[a["PQ"]] + SPs_HI[a["PG"]] + 124 + ARC_SMAX[gport] - SPs_HI[a["PA"]]
        out[("box", name)].append((box, r)); out[("slow", name)].append((slow, r))
for k in sorted(out):
    v = sorted(out[k], key=lambda x: x[0])
    neg = sum(x[0] <= 0 for x in v)
    gcd = [x for x in v if x[1]["design"] == "gcd_hw[mine v4+pads]"]
    print(f"{k[0]:5s} {k[1]:9s} min {v[0][0]:+7.0f} ({v[0][1]['design']} {v[0][1]['client']}) rows<=0: {neg}/{len(v)}  gcd_hw v4 8 seeds min {gcd[0][0]:+.0f}")
t = [x for x in out[("box","worst")] if x[1]["raw"] == 618][0]; print("tightest raw row (+618) box/worst:", round(t[0]))
t = [x for x in out[("slow","worst")] if x[1]["raw"] == 618][0]; print("tightest raw row (+618) slow/worst:", round(t[0]))
nopin = min(0.772*(r["early"]-372-r["shared"]) + 45 + (45 if r["client"]==2 else 42) - 1.155*(r["late"]-124-r["shared"]) for r in d if r["raw"]==618)
print("tightest raw row box without pins:", round(nopin))
