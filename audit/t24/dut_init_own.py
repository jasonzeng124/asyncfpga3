# T24: does the BITSTREAM implement each runt_top cell under test as intended?  For every TEST/NEG/LONG cell (bd_c2n,
# LUT6 INIT 64'h00B2..) and PULSE cell (LUT3 8'h02 = a.~b.~clr): take its BEL and physical pin map from the routed JSON
# (X_ORIG_PORT_Ak attributes), its 64-bit O6 INIT from my own read-back FASM, and evaluate the read-back truth table on
# the physical pins for every value of the logical inputs and of every unused physical pin.
# usage: dut_init_own.py ROUTED_JSON FROMBIT_FASM TILEGRID_JSON
import json, re, sys, itertools, collections
m = list(json.load(open(sys.argv[1]))["modules"].values())[0]
bits = collections.defaultdict(set)
for l in open(sys.argv[2]):
    mm = re.match(r"(\S+)\.([A-D])LUT\.INIT(?:\[(\d+)\])?\s*$", l.strip())
    if mm: bits[(mm.group(1), mm.group(2))].add(int(mm.group(3) or 0))
site2 = {}
for t, v in json.load(open(sys.argv[3])).items():
    ss = sorted(v.get("sites", {}), key=lambda s: int(re.search(r"X(\d+)", s).group(1)))
    for i, s in enumerate(ss):
        if s.startswith("SLICE_"): site2[s] = "%s.%s_X%d" % (t, v["sites"][s], i)
def want(kind, a, b, q, r):
    if kind == "PULSE": return int(a and not b and not r)
    return int(((a and not b) or (q and not (b and not a))) and not r)   # 0xB2 rows, rst on I3 clears
assert all(want("C", a, b, q, 0) == (0xB2 >> (a + 2*b + 4*q)) & 1 for a in (0,1) for b in (0,1) for q in (0,1))
res = collections.Counter(); bad = []
for n, c in m["cells"].items():
    mm = re.match(r"inst\[(\d+)\]\.(ce\.dut|pl)\.u$", n)
    if not mm: continue
    kind = "PULSE" if mm.group(2) == "pl" else "C"
    bel = c["attributes"]["NEXTPNR_BEL"]; site, lut = bel.split("/"); L = lut[0]
    init = bits[(site2[site], L)]
    lp = {}                                            # logical I-index -> physical pin number
    for k in range(1, 7):
        for x in c["attributes"].get("X_ORIG_PORT_A%d" % k, "").split():
            lp[int(x[1:])] = k
    names = {0: "a", 1: "b", 2: "q" if kind == "C" else "r", 3: "r"}
    used = set(lp.values()); free = [k for k in range(1, 7) if k not in used]
    ok = True
    for vals in itertools.product((0, 1), repeat=len(lp)):
        lv = dict(zip(sorted(lp), vals))
        if any(lv[i] for i in lv if i >= 4): continue    # I4/I5 of bd_c2n are tied 1'b0 in the RTL (GND-driven pins)
        v = {names[i]: lv[i] for i in lv if i < 4}
        w = want("PULSE" if kind == "PULSE" else "C", v["a"], v["b"], v.get("q", 0), v["r"])
        for fv in itertools.product((0, 1), repeat=len(free)):
            phys = {lp[i]: lv[i] for i in lv}; phys.update(dict(zip(free, fv)))
            idx = sum(phys[k] << (k - 1) for k in range(1, 7))
            if (idx in init) != bool(w): ok = False
    res[(kind, ok)] += 1
    if not ok: bad.append((n, bel, sorted(lp.items())))
print("cells checked:", dict(res)); print("mismatches:", bad[:10])
