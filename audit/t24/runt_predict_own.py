# T24: own prediction of runt_top's per-cell episode width w and loop, walking the ROUTED JSON netlist (net drivers,
# not the SDF's INTERCONNECT keys) and taking delays from the xray SDF.  For the cell under test inst[i].ce.dut.u (or
# inst[i].pl.u): for its logical a (I0) and b (I1) inputs, follow net -> driver; a LUT1 driver adds its IOPATH and the
# interconnect into its own input, recursively; a flop adds CK->Q plus its clock interconnect.  loop = IOPATH(a pin->O6)
# + interconnect(O6 -> q pin).  Columns at FAST_MIN, SLOW_MAX and band b (FAST_MIN + b (SLOW_MAX - FAST_MIN)).
# usage: runt_predict_own.py ROUTED_JSON XRAY_SDF [BAND]
import json, re, sys
m = list(json.load(open(sys.argv[1]))["modules"].values())[0]; band = float(sys.argv[3]) if len(sys.argv) > 3 else 0.288
cells = m["cells"]
drv = {b: (n, p) for n, c in cells.items() for p, bits in c["connections"].items() if c["port_directions"].get(p) == "output" for b in bits}
un = lambda s: s.replace("\\", "")
IC, IO, inst = {}, {}, None
for l in open(sys.argv[2]):
    mm = re.search(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):\d+:(\d+)\)", l)
    if mm: IC[(un(mm.group(1)), un(mm.group(2)))] = (int(mm.group(3)), int(mm.group(4))); continue
    mm = re.search(r"\(INSTANCE\s*([^)]*)\)", l)
    if mm: inst = un(mm.group(1)); continue
    mm = re.search(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):\d+:(\d+)\)", l)
    if mm and inst: IO[(inst, mm.group(1), mm.group(2))] = (int(mm.group(3)), int(mm.group(4)))
add = lambda x, y: (x[0] + y[0], x[1] + y[1])
def phys(cell, logical):                       # physical pin carrying logical input I<k>
    for k in range(1, 7):
        if logical in cells[cell]["attributes"].get("X_ORIG_PORT_A%d" % k, "").split(): return "A%d" % k
def arrive(cell, pin):
    net = cells[cell]["connections"][pin][0]; d, dp = drv[net]
    t = IC[(d + "/" + dp, cell + "/" + pin)]
    dt = cells[d]["type"]
    if dt in ("FDRE", "SLICE_FFX"):
        ck = [p for p in cells[d]["connections"] if p.upper() in ("C", "CK", "CLK")][0]
        cnet = cells[d]["connections"][ck][0]; cd, cdp = drv[cnet]
        return add(add(t, IO[(d, "CK", dp)]), IC[(cd + "/" + cdp, d + "/" + ck)]), 0
    ins = [p for p in cells[d]["connections"] if p.startswith("A") and cells[d]["connections"][p] and cells[d]["port_directions"][p] == "input"
           and not drv[cells[d]["connections"][p][0]][0].startswith("$PACKER")]
    assert len(ins) == 1, (d, ins)
    t2, h = arrive(d, ins[0])
    return add(add(t, IO[(d, ins[0], dp)]), t2), h + 1
bd = lambda v: v[0] + band * (v[1] - v[0])
print("instance\tkind_guess\tw_fastmin\tw_slowmax\tw_band\tloop_band\thops_a\thops_b")
for n in sorted(cells, key=lambda s: int(re.search(r"\[(\d+)\]", s).group(1)) if s.startswith("inst[") else -1):
    mm = re.match(r"inst\[(\d+)\]\.(ce\.dut|pl)\.u$", n)
    if not mm: continue
    pa, pb = phys(n, "I0"), phys(n, "I1")
    ta, ha = arrive(n, pa); tb, hb = arrive(n, pb); w = (tb[0] - ta[0], tb[1] - ta[1])
    if mm.group(2) == "ce.dut":
        pq = phys(n, "I2"); lp = add(IO[(n, pa, "O6")], IC[(n + "/O6", n + "/" + pq)]); lps = "%.0f" % bd(lp)
    else: lps = "-"
    print("%s\t%s\t%d\t%d\t%.0f\t%s\t%d\t%d" % (mm.group(1), "C" if mm.group(2) == "ce.dut" else "PULSE", w[0], w[1], bd(w), lps, ha, hb))
