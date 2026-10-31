"""UNTRUSTED (probe E8Arb): q-caused R0 edges vs HARB7's virtual R0 bands (cert8 output).
For each arbiter: real delay q -> R0 (ustate$LUT5 pin reading q: arc + lut) and q -> g_b
(ugrant pin reading q: arc + lut); the virtual R0 = OR of grants through F (R0 lut band) and
tap [lo, hi]: R0 edge must come between Flo+taplo and Fhi+taphi after the grant edge.
usage: r0chk.py skel.json bands.json cert.json"""
import json, sys
d = json.load(open(sys.argv[1])); m = d["modules"]["gcd_ctl"]; b = json.load(open(sys.argv[2]))
c = json.load(open(sys.argv[3]))
cells = m["cells"]
def ins(cn):
    k = int(cells[cn]["type"][3]); return [cells[cn]["connections"][f"I{i}"][0] for i in range(k)]
def outw(cn): return cells[cn]["connections"]["O"][0]
def band(cn, w):
    i = ins(cn).index(w); a = b["arcs"][f"{cn}/I{i}"]; l = b["cells"][cn]
    return (a[0] + l[0], a[1] + l[1])
nodes = c["nodes"]
worst = None
for j, n in enumerate(nodes):
    if not (n["virt"] and n["mg"]): continue
    R = n["name"][4:]                       # ...ustate$LUT5
    a = R.rsplit(".", 1)[0]
    q = outw(a + ".ustate$LUT6")
    dR = band(R, q)
    Flo, Fhi = n["F"]
    for p in n["pins"]:
        g = nodes[p["src"]]["name"][4:]     # ...ugrant$LUT5/6
        dg = band(g, q)
        rel_lo, rel_hi = dR[0] - dg[1], dR[1] - dg[0]
        need_lo, need_hi = Flo + p["lo"][0], Fhi + p["hi"][0]
        # fixed-delay (lower ends, as Wip/E8Hyp/sim0.py) relative delay:
        rel_fix = dR[0] - dg[0]
        ok_fix = need_lo <= rel_fix <= need_hi
        ok_box = need_lo <= rel_lo and rel_hi <= need_hi
        print(f"{a.split('udut.')[-1]:28s} {g[-4:]}: q->R0 {dR} q->g {dg} rel_fix {rel_fix:5d} box [{rel_lo},{rel_hi}]  virtual needs [{need_lo},{need_hi}]  fix {'ok' if ok_fix else 'VIOL'} box {'ok' if ok_box else 'VIOL'}")
