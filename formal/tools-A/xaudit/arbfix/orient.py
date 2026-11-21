"""UNTRUSTED (probe E8ArbFix): per arbiter, the relative delay R0-term minus grant over the per-pin
bands, for the two edge causes the uncontested cell has (q flip; request edge), and whether R0 can
be modelled DOWNSTREAM of the grant (old structure, needs both lower ends >= 1), UPSTREAM of it
(both upper ends <= -1), or neither (needs the shadow core).  Bands: arc + lut per pin (A's
per-pin model).  usage: orient.py skel.json bands.json"""
import json, sys
d = json.load(open(sys.argv[1])); m = d["modules"]["gcd_ctl"]; b = json.load(open(sys.argv[2]))
cells = m["cells"]
def ins(cn):
    k = int(cells[cn]["type"][3]); return [cells[cn]["connections"][f"I{i}"][0] for i in range(k)]
def outw(cn): return cells[cn]["connections"]["O"][0]
def band(cn, w):
    i = ins(cn).index(w); a = b["arcs"][f"{cn}/I{i}"]; l = b["cells"][cn]
    return (a[0] + l[0], a[1] + l[1])
arbs = sorted({cn.rsplit(".", 1)[0] for cn in cells if cn.endswith(".ustate$LUT6")})
cnt = {"down": 0, "up": 0, "neither": 0}
for a in arbs:
    st, R = a + ".ustate$LUT6", a + ".ustate$LUT5"; q = outw(st)
    gs = [a + ".ugrant$LUT5", a + ".ugrant$LUT6"]
    rq = [w for w in ins(gs[0]) if isinstance(w, int) and w != q]
    out = []
    for g in gs:
        # which request does g read with effect: try both, keep the one also read by R
        for r in rq:
            if r not in ins(g) or r not in ins(R): continue
            dq = (band(R, q)[0] - band(g, q)[1], band(R, q)[1] - band(g, q)[0])
            dr = (band(R, r)[0] - band(g, r)[1], band(R, r)[1] - band(g, r)[0])
            lo, hi = min(dq[0], dr[0]), max(dq[1], dr[1])
            o = "down" if lo >= 1 else ("up" if hi <= -1 else "neither")
            out.append((g[-4:], r, dq, dr, o))
    # pair each grant with its request: g1 reads r1 (I0), g2 reads r2 (I1) in bd_arbiter
    sel = [x for x in out if (x[0] == "LUT5" and x[1] == ins(gs[0])[0]) or (x[0] == "LUT6" and x[1] == ins(gs[1])[1])]
    for x in sel: cnt[x[4]] += 1
    print(f"{a.split('udut.')[-1]:24s} " + " | ".join(f"{x[0]} q-rel {x[2]} r-rel {x[3]} {x[4]}" for x in sel))
print("orientation per grant:", cnt)
