"""UNTRUSTED (probe E8Arb): per arbiter, B's loop L (ustate q pin: arc+lut, hi), the read skew S of
the request / A0 pins over the 4 LUT outputs, the window W = L + S, and the q-caused R0 relative
delay range vs HARB7's virtual R0 need (disjoint = violated for EVERY delay choice in the bands).
usage: wchk.py skel.json bands.json cert.json
E8ArbFix: on a cert with arb_core = fix, checks the corrected core instead (see the branch below)."""
import json, sys
d = json.load(open(sys.argv[1])); m = d["modules"]["gcd_ctl"]; b = json.load(open(sys.argv[2]))
c = json.load(open(sys.argv[3])); cells = m["cells"]
def ins(cn):
    k = int(cells[cn]["type"][3]); return [cells[cn]["connections"][f"I{i}"][0] for i in range(k)]
def outw(cn): return cells[cn]["connections"]["O"][0]
def band(cn, w):
    i = ins(cn).index(w); a = b["arcs"][f"{cn}/I{i}"]; l = b["cells"][cn]
    return (a[0] + l[0], a[1] + l[1])
nodes = c["nodes"]; dis = 0; tot = 0
if c.get("arb_core") == "fix":
    # probe E8ArbFix: the corrected core (events4/model.py build_arb_fix).  For every pair
    # (grant g_b, R0) the q-caused relative delay R0 - g_b of the core, read from ONE ctl edge:
    # [Psh_lo + 2 - Pg_hi, Psh_hi + 2 - Pg_lo] (shadow ctl pin, 2 merge/tap steps; grant ctl pin),
    # must contain the real one [Dq(R0)lo - Dq(g)hi, Dq(R0)hi - Dq(g)lo]; and the lower end
    # A0 -> X of the core (ctl lo + 1 + P_lo + 1 [+ 2]) must not exceed the real DA0lo + Dq(X)lo (D2).
    byname = {n["name"]: n for n in nodes}
    bad = 0; tot = 0
    for n in nodes:
        if not (n["virt"] and n["mg"]): continue
        R = n["name"][4:]; a = R.rsplit(".", 1)[0]
        st = a + ".ustate$LUT6"; q = outw(st)
        ctl = byname["vctl:" + st]; loc = ctl["pins"][0]["lo"][0]
        rstw = m["ports"]["rig_rst"]["bits"][0]
        a0 = [w for w in ins(st) if isinstance(w, int) and w not in ins(a + ".ugrant$LUT6") and w not in (q, rstw)]
        da0 = band(st, a0[0])[0] if a0 else None
        rows = []
        for p in n["pins"]:
            sh = nodes[p["src"]]; bi = int(sh["name"][-1]); g = a + (".ugrant$LUT5" if bi == 0 else ".ugrant$LUT6")
            gn = byname["arb:" + g]
            Pg = (gn["pins"][1]["lo"][0], gn["pins"][1]["hi"][0]); Ps = (sh["pins"][1]["lo"][0], sh["pins"][1]["hi"][0])
            real = (band(R, q)[0] - band(g, q)[1], band(R, q)[1] - band(g, q)[0])
            virt = (Ps[0] + 2 - Pg[1], Ps[1] + 2 - Pg[0])
            ok1 = virt[0] <= real[0] and real[1] <= virt[1]
            lg = loc + 1 + Pg[0] + 1; ls = loc + 1 + Ps[0] + 1 + 2
            ok2 = da0 is not None and lg <= da0 + band(g, q)[0] and ls <= da0 + band(R, q)[0]
            tot += 1; bad += (not ok1) + (not ok2)
            rows.append(f"g{bi+1} rel real [{real[0]},{real[1]}] core [{virt[0]},{virt[1]}]{'' if ok1 else ' NOT COVERED'}"
                        f" A0->g {lg}<={da0 + band(g, q)[0]} A0->R0 {ls}<={da0 + band(R, q)[0]}{'' if ok2 else ' D2 VIOLATED'}")
        print(f"{a.split('udut.')[-1]:24s} | " + " | ".join(rows))
    print(f"corrected core: {tot} grant/R0 pairs, {bad} failures (relation not covered or lower end late)")
    sys.exit(0)
for j, n in enumerate(nodes):
    if not (n["virt"] and n["mg"]): continue
    R = n["name"][4:]; a = R.rsplit(".", 1)[0]
    st = a + ".ustate$LUT6"; q = outw(st)
    rst = [w for w in ins(st) if isinstance(w, int)]
    rq = [w for w in ins(a + ".ugrant$LUT6") if isinstance(w, int) and w != q]
    L = band(st, q)[1]
    reads = [band(cn, w) for cn in (st, R, a + ".ugrant$LUT5", a + ".ugrant$LUT6") for w in rq if w in ins(cn)]
    S = max(x[1] for x in reads) - min(x[0] for x in reads)
    rows = []
    dR = band(R, q)
    for p in n["pins"]:
        g = nodes[p["src"]]["name"][4:]; dg = band(g, q)
        lo, hi = dR[0] - dg[1], dR[1] - dg[0]; nlo, nhi = n["F"][0] + p["lo"][0], n["F"][1] + p["hi"][0]
        disj = hi < nlo or lo > nhi; dis += disj; tot += 1
        rows.append(f"{g[-4:]} rel [{lo},{hi}] need [{nlo},{nhi}]{' DISJOINT' if disj else ''}")
    print(f"{a.split('udut.')[-1]:24s} L {L:5d} S {S:5d} W {L+S:5d} | " + " | ".join(rows))
print(f"q-caused R0 relation disjoint from the virtual band: {dis}/{tot}")
