"""UNTRUSTED (probe E8Arb): per arbiter, B's loop L (ustate q pin: arc+lut, hi), the read skew S of
the request / A0 pins over the 4 LUT outputs, the window W = L + S, and the q-caused R0 relative
delay range vs HARB7's virtual R0 need (disjoint = violated for EVERY delay choice in the bands).
usage: wchk.py skel.json bands.json cert.json"""
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
