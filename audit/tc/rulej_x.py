#!/usr/bin/env python3
"""Auditor's rule J recomputation with per-pin prjxray delays (own xrc.py Elmore + site pins + OUTMUX).

Structure exactly as arb_fork.py (A0 -> ua_k vs A0 -> ustate -> ugrant_k -> ua_k), sink cells/pins resolved
the same way.  Per arc we take prjxray corner values (ps): [FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX].
Margins (early side must exceed late side; positive = safe):
  slow  : early@SLOW_MIN - late@SLOW_MAX             (one corner, H_ONE_CORNER)
  fast  : early@FAST_MIN - late@FAST_MAX
  slowG : 0.772*early@SLOW_MIN - 1.155*late@SLOW_MAX (project band on the corner)
  fastG : 0.772*early@FAST_MIN - 1.155*late@FAST_MAX
  mix   : early@FAST_MIN - late@SLOW_MAX              (fast-early / slow-late box)
each WITH the exact shared credit (both sides measured from the branch point of A0's RC tree, so the
shared elements cancel) -- suffix x -- and WITHOUT (from A0's driver) -- suffix 0.
Also: c_proj (arb_fork's pip-count estimate, SDF units) vs c_exact (shared fraction of the SDF number,
taken as prjxray SLOW_MAX shared/total of each sink, min of the two -- same definition as the claim)."""
import sys, re, json
sys.path.insert(0, "/home/user/asyncfpga3/audit/tc")
import xrc

LO, HI = 0.772, 1.155


def main(odir, tag):
    R = xrc.Route(odir)
    cells = R.cells
    arbs = sorted(cn[:-len(".ustate$LUT6")] for cn in cells if cn.endswith(".ustate$LUT6"))
    fanout = {b: len(v) for b, v in R.sinks_of.items()}

    def pins(cn):
        c = cells[cn]
        return {p: c["connections"][p][0] for p, d in c["port_directions"].items() if d == "input" and c["connections"].get(p)}

    def out_bit(cn):
        c = cells[cn]
        for p in ("O6", "O5", "O"):
            if p in c["connections"] and c["port_directions"].get(p) == "output":
                return p, c["connections"][p][0]
        return None, None

    def wire(cn, p):
        n, s = R.sink_of_cellpin(cn, p)
        if s is None:
            raise KeyError(f"unresolved sink {cn}/{p} ({n.why if n else 'nonet'})")
        return n, s

    def lut(cn, p, out):
        v = R.lut_arc(cn, p, out)
        if v is None:
            raise KeyError(f"no lut arc {cn}/{p}->{out}")
        return v

    rows = []
    for a in arbs:
        st = a + ".ustate$LUT6"
        _, q = out_bit(st)
        for k, gcell in ((1, a + ".ugrant$LUT5"), (2, a + ".ugrant$LUT6")):
            ua = a + f".ua{k}.u"
            try:
                gport, g = out_bit(gcell)
                if gcell.endswith("$LUT5") and "O5" in cells[gcell]["connections"]:
                    gport, g = "O5", cells[gcell]["connections"]["O5"][0]
                pu, ps, pg = pins(ua), pins(st), pins(gcell)
                common = (set(pu.values()) & set(ps.values())) - {q, g}
                ext = [b for b in common if not R.driver.get(b, ("", ""))[0].startswith(a + ".")]
                a0 = min(ext, key=lambda b: fanout[b])
                dc, dp = R.driver[a0]
                ua_a0 = next(p for p, b in pu.items() if b == a0)
                ua_g = next(p for p, b in pu.items() if b == g)
                st_a0 = next(p for p, b in ps.items() if b == a0)
                g_q = next(p for p, b in pg.items() if b == q)
                n0, s_ua = wire(ua, ua_a0)
                _, s_st = wire(st, st_a0)
                _, s_q = wire(gcell, g_q)
                _, s_g = wire(ua, ua_g)
                # branch point: deepest common element of the two sink paths
                pa, pb = s_ua["path"], s_st["path"]
                ncom = 0
                for x, y in zip(pa, pb):
                    if x != y:
                        break
                    ncom += 1
                if ncom:
                    shared = n0.elems[pa[ncom - 1]]["acc"]
                else:
                    shared = [0.0] * 4  # different outpins (O6 direct vs MUX): branch at the LUT output
                late_full = [s_ua["d"][j] + lut(ua, ua_a0, "O6")[j] for j in range(4)]
                early_full = [s_st["d"][j] + lut(st, st_a0, "O6")[j] + s_q["d"][j] + lut(gcell, g_q, gport)[j]
                              + s_g["d"][j] + lut(ua, ua_g, "O6")[j] for j in range(4)]
                # SDF numbers (rule J's own)
                d_ua = R.ic[(f"{dc}/{dp}", f"{ua}/{ua_a0}")]
                d_st = R.ic[(f"{dc}/{dp}", f"{st}/{st_a0}")]
                sdf_late = d_ua + R.io[(ua, ua_a0, "O6")]
                sdf_early = (d_st + R.io[(st, st_a0, "O6")] + R.ic[(f"{st}/O6", f"{gcell}/{g_q}")] + R.io[(gcell, g_q, gport)]
                             + R.ic[(f"{gcell}/{gport}", f"{ua}/{ua_g}")] + R.io[(ua, ua_g, "O6")])
            except (KeyError, StopIteration, ValueError) as e:
                rows.append(dict(seed=tag, arb=a, k=k, err=str(e)[:120]))
                continue
            # arb_fork's pip-count c
            c_proj = pipcount(R, a0, ua, st, d_ua, d_st)
            # exact fraction in SDF units: shared/total at SLOW_MAX per sink, min of the two
            c_x = int(min(d_ua * shared[3] / s_ua["d"][3], d_st * shared[3] / s_st["d"][3])) if ncom else 0
            E, L = early_full, late_full
            Ex = [E[j] - shared[j] for j in range(4)]
            Lx = [L[j] - shared[j] for j in range(4)]
            r = dict(seed=tag, arb=a, k=k, a0_driver=dc, ua_pin=s_ua["pin"], st_pin=s_st["pin"], g_pin=s_g["pin"],
                     a0_out=s_ua["outpin"] + "/" + s_st["outpin"],
                     sdf_raw=sdf_early - sdf_late, sdf_guard=int(LO * (sdf_early - c_proj) - HI * (sdf_late - c_proj)),
                     c_proj=c_proj, c_x=c_x, shared=[round(x) for x in shared],
                     A0_ua_sdf=d_ua, A0_ua_prjx=[round(x) for x in s_ua["d"]])
            for sfx, e_, l_ in (("x", Ex, Lx), ("0", E, L)):
                r["slow" + sfx] = round(e_[2] - l_[3])
                r["fast" + sfx] = round(e_[0] - l_[1])
                r["slowG" + sfx] = round(LO * e_[2] - HI * l_[3])
                r["fastG" + sfx] = round(LO * e_[0] - HI * l_[1])
                r["mix" + sfx] = round(e_[0] - l_[3])
                r["mixG" + sfx] = round(LO * e_[0] - HI * l_[3])
            rows.append(r)
    return rows


def pipcount(R, bit, sink_a, sink_b, d_a, d_b):
    """arb_fork.shared_ps, re-implemented"""
    r = R.routes.get(bit)
    f = r.split(";")
    parent = {}
    for i in range(0, len(f) - 2, 3):
        w, pip = f[i], f[i + 1]
        parent[w] = pip.split("->")[0] if "->" in pip else None

    def path_to(cn):
        site, lut = R.cells[cn]["attributes"]["NEXTPNR_BEL"].split("/")
        sink = re.compile(r"^SITEWIRE/%s/%s[1-6]$" % (re.escape(site), lut[0]))
        hits = [w for w in parent if sink.match(w)]
        if len(hits) != 1:
            return None
        out, w, seen = [], hits[0], set()
        while w is not None and w not in seen:
            seen.add(w); out.append(w); w = parent.get(w)
        return out[::-1]
    pa, pb = path_to(sink_a), path_to(sink_b)
    if not pa or not pb:
        return 0
    n = 0
    for x, y in zip(pa, pb):
        if x != y:
            break
        n += 1
    ha, hb = max(len(pa) - 1, 1), max(len(pb) - 1, 1)
    sh = max(n - 1, 0)
    return int(min(d_a * sh / ha, d_b * sh / hb))


if __name__ == "__main__":
    out = []
    for arg in sys.argv[1:]:
        tag, odir = arg.split("=", 1)
        out += main(odir, tag)
    cols = ["seed", "arb", "k", "ua_pin", "st_pin", "g_pin", "a0_out", "sdf_raw", "sdf_guard", "c_proj", "c_x",
            "shared", "slowx", "fastx", "slowGx", "fastGx", "mixx", "mixGx", "slow0", "fast0", "slowG0", "fastG0", "mix0", "mixG0"]
    print("\t".join(cols))
    for r in out:
        if "err" in r:
            print(f"{r['seed']}\t{r['arb']}\t{r['k']}\tERR {r['err']}")
        else:
            print("\t".join(str(r[c]) for c in cols))
