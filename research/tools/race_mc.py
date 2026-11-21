#!/usr/bin/env python3
"""race_mc.py ROUTED_JSON ARCS_TSV SPEC [N] -- how often the delay model (bench_gate.sh draw:K) loses one named race,
by Monte Carlo over the model's own random parts, without a simulation.

A race is two paths that start at one launch and end at one cell output: S (the side that must arrive FIRST, e.g. a
steer's condition) and F (the side that must arrive LAST, e.g. the steer's request).  The margin is F - S at the end.
SPEC is adv_sdf.py's format, of which only these lines are read:

    S  KIND  SRC_REGEX  DST_REGEX      an arc on the early-required path (KIND IC or IO)
    F  KIND  SRC_REGEX  DST_REGEX      an arc on the late path
    chain  INST_REGEX                  instances in the model's "chains" class (default: bench_gate.sh's
                                       '\\.chain\\.g\\[\\d+\\]\\.u$'); an IO arc of such an instance, and an IC arc INTO it,
                                       takes the chains band, every other arc the "rest" band

Each S / F line must match exactly one arc in ARCS_TSV (cells/gls/fid/xray_delay.py --arcs: FAST_MIN / FAST_MAX /
SLOW_MIN / SLOW_MAX per arc); the path is the sum of its arcs.

The model, exactly as cells/gls/gen.py draws it under bench_gate.sh draw:K (GLS_SDF_FIELD=band, GLS_SCATTER=0.126,
GLS_SCATTER_MODE=wire, GLS_SCATTER_REGION=0.02, GLS_REGION_SLICES=10; JOURNAL 2026-11-16):
  * an arc's base delay = FAST_MIN + band * (SLOW_MAX - FAST_MIN), band = the chains band XC for a chain instance (and
    the wires into it), else the rest band XR; XC, XR independent, uniform on [0.20, 0.31];
  * an INTERCONNECT arc times the mean of one factor per pip on its own route branch (1 + 0.126 N(0,1) per pip,
    one draw per pip and model point, shared by every sink whose branch runs through that pip), times its sink's
    region factor;
  * an IOPATH arc times its own factor (1 + 0.126 N(0,1)), times its instance's region factor;
  * a region is a 10 x 10 block of slice sites, factor 1 + 0.02 N(0,1).
The pips of each IC arc come from the routed JSON (gen.py's WireModel walk); an arc whose branch cannot be found falls
back, as in gen.py, to one factor of its own.  Prints the margin's mean, sd, quantiles, the fraction of model points
below 0 / 20 / 50 ps, and the same at the four band corners with no scatter.
"""
import json
import math
import random
import re
import statistics as st
import sys


def load_spec(path):
    rules, chain = [], re.compile(r".*\.chain\.g\[\d+\]\.u$")
    for ln in open(path):
        w = ln.split()
        if not w or w[0].startswith("#"):
            continue
        if w[0] in ("S", "F"):
            rules.append((w[0], w[1], re.compile(w[2]), re.compile(w[3]), ln.strip()))
        elif w[0] == "chain":
            chain = re.compile(w[1])
    return rules, chain


def main():
    rj, tsv, specf = sys.argv[1:4]
    n = int(sys.argv[4]) if len(sys.argv) > 4 else 200000
    rules, chain = load_spec(specf)
    arcs, hdr = [], None
    for ln in open(tsv):
        f = ln.rstrip("\n").split("\t")
        if hdr is None:
            hdr = f
            continue
        d = dict(zip(hdr, f))
        if d["kind"] in ("IC", "IO"):
            arcs.append(d)
    top = json.load(open(rj))["modules"]["top"]
    cells = top["cells"]
    routes = {}
    for nn in top["netnames"].values():
        r = nn.get("attributes", {}).get("ROUTING")
        if r and nn["bits"]:
            routes.setdefault(nn["bits"][0], r)

    def branch(dst):
        """the pips on the route branch into dst (gen.py WireModel.factor's walk), or None"""
        cell, _, pin = dst.rpartition("/")
        c = cells.get(cell)
        if c is None or pin not in c["connections"]:
            return None
        bit = c["connections"][pin][0]
        if bit not in routes:
            return None
        fl = routes[bit].split(";")
        par = {fl[i]: fl[i + 1] for i in range(0, len(fl) - 2, 3)}
        bel = c["attributes"].get("NEXTPNR_BEL", "")
        if "/" not in bel:
            return None
        site, b = bel.split("/")[:2]
        pre = "SITEWIRE/%s/" % site
        if b.endswith("LUT"):
            sinks = [w for w in par if w.startswith(pre) and re.match(r"^%s[1-6]$" % b[0], w[len(pre):])]
        else:
            sinks = [w for w in par if w.startswith(pre + pin)] or \
                    [w for w in par if w.startswith(pre) and par[w] and
                     not any(par.get(x, "").split("->")[0] == w for x in par)]
        if len(sinks) != 1:
            return None
        pips, w, seen = [], sinks[0], set()
        while w in par and par[w] and w not in seen:
            seen.add(w)
            pips.append(par[w])
            w = par[w].split("->")[0]
        return pips or None

    re_site = re.compile(r"^[A-Z0-9_]*?_X(\d+)Y(\d+)/")

    def region(inst):
        c = cells.get(inst)
        m = re_site.match((c or {}).get("attributes", {}).get("NEXTPNR_BEL", "")) if c else None
        return (int(m.group(1)) // 10, int(m.group(2)) // 10) if m else None

    path = {"S": [], "F": []}
    for side, kind, rs, rd, txt in rules:
        hit = [a for a in arcs if a["kind"] == kind and rs.fullmatch(a["src"]) and rd.fullmatch(a["dst"])]
        if len(hit) != 1:
            sys.exit("race_mc.py: %d arcs match '%s' (need exactly 1)" % (len(hit), txt))
        a = hit[0]
        inst = (a["dst"] if kind == "IC" else a["src"]).rpartition("/")[0]
        lo, hi = int(a["fast_min_ps"]), int(a["slow_max_ps"])
        pips = branch(a["dst"]) if kind == "IC" else None
        path[side].append({"kind": kind, "lo": lo, "hi": hi, "chain": bool(chain.fullmatch(inst)),
                           "pips": pips, "reg": region(inst), "name": "%s %s -> %s" % (kind, a["src"], a["dst"])})
    for side in "SF":
        for a in path[side]:
            print("%s %-4s %s %-5s [%d, %d]%s" % (side, "chain" if a["chain"] else "rest", a["name"], "",
                                                    a["lo"], a["hi"], "  pips %d" % len(a["pips"]) if a["pips"]
                                                    else ("  (own factor)" if a["kind"] == "IC" else "")))

    def total(side, xc, xr, pf, rf, af):
        t = 0.0
        for i, a in enumerate(path[side]):
            b = xc if a["chain"] else xr
            d = a["lo"] + b * (a["hi"] - a["lo"])
            if pf is not None:
                if a["kind"] == "IC" and a["pips"]:
                    f = sum(pf(p) for p in a["pips"]) / len(a["pips"])
                else:
                    f = af[(side, i)]
                f *= rf(a["reg"])
                d = max(0.0, d * f)
            t += d
        return t

    for xc in (0.20, 0.31):
        for xr in (0.20, 0.31):
            print("corner chains %.2f rest %.2f, no scatter: F - S = %.0f ps"
                  % (xc, xr, total("F", xc, xr, None, None, None) - total("S", xc, xr, None, None, None)))
    rnd = random.Random(12345)
    ms = []
    for _ in range(n):
        xc, xr = rnd.uniform(.20, .31), rnd.uniform(.20, .31)
        pcache, rcache = {}, {}

        def pf(p):
            if p not in pcache:
                pcache[p] = 1 + 0.126 * rnd.gauss(0, 1)
            return pcache[p]

        def rf(k):
            if k is None:
                return 1.0
            if k not in rcache:
                rcache[k] = 1 + 0.02 * rnd.gauss(0, 1)
            return rcache[k]
        af = {(s, i): 1 + 0.126 * rnd.gauss(0, 1) for s in "SF" for i in range(len(path[s]))}
        ms.append(total("F", xc, xr, pf, rf, af) - total("S", xc, xr, pf, rf, af))
    ms.sort()
    q = lambda p: ms[min(len(ms) - 1, int(p * len(ms)))]
    mu, sd = st.mean(ms), st.pstdev(ms)
    print("model points %d: margin F - S mean %.0f ps, sd %.0f ps (mean / sd %.2f); quantiles 1e-4 %.0f, 1e-3 %.0f, "
          "0.01 %.0f, 0.5 %.0f" % (n, mu, sd, mu / sd if sd else float("inf"), q(1e-4), q(1e-3), q(0.01), q(0.5)))
    for t in (0, 20, 50):
        k = sum(1 for m in ms if m < t)
        print("  below %3d ps: %d of %d (%.2g)%s" % (t, k, n, k / n,
              "" if k else "  (normal tail at mean/sd: %.2g)" % (0.5 * math.erfc((mu - t) / sd / math.sqrt(2)))))


if __name__ == "__main__":
    main()
