#!/usr/bin/env python3
"""siteskew.py -- how much of the own-feedback race margin is site-pin delay, per C-element pin.

    python3 -I siteskew.py ROUTED.json [ROUTED.json ...] [--db PRJXRAY_DB/zynq7]

For every LUT with own feedback in a nextpnr-xilinx routed JSON (a bd_ce.v C-element:
logical pins a, b, .., then the feedback, then rst), with the placer's permutation read
from X_ORIG_PORT_A<k>: the physical pin of the feedback and of each input, and the
site-pin term of the per-pin race margin at each corner,

    s(p) = siteLo(input pin p) - siteHi(feedback pin)      (ps; prjxray site-pin intrinsic)

BackPin's margin contains s(p) (pinbands.py puts it in the pin arc); routed2x/xray_delay
bands contain it too (inside the routed arcs), so the atomic xevents2/events4 margins
already include it.  A delay model WITHOUT site-pin delays (nextpnr's SDF: C-11b, A-fidelity
section 7) is off by exactly s(p) on that pin.  UNTRUSTED report.
"""
import argparse
import collections
import json
import os
import re
import statistics

RE_I = re.compile(r"I(\d+)")
CORNERS = {"fast": (0, 1), "slow": (2, 3), "indep": (0, 3)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("routed", nargs="+")
    ap.add_argument("--db", default=os.path.expanduser(
        "~/dev2/lib/fpgatoolchain/openxc7/share/nextpnr/prjxray-db/zynq7"))
    a = ap.parse_args()
    tg = json.load(open(a.db + "/xc7z010/tilegrid.json"))
    site_tile = {}
    for t, v in tg.items():
        for i, s in enumerate(sorted(v.get("sites", {}), key=lambda s: int(re.search(r"X(\d+)", s).group(1)))):
            site_tile[s] = (v["type"], i)
    tt = {}

    def sp(site, pin):
        typ, idx = site_tile[site]
        if typ not in tt:
            tt[typ] = json.load(open("%s/tile_type_%s.json" % (a.db, typ)))
        s = [s for s in tt[typ]["sites"] if s["x_coord"] == idx][0]
        return [int(round(float(x) * 1000)) for x in s["site_pins"][pin]["delay"]]

    for path in a.routed:
        m = json.load(open(path))["modules"]["top"]
        fbpin = collections.Counter()
        inpin = collections.Counter()
        terms = {c: [] for c in CORNERS}
        nst = 0
        for cn, c in m["cells"].items():
            if c["type"] != "SLICE_LUTX":
                continue
            op = "O6" if c["connections"].get("O6") else "O5"
            ob = c["connections"][op][0]
            phys = {}
            for k in range(1, 7):
                for l in map(int, RE_I.findall(c["attributes"].get("X_ORIG_PORT_A%d" % k, ""))):
                    phys[l] = k
            fbl = [l for l, k in phys.items() if c["connections"].get("A%d" % k, [None])[0] == ob]
            if len(fbl) != 1:
                continue
            lq = fbl[0]
            if not 1 <= lq <= 4:
                continue
            nst += 1
            site, bel = c["attributes"]["NEXTPNR_BEL"].split("/")[:2]
            L = bel[0]
            kq = phys[lq]
            fbpin["A%d" % kq] += 1
            sq = sp(site, "%s%d" % (L, kq))
            for l in range(lq):
                if l not in phys:
                    continue
                k = phys[l]
                inpin["A%d" % k] += 1
                s = sp(site, "%s%d" % (L, k))
                for cor, (lo, hi) in CORNERS.items():
                    terms[cor].append(s[lo] - sq[hi])
        print("%s: %d own-feedback LUTs; feedback on %s; inputs on %s" % (
            path, nst, dict(sorted(fbpin.items())), dict(sorted(inpin.items()))))
        for cor in CORNERS:
            t = sorted(terms[cor])
            if t:
                print("  %-5s site-pin term s(p) = siteLo(p) - siteHi(fb): min %d, median %d, max %d ps; "
                      "negative on %d of %d pins" % (cor, t[0], int(statistics.median(t)), t[-1],
                                                     sum(1 for x in t if x < 0), len(t)))


if __name__ == "__main__":
    main()
