#!/usr/bin/env python3
"""guard_est.py SPECDIR RULEROOT FARMRESULTS -- what a wider rule E / J guard would cost each route, on the route itself.

For each kernel K with a spec in SPECDIR (research/data/suite/board/suite_v10: the shipped iteration's sizes, with its
trim record applied: the route as shipped) and the
rule's outputs under RULEROOT/K (corner_audit on that route as built, merged over bands 0.20 / 0.31 by merge_rules.py:
rule/ at the flow's 0.97 / 1.03 guard, ruleG/ at the wider one): every line whose wider-guard proposal exceeds its
built size must grow by the difference (a guard never shortens a line). The route's critical cycle (the farm's
auto/cyc_I.txt for the shipped iteration I, after the trim) prices it: a line on the cycle grows the period by its
extra elements x its own mean element delay there (chain ps / elements). A static estimate -- no re-route, so none of
the route-to-route churn that swamps single-seed A/Bs (flow v10's sqrtsub spans 17.2-32.2 ns over its 4 seeds) -- and
a lower bound in one way: a grown line off the cycle can make a new cycle critical. Run from the repo root. Prints
one row per kernel and the
geometric mean of (P + dP) / P over the routes with a P."""
import glob
import math
import os
import re
import sys


def rd(p):
    try:
        return {m.group(1): int(m.group(2)) for m in (re.match(r"`define\s+(\S+)\s+(\d+)", l) for l in open(p)) if m}
    except OSError:
        return None


def spec(p):
    return dict(l.rstrip("\n").split("=", 1) for l in open(p) if "=" in l and not l.startswith("#"))


def main():
    sd, rr, fr = sys.argv[1:4]
    rows, ratios = [], []
    for sp in sorted(glob.glob(os.path.join(sd, "*.spec"))):
        k = os.path.basename(sp)[:-5]
        s = spec(sp)
        head = open(sp).readline()
        m = re.search(r"farm results (\S+)\)", head)
        pm = re.search(r"P=(\d+)", head)
        built = rd(s["SIZES"])   # repo-relative: run from the repo root
        # the route as SHIPPED: the trim record (MACRO=LEN) over the built sizes -- a trimmed line is the length to grow from
        if built is not None and s.get("TRIMS", "-") not in ("-", ""):
            for t in open(s["TRIMS"]).read().split():
                if "=" in t:
                    mac, v = t.split("=")
                    built[mac] = int(v)
        base, wide = rd(os.path.join(rr, k, "rule/sizes.vh")), rd(os.path.join(rr, k, "ruleG/sizes.vh"))
        if built is None or wide is None or base is None:
            rows.append("| %s | - | rule outputs missing | | |" % k); continue
        grow = {mac: wide[mac] - built.get(mac, 0) for mac in wide if wide[mac] > built.get(mac, 0)}
        it = None
        if m:
            d = os.path.join(fr, m.group(1), "auto")
            try:
                it = re.match(r"CLEAN it=(\d+)", [l for l in open(os.path.join(d, "result.txt")) if l.startswith("CLEAN")][-1]).group(1)
            except (OSError, IndexError, AttributeError):
                it = None
        cyc = {}
        if it is not None:
            try:
                for l in open(os.path.join(fr, m.group(1), "auto", "cyc_%s.txt" % it)):
                    mm = re.match(r"^\s*(\S+)\s+chain\s+(\d+)\s+\(\s*(\d+)\s+el\)", l)
                    if mm:
                        cyc[mm.group(1)] = (int(mm.group(2)), int(mm.group(3)))
            except OSError:
                pass
        dp, on = 0, []
        for mac, g in sorted(grow.items()):
            unit = mac.replace("BD_SZ_BRIDGE_I_UDUT_", "").lower()
            if unit in cyc:
                ps, el = cyc[unit]
                step = ps / el if el else 380.0
                dp += g * step; on.append("%s +%d" % (unit, g))
        P = int(pm.group(1)) if pm else None
        if P:
            ratios.append((P + dp) / P)
        rows.append("| %s | %s | %d line(s), +%d elements | %s | %s |" % (
            k, ("%.2f" % (P / 1000.0)) if P else "-", len(grow), sum(grow.values()), ", ".join(on) or "none on the cycle",
            ("+%.0f ps (+%.1f %%)" % (dp, 100.0 * dp / P)) if P else ("+%.0f ps" % dp if dp else "-")))
    print("| kernel | P (ns, shipped) | lines that must grow at the wider guard | of them on the critical cycle | estimated dP |")
    print("|---|---|---|---|---|")
    print("\n".join(rows))
    if ratios:
        g = math.exp(sum(math.log(r) for r in ratios) / len(ratios))
        print("\ngeometric mean (P + dP) / P over %d routes with a P: %.3f" % (len(ratios), g))


if __name__ == "__main__":
    main()
