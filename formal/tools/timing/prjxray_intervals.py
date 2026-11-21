#!/usr/bin/env python3
"""Probe C-10b: the delay data a verified timing checker would need, read
straight out of prjxray-db (zynq7), next to what nextpnr-xilinx writes into
the SDF that rules E/A/J read.

    python3 -I formal/tools/timing/prjxray_intervals.py [PRJXRAY_DB_ZYNQ7_DIR]

Prints
  1. per INT_L pip class: fast/slow min/max ratios to slow_max (corner spread),
  2. CLBLL_L SLICEL LUT input site-pin delays (nextpnr: flat 25 ps),
  3. LUT6 cell arcs,
  4. for the pips used by formal/lean/Formal/Timing/Rules.lean's
     counterexamples: the prjxray 4-tuple and the number nextpnr-xilinx's
     getPipDelay puts in the SDF:
         max(slow_min, slow_max)*1000 + int((src_len*R_src + R_pip)*C_pip/1e9)
     with R, C scaled x1000 (nextpnr_structs.py r_scale/c_scale), src_len=1,
     floored at 35 ps (xilinx/arch.h, openXC7/nextpnr-xilinx).
"""
import json, os, re, sys, collections

DB = sys.argv[1] if len(sys.argv) > 1 else os.path.expanduser(
    "~/dev2/lib/fpgatoolchain/openxc7/share/nextpnr/prjxray-db/zynq7")


def ps(x):
    return round(float(x) * 1000)


def main():
    it = json.load(open(os.path.join(DB, "tile_type_INT_L.json")))
    wires = it["wires"]
    print("1. INT_L pips by destination class: ratio to slow_max")
    rat = collections.defaultdict(list)
    for k, p in it["pips"].items():
        s = p.get("src_to_dst") or {}
        d = s.get("delay")
        if not d:
            continue
        fmin, fmax, smin, smax = map(float, d)
        if smax == 0:
            continue
        cls = re.sub(r"\d", "", p["dst_wire"].split("_")[0])
        rat[cls].append((fmin / smax, fmax / smax, smin / smax, smax))
    print(f"   {'class':10s} {'n':>5s} {'fmin/smax':>13s} {'fmax/smax':>13s} {'smin/smax':>13s} {'smax ps':>9s}")
    for c, v in sorted(rat.items()):
        r = lambda i: f"{min(x[i] for x in v):.3f}-{max(x[i] for x in v):.3f}"
        print(f"   {c:10s} {len(v):5d} {r(0):>13s} {r(1):>13s} {r(2):>13s} "
              f"{ps(min(x[3] for x in v)):4d}-{ps(max(x[3] for x in v)):<4d}")

    cl = json.load(open(os.path.join(DB, "tile_type_CLBLL_L.json")))
    print("\n2. CLBLL_L SLICEL LUT input site pins (fast_min fast_max slow_min slow_max, ps)")
    site = cl["sites"][0]
    for pin in ("A1", "A2", "A3", "A4", "A5", "A6"):
        d = site["site_pins"][pin]["delay"]
        print(f"   {pin}: {tuple(ps(x) for x in d)}   nextpnr SDF: 25 (site entry pip, flat)")

    print("\n3. LUT6 arcs, timings/CLBLL_L.sdf (first block):")
    sdf = open(os.path.join(DB, "timings", "CLBLL_L.sdf")).read()
    m = re.search(r'\(CELLTYPE "LUT6"\).*?\(IOPATH A1 O6 (\([^)]*\))(\([^)]*\))', sdf, re.S)
    print(f"   A1->O6 {m.group(1)} {m.group(2)}   nextpnr: max of both = slow max")

    print("\n4. pips used by Rules.lean counterexamples")
    for name in ("INT_L.LOGIC_OUTS_L0->>SW2BEG0", "INT_L.EE2END0->>NN2BEG0",
                 "INT_L.BYP_BOUNCE0->>IMUX_L2"):
        p = it["pips"][name]
        s = p["src_to_dst"]
        d = [ps(x) for x in s["delay"]]
        r_pip = float(s.get("res") or 0) * 1000
        c_pip = float(s.get("in_cap") or 0) * 1000
        r_src = float((wires.get(p["src_wire"]) or {}).get("res") or 0) * 1000
        rc = int((1 * r_src + r_pip) * c_pip / 1e9)
        sdfv = max(max(d[2], d[3]) + rc, 35)
        print(f"   {name}: {tuple(d)}  buffered={not int(p.get('is_pass_transistor', 0))}"
              f"  RC term {rc} ps  -> SDF {sdfv} ps")


if __name__ == "__main__":
    main()
