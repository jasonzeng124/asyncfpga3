#!/usr/bin/env python3
"""gcdpin.py -- per-pin (BackPin) margins of the gcd_hw R5 control, from A-events4's Back margins.

    python3 -I gcdpin.py SK.json BANDS.json --label CORNER

UNTRUSTED analysis (no Lean verdict: xevents2/xevents2pin do not recognise gcd_hw, whose
control has choice -- merges, arbiters, guarded pins -- see A-events4).  SK.json is
events4/ana.py --json on the routed2x skeleton, BANDS.json the routed2x bands of the same
corner (formal/tools-A/xaudit/gcd/inputs).

The per-pin correction (formal/notes/A-events2pin.md, section 3).  In routed2x/xray_delay
bands the site-pin delay of every physical LUT pin is already inside that pin's routed arc
(xray_delay charges prjxray's Inpin to the INTERCONNECT row), on both sides of the race.
What H_ATOMIC_LUT hides is only the LUT's own pin-to-O arc: with per-pin arcs

    BackPin margin = Back margin - (hiIO(feedback pin) - loIO(pin p)) + sum_walk (loIO_k - loF_k)

and loF_k = min over the pins of LUT k, so the walk sum is >= 0.  This script drops it and
bounds hiIO(fb) - loIO(p) by the stage LUT's atomic band width hiF - loF:

    BackPin margin >= Back margin - (hiF_j - loF_j)

exact when the LUT's IOPATH rows are flat over its pins (every LUT6 O6 in prjxray-db:
45/56/100/124 ps on A1..A6), conservative otherwise (O5 rows differ by a few ps).
Virtual stages (H_ARB's virtual mux core, `virtual`: true) have no own LUT feedback pin
and are reported unchanged.  Guarded pins (events4 rule Guard) are listed with their entry
margin corrected the same way (an entry race is the same feedback-vs-arrival race).
"""
import argparse
import json


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("sk")
    ap.add_argument("bands")
    ap.add_argument("--label", default="")
    a = ap.parse_args()
    s = json.load(open(a.sk))
    cells = json.load(open(a.bands))["cells"]
    rows, widths = [], {}
    nvirt = 0
    for e in s["stages"]:
        if e["rule"] != "Back":
            continue
        if e.get("virtual"):
            nvirt += 1
            continue
        lo, hi = cells[e["stage"]]
        w = hi - lo
        widths[w] = widths.get(w, 0) + 1
        rows.append((e["margin"] - w, e["margin"], w, e))
    rows.sort(key=lambda r: r[0])
    bad = [r for r in rows if r[0] <= 0]
    newbad = [r for r in bad if r[1] > 0]
    print(f"[{a.label}] Back pins (real stages) {len(rows)}, virtual (H_ARB) {nvirt}; "
          f"stage-LUT band widths hiF-loF (ps): {dict(sorted(widths.items()))}")
    print(f"  min atomic Back margin {min(r[1] for r in rows)} ps; min per-pin (BackPin) margin {rows[0][0]} ps")
    print(f"  per-pin margin <= 0: {len(bad)} pin(s), of which {len(newbad)} had atomic margin > 0")
    for m, m0, w, e in bad:
        print(f"    BackPin {m:6d}  (atomic {m0:6d}, skew {w})  {e['stage']} pin{e['pin']} <- {e['src']}")
    near = [r for r in rows if 0 < r[0] <= 100]
    print(f"  per-pin margin in (0, 100] ps: {len(near)}")
    for m, m0, w, e in near[:10]:
        print(f"    BackPin {m:6d}  (atomic {m0:6d})  {e['stage']} pin{e['pin']} <- {e['src']}")
    gs = []
    for e in s["stages"]:
        if e["rule"] == "Guard" and e.get("entry") is not None and e["stage"] in cells:
            lo, hi = cells[e["stage"]]
            gs.append((e["entry"] - (hi - lo), e["entry"], e))
    if gs:
        gs.sort(key=lambda r: r[0])
        print(f"  guarded pins {len(gs)}: min entry margin atomic {min(g[1] for g in gs)} ps, "
              f"per-pin {gs[0][0]} ps; <= 0 per pin: {sum(1 for g in gs if g[0] <= 0)}")


if __name__ == "__main__":
    main()
