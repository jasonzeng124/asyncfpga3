#!/usr/bin/env python3
"""Gate for verify/MTBF.md's placement precondition.

    python3 hw/check_fracture.py [routed.json]

MTBF.md is explicit: both grants of an arb channel must land in ONE fractured
LUT6_2 site.  Two separate LUTs have identical intrinsic delay but different,
build-dependent routing, and an asymmetry that moves between builds makes a
measured MTBF worthless the moment anything is rebuilt -- the whole
characterisation would not transfer to the next bitstream.

hw/build_hw.sh deliberately does not carry over flow.sh's fracture check
(nothing in ro_top is fractured, so there was nothing to check).  arb_mtbf.v
is different: every channel's ugrant is a LUT6_2, named `ch[N].ugrant` in the
source (and, since the Phase 1 depth-0 population was added, `pop[N].ugrant`
too -- same primitive, same precondition, just a different generate block),
and nextpnr's routed JSON splits a fractured pair into two cells --
`ch[N].ugrant$LUT6` (the O6 function) and `ch[N].ugrant$LUT5` (the O5
function) -- each carrying a NEXTPNR_BEL attribute like "SLICE_X36Y45/A6LUT"
and "SLICE_X36Y45/A5LUT".  Fractured-together means those two strings agree on
everything except the 5/6 digit.  If nextpnr had split the pair into two
sites, the two BELs would land on different slices or different letters, and
this catches that before a single hour is spent measuring.

Placement STABILITY across builds is the second half of the precondition and
is not visible from one build alone.  The first run records each channel's
BEL pair into a baseline file next to the routed JSON; every later run against
the same design compares against it and fails if a channel moved.  Delete the
baseline to intentionally accept a new placement (e.g. after a deliberate RTL
change to this file).
"""

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# arb_mtbf names its fractured pairs ch[N].ugrant / pop[N].ugrant.  arb_prot
# instantiates the whole bd_arbiter, so its pairs are arb[N].uarb.ugrant AND
# arb[N].uarb.ustate -- the state node is fractured too there, pairing q on O6
# with R0 on O5, and if THAT splits the arbiter stops being four LUTs and R0
# stops reading the same q the grants read.  Same precondition, so the same
# gate covers it.
NAME_RE = re.compile(
    r"^(ch|pop|arb)\[(\d+)\](?:\.uarb)?\.(ugrant|ustate)\$LUT([56])$")
BEL_RE = re.compile(r"^(SLICE_X\d+Y\d+)/([A-D])([56])LUT$")


def baseline_key(prefix, idx, cell):
    """Stable baseline key.

    ugrant keeps the historical bare form so arb_mtbf's recorded baseline stays
    valid across this change; the state node, which only arb_prot exposes, is
    qualified.  Renaming the existing keys would have made every one of
    arb_mtbf's 192 channels read as new and silently accepted a fresh
    placement, which is the exact failure this baseline exists to prevent.
    """
    return f"{prefix}{idx}" if cell == "ugrant" else f"{prefix}{idx}.{cell}"


def load_grant_bels(routed_json):
    d = json.loads(routed_json.read_text())
    modules = d["modules"]
    top = next(iter(modules))
    cells = modules[top]["cells"]

    found = {}  # (prefix, index, cell) -> {"5": bel, "6": bel}
    for name, c in cells.items():
        m = NAME_RE.match(name)
        if not m:
            continue
        key = (m.group(1), int(m.group(2)), m.group(3))
        half = m.group(4)
        bel = c.get("attributes", {}).get("NEXTPNR_BEL", "")
        found.setdefault(key, {})[half] = bel
    return found


def main():
    routed = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else \
        ROOT / "build/hw/arb_mtbf/arb_mtbf_routed.json"
    baseline_path = routed.parent / "grant_bels.json"

    if not routed.exists():
        print(f"missing {routed} -- run hw/build_hw.sh arb_mtbf first",
              file=sys.stderr)
        return 2

    found = load_grant_bels(routed)
    if not found:
        print("no ugrant/ustate $LUT5/$LUT6 pairs found in the routed JSON "
              "-- wrong design, or nextpnr did not fracture anything",
              file=sys.stderr)
        return 2

    bad = 0
    sites = {}
    print("fracture check")
    print("-" * 78)
    for key in sorted(found, key=lambda k: (k[0], k[2], k[1])):
        prefix, idx, cell = key
        label = f"{prefix}[{idx}].{cell}"
        halves = found[key]
        if "5" not in halves or "6" not in halves:
            print(f"  channel {label}: only found half(s) {sorted(halves)} "
                  f"-- the pair did not both survive as named cells")
            bad += 1
            continue
        b5, b6 = halves["5"], halves["6"]
        m5, m6 = BEL_RE.match(b5), BEL_RE.match(b6)
        if not (m5 and m6):
            print(f"  channel {label}: BEL did not parse ({b5!r}, {b6!r})")
            bad += 1
            continue
        same_site = (m5.group(1) == m6.group(1) and m5.group(2) == m6.group(2))
        ok5, ok6 = m5.group(3) == "5", m6.group(3) == "6"
        if same_site and ok5 and ok6:
            site = f"{m5.group(1)}/{m5.group(2)}"
            sites[key] = site
            print(f"  channel {label}: fractured, one site  {site}  "
                  f"(O5 {b5}, O6 {b6})")
        else:
            print(f"  channel {label}: NOT one fractured site -- "
                  f"O5 {b5}  O6 {b6}")
            bad += 1

    if bad:
        print()
        print(f"{bad} channel(s) failed the fracture check -- do not run "
              f"the long measurement against this build")
        return 1

    print()
    if baseline_path.exists():
        baseline = json.loads(baseline_path.read_text())
        moved = 0
        for key, site in sites.items():
            prefix, idx, cell = key
            label = f"{prefix}[{idx}].{cell}"
            bkey = baseline_key(prefix, idx, cell)
            prev = baseline.get(bkey)
            if prev is None:
                print(f"  channel {label}: no baseline entry (new channel?) "
                      f"-- recording {site}")
                baseline[bkey] = site
            elif prev != site:
                print(f"  channel {label}: MOVED since baseline -- was "
                      f"{prev}, now {site}")
                moved += 1
            else:
                print(f"  channel {label}: stable at {site}, matches "
                      f"baseline")
        if moved:
            print()
            print(f"{moved} channel(s) moved since the baseline build -- a "
                  f"measured MTBF from")
            print("either build does not transfer to the other; rebuild "
                  "deterministically or")
            print("delete the baseline to accept the new placement "
                  "deliberately.")
            return 1
        baseline_path.write_text(json.dumps(baseline, indent=2, sort_keys=True))
    else:
        baseline_path.write_text(
            json.dumps({baseline_key(*k): v for k, v in sites.items()},
                       indent=2, sort_keys=True))
        print(f"no baseline existed -- recorded this build's sites to "
              f"{baseline_path}")
        print("run this again after a clean rebuild before trusting a long "
              "measurement.")

    print()
    print("check_fracture.py PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
