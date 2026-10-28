#!/usr/bin/env python3
"""check_bands.py -- validate band files; find and correct the prjxray BRKH_INT fast-corner inversion.

    python3 check_bands.py check BANDS.json...
        every band (sections cells / arcs / pins / sitepins, summary fields lut / route / feedback /
        pad_steps) must be a JSON array of exactly two naturals [lo, hi] with lo <= hi.  Prints each
        violation; exit 1 if any.  The Lean reader silently reads lo > hi as [lo, lo]
        (XAudit/Parse.toSteps) and silently DROPS a malformed entry (XAudit/Parse.pairOf, the arc
        then gets the default band); this is the gate in front of it.  Its Lean counterpart, with
        a proved statement of what passing guarantees, is Formal/Core/XAudit/BandCheck.lean.

    python3 check_bands.py brkh FAST.json SLOW.json [--skel SKEL_BANDS.json ...]
        lists the arcs whose route crosses a BRKH_INT pip (signature below), with whether each is
        inverted (FAST lo > hi) and whether it is in the given skeleton band file(s).

    python3 check_bands.py fix FAST.json SLOW.json INDEP.json OUTDIR
        writes OUTDIR/fast.bands.json and OUTDIR/indep.bands.json corrected on the BRKH arcs, and
        checks them.

THE CAUSE (formal/notes/A-kapres2.md).  prjxray-db zynq7 tile_type_BRKH_INT.json gives 14 pips
(the NL1/NR1 BEG and SL1/SR1 END single-length pips through the clock-region break row) the
4-tuple [FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX] = [0.202, 0.105, 0.231, 0.312] ns: FAST_MIN >
FAST_MAX.  It is the only element of the whole zynq7 db with an inverted corner (pips, reverse
pips and site pins scanned).  xray_delay.py sums the 4-tuples column by column along the route
(plus one RC term in every column), so an arc through k such pips has its fast columns shifted
by +202k / +105k: FAST_MIN - FAST_MAX grows by 97k.  When the rest of the route's fast spread is
below 97k the arc is inverted; otherwise it is NOT inverted but its fast band is still 2*97k
narrower than any reading of the element that keeps both of its numbers.

SOUND TREATMENT.  Read the element's fast delay as the hull [0.105, 0.202] (both prjxray numbers
are admissible).  For an arc with k crossings the fast band becomes
    [FAST_MIN - 97k, FAST_MAX + 97k]                       (exact: 97 ps is an integer)
and the mixed (indep) band [FAST_MIN, SLOW_MAX] becomes [FAST_MIN - 97k, SLOW_MAX].  The slow
band is unaffected (0.231 <= 0.312).  Taking the hull of the ARC's two numbers (what
kapres/cornerband.py did) is NOT enough: it misses [FAST_MIN-97k, FAST_MAX) and (FAST_MIN,
FAST_MAX+97k].

DETECTION (the route is not available; the committed band files are).  A BRKH pip adds -97 ps to
the arc's fast spread (FAST_MAX - FAST_MIN) and +81 ps to its slow spread; ordinary elements have
fast spread ~0.33-0.45 x slow spread.  So r = fast_spread - 0.375 * slow_spread is about -127k
lower on a crossing arc.  On all four gcd_hw seeds r is >= -20 on every other arc and in
[-135, -117] on the flagged ones (k = 1; nothing near -254); the threshold is R_CUT = -60.  This is
evidence, not proof: a crossing arc whose ordinary part had r > +67 would be missed (the largest
ordinary r seen is about +79, on long routes).
"""
import json
import os
import sys

R_CUT = -60
BRKH_FAST = (202, 105)        # ps, prjxray-db zynq7 BRKH_INT pips: FAST_MIN, FAST_MAX
SHIFT = BRKH_FAST[0] - BRKH_FAST[1]   # 97
SECTIONS = ("cells", "arcs", "pins", "sitepins")
SUMMARY = ("lut", "route", "feedback", "pad_steps")


def is_nat(x):
    return isinstance(x, int) and not isinstance(x, bool) and x >= 0


def pair_ok(v):
    """a band the Lean reader takes as written: a JSON array of exactly two naturals, lo <= hi.
    (XAudit/Parse.pairOf silently DROPS an entry that is not two naturals -- the arc then gets
    the default band -- and toSteps narrows lo > hi to [lo, lo]; both are rejected here.)"""
    return isinstance(v, list) and len(v) == 2 and is_nat(v[0]) and is_nat(v[1]) and v[0] <= v[1]


def check(path):
    """all violations in a band file: (section, key, value).  Mirrors BandCheck.jsonBandsOK."""
    b = json.load(open(path))
    bad = []
    if not isinstance(b, dict):
        return [("file", "-", "not a JSON object")]
    for sec in SECTIONS:
        v = b.get(sec)
        if v is None:
            continue
        if not isinstance(v, dict):
            bad.append((sec, "-", "section is not an object"))
            continue
        for k, x in v.items():
            if not pair_ok(x):
                bad.append((sec, k, x))
    for k in SUMMARY:
        if k in b and not pair_ok(b[k]):
            bad.append(("summary", k, b[k]))
    return bad


def brkh(F, S):
    """arcs with the BRKH_INT signature: key -> (k, r)."""
    out = {}
    for key, (f0, f1) in F["arcs"].items():
        s0, s1 = S["arcs"][key]
        r = (f1 - f0) - 0.375 * (s1 - s0)
        if r < R_CUT:
            k = max(1, round(-r / 127.0))
            out[key] = (k, r)
    return out


def main():
    cmd, args = sys.argv[1], sys.argv[2:]
    if cmd == "check":
        nbad = 0
        for p in args:
            bad = check(p)
            nbad += len(bad)
            print("%s: %s" % (p, "OK (every band has lo <= hi)" if not bad else "%d INVERTED band(s)" % len(bad)))
            for sec, k, v in bad:
                print("  REJECT %s %s %s" % (sec, k, v))
        sys.exit(1 if nbad else 0)
    if cmd == "brkh":
        F, S = json.load(open(args[0])), json.load(open(args[1]))
        skels = []
        if "--skel" in args:
            skels = [json.load(open(p)) for p in args[args.index("--skel") + 1:]]
        hit = brkh(F, S)
        rs = sorted((f1 - f0) - 0.375 * (S["arcs"][k][1] - S["arcs"][k][0])
                    for k, (f0, f1) in F["arcs"].items() if k not in hit)
        print("arcs %d, BRKH-signature arcs %d (inverted %d); r of the others in [%.0f, %.0f]; "
              "in skeleton: %d" % (len(F["arcs"]), len(hit),
                                   sum(1 for k in hit if F["arcs"][k][0] > F["arcs"][k][1]), rs[0], rs[-1],
                                   sum(1 for k in hit if any(k in s["arcs"] for s in skels))))
        for key in sorted(hit):
            k, r = hit[key]
            f0, f1 = F["arcs"][key]
            print("  %-90s fast %s slow %s r %.0f k %d %s%s" % (
                key, F["arcs"][key], S["arcs"][key], r, k, "INVERTED" if f0 > f1 else "not-inverted",
                " IN-SKELETON" if any(key in s["arcs"] for s in skels) else ""))
        return
    if cmd == "fix":
        F, S, I = (json.load(open(p)) for p in args[:3])
        od = args[3]
        os.makedirs(od, exist_ok=True)
        hit = brkh(F, S)
        for key, (k, _) in hit.items():
            f0, f1 = F["arcs"][key]
            F["arcs"][key] = [max(0, f0 - SHIFT * k), f1 + SHIFT * k]
            i0, i1 = I["arcs"][key]
            I["arcs"][key] = [max(0, i0 - SHIFT * k), i1]
        note = "; BRKH_INT fast hull applied to %d arcs (kapres2/check_bands.py fix)" % len(hit)
        F["comment"] = F.get("comment", "") + note
        I["comment"] = I.get("comment", "") + note
        for nm, b in (("fast", F), ("indep", I)):
            p = os.path.join(od, nm + ".bands.json")
            json.dump(b, open(p, "w"))
            bad = check(p)
            print("%s: %d arcs corrected, %s" % (p, len(hit), "OK" if not bad else "STILL INVERTED %d" % len(bad)))
            if bad:
                sys.exit(1)
        return
    sys.exit(__doc__)


if __name__ == "__main__":
    main()
