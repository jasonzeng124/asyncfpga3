#!/usr/bin/env python3
"""ratchet.py CUR.vh PROP.vh NEG.tsv OUT.vh [PINNED] -- one step of the automatic sizing loop (auto_size.sh).
A line the rule asks to lengthen on this route (PROP > CUR) is lengthened and PINNED: from then on it never goes below
max(CUR, PROP).  A line that was never asked to lengthen follows the rule's proposal, shorter included.
Why not max(CUR, PROP) for every line (the first version): the first proposal is computed on the route built at
bdc/emit.py's estimates, the most spread-out route the loop ever sees (xorshift seed 1: 511 links of delay, wires long),
and a max over every line kept that proposal as a floor for good (UCMPI1 26 there, against 5 on the hand recipe's routes
with every draw passing).  Pinning only the lines that were ever short keeps what the ratchet was for -- tighten_loop.sh's
period-2 oscillation is a line shortened, found short on the next route, padded, shortened again; a pinned line cannot
be shortened again -- and lets every other line shrink on the compact routes.  The loop still ships only a route the
rule finds clean as built, so the pinning changes how short the sizes get, not what is shipped.
PINNED (a file of macro names, read and rewritten) defaults to OUT.vh's directory /pinned.txt.
Prints "raised N unfixable M negative K lowered L pinned P"."""
import os, re, sys

def rd(p):
    out, order = {}, []
    for ln in open(p):
        m = re.match(r"`define\s+(\S+)\s+(\d+)", ln)
        if m:
            out[m.group(1)] = int(m.group(2)); order.append(m.group(1))
    return out, order

cur, order = rd(sys.argv[1])
prop, _ = rd(sys.argv[2])
neg = [l.rstrip("\n").split("\t") for l in open(sys.argv[3]) if l.strip() and not l.startswith("rule\t")]
RAISE_ONLY = "--raise-only" in sys.argv   # the finish phase (auto_size.sh): every line max(CUR, PROP), none lowered
NOPIN = "--nopin" in sys.argv             # it 1 (auto_size.sh): follow the proposal, pin nothing (a recalibration)
sys.argv = [a for a in sys.argv if a != "--nopin"]
HEADROOM = 0                               # --headroom N: a line raised gets N more elements than the rule asks
if "--headroom" in sys.argv:
    i = sys.argv.index("--headroom"); HEADROOM = int(sys.argv[i + 1]); del sys.argv[i:i + 2]
# --near PS LINES (with --raise-only; auto_size.sh AUTO_NEAR_PS): a line the rule keeps at least at its size with fewer
# than PS ps left at any corner (LINES: corner_audit's lines.tsv per corner, comma-separated) gets HEADROOM more elements
# too, not only the lines that are short.  Why: in the finish phase each re-route moves the small margins by a few
# hundred ps, so raising only the negative lines leaves the next route its new negatives among the lines that were
# just positive (farm suite6, flow v6: 16 of 32 loops ended NOT CLEAN after three raise-only routes, typically 2-10
# rows of tens to hundreds of ps; collatz s1's last route: H -15 ps, with four lines at 106-326 ps left).
NEAR, NEARLINES = None, []
if "--near" in sys.argv:
    i = sys.argv.index("--near"); NEAR = int(sys.argv[i + 1])
    NEARLINES = [q for q in sys.argv[i + 2].split(",") if q]; del sys.argv[i:i + 3]
sys.argv = [a for a in sys.argv if a != "--raise-only"]
near = set()
if NEAR is not None and RAISE_ONLY:
    for q in NEARLINES:
        if not os.path.exists(q):
            continue
        for ln in open(q):
            f_ = ln.rstrip("\n").split("\t")
            if len(f_) < 8 or f_[0] == "macro":
                continue
            m = re.search(r"\((-?\d+) ps left\)", f_[7])
            if m and int(f_[2]) >= int(f_[1]) and int(m.group(1)) < NEAR:
                near.add(f_[0])
pf = sys.argv[5] if len(sys.argv) > 5 else os.path.join(os.path.dirname(os.path.abspath(sys.argv[4])), "pinned.txt")
pinned = set(l.strip() for l in open(pf)) if os.path.exists(pf) else set()
raised, lowered = [], []
with open(sys.argv[4], "w") as f:
    f.write("// ratchet.py: lines ever lengthened are pinned at max(%s, %s); the others follow the proposal\n"
            % (sys.argv[1], sys.argv[2]))
    for mac in order:
        p = prop.get(mac, cur[mac])
        if p > cur[mac] and not NOPIN:
            pinned.add(mac)
        v = max(cur[mac], p) if (mac in pinned or RAISE_ONLY) else p
        if p > cur[mac] or (mac in near and RAISE_ONLY):
            v += HEADROOM
        if v > cur[mac]:
            raised.append("%s %d->%d" % (mac, cur[mac], v))
        elif v < cur[mac]:
            lowered.append("%s %d->%d" % (mac, cur[mac], v))
        f.write("`define %s %d%s\n" % (mac, v, "" if v == cur[mac] else "   // was %d" % cur[mac]))
with open(pf, "w") as f:
    f.write("".join(m + "\n" for m in sorted(pinned)))
unf = [r for r in neg if len(r) > 3 and r[3] == "unfixable"]
print("raised %d unfixable %d negative %d lowered %d pinned %d" % (len(raised), len(unf), len(neg), len(lowered), len(pinned))
      + ("" if NEAR is None else " near %d (< %d ps left)" % (len(near & set(order)), NEAR)))
for r in raised:
    print("  raised " + r)
for r in lowered:
    print("  lowered " + r)
for r in unf:
    print("  unfixable " + " ".join(r[:3]))
