#!/usr/bin/env python3
"""tools-B/preload/preload_net.py (shard B, UNTRUSTED): preload a loop variable's ENTRY value in a decoded bench net.

    python3 preload_net.py NET.json ROUTED.json OUT.json --link ulink_n6 --value 0x3ffffff0 [--width 32]
           [--dump DUMP.json]   (check, on an ordinary run's simx dump, that the edited nodes never moved)

Why: research's kernels start their loop counters from a CONSTANT (xorshift: i = 0 enters umux0's x input through the
pipe ulink_n6, whose stage latches read GND). A counter that must count to ~2^30 before its long carry happens can
never be simulated there. Here the latch state nodes of the entry link (every stage, both LUT6_2 halves) are made to
hold VALUE from t = 0: each decoded gate SLICE_XxYy.<L>LUT.O5/O6 that nextpnr placed for <link>...lat.pair[j].u
(O5 = bit j, O6 = bit j+1, bd_latch) or ...lat.odd.u (bit W-1) gets the constant truth table of its bit of VALUE. Its
pins and arcs stay (they no longer matter). In the original these nodes are constant 0 for the whole run (checked with
--dump), so the edit is exactly "the same bitstream with the entry constant tied to VALUE instead of 0"; every other
gate, pip and delay is untouched. The loop then starts at i = VALUE at its header, and the oracle is the C loop run
from that state (oracle.c), valid while VALUE < n (the hardware's rotated loop tests after the body).
Not the same as poking a register mid-run: nothing on the entry path moves at the call, as in the original.
"""
import argparse, json, re, sys
ap = argparse.ArgumentParser()
ap.add_argument("net"); ap.add_argument("routed"); ap.add_argument("out")
ap.add_argument("--link", required=True); ap.add_argument("--value", required=True)
ap.add_argument("--width", type=int, default=32); ap.add_argument("--dump", default=None)
ap.add_argument("--inst", default="bridge_i.udut.")
ap.add_argument("--orig", default="0", help="the entry constant in the original (isprime's d = 2): with --dump, each edited "
                "node must hold its bit of ORIG from --settle ps on and never move after it")
ap.add_argument("--settle", type=int, default=0, help="ps: with --orig != 0 the latches take the constant once, as their "
                "first transparent phase after reset (isprime ulink_n16 bit 1 at ~436 ns, before any call); default 0")
a = ap.parse_args()
V = int(a.value, 0)
N = json.load(open(a.net)); G = N["gates"]
cells = json.load(open(a.routed))["modules"]["top"]["cells"]
byname = {g["name"]: gi for gi, g in enumerate(G)}
pat = re.compile(r"^" + re.escape(a.inst + a.link) + r"\.(?:many\.stage\[(\d+)\]\.u\.)?lat\.(?:pair\[(\d+)\]|odd)\.u\$(LUT[56])$")
edits = {}
for cn, c in cells.items():
    m = pat.match(cn)
    if not m: continue
    bel = c["attributes"].get("NEXTPNR_BEL", "")
    b = re.match(r"^(SLICE_X\d+Y\d+)/([A-D])([56])LUT$", bel)
    if not b: sys.exit("preload: %s placed at %r, not a slice LUT" % (cn, bel))
    stage, j, half = m.group(1) or "0", m.group(2), m.group(3)
    if j is None: bit = a.width - 1   # odd bit: a single LUT6 (its O6)
    else: bit = int(j) + (0 if half == "LUT5" else 1)
    gname = "%s.%sLUT.O%s" % b.groups()
    if b.group(3) != half[-1]: sys.exit("preload: %s is %s but placed on O%s" % (cn, half, b.group(3)))
    gi = byname.get(gname)
    if gi is None: sys.exit("preload: no decoded gate %s for %s" % (gname, cn))
    if gi in edits: sys.exit("preload: gate %s claimed twice" % gname)
    edits[gi] = (cn, stage, bit)
bits_seen = {}
for gi, (cn, st, bit) in edits.items(): bits_seen.setdefault(st, set()).add(bit)
for st, bs in sorted(bits_seen.items()):
    if bs != set(range(a.width)): sys.exit("preload: stage %s covers bits %s, not 0..%d" % (st, sorted(bs), a.width - 1))
if a.dump:
    D = json.load(open(a.dump))["nodes"]
    for gi, (cn, st, bit) in edits.items():
        h = D.get(str(G[gi]["out"]))
        ob = (int(a.orig, 0) >> bit) & 1
        if h is None: h = [False, []]
        v0, ts = bool(h[0]), list(h[1])
        late = [t for t in ts if t > a.settle]
        final = v0 ^ (len(ts) % 2 == 1)
        if late or final != bool(ob):
            sys.exit("preload: %s (%s) does not hold %d from %d ps in the reference run: %s" % (G[gi]["name"], cn, ob, a.settle, str(h)[:120]))
    print("preload: all %d edited nodes hold their bit of %s from %d ps on in %s" % (len(edits), a.orig, a.settle, a.dump), file=sys.stderr)
for gi, (cn, st, bit) in sorted(edits.items()):
    k = G[gi]["k"]; v = (V >> bit) & 1
    G[gi]["init"] = ((1 << (1 << k)) - 1) if v else 0
    G[gi].setdefault("prov", {})["preload"] = "%s bit %d = %d (was a %s latch half)" % (a.link, bit, v, cn)
json.dump(N, open(a.out, "w"))
print("preload: %s = %#x on %d latch gates (%d stages x %d bits) -> %s" % (a.link, V, len(edits), len(bits_seen), a.width, a.out), file=sys.stderr)
