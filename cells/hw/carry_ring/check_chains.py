#!/usr/bin/env python3
"""check_chains.py -- are the carry chains and MUXF7 stages really in the rings, in the BITS?

    python3 cells/hw/carry_ring/check_chains.py ROUTED.json FID/fasm_routed.json

ROUTED.json is nextpnr's routed design; fasm_routed.json the netlist
cells/gls/fid/fasm2net.py decoded from the .bit.  Checks, on the DECODED
netlist (connectivity and configuration from the bits only):
  1. carry chains: follow CIN <- CO3 between CARRY4 sites; the chain lengths
     must be exactly 8 x {1, 4, 16, 32} for the rings plus 8 x 8 for the slot
     counters (32-bit increment), and every ring chain's sites must be the
     sites nextpnr placed that ring's CARRY4s on (routed JSON BEL), in order;
  2. every ring CARRY4 propagates: S1..S3 (and S0 past the first) are driven
     by a LUT, the first has its carry-in from the constant (CYINIT 1 / no CIN)
     and the loop leaves through CO3 of the last;
  3. every MUXF7 of an F ring is a SELMUX2_1 site in the decoded netlist whose
     S0 is driven, and the F rings hold 8 x 8 + 8 x 16 of them.
Prints one line per check and ALL CHAINS OK / FAIL; exit 0 / 1.
"""
import json
import re
import sys
from collections import Counter


def mod(path):
    d = json.load(open(path))
    return list(d["modules"].values())[0]


def main():
    R, D = mod(sys.argv[1]), mod(sys.argv[2])
    rc = R["cells"]
    dc = D["cells"]
    # routed: ring CARRY4 -> BEL, in chain order
    ring_c4 = {}
    for name, c in rc.items():
        m = re.match(r"grp\[(\d+)\]\.ro\[(\d+)\]\.cring\.c4\[(\d+)\]\.cc$", name)
        if m and c["type"] == "CARRY4":
            ring_c4.setdefault((int(m.group(1)), int(m.group(2))), {})[int(m.group(3))] = \
                c["attributes"]["NEXTPNR_BEL"]
    # decoded: CO3 net -> site, then chains
    c4 = {k: v for k, v in dc.items() if v["type"] == "CARRY4"}
    co3 = {}
    for k, v in c4.items():
        n = v["connections"].get("CO3", [])
        if n:
            co3[n[0]] = k
    prev = {}
    for k, v in c4.items():
        n = v["connections"].get("CIN", [])
        if n and n[0] in co3:
            prev[k] = co3[n[0]]
    nxt = {p: k for k, p in prev.items()}
    heads = [k for k in c4 if k not in prev]
    chains = []
    for h in heads:
        ch = [h]
        while ch[-1] in nxt:
            ch.append(nxt[ch[-1]])
        chains.append(ch)
    lens = Counter(len(c) for c in chains)
    want = Counter({1: 8, 4: 8, 16: 8, 32: 8})
    want[8] += 8                                     # the eight 32-bit slot counters
    ok = True
    print("1. decoded carry chains by length: %s (want %s)" % (dict(sorted(lens.items())), dict(sorted(want.items()))))
    ok &= lens == want
    by_site = {tuple(c): c for c in chains}
    miss = 0
    for (g, b), d in sorted(ring_c4.items()):
        bels = tuple(d[i] for i in range(len(d)))
        if bels not in by_site:
            miss += 1
            if miss <= 3:
                print("   ring g%d.b%d: routed chain %s..%s (%d) is not a chain in the bits" % (g, b, bels[0], bels[-1], len(bels)))
    print("   %d of %d ring chains are the same site sequence in the bits as in the routed JSON" % (
        len(ring_c4) - miss, len(ring_c4)))
    ok &= miss == 0 and len(ring_c4) == 32
    bad = 0
    for (g, b), d in ring_c4.items():
        bels = [d[i] for i in range(len(d))]
        for i, s in enumerate(bels):
            con = dc[s]["connections"]
            pins = ["S1", "S2", "S3"] + (["S0"] if i else [])
            for p in pins:
                src = con.get(p, [])
                if not src:
                    bad += 1
            if i == 0 and con.get("CIN"):
                bad += 1
            if i == len(bels) - 1 and not con.get("CO3"):
                bad += 1
        if str(dc[bels[0]].get("parameters", {}).get("PRECYINIT_CONST")) != "1":   # decoded from the bits
            bad += 1
    print("2. ring CARRY4 S pins driven / first carry-in constant / last CO3 used: %s" % ("ok" if not bad else "%d problems" % bad))
    ok &= bad == 0
    f7_rt = [n for n, c in rc.items() if re.match(r"grp\[\d+\]\.ro\[\d+\]\.fring\.fk\[\d+\]\.m$", n)]
    bels = [rc[n]["attributes"]["NEXTPNR_BEL"] for n in f7_rt]
    sel = sum(1 for bl in bels if bl in dc and dc[bl]["type"] == "SELMUX2_1" and dc[bl]["connections"].get("S0"))
    print("3. F-ring MUXF7: %d in the routed JSON (want %d), %d decoded as SELMUX2_1 with S0 driven" % (
        len(f7_rt), 8 * 8 + 8 * 16, sel))
    ok &= len(f7_rt) == 192 and sel == 192
    print("ALL CHAINS OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
