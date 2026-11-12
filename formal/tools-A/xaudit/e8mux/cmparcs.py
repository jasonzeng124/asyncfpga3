#!/usr/bin/env python3
"""E8Mux: which prjxray IC rows does the OUTMUX fix change, and are they exactly the right ones?
    python3 -I cmparcs.py ROUTED.json ARCS_OLD.tsv ARCS_NEW.tsv [ARCS_R7.tsv]
For every IC row: driver cell, its kind (O6 / O5 LUT, MUXF7/F8, CARRY4, FF, other) from the routed
JSON (NEXTPNR_BEL), and the shift new - old per column.  Checks:
  (a) every changed row's driver is NOT an O6 LUT (the fix must not touch O6 exits);
  (b) per driver kind: number of rows changed / unchanged, shift range per column;
  (c) with ARCS_R7 (research 7dc5dde): rows whose src is a LUT/MUXF/CARRY4 output and whose dst is a
      LUT / MUXF / CARRY4 input pin must be equal new vs r7 (differences listed)."""
import collections, json, sys
routed, fo, fn = sys.argv[1:4]
fr = sys.argv[4] if len(sys.argv) > 4 else None
cells = json.load(open(routed))["modules"]["top"]["cells"]
def kind(src):
    cn, _, port = src.rpartition("/")
    c = cells.get(cn)
    if c is None:
        return "?"
    t = c["type"]
    if t == "SLICE_LUTX":
        return "LUT-" + ("O5" if c["attributes"].get("NEXTPNR_BEL", "").endswith("5LUT") else "O6")
    if t == "SELMUX2_1":
        return "MUXF"
    return t
def load(p):
    d = {}
    with open(p) as f:
        h = f.readline().rstrip("\n").split("\t")
        for line in f:
            r = line.rstrip("\n").split("\t")
            if r[0] == "IC":
                d[(r[1], r[2])] = tuple(int(x) for x in r[4:8])
    return d
O, N = load(fo), load(fn)
assert set(O) == set(N), "row sets differ"
st = collections.defaultdict(lambda: [0, 0, [10**9] * 4, [-10**9] * 4])
bad = []
for k in O:
    kd = kind(k[0])
    s = st[kd]
    dlt = tuple(b - a for a, b in zip(O[k], N[k]))
    if any(dlt):
        s[0] += 1
        s[2] = [min(x, y) for x, y in zip(s[2], dlt)]
        s[3] = [max(x, y) for x, y in zip(s[3], dlt)]
        if kd == "LUT-O6":
            bad.append(k)
    else:
        s[1] += 1
print("IC rows %d; per driver kind: changed / unchanged, shift (new-old ps) min..max per FAST_MIN FAST_MAX SLOW_MIN SLOW_MAX" % len(O))
for kd, s in sorted(st.items()):
    rng = " ".join("%d..%d" % (a, b) for a, b in zip(s[2], s[3])) if s[0] else "-"
    print("  %-8s %6d / %6d   %s" % (kd, s[0], s[1], rng))
print("(a) changed rows driven by an O6 LUT: %d %s" % (len(bad), bad[:3]))
if fr:
    R = load(fr)
    comb = lambda p: kind(p) in ("LUT-O5", "LUT-O6", "MUXF", "CARRY4")
    ks = [k for k in N if comb(k[0]) and comb(k[1])]
    dif = [k for k in ks if R.get(k) != N[k]]
    print("(c) comb->comb IC rows %d; new != r7 (7dc5dde): %d" % (len(ks), len(dif)))
    for k in dif[:10]:
        print("    %s -> %s new %s r7 %s" % (k[0], k[1], N[k], R.get(k)))
