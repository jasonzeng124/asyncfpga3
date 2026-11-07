#!/usr/bin/env python3
"""analyze.py -- summarise an `xaudit --all` report on the gcd_hw rig netlist.

    python3 -I analyze.py REPORT.txt [--release-ps 20000] [--list N]

Only re-reads what xaudit printed (presentation; trusted like xaudit's own
classifier).  Splits storage nodes into DATA latch bits (bd_latch, pairs and the odd bit:
'.lat.' in the cell name) and CONTROL storage (C-elements, arbiter state,
mux joins, everything else), and for each class counts xaudit's verdicts:
  never-resolved  X from power-up to the horizon (a latch never written)
  clean           every X window is power-up or a bounded transition p -> q
  GLITCH / STORED / UNRESOLVED  -- the flags.
It also reconstructs the waveform of the rig's observable outputs (rig_lap,
rig_ok, rig_err, rig_res_data[*]) from the X windows and the values between them.
"""
import argparse
import collections
import re

HEAD = re.compile(r"^  (STORAGE|node   ) (\S+) \(wire (\d+) '([^']*)'\): final (\S), (\d+) flagged")
XW = re.compile(r"^    X \[(\d+), (\d+)\] ps: (.*)$")


def kind_of(line):
    if "power-up, resolved" in line:
        return "powerup"
    if "power-up, NEVER RESOLVED" in line:
        return "never"
    if "UNRESOLVED" in line:
        return "UNRESOLVED"
    if "POSSIBLE GLITCH" in line:
        return "GLITCH"
    if "STORED X" in line:
        return "STORED"
    if "transition" in line:
        return "transition"
    return "?"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("report")
    ap.add_argument("--release-ps", type=int, default=20000)
    ap.add_argument("--list", type=int, default=40)
    a = ap.parse_args()
    nodes = []
    cur = None
    horizon = None
    for line in open(a.report):
        m = re.search(r"horizon (\d+) steps = (\d+) ps", line)
        if m:
            horizon = int(m.group(2))
        m = HEAD.match(line)
        if m:
            cur = {"stor": m.group(1) == "STORAGE", "name": m.group(2), "net": m.group(4),
                   "final": m.group(5), "flag": int(m.group(6)), "win": []}
            nodes.append(cur)
            continue
        m = XW.match(line)
        if m and cur is not None:
            cur["win"].append((int(m.group(1)), int(m.group(2)), kind_of(m.group(3)), m.group(3)))
    print("report %s: %d nodes printed, %d storage, horizon %s ps" % (
        a.report, len(nodes), sum(n["stor"] for n in nodes), horizon))

    def cls(n):
        return "data" if ".lat." in n["name"] else "control"

    for c in ("control", "data"):
        S = [n for n in nodes if n["stor"] and cls(n) == c]
        cnt = collections.Counter()
        first = []
        for n in S:
            ks = [w[2] for w in n["win"]]
            bad = [w for w in n["win"] if w[2] in ("GLITCH", "STORED", "UNRESOLVED")]
            if "never" in ks:
                cnt["never-resolved (X power-up to horizon)"] += 1
            elif bad:
                cnt["flagged: " + bad[0][2]] += 1
                first.append((bad[0][0], n, bad[0]))
            else:
                cnt["clean"] += 1
        print("\n%s storage: %d nodes" % (c.upper(), len(S)))
        for k, v in sorted(cnt.items()):
            print("  %-45s %d" % (k, v))
        first.sort(key=lambda r: r[0])
        if first:
            print("  earliest flags (first bad window per node):")
            for t, n, w in first[:a.list]:
                print("    %7d..%-7d ps  %-10s %s  (net %s)" % (w[0], w[1], w[2], n["name"], n["net"]))
        if c == "control":
            nv = [n for n in S if any(w[2] == "never" for w in n["win"])]
            for n in nv[:a.list]:
                print("    never-resolved control node: %s (net %s)" % (n["name"], n["net"]))

    # observables
    def pn(txt):
        m = re.search(r"transition (\S) -> (\S) ", txt) or re.search(r"(\S) -> X -> (\S)", txt)
        if m:
            return m.group(1), m.group(2)
        m = re.search(r"after (\S),", txt)
        return (m.group(1) if m else None), None

    def wave(n):
        """[(t0, t1, v)] segments; v in 0/1/X; the value between two X windows is the
        'next' value of the first (or the 'prev' value of the second, or final)."""
        segs = []
        t = 0
        nxt = None
        W = n["win"]
        for i, (s, e, k, txt) in enumerate(W):
            p, q = pn(txt)
            if s > t:
                segs.append((t, s - 1, nxt or p or "?"))
            segs.append((s, e, "X"))
            nxt = q
            t = e + 1
        if horizon is not None and t <= horizon:
            segs.append((t, horizon, nxt or n["final"]))
        return segs

    byname = {n["net"]: n for n in nodes}
    print("\nOBSERVABLE OUTPUTS (net: segments t0..t1=v, X = undetermined)")
    for nm in ("rig_rst", "urig.out0_req", "rig_lap", "rig_ok", "rig_err"):
        n = byname.get(nm)
        if n:
            print("  %-14s %s" % (nm, "  ".join("%d..%d=%s" % s for s in wave(n))))
    lap = byname.get("rig_lap")
    if lap:
        rises = [s for s in wave(lap) if s[2] == "1"]
        if rises:
            t = rises[0][0]
            bits = {}
            for nm, n in byname.items():
                m = re.match(r"rig_res_data\[(\d+)\]$", nm)
                if m:
                    v = "?"
                    for s in wave(n):
                        if s[0] <= t <= s[1]:
                            v = s[2]
                    bits[int(m.group(1))] = v
            s = "".join(bits.get(i, "?") for i in range(31, -1, -1))
            print("  rig_res_data at the first binary rig_lap=1 (t=%d ps): %s%s" % (
                t, s, ("  = %d" % int(s, 2)) if set(s) <= {"0", "1"} else ""))
        else:
            print("  rig_lap never binary 1 within the horizon")


if __name__ == "__main__":
    main()
