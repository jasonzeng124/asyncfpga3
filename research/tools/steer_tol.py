#!/usr/bin/env python3
"""steer_tol.py SKEW_LOG... -- the path-error tolerance of every select gate rule E measured (cells/verify/skew.py's log,
e.g. corner_audit's OUT/skew.log), in formal B24's terms: the request walk -x against the select's cone +x, both from
the launch past their divergence point. A gate holds while (req - D)(1 - x) > (sel - D)(1 + x), i.e. up to
x = (req - sel) / (req + sel - 2 D): rule E's own guard (0.97 x request vs 1.03 x select) is x = 0.03; formal's guide
calls a route fine with no pulses at x <= 0.10 (AUTO_GUARD_E=0.90,1.10). On flow v10's collatz64 s1 this gives 0.078 for
ucond_br6 where formal's xtol.sh found the first pulses at x = 0.08 (research/data/guardx/).
Prints, per log: the weakest steer and the weakest gate of any kind (x, the gate, req / sel / divergence ps), then
"min_x steer X any Y"; with --all every gate, weakest first."""
import re
import sys


def gates(path):
    out, cur = [], None
    for l in open(path, errors="replace"):
        m = re.match(r"^  (\S+)\s+(bd_\w+|bdc_\w+)\s+(\S+)", l)
        if m:
            if cur and "req" in cur and "sel" in cur:
                out.append(cur)
            cur = {"status": m.group(1), "kind": m.group(2), "name": m.group(3), "div": 0}
            continue
        if cur is None:
            continue
        m = re.match(r"^\s+divergence point (-?\d+) ps", l)
        if m:
            cur["div"] = int(m.group(1))
        m = re.match(r"^\s+earliest (-?\d+) ps", l)
        if m:
            cur["req"] = int(m.group(1))
        m = re.match(r"^\s+latest\s+(-?\d+) ps", l)
        if m:
            cur["sel"] = int(m.group(1))
    if cur and "req" in cur and "sel" in cur:
        out.append(cur)
    for g in out:
        den = g["req"] + g["sel"] - 2 * g["div"]
        g["x"] = (g["req"] - g["sel"]) / den if den > 0 else float("nan")
    return out


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    for p in args:
        gs = [g for g in gates(p) if g["x"] == g["x"]]
        if not gs:
            print("%s: no select gate" % p)
            continue
        st = [g for g in gs if g["kind"] == "bd_steer"]
        ws = min(st, key=lambda g: g["x"]) if st else None
        wa = min(gs, key=lambda g: g["x"])
        f = lambda g: "%.3f %s %s (req %d sel %d div %d)" % (g["x"], g["kind"], g["name"].replace("bridge_i.udut.", ""),
                                                             g["req"], g["sel"], g["div"]) if g else "-"
        print("%s: weakest steer %s | weakest gate %s | min_x steer %s any %.3f" % (
            p, f(ws), f(wa), ("%.3f" % ws["x"]) if ws else "-", wa["x"]))
        if "--all" in sys.argv:
            for g in sorted(gs, key=lambda g: g["x"]):
                print("   " + f(g))


if __name__ == "__main__":
    main()
