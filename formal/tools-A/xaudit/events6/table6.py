"""table6.py -- compare xevents5 (Lean checker, per-pin) with ana5.py (atomic, events5) stage by stage.

    python3 table6.py OUTDIR > table6.txt
OUTDIR = run6.sh's $O (per seed: skel.json, skel_<c>.bands.json, cert_<c>.txt). Reads
xe5_<s>_<c>.txt next to this script. UNTRUSTED report code.
"""
import collections
import io
import os
import re
import sys
import contextlib

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "events4"))
sys.path.insert(0, os.path.join(HERE, "..", "events5"))
from model import Model  # noqa: E402
from ana import Ana  # noqa: E402
import ana5  # noqa: E402


def ana5_bad(skel, bands):
    Ana.W.__defaults__[0].clear()  # ana.py's W cache is a shared mutable default: one per process in ana5.py
    M = Model(skel, bands)
    A = Ana(M)
    r = A.run()
    C = ana5.Contig5(A)
    c5 = [C.pin(m["stage"], m["pin"], ana5.stage_net(M, m["stage"], m["pin"]), m["src"]) for m in r["multis"]]
    real = [e for e in r["stages"] if not e["virtual"]]
    stg = {e["stage"] for e in real}
    bad = collections.defaultdict(set)
    for e in real:
        if e["rule"] == "Back" and e["margin"] <= 0:
            bad[e["stage"]].add("Back")
        if e["rule"] == "Guard" and (e["entry"] is None or e["entry"] <= 0):
            bad[e["stage"]].add("GuardEntry")
        if e["rule"] == "Guard" and (e["exit"] is None or e["exit"] <= 0):
            bad[e["stage"]].add("GuardExit")
        if e["rule"] == "NONE":
            bad[e["stage"]].add("NONE")
    for m in c5:
        if m["stage"] in stg and (m.get("margin") is None or m["margin"] <= 0):
            bad[m["stage"]].add("Contig5")
    backs = [e["margin"] for e in real if e["rule"] == "Back"]
    c5m = [m["margin"] for m in c5 if m.get("margin") is not None]
    rules = {(e["stage"], str(e["pin"])): e["rule"] for e in r["stages"]}
    return stg, bad, min(backs), min(c5m), sum(m["ok"] for m in r["merges"]), len(r["merges"]), rules


def xe5(path):
    t = open(path).read()
    g = lambda pat: re.search(pat, t)
    res = re.findall(r"RESIDUAL (Back|Line|Excl) (\S+)(?: pin(\d+))?[^\n]*", t)
    out = dict(
        recog=g(r"Recog6 node failures (\d+)").group(1), ok=g(r"Net4.OK (\w+)").group(1),
        back=g(r"Back pins (\d+)/(\d+) certified \(strict\), min margin (-?\d+)").groups(),
        line=g(r"line pins (\d+)/(\d+) certified \(strict\), min margin (-?\d+)").groups(),
        merge=g(r"merges (\d+)/(\d+) certified").groups(),
        resid=res, verdict=g(r"VERDICT (.*?) \(").group(1))
    return out


def cert_reasons(path):
    rs = {}
    for line in open(path):
        m = re.match(r"\s+UNCERTIFIED (back|line|excl) (\S+?)(?: pin(\d+))?: (.*)", line)
        if m:
            rs[(m.group(1), m.group(2), m.group(3))] = m.group(4)
    return rs


def cat(reason):
    if reason is None:
        return "margin"
    if "guarded delay-line" in reason:
        return "guard-line"
    if "cannot express" in reason or "S -> merge" in reason:
        return "U3|W-E4x"
    if "U witness" in reason:
        return "U3"
    if "multi-bit" in reason or "3-arm" in reason:
        return "W-E4x"
    if "no walk" in reason or "no cycle" in reason:
        return "no-walk(cascade/NONE)"
    return "other"


def main():
    O = sys.argv[1]
    print("A-events6: xevents5 (Lean, per-pin, strict) against ana5.py (atomic, strict, contig5)")
    print("columns: Recog6 failures | Net4.OK | Back cert/total min | line cert/total min | merges cert/total |"
          " ana5 Back min, contig5 min, merges | residual by cause\n")
    for s in "d345":
        for c in ("slow", "fast", "indep", "gb"):
            xp = os.path.join(HERE, f"xe5_{s}_{c}.txt")
            if not os.path.exists(xp) or "VERDICT" not in open(xp).read():
                continue
            X = xe5(xp)
            with contextlib.redirect_stdout(io.StringIO()):
                stg, bad, bmin, c5min, mok, mn, rules = ana5_bad(os.path.join(O, s, "skel.json"),
                                                          os.path.join(O, s, f"skel_{c}.bands.json"))
            R = cert_reasons(os.path.join(O, s, f"cert_{c}.txt"))
            causes = collections.Counter()
            xstages = collections.defaultdict(set)
            for kind, name, pin in X["resid"]:
                r = R.get((kind.lower(), name, pin or None))
                if r is None and kind == "Excl":
                    r = R.get(("excl", name, None))
                if r is None and kind == "Back" and rules.get((name, pin)) == "Guard":
                    r = "guarded delay-line pin (Net4 guard pins have one copy)"
                causes[(kind, cat(r) if (kind.lower(), name, pin or None) in R or r else "margin")] += 1
                xstages[name].add(kind + ":" + (cat(r) if r else "margin"))
            print(f"{s} {c:5s} recog-fail {X['recog']} OK {X['ok']} | Back {X['back'][0]}/{X['back'][1]} min {X['back'][2]}"
                  f" | line {X['line'][0]}/{X['line'][1]} min {X['line'][2]} | merges {X['merge'][0]}/{X['merge'][1]}"
                  f" | ana5 Back min {bmin} contig5 min {c5min} merges {mok}/{mn} | {X['verdict']}")
            print("    residual: " + ", ".join(f"{k[0]}/{k[1]} {v}" for k, v in sorted(causes.items())))
            # stage by stage: real stages
            real_x = {n for n in xstages if n in stg}
            ana_bad_nonguard = {n for n, r in bad.items() if r - {"GuardEntry", "GuardExit"}}
            both = sorted(real_x & ana_bad_nonguard)
            only_x = sorted(real_x - ana_bad_nonguard)
            only_a = sorted(ana_bad_nonguard - real_x)
            guard_only = sorted(n for n, r in bad.items() if not (r - {"GuardEntry", "GuardExit"}))
            print(f"    stages: ana5 bad (non-guard) {len(ana_bad_nonguard)}, xevents5 residual {len(real_x)}, both {len(both)}, "
                  f"xevents5 only {len(only_x)}, ana5 only {len(only_a)}; ana5 guard-only bad {len(guard_only)} (GuardOK is a hypothesis in Lean)")
            for n in both:
                print(f"      BOTH   {n}: ana5 {sorted(bad[n])} / xevents5 {sorted(xstages[n])}")
            for n in only_a:
                print(f"      ANA5   {n}: {sorted(bad[n])}")
            byc = collections.Counter(tuple(sorted(xstages[n])) for n in only_x)
            for k, v in byc.most_common():
                print(f"      XE5    {v} stages: {list(k)}")
            for n in only_x:
                if any(":margin" in t for t in xstages[n]):
                    print(f"      XE5-margin {n}: {sorted(xstages[n])}")
            print()


if __name__ == "__main__":
    main()
