#!/usr/bin/env python3
"""Row-by-row comparison: tcheck verdicts vs tighten.py rules H and I on one route.

    python3 formal/tools/tcheck/compare.py TCHECK.out TIGHTEN.log [--tsv OUT]

tighten rows: per controller, `enable|close T  data T  guard G  margin M` (H, I).
tcheck rows:  `H|I <ctl> ... <variant> fallback=a/b  PASS|FAIL  margin ...` (6 variants).
For I, tighten reports the worst upstream; tcheck has one row per upstream, and the
minimum margin over them is compared.  The tcheck VERDICT is fastG AND slowG
(H_ONE_CORNER x GUARD band, prjxray data).
"""
import re
import sys
from collections import defaultdict

V = ["sdf", "sdfband", "fast", "slow", "fastG", "slowG"]


def tighten_rows(path):
    rows, sec = {}, None
    for line in open(path):
        if re.match(r"^H\. ", line):
            sec = "H"
        elif re.match(r"^I\. ", line):
            sec = "I"
        elif re.match(r"^[A-Z]\. ", line):
            sec = None
        if sec is None:
            continue
        m = re.match(r"^\s+(\S+)\s+(\d+) links\s+(?:enable|close)\s+(-?\d+)\s+data\s+(-?\d+)"
                     r".*?guard\s+(\d+)\s+margin\s+(-?\d+)\s+(.*)$", line)
        if m:
            ctl = m.group(1)
            rows[(sec, ctl)] = {"t_ref": int(m.group(3)), "t_data": int(m.group(4)),
                                "guard": int(m.group(5)), "margin": int(m.group(6)),
                                "raw": int(m.group(6)) + int(m.group(5)), "verdict": m.group(7).strip()}
        elif re.match(r"^\s+(\S+)\s+.*not audited", line):
            ctl = line.split()[0]
            rows[(sec, ctl)] = {"verdict": "not audited", "margin": None}
    return rows


def tcheck_rows(path):
    rows = defaultdict(lambda: defaultdict(list))
    fb = {}
    for line in open(path):
        f = line.rstrip("\n").split("\t")
        if len(f) < 3:
            continue
        lab = f[0].split()
        rule, ctl, var = lab[0], lab[1], lab[-2]
        fb_ = lab[-1]
        m = None if f[2] == "none" else int(f[2])
        rows[(rule, ctl)][var].append((m, f[1], " ".join(lab[2:-2])))
        fb.setdefault((rule, ctl), []).append(fb_)
    return rows, fb


def main():
    tc, tl = sys.argv[1], sys.argv[2]
    out = sys.argv[sys.argv.index("--tsv") + 1] if "--tsv" in sys.argv else None
    T = tighten_rows(tl)
    C, FB = tcheck_rows(tc)
    keys = sorted(set(T) | set(C))
    lines = []
    hdr = ("rule", "controller", "tighten_raw", "tighten_guard", "tighten_margin", "tighten",
           *[f"tc_{v}" for v in V], "tcheck", "agree", "fallback")
    lines.append("\t".join(hdr))
    stats = defaultdict(int)
    for k in keys:
        t = T.get(k, {})
        c = C.get(k, {})
        mins = {}
        for v in V:
            xs = [m for m, _, _ in c.get(v, []) if m is not None]
            mins[v] = min(xs) if xs else None
        tv = None if t.get("margin") is None else ("PASS" if t["margin"] >= 0 else "FAIL")
        cv = None
        if mins["fastG"] is not None and mins["slowG"] is not None:
            cv = "PASS" if min(mins["fastG"], mins["slowG"]) >= 0 else "FAIL"
        agree = "-" if (tv is None or cv is None) else ("yes" if tv == cv else "NO")
        stats[(k[0], tv, cv)] += 1
        fbs = sorted(set(FB.get(k, [])))
        lines.append("\t".join(str(x) for x in (
            k[0], k[1], t.get("raw", "-"), t.get("guard", "-"), t.get("margin", "-"),
            tv or t.get("verdict", "-"), *[mins[v] if mins[v] is not None else "-" for v in V],
            cv or "-", agree, ",".join(x.replace("fallback=", "") for x in fbs[:3]))))
    txt = "\n".join(lines) + "\n"
    if out:
        open(out, "w").write(txt)
    sys.stdout.write(txt)
    print("\n# rule  tighten  tcheck  count")
    for (r, a, b), n in sorted(stats.items(), key=lambda x: str(x)):
        print(f"# {r}  {a}  {b}  {n}")


if __name__ == "__main__":
    main()
