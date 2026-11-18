#!/usr/bin/env python3
"""dyn_status.py -- every integer test of Dynamatic's integration suite, and how far it gets today.

    python3 research/tools/suite/dyn_status.py OUT.tsv > TABLE.md

Reads, all under research/data/suite/dyn/ unless said otherwise:
  README.md's two "All ... directories" tables (2026-11-17 triage): which tests exist and which are float (out of
      scope: only the `int` rows are listed);
  triage.tsv: the frontend's verdict (fe);
  blockers.tsv: every refusal of bdc today (research/tools/suite/dyn_blockers.py, rerun on build/frontend);
  emit.tsv: emit.py --no-top per mode (default, BDC_AUTO=1, BDC_HOST_MEM=1): ok or the first error;
  research/tools/suite/kernels.txt: which are in the suite;
  rtl.tsv: research/tools/suite/rtl_bench.sh verdicts (the bench's own Verilog in RTL), default and BDC_AUTO=1;
  smoke.tsv: routed smoke verdicts (seed, flow, worst corner, the gate's line).
Status is the furthest stage reached: does not compile (frontend | bdc: blockers) < emits < in the suite < passes RTL
< passes routed smoke.  A row whose RTL or smoke FAILED says so: "wrong answer" and "deadlock" are results.
"""
import csv, os, re, sys

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "data", "suite", "dyn")
R = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..")


def tsv(name):
    p = os.path.join(D, name)
    if not os.path.exists(p):
        return []
    return list(csv.DictReader(open(p), delimiter="\t"))


def main():
    rows = []
    for l in open(os.path.join(D, "README.md")):
        m = re.match(r"\| (?:memory/|sharing/)?([a-z_0-9]+) \| (int|\*\*float\*\*) \|", l)
        if m:
            rows.append((("memory/" if "| memory/" in l else "sharing/" if "| sharing/" in l else "")
                         + m.group(1), m.group(1), m.group(2) == "int"))
    seen, tests = set(), []
    for full, name, isint in rows:
        if name not in seen and isint:
            seen.add(name)
            tests.append((full, name))
    fe = {r["name"]: r["fe"] for r in tsv("triage.tsv")}
    bl = {r["name"]: r for r in tsv("blockers.tsv")}
    em = {r["name"]: r for r in tsv("emit.tsv")}
    rtl = {}
    for r in tsv("rtl.tsv"):
        rtl.setdefault(r["name"], {})[r["flow"]] = r
    sm = {}
    for r in tsv("smoke.tsv"):
        sm.setdefault(r["name"], []).append(r)
    suite = set(l.split()[0] for l in open(os.path.join(R, "research", "tools", "suite", "kernels.txt"))
                if l.strip() and not l.startswith("#"))
    out = csv.writer(open(sys.argv[1], "w"), delimiter="\t", lineterminator="\n")
    out.writerow(["test", "status", "blockers", "emit_default", "emit_auto", "suite", "rtl_default", "rtl_auto",
                  "smoke"])
    print("| test | status today | what blocks it | emits (default / AUTO) | in the suite | RTL default / AUTO "
          "| routed smoke (seed 1, worst corner) |")
    print("|---|---|---|---|---|---|---|")
    counts = {}
    for full, name in tests:
        f = fe.get(name, "?")
        b = bl.get(name, {}).get("blockers", "-") if f == "ok" else "frontend"
        e = em.get(name, {})
        ed, ea = e.get("default", "-"), e.get("auto", "-")
        ins = name in suite
        rd = rtl.get(name, {}).get("default", {}).get("verdict", "")
        ra = rtl.get(name, {}).get("auto", {}).get("verdict", "")
        smk = sm.get(name, [])
        smv = "; ".join("%s %s: %s" % (s["flow"], s["seed"], s["verdict"]) for s in smk)
        if f != "ok":
            st = "does not compile (frontend)"
        elif b not in ("-", ""):
            st = "does not compile (bdc)"
        elif ed != "ok":
            st = "does not compile (bdc: %s)" % ed
        elif not ins:
            st = "emits"
        elif any(s["verdict"].startswith("PASS") for s in smk):
            st = "passes routed smoke"
        elif rd.startswith("PASS") or ra.startswith("PASS"):
            st = "passes RTL"
        else:
            st = "in the suite"
        counts[st] = counts.get(st, 0) + 1
        short = lambda v: (v.split(" RTL")[0] if v else "-")
        out.writerow([full, st, b, ed, ea, "yes" if ins else "no", rd, ra, smv])
        print("| %s | %s | %s | %s / %s | %s | %s / %s | %s |" % (
            full, ("**%s**" % st) if "passes" in st else st, "" if b == "-" else b.replace(",", ", "),
            ed, ea, "yes" if ins else "-", short(rd), short(ra), smv or "-"))
    print()
    print("%d integer tests: " % len(tests) + ", ".join("%s %d" % kv for kv in sorted(counts.items(), key=lambda x: -x[1])))


if __name__ == "__main__":
    main()
