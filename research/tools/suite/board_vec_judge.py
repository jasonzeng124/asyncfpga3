#!/usr/bin/env python3
"""board_vec_judge.py EXPFILE LOG [MEMEXP] -- judge a board run of cells/hw/xsdb_bench_vec.tcl (or a GLS run.log of
the same vectors) by research/tools/eventgraph/bench_gate.sh's rules, and say so in one line:

    PASS k/n ...   exit 0   every call's last result = EXPFILE's line (derived from the C: research/tools/suite/
                            oracle.sh / oracle_mem.sh), every run of the call agreed (mism_st bit 0 clear), every run
                            completed (completed == n), no x in SIG; with MEMEXP (oracle_mem.sh's ORACLE_MEMOUT, the
                            C's arrays after each call; the run needs memdump = 1) every array matched; no fill failure,
                            no BENCHMEMCHK mismatch
    FAIL k/n ...   exit 1   anything else, the calls that failed and why
    exit 2                  nothing to judge: no EXPFILE line, no BENCHRES line, or the run stopped early (no
                            BENCHSUMMARY line: a board script that died mid-run)
A `void` EXPFILE line (a kernel that returns nothing) passes only on its arrays, so only with MEMEXP -- as in the gate.
The gate's GLS-only checks (the runt monitor, RAMB18 timing events, the bits-decoded netlist's verdict) have no board
counterpart and are not applied here."""
import re
import sys


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    exp = open(sys.argv[1]).read().split()
    memexp = {}
    if len(sys.argv) > 3 and sys.argv[3]:
        for l in open(sys.argv[3]):
            d = dict(re.findall(r"(\w+)=(\S+)", l))
            if "call" in d and "mem" in d:
                memexp[(int(d["call"]), int(d["mem"]))] = d["data"]
    got, memgot, membad, why = {}, {}, set(), {}
    summary = None
    for l in open(sys.argv[2], errors="replace"):
        if l.startswith("BENCHRES"):
            d = dict(re.findall(r"(\w+)=(\S+)", l)); got[int(d["batch"])] = d
            d["_done"] = l.rstrip().endswith("DONE")
        elif l.startswith("BENCHMEMCHK"):
            d = dict(re.findall(r"(\w+)=(\S+)", l))
            if int(d["bad"]):
                membad.add(int(d["batch"])); why[int(d["batch"])] = "memory read-back: %s bad" % d["bad"]
        elif l.startswith("BENCHMEM ") and "FILL FAILED" in l:
            j = int(re.search(r"batch=(\d+)", l).group(1)); membad.add(j); why[j] = "memory fill failed"
        elif l.startswith("BENCHMEM "):
            d = dict(re.findall(r"(\w+)=(\S+)", l)); memgot[(int(d["batch"]), int(d["mem"]))] = d["data"]
        elif l.startswith("BENCHSUMMARY"):
            summary = l.strip()
    if not exp or not got or summary is None or not summary.startswith("BENCHSUMMARY batches="):
        print("NOTHING TO JUDGE: %d expected line(s), %d BENCHRES line(s), summary %s" % (
            len(exp), len(got), summary or "missing (the run stopped early)"))
        return 2
    for (j, m), v in memexp.items():
        if memgot.get((j, m)) != v:
            membad.add(j); why.setdefault(j, "array %d after the call differs from the C's" % m)
    ok, bad = 0, []
    for j, e in enumerate(exp):
        g = got.get(j)
        if g is None:
            bad.append("%d: no result" % j); continue
        if j in membad:
            bad.append("%d: %s" % (j, why[j])); continue
        if g["completed"] != g["n"] or not g["_done"]:
            bad.append("%d: %s/%s runs completed%s" % (j, g["completed"], g["n"], "" if g["_done"] else ", HANG")); continue
        if int(g.get("mism_st", "0"), 16) & 1:
            bad.append("%d: the runs disagreed (mism_st %s)" % (j, g["mism_st"])); continue
        if re.search(r"[xXzZ]", g.get("sig", "")):
            bad.append("%d: x in SIG" % j); continue
        if e == "void":
            if g["odata"] == "00000000" and any(c == j for c, _ in memexp):
                ok += 1
            else:
                bad.append("%d: void call with no array oracle" % j)
            continue
        if g["odata"].lower() != e.lower():
            bad.append("%d: odata %s, the C says %s" % (j, g["odata"], e)); continue
        ok += 1
    extra = len([j for j in got if j >= len(exp)])
    verdict = "PASS" if ok == len(exp) else "FAIL"
    print("%s %d/%d%s%s" % (verdict, ok, len(exp), (" | " + "; ".join(bad[:8]) + (" ..." if len(bad) > 8 else "")) if bad else "",
                            " | %d call(s) beyond EXPFILE ignored" % extra if extra else ""))
    return 0 if verdict == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
