#!/usr/bin/env python3
"""aug_board_vectors.py BUILD OUT_PREFIX -- the board's FIXED-mode latencies for one August bench build, from its logs.

    python3 research/tools/aug_board_vectors.py ipow_bench_gen $S/aug/ipow

Reads research/board/aug/README.md for the logs that programmed BUILD's .bit with match=yes (the log measured this
exact file), and from each log the first FIXED-mode section: "FIXED-mode repeatability: op0=A op1=B, N=n" and the
"completed=n latmin=L latmax=H ... odata=R" line under it.  Writes
  OUT_PREFIX.tsv   op0 op1 latmin latmax odata log   (one row per distinct (op0, op1); repeats must agree on odata)
  OUT_PREFIX.hex   "op0 op1" in hex, one vector per line, for ps7_bench.v +VECFILE
Board logs are data; nothing here is pasted from a run of the simulator.
"""
import os, re, sys

AUG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "board", "aug")


def main():
    build, out = sys.argv[1:3]
    readme = open(os.path.join(AUG, "README.md")).read()
    m = re.search(r"^- \*\*%s\*\*: (.*)$" % re.escape(build), readme, re.M)
    if not m:
        sys.exit("aug_board_vectors: %s not in README.md's per-log list" % build)
    logs = [x for x in re.findall(r"`(_[^`]+\.log)`( \(NO\))?", m.group(1)) if not x[1]]
    rows = {}
    for name, _ in logs:
        txt = open(os.path.join(AUG, "logs", name)).read()
        a = re.search(r"FIXED-mode repeatability: op0=(\d+) op1=(\d+), N=(\d+)", txt)
        if not a:
            continue
        b = re.search(r"completed=(\d+) latmin=(\d+) latmax=(\d+).*?odata=(\d+)", txt[a.end():])
        if not b or b.group(1) != a.group(3):
            continue
        key = (int(a.group(1)), int(a.group(2)))
        row = (int(b.group(2)), int(b.group(3)), int(b.group(4)), name)
        if key in rows and rows[key][2] != row[2]:
            sys.exit("aug_board_vectors: %s gives %d in %s and %d in %s" % (key, rows[key][2], rows[key][3], row[2], name))
        if key not in rows or row[0] < rows[key][0]:
            rows[key] = row
    if not rows:
        sys.exit("aug_board_vectors: no FIXED-mode section in %d logs of %s" % (len(logs), build))
    with open(out + ".tsv", "w") as f, open(out + ".hex", "w") as h:
        f.write("op0\top1\tlatmin\tlatmax\todata\tlog\n")
        for (a, b), (lo, hi, r, n) in sorted(rows.items(), key=lambda kv: kv[1][0]):
            f.write("%d\t%d\t%d\t%d\t%d\t%s\n" % (a, b, lo, hi, r, n))
            h.write("%08x %08x\n" % (a & 0xFFFFFFFF, b & 0xFFFFFFFF))
    print("%s: %d vectors from %d logs -> %s.tsv/.hex" % (build, len(rows), len(logs), out))


if __name__ == "__main__":
    main()
