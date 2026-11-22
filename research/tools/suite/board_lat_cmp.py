#!/usr/bin/env python3
"""board_lat_cmp.py LOG_A LOG_B MAX_RATIO -- compare two runs of the same kernel's vectors (board logs of
cells/hw/xsdb_bench_vec.tcl, or the GLS gate's BENCHRES files): the per-call latency is each call's latmin (host cycles
of 12 ns, the bench's own count), summed over the calls both logs completed. Prints both sums in ns and B / A, and
"PASS" when B / A <= MAX_RATIO (exit 0), "FAIL" otherwise (exit 1); exit 2 when either log has no complete call or the
two logs ran different operands (nothing to compare)."""
import re
import sys


def calls(path):
    out = {}
    for ln in open(path, errors="replace"):
        if "BENCHRES" not in ln:
            continue
        d = dict(re.findall(r"(\w+)=(\S+)", ln))
        if "batch" not in d or "latmin" not in d or d.get("completed", "0") == "0":
            continue
        out[int(d["batch"])] = (d.get("op0"), d.get("op1"), int(d["latmin"]))
    return out


def main():
    a, b, mx = calls(sys.argv[1]), calls(sys.argv[2]), float(sys.argv[3])
    both = sorted(set(a) & set(b))
    if not both:
        print("board_lat_cmp: no call completed in both logs: nothing to compare"); sys.exit(2)
    diff = [k for k in both if a[k][:2] != b[k][:2]]
    if diff:
        print("board_lat_cmp: calls %s ran different operands in the two logs: nothing to compare" % diff); sys.exit(2)
    sa, sb = sum(a[k][2] for k in both) * 12, sum(b[k][2] for k in both) * 12
    r = sb / float(sa) if sa else float("inf")
    ok = r <= mx
    print("board_lat_cmp: %d calls; A %d ns, B %d ns; B / A = %.3f (<= %.2f: %s)" % (len(both), sa, sb, r, mx,
                                                                                   "PASS" if ok else "FAIL"))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
