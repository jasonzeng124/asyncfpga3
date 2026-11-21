#!/usr/bin/env python3
"""sizerule_floor.py FAILED.vh OUT.vh --base ITEM.vh [--named CELL[:RULE] ...] -- the floor corner_audit's CA_SIZERULE_FLOOR reads:
no line may be proposed below the largest size that FAILED a draw (research/data/sizerule/README.md).

Every macro of FAILED.vh (a sizes file that failed at least one draw on an EQUIVALENT, ffmux-clean route) that it SHORTENED
against --base (the item the failing file was scaled from) is copied at its size; a line the failing file kept at the
item's size says nothing about a shorter size and gets no floor; a macro whose cell the static check named on a failing route (--named: uxori1, ucmpi0, ulink_n7:H, ulink_n25:I ...)
gets +1, since that size is known to fail.  Rule H names a link controller and maps to its _UACK line, rule I to its
_SDELAY line; any other name maps to the cell's own delay macro.  Sizes of 0 (no line) stay 0."""
import argparse, re
ap = argparse.ArgumentParser(); ap.add_argument("failed"); ap.add_argument("out")
ap.add_argument("--named", nargs="*", default=[]); ap.add_argument("--base", required=True); ap.add_argument("--prefix", default="BD_SZ_BRIDGE_I_UDUT_")
A = ap.parse_args()
bump = set()
for nm in A.named:
    cell, _, rule = nm.partition(":")
    base = A.prefix + cell.upper()
    bump.add(base + {"H": "_UACK", "I": "_SDELAY"}.get(rule, ""))
base = {m.group(1): int(m.group(2)) for m in (re.match(r"`define\s+(\S+)\s+(\d+)", l) for l in open(A.base)) if m}
out, hit = ["// draw floor (research/tools/sizerule_floor.py): %s (lines it shortened vs %s), +1 on %s" % (A.failed.split("/")[-1], A.base.split("/")[-1], " ".join(A.named) or "none")], set()
for ln in open(A.failed):
    m = re.match(r"`define\s+(\S+)\s+(\d+)", ln)
    if m:
        v = int(m.group(2)); k = m.group(1)
        if k in base and v >= base[k]:
            continue
        if k in bump and v > 0:
            v += 1; hit.add(k)
        out.append("`define %s %d" % (k, v))
open(A.out, "w").write("\n".join(out) + "\n")
miss = bump - hit
print("%s: %d macros, +1 on %d%s" % (A.out, len(out) - 1, len(hit), ("; named but not in file: " + " ".join(sorted(miss))) if miss else ""))
