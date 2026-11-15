#!/usr/bin/env python3
"""hold_pads.py BASE.vh OUT.vh REPORT.txt [REPORT.txt ...] -- the rule H / I pads corner_audit reports but cannot size.

corner_audit sizes a rule's knob by measuring the knob's chain on the route.  A DACK (UACK) line at 0 links has no
chain in the netlist, so an H violation on it ("PAD to k -- VIOLATION (no DACK line routed ...)") never reaches the
proposal sizes.vh; the eval_task summary did not show H / I rows either (until 2026-11-15).  This takes every H / I
row below 0 in the given corner_audit report.txt files (several routes and corners) and sets its knob to the largest
"PAD to k" over them (never lowering BASE):
  H  <link>.ctl.u.u                     -> BD_SZ_<LINK>_UACK   (bd_link's DACK)
  H  <pipe>.many.stage[i].u.ctl.u.u     -> BD_SZ_<PIPE>_UACK   (bd_pipe's DACK is one knob for every stage)
  I  <pipe>.many.stage[i].u.ctl.u.u     -> BD_SZ_<PIPE>_SDELAY (the line in front of stage i, i < N; the
                                           [from ...] stage names it; a row naming a pipe's last line is reported)
Prices are per corner, so k is the report's own estimate: re-run corner_audit on the rebuilt routes (a link more
moves other margins), as for every other proposal.
"""
import re, sys

base_p, out_p, reps = sys.argv[1], sys.argv[2], sys.argv[3:]
P = "bridge_i.udut."


def macro(path):
    return "BD_SZ_" + re.sub(r"[^A-Za-z0-9]", "_", path).upper()


lines = open(base_p).read().splitlines()
base = {}
for ln in lines:
    m = re.match(r"`define\s+(\S+)\s+(\d+)", ln)
    if m:
        base[m.group(1)] = int(m.group(2))
want, why, odd = {}, {}, []
for rp in reps:
    seen = set()
    for ln in open(rp):
        m = re.match(r"\s+([HI])\s+(-?\d+)\s+(\S+)\s.*PAD to (\d+)", ln)
        if not m or int(m.group(2)) >= 0 or (m.group(1), m.group(3)) in seen:
            continue
        seen.add((m.group(1), m.group(3)))
        rule, mg, label, k = m.group(1), int(m.group(2)), m.group(3), int(m.group(4))
        mp = re.match(re.escape(P) + r"(.+?)\.many\.stage\[(\d+)\]\.u\.ctl\.u\.u$", label)
        ml = re.match(re.escape(P) + r"(.+?)\.ctl\.u\.u$", label)
        if rule == "H":
            knob = macro(P + (mp or ml).group(1)) + "_UACK" if (mp or ml) else None
        elif mp and int(mp.group(2)) > 0:
            knob = macro(P + mp.group(1)) + "_SDELAY"
        else:
            knob = None
        if knob is None:
            odd.append("%s %d %s (%s): no knob this tool knows" % (rule, mg, label, rp))
            continue
        if k > want.get(knob, -1):
            want[knob] = k
        why.setdefault(knob, []).append("%s %+d" % (rule, mg))
out, moved = [], 0
done = set()
for ln in lines:
    m = re.match(r"`define\s+(\S+)\s+(\d+)", ln)
    if m and m.group(1) in want and want[m.group(1)] > int(m.group(2)):
        k = m.group(1)
        out.append("`define %s %d   // hold_pads.py: was %s; %d rows below 0 (worst %s)"
                   % (k, want[k], m.group(2), len(why[k]), min(why[k], key=lambda s: int(s.split()[1]))))
        moved += 1
    else:
        out.append(ln)
    if m:
        done.add(m.group(1))
for k in sorted(set(want) - done):
    out.append("`define %s %d   // hold_pads.py: not in base; %d rows below 0 (worst %s)"
               % (k, want[k], len(why[k]), min(why[k], key=lambda s: int(s.split()[1]))))
    moved += 1
open(out_p, "w").write("\n".join(out) + "\n")
for o in odd:
    print("  " + o)
print("%d knob(s) moved from %d report(s) -> %s" % (moved, len(reps), out_p))
