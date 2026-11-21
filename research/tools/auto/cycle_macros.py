#!/usr/bin/env python3
"""cycle_macros.py CYC_TXT SIZES_VH [PREFIX] -- the sizes.vh macros of the delay lines of every instance on a critical
cycle (research/tools/eventgraph/cycdecomp.py's output: one "== NAME P=..." block, then one row per instance), one per
line.  An instance X maps to BD_SZ_<PREFIX>X (its udly / rdly), _UACK and _SDELAY (a link's acknowledge and a pipe's
inner stages), each only if SIZES_VH defines it.  PREFIX defaults to BRIDGE_I_UDUT_ (the kernel bench).  Used by
research/tools/auto/auto_size.sh AUTO_TRIM_SCOPE=cycle: a trim off the critical cycle cannot lower the period and only
spends a race's margin (formal B25: ipow s1's loop-exit compare 16 -> 11, its steer's proved bound 0.171 -> 0.017, P
unchanged)."""
import re
import sys


def main():
    cyc, sizes = sys.argv[1], sys.argv[2]
    pre = "BD_SZ_" + (sys.argv[3] if len(sys.argv) > 3 else "BRIDGE_I_UDUT_")
    defined = {m.group(1) for m in (re.match(r"`define\s+(\S+)\s+\d+", l) for l in open(sizes)) if m}
    insts = []
    for l in open(cyc):
        if l.startswith("==") or "TOTAL" in l or not l.strip():
            continue
        f = l.split()
        if f and f[1:2] == ["chain"]:
            insts.append(f[0])
    out = []
    for x in insts:
        base = pre + x.upper()
        for m in (base, base + "_UACK", base + "_SDELAY"):
            if m in defined and m not in out:
                out.append(m)
    print("\n".join(out))


if __name__ == "__main__":
    main()
