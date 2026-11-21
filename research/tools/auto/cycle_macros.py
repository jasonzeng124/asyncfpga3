#!/usr/bin/env python3
"""cycle_macros.py CYC_TXT SIZES_VH [PREFIX] -- the sizes.vh macros of the delay lines of every instance on a critical
cycle (research/tools/eventgraph/cycdecomp.py's output: one "== NAME P=..." block, then one row per instance), one per
line.  An instance X maps to BD_SZ_<PREFIX>X (its udly / rdly), _UACK and _SDELAY (a link's acknowledge and a pipe's
inner stages), each only if SIZES_VH defines it.  PREFIX defaults to BRIDGE_I_UDUT_ (the kernel bench).  Used by
research/tools/auto/auto_size.sh AUTO_TRIM_SCOPE=cycle: a trim off the critical cycle cannot lower the period and only
spends a race's margin (formal B25: ipow s1's loop-exit compare 16 -> 11, its steer's proved bound 0.171 -> 0.017, P
unchanged).

--ports LIST (auto_size.sh AUTO_TRIM_PORTS=1, opt-in 2026-11-21; without it the output is unchanged): a memory port
X_uport on the cycle also maps to its own lines, BD_SZ_<PREFIX>X_* (bdc/mem.py: umem0 / umem1's usetup and uco, ...),
each only if LIST (trim_lines.py --list on the route) calls it trimmable. Why: the port's lines carry no "_UPORT" in their
macro names, so the instance-name mapping above never finds them, and a cycle-scoped trim left them at their built
length even where the port is the critical cycle and the rule asks for less (flow v10 + BDC_MEM_FASTFALL, whose bd_mem_ff
lines are trimmable: on all 17 rule-CLEAN routes with the port on the cycle, 4-29 elements of port lines the rule would
remove, none trimmed). A plain bd_mem's lines are symmetric (trim_lines.py refuses them), hence the LIST filter."""
import re
import sys


def main():
    ports = None
    if "--ports" in sys.argv:
        i = sys.argv.index("--ports")
        ports = {f[0] for f in (l.rstrip("\n").split("\t") for l in open(sys.argv[i + 1])) if len(f) >= 3 and f[1] == "trimmable"}
        del sys.argv[i:i + 2]
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
        mp = re.match(r"^(.+)_uport$", x)
        if ports is not None and mp:
            pb = pre + mp.group(1).upper() + "_"
            for m in sorted(defined):
                if m.startswith(pb) and m in ports and m not in out:
                    out.append(m)
    print("\n".join(out))


if __name__ == "__main__":
    main()
