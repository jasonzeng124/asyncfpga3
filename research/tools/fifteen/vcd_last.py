#!/usr/bin/env python3
"""vcd_last.py DUMPDIR REGEX [REGEX ...] -- for every logical net whose name (nets.map, the decoded netlist's names for
the kernel's nets) matches one of the regexes: its transition count, its last change (time, value) and its value at the
end of the dump; plus the time of the last event of ANY net in the dump. For locating where a run stops: a handshake
that stalls shows its last change long before the dump ends, with the request high and the acknowledge low (or the
reverse).  Times in ps."""
import re, sys, collections
d = sys.argv[1]; rxs = [re.compile(r) for r in sys.argv[2:]]
nm = collections.defaultdict(list)
for l in open(d + '/nets.map'):
    if l.startswith('#'): continue
    a, b = l.split()[:2]
    if any(r.search(a) for r in rxs): nm[b].append(a)
ids = collections.defaultdict(list); last = {}; cnt = collections.Counter(); t = 0; t_any = 0
for l in open(d + '/dump.vcd'):
    if l.startswith('$var'):
        p = l.split()
        if p[4] in nm: ids[p[3]].append(p[4])
    elif l[0] == '#': t = int(l[1:])
    elif l[0] in '01xz':
        t_any = t
        for x in ids.get(l[1:].strip(), ()): last[x] = (t, l[0]); cnt[x] += 1
print(f"# last event of any net: {t_any} ps")
for net, names in sorted(nm.items(), key=lambda kv: last.get(kv[0], (-1, ''))[0]):
    tt, v = last.get(net, (None, '?'))
    print(f"{min(names, key=len):60s} {net:8s} changes {cnt[net]:6d}  last {tt} -> {v}")
