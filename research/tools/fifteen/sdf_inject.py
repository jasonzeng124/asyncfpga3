#!/usr/bin/env python3
"""sdf_inject.py IN.sdf OUT.sdf SRC_RE DST_RE PS -- a constructed defect: add PS picoseconds to every delay value of every
INTERCONNECT arc whose source pin matches SRC_RE and whose destination pin matches DST_RE (Python regexes, searched in
the pin names with the SDF's backslash escapes removed).  Every other line is copied byte for byte, so the netlist and
the bits stay those of the route; only the timing of the chosen wires changes.

Used for the select negative controls (PROGRAM "A check earns its place by failing"): the select latch's output into
a mux's request joins (umuxN.uj0 / uj1) made late, as in the collatz control of 2026-11-15 (+3000 ps on umux1.uj0/uj1
A5 from ulink_n14__1's latch).  Prints each changed arc; exits 1 if none matched (a control that injects nothing must
not pass for one)."""
import re, sys

src_re, dst_re = re.compile(sys.argv[3]), re.compile(sys.argv[4])
add = int(sys.argv[5])
arc = re.compile(r'^(\s*\(INTERCONNECT\s+)(\S+)\s+(\S+)(\s+.*)$')
num = re.compile(r'-?\d+(?:\.\d+)?')
n = 0
with open(sys.argv[1]) as f, open(sys.argv[2], 'w') as g:
    for line in f:
        m = arc.match(line.rstrip('\n'))
        if m:
            s, d = m.group(2).replace('\\', ''), m.group(3).replace('\\', '')
            if src_re.search(s) and dst_re.search(d):
                def bump(t):
                    v = t.group(0)
                    return str(int(round(float(v))) + add) if '.' not in v else '%.3f' % (float(v) + add)
                tail = re.sub(r'\(([^()]*)\)', lambda p: '(' + num.sub(bump, p.group(1)) + ')', m.group(4))
                new = m.group(1) + m.group(2) + ' ' + m.group(3) + tail + '\n'
                print('INJECT %s -> %s : %s  =>  %s' % (s, d, m.group(4).strip(), tail.strip()))
                g.write(new); n += 1; continue
        g.write(line)
print('injected %d arcs, +%d ps' % (n, add))
sys.exit(0 if n else 1)
