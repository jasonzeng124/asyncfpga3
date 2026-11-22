#!/usr/bin/env python3
"""
ring_predict.py -- predicted ring-oscillator periods from an SDF, per column.

    python3 cells/gls/fid/ring_predict.py ro_top      NEXTPNR.sdf [XRAY.sdf] > out.tsv
    python3 cells/gls/fid/ring_predict.py ro_many_top NEXTPNR.sdf [XRAY.sdf] > out.tsv

The loop walk is hw/ro_measure.py's and hw/ro_many_measure.py's (start at
<ring>inv/O6, follow the one in-ring successor of every pin, sum IOPATH and
INTERCONNECT once around; ro_top excludes the ring's BUFG tap by name), and the
period is twice the loop, as there.  The only difference is that every column
of the (min:typ:max) triple is kept, so an xray_delay.py SDF gives the period
at FAST_MIN, SLOW_MIN and SLOW_MAX (its three columns), next to nextpnr's.
"""
import re
import sys
from collections import defaultdict

RE_INST = re.compile(r"\(INSTANCE\s+(\S*?)\)")
RE_IO = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)")
RE_IC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)")


def unesc(s):
    return s.replace("\\", "")


def parse(path):
    edges = defaultdict(list)
    inst = None
    for line in open(path):
        m = RE_IC.search(line)
        if m:
            edges[unesc(m.group(1))].append((unesc(m.group(2)), tuple(int(m.group(k)) for k in (3, 4, 5))))
            continue
        m = RE_INST.search(line)
        if m:
            inst = unesc(m.group(1))
            continue
        m = RE_IO.search(line)
        if m and inst is not None:
            edges["%s/%s" % (inst, m.group(1))].append(
                ("%s/%s" % (inst, m.group(2)), tuple(int(m.group(k)) for k in (3, 4, 5))))
    return edges


def inst_of(pin):
    return pin.rpartition("/")[0]


def loop(edges, pref, exclude=None):
    start = pref + "inv/O6"
    if start not in edges:
        return None, 0
    tot = [0, 0, 0]
    pin, seen, n = start, set(), 0
    while True:
        nxt = [(d, w) for d, w in edges.get(pin, ())
               if inst_of(d).startswith(pref) and inst_of(d) != exclude]
        if len(nxt) != 1:
            return None, n
        d, w = nxt[0]
        tot = [a + b for a, b in zip(tot, w)]
        n += 1
        pin = d
        if pin == start:
            return tot, n
        if pin in seen:
            return None, n
        seen.add(pin)


def rings(design):
    if design == "ro_top":
        for i, n in enumerate([7, 15, 31, 63, 127]):
            yield "ro[%d]" % i, n, "ro[%d]." % i, "ro[%d].bg" % i
    elif design == "ro_many_top":
        L = [7, 15, 31, 63]
        for g in range(16):
            for b in range(8):
                yield "g%d.b%d" % (g, b), L[(g + b) % 4], "grp[%d].ro[%d]." % (g, b), None
    else:
        sys.exit("unknown design " + design)


def main():
    design, npr = sys.argv[1], sys.argv[2]
    xr = sys.argv[3] if len(sys.argv) > 3 else None
    E1 = parse(npr)
    E2 = parse(xr) if xr else None
    print("ring\tlinks\tarcs\tnextpnr_period_ps" +
          ("\txray_fastmin_ps\txray_slowmin_ps\txray_slowmax_ps" if xr else ""))
    for name, n, pref, ex in rings(design):
        a, k = loop(E1, pref, ex)
        row = [name, n, k, 2 * a[0] if a else "NA"]
        if xr:
            b, k2 = loop(E2, pref, ex)
            row += [2 * x for x in b] if b else ["NA"] * 3
        print("\t".join(str(x) for x in row))


if __name__ == "__main__":
    main()
