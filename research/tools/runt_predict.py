#!/usr/bin/env python3
"""runt_predict.py INSTANCES_TSV XRAY_SDF OUT_TSV [BAND] -- runt_top's per-instance prediction table for
research/tools/runt_judge.py, from this build's prjxray SDF (cells/gls/fid/xray_delay.py; columns FAST_MIN:SLOW_MIN:SLOW_MAX).

    python3 research/tools/runt_predict.py cells/build/hw/runt_top/instances.tsv \
        cells/build/hw/runt_top/runt_top_xray.sdf research/board/runt/predicted.tsv

For each instance (cells/hw/runt_measure.py --table), the arrival of a and of b at the cell-under-test's PHYSICAL pins:
walk back from the pin through INTERCONNECT and single-input LUT IOPATHs to the first flop Q, then add the flop's
CK->Q and its clock's INTERCONNECT from bufg_rclk (so the La/Lb skew is in).  w = t(b) - t(a): the force-high episode
of C(a, ~b).  loop = IOPATH(a pin -> O6) + INTERCONNECT(O6 -> q pin): the transport picture's capture edge is w = loop.
Every arc is taken at FAST_MIN, SLOW_MAX and the band point FAST_MIN + BAND*(SLOW_MAX - FAST_MIN) (default 0.288, the
ring128 fit); the sum is linear, so the band column is the band of the sum.  prjxray gives every LUT pin the same arc,
so pin-to-pin differences inside the LUT are not in w (tens of ps, unmodelled).  A pin that does not walk back to a
flop is an error, not a silent row.
"""
import re, sys
from collections import defaultdict

RE_INST = re.compile(r"\(INSTANCE\s+(\S*?)\)")
RE_IO = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)")
RE_IC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)")


def un(s):
    return s.replace("\\", "")


def parse(path):
    ic, io, inst = {}, defaultdict(dict), None
    for ln in open(path):
        m = RE_IC.search(ln)
        if m:
            ic[un(m.group(2))] = (un(m.group(1)), (int(m.group(3)), int(m.group(5))))
            continue
        m = RE_INST.search(ln)
        if m:
            inst = un(m.group(1)); continue
        m = RE_IO.search(ln)
        if m and inst is not None:
            io[inst][(m.group(1), m.group(2))] = (int(m.group(3)), int(m.group(5)))
    return ic, io


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def arrival(pin, ic, io):
    t, hops = (0, 0), 0
    while True:
        src, d = ic[pin]
        t = add(t, d)
        cell, opin = src.rsplit("/", 1)
        arcs = io.get(cell, {})
        if ("CK", opin) in arcs:                       # a flop: CK->Q plus its clock arrival
            t = add(t, arcs[("CK", opin)])
            return add(t, ic[cell + "/CK"][1]), hops
        ins = [i for (i, o) in arcs if o == opin and cell + "/" + i in ic]
        if len(ins) != 1:
            sys.exit("runt_predict: %s: %d driven inputs reach %s (want one: a LUT1 chain)" % (pin, len(ins), src))
        t = add(t, arcs[(ins[0], opin)]); pin = cell + "/" + ins[0]; hops += 1


def main():
    tab, sdf, out = sys.argv[1:4]
    band = float(sys.argv[4]) if len(sys.argv) > 4 else 0.288
    ic, io = parse(sdf)
    bd = lambda v: v[0] + band * (v[1] - v[0])
    rows = [ln.split("\t") for ln in open(tab).read().splitlines() if ln and not ln.startswith("#")]
    hd, rows = rows[0], rows[1:]
    with open(out, "w") as f:
        f.write("instance\tw_fastmin_ps\tw_slowmax_ps\tw_band_ps\tloop_band_ps\tkind\tk\tloop_fastmin_ps\tloop_slowmax_ps\t"
                "hops_a\thops_b\n")
        for r in rows:
            d = dict(zip(hd, r))
            cell = d["dut_cell"]; pp = dict(kv.split("=") for kv in d["physical_pins"].split(","))
            ta, ha = arrival(cell + "/" + pp["a"], ic, io)
            tb, hb = arrival(cell + "/" + pp["b"], ic, io)
            w = (tb[0] - ta[0], tb[1] - ta[1])
            if "q" in pp:
                lp = add(io[cell][(pp["a"], "O6")], ic[cell + "/" + pp["q"]][1]) if (cell + "/" + pp["q"]) in ic else None
            else:
                lp = None
            lps = ("%.0f\t%d\t%d" % (bd(lp), lp[0], lp[1])) if lp else "-\t-\t-"
            lb = lps.split("\t")[0]
            f.write("%s\t%d\t%d\t%.0f\t%s\t%s\t%s\t%s\t%d\t%d\n" % (d["instance"], w[0], w[1], bd(w), lb, d["kind"], d["k"],
                                                                 "\t".join(lps.split("\t")[1:]), ha, hb))
    print("%d instances -> %s (band %s)" % (len(rows), out, band))


if __name__ == "__main__":
    main()
