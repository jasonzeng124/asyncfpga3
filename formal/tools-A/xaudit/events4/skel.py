"""skel.py -- cut the CONTROL SKELETON out of a routed2x netlist (UNTRUSTED, copy-only).

    python3 skel.py NET.json BANDS.json OUT_NET.json OUT_BANDS.json

Kept: every reset-carrying storage LUT (C-elements and the arbiter state LUTs) and every
stateless LUT on a control path between them (classify.Skel.ctl_net), copied verbatim
(INIT, physical pin order, connections).  Cut: every other net read by a kept LUT becomes a
free input port named sel_<net> (data-latch outputs feeding steers and mux joins: the
SELECT inputs, i.e. environment choice sequences), plus rig_rst.  Bands are copied for the
kept LUTs and their pin arcs.  The verdicts on the skeleton hold for every waveform of the
cut nets, hence for every behaviour of the full netlist (each kept gate's relation reads only
kept nets and cut nets).
"""
import json
import sys
from netlib import Net
from classify import Skel


def main(netp, bandp, outn, outb):
    n = Net(netp, bandp)
    s = Skel(n)
    src = json.load(open(netp))["modules"]["gcd_ctl"]
    keep = set(s.kind)
    # stateless control gates: drivers of control nets read by kept cells (transitively)
    todo = list(keep)
    while todo:
        cn = todo.pop()
        for b in n.cells[cn]["ins"]:
            if not isinstance(b, int) or b == n.rst or b not in n.drv:
                continue
            d = n.drv[b]
            if d in keep:
                continue
            if d in s.storage:
                continue  # data storage: cut
            if s.ctl_net(b):
                keep.add(d)
                todo.append(d)
    kept_out = {n.cells[c]["out"] for c in keep}
    cut = set()
    for cn in keep:
        for b in n.cells[cn]["ins"]:
            if isinstance(b, int) and b not in kept_out and b != n.rst:
                cut.add(b)
    ports = {"rig_rst": {"direction": "input", "bits": [n.rst]}}
    for b in sorted(cut):
        ports[f"sel_{b}"] = {"direction": "input", "bits": [b]}
    cells = {cn: src["cells"][cn] for cn in sorted(keep)}
    netnames = {}
    for nm, v in src["netnames"].items():
        bits = [b for b in v["bits"] if isinstance(b, int) and (b in kept_out or b in cut or b == n.rst)]
        if len(bits) == len(v["bits"]) and bits:
            netnames[nm] = v
    out = {"creator": "events4/skel.py", "modules": {"gcd_ctl": {
        "attributes": {"top": "00000000000000000000000000000001"}, "ports": ports,
        "cells": cells, "netnames": netnames}}}
    json.dump(out, open(outn, "w"))
    b = json.load(open(bandp))
    b["cells"] = {k: v for k, v in b["cells"].items() if k in keep}
    b["arcs"] = {k: v for k, v in b["arcs"].items() if k.rsplit("/", 1)[0] in keep}
    b["comment"] = b.get("comment", "") + "; control skeleton (events4/skel.py)"
    json.dump(b, open(outb, "w"))
    print(f"skeleton: {len(keep)} LUTs ({len(s.kind)} storage with reset), {len(cut)} cut nets (select inputs)")


if __name__ == "__main__":
    main(*sys.argv[1:5])
