#!/usr/bin/env python3
"""Routed pin-level delay-graph dump for xc7 signoff. Runs INSIDE
nextpnr-xilinx (its embedded Python; `ctx` is the global) via:

    PNR_SYNTH_JSON=<top>.json PNR_GRAPH_OUT=<out>.graph.json \
        nextpnr-xilinx ... --post-route boards/xc7/timing_dump.py

and writes the routed design as the JSON graph tools/timing_signoff.py
loads with --graph-json: the xc7 counterpart of nextpnr-ice40's --sdf
(which stock nextpnr-xilinx lacks, QUESTIONS.md Q7b). Requires the
owner's local pybinding patch in nextpnr-xilinx/xilinx/arch_pybindings.cc
(getCellDelay / getRouteDelayPs -- found as uncommitted modifications in
~/dev2/lib/fpgatoolchain/openxc7-src, already in the built binary).

Logical-pin resolution (the fracturing lesson, learned the hard way in
the predecessor project's postroute_audit_xc7.py -- do not skip this):
nextpnr-xilinx's legalizer packs two independent LUTs onto one physical
bel when their combined inputs fit (O5/O6 fracturable-LUT6 mode), and
from then on the post-route API reports the bel's FULL pin set for
EITHER logical cell -- net.users includes the bel-mate's foreign pins
under this cell's name. Walking those drags an arbitrary unrelated
fan-in cone into the graph. The pre-place synth JSON (PNR_SYNTH_JSON --
the SAME file passed to --json) still has exact logical connectivity,
so every input pin here is admitted only by matching its net back to
the cell's logical connections by name, and is emitted under its
LOGICAL name (I0..I5) with the physical arc/route delays. Cells with no
synth counterpart (packer-created constant LUTs, split/repacked CARRY4s)
keep their physical pins -- their pin sets are not fracturable.

Delays are ps, single-corner (the timing model's typical numbers; no
min/max split -- the SDF-loader's dmin/dmax collapse to one value, which
the Q9 ratio guardband is there to cover). CARRY4 arcs missing from
getCellDelay fall back to the worst Zynq-7 CLB carry arc (642 ps),
conservative on the data side; request chains never route through
CARRY4s (they are library LUT4s only), so the fallback never dilutes a
request-side min.
"""
import json
import os
import sys
import traceback

CARRY4_COMB_MAX_PS = 642.0


def load_true_connectivity(path):
    """cell -> {logical input pin: net_idx}, cell -> synth type,
    net_idx -> {name aliases}, from the pre-place synth JSON."""
    d = json.load(open(path))
    mods = d["modules"]
    top = max(mods, key=lambda m: len(mods[m].get("cells", {})))
    mod = mods[top]
    true_in, true_type = {}, {}
    for cn, c in mod["cells"].items():
        dirs = c.get("port_directions", {})
        real = {}
        for pn, bits in c.get("connections", {}).items():
            if dirs.get(pn) != "input":
                continue
            for i, bit in enumerate(bits):
                if isinstance(bit, int):      # strings are tied constants
                    real[pn if len(bits) == 1 else "%s%d" % (pn, i)] = bit
        true_in[cn] = real
        true_type[cn] = c["type"]
    net_names = {}
    for name, info in mod.get("netnames", {}).items():
        bits = info.get("bits", [])
        for i, bit in enumerate(bits):
            if isinstance(bit, int):
                alias = name if len(bits) == 1 else "%s[%d]" % (name, i)
                net_names.setdefault(bit, set()).add(alias)
    return true_in, true_type, net_names


def main(ctx):
    synth_json = os.environ["PNR_SYNTH_JSON"]
    out_path = os.environ.get("PNR_GRAPH_OUT", "timing_graph.json")
    true_in, true_type, net_names = load_true_connectivity(synth_json)

    cell_by_name, cell_type = {}, {}
    for kv in ctx.cells:
        cell_by_name[str(kv.first)] = kv.second
        cell_type[str(kv.first)] = str(kv.second.type)

    # post-route connectivity (bel-wide, unfiltered)
    driver = {}         # net -> (cell, out pin)
    raw_in = {}         # cell -> {physical in pin: net}
    net_users = {}      # net -> [(cell, physical in pin)]
    for kv in ctx.nets:
        nname = str(kv.first)
        net = kv.second
        drv = net.driver
        if drv.cell is not None:
            driver[nname] = (str(drv.cell.name), str(drv.port))
        for u in net.users:
            cn, pn = str(u.cell.name), str(u.port)
            raw_in.setdefault(cn, {})[pn] = nname
            net_users.setdefault(nname, []).append((cn, pn))

    # resolve logical input pins by net identity (fracture-safe); each
    # physical pin is consumed at most once so duplicate nets on two
    # logical pins still resolve one-to-one
    pin_l2p = {}        # cell -> {logical pin: (physical pin, net)}
    pin_p2l = {}        # cell -> {physical pin: logical pin}
    unresolved = 0
    for cn, ports in true_in.items():
        if cn not in raw_in:
            continue                    # swept / const-folded away
        used, got = set(), {}
        for lp, net_idx in sorted(ports.items()):
            aliases = net_names.get(net_idx, set())
            for ap, nn in raw_in[cn].items():
                if ap not in used and nn in aliases:
                    got[lp] = (ap, nn)
                    used.add(ap)
                    break
            else:
                unresolved += 1
        pin_l2p[cn] = got
        pin_p2l[cn] = {ap: lp for lp, (ap, _nn) in got.items()}
    print("  [xc7 dump] resolved logical pins for %d synth cells "
          "(%d inputs unmatched)" % (len(pin_l2p), unresolved))

    def is_const_cell(cn):
        # nextpnr-xilinx materializes GND/VCC as routed cones
        # (PSEUDO_GND/VCC "$PACKER_*_DRV" drivers feeding
        # "$PACKER_*_NET$LUT$n" constant LUTs). ice40's SDF contains no
        # such nets -- constants are absorbed into LUT inits -- and the
        # signoff tracer's pin-count reasoning is calibrated to that
        # (a const-tied pin never toggles, so it carries no timing
        # event). Drop the whole cone so both targets present the same
        # graph shape; sink cells keep their real pins.
        return (cell_type.get(cn, "").startswith("PSEUDO")
                or cn.startswith("$PACKER_GND_NET")
                or cn.startswith("$PACKER_VCC_NET"))

    def out_pin_name(cn, phys):
        # single logical output per cell: LUT-class outputs are "O"
        if cell_type.get(cn) == "SLICE_LUTX":
            return "O"
        return phys

    def in_pin_name(cn, phys):
        if cn in pin_p2l:
            lp = pin_p2l[cn].get(phys)
            return lp                   # None = foreign bel-mate pin: drop
        return phys                     # no synth counterpart: physical

    cell_outs = {}
    for nn, (dc, dp) in driver.items():
        cell_outs.setdefault(dc, set()).add(dp)

    cells, iopaths, edges = {}, [], []
    n_const = 0
    for cn, ct in cell_type.items():
        if is_const_cell(cn):
            n_const += 1
            continue
        cells[cn] = ct
        cell = cell_by_name[cn]
        outs = cell_outs.get(cn, set())
        ins = ([(ap, lp) for ap, lp in pin_p2l[cn].items()]
               if cn in pin_l2p else
               [(ap, ap) for ap in raw_in.get(cn, {})])
        for ap, lp in ins:
            if lp is None:
                continue
            for op in outs:
                found, ps = ctx.getCellDelay(cell, ap, op)
                if found:
                    iopaths.append([cn, lp, out_pin_name(cn, op),
                                    float(ps)])
                elif "CARRY4" in ct:
                    iopaths.append([cn, lp, out_pin_name(cn, op),
                                    CARRY4_COMB_MAX_PS])

    dropped_edges = 0
    for nn, (dc, dp) in driver.items():
        if is_const_cell(dc):
            continue
        src = (dc, out_pin_name(dc, dp))
        for uc, up in net_users.get(nn, []):
            if is_const_cell(uc):
                continue
            lp = in_pin_name(uc, up)
            if lp is None:
                dropped_edges += 1      # bel-mate pollution, by design
                continue
            ps = ctx.getRouteDelayPs(nn, uc, up)
            edges.append([src[0], src[1], uc, lp,
                          float(ps) if ps >= 0.0 else 0.0])
    print("  [xc7 dump] %d cells, %d arcs, %d edges "
          "(%d bel-mate pin claims dropped, %d const-cone cells dropped)"
          % (len(cells), len(iopaths), len(edges), dropped_edges,
             n_const))

    json.dump({"source": "nextpnr-xilinx timing_dump.py",
               "units": "ps", "cells": cells,
               "iopaths": iopaths, "edges": edges},
              open(out_path, "w"))
    print("  [xc7 dump] wrote %s" % out_path)


try:
    main(ctx)                          # noqa: F821 (nextpnr global)
except Exception:
    traceback.print_exc()
    sys.exit(1)
