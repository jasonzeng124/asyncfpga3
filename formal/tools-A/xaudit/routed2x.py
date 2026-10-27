#!/usr/bin/env python3
"""routed2x.py -- a nextpnr-xilinx ROUTED netlist -> an xaudit netlist + per-arc band file.

    python3 -I routed2x.py ROUTED.json --out NET.json --bands BANDS.json
            [--xray-arcs ARCS.tsv --corner indep|slow|fast | --sdf NEXTPNR.sdf --kappa LO,HI]
            [--keep-prefix urig.] [--cut-net rig_rst ...] [--unit-ps 25] [--report R.txt]

INPUT.  The routed JSON nextpnr writes with --write (cells after packing:
SLICE_LUTX, SELMUX2_1, CARRY4, SLICE_FFX, ...; LUT pins are PHYSICAL A1..A6,
the logical input(s) on each pin recorded in X_ORIG_PORT_A<k> -- the record
cells/verify/fasm_audit.py checks against the bitstream).  Delays come from
either
  --xray-arcs   the per-arc TSV of the research branch's cells/gls/fid/xray_delay.py
                (prjxray-db Elmore model on the actual route; four corners
                FAST_MIN FAST_MAX SLOW_MIN SLOW_MAX per arc, RC term in all four), or
  --sdf         nextpnr's own SDF (slow-max only: one number per arc), with a
                band [KLO*d, KHI*d] (documented fallback; NOT used for the gcd_hw
                result, see formal/notes/A-xaudit-gcd.md).

THE CUT (the clocked shell).  xaudit has no flip-flop model.  The kept region is
  every cell whose name starts with --keep-prefix (default "urig.": the rig,
  i.e. the compiled kernel bdc_gcd + its handshake environment + the checker),
  plus the COMBINATIONAL transitive fan-in of those cells (LUTs, MUXF7/F8,
  CARRY4 outside the prefix that yosys/abc hoisted out of the hierarchy, e.g.
  the vector ROM a_v/b_v/g_v and the mismatch reduction `mism`),
  stopping at:
    - a sequential/hard cell output (SLICE_FFX Q, BUFGCTRL, BSCAN, IOB): the net
      becomes a FREE INPUT of the xaudit netlist (named by its net name);
    - a net named with --cut-net (default rig_rst): also a free input, so the
      stimulus drives the rig's reset directly rather than the shell's FFs;
    - the constant nets (PSEUDO_GND/VCC, and packer LUTs whose every input is
      constant): folded to the constants 0/1.
Every net a kept cell drives that a non-kept cell reads is listed in the report
as an observed output (it is simply not simulated further).  FFs never enter the
kept region (the script stops loudly if one would).

PRIMITIVES (all emitted as yosys LUTk cells, so the PROVED xaudit engine needs no
change; Lut.keval is the exact ternary extension of the INIT, so a LUT3 mux is the
Kleene mux):
  SLICE_LUTX (O6 or O5)  -> LUTk over its USED PHYSICAL pins (those with an
      X_ORIG_PORT name), INIT re-encoded from the logical INIT by name (the
      fasm_audit encoding).  One xaudit arc per physical pin, as in silicon: a
      physical pin carrying two logical inputs ("I0 I3") is ONE wire, not two.
  SELMUX2_1 (MUXF7/MUXF8) -> LUT3 I0='0', I1='1', I2='S0', INIT 0xCA (S ? I1 : I0).
  CARRY4 -> for i = 0..3:  ci_0 = CIN | CYINIT | PRECYINIT_CONST,
      MUXCY_i: LUT3 (I0=DI_i, I1=ci_i, I2=S_i) INIT 0xCA -> CO_i (= ci_{i+1})
      XORCY_i: LUT2 (I0=S_i,  I1=ci_i)         INIT 0x6  -> O_i
      named "<cell>#cy<i>" / "<cell>#xor<i>".  An unconnected DI_i reads 0.
BANDS (ps; xaudit rounds lo down -- raising it to 1 step if below -- and hi up):
  routed arc (net -> sink pin): the IC row of that (driver pin, sink pin).
  LUT / MUXF gate: [min lo, max hi] over the cell's IOPATH rows to that output.
  CARRY4 internals: XORCY_i [lo,hi] of IO S_i->O_i; MUXCY_i [0, hi of IO S_i->CO_i];
      internal ci arcs [0, max per-bit carry increment at hi].  The script CHECKS
      that every CARRY4 IO path's real hi is <= the model's summed hi (else exits 1)
      and REPORTS every path whose real lo is below the model's 1-step-per-element
      floor (the documented sub-step unsoundness, see the notes).
  --corner indep: [FAST_MIN, SLOW_MAX]  (any element anywhere in sign-off range)
           slow:  [SLOW_MIN, SLOW_MAX]  (H_ONE_CORNER, slow die)
           fast:  [FAST_MIN, FAST_MAX]  (H_ONE_CORNER, fast die)
"""
import argparse
import collections
import json
import math
import re
import sys

COLS = {"indep": (4, 7), "slow": (6, 7), "fast": (4, 5)}   # column indices into arcs.tsv
SEQ_TYPES = {"SLICE_FFX", "BUFGCTRL", "BUFG", "BSCAN", "IOB33_OUTBUF", "IOB33_INBUF_EN",
             "PAD", "DSP48E1", "RAMB18E1", "RAMB36E1"}
COMB_TYPES = {"SLICE_LUTX", "SELMUX2_1", "CARRY4"}
RE_NAME = re.compile(r"I(\d+)")


def die(msg):
    print("routed2x: " + msg, file=sys.stderr)
    sys.exit(1)


def load_xray(path, corner):
    lo_c, hi_c = COLS[corner]
    ic, io = {}, collections.defaultdict(list)
    with open(path) as f:
        hdr = f.readline()
        assert hdr.startswith("kind\tsrc\tdst"), "not an xray_delay --arcs TSV"
        for line in f:
            r = line.rstrip("\n").split("\t")
            band = (float(r[lo_c]), float(r[hi_c]))
            if r[0] == "IC":
                ic[(r[1], r[2])] = band
            else:
                io[r[2]].append((r[1], band))   # dst "cell/OUT" -> [(src pin, band)]
    return ic, io


def load_sdf(path, klo, khi):
    """nextpnr SDF: INTERCONNECT (d:d:d) and IOPATH (d:d:d); one number, slow max."""
    txt = open(path).read()
    unesc = lambda s: s.replace("\\", "")
    ic, io = {}, collections.defaultdict(list)
    for a, b, d in re.findall(r"\(INTERCONNECT (\S+) (\S+) \(([\d.]+):", txt):
        d = float(d)
        ic[(unesc(a), unesc(b))] = (klo * d, khi * d)
    for inst, body in re.findall(r"\(INSTANCE ([^)]*)\)\s*\(DELAY\s*\(ABSOLUTE(.*?)\)\s*\)\s*\)", txt, re.S):
        for a, b, d in re.findall(r"\(IOPATH (\S+) (\S+) \(([\d.]+):", body):
            d = float(d)
            io["%s/%s" % (unesc(inst), b)].append(("%s/%s" % (unesc(inst), a), (klo * d, khi * d)))
    return ic, io


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("routed")
    ap.add_argument("--out", required=True)
    ap.add_argument("--bands", required=True)
    ap.add_argument("--xray-arcs")
    ap.add_argument("--corner", default="indep", choices=sorted(COLS))
    ap.add_argument("--sdf")
    ap.add_argument("--kappa", default="0.35,1.0",
                    help="SDF fallback band [KLO*d, KHI*d]; default 0.35 = median prjxray FAST_MIN/SLOW_MAX")
    ap.add_argument("--keep-prefix", default="urig.")
    ap.add_argument("--cut-net", action="append", default=None)
    ap.add_argument("--unit-ps", type=int, default=25)
    ap.add_argument("--report")
    a = ap.parse_args()
    cut_nets = set(a.cut_net if a.cut_net is not None else ["rig_rst"])
    if a.xray_arcs:
        ic, io = load_xray(a.xray_arcs, a.corner)
        src = "xray_delay.py arcs %s, corner %s" % (a.xray_arcs, a.corner)
    elif a.sdf:
        klo, khi = map(float, a.kappa.split(","))
        ic, io = load_sdf(a.sdf, klo, khi)
        src = "nextpnr SDF %s, kappa band [%g*d, %g*d]" % (a.sdf, klo, khi)
    else:
        die("need --xray-arcs or --sdf")

    j = json.load(open(a.routed))
    mods = j["modules"]
    m = mods.get("top") or next(iter(mods.values()))
    cells = m["cells"]
    rep = []

    # net names (prefer visible)
    nname = {}
    for nn, v in m["netnames"].items():
        hide = v.get("hide_name", 0)
        for i, b in enumerate(v["bits"]):
            if isinstance(b, int):
                s = nn if len(v["bits"]) == 1 else "%s[%d]" % (nn, i)
                if b not in nname or not hide and nname[b][1]:
                    nname[b] = (s, hide)
    name = lambda b: nname.get(b, ("net%d" % b, 1))[0]

    drv = {}
    for cn, c in cells.items():
        for p, d in c["port_directions"].items():
            if d == "output":
                for b in c["connections"].get(p, []):
                    if b in drv:
                        die("net %s has two drivers" % name(b))
                    drv[b] = (cn, p)
    readers = collections.defaultdict(list)
    for cn, c in cells.items():
        for p, d in c["port_directions"].items():
            if d == "input":
                for b in c["connections"].get(p, []):
                    readers[b].append((cn, p))

    # constants: PSEUDO_GND/VCC, then LUTs whose every used input is constant (to a fixed point)
    const = {}
    for b, (cn, p) in drv.items():
        t = cells[cn]["type"]
        if t == "PSEUDO_GND":
            const[b] = 0
        elif t == "PSEUDO_VCC":
            const[b] = 1

    def lut_phys(c):
        """-> (list of (phys pin name, net), physical INIT over those pins, out port)."""
        init_s = c["parameters"]["INIT"]
        init, width = int(init_s, 2), len(init_s)
        outp = [p for p in ("O6", "O5") if c["connections"].get(p)]
        if len(outp) != 1:
            die("SLICE_LUTX with outputs %s" % outp)
        pins = []
        for k in range(1, 7):
            nm = c["attributes"].get("X_ORIG_PORT_A%d" % k, "")
            ls = [int(x) for x in RE_NAME.findall(nm)]
            if ls:
                conn = c["connections"].get("A%d" % k, [])
                if len(conn) != 1:
                    die("LUT pin A%d named %r but not connected" % (k, nm))
                pins.append(("A%d" % k, conn[0], ls))
        tab = 0
        for jj in range(1 << len(pins)):
            log = 0
            for i, (_, _, ls) in enumerate(pins):
                if (jj >> i) & 1:
                    for n in ls:
                        log |= 1 << n
            if log < width and (init >> log) & 1:
                tab |= 1 << jj
        return [(p, b) for p, b, _ in pins], tab, outp[0]

    changed = True
    while changed:
        changed = False
        for cn, c in cells.items():
            if c["type"] != "SLICE_LUTX":
                continue
            pins, tab, op = lut_phys(c)
            ob = c["connections"][op][0]
            if ob in const or not all(b in const for _, b in pins):
                continue
            addr = sum(const[b] << i for i, (_, b) in enumerate(pins))
            const[ob] = (tab >> addr) & 1
            changed = True

    # kept region
    keep = set(cn for cn in cells if cn.startswith(a.keep_prefix))
    for cn in keep:
        if cells[cn]["type"] not in COMB_TYPES:
            die("cell %s (%s) under the prefix is not combinational" % (cn, cells[cn]["type"]))
    work = list(keep)
    free = {}
    while work:
        cn = work.pop()
        c = cells[cn]
        for p, d in c["port_directions"].items():
            if d != "input":
                continue
            for b in c["connections"].get(p, []):
                if b in const or b in free:
                    continue
                if name(b) in cut_nets:
                    free[b] = "cut-net"
                    continue
                if b not in drv:
                    die("net %s read by %s/%s has no driver" % (name(b), cn, p))
                dc, dp = drv[b]
                t = cells[dc]["type"]
                if dc in keep:
                    continue
                if t in COMB_TYPES:
                    keep.add(dc)
                    work.append(dc)
                else:
                    free[b] = "%s output %s/%s" % (t, dc, dp)
    pulled = sorted(cn for cn in keep if not cn.startswith(a.keep_prefix))

    # emit
    U = a.unit_ps
    out_cells, bands_cells, bands_arcs = {}, {}, {}
    used_nets = set()
    intern = [max(list(drv) + list(readers)) + 1]
    stats = collections.Counter()
    missing = collections.Counter()
    sub_lo = []          # (key, lo ps) arcs/gates whose lo < 1 unit (raised by xaudit)
    carry_floor = []     # (cell, src, dst, real lo, model floor lo)

    def bit(b):
        if b in const:
            return str(const[b])
        used_nets.add(b)
        return b

    def arc_band(b, cn, pin):
        if b in const:
            return None
        if b in free and free[b] == "cut-net":
            d = drv.get(b)
        else:
            d = drv.get(b)
        if d is None:
            die("no driver for %s" % name(b))
        k = ("%s/%s" % d, "%s/%s" % (cn, pin))
        bd = ic.get(k)
        if bd is None:
            missing["IC"] += 1
            die("no interconnect delay for %s -> %s" % k)
        return bd

    def gate_band(cn, outp, pins=None):
        rows = io.get("%s/%s" % (cn, outp), [])
        if pins is not None:
            rows = [r for r in rows if r[0].rsplit("/", 1)[1] in pins]
        if not rows:
            die("no IOPATH rows to %s/%s" % (cn, outp))
        return (min(r[1][0] for r in rows), max(r[1][1] for r in rows))

    def put(nm, typ, conns, init, k, band, arcs):
        out_cells[nm] = {"type": typ, "parameters": {"INIT": format(init, "0%db" % (1 << k))},
                         "port_directions": dict({("I%d" % i): "input" for i in range(k)}, O="output"),
                         "connections": conns}
        bands_cells[nm] = [int(math.floor(band[0])), int(math.ceil(band[1]))]
        if band[0] < U:
            sub_lo.append((nm, band[0]))
        for pin, bd in arcs.items():
            if bd is None:
                continue
            key = "%s/%s" % (nm, pin)
            bands_arcs[key] = [int(math.floor(bd[0])), int(math.ceil(bd[1]))]
            if bd[0] < U:
                sub_lo.append((key, bd[0]))

    for cn in sorted(keep):
        c = cells[cn]
        t = c["type"]
        cc = c["connections"]
        if t == "SLICE_LUTX":
            pins, tab, op = lut_phys(c)
            k = len(pins)
            ob = cc[op][0]
            if ob in const:          # constant-folded (every input constant): readers see 0/1
                stats["LUT const-folded"] += 1
                continue
            if k == 0:
                die("LUT %s has no used input" % cn)
            conns = {"I%d" % i: [bit(b)] for i, (_, b) in enumerate(pins)}
            conns["O"] = [bit(ob)]
            arcs = {"I%d" % i: arc_band(b, cn, p) for i, (p, b) in enumerate(pins)}
            put(cn, "LUT%d" % k, conns, tab, k, gate_band(cn, op), arcs)
            stats["LUT"] += 1
        elif t == "SELMUX2_1":
            conns = {"I0": [bit(cc["0"][0])], "I1": [bit(cc["1"][0])], "I2": [bit(cc["S0"][0])],
                     "O": [bit(cc["OUT"][0])]}
            arcs = {"I0": arc_band(cc["0"][0], cn, "0"), "I1": arc_band(cc["1"][0], cn, "1"),
                    "I2": arc_band(cc["S0"][0], cn, "S0")}
            put(cn, "LUT3", conns, 0xCA, 3, gate_band(cn, "OUT"), arcs)
            stats[c["attributes"].get("X_ORIG_TYPE", "MUXF")] += 1
        elif t == "CARRY4":
            stats["CARRY4"] += 1
            rows = {}
            for dst in ["O%d" % i for i in range(4)] + ["CO%d" % i for i in range(4)]:
                for s, bd in io.get("%s/%s" % (cn, dst), []):
                    rows[(s.rsplit("/", 1)[1], dst)] = bd
            # carry-in
            if cc.get("CIN"):
                ci, ci_pin = cc["CIN"][0], "CIN"
            elif cc.get("CYINIT"):
                ci, ci_pin = cc["CYINIT"][0], "CYINIT"
            else:
                pc = c["parameters"].get("PRECYINIT_CONST", "0")
                if pc not in ("0", "1"):
                    die("CARRY4 %s: PRECYINIT_CONST %r" % (cn, pc))
                ci, ci_pin = None, pc
            hiS = lambda i, o: rows.get(("S%d" % i, o), (0.0, 0.0))[1]
            inc = max([hiS(0, "CO%d" % i) - hiS(0, "CO%d" % (i - 1)) for i in range(1, 4)] + [0.0])
            inc_band = (0.0, inc)
            for i in range(4):
                Si = cc["S%d" % i][0]
                DI = cc.get("DI%d" % i) or []
                cy = "%s#cy%d" % (cn, i)
                xo = "%s#xor%d" % (cn, i)
                co = cc.get("CO%d" % i) or []
                if co:
                    cob = co[0]
                else:
                    cob = intern[0]
                    intern[0] += 1
                # inputs of stage i
                if i == 0:
                    if ci is None:
                        ci_bit, ci_arc = ci_pin, None
                    else:
                        ci_bit, ci_arc = bit(ci), arc_band(ci, cn, ci_pin)
                else:
                    ci_bit, ci_arc = bit(prev), inc_band
                di_bit = bit(DI[0]) if DI else "0"
                di_arc = arc_band(DI[0], cn, "DI%d" % i) if DI else None
                s_bit, s_arc = bit(Si), arc_band(Si, cn, "S%d" % i)
                put(cy, "LUT3", {"I0": [di_bit], "I1": [ci_bit], "I2": [s_bit], "O": [bit(cob)]},
                    0xCA, 3, (0.0, rows.get(("S%d" % i, "CO%d" % i), (0, 0))[1]),
                    {"I0": di_arc, "I1": ci_arc, "I2": s_arc})
                Oi = cc.get("O%d" % i) or []
                if Oi:
                    put(xo, "LUT2", {"I0": [s_bit], "I1": [ci_bit], "O": [bit(Oi[0])]},
                        0x6, 2, rows[("S%d" % i, "O%d" % i)], {"I0": s_arc, "I1": ci_arc})
                prev = cob
            # check the decomposition against every IO row of this CARRY4
            g = lambda nm: bands_cells[nm]
            ar = lambda key: bands_arcs.get(key, [0, 0])
            for (sp, dst), bd in rows.items():
                kind, idx = ("O", int(dst[1:])) if dst[0] == "O" else ("CO", int(dst[2:]))
                if sp.startswith("S"):
                    j0, first = int(sp[1:]), "I2"
                elif sp.startswith("DI"):
                    j0, first = int(sp[2:]), "I0"
                else:
                    j0, first = 0, "I1"         # CIN / CYINIT
                if j0 > idx:
                    continue
                # elements: arc into stage j0 (external, not counted: it is the IC row),
                # then gates/internal arcs to the output
                hi = 0.0
                nel = 0
                if kind == "O" and j0 == idx and first != "I0":
                    hi += g("%s#xor%d" % (cn, idx))[1]
                    nel += 1
                else:
                    stop = idx if kind == "CO" else idx - 1
                    for s in range(j0, stop + 1):
                        hi += g("%s#cy%d" % (cn, s))[1]
                        nel += 1
                        if s < stop or kind == "O":
                            hi += inc
                            nel += 1
                    if kind == "O":
                        hi += g("%s#xor%d" % (cn, idx))[1]
                        nel += 1
                if hi + 1e-6 < bd[1]:
                    die("CARRY4 %s: path %s->%s model hi %.0f < real hi %.0f" % (cn, sp, dst, hi, bd[1]))
                if nel * U > bd[0]:
                    carry_floor.append((cn, sp, dst, bd[0], nel * U))
        else:
            die("unexpected kept cell %s type %s" % (cn, t))

    # ports: free inputs; outputs = kept-driven nets read outside
    ports = {}
    for b, why in sorted(free.items(), key=lambda kv: name(kv[0])):
        ports[name(b)] = {"direction": "input", "bits": [b]}
        used_nets.add(b)
    outs = []
    for b in sorted(used_nets):
        d = drv.get(b)
        if d and d[0] in keep and any(r[0] not in keep for r in readers.get(b, [])):
            outs.append(name(b))
    netnames = {}
    for b in sorted(used_nets):
        if b in free:
            continue
        nm = name(b) if b in nname else "n%d" % b
        if nm in netnames or nm in ports:
            nm = "%s#%d" % (nm, b)
        netnames[nm] = {"hide_name": 0, "bits": [b]}
    for nm, p in ports.items():
        netnames[nm] = {"hide_name": 0, "bits": p["bits"]}
    top = {"attributes": {"top": "00000000000000000000000000000001"}, "ports": ports,
           "cells": out_cells, "netnames": netnames}
    json.dump({"creator": "routed2x.py", "modules": {"gcd_ctl": top}}, open(a.out, "w"))
    allb = [v for v in bands_arcs.values()]
    json.dump({"comment": "per-arc bands from %s; see routed2x.py" % src, "unit_ps": U,
               "lut": [45, 124], "route": [0, max(v[1] for v in allb)],
               "cells": bands_cells, "arcs": bands_arcs}, open(a.bands, "w"))

    rep.append("routed2x: %s -> %s" % (a.routed, a.out))
    rep.append("delays: %s; unit %d ps" % (src, U))
    rep.append("kept %d cells (%d by prefix %r, %d pulled in as combinational fan-in): %s" % (
        len(keep), len(keep) - len(pulled), a.keep_prefix, len(pulled), dict(stats)))
    rep.append("emitted %d LUT cells, %d routed arcs; %d constant nets folded" % (
        len(out_cells), len(bands_arcs), len(const)))
    rep.append("free inputs (%d):" % len(free))
    for b, why in sorted(free.items(), key=lambda kv: name(kv[0])):
        rep.append("  %-28s %s" % (name(b), why))
    rep.append("observed outputs into the shell (%d): %s" % (len(outs), " ".join(sorted(outs))))
    rep.append("pulled-in cells outside the prefix (%d), first 20: %s" % (len(pulled), pulled[:20]))
    rep.append("elements with lo < 1 unit (xaudit raises to 1 step): %d" % len(sub_lo))
    for k, v in sorted(sub_lo, key=lambda kv: kv[1])[:10]:
        rep.append("  %-90s lo %.1f ps" % (k[-90:], v))
    rep.append("CARRY4 IO paths whose real lo is below the model floor (elements x unit): %d" % len(carry_floor))
    for r in carry_floor[:10]:
        rep.append("  %s %s->%s real lo %.0f ps, model floor %d ps" % (r[0][-50:], r[1], r[2], r[3], r[4]))
    los = sorted(v[0] for v in allb)
    his = sorted(v[1] for v in allb)
    w = sorted(v[1] - v[0] for v in allb)
    q = lambda s, f: s[int(f * (len(s) - 1))]
    rep.append("arc bands (ps): lo median %d, hi median %d, width median %d, width p90 %d, max hi %d" % (
        q(los, .5), q(his, .5), q(w, .5), q(w, .9), his[-1]))
    txt = "\n".join(rep) + "\n"
    if a.report:
        open(a.report, "w").write(txt)
    sys.stdout.write(txt)


if __name__ == "__main__":
    main()
