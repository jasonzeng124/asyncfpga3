#!/usr/bin/env python3
"""fasm2lean3 (probe C-11f): a WHOLE routed design's FASM -> a physical netlist (JSON).

    python3 formal/tools/fasm2lean3/fasm2lean3.py FASM XDC --json OUT.json

Reads ONLY the FASM (normally the one read back from the .bit) and prjxray-db,
plus the XDC to name IOB sites (as 11b/11c).  It reuses 11c's fabric model and
pip walker (formal/tools/fasm2lean2/fasm2lean2.py, imported read-only: Fabric,
Extract.walk, the IOI bypass checks, the short / floating checks) and extends
what a walk may end at and what a site may contain:

  primitive        decoded from (prjxray fuzzers 010-017)            physical cell (Formal.Gen kind)
  LUT6 / LUT6_2    ?LUT.INIT[63:0]; pins A1..A6 walked               lut6_2, I0..I5 = A1..A6
  FF (?FF)         ?FFMUX.{AX,O6,O5,XOR,CY}, FFSYNC, ?FF.ZRST,        fdre/fdse (sync, ZRST set/unset)
                   ?FF.ZINI, CEUSEDMUX, SRUSEDMUX, CLKINV;            fdce/fdpe (async)
                   CLK/CE/SR site pins walked
  FF (?5FF)        ?5FFMUX.{IN_A (=O5), IN_B (=?X)}, same site bits   as above
  CARRY4           PRECYINIT.{C0,C1,AX,CIN}, CARRY4.?CY0 (set: DI=O5, carry4: CI, CYINIT, DI0..3, S0..3
                   else DI=?X), S_i = O6 of LUT i                    O0..3 (XOR), CO0..3 (CY)
  ?OUTMUX          O6, O5, XOR, CY, ?5Q                              (a selection, no cell)
  BUFGCTRL         I0 walked; identity (H_BUF_IDENTITY)              buf "BUFGCTRL"
  BSCAN            TDO walked; outputs are opaque sources            opaque "BSCAN"
  IOB (output)     the 11c walk from the pad's O pin                 an output port
  MUXF7/F8, LATCH, LUTRAM/SRL, DSP/BRAM, any other site               REFUSED (exit 1, named)

Every FASM feature is either consumed by the decoder, a known default, or a
refusal.  Nets are named by their DRIVER: "<site>.<A..D>6" (O6), ".<L>5" (O5),
".<L>Q", ".<L>5Q", ".XOR<i>", ".CO<i>", "<site>/<pin>" for a non-slice output,
plus each FF's synthetic master "<Q net>$master" (Formal.Gen's H_FF_MS model).
A LUT site without an INIT feature (all-zero INIT) drives constant 0; a read of
it is recorded as const 0 (and counted).
"""
import argparse
import csv
import importlib.util
import json
import os
import re
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "fasm2lean2", os.path.join(HERE, "..", "fasm2lean2", "fasm2lean2.py"))
F2 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(F2)

LS = "ABCD"


def die(msg):
    print("fasm2lean3: " + msg, file=sys.stderr)
    sys.exit(1)


class Extract3(F2.Extract):
    def source_pin(self, node):
        for t, w in node:
            if w in ("GND_WIRE", "VCC_WIRE"):
                return ("const", w == "VCC_WIRE")
        for t, w in node:
            j = self.fab.tt(self.fab.ttype(t))
            sp = j["_sitepin"].get(w)
            if not sp:
                continue
            site, pin, v = sp
            if site["type"] in ("SLICEL", "SLICEM"):
                if pin in F2.SLICE_OUT:
                    return ("slice", t, site, pin)
                continue
            if site["type"].startswith("IOB"):
                if pin == "I":
                    return ("iob", t, site, pin)
                continue
            if "res" in v:      # an output site pin (prjxray-db: drivers carry R)
                return ("site", t, site, pin)
        return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("fasm")
    ap.add_argument("xdc")
    ap.add_argument("--json", required=True)
    a = ap.parse_args()

    feats, vecs = F2.read_fasm(a.fasm)
    fab = F2.Fabric()
    pin_site = {}
    with open(os.path.join(F2.DB, F2.PKG, "package_pins.csv")) as f:
        for r in csv.DictReader(f):
            pin_site[r["pin"]] = r["site"]
    port_of_site = {}
    with open(a.xdc) as f:
        for line in f:
            m = re.match(r"\s*set_property\s+PACKAGE_PIN\s+(\S+)\s+\[get_ports\s+(?:\{([^}]+)\}|([^\s\]]+))\s*\]", line)
            if m:
                port_of_site[pin_site[m.group(1)]] = m.group(2) or m.group(3)
    ex = Extract3(fab, feats, vecs, port_of_site)

    # ---- site features, grouped by (tile, site prefix)
    consumed = set()
    sf = defaultdict(set)           # "TILE.SLICEL_X1" -> {"AFFMUX.O6", ...}
    for f in ex.site_feats:
        p = f.split(".")
        if len(p) >= 3 and re.match(r"SLICE[LM]_X[01]$", p[1]):
            sf["%s.%s" % (p[0], p[1])].add(".".join(p[2:]))
    lut_init = {}
    for name, val in vecs.items():
        m = F2.RE_LUT.match(name)
        if m:
            lut_init[("%s.%s" % (m.group(1), m.group(2)), m.group(3))] = val
            consumed.add(name)

    def slice_site(pre):
        tile, sl = pre.split(".")
        j = fab.tt(fab.ttype(tile))
        x = int(sl[-1])
        site = [s for s in j["sites"] if s["type"].startswith("SLICE") and s["x_coord"] == x][0]
        return tile, site, fab.site_name(tile, site)

    sname_of = {}
    zero_reads = []

    def has(pre, feat):
        if feat in sf[pre]:
            consumed.add("%s.%s" % (pre, feat))
            return True
        return False

    def src_key(src, what):
        if src[0] == "const":
            return {"const": src[1]}
        _, tile, site, pin = src
        if src[0] == "iob":
            sname = fab.site_name(tile, site)
            port = port_of_site.get(sname)
            if port is None:
                die("%s: driven by IOB %s, not named by the XDC" % (what, sname))
            return {"net": "port:" + port}
        if src[0] == "site":
            return {"net": "%s/%s" % (fab.site_name(tile, site), pin)}
        pre = "%s.%s_X%d" % (tile, site["type"], site["x_coord"])
        sn = fab.site_name(tile, site)
        sname_of[pre] = sn
        if pin in LS:
            if (pre, pin) not in lut_init:
                zero_reads.append(what)
                return {"const": False}
            return {"net": "%s.%s6" % (sn, pin)}
        if pin.endswith("Q"):
            return {"net": "%s.%sQ" % (sn, pin[0])}
        if pin == "COUT":
            return {"net": "%s.CO3" % sn}
        if pin.endswith("MUX"):
            L = pin[0]
            i = LS.index(L)
            for o, key in (("O6", "%s6" % L), ("O5", "%s5" % L), ("XOR", "XOR%d" % i),
                           ("CY", "CO%d" % i), ("%s5Q" % L, "%s5Q" % L)):
                if has(pre, "%sOUTMUX.%s" % (L, o)):
                    if o in ("O6", "O5") and (pre, L) not in lut_init:
                        zero_reads.append(what)
                        return {"const": False}
                    return {"net": "%s.%s" % (sn, key)}
            die("%s: %s.%s selects an unmodelled OUTMUX input (F7/F8?) %s" % (what, pre, pin, sorted(sf[pre])))
        die("%s: unmodelled slice source %s.%s" % (what, pre, pin))

    def walk_pin(tile, site, pin, what):
        v = site["site_pins"][pin]
        src, _path = ex.walk(tile, v["wire"], what)
        return src_key(src, what)

    cells = []
    # ---- LUT sites
    for (pre, L), init in sorted(lut_init.items()):
        tile, site, sn = slice_site(pre)
        sname_of[pre] = sn
        conn = {}
        for k in range(1, 7):
            conn["I%d" % (k - 1)] = walk_pin(tile, site, "%s%d" % (L, k), "%s %s%d" % (sn, L, k))
        cells.append({"name": "%s.%sLUT" % (sn, L), "kind": "lut6_2", "init": init, "conn": conn,
                      "outs": {"O6": "%s.%s6" % (sn, L), "O5": "%s.%s5" % (sn, L)}, "inv": []})

    def lut_net(pre, sn, L, o, what):
        if (pre, L) not in lut_init:
            zero_reads.append(what)
            return {"const": False}
        return {"net": "%s.%s%s" % (sn, L, o)}

    # ---- per slice: FFs, CARRY4, refusals
    carry_used = set()
    for pre in sorted(sf):
        tile, site, sn = slice_site(pre)
        sname_of[pre] = sn
        fs = sf[pre]
        if any(re.search(r"F7|F8", x) for x in fs):
            die("%s: wide mux (MUXF7/F8) not modelled: %s" % (sn, sorted(x for x in fs if re.search("F7|F8", x))))
        if has(pre, "LATCH"):
            die("%s: LATCH mode not modelled (LDCE/LDPE)" % sn)
        if any(re.search(r"\.RAM|SRL|SMALL|WA[678]USED|WEMUX", "." + x) for x in fs):
            die("%s: LUTRAM/SRL not modelled: %s" % (sn, sorted(fs)))
        ffs = []
        for L in LS:
            for fx in ("FF", "5FF"):
                mux = [x for x in fs if x.startswith("%s%sMUX." % (L, fx))]
                if mux:
                    ffs.append((L, fx, mux))
        sync = has(pre, "FFSYNC")
        clkinv = has(pre, "CLKINV")
        has(pre, "NOCLKINV")
        ceused = has(pre, "CEUSEDMUX")
        srused = has(pre, "SRUSEDMUX")
        if ffs:
            clk = walk_pin(tile, site, "CLK", "%s CLK" % sn)
            ce = walk_pin(tile, site, "CE", "%s CE" % sn) if ceused else {"const": True}
            sr = walk_pin(tile, site, "SR", "%s SR" % sn) if srused else {"const": False}
        for L, fx, mux in ffs:
            if len(mux) != 1:
                die("%s: two %s%sMUX values %s" % (sn, L, fx, mux))
            sel = mux[0].split(".", 1)[1]
            consumed.add("%s.%s" % (pre, mux[0]))
            i = LS.index(L)
            what = "%s %s%s D" % (sn, L, fx)
            if fx == "FF":
                if sel == L + "X":
                    d = walk_pin(tile, site, L + "X", what)
                elif sel in ("O6", "O5"):
                    d = lut_net(pre, sn, L, sel[1], what)
                elif sel == "XOR":
                    d = {"net": "%s.XOR%d" % (sn, i)}; carry_used.add(pre)
                elif sel == "CY":
                    d = {"net": "%s.CO%d" % (sn, i)}; carry_used.add(pre)
                else:
                    die("%s: %s not modelled" % (sn, mux[0]))
            else:
                if sel == "IN_A":
                    d = lut_net(pre, sn, L, "5", what)
                elif sel == "IN_B":
                    d = walk_pin(tile, site, L + "X", what)
                else:
                    die("%s: %s not modelled" % (sn, mux[0]))
            zrst = has(pre, "%s%s.ZRST" % (L, fx))
            zini = has(pre, "%s%s.ZINI" % (L, fx))
            kind = ("fdre" if zrst else "fdse") if sync else ("fdce" if zrst else "fdpe")
            rpin = {"fdre": "R", "fdse": "S", "fdce": "CLR", "fdpe": "PRE"}[kind]
            q = "%s.%s%sQ" % (sn, L, "5" if fx == "5FF" else "")
            cells.append({"name": "%s.%s%s" % (sn, L, fx), "kind": kind, "init": 0 if zini else 1,
                          "conn": {"C": clk, "CE": ce, "D": d, rpin: sr,
                                   "Q": {"net": q}, "M": {"net": q + "$master"}},
                          "outs": {"Q": q, "M": q + "$master"}, "inv": ["C"] if clkinv else []})
        if (not ffs) and (sync or clkinv or ceused or srused):
            print("fasm2lean3: note: %s has FF control bits but no FF" % sn, file=sys.stderr)
        if any(re.search(r"CARRY4|PRECYINIT\.(AX|C1|CIN)|OUTMUX\.(XOR|CY)", x) for x in fs):
            carry_used.add(pre)

    # CARRY4 used because a walk reached its COUT or a XOR/CY output
    def add_carries():
        for pre in sorted(carry_used):
            sn = sname_of[pre]
            if any(c["name"] == sn + ".CARRY4" for c in cells):
                continue
            tile, site, _ = slice_site(pre)
            fs = sf[pre]
            if has(pre, "PRECYINIT.CIN"):
                ci, cy = walk_pin(tile, site, "CIN", "%s CIN" % sn), {"const": False}
                cin_pre = None
            elif has(pre, "PRECYINIT.AX"):
                ci, cy = {"const": False}, walk_pin(tile, site, "AX", "%s AX (CYINIT)" % sn)
            elif has(pre, "PRECYINIT.C1"):
                ci, cy = {"const": False}, {"const": True}
            else:
                has(pre, "PRECYINIT.C0")
                ci, cy = {"const": False}, {"const": False}
            conn = {"CI": ci, "CYINIT": cy}
            for i, L in enumerate(LS):
                if has(pre, "CARRY4.%sCY0" % L):
                    conn["DI%d" % i] = lut_net(pre, sn, L, "5", "%s DI%d" % (sn, i))
                else:
                    conn["DI%d" % i] = walk_pin(tile, site, L + "X", "%s DI%d (%sX)" % (sn, i, L))
                conn["S%d" % i] = lut_net(pre, sn, L, "6", "%s S%d" % (sn, i))
            outs = {}
            for i in range(4):
                outs["O%d" % i] = "%s.XOR%d" % (sn, i)
                outs["CO%d" % i] = "%s.CO%d" % (sn, i)
            cells.append({"name": sn + ".CARRY4", "kind": "carry4", "init": 0, "conn": conn,
                          "outs": outs, "inv": []})
    # iterate: a CIN walk may reach a further COUT
    for _ in range(64):
        n0 = len(cells)
        referenced = {v["net"] for c in cells for v in c["conn"].values() if "net" in v}
        for net in referenced:
            m = re.match(r"^(SLICE_X\d+Y\d+)\.(XOR|CO)\d$", net)
            if m:
                pre = [p for p, s in sname_of.items() if s == m.group(1)]
                if pre:
                    carry_used.add(pre[0])
        add_carries()
        if len(cells) == n0:
            break

    # ---- non-slice sites: BUFGCTRL, BSCAN (by their features)
    other = defaultdict(set)
    for f in ex.site_feats:
        p = f.split(".")
        if f in consumed or (len(p) >= 2 and re.match(r"SLICE[LM]_X[01]$", p[1])):
            continue
        other[p[0]].add(".".join(p[1:]))
    for tile in sorted(other):
        for rest in sorted(other[tile]):
            m = re.match(r"^BUFGCTRL\.(BUFGCTRL_X\d+Y\d+)\.IN_USE$", rest)
            if m:
                sname = m.group(1)
                j = fab.tt(fab.ttype(tile))
                site = [s for s in j["sites"] if fab.site_name(tile, s) == sname][0]
                feats_b = sorted(x for x in other[tile] if x.startswith("BUFGCTRL.%s." % sname))
                for x in feats_b:
                    consumed.add("%s.%s" % (tile, x))
                cells.append({"name": sname, "kind": "buf", "init": 0,
                              "conn": {"I": walk_pin(tile, site, "I0", "%s I0" % sname)},
                              "outs": {"O": "%s/O" % sname}, "inv": [], "features": feats_b})
    # BSCAN: an opaque cell wherever a walk reached one of its outputs
    srcs = {v["net"] for c in cells for v in c["conn"].values() if "net" in v}
    for net in sorted(srcs):
        m = re.match(r"^(BSCAN_X\d+Y\d+)/(\w+)$", net)
        if m and not any(c["name"] == m.group(1) for c in cells):
            sname = m.group(1)
            tile = [t for t, g in fab.grid.items() if sname in g.get("sites", {})][0]
            j = fab.tt(fab.ttype(tile))
            site = [s for s in j["sites"] if fab.site_name(tile, s) == sname][0]
            outs = sorted({n.split("/")[1] for n in srcs if n.startswith(sname + "/")})
            feats_b = sorted(x for x in other[tile] if "BSCAN" in x)
            for x in feats_b:
                consumed.add("%s.%s" % (tile, x))
            cells.append({"name": sname, "kind": "opaque", "prim": "BSCAN", "init": 0,
                          "conn": {"TDO": walk_pin(tile, site, "TDO", "%s TDO" % sname)},
                          "outs": {o: "%s/%s" % (sname, o) for o in outs}, "inv": [],
                          "features": feats_b})

    # ---- output ports (11c's rule)
    outs = {}
    for sname, port in sorted(port_of_site.items(), key=lambda kv: kv[1]):
        tile = [t for t, g in fab.grid.items() if sname in g.get("sites", {})][0]
        j = fab.tt(fab.ttype(tile))
        site = [s for s in j["sites"] if fab.site_name(tile, s) == sname][0]
        fy = "%s.IOB_Y%d" % (tile, int(re.search(r"Y(\d+)$", sname).group(1)) % 2)
        if not any(f.startswith(fy + ".") and ".DRIVE." in f for f in feats):
            continue
        src, _ = ex.walk(tile, site["site_pins"]["O"]["wire"], "port %s" % port)
        outs[port] = src_key(src, "port %s" % port)

    # ---- leftover features: every one must be a known default / electrical, else refuse
    left = sorted(f for f in ex.site_feats if f not in consumed)
    bad = []
    census = defaultdict(int)
    for f in left:
        rest = f.split(".", 1)[1] if "." in f else f
        for rx, cat in F2.SITE_OK + [(r"^BUFGCTRL\.", "bufgctrl (unused site default)"),
                                      (r"^SLICE[LM]_X[01]\.PRECYINIT\.C0$", "default")]:
            if re.search(rx, rest):
                census[cat] += 1
                break
        else:
            bad.append(f)
    if bad:
        die("site features the model does not cover (refused):\n  " + "\n  ".join(bad))

    unused = [(t, d, s) for t in ex.active for d, s in ex.active[t] if (t, d, s) not in ex.used_pips]
    kinds = defaultdict(int)
    for c in cells:
        kinds[c["kind"] if c["kind"] != "opaque" else "opaque:" + c["prim"]] += 1
    res = {"cells": cells, "outputs": outs, "census": dict(kinds), "zero_lut_reads": zero_reads,
           "leftover_features": dict(census), "untraced_pips": len(unused),
           "active_pips": sum(len(v) for v in ex.active.values())}
    with open(a.json, "w") as f:
        json.dump(res, f, indent=0, sort_keys=True)
    print("fasm2lean3: %s; %d outputs; %d reads of all-zero LUTs; %d active pips, %d untraced"
          % (dict(kinds), len(outs), len(zero_reads), res["active_pips"], len(unused)), file=sys.stderr)


if __name__ == "__main__":
    main()
