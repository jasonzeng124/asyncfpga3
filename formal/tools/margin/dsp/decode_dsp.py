#!/usr/bin/env python3
"""margin/dsp/decode_dsp.py (shard C, UNTRUSTED): shard A's decode_base.py, plus combinational DSP48E1 sites.

    python3 decode_dsp.py FASM XDC --json D0.json [--routed ROUTED.json] [--corrupt SITE:FIELD:BIT]

decode_base.py (formal/tools-A/target, imported read-only, NOT edited) refuses every DSP feature. This wrapper:
 1. patches its walker's source_pin (in this process only) so that a walk may END at a DSP48E1 output pin (P, PCOUT,
    ACOUT, BCOUT, ...: the net "<DSP site>/<pin>", as decode_base names a BUFG output) or at a DSP tile's TIEOFF
    (DSP_GND_* / DSP_VCC_*: a constant);
 2. runs decode_base's main() unchanged on the FASM with the DSP site configuration lines removed (its own output, the
    same cells, routes and refusals as before for everything that is not a DSP);
 3. decodes every DSP48E1 site's configuration (strict whitelist, below), walks the routes into its used input pins with
    the same walker, and appends one cell {"kind": "dsp48e1", "conn": {pin: route}, "dsp": {...}} per site to D0.json.
    build_net.py (A's) gives it no gate (an opaque cell: its input routes are added, its outputs are free nodes);
    dsp_gates.py then adds the DSP's gates to the net.

Configuration (prjxray-db segbits_dsp_{l,r}.db, fuzzer 100-dsp-mskpat: a Z-prefixed feature is set when the
attribute is 0 / FALSE):
  required  AREG_0, BREG_0, ZAREG_2_ACASCREG_1, ZBREG_2_BCASCREG_1, ZADREG, ZALUMODEREG, ZCARRYINREG, ZCARRYINSELREG,
            ZCREG, ZDREG, ZINMODEREG, ZMREG, ZOPMODEREG, ZPREG   (every register off: the site is combinational)
  optional  A_INPUT[0] / B_INPUT[0] (operand from ACIN / BCIN), ZIS_{ALUMODE,INMODE,OPMODE}_INVERTED[i],
            ZIS_CARRYIN_INVERTED (input inverters; absent = inverted), ZIS_CLK_INVERTED (no register: no effect),
            MASK / PATTERN (pattern detector only; its outputs must be unread)
  refused   AREG_2, BREG_2, USE_DPORT, USE_SIMD_*, AUTORESET_*, SEL_MASK_*, any missing required bit, anything else.
  USE_MULT has no bit in prjxray-db (the fuzzer found none): the multiplier is taken as present.
Control pins (OPMODE, ALUMODE, INMODE, CARRYINSEL, CARRYIN) must decode to constants. A pin driven through the
interconnect is the walked constant XOR its IS_*_INVERTED bit. A pin driven by the DSP tile's own DSP_GND/DSP_VCC pip
is the constant itself: those pips bypass the site's input inverter (patches/README.md, nextpnr-xilinx-dsp-constpins:
measured on the board, where the inverter-applied reading of the same bits gave INMODE 11111 and a dead A operand).
Data pins (A/ACIN, B/BCIN, C, PCIN, CARRYIN) are walked only where the decoded OPMODE/ALUMODE/INMODE read them.
With --routed, every decoded control value and register setting is checked against nextpnr's routed json (the
DSP48E1 cell at that BEL: its IS_*_INVERTED parameters, constant nets and DSP_VCC_PINS / DSP_GND_PINS), and every
data pin's net against the json net (one-to-one); any disagreement exits 1.
--corrupt SITE:FIELD:BIT flips one decoded control bit (FIELD opmode / alumode / inmode) AFTER the checks: a negative
control (the json check is skipped for that site; the output is marked "corrupted").
"""
import argparse, importlib.util, json, os, re, sys, tempfile
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
A_DIR = os.path.join(HERE, "..", "..", "..", "tools-A", "target")
sys.path.insert(0, HERE)
import dspmodel  # noqa: E402

_spec = importlib.util.spec_from_file_location("decode_base", os.path.join(A_DIR, "decode_base.py"))
DBm = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(DBm)
F2 = DBm.F2

DSP_OUT = re.compile(r"^(P|PCOUT|ACOUT|BCOUT|CARRYOUT|CARRYCASCOUT|MULTSIGNOUT|OVERFLOW|UNDERFLOW|PATTERNDETECT|PATTERNBDETECT)\d*$")
_orig_source_pin = DBm.Extract3.source_pin


def source_pin(self, node):
    r = _orig_source_pin(self, node)
    if r:
        return r
    for t, w in node:
        sp = self.fab.tt(self.fab.ttype(t))["_sitepin"].get(w)
        if not sp:
            continue
        site, pin, _v = sp
        if site["type"] == "TIEOFF" and pin in ("HARD0", "HARD1"):
            return ("const", pin == "HARD1")
        if site["type"] == "DSP48E1" and DSP_OUT.match(pin):
            return ("site", t, site, pin)
    return None


DBm.Extract3.source_pin = source_pin


def die(m):
    print("decode_dsp: " + m, file=sys.stderr)
    sys.exit(1)


REQUIRED = ["AREG_0", "BREG_0", "ZAREG_2_ACASCREG_1", "ZBREG_2_BCASCREG_1"] + \
    ["Z%sREG[0]" % r for r in ("AD", "ALUMODE", "CARRYIN", "CARRYINSEL", "C", "D", "INMODE", "M", "OPMODE", "P")]
OPTIONAL = re.compile(r"^(A_INPUT\[0\]|B_INPUT\[0\]|ZIS_(ALUMODE|INMODE|OPMODE)_INVERTED\[\d\]|ZIS_CARRYIN_INVERTED|"
                      r"ZIS_CLK_INVERTED)$")
CTRL = {"OPMODE": 7, "ALUMODE": 4, "INMODE": 5, "CARRYINSEL": 3, "CARRYIN": 1}
INV = {"OPMODE", "ALUMODE", "INMODE", "CARRYIN"}          # pins with a site inverter (IS_*_INVERTED)
WIDTH = {"A": 30, "B": 18, "C": 48, "PCIN": 48, "CARRYIN": 1, "ACIN": 30, "BCIN": 18}


def nname(fab, node):
    t, w = min(node)
    return "%s/%s" % (t, w)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("fasm"); ap.add_argument("xdc"); ap.add_argument("--json", required=True)
    ap.add_argument("--routed"); ap.add_argument("--corrupt", action="append", default=[])
    a = ap.parse_args()

    # ---- 1-2. decode_base on the FASM without the DSP site configuration (pips in DSP tiles stay)
    dspcfg = re.compile(r"^DSP_[LR]_X\d+Y\d+\.DSP48\.")
    lines = open(a.fasm).read().splitlines(True)
    keep = [l for l in lines if not dspcfg.match(l.split("#", 1)[0].strip())]
    fd, tmp = tempfile.mkstemp(suffix=".fasm", dir=os.path.dirname(os.path.abspath(a.json)))
    with os.fdopen(fd, "w") as f:
        f.writelines(keep)
    argv0 = sys.argv
    sys.argv = ["decode_base.py", tmp, a.xdc, "--json", a.json]
    try:
        DBm.main()
    finally:
        sys.argv = argv0
        os.unlink(tmp)
    D = json.load(open(a.json))
    if len(keep) == len(lines):
        print("decode_dsp: no DSP48 site configuration in the FASM (decode_base's output unchanged)", file=sys.stderr)
        return

    # ---- 3. DSP sites
    feats, vecs = DBm.read_fasm3(a.fasm)
    fab = DBm.Fabric3()
    ex = DBm.Extract3(fab, feats, vecs, {})
    st = json.load(open(os.path.join(F2.DB, "site_type_DSP48E1.json")))["site_pins"]
    cfg = defaultdict(set)
    for f in ex.site_feats:
        m = re.match(r"^(DSP_[LR]_X\d+Y\d+)\.DSP48\.(DSP_[01])\.(.+)$", f)
        if m:
            cfg[(m.group(1), m.group(2))].add(m.group(3))
        elif f.startswith("DSP_"):
            die("unexpected DSP tile feature %s" % f)
    vec_ok = defaultdict(list)
    for k, v in vecs.items():
        m = re.match(r"^(DSP_[LR]_X\d+Y\d+)\.DSP48\.(DSP_[01])\.(\w+)$", k)
        if m:
            if m.group(3) not in ("MASK", "PATTERN"):
                die("%s: DSP vector feature not modelled" % k)
            vec_ok[(m.group(1), m.group(2))].append("%s=%x" % (m.group(3), v))
            cfg[(m.group(1), m.group(2))]
    # every reference to a DSP output in decode_base's routes (the fabric's reads)
    reads = defaultdict(set)
    for c in D["cells"]:
        for v in c["conn"].values():
            if isinstance(v, dict) and str(v.get("net", "")).startswith("DSP48_"):
                s, p = v["net"].split("/")
                reads[s].add(p)
    for v in D["outputs"].values():
        if str(v.get("net", "")).startswith("DSP48_"):
            die("an output port reads %s directly" % v["net"])

    zero_reads = []
    lut_cells = {c["name"]: c for c in D["cells"] if c["kind"] == "lut6_2"}
    driven = {o for c in D["cells"] for o in c["outs"].values()}

    def src_key(src, what):
        """decode_base's naming of a walked source (its src_key is local to its main())."""
        if src[0] == "const":
            return {"const": src[1]}
        if src[0] == "float":
            die("%s: floating (no driver)" % what)
        _, tile, site, pin = src
        sn = fab.site_name(tile, site)
        if src[0] == "site":
            return {"net": "%s/%s" % (sn, pin)}
        if src[0] != "slice":
            die("%s: driven by %s %s (not modelled)" % (what, src[0], sn))
        if pin in "ABCD":
            if "%s.%sLUT" % (sn, pin) not in lut_cells:
                zero_reads.append(what)
                return {"const": False}
            return {"net": "%s.%s6" % (sn, pin)}
        if pin.endswith("Q"):
            net = "%s.%sQ" % (sn, pin[0])
        elif pin == "COUT":
            net = "%s.CO3" % sn
        elif pin.endswith("MUX"):
            L = pin[0]; i = "ABCD".index(L)
            pre = "%s.%s_X%d" % (tile, site["type"], site["x_coord"])
            sel = [o for o in ("O6", "O5", "XOR", "CY", "%s5Q" % L, "F7", "F8") if "%s.%sOUTMUX.%s" % (pre, L, o) in feats]
            if len(sel) != 1:
                die("%s: %s.%sOUTMUX select %s" % (what, pre, L, sel))
            key = {"O6": "%s6" % L, "O5": "%s5" % L, "XOR": "XOR%d" % i, "CY": "CO%d" % i, "%s5Q" % L: "%s5Q" % L,
                   "F7": "F7A" if L == "A" else "F7B", "F8": "F8"}[sel[0]]
            if sel[0] in ("O6", "O5") and "%s.%sLUT" % (sn, L) not in lut_cells:
                zero_reads.append(what)
                return {"const": False}
            net = "%s.%s" % (sn, key)
        else:
            die("%s: unmodelled slice source %s" % (what, pin))
        if net not in driven:
            die("%s: reads %s, which no decoded cell drives (a slice resource only a DSP reads: not modelled)" % (what, net))
        return {"net": net}

    def walk_pin(tile, site, pin, what):
        """decode_base's walk_pin (route kept pip by pip, source first), plus: tile-local tie or not."""
        v = site["site_pins"][pin]
        src, path = ex.walk(tile, v["wire"], what)
        k = dict(src_key(src, what))
        pips = [[t, p["dst_wire"], p["src_wire"], bool(ps), nname(fab, fab.node(t, p["src_wire"])), nname(fab, dn)]
                for (t, p, ps, dn) in reversed(path)]
        k["_route"] = {"sink": nname(fab, fab.node(tile, v["wire"])), "sinkwire": [tile, v["wire"]], "pips": pips,
                       "srcnode": pips[0][4] if pips else nname(fab, fab.node(tile, v["wire"])),
                       "srcpin": ([src[1], src[3], src[2]["type"], src[2]["x_coord"]] if src[0] in ("slice", "site") else None)}
        tl = bool(pips) and pips[0][0] == tile and re.match(r"^DSP_(GND|VCC)_[LR]$", pips[0][2]) is not None
        return k, tl

    J = None
    if a.routed:
        J = json.load(open(a.routed))["modules"]["top"]
        jnn = {}
        for n, v in J["netnames"].items():
            for i, b in enumerate(v["bits"]):
                jnn.setdefault(b, n if len(v["bits"]) == 1 else "%s[%d]" % (n, i))
        jsinks = defaultdict(int)
        for cn, c in J["cells"].items():
            for p, bits in c["connections"].items():
                if c.get("port_directions", {}).get(p) == "input":
                    for b in bits:
                        jsinks[b] += 1
        jbel = {c["attributes"].get("NEXTPNR_BEL"): (cn, c) for cn, c in J["cells"].items()}
    corrupt = defaultdict(list)
    for x in a.corrupt:
        s, fld, bit = x.split(":")
        corrupt[s].append((fld.lower(), int(bit)))

    net_map, net_map_r = {}, {}   # json net <-> decoded net (one-to-one), over every DSP data pin
    report = []
    sites = []
    for (tile, dk), fs in sorted(cfg.items()):
        j = fab.tt(fab.ttype(tile))
        site = [s for s in j["sites"] if s["type"] == "DSP48E1" and s["y_coord"] == int(dk[-1])][0]
        sn = fab.site_name(tile, site)
        if not fs and not vec_ok[(tile, dk)]:
            continue
        miss = [r for r in REQUIRED if r not in fs]
        if miss:
            die("%s (%s.%s): register(s) not off: missing %s -- registered DSPs are not modelled (refused)" % (sn, tile, dk, miss))
        bad = sorted(x for x in fs if x not in REQUIRED and not OPTIONAL.match(x))
        if bad:
            die("%s (%s.%s): DSP configuration not modelled (refused): %s" % (sn, tile, dk, bad))
        a_casc, b_casc = "A_INPUT[0]" in fs, "B_INPUT[0]" in fs
        inv = {p: [0 if ("ZIS_%s_INVERTED[%d]" % (p, i)) in fs else 1 for i in range(CTRL[p])] for p in ("OPMODE", "ALUMODE", "INMODE")}
        inv["CARRYIN"] = [0 if "ZIS_CARRYIN_INVERTED" in fs else 1]
        conn, val, how = {}, {}, {}
        for p, w in CTRL.items():
            v = 0
            for i in range(w):
                pin = p if p == "CARRYIN" else "%s%d" % (p, i)
                k, tl = walk_pin(tile, site, pin, "%s %s" % (sn, pin))
                if "const" not in k:
                    die("%s %s: control pin driven by %s, not a constant (dynamic DSP control not modelled)" % (sn, pin, k.get("net")))
                b = int(bool(k["const"]))
                if p in INV and not tl:
                    b ^= inv[p][i]
                how[pin] = ("tile-%s" % ("VCC" if k["const"] else "GND")) if tl else ("fabric-%d%s" % (int(bool(k["const"])), ",inv" if p in INV and inv[p][i] else ""))
                v |= b << i
                conn[pin] = k
            val[p] = v
        cfgv = (val["OPMODE"], val["ALUMODE"], val["INMODE"], val["CARRYINSEL"])
        try:
            dspmodel.check_cfg(*cfgv)
        except dspmodel.Refused as e:
            die("%s: %s (refused)" % (sn, e))
        used = dspmodel.used_ports(*cfgv)
        data = {}
        for port in ("A", "B", "C", "PCIN"):
            if port not in used:
                continue
            pp = {"A": "ACIN" if a_casc else "A", "B": "BCIN" if b_casc else "B"}.get(port, port)
            bits = []
            for i in range(WIDTH[pp]):
                k, tl = walk_pin(tile, site, "%s%d" % (pp, i), "%s %s%d" % (sn, pp, i))
                conn["%s%d" % (pp, i)] = k
                bits.append("%s%d" % (pp, i))
            data[port] = bits
        if "CARRYIN" in used:
            data["CARRYIN"] = ["CARRYIN"]
        cell = {"name": sn, "kind": "dsp48e1", "init": 0, "conn": conn, "inv": [],
                "outs": {}, "features": sorted(fs) + vec_ok[(tile, dk)],
                "dsp": {"tile": tile, "tiletype": fab.ttype(tile), "opmode": val["OPMODE"], "alumode": val["ALUMODE"],
                        "inmode": val["INMODE"], "carryinsel": val["CARRYINSEL"], "carryin": val["CARRYIN"],
                        "a_cascade": a_casc, "b_cascade": b_casc, "ports": data, "pin_source": how,
                        "is_inverted": inv}}
        sites.append((cell, tile, dk, fs, data, conn, val, how, inv, a_casc, b_casc))
    for c_ in sites:
        for pin, k in c_[0]["conn"].items():
            n = k.get("net", "")
            if n.startswith("DSP48_"):
                reads[n.split("/")[0]].add(n.split("/")[1])
    cells_out = []
    for (cell, tile, dk, fs, data, conn, val, how, inv, a_casc, b_casc) in sites:
        sn = cell["name"]
        rd = sorted(reads.get(sn, ()), key=lambda p: (re.sub(r"\d+$", "", p), int(re.sub(r"^\D+", "", p) or 0)))
        bad = [p for p in rd if not re.match(r"^(P|PCOUT|ACOUT|BCOUT)\d+$", p)]
        if bad:
            die("%s: the fabric reads %s (only P / PCOUT / ACOUT / BCOUT modelled)" % (sn, bad))
        # ---- the json check
        if J is not None and sn not in corrupt:
            jc = jbel.get("%s/DSP48E1" % sn)
            if jc is None:
                die("%s: no DSP48E1 at this BEL in the routed json" % sn)
            cn, c = jc
            P = c["parameters"]
            def pint(k, d=0):
                x = P.get(k)
                return d if x is None else (int(x, 2) if re.match(r"^[01]+$", str(x)) else int(x))
            for r_ in ("AREG", "BREG", "ACASCREG", "BCASCREG", "CREG", "DREG", "ADREG", "MREG", "PREG", "OPMODEREG",
                       "ALUMODEREG", "INMODEREG", "CARRYINREG", "CARRYINSELREG"):
                if pint(r_, 1) != 0:
                    die("%s: json %s = %s, decoded 0" % (sn, r_, P.get(r_)))
            for k_, want in (("A_INPUT", "CASCADE" if a_casc else "DIRECT"), ("B_INPUT", "CASCADE" if b_casc else "DIRECT"),
                             ("USE_DPORT", "FALSE"), ("USE_SIMD", "ONE48")):
                if P.get(k_, {"USE_DPORT": "FALSE", "USE_SIMD": "ONE48"}.get(k_)) != want:
                    die("%s: json %s = %s, decoded %s" % (sn, k_, P.get(k_), want))
            vccp = set(c["attributes"].get("DSP_VCC_PINS", "").split())
            gndp = set(c["attributes"].get("DSP_GND_PINS", "").split())
            for p, w in CTRL.items():
                for i in range(w):
                    pin = p if p == "CARRYIN" else "%s%d" % (p, i)
                    ji = pint("IS_%s_INVERTED" % p) if p == "CARRYIN" else pint("IS_%s[%d]_INVERTED" % (p, i))
                    if ji is None: ji = 0
                    if p in INV and ji != inv[p][i]:
                        die("%s %s: json IS_INVERTED %d, bitstream %d" % (sn, pin, ji, inv[p][i]))
                    nets = [jnn.get(b, b) for b in c["connections"].get(pin, [])]
                    if pin in vccp: raw = 1
                    elif pin in gndp: raw = 0
                    elif nets == ["$PACKER_VCC_NET"]: raw = 1
                    elif nets == ["$PACKER_GND_NET"]: raw = 0
                    else: die("%s %s: json connects %s (not a constant)" % (sn, pin, nets))
                    if ((raw ^ ji) if p in INV else raw) != (val[p] >> i) & 1:
                        die("%s %s: json logical %d, decoded %d (%s)" % (sn, pin, (raw ^ ji) if p in INV else raw, (val[p] >> i) & 1, how[pin]))
            for port, bits in data.items():
                for pin in bits:
                    k = conn[pin]
                    nets = [jnn.get(b, b) for b in c["connections"].get(pin, [])]
                    jn = nets[0] if nets else "$PACKER_GND_NET"
                    if jn in ("$PACKER_GND_NET", "$PACKER_VCC_NET"):
                        want = jn == "$PACKER_VCC_NET"
                        dn = k.get("net")
                        if "const" in k:
                            if bool(k["const"]) != want:
                                die("%s %s: json %s, decoded const %d" % (sn, pin, jn, k["const"]))
                        else:   # a LUT-driven constant: the decoded LUT must be constant on its constant inputs
                            cv = const_of(dn, D)
                            if cv is None or cv != want:
                                die("%s %s: json %s, decoded %s (value %s)" % (sn, pin, jn, dn, cv))
                        continue
                    dn = k.get("net")
                    if dn is None:
                        die("%s %s: json net %s, decoded constant %s" % (sn, pin, jn, k.get("const")))
                    if net_map.setdefault(jn, dn) != dn or net_map_r.setdefault(dn, jn) != jn:
                        die("%s %s: json net %s <-> decoded %s is not one-to-one (%s / %s)" % (sn, pin, jn, dn, net_map[jn], net_map_r[dn]))
            # the P / PCOUT bits the fabric reads <-> json P / PCOUT bits whose net has another reader
            for pfx in ("P", "PCOUT", "ACOUT", "BCOUT"):
                for i in range(48):
                    pin = "%s%d" % (pfx, i)
                    bits = c["connections"].get(pin, [])
                    jr = bool(bits) and jsinks.get(bits[0], 0) > 0
                    if jr != (pin in rd):
                        die("%s %s: json %s, decoded %s" % (sn, pin, "read" if jr else "unread", "read" if pin in rd else "unread"))
                    if jr:
                        jn = jnn.get(bits[0], bits[0]); dn = "%s/%s" % (sn, pin)
                        if net_map.setdefault(jn, dn) != dn or net_map_r.setdefault(dn, jn) != jn:
                            die("%s %s: json net %s <-> decoded %s not one-to-one" % (sn, pin, jn, dn))
            cell["dsp"]["json_cell"] = cn
        for fld, bit in corrupt.get(sn, ()):
            cell["dsp"][fld] ^= 1 << bit
            cell["dsp"]["corrupted"] = cell["dsp"].get("corrupted", []) + ["%s[%d]" % (fld, bit)]
            print("decode_dsp: NEGATIVE CONTROL: %s %s[%d] flipped -> %s" % (sn, fld, bit, format(cell["dsp"][fld], "b")), file=sys.stderr)
        cell["outs"] = {p: "%s/%s" % (sn, p) for p in rd}
        cell["dsp"]["read"] = rd
        cells_out.append(cell)
        report.append("%s %s.%s OPMODE %s ALUMODE %s INMODE %s CARRYINSEL %s CARRYIN %d A %s B %s ports %s; reads %d P, %d PCOUT, %d ACOUT, %d BCOUT"
                      % (sn, tile, dk, format(val["OPMODE"], "07b"), format(val["ALUMODE"], "04b"), format(val["INMODE"], "05b"),
                         format(val["CARRYINSEL"], "03b"), val["CARRYIN"], "ACIN" if a_casc else "A", "BCIN" if b_casc else "B",
                         "/".join(sorted(data)), *(sum(1 for p in rd if re.match(r"^%s\d" % x, p)) for x in ("P", "PCOUT", "ACOUT", "BCOUT"))))
    sites = cells_out
    # a DSP output read by the fabric must belong to a decoded DSP site
    for s in reads:
        if s not in {c["name"] for c in sites}:
            die("%s is read but has no decoded configuration" % s)
    # cascades: the site a cascade input reads must be a decoded DSP and its output pin the matching one
    names = {c["name"] for c in sites}
    for c in sites:
        for pin, k in c["conn"].items():
            n = k.get("net", "")
            if n.startswith("DSP48_"):
                s, p = n.split("/")
                want = {"ACIN": "ACOUT", "BCIN": "BCOUT", "PCIN": "PCOUT"}.get(re.sub(r"\d+$", "", pin))
                if s not in names or want is None or p != want + re.sub(r"^\D+", "", pin):
                    die("%s %s: cascade source %s unexpected" % (c["name"], pin, n))
    D["cells"] += sites
    D["census"]["dsp48e1"] = len(sites)
    D["zero_lut_reads"] += zero_reads
    D["dsp_report"] = report
    if a.routed:
        D["dsp_json_check"] = "%d DSP sites agree with %s (controls, registers, inverters, %d data nets one-to-one)" % (
            len([c for c in sites if "json_cell" in c["dsp"]]), os.path.basename(a.routed), len(net_map))
    with open(a.json, "w") as f:
        json.dump(D, f, indent=0, sort_keys=True)
    for r in report:
        print("decode_dsp: " + r, file=sys.stderr)
    if a.routed:
        print("decode_dsp: " + D["dsp_json_check"], file=sys.stderr)


def const_of(net, D):
    """The constant a decoded LUT output carries when every input it depends on is a constant, else None."""
    m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])([56])$", net or "")
    if not m:
        return None
    c = [x for x in D["cells"] if x["name"] == "%s.%sLUT" % (m.group(1), m.group(2))]
    if not c:
        return None
    c = c[0]
    init = c["init"] if m.group(3) == "6" else c["init"] & 0xFFFFFFFF
    k = 6 if m.group(3) == "6" else 5
    fixed = {}
    for i in range(k):
        v = c["conn"]["I%d" % i]
        if "const" in v:
            fixed[i] = int(bool(v["const"]))
    vals = set()
    for ad in range(1 << k):
        if all(((ad >> i) & 1) == b for i, b in fixed.items()):
            vals.add((init >> ad) & 1)
    return bool(vals.pop()) if len(vals) == 1 else None


if __name__ == "__main__":
    main()
