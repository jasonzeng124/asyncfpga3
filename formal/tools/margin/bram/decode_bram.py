#!/usr/bin/env python3
"""margin/bram/decode_bram.py (shard C, UNTRUSTED): decode_dsp.py (decode_base + DSP48E1), plus RAMB18E1 sites.

    python3 decode_bram.py FASM XDC --json D0.json [--routed ROUTED.json]

decode_base.py (formal/tools-A/target) and decode_dsp.py are imported read-only, NOT edited. This wrapper:
 1. patches the walker's source_pin (in this process only) so a walk may END at a RAMB18 output pin (wire
    BRAM_RAMB18_DO* for the site at y 1, BRAM_FIFO18_DO* for the one at y 0); the net is "<site>/<RAMB18E1 pin>";
 2. runs decode_dsp's main() on the FASM with the RAMB18 site configuration lines (RAMB18_Y0. / RAMB18_Y1.) removed;
 3. decodes every RAMB18 site in use (strict whitelist, below), walks its input pins with the same walker, and appends
    one cell {"kind": "ramb18e1", "conn": {pin: route}, "ram": {...}} per site.  bram_gates.py makes its gates.

What is modelled (bd_mem.v's use, nothing else; anything else is refused):
  port A only, TDP, READ_WIDTH_A = WRITE_WIDTH_A = 18, DOA_REG 0, WRITE_MODE_A WRITE_FIRST (neither READ_FIRST nor
  NO_CHANGE set), CLKARDCLK not inverted (ZINV_CLKARDCLK) and driven by a net; ENARDEN logical 1; RSTRAMARSTRAM and
  RSTREGARSTREG logical 0 (else the output latch could be reset); port B: CLKBWRCLK constant (no edge ever: port B
  never acts), DOBDO / DOPBDOP unread.  Word address = ADDRARDADDR[13:4] (x18), data DIADI[15:0], DIPADIP[1:0], byte
  write enables WEA[1:0] (WEA[3:2] unused in x18).  Initial contents from INIT_00..3F / INITP_00..07 (not verified
  against a fuzzer: every route seen so far has none, the host fills the arrays), output latch initial value from
  ZINIT_A (Z = inverted).
Logical value of a constant control pin = walked constant XOR its inverter (inverted unless ZINV_<pin> is set).
With --routed, every constant control's logical value is checked against nextpnr's routed json (its connection's
constant XOR IS_<pin>_INVERTED), and every data / address / WE / clock pin's net one-to-one; disagreement exits 1.
"""
import argparse, importlib.util, json, os, re, sys, tempfile
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("decode_dsp", os.path.join(HERE, "..", "dsp", "decode_dsp.py"))
DD = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(DD)
DBm = DD.DBm
F2 = DBm.F2

DOWIRE = re.compile(r"^BRAM_(RAMB18|FIFO18)_((DOADO|DOPADOP|DOBDO|DOPBDOP)\d+)$")
_prev_source_pin = DBm.Extract3.source_pin


def ram_site(fab, tile, y):
    j = fab.tt(fab.ttype(tile))
    s = [x for x in j["sites"] if x["prefix"] == "RAMB18" and x["y_coord"] == y]
    if len(s) != 1:
        die("%s: no RAMB18 site at y %d" % (tile, y))
    return s[0]


def source_pin(self, node):
    r = _prev_source_pin(self, node)
    if r:
        return r
    for t, w in node:
        m = DOWIRE.match(w)
        if m and self.fab.ttype(t).startswith("BRAM_"):
            return ("site", t, ram_site(self.fab, t, 1 if m.group(1) == "RAMB18" else 0), m.group(2))
    return None


DBm.Extract3.source_pin = source_pin


def die(m):
    print("decode_bram: " + m, file=sys.stderr)
    sys.exit(1)


REQUIRED = {"IN_USE", "READ_WIDTH_A_18", "WRITE_WIDTH_A_18", "ZINV_CLKARDCLK"}
OPTIONAL = re.compile(r"^(READ_WIDTH_B_(1|2|4|9|18)|WRITE_WIDTH_B_(1|2|4|9|18)|RSTREG_PRIORITY_[AB]_(RSTREG|REGCE)|"
                      r"ZINV_(CLKBWRCLK|ENARDEN|ENBWREN|REGCLKARDRCLK|REGCLKB|RSTRAMARSTRAM|RSTRAMB|RSTREGARSTREG|RSTREGB)|"
                      r"DOB_REG|WRITE_MODE_B_(READ_FIRST|NO_CHANGE)|RDADDR_COLLISION_HWCONFIG_DELAYED_WRITE)$")
UNUSED_OK = re.compile(r"^(READ_WIDTH_[AB]_1|WRITE_WIDTH_[AB]_1|RSTREG_PRIORITY_[AB]_RSTREG|RDADDR_COLLISION_HWCONFIG_DELAYED_WRITE)$")
VECOK = re.compile(r"^(ZINIT_[AB]|ZSRVAL_[AB]|INIT_[0-3][0-9A-F]|INITP_0[0-7])$")
INVPINS = ("CLKARDCLK", "CLKBWRCLK", "ENARDEN", "ENBWREN", "REGCLKARDRCLK", "REGCLKB", "RSTRAMARSTRAM", "RSTRAMB",
           "RSTREGARSTREG", "RSTREGB")
# pins that may float (unrouted): they act only with DOA_REG = 1 or through port B, which never clocks here
FLOATOK = {"REGCLKARDRCLK", "REGCLKB", "REGCEAREGCE", "REGCEB", "RSTREGARSTREG", "RSTREGB", "RSTRAMB", "ENBWREN", "WEBWE",
           "DIPADIP"}
CTRL1 = {"ENARDEN": 1, "RSTRAMARSTRAM": 0}       # required logical constants
DATA = ["ADDRARDADDR%d" % i for i in range(4, 14)] + ["DIADI%d" % i for i in range(16)] + \
       ["DIPADIP%d" % i for i in range(2)] + ["WEA0", "WEA1"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("fasm"); ap.add_argument("xdc"); ap.add_argument("--json", required=True)
    ap.add_argument("--routed")
    a = ap.parse_args()
    ramcfg = re.compile(r"^BRAM_[LR]_X\d+Y\d+\.(RAMB18_Y[01]|RAMB36)\.")
    lines = open(a.fasm).read().splitlines(True)
    keep = [l for l in lines if not ramcfg.match(l.split("#", 1)[0].strip())]
    fd, tmp = tempfile.mkstemp(suffix=".fasm", dir=os.path.dirname(os.path.abspath(a.json)))
    with os.fdopen(fd, "w") as f:
        f.writelines(keep)
    argv0 = sys.argv
    sys.argv = ["decode_dsp.py", tmp, a.xdc, "--json", a.json] + (["--routed", a.routed] if a.routed else [])
    try:
        DD.main()
    finally:
        sys.argv = argv0
        os.unlink(tmp)
    D = json.load(open(a.json))
    if len(keep) == len(lines):
        print("decode_bram: no RAMB18 site configuration in the FASM (decode_dsp's output unchanged)", file=sys.stderr)
        return

    feats, vecs = DBm.read_fasm3(a.fasm)
    fab = DBm.Fabric3()
    ex = DBm.Extract3(fab, feats, vecs, {})
    cfg, vcfg = defaultdict(set), defaultdict(dict)
    for f in ex.site_feats:
        m = re.match(r"^(BRAM_[LR]_X\d+Y\d+)\.RAMB18_Y([01])\.(.+)$", f)
        if m:
            cfg[(m.group(1), int(m.group(2)))].add(m.group(3))
    for f in ex.site_feats:
        m = re.match(r"^(BRAM_[LR]_X\d+Y\d+)\.RAMB36\.(.+)$", f)
        if m and m.group(2) not in ("RAM_EXTENSION_A_NONE_OR_UPPER", "RAM_EXTENSION_B_NONE_OR_UPPER"):
            die("%s: RAMB36 feature not modelled (a cascaded / 36-bit RAM)" % f)
    for k, v in vecs.items():
        m = re.match(r"^(BRAM_[LR]_X\d+Y\d+)\.RAMB18_Y([01])\.(\w+)$", k)
        if m:
            if not VECOK.match(m.group(3)):
                die("%s: RAMB18 vector feature not modelled" % k)
            vcfg[(m.group(1), int(m.group(2)))][m.group(3)] = v
            cfg[(m.group(1), int(m.group(2)))]
    # a ZINIT / ZSRVAL / INIT single-bit set may come as plain features "X[k]"
    for key, fs in list(cfg.items()):
        for f in list(fs):
            m = re.match(r"^(ZINIT_[AB]|ZSRVAL_[AB]|INIT_[0-3][0-9A-F]|INITP_0[0-7])\[(\d+)\]$", f)
            if m:
                vcfg[key][m.group(1)] = vcfg[key].get(m.group(1), 0) | (1 << int(m.group(2)))
                fs.discard(f)

    reads = defaultdict(set)
    for c in D["cells"]:
        for v in c["conn"].values():
            if isinstance(v, dict) and str(v.get("net", "")).startswith("RAMB18_"):
                s, p = v["net"].split("/")
                reads[s].add(p)
    for v in D["outputs"].values():
        if str(v.get("net", "")).startswith("RAMB18_"):
            die("an output port reads %s directly" % v["net"])

    lut_cells = {c["name"]: c for c in D["cells"] if c["kind"] == "lut6_2"}
    driven = {o for c in D["cells"] for o in c["outs"].values()}

    def walk_pin(tile, y, pin, what):
        wire = "BRAM_%s_%s" % ("RAMB18" if y == 1 else "FIFO18", pin)
        src, path = ex.walk(tile, wire, what)
        if src[0] == "const":
            k = {"const": src[1]}
        elif src[0] == "float":
            if pin.split("_")[0] in FLOATOK or re.sub(r"\d+$", "", pin) in FLOATOK:
                return {"float": True}, False
            die("%s: floating (no driver)" % what)
        else:
            k = dict(DD_src_key(fab, src, what, lut_cells, driven, feats))
        pips = [[t, p["dst_wire"], p["src_wire"], bool(ps), DD.nname(fab, fab.node(t, p["src_wire"])), DD.nname(fab, dn)]
                for (t, p, ps, dn) in reversed(path)]
        k["_route"] = {"sink": DD.nname(fab, fab.node(tile, wire)), "sinkwire": [tile, wire], "pips": pips,
                       "srcnode": pips[0][4] if pips else DD.nname(fab, fab.node(tile, wire)),
                       "srcpin": ([src[1], src[3], src[2]["type"], src[2]["x_coord"]] if src[0] in ("slice", "site") else None)}
        tl = bool(pips) and pips[0][0] == tile and not pips[0][2].startswith("BRAM_IMUX") and \
            ("GND" in pips[0][2] or "VCC" in pips[0][2])
        return k, tl

    J = None
    if a.routed:
        J = json.load(open(a.routed))["modules"]["top"]
        jnn = {}
        for n, v in J["netnames"].items():
            for i, b in enumerate(v["bits"]):
                jnn.setdefault(b, n if len(v["bits"]) == 1 else "%s[%d]" % (n, i))
        jbel = {c["attributes"].get("NEXTPNR_BEL"): (cn, c) for cn, c in J["cells"].items()}
    net_map, net_map_r = {}, {}
    cells_out, report = [], []
    for (tile, y), fs in sorted(cfg.items()):
        site = ram_site(fab, tile, y)
        sn = fab.site_name(tile, site)
        if "IN_USE" not in fs:
            # an unused site read back from the bits: its default configuration only (the widths' and priorities'
            # zero state, the collision mode); nothing reads it (checked below: a read of it has no decoded site)
            if all(UNUSED_OK.match(x) for x in fs) and all(VECOK.match(k_) and not k_.startswith("INIT") for k_ in vcfg[(tile, y)]):
                continue
            die("%s: RAMB18 configuration without IN_USE: %s" % (sn, sorted(fs)))
        miss = sorted(REQUIRED - fs)
        if miss:
            die("%s: required feature(s) missing %s -- not the modelled configuration (refused)" % (sn, miss))
        bad = sorted(x for x in fs if x not in REQUIRED and not OPTIONAL.match(x))
        if bad:
            die("%s: RAMB18 configuration not modelled (refused): %s" % (sn, bad))
        inv = {p: 0 if ("ZINV_%s" % p) in fs else 1 for p in INVPINS}
        conn, how = {}, {}
        logical = {}
        for p in INVPINS + ("REGCEAREGCE", "REGCEB") + tuple("WEBWE%d" % i for i in range(8)):
            k, tl = walk_pin(tile, y, p, "%s %s" % (sn, p))
            conn[p] = k
            if "const" in k:
                b = int(bool(k["const"]))
                logical[p] = b ^ (inv.get(p, 0) if not tl else 0)
                how[p] = "%s%d%s" % ("tile-" if tl else "fabric-", int(bool(k["const"])), ",inv" if inv.get(p, 0) and not tl else "")
        if "const" in conn["CLKARDCLK"]:
            die("%s: CLKARDCLK is a constant (the RAM never clocks)" % sn)
        for p, want in CTRL1.items():
            if logical.get(p) != want:
                die("%s %s: logical %s (%s), modelled only %d" % (sn, p, logical.get(p, "a net"), how.get(p, conn[p].get("net")), want))
        if "const" not in conn["CLKBWRCLK"]:
            die("%s: port B clocked by %s (port B not modelled)" % (sn, conn["CLKBWRCLK"].get("net")))
        for p in DATA:
            k, tl = walk_pin(tile, y, p, "%s %s" % (sn, p))
            conn[p] = k
        rd = sorted(reads.get(sn, ()))
        badr = [p for p in rd if not re.match(r"^DOADO\d+$|^DOPADOP\d$", p)]
        if badr:
            die("%s: the fabric reads %s (only DOADO / DOPADOP modelled)" % (sn, badr))
        v = vcfg[(tile, y)]
        zinit = v.get("ZINIT_A", 0)
        init_do = (~zinit) & 0x3FFFF        # ZINIT_A[17:0], inverted: the output latch's power-up value (DO 15:0, DOP 17:16)
        mem = [0] * 1024
        for kname, val in v.items():
            m = re.match(r"^INIT_([0-3][0-9A-F])$", kname)
            if m:
                base = int(m.group(1), 16) * 256
                for b in range(256):
                    if (val >> b) & 1:
                        w, bit = divmod(base + b, 16)
                        mem[w] |= 1 << bit
        if any(re.match(r"^INITP_", k_) for k_ in v):
            die("%s: INITP (parity contents) not modelled" % sn)
        cell = {"name": sn, "kind": "ramb18e1", "init": 0, "conn": conn, "inv": [], "outs": {p: "%s/%s" % (sn, p) for p in rd},
                "features": sorted(fs) + ["%s=%x" % kv for kv in sorted(v.items())],
                "ram": {"tile": tile, "tiletype": fab.ttype(tile), "y": y, "how": how, "logical": logical,
                        "init_do": init_do, "mem_nonzero": {str(i): w for i, w in enumerate(mem) if w}, "read": rd,
                        "write_mode": "WRITE_FIRST"}}
        if J is not None:
            jc = jbel.get("%s/RAMB18E1" % sn)
            if jc is None:
                die("%s: no RAMB18E1 at this BEL in the routed json" % sn)
            cn, c = jc
            P = c["parameters"]
            def pint(k_, d=0):
                x = P.get(k_)
                return d if x is None else (int(x, 2) if re.match(r"^[01]+$", str(x)) else int(x))
            if pint("READ_WIDTH_A") != 18 or pint("WRITE_WIDTH_A") != 18 or pint("DOA_REG") != 0 or \
                    P.get("WRITE_MODE_A", "WRITE_FIRST") != "WRITE_FIRST" or P.get("RAM_MODE", "TDP") != "TDP":
                die("%s: json parameters differ from the modelled configuration: %s" % (sn, {k_: P.get(k_) for k_ in
                    ("READ_WIDTH_A", "WRITE_WIDTH_A", "DOA_REG", "WRITE_MODE_A", "RAM_MODE")}))
            for p in logical:
                nets = [jnn.get(b, b) for b in c["connections"].get(p, [])]
                if not nets:
                    continue          # an unconnected json pin: nextpnr's tie, no claim from the json
                if nets[0] in ("$PACKER_GND_NET", "$PACKER_VCC_NET") or nets[0] in ("0", "1"):
                    raw = 1 if nets[0] in ("$PACKER_VCC_NET", "1") else 0
                    jl = raw ^ (pint("IS_%s_INVERTED" % p) if p in INVPINS else 0)
                    if jl != logical[p]:
                        die("%s %s: json logical %d, decoded %d (%s)" % (sn, p, jl, logical[p], how[p]))
            for p in DATA + ["CLKARDCLK"]:
                k = conn[p]
                nets = [jnn.get(b, b) for b in c["connections"].get(p, [])]
                jn = nets[0] if nets else None
                if "const" in k:
                    continue
                if jn is None:
                    die("%s %s: decoded %s, json pin unconnected" % (sn, p, k.get("net")))
                dn = k["net"]
                if net_map.setdefault(jn, dn) != dn or net_map_r.setdefault(dn, jn) != jn:
                    die("%s %s: json net %s <-> decoded %s not one-to-one" % (sn, p, jn, dn))
            for p in rd:
                bits = c["connections"].get(p, [])
                if bits:
                    jn = jnn.get(bits[0], bits[0]); dn = "%s/%s" % (sn, p)
                    if net_map.setdefault(jn, dn) != dn or net_map_r.setdefault(dn, jn) != jn:
                        die("%s %s: json net %s <-> decoded %s not one-to-one" % (sn, p, jn, dn))
            cell["ram"]["json_cell"] = cn
        cells_out.append(cell)
        report.append("%s %s.RAMB18_Y%d: port A x18 WRITE_FIRST, clock %s, reads %d DOADO / %d DOPADOP, WE %s, "
                      "init words %d, controls %s" % (sn, tile, y, conn["CLKARDCLK"].get("net"),
                      sum(1 for p in rd if p.startswith("DOADO")), sum(1 for p in rd if p.startswith("DOPADOP")),
                      [conn[w].get("net", conn[w].get("const")) for w in ("WEA0", "WEA1")], len(cell["ram"]["mem_nonzero"]),
                      ",".join("%s=%s" % (p, how[p]) for p in sorted(how))))
    for s in reads:
        if s not in {c["name"] for c in cells_out}:
            die("%s is read but has no decoded configuration" % s)
    D["cells"] += cells_out
    D["census"]["ramb18e1"] = len(cells_out)
    D["bram_report"] = report
    if J is not None:
        D["bram_json_check"] = "%d RAMB18 sites agree with %s (configuration, constant controls, %d nets one-to-one)" % (
            len(cells_out), os.path.basename(a.routed), len(net_map))
    with open(a.json, "w") as f:
        json.dump(D, f, indent=0, sort_keys=True)
    for r in report:
        print("decode_bram: " + r, file=sys.stderr)
    if J is not None:
        print("decode_bram: " + D["bram_json_check"], file=sys.stderr)


def DD_src_key(fab, src, what, lut_cells, driven, feats):
    """decode_dsp's src_key (local to its main()): the same naming of a walked fabric source."""
    _, tile, site, pin = src
    sn = fab.site_name(tile, site)
    if src[0] == "site":
        return {"net": "%s/%s" % (sn, pin)}
    if src[0] != "slice":
        die("%s: driven by %s %s (not modelled)" % (what, src[0], sn))
    if pin in "ABCD":
        if "%s.%sLUT" % (sn, pin) not in lut_cells:
            die("%s: reads an unused LUT %s.%s (zero read)" % (what, sn, pin))
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
        net = "%s.%s" % (sn, key)
    else:
        die("%s: unmodelled slice source %s" % (what, pin))
    if net not in driven:
        die("%s: reads %s, which no decoded cell drives" % (what, net))
    return {"net": net}


if __name__ == "__main__":
    main()
