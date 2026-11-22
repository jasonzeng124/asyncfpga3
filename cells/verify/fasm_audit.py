#!/usr/bin/env python3
"""Does the FASM say what the netlist says?  The bitstream seam, checked.

    python3 verify/fasm_audit.py ROUTED_JSON FASM [--synth SYNTH_JSON]

Three of this project's four worst bugs were in nextpnr's FASM writer: the
JSON, the SDF and every simulation of them were correct, and only the bits
were wrong (patches/README.md).  cells/verify/toolchain.sh guards against an
unpatched binary by looking for a string literal each patch adds -- which
says the patch is present, not that the bits are right, and for
nextpnr-xilinx-dsp-areg.patch the literal it looks for ("ZAREG_2_ACASCREG_1")
is in the UNPATCHED source too (fasm.cc at bfdeaf7c, line 5066), so that
fingerprint cannot fail.  This reads the FASM back and checks it against the
netlist, so it fails on the defect itself, whatever binary produced it:

  LUT    every occupied LUT site's INIT[63:0] equals the function of the
         netlist cell(s) on it, re-encoded from X_ORIG_PORT_A<n> by NAME.
         nextpnr-xilinx-lut-pinmap.patch: X_ORIG_PORT_A<n> is written both
         'I0 I3' and run together 'I2I0 '; the unpatched writer split on ' ',
         looked 'I2I0' up with operator[] and got I0, and 131 LUTs of gcd_hw
         got a truth table that is not their function.
  ZAREG  each DSP48E1's ZAREG_2_ACASCREG_1 / ZBREG_2_BCASCREG_1 bit is present
         exactly when NOT (AREG == 2 and ACASCREG == 1) -- prjxray's
         fuzzers/100-dsp-mskpat/generate.py defines the feature as that
         conjunction.  nextpnr-xilinx-dsp-areg.patch: the unpatched writer
         used !ACASCREG, so AREG=1 (and AREG=2/ACASCREG=2) wrote no bit.
  CONST  each DSP48E1 pin that has no route into the site (prjxray gives it
         only <PIN>.DSP_GND_* / <PIN>.DSP_VCC_* tile bits) carries exactly
         one such bit, with the LOGICAL value the SYNTHESIS netlist gives it
         (connection XOR IS_<pin>_INVERTED).  nextpnr-xilinx-dsp-constpins.patch:
         INMODE0..4, ALUMODE2/3 and OPMODE6 got no bit at all, came up as
         the tile default, and INMODE[1]=1 gated the multiplier's A to zero.
         The truth comes from the pre-pack yosys JSON, because the packer
         that dropped those pins is the thing under test.

Exit 0 when every checked item agrees, 1 on any disagreement, 2 when the
check could not be made (missing input, a cell it cannot locate in the
tilegrid or the synthesis netlist, a vacuous run under --min-*).  2 is NOT a
pass: flow.sh and build_hw.sh stop on any nonzero exit, because an audit
that could not run has said nothing about the bitstream.  Prints
how many items of each kind it checked, so a vacuous pass is visible: a
design with no multi-name LUT pin does not exercise the pinmap bug, and the
gate that wants that (verify/fasm/check.sh) asserts the count.
"""
import argparse
import json
import os
import re
import sys

DB = os.path.join(os.environ.get("TC", os.path.expanduser("~/dev2/lib/fpgatoolchain")),
                  "openxc7/share/nextpnr/prjxray-db/zynq7")
PART = "xc7z010"

RE_NAME = re.compile(r"I(\d+)")
RE_BEL = re.compile(r"^(SLICE_X\d+Y\d+)/([A-D])([56])LUT$")
RE_VEC = re.compile(r"^(\S+)\[(\d+):(\d+)\]\s*=\s*(\d+)'b([01]+)$")


# ---------------------------------------------------------------- the FASM

def read_fasm(path):
    """FASM -> (set of single-bit features, {vector feature: int value})."""
    feats, vecs = set(), {}
    with open(path) as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if not line:
                continue
            m = RE_VEC.match(line)
            if m:
                name, hi, lo, _w, bits = m.groups()
                if int(lo) != 0 or len(bits) != int(hi) + 1:
                    raise SystemExit("fasm_audit: cannot read %r" % line)
                vecs[name] = int(bits, 2)
            elif "=" in line:
                name, val = (s.strip() for s in line.split("=", 1))
                if val not in ("1", "1'b1"):
                    raise SystemExit("fasm_audit: cannot read %r" % line)
                feats.add(name)
            else:
                feats.add(line)
    return feats, vecs


# ------------------------------------------------- where a site is in FASM

def load_sites(db=DB, part=PART):
    """site name -> (tile name, index of the site within its tile, tile type)."""
    with open(os.path.join(db, part, "tilegrid.json")) as f:
        grid = json.load(f)
    out = {}
    for tile, t in grid.items():
        sites = t.get("sites", {})
        if not sites:
            continue

        def key(s):
            m = re.search(r"_X(\d+)Y(\d+)$", s)
            return (int(m.group(1)), int(m.group(2))) if m else (0, 0)
        # SLICEL and SLICEM share one numbering (X0 = the lower X); every
        # other kind (DSP48E1, TIEOFF, ...) is numbered on its own.
        def group(k):
            return "SLICE" if k.startswith("SLICE") else k
        for kind in set(map(group, sites.values())):
            same = sorted((s for s, k in sites.items() if group(k) == kind), key=key)
            for i, s in enumerate(same):
                out[s] = (tile, i, t["type"])
    return out


def slice_prefix(site, sites):
    tile, half, ttype = sites[site]
    is_m = ttype.startswith("CLBLM")
    name = ("SLICEM_X0" if is_m else "SLICEL_X0") if half == 0 else "SLICEL_X1"
    return "%s.%s" % (tile, name)


# ------------------------------------------------------------------- LUTs

def lut_names(attrs, k):
    """Logical inputs on physical pin A<k+1>, matched by NAME (the fix)."""
    return [int(n) for n in RE_NAME.findall(attrs.get("X_ORIG_PORT_A%d" % (k + 1), ""))]


def lut_init(cell):
    s = cell["parameters"].get("INIT", "")
    return int(s, 2) if s else 0, len(s)


def expected_lut_bits(lut6, lut5, names=lut_names):
    """fasm.cc get_lut_init() as patched: 64 physical bits for one LUT site.

    lut6/lut5 are routed-JSON cells (or None).  A fractured pair splits the
    table: the 5LUT owns physical bits 0..31, the 6LUT bits 32..63.  Logical
    input I<n> is address bit n of the cell's own INIT (yosys order, I0 = LSB);
    an address past the end of INIT reads 0, as Property::extract pads.
    `names` is the parser under test -- the negative controls swap it."""
    bits = 0
    for which, lut in (("6", lut6), ("5", lut5)):
        if lut is None:
            continue
        init, width = lut_init(lut)
        p2l = [names(lut["attributes"], k) for k in range(6)]
        lo, hi = 0, 64
        if lut6 is not None and lut5 is not None:
            lo, hi = (32, 64) if which == "6" else (0, 32)
        for j in range(lo, hi):
            log = 0
            for k in range(6):
                if (j >> k) & 1:
                    for n in p2l[k]:
                        log |= 1 << n
            if log < width and (init >> log) & 1:
                bits |= 1 << j
    return bits


def check_luts(cells, fasm_vecs, sites, names=lut_names):
    """-> (n_sites, n_multi_pins, n_runtogether, [mismatch strings])."""
    by_site = {}
    n_multi = n_run = 0
    for cname, c in cells.items():
        if c["type"] != "SLICE_LUTX":
            continue
        bel = c["attributes"].get("NEXTPNR_BEL", "")
        m = RE_BEL.match(bel)
        if not m:
            raise LookupError("LUT %s has no slice LUT BEL (%r)" % (cname, bel))
        site, letter, size = m.groups()
        slot = by_site.setdefault((site, letter), {})
        if size in slot:
            raise LookupError("two cells on %s" % bel)
        slot[size] = c
        for k in range(6):
            v = c["attributes"].get("X_ORIG_PORT_A%d" % (k + 1), "")
            if len(RE_NAME.findall(v)) > 1:
                n_multi += 1
                if " " not in v.strip():
                    n_run += 1
    bad = []
    for (site, letter), slot in sorted(by_site.items()):
        if site not in sites:
            raise LookupError("site %s is not in the tilegrid" % site)
        feat = "%s.%sLUT.INIT" % (slice_prefix(site, sites), letter)
        want = expected_lut_bits(slot.get("6"), slot.get("5"), names)
        got = fasm_vecs.get(feat)
        if got is None:
            bad.append("%s: no INIT in the FASM (cells %s)" % (feat, sorted(slot)))
        elif got != want:
            cn = [n for n, c in cells.items() if any(c is x for x in slot.values())]
            bad.append("%s: FASM %016x, netlist %016x  (%s)" % (feat, got, want, ", ".join(cn)))
    return len(by_site), n_multi, n_run, bad


# ------------------------------------------------------------------- DSPs

def const_only_pins(db=DB):
    """DSP48E1 pins prjxray reaches only through a tile bit (DSP_GND/DSP_VCC)."""
    pins = set()
    with open(os.path.join(db, "segbits_dsp_l.db")) as f:
        for line in f:
            m = re.match(r"DSP_L\.DSP_0_([A-Z0-9]+)\.DSP_(GND|VCC)_L\s", line)
            if m:
                pins.add(m.group(1))
    return pins


def pint(params, name, default):
    v = params.get(name)
    if v is None:
        return default
    if isinstance(v, int):
        return v
    v = v.strip()
    if re.fullmatch(r"[01xz]+", v):
        return int(v.replace("x", "0").replace("z", "0"), 2)
    return int(v)


def synth_pin_value(sc, pin):
    """Logical constant on a const-only pin, from the yosys netlist, or None
    when it is not a constant (which a const-only pin cannot route)."""
    m = re.fullmatch(r"([A-Z]+?)(\d*)", pin)
    base, idx = m.group(1), m.group(2)
    conns = sc["connections"]
    if base in conns and idx != "" and len(conns[base]) > 1:
        bit = conns[base][int(idx)]
        inv = (pint(sc["parameters"], "IS_%s_INVERTED" % base, 0) >> int(idx)) & 1
    elif pin in conns:
        bit = conns[pin][0]
        inv = pint(sc["parameters"], "IS_%s_INVERTED" % pin, 0) & 1
    else:
        return "unconnected"
    if bit not in ("0", "1"):
        return None
    return int(bit) ^ inv


def check_dsps(cells, synth_cells, feats, sites, const_pins):
    """-> (n_dsps, n_zreg_checked, n_const_checked, [mismatch strings])."""
    bad = []
    n = nz = nc = 0
    for cname, c in sorted(cells.items()):
        if not c["type"].startswith("DSP48E1"):
            continue
        n += 1
        bel = c["attributes"].get("NEXTPNR_BEL", "")
        site = bel.split("/")[0]
        if site not in sites:
            raise LookupError("DSP %s on %r, not in the tilegrid" % (cname, bel))
        tile, idx, ttype = sites[site]
        side = "L" if ttype == "DSP_L" else "R"
        dsp = "DSP_%d" % idx
        p = c["parameters"]
        for X in "AB":
            reg = pint(p, X + "REG", 1)
            cas = pint(p, X + "CASCREG", 1)
            want = not (reg == 2 and cas == 1)
            f = "%s.DSP48.%s.Z%sREG_2_%sCASCREG_1" % (tile, dsp, X, X)
            nz += 1
            if (f in feats) != want:
                bad.append("%s: %s %s, but %sREG=%d %sCASCREG=%d wants it %s"
                           % (cname, f, "present" if f in feats else "absent",
                              X, reg, X, cas, "present" if want else "absent"))
        if synth_cells is None:
            continue
        sc = synth_cells.get(cname)    # LookupError when it cannot be resolved
        for pin in sorted(const_pins):
            v = synth_pin_value(sc, pin)
            if v == "unconnected":
                continue
            fg = "%s.%s_%s.DSP_GND_%s" % (tile, dsp, pin, side)
            fv = "%s.%s_%s.DSP_VCC_%s" % (tile, dsp, pin, side)
            have = [x for x in (fg, fv) if x in feats]
            if v is None:
                bad.append("%s: %s has no route into the site but is not a constant" % (cname, pin))
                continue
            nc += 1
            want = fv if v else fg
            if have != [want]:
                bad.append("%s: %s is logically %d, FASM has %s"
                           % (cname, pin, v, have or "no bit (tile default)"))
    return n, nz, nc, bad


# ------------------------------------------- what an unpatched writer wrote
#
# Negative controls.  There is no unpatched nextpnr binary to run, so each
# function below re-writes a GOOD FASM the way the unpatched fasm.cc /
# pack_dsp_xc7.cc at bfdeaf7c would have written it, from the same routed
# netlist, line for line from that source.  The audit must FAIL on every one
# of them; verify/fasm/check.sh and test_fasm_audit.py both insist on it.

UNPATCHED = ("pinmap", "areg", "constpins-packer", "constpins-inv")


def unpatched_lut_names(attrs, k):
    """fasm.cc before nextpnr-xilinx-lut-pinmap.patch: boost::split on ' ',
    then log_to_bit[token] through operator[], which inserts 0 for a name it
    does not know -- so 'I2I0' and the empty token after a trailing space
    both read as I0."""
    v = attrs.get("X_ORIG_PORT_A%d" % (k + 1))
    if v is None:
        return []
    return [int(t[1:]) if re.fullmatch(r"I\d+", t) else 0 for t in v.split(" ")]


def write_unpatched(kind, routed, fasm_in, fasm_out, db=DB):
    """Copy fasm_in to fasm_out as the unpatched writer `kind` would have
    written it.  Returns the number of FASM lines that changed."""
    assert kind in UNPATCHED, kind
    cells = top_cells(routed)
    sites = load_sites(db)
    lines = open(fasm_in).read().splitlines()
    out, changed = [], 0
    drop, add = set(), []
    if kind == "pinmap":
        luts = {}
        for c in cells.values():
            m = RE_BEL.match(c["attributes"].get("NEXTPNR_BEL", "")) if c["type"] == "SLICE_LUTX" else None
            if m:
                luts.setdefault((m.group(1), m.group(2)), {})[m.group(3)] = c
        repl = {}
        for (site, letter), slot in luts.items():
            feat = "%s.%sLUT.INIT[63:0]" % (slice_prefix(site, sites), letter)
            repl[feat] = expected_lut_bits(slot.get("6"), slot.get("5"), unpatched_lut_names)
        for ln in lines:
            name = ln.split("=", 1)[0].strip()
            if name in repl:
                new = "%s = 64'b%s" % (name, format(repl[name], "064b"))
                changed += new != ln
                ln = new
            out.append(ln)
        lines = out
    else:
        for cname, c in cells.items():
            if not c["type"].startswith("DSP48E1"):
                continue
            tile, idx, ttype = sites[c["attributes"]["NEXTPNR_BEL"].split("/")[0]]
            side = "L" if ttype == "DSP_L" else "R"
            dsp = "DSP_%d" % idx
            p = c["parameters"]
            if kind == "areg":
                # write_bit("ZAREG_2_ACASCREG_1", !bool_or_default(ACASCREG))
                for X in "AB":
                    f = "%s.DSP48.%s.Z%sREG_2_%sCASCREG_1" % (tile, dsp, X, X)
                    drop.add(f)
                    if pint(p, X + "CASCREG", 1) == 0:
                        add.append(f)
                continue
            for net in ("GND", "VCC"):
                for pin in c["attributes"].get("DSP_%s_PINS" % net, "").split():
                    m = re.fullmatch(r"([A-Z]+?)(\d*)", pin)
                    base, i = m.group(1), m.group(2)
                    if kind == "constpins-packer":
                        # INMODE, ALUMODE2/3 and OPMODE6 never reached the
                        # const-pin list, so no bit was written for them.
                        if base == "INMODE" or pin in ("ALUMODE2", "ALUMODE3", "OPMODE6"):
                            for n2 in ("GND", "VCC"):
                                drop.add("%s.%s_%s.DSP_%s_%s" % (tile, dsp, pin, n2, side))
                    else:
                        # erase_all(digits) looked up IS_INMODE_INVERTED, which
                        # does not exist, so a bussed pin never got flipped.
                        inv_true = (pint(p, "IS_%s_INVERTED" % pin, 0) or
                                    (i != "" and pint(p, "IS_%s[%s]_INVERTED" % (base, i), 0)))
                        inv_bug = pint(p, "IS_%s_INVERTED" % base, 0) & 1 if i == "" else 0
                        if bool(inv_true) != bool(inv_bug):
                            good = net if not inv_true else ("VCC" if net == "GND" else "GND")
                            bad = net if not inv_bug else ("VCC" if net == "GND" else "GND")
                            drop.add("%s.%s_%s.DSP_%s_%s" % (tile, dsp, pin, good, side))
                            add.append("%s.%s_%s.DSP_%s_%s" % (tile, dsp, pin, bad, side))
        for ln in lines:
            if ln.strip() in drop:
                changed += 1
                continue
            out.append(ln)
        present = set(ln.strip() for ln in out)
        for f in add:
            if f not in present:
                out.append(f)
                changed += 1
        # a feature dropped and re-added unchanged is not a change
        changed -= sum(1 for f in add if f in drop and f in set(l.strip() for l in lines))
        lines = out
    with open(fasm_out, "w") as f:
        f.write("\n".join(lines) + "\n")
    return changed


# ------------------------------------------------------------------- main

class SynthCells:
    """Cells of a yosys JSON by their FLATTENED name, as nextpnr reports them.

    flow.sh's synthesis flattens, so a cell is usually a top-level name; a
    hierarchical netlist (fusion_bench's, for one) keeps `uut.umuli1.<cell>`
    as instance `uut` of the top, instance `umuli1` of that module, then the
    cell.  Cell names contain dots themselves, so at each level the whole
    remaining name is tried as a cell first, then each dotted prefix as an
    instance of a module this JSON defines.  Strict: a name that resolves to
    nothing, or to more than one cell, is a LookupError -- never a skip."""

    def __init__(self, path):
        with open(path) as f:
            self.mods = json.load(f)["modules"]
        tops = [n for n, m in self.mods.items()
                if "1" in str(m.get("attributes", {}).get("top", ""))]
        if len(tops) != 1:
            if len(self.mods) != 1:
                raise LookupError("%s: cannot tell which module is the top" % path)
            tops = list(self.mods)
        self.top = tops[0]

    def _is_inst(self, cell):
        """An instance of a module this netlist DEFINES -- not a primitive
        whose blackbox (cells_sim.v read -lib) also sits in the JSON."""
        m = self.mods.get(cell["type"])
        return m is not None and "1" not in str(m.get("attributes", {}).get("blackbox", "")) \
            and bool(m.get("cells"))

    def _find(self, mod, name):
        cells = self.mods[mod]["cells"]
        hits = []
        if name in cells and not self._is_inst(cells[name]):
            hits.append(cells[name])
        parts = name.split(".")
        for i in range(1, len(parts)):
            inst = ".".join(parts[:i])
            c = cells.get(inst)
            if c is not None and self._is_inst(c):
                hits.extend(self._find(c["type"], ".".join(parts[i:])))
        return hits

    def get(self, name):
        hits = self._find(self.top, name)
        if len(hits) != 1:
            raise LookupError("cell %s %s in the synthesis netlist" % (
                name, "is not" if not hits else "resolves to %d cells" % len(hits)))
        return hits[0]


def top_cells(path):
    with open(path) as f:
        mods = json.load(f)["modules"]
    tops = [m for m in mods.values() if "1" in str(m.get("attributes", {}).get("top", ""))]
    mod = tops[0] if tops else (list(mods.values())[0] if len(mods) == 1 else None)
    if mod is None:
        raise LookupError("%s: cannot tell which module is the top" % path)
    return mod["cells"]


def audit(routed, fasm, synth=None, db=DB, names=lut_names, out=sys.stdout):
    """-> (exit code, stats dict)."""
    cells = top_cells(routed)
    feats, vecs = read_fasm(fasm)
    sites = load_sites(db)
    nl, nmulti, nrun, bad_l = check_luts(cells, vecs, sites, names)
    synth_cells = SynthCells(synth) if synth else None
    nd, nz, nc, bad_d = check_dsps(cells, synth_cells, feats, sites, const_only_pins(db))
    print("fasm_audit: %d LUT sites (%d multi-name pins, %d run together), "
          "%d DSP48E1 (%d Z*REG bits, %d const-only pins%s)"
          % (nl, nmulti, nrun, nd, nz, nc, "" if synth_cells is not None or not nd
             else "; const pins NOT checked, no --synth"), file=out)
    for b in bad_l + bad_d:
        print("  MISMATCH " + b, file=out)
    stats = dict(lut_sites=nl, multi=nmulti, runtogether=nrun, dsps=nd,
                 zreg=nz, const=nc, bad=len(bad_l) + len(bad_d))
    if bad_l or bad_d:
        print("fasm_audit FAIL: %d LUT site(s), %d DSP item(s) where the bitstream "
              "disagrees with the netlist" % (len(bad_l), len(bad_d)), file=out)
        return 1, stats
    print("fasm_audit PASS", file=out)
    return 0, stats


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("routed")
    ap.add_argument("fasm")
    ap.add_argument("--synth", help="pre-pack yosys JSON (needed for the DSP const-pin check)")
    ap.add_argument("--db", default=DB)
    ap.add_argument("--min-runtogether", type=int, default=0,
                    help="fail unless at least this many run-together X_ORIG_PORT pins were checked")
    ap.add_argument("--min-dsp", type=int, default=0,
                    help="fail unless at least this many DSP48E1 were checked")
    ap.add_argument("--write-unpatched", nargs=2, metavar=("KIND", "OUT_FASM"),
                    help="negative control: write the FASM an unpatched nextpnr would "
                         "have written (KIND in %s) and exit" % ", ".join(UNPATCHED))
    a = ap.parse_args()
    if a.write_unpatched:
        n = write_unpatched(a.write_unpatched[0], a.routed, a.fasm, a.write_unpatched[1], a.db)
        print("fasm_audit: %s: %d FASM line(s) differ from what the patched writer wrote"
              % (a.write_unpatched[0], n))
        return 0
    for p in (a.routed, a.fasm) + ((a.synth,) if a.synth else ()):
        if not os.path.exists(p):
            print("fasm_audit: missing %s" % p)
            return 2
    try:
        rc, st = audit(a.routed, a.fasm, a.synth, a.db)
    except LookupError as e:
        print("fasm_audit: cannot check: %s" % e)
        return 2
    if st["runtogether"] < a.min_runtogether or st["dsps"] < a.min_dsp:
        print("fasm_audit: VACUOUS -- wanted >= %d run-together pins and >= %d DSPs"
              % (a.min_runtogether, a.min_dsp))
        return 2
    return rc


if __name__ == "__main__":
    sys.exit(main())
