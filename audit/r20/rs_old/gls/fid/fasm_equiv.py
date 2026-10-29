#!/usr/bin/env python3
"""
fasm_equiv.py -- is the netlist the board runs the netlist nextpnr meant?

    fasm_equiv.py ROUTED.json FASM_ROUTED.json [ROUTES.tsv] [--max N]

ROUTED.json is nextpnr's routed design (what gls/gen.py simulates);
FASM_ROUTED.json and ROUTES.tsv come from fasm2net.py (the bits).  Both are
bel-level, so everything is compared by bel name:

  1. cell set      same bels, same cell type
  2. config        FF INIT and set/reset sense, CARRY4 carry-in, BUFG inversions
  3. connectivity  every input pin: same driver (bel/pin, or the same constant).
                   The two LUT bels of one position (A6LUT/A5LUT) share six
                   physical pins, so pins are compared per LUT POSITION.
                   A LUT pin the JSON ties to one constant and the bits to the
                   other (nextpnr ties it to GND but never routes it, so the
                   IMUX reads VCC through its default ppip) is HARMLESS, and
                   counted as such, iff the bits' LUT function does not read
                   that pin (both halves, the other pins at their own drivers);
                   otherwise it is a hard difference.
  4. LUT function  every LUT, evaluated over every assignment of the distinct
                   nets on its pins, each side with ITS OWN pin map and constants
                   -- JSON through gen.py's X_ORIG_PORT expansion (the logical
                   function), FASM through the physical INIT.  This is "same
                   function after pin permutation", and is where the lut-pinmap
                   bug lives.
  5. routing       per net, the set of pips as (src node, dst node) pairs: the
                   JSON's ROUTING attribute against the pips the bits enable.

Exit status 0 only if every check is clean.  Nothing is skipped silently: an
item a check cannot compare is counted as such.
"""
import argparse, collections, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))          # cells/gls -> gen.py
sys.path.insert(0, HERE)
import gen                                          # noqa: E402  (expand_lut_init, TIE)
import fasm2net                                     # noqa: E402

CONST = {"PSEUDO_VCC": 1, "PSEUDO_GND": 0}


def load(path):
    top = json.load(open(path))["modules"]["top"]
    cells = top["cells"]
    drv = {}
    for cn, c in cells.items():
        for p, bl in c["connections"].items():
            if c.get("port_directions", {}).get(p) == "output" and bl:
                drv[bl[0]] = (cn, p)
    return top, cells, drv


def bel(c, cn):
    return c["attributes"].get("NEXTPNR_BEL", cn)


def lutpos(b):
    """SLICE_X1Y2/A6LUT -> SLICE_X1Y2/A (the physical LUT position)."""
    m = re.match(r"(.*)/([A-D])[56]LUT$", b)
    return "%s/%s" % m.groups() if m else None


def pin_drivers(cells, drv, gen_ties):
    """-> {(bel or lut position, pin): driver} where driver is
    ('bel', bel, pin) | ('const', v) | ('tie', v) (unconnected: gen.py's TIE)."""
    out = {}
    belof = {cn: bel(c, cn) for cn, c in cells.items()}
    for cn, c in cells.items():
        t = c["type"]
        if t in CONST or t == "PAD":
            continue            # a pad is the port itself; its net has no driver on either side
        b = belof[cn]
        key = lutpos(b) or b
        if t == gen.DSP_T:
            continue            # compared in section 2b, pins the model reads only
        for p, bl in c["connections"].items():
            if c.get("port_directions", {}).get(p) not in ("input", "inout"):
                continue
            if bl:
                d = drv.get(bl[0])
                if d is None:
                    v = ("undriven",)
                elif cells[d[0]]["type"] in CONST:
                    v = ("const", CONST[cells[d[0]]["type"]])
                elif cells[d[0]]["type"] == "PAD":
                    v = ("undriven",)       # fasm2net names the pad as the driver of its own net
                else:
                    v = ("bel", belof[d[0]], d[1])
            else:
                continue
            k = (key, p)
            if k in out and out[k] != v:
                out[k] = ("CONFLICT", out[k], v)
            else:
                out[k] = v
    return out


def lut_eval_inputs(cn, c, pd, gen_ties):
    """Physical pin -> driver for one LUT cell, unconnected pins at gen's TIE."""
    b = bel(c, cn)
    key = lutpos(b)
    m = {}
    for i in range(1, 7):
        d = pd.get((key, "A%d" % i))
        if d is None:
            d = ("tie", gen_ties.get(("SLICE_LUTX", "A%d" % i), 0))
        m["A%d" % i] = d
    return m


def lut_table(c, out_port):
    """Physical truth table, A1 = bit 0 (gen.py's expansion of the JSON;
    for fasm2net's cells X_ORIG_PORT is the identity, so this is the INIT)."""
    return gen.expand_lut_init(c["parameters"].get("INIT", "0"), c["attributes"], out_port)


def lut_reads_pin(pos, pin, vals, cells_by_bel, pd):
    """Does the bits' LUT function at LUT position `pos` (both its 6LUT and
    5LUT bels) change when physical pin `pin` moves between the constants in
    `vals`?  The other pins take their own bits-side drivers: constants fixed,
    every distinct live net free over 0/1.  -> (reads?, which bels looked at)."""
    site, L = pos.rsplit("/", 1)
    i = int(pin[1]) - 1
    seen = []
    for b6 in ("6", "5"):
        b = "%s/%s%sLUT" % (site, L, b6)
        if b not in cells_by_bel:
            continue
        cn, c = cells_by_bel[b]
        out = "O6" if b6 == "6" else "O5"
        npins = 6 if out == "O6" else 5
        seen.append(b)
        if i >= npins:
            continue                    # A6 is not an input of the O5 half
        t = lut_table(c, out)
        m = lut_eval_inputs(cn, c, pd, gen.TIE)
        var = sorted({d for k2, d in list(m.items())[:npins]
                      if k2 != pin and d[0] not in ("const", "tie")}, key=str)
        for v in range(1 << len(var)):
            env = {d: (v >> j) & 1 for j, d in enumerate(var)}
            outs = set()
            for pv in vals:
                x = 0
                for j in range(npins):
                    d = m["A%d" % (j + 1)]
                    bitv = pv if j == i else (d[1] if d[0] in ("const", "tie") else env[d])
                    x |= bitv << j
                outs.add((t >> x) & 1)
            if len(outs) > 1:
                return True, seen
    return False, seen


HARMLESS_CONST = ("HARMLESS: LUT pin on a different constant in the routed JSON than on the board "
                  "(an IMUX nextpnr tied to GND but never routed reads VCC through its default "
                  "ppip), and the bits' LUT function does not read that pin")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("routed")
    ap.add_argument("fasm_routed")
    ap.add_argument("routes", nargs="?")
    ap.add_argument("stubs", nargs="?")
    ap.add_argument("--max", type=int, default=12)
    ap.add_argument("--out", help="also write the report here")
    a = ap.parse_args()
    R = []
    say = R.append
    bad = collections.Counter()
    ex = collections.defaultdict(list)

    def flag(kind, e):
        bad[kind] += 1
        if len(ex[kind]) < a.max:
            ex[kind].append(e)

    jt, jc, jd = load(a.routed)
    ft, fc, fd = load(a.fasm_routed)
    jb = {bel(c, cn): (cn, c) for cn, c in jc.items() if c["type"] not in CONST}
    fb = {bel(c, cn): (cn, c) for cn, c in fc.items() if c["type"] not in CONST}

    # ---- 1. cells
    only_j = sorted(set(jb) - set(fb))
    only_f = sorted(set(fb) - set(jb))
    say("1. CELLS  routed JSON %d bels, bitstream %d bels, common %d"
        % (len(jb), len(fb), len(set(jb) & set(fb))))
    for b in only_j:
        cn, c = jb[b]
        loads = sum(1 for x in jc.values() for p, bl in x["connections"].items()
                    if x.get("port_directions", {}).get(p) == "input" and bl and
                    any(bl[0] == c["connections"].get(o, [None])[0]
                        for o, d in c["port_directions"].items() if d == "output"))
        flag("cell in routed JSON, not configured by the bits%s" % (" (it has NO loads)" if loads == 0 else " (HAS LOADS)"),
             "%s %s %s" % (b, c["type"], cn[:80]))
    for b in only_f:
        flag("cell configured by the bits, absent from routed JSON", "%s %s" % (b, fb[b][1]["type"]))
    for b in sorted(set(jb) & set(fb)):
        if jb[b][1]["type"] != fb[b][1]["type"]:
            flag("cell type differs", "%s %s vs %s" % (b, jb[b][1]["type"], fb[b][1]["type"]))

    # ---- 2. config
    for b in sorted(set(jb) & set(fb)):
        (jn, j), (fn, f) = jb[b], fb[b]
        t = j["type"]
        if t == "SLICE_FFX":
            jl = j["attributes"].get("X_ORIG_TYPE") in ("LDCE", "LDPE")
            fl = f["attributes"].get("X_ORIG_TYPE") in ("LDCE", "LDPE")
            if jl != fl:
                flag("FF/LATCH MODE DIFFERS", "%s json %s bits %s" % (
                    b, j["attributes"].get("X_ORIG_TYPE"), f["attributes"].get("X_ORIG_TYPE")))
            elif jl:
                ginv = lambda c: int(str(c["parameters"].get("IS_CLK_INVERTED", "0")) or "0", 2) & 1
                if ginv(j) != ginv(f):
                    flag("LATCH GATE SENSE DIFFERS", "%s json IS_CLK_INVERTED=%d bits %d" % (b, ginv(j), ginv(f)))
                if j["attributes"]["X_ORIG_TYPE"] != f["attributes"]["X_ORIG_TYPE"]:
                    flag("LATCH CLEAR/PRESET DIFFERS", "%s json %s bits %s" % (
                        b, j["attributes"]["X_ORIG_TYPE"], f["attributes"]["X_ORIG_TYPE"]))
                continue
            ji = int((j["parameters"].get("INIT", "0") or "0").replace("x", "0"), 2)
            fi = int(f["parameters"]["INIT"], 2)
            if ji != fi:
                flag("FF INIT differs", "%s json %d bits %d" % (b, ji, fi))
            js = 1 if j["attributes"].get("X_ORIG_PORT_SR") == "S" else 0
            fs = 1 if f["attributes"].get("X_ORIG_PORT_SR") == "S" else 0
            if js != fs:
                flag("FF set/reset value differs (only matters if SR is used)", "%s json %d bits %d" % (b, js, fs))
        elif t == "CARRY4":
            jp = j["parameters"].get("PRECYINIT_CONST")
            fp = f["parameters"].get("PRECYINIT_CONST")
            jcin = bool(j["connections"].get("CIN"))
            fcin = bool(f["connections"].get("CIN"))
            jax = bool(j["connections"].get("CYINIT"))
            fax = bool(f["connections"].get("CYINIT"))
            if (jp, jcin, jax) != (fp, fcin, fax) and not (jp and not jcin and not jax and fp == jp):
                flag("CARRY4 carry-in source differs", "%s json const=%s cin=%s ax=%s bits const=%s cin=%s ax=%s"
                     % (b, jp, jcin, jax, fp, fcin, fax))
        elif t in ("BUFGCTRL", "BSCAN"):
            def norm(d):
                o = {}
                for k, v in d.items():
                    iv = int(v, 2) if isinstance(v, str) and v and set(v) <= set("01") else v
                    if iv:
                        o[k] = iv
                return o
            if norm(j["parameters"]) != norm(f["parameters"]):
                flag("%s parameters differ" % t, "%s json %s bits %s" % (b, j["parameters"], f["parameters"]))

    ncfg = collections.Counter(jb[b][1]["type"] for b in set(jb) & set(fb)
                               if jb[b][1]["type"] in ("SLICE_FFX", "CARRY4", "BUFGCTRL", "BSCAN"))
    say("2. CONFIG  compared %s (FF INIT/set-reset, CARRY4 carry-in, BUFG/BSCAN parameters)"
        % dict(sorted(ncfg.items())))

    # ---- 2b. DSP48E1: the decoded control words and the pins the model reads
    def dsp_words(c, drv, cells):
        netv = {}
        for cn2, c2 in cells.items():
            if c2["type"] in CONST:
                netv[c2["connections"]["Y"][0]] = CONST[c2["type"]]
        params, attrs, conns = c.get("parameters", {}), c.get("attributes", {}), c["connections"]
        vcc = set(attrs.get("DSP_VCC_PINS", "").split())
        gnd = set(attrs.get("DSP_GND_PINS", "").split())

        def pv(k, d=0):
            v = params.get(k)
            if v is None:
                return d
            return int(v, 2) if set(v) <= set("01") else v
        out = {}
        for g, w in (("OPMODE", 7), ("ALUMODE", 4), ("INMODE", 5), ("CARRYINSEL", 3), ("CARRYIN", 0)):
            val = 0
            for i in range(max(w, 1)):
                pin = g if w == 0 else "%s%d" % (g, i)
                bl = conns.get(pin)
                if bl:
                    v = netv.get(bl[0], "live")
                elif pin in vcc:
                    v = 1
                elif pin in gnd:
                    v = 0
                else:
                    v = "none"
                if not isinstance(v, int):
                    out[g] = "%s=%s" % (pin, v)
                    break
                inv = pv("IS_%s_INVERTED" % pin) if w == 0 else pv("IS_%s[%d]_INVERTED" % (g, i))
                val |= (v ^ (int(inv) & 1)) << i
            else:
                out[g] = format(val, "0%db" % max(w, 1))
        for k in ("AREG", "ACASCREG", "BREG", "BCASCREG", "CREG", "DREG", "ADREG", "MREG", "PREG",
                  "INMODEREG", "OPMODEREG", "ALUMODEREG", "CARRYINREG", "CARRYINSELREG",
                  "A_INPUT", "B_INPUT", "USE_DPORT", "USE_SIMD"):
            out[k] = pv(k, "default")
        return out
    n_dsp = 0
    for b in sorted(set(jb) & set(fb)):
        (jn, j), (fn, f) = jb[b], fb[b]
        if j["type"] != gen.DSP_T:
            continue
        n_dsp += 1
        wj, wf = dsp_words(j, jd, jc), dsp_words(f, fd, fc)
        for k in sorted(set(wj) | set(wf)):
            if wj.get(k) != wf.get(k):
                flag("DSP CONFIGURATION DIFFERS", "%s %s: json %s bits %s" % (b, k, wj.get(k), wf.get(k)))
        if "FASM2NET_REFUSED" in f["attributes"]:
            flag("DSP REFUSED by the bit decoder", "%s: %s" % (b, f["attributes"]["FASM2NET_REFUSED"]))
        z = int(wj["OPMODE"], 2) >> 4 if set(str(wj["OPMODE"])) <= set("01") else 0
        cas = wj.get("A_INPUT") == "CASCADE"
        read = ["%s%d" % ("ACIN" if cas else "A", i) for i in range(25)] + ["B%d" % i for i in range(18)] + \
               (["PCIN%d" % i for i in range(48)] if z else [])
        # a registered DSP (S7): its clock and the CE/RST pins its registers read
        read += gen.dsp_regs(j)[1]
        bj = {cn: bel(c, cn) for cn, c in jc.items()}
        bf = {cn: bel(c, cn) for cn, c in fc.items()}
        for p in read:
            def d(c, drv, cells, bm):
                bl = c["connections"].get(p)
                if not bl:
                    return None
                x = drv.get(bl[0])
                if x is None:
                    return ("undriven",)
                if cells[x[0]]["type"] in CONST:
                    return ("const", CONST[cells[x[0]]["type"]])
                return (bm[x[0]], x[1])
            if d(j, jd, jc, bj) != d(f, fd, fc, bf):
                flag("DSP DATA PIN DRIVER DIFFERS", "%s/%s json %s bits %s"
                     % (b, p, d(j, jd, jc, bj), d(f, fd, fc, bf)))
    say("2b. DSP48E1  %d compared: control words (OPMODE/ALUMODE/INMODE/CARRYINSEL/CARRYIN), "
        "register/input parameters, drivers of every data pin the modelled function reads" % n_dsp)

    # ---- 3. connectivity
    jp = pin_drivers(jc, jd, gen.TIE)
    fp = pin_drivers(fc, fd, gen.TIE)
    common_pos = {lutpos(b) or b for b in set(jb) & set(fb)}
    n_same = 0
    for k in sorted(set(jp) | set(fp), key=str):
        if k[0] not in common_pos:
            continue
        a_, b_ = jp.get(k), fp.get(k)
        if a_ == b_:
            n_same += 1
            continue
        if a_ is None and k[0].endswith("/BUFGCTRL") and k[1] == "I1":
            # the I1 input mux's all-zero encoding IS a connection; fasm2net's
            # check_bufg proves I1 is deselected, so it cannot reach O
            flag("BUFGCTRL I1 unconnected in JSON, connected on the board by the "
                 "mux's all-zero default (deselected)", "%s/%s <- %s" % (k[0], k[1], b_))
            continue
        if a_ is None and b_ is not None and b_[0] == "const":
            # unconnected in JSON: gen.py ties it (TIE); the board has a constant.
            t = fb[k[0]][1]["type"] if k[0] in fb else "SLICE_LUTX"
            tie = gen.TIE.get((t, k[1]))
            if tie == b_[1]:
                flag("pin unconnected in routed JSON, same constant (%d) on the board as gen.py's tie"
                     % b_[1], "%s/%s" % k)
            elif t == "SLICE_LUTX":
                flag("LUT pin unconnected in routed JSON, constant %d on the board, gen.py ties %s "
                     "(harmless iff section 4 finds the function identical)" % (b_[1], tie), "%s/%s" % k)
            else:
                flag("PIN TIED DIFFERENTLY: gen.py ties %s, the board has %d" % (tie, b_[1]), "%s/%s" % k)
            continue
        if a_ is None and k[0].endswith("/BUFGCTRL") and k[1] == "I1":
            # the I1 input mux's all-zero encoding IS a connection (to the same
            # IMUX as I0 here); fasm2net's check_bufg proves I1 is deselected
            flag("BUFGCTRL I1 unconnected in JSON, connected on the board by the "
                 "mux's all-zero default (deselected)", "%s/%s <- %s" % (k[0], k[1], b_))
            continue
        if a_ is None:
            flag("pin unconnected in routed JSON, DRIVEN on the board", "%s/%s <- %s" % (k[0], k[1], b_))
            continue
        if b_ is None:
            flag("pin connected in routed JSON, unconnected on the board", "%s/%s <- %s" % (k[0], k[1], a_))
            continue
        if a_[0] == "const" and b_[0] == "const" and re.search(r"/[A-D]$", k[0]) \
                and re.match(r"^A[1-6]$", k[1]):
            reads, seen = lut_reads_pin(k[0], k[1], (a_[1], b_[1]), fb, fp)
            if not reads:
                flag(HARMLESS_CONST, "%s/%s json %d bits %d (%s)" % (k[0], k[1], a_[1], b_[1],
                                                                     ", ".join(seen) or "no LUT"))
            else:
                flag("LUT PIN ON A DIFFERENT CONSTANT AND THE LUT FUNCTION READS IT",
                     "%s/%s json %d bits %d (%s)" % (k[0], k[1], a_[1], b_[1], ", ".join(seen)))
            continue
        flag("DRIVER DIFFERS", "%s/%s json %s bits %s" % (k[0], k[1], a_, b_))
    say("3. CONNECTIVITY  %d pins with the same driver on both sides" % n_same)
    # driver -> sink pairs, as sets
    pairs = lambda pd: {(v, k) for k, v in pd.items() if k[0] in common_pos and v[0] in ("bel", "const")}
    pj, pf = pairs(jp), pairs(fp)
    say("   driver->sink pairs: json %d, bits %d, common %d" % (len(pj), len(pf), len(pj & pf)))

    # ---- 4. LUT functions
    n_lut = n_lut_ok = 0
    for b in sorted(set(jb) & set(fb)):
        (jn, j), (fn, f) = jb[b], fb[b]
        if j["type"] != "SLICE_LUTX":
            continue
        n_lut += 1
        out = "O6" if b.endswith("6LUT") else "O5"
        tj, tf = lut_table(j, out), lut_table(f, out)
        mj = lut_eval_inputs(jn, j, jp, gen.TIE)
        mf = lut_eval_inputs(fn, f, fp, gen.TIE)
        npins = 6 if out == "O6" else 5
        var = sorted({d for m in (mj, mf) for d in list(m.values())[:npins]
                      if d[0] not in ("const", "tie")}, key=str)
        diff = []
        for v in range(1 << len(var)):
            env = {d: (v >> i) & 1 for i, d in enumerate(var)}

            def addr(m):
                x = 0
                for i in range(npins):
                    d = m["A%d" % (i + 1)]
                    bitv = d[1] if d[0] in ("const", "tie") else env[d]
                    x |= bitv << i
                return x
            oj, of = (tj >> addr(mj)) & 1, (tf >> addr(mf)) & 1
            if oj != of:
                diff.append(v)
        if diff:
            flag("LUT FUNCTION DIFFERS", "%s (%s) on %d of %d input assignments"
                 % (b, jn[:60], len(diff), 1 << len(var)))
        else:
            n_lut_ok += 1
    say("4. LUT FUNCTIONS  %d LUTs compared, %d identical over every input assignment" % (n_lut, n_lut_ok))

    # ---- 5. routing, pip by pip
    if a.routes:
        fab = fasm2net.Fabric(fasm2net.DB_ROOT, fasm2net.PART)

        def nd(tw):
            t, _, w = tw.partition("/")
            return fab.node(t, w)
        # JSON: net -> set of (src node, dst node) for every routing pip
        jpips = {}
        jconst = set()
        belof = {cn: bel(c, cn) for cn, c in jc.items()}
        for name, nn in jt["netnames"].items():
            r = nn.get("attributes", {}).get("ROUTING")
            if not r or len(nn["bits"]) != 1:
                continue
            d = jd.get(nn["bits"][0])
            if d is None:
                continue
            key = ("const", CONST[jc[d[0]]["type"]]) if jc[d[0]]["type"] in CONST else (belof[d[0]], d[1])
            f = r.split(";")
            s = jpips.setdefault(key, set())
            for i in range(0, len(f) - 2, 3):
                pip = f[i + 1]
                if not pip or "SITEWIRE" in pip or "SITEPIP" in pip:
                    continue
                src, dst = pip.split("->")
                s.add((nd(src), nd(dst)))
        fpips = collections.defaultdict(set)
        always = set()
        for line in open(a.routes):
            if line.startswith("#"):
                continue
            netn, sink, csrc, pips = (line.rstrip("\n").split("\t") + [""] * 4)[:4]
            if netn.startswith("$const") or netn in ("$PACKER_VCC_NET", "$PACKER_GND_NET"):
                key = ("const", 1 if netn in ("$const1", "$PACKER_VCC_NET") else 0)
                if csrc == "default":
                    continue        # no pip at all: an IMUX left alone reads VCC
            else:
                bb, _, pp = netn.rpartition("/")
                key = (bb, pp)
            for pid in pips.split():
                t, d_, s_ = pid.split(".")
                pr = (fab.node(t, s_), fab.node(t, d_))
                fpips[key].add(pr)
                if s_ in fab.tt(fab.ttype[t])["always"].get(d_, ()):
                    always.add(pr)
        stub = set()
        if a.stubs:
            for line in open(a.stubs):
                if not line.startswith("#"):
                    t, d_, s_ = line.split("\t")[0].split(".")
                    stub.add((fab.node(t, s_), fab.node(t, d_)))
        n_eq = n_ne = n_dead = n_const = 0
        cw = {n for n in range(len(fab.nodes))
              if any(w in fasm2net.CONST_WIRES for _, w in fab.nodes[n])}
        for key in sorted(set(jpips) | set(fpips), key=str):
            A, B = jpips.get(key, set()), fpips.get(key, set())
            if key[0] == "const":
                # A constant is a tie, and section 3 already compared every
                # pin's constant.  Its pips cannot be compared from the bits:
                # an IMUX with no pip set reads VCC through a "default" ppip
                # that has no bits, so the bits do not say which pins nextpnr
                # routed to VCC_WIRE and which it left alone.
                n_const += 1
                continue
            if False:
                # A constant reaches a pin through the tile's VCC_WIRE or, for an
                # IMUX left alone, through its default ppip, which has no bits --
                # the bits cannot say which nextpnr meant.  Compare the pips that
                # do NOT start at a constant wire.
                A = {p for p in A if p[0] not in cw}
                B = {p for p in B if p[0] not in cw}
            dead = (A - B) & stub
            # a json-only pip whose far end feeds nothing but such dead pips is
            # the head of the same dead route (e.g. the always-on CLBLL_L_C ->
            # LOGIC_OUTS ppip, which has no bits and so is never a stub)
            grew = True
            while dead and grew:
                feeds = collections.defaultdict(set)
                for p in A:
                    feeds[p[0]].add(p)
                more = {p for p in (A - B) - dead if feeds[p[1]] and feeds[p[1]] <= dead}
                grew = bool(more)
                dead |= more
            if dead:
                n_dead += 1
                flag("json pips that ARE in the bits but reach no live sink (routing to a dead bel)",
                     "%s: %d pips, e.g. %s" % (key, len(dead), [(fab.node_name(x), fab.node_name(y))
                                                               for x, y in list(dead)[:2]]))
                A = A - dead
            ap = (B - A) & always
            if ap:
                flag("bits-only always-on ppip the JSON does not list (no bits: a fixed wire)",
                     "%s: %s" % (key, [(fab.node_name(x), fab.node_name(y)) for x, y in list(ap)[:2]]))
                B = B - ap
            i1 = {p for p in B - A if re.search(r"BUFGCTRL\d+_I1$", fab.node_name(p[1]))}
            if i1:
                flag("bits-only pip into a deselected BUFGCTRL I1 (all-zero mux encoding)",
                     "%s: %s" % (key, [(fab.node_name(x), fab.node_name(y)) for x, y in i1]))
                B = B - i1
            if A == B:
                n_eq += 1
            else:
                n_ne += 1
                flag("NET ROUTED DIFFERENTLY (pip sets differ)",
                     "%s: %d pips json-only, %d bits-only, %d common; e.g. json-only %s bits-only %s"
                     % (key, len(A - B), len(B - A), len(A & B),
                        [(fab.node_name(x), fab.node_name(y)) for x, y in list(A - B)[:2]],
                        [(fab.node_name(x), fab.node_name(y)) for x, y in list(B - A)[:2]]))
        say("5. ROUTING  %d nets with identical pip sets, %d differ "
            "(%d of the equal ones only after removing pips to dead bels); %d constant nets "
            "compared by sink in 3, not by pip" % (n_eq, n_ne, n_dead, n_const))

    say("")
    say("DIFFERENCES (%d kinds):" % len(bad))
    for k, v in sorted(bad.items()):
        say("  %6d  %s" % (v, k))
        for e in ex[k]:
            say("            %s" % e)
    txt = "\n".join(R)
    print(txt)
    if a.out:
        open(a.out, "w").write(txt + "\n")
    benign = ("cell in routed JSON, not configured by the bits (it has NO loads)",
              "json pips that ARE in the bits", "pin unconnected in routed JSON, same constant",
              "LUT pin unconnected in routed JSON", "BUFGCTRL I1 unconnected in JSON",
              "bits-only pip into a deselected BUFGCTRL I1", "bits-only always-on ppip",
              HARMLESS_CONST)
    hard = [k for k in bad if not k.startswith(benign)]
    say("VERDICT: %s" % ("EQUIVALENT (only the benign kinds above)" if not hard else
                         "NOT EQUIVALENT: " + "; ".join(hard)))
    print(R[-1])
    if a.out:
        open(a.out, "a").write(R[-1] + "\n")
    sys.exit(1 if hard else 0)


if __name__ == "__main__":
    main()
