#!/usr/bin/env python3
"""
gen.py -- turn nextpnr-xilinx's ROUTED design (gcd_hw_routed.json) plus its
ROUTED SDF (gcd_hw.sdf) into an iverilog-simulatable gate-level netlist with
100% of the routed delays actually attached.

Two problems are solved here, and they are the two that stopped the previous
attempt.

1. ESCAPING.  nextpnr escapes individual characters inside instance paths
   (\\$abc\\$8577\\$auto\\$blifparse.cc\\:557\\:parse_blif\\$8578).  iverilog 11's
   SDF lexer rejects that and then discards the WHOLE DELAYFILE.  Since this
   script generates the netlist, it also owns the names: every cell is renamed
   to a plain identifier c_NNNNNN and the SDF is rewritten through the SAME
   bijection.  names.map records the correspondence in both directions so a
   failing cell can always be traced back to urig.udut.ucond_br10.

2. INTERCONNECT IS SILENTLY IGNORED BY IVERILOG 11.  Verified directly: an
   (INTERCONNECT u1/O u2/A (5000:5000:5000)) parses without complaint and
   changes nothing.  That matters more than everything else in this file --
   on this route the median interconnect delay is 720 ps against a flat 124 ps
   LUT arc, so ignoring INTERCONNECT throws away ~85% of every path and yields
   a simulation that looks annotated and is not.

   Fix: every INTERCONNECT becomes a real one-input cell.  The routed JSON has
   exactly one INTERCONNECT per connected input pin (45569 entries, 45569
   distinct destinations, zero input pins missing) so the transform is exact
   and total, not an approximation: each destination pin gets its own private
   net driven by an ICBUF, and the SDF entry is rewritten as an (IOPATH I O)
   on that ICBUF.  A driver's fanout therefore arrives at each of its sinks at
   its own routed time, which is the property an asynchronous design actually
   depends on and which a single shared net cannot express.

   Everything is then an IOPATH, so the acceptance gate is one number:
   iverilog either matched all of them or it names the ones it did not.

SLICE_LUTX INIT expansion is inherited from the previous attempt's mknetlist.py
(nextpnr's own get_lut_init() walk over X_ORIG_PORT_A<n>) and is unchanged; see
expand_lut_init.
"""
import json, os, re, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dsp_model  # noqa: E402  (the DSP48E1 configurations prims.v models)

# Where the routed inputs live and the generated files go.  Defaults to
# this directory so the scripts still work standing alone, but build.sh
# sets GLS_WORK to a per-design build dir: the sources stay in git and
# the ~900 MB of generated netlist, maps and vvp images stay out of it.
HERE = os.environ.get("GLS_WORK") or os.path.dirname(os.path.abspath(__file__))
JSON = os.path.join(HERE, "routed.json")
SDF  = os.path.join(HERE, "routed.sdf")
OUT_V   = os.path.join(HERE, "netlist.v")
OUT_VB  = os.path.join(HERE, "netlist_baked.v")
OUT_SDF = os.path.join(HERE, "annot.sdf")
OUT_MAP = os.path.join(HERE, "names.map")
OUT_NET = os.path.join(HERE, "nets.map")

# nextpnr bel port names that are not legal Verilog identifiers, and the legal
# name used on both sides of the rewrite.  SELMUX2_1's two data inputs are the
# bare digits.
PORT_RENAME = {("SELMUX2_1", "0"): "D0", ("SELMUX2_1", "1"): "D1"}

OUTPUT_PORTS = {
    "SLICE_LUTX": {"O5", "O6"},
    "SELMUX2_1": {"OUT"},
    "SLICE_FFX": {"Q"},
    "CARRY4": {"O0", "O1", "O2", "O3", "CO0", "CO1", "CO2", "CO3"},
    "BUFGCTRL": {"O"},
    "BSCAN": {"CAPTURE", "DRCK", "RESET", "RUNTEST", "SEL", "SHIFT",
              "TCK", "TDI", "TMS", "UPDATE"},
    "IOB33_OUTBUF": {"OUT"},
    "IOB33_INBUF_EN": {"OUT"},
    "PSEUDO_GND": {"Y"},
    "PSEUDO_VCC": {"Y"},
    "DSP48E1_DSP48E1": set(["P%d" % i for i in range(48)]
                           + ["PCOUT%d" % i for i in range(48)]
                           + ["ACOUT%d" % i for i in range(30)]),
    "PAD": set(),          # PAD/PAD is an INTERCONNECT destination: an input here
}

# What an unrouted input pin is at the bel level.  A pin nextpnr left unrouted
# is not floating on silicon -- the bel has a hardware default -- and every one
# of these is checked against a census of what actually occurs (see the
# unexpected-unconnected assertion at the end).
TIE = {
    ("SLICE_LUTX", "A1"): 0, ("SLICE_LUTX", "A2"): 0, ("SLICE_LUTX", "A3"): 0,
    ("SLICE_LUTX", "A4"): 0, ("SLICE_LUTX", "A5"): 0, ("SLICE_LUTX", "A6"): 1,
    ("SLICE_FFX", "CE"): 1,      # unrouted CE = permanently enabled
    ("SLICE_FFX", "SR"): 0,      # unrouted SR = never set/reset
    ("CARRY4", "CIN"): 0, ("CARRY4", "CYINIT"): 0,
    ("CARRY4", "DI0"): 0, ("CARRY4", "DI1"): 0,
    ("CARRY4", "DI2"): 0, ("CARRY4", "DI3"): 0,
    ("BUFGCTRL", "I1"): 0, ("BUFGCTRL", "S0"): 0, ("BUFGCTRL", "S1"): 0,
    ("BUFGCTRL", "CE0"): 1, ("BUFGCTRL", "CE1"): 1,
    ("BUFGCTRL", "IGNORE0"): 1, ("BUFGCTRL", "IGNORE1"): 1,
    ("BSCAN", "TDO"): 0,
}

PORT_ORDER = {
    "SLICE_LUTX": ["A1", "A2", "A3", "A4", "A5", "A6", "O5", "O6"],
    "SELMUX2_1": ["0", "1", "S0", "OUT"],
    "SLICE_FFX": ["CK", "D", "CE", "SR", "Q"],
    "CARRY4": ["CIN", "CYINIT", "DI0", "DI1", "DI2", "DI3",
               "S0", "S1", "S2", "S3", "O0", "O1", "O2", "O3",
               "CO0", "CO1", "CO2", "CO3"],
    "BUFGCTRL": ["I0", "I1", "S0", "S1", "CE0", "CE1", "IGNORE0", "IGNORE1", "O"],
    "BSCAN": ["TDO", "CAPTURE", "DRCK", "RESET", "RUNTEST", "SEL", "SHIFT",
              "TCK", "TDI", "TMS", "UPDATE"],
    "PAD": ["PAD"],
    "IOB33_OUTBUF": ["IN", "OUT"],
    "IOB33_INBUF_EN": ["PAD", "OUT"],
    "PSEUDO_GND": ["Y"],
    "PSEUDO_VCC": ["Y"],
}

# ---- DSP48E1 ----------------------------------------------------------------
# prims.v models the configurations dsp_model.py accepts -- combinational,
# and since S7 registered (AREG/BREG/CREG/MREG/PREG; see its DSP48E1_DSP48E1
# header and dsp_model.reg_config).  These
# are its port groups, in the order prims.v declares them; a group of width 0
# is a scalar pin.
DSP_T = "DSP48E1_DSP48E1"
DSP_IN = [("A", 30), ("ACIN", 30), ("B", 18), ("C", 48), ("PCIN", 48),
          ("OPMODE", 7), ("ALUMODE", 4), ("CARRYINSEL", 3), ("CARRYIN", 0)]
DSP_OUT = [("P", 48), ("PCOUT", 48), ("ACOUT", 30)]


def _dsp_pins(groups):
    return [g if n == 0 else "%s%d" % (g, i) for g, n in groups
            for i in range(max(n, 1))]


PORT_ORDER[DSP_T] = _dsp_pins(DSP_IN) + _dsp_pins(DSP_OUT)


# A REGISTERED cell (dsp_model.reg_config) also connects these, and only
# those its registers read; a combinational cell never does, so its instance
# text is what it always was.
DSP_REG_IN = [(p, 0) for p in ("CLK", "CEA1", "CEA2", "CEB1", "CEB2", "CEC", "CEM", "CEP",
                               "RSTA", "RSTB", "RSTC", "RSTM", "RSTP")]


def dsp_group(pin):
    for g, n in DSP_IN + DSP_REG_IN + DSP_OUT:
        if pin == g if n == 0 else (pin.startswith(g) and pin[len(g):].isdigit()):
            return g
    return None


# Parameters a routed DSP48E1 of this flow carries, and the value each must
# have for the modelled configuration (None = checked separately).  Anything
# else -- a parameter not listed, or a listed one with another value -- is
# refused: an unmodelled DSP mode would otherwise simulate as this one.
DSP_PARAMS = {"AREG": None, "ACASCREG": None, "BREG": None, "BCASCREG": None, "CREG": None,
              "DREG": 0, "ADREG": 0, "MREG": None, "PREG": None, "INMODEREG": 0,
              "OPMODEREG": 0, "ALUMODEREG": 0, "CARRYINREG": 0,
              "CARRYINSELREG": 0, "USE_MULT": "MULTIPLY", "USE_SIMD": "ONE48",
              "USE_DPORT": "FALSE", "B_INPUT": "DIRECT", "A_INPUT": None,
              "IS_CLK_INVERTED": None}
RE_DSP_INV = re.compile(r"^IS_(OPMODE|ALUMODE|INMODE)\[(\d)\]_INVERTED$|^IS_CARRYIN_INVERTED$")


def dsp_regs(c):
    """-> (rp, pins, why) of the DSP48E1 `c`'s register parameters
    (dsp_model.reg_config): pins = the CLK/CE/RST pins a registered cell
    connects, [] for a combinational one."""
    params = c.get("parameters", {})

    def iv(v):
        if isinstance(v, int):
            return v
        return int(v, 2) if isinstance(v, str) and v and set(v) <= set("01") else 0
    return dsp_model.reg_config({k: iv(params.get(k, 0))
                                 for k in dsp_model.REGS + dsp_model.REGS_REFUSED})


def dsp_config(cname, c, netname):
    """-> (ZMUX, ACASC, extra parameter text) for the routed DSP48E1 `c`, or
    exit naming what is not modelled (dsp_model.config() decides).  A control pin's value is its connected constant net, or
    the tile constant nextpnr recorded in DSP_VCC_PINS / DSP_GND_PINS (pins
    with no interconnect path, patches/nextpnr-xilinx-dsp-constpins.patch),
    XOR its IS_*_INVERTED parameter."""
    def refuse(why):
        sys.exit("gen.py: DSP48E1 %s: %s -- prims.v models only the "
                 "configurations of cells/gls/dsp_model.py (see its DSP48E1_DSP48E1 "
                 "header); refusing rather than simulating this one as another." % (cname, why))
    params, attrs, conns = c.get("parameters", {}), c.get("attributes", {}), c["connections"]

    def val(v):
        return int(v, 2) if isinstance(v, str) and v and set(v) <= set("01") else v
    inv = {}
    for k, v in params.items():
        m = RE_DSP_INV.match(k)
        if m:
            inv[(m.group(1) or "CARRYIN") + (m.group(2) or "")] = val(v) & 1
        elif k not in DSP_PARAMS:
            refuse("parameter %s=%s is not one this model knows" % (k, v))
        elif DSP_PARAMS[k] is not None and val(v) != DSP_PARAMS[k]:
            refuse("%s=%s (modelled: %s)" % (k, v, DSP_PARAMS[k]))
    rp, rpins, rwhy = dsp_regs(c)
    if rwhy:
        refuse("; ".join(rwhy))
    reg = dsp_model.registered(rp)
    clkinv = val(params.get("IS_CLK_INVERTED", 0) or 0)
    clkinv = clkinv & 1 if isinstance(clkinv, int) else None
    if clkinv is None:
        refuse("IS_CLK_INVERTED=%s" % params.get("IS_CLK_INVERTED"))
    vcc = set(attrs.get("DSP_VCC_PINS", "").split())
    gnd = set(attrs.get("DSP_GND_PINS", "").split())
    if reg:
        # the clock must be a live net; CE/RST may be live or constant, but
        # must be wired (no tie-off is assumed for a register control)
        for pin in rpins:
            if not conns.get(pin) and pin not in vcc and pin not in gnd:
                refuse("registered (%s) but %s is not connected" %
                       (" ".join("%s=%d" % kv for kv in sorted(rp.items()) if kv[1]), pin))
        cn = netname.get(conns["CLK"][0], "")
        if cn in ("$PACKER_VCC_NET", "$PACKER_GND_NET"):
            refuse("registered but CLK is the constant %s" % cn)

    def ctl(pin):
        bl = conns.get(pin)
        if bl:
            name = netname.get(bl[0], "")
            if name == "$PACKER_VCC_NET":
                v = 1
            elif name == "$PACKER_GND_NET":
                v = 0
            else:
                refuse("control pin %s is driven by %r, not a constant" % (pin, name))
        elif pin in vcc:
            v = 1
        elif pin in gnd:
            v = 0
        else:
            refuse("control pin %s is neither connected nor a recorded tile constant" % pin)
        return v ^ inv.get(pin, 0)

    def word(g, n):
        return sum(ctl("%s%d" % (g, i)) << i for i in range(n))
    opmode, alumode, inmode = word("OPMODE", 7), word("ALUMODE", 4), word("INMODE", 5)
    carryinsel, carryin = word("CARRYINSEL", 3), ctl("CARRYIN")
    cfg, why = dsp_model.config(opmode, alumode, inmode, carryinsel, carryin, rp if reg else None)
    if why:
        refuse("OPMODE=%s ALUMODE=%s INMODE=%s CARRYINSEL=%s CARRYIN=%d: %s"
               % (format(opmode, "07b"), format(alumode, "04b"), format(inmode, "05b"),
                  format(carryinsel, "03b"), carryin, "; ".join(why)))
    zmux = cfg["ZMUX"]
    acasc = {"DIRECT": 0, "CASCADE": 1}.get(params.get("A_INPUT", "DIRECT"))
    if acasc is None:
        refuse("A_INPUT=%s" % params.get("A_INPUT"))
    for pin, bl in conns.items():
        if bl and c["port_directions"].get(pin) == "output" and dsp_group(pin) is None:
            refuse("output %s is connected and not modelled" % pin)
    # The operand pins the function reads must be wired, or the model would
    # multiply tie-offs.
    rd = cfg["reads"]
    need = ["%s%d" % ("ACIN" if acasc else "A", i) for i in range(30 if "A30" in rd else 25)] + \
           ["B%d" % i for i in range(18)] + \
           (["PCIN%d" % i for i in range(48)] if "PCIN" in rd else []) + \
           (["C%d" % i for i in range(48)] if "C" in rd else [])
    missing = [p for p in need if not conns.get(p)]
    if missing:
        refuse("operand pins %s... are not connected" % ", ".join(missing[:4]))
    # the original configuration keeps its original parameter text
    extra = "" if dsp_model.is_default(cfg) else "".join(
        ", .%s(%d)" % (k, cfg[k]) for k in ("XMUX", "YMUX", "ALUMODE", "AGATE", "CIN", "MUNK"))
    if reg:
        extra += "".join(", .%s(%d)" % (k, cfg[k]) for k in dsp_model.REG_PARAMS)
        extra += ", .CLKINV(%d)" % clkinv
    elif clkinv:
        pass    # no register reads the clock: its inversion changes nothing
    return zmux, acasc, extra


def dsp_reg_conn(c):
    """-> [(port, fixed value or None)] the extra ports a registered DSP48E1
    instance connects: None = through arg() (its routed net), else a tile
    constant from DSP_VCC_PINS / DSP_GND_PINS.  [] for a combinational one."""
    rp, pins, why = dsp_regs(c)
    if why or not dsp_model.registered(rp):
        return []
    attrs, conns = c.get("attributes", {}), c["connections"]
    vcc = set(attrs.get("DSP_VCC_PINS", "").split())
    out = []
    for p in pins:
        if conns.get(p):
            out.append((p, None))
        else:
            out.append((p, "1'b1" if p in vcc else "1'b0"))   # dsp_config() refused anything else
    return out


RE_ORIG_PORT = re.compile(r"I\d+")


def expand_lut_init(init_str, attrs, out_port):
    """nextpnr-xilinx xilinx/fasm.cc get_lut_init(), reimplemented.

    The JSON INIT is in the ORIGINAL logical order (I0 = LSB); the packer is
    free to put any logical input on any physical A-pin and records where it
    put it in X_ORIG_PORT_A<n>.

    THAT ATTRIBUTE IS NOT CONSISTENTLY DELIMITED, and a whitespace split on it
    silently computes the wrong truth table.  When one physical pin carries
    several logical inputs -- which happens whenever the packer routes one net
    to two pins of the same LUT -- nextpnr writes the list two different ways
    in the same file:

        'I0 I3'    'I2 I3 I4'      space separated
        'I4I3 '    'I3I1 '         run together, with a trailing space

    On the second form .split() returns the single token "I4I3", which matches
    no logical input, so BOTH inputs drop out of the address and the expanded
    table is the function of a smaller LUT.  There is no error: the netlist
    elaborates, the design simulates, and 131 LUTs of gcd_hw compute something
    that is not what the bitstream computes -- 33 of them inside ucmpi11 alone,
    which is why gate simulation insisted gcd's comparator answered 0 for
    ordinary positive numbers while the same bitstream on the die was getting
    31-iteration vectors right.  The silicon was never affected; nextpnr's own
    fasm.cc reads the attribute it wrote.  Match the names instead of splitting
    on the delimiter, because the delimiter is not dependable.  Return a truth table addressed by PHYSICAL
    pin (A1 = bit 0), so the Verilog model can be a plain direct-addressed
    decoder.  Arity comes from the stored width of INIT, never from
    X_ORIG_TYPE -- the two disagree on real cells here, and trusting
    X_ORIG_TYPE truncates the address and drops live inputs.
    """
    v = int(init_str, 2) if init_str else 0
    arity = max(1, len(init_str).bit_length() - 1)
    log_to_bit = {"I%d" % i: i for i in range(arity)}
    n_phys = 6 if out_port == "O6" else 5
    table = 0
    for j in range(1 << n_phys):
        log_index = 0
        for k in range(n_phys):
            if not (j >> k) & 1:
                continue
            for name in RE_ORIG_PORT.findall(
                    attrs.get("X_ORIG_PORT_A%d" % (k + 1), "")):
                if name in log_to_bit:
                    log_index |= 1 << log_to_bit[name]
        if log_index < (1 << arity):
            table |= ((v >> log_index) & 1) << j
    return table


# --------------------------------------------------------------- read the SDF

RE_CT   = re.compile(r'\(CELLTYPE "([^"]*)"\)')
RE_INST = re.compile(r"\(INSTANCE\s+(\S*?)\)")
RE_IO   = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)")
RE_IC   = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)")
RE_SH   = re.compile(r"\(SETUPHOLD\s+\((\w+)\s+(\w+)\)\s+\((\w+)\s+(\w+)\)"
                     r"\s+\((-?\d+):-?\d+:-?\d+\)\s+\((-?\d+):-?\d+:-?\d+\)")


def unesc(s):
    return s.replace("\\", "")


# Which column of each (min:typ:max) triple to read.  nextpnr writes the same
# number in all three, so for its SDF this changes nothing; an SDF from
# fid/xray_delay.py carries (FAST_MIN : SLOW_MIN : SLOW_MAX) and this picks
# the corner.  Default "min" keeps the behaviour this file always had.
# GLS_SDF_FIELD=band (F3) reads BOTH ends of an xray_delay.py triple and takes
#   fast_min + GLS_SDF_BAND * (slow_max - fast_min)
# -- the board's position inside [fast min, slow max] (F1: 0.35-0.41 on long
# rings), never a mix of corners within one arc.  On nextpnr's own SDF (all
# three columns equal) it returns that number unchanged.
_FIELD = os.environ.get("GLS_SDF_FIELD", "min")
SDF_FIELD = {"min": 0, "typ": 1, "max": 2, "band": 0}[_FIELD]
SDF_BAND = float(os.environ.get("GLS_SDF_BAND", "0.38"))


def tri(m, first):
    """the selected column of the triple whose min is group `first`"""
    if _FIELD == "band":
        lo, hi = int(m.group(first)), int(m.group(first + 2))
        return int(round(lo + SDF_BAND * (hi - lo)))
    return int(m.group(first + SDF_FIELD))


# Delay perturbation, for corner and scatter runs (off by default, and then
# every number below is the routed SDF's own):
#   GLS_DELAY_SCALE=f      every IOPATH and INTERCONNECT times f (a corner:
#                          0.9 fast, 1.1 slow)
#   GLS_SCATTER=sigma      then each arc independently times (1 + sigma*N(0,1)),
#                          clamped at 0; GLS_SCATTER_SEED picks the draw.
#   GLS_SCATTER_MODE=wire  instead, every PIP of the route gets one factor
#                          (a stable hash of seed and pip name), and each
#                          interconnect arc is scaled by the mean factor of the
#                          pips on its own path -- so sinks that share a wire
#                          share its scatter, and sigma 0 is still exact.  The
#                          SDF has no per-pip delays, hence the mean.  Arcs
#                          whose route sink cannot be found fall back to one
#                          draw each, and are counted.
#   GLS_SCATTER_ONLY=prefix[,prefix...]
#                          apply the scatter only to arcs of instances with one
#                          of these prefixes; every arc still draws its factor,
#                          so each keeps exactly the value it had in the full
#                          draw -- for bisecting which unit a failure needs.
#                          A prefix ending in '=' matches that name exactly.
#   GLS_SCALE_INST=prefix:f[,prefix:f...]
#                          arcs of instances whose name starts with prefix
#                          (and interconnect INTO them) times f as well -- a
#                          targeted fault, for proving a check can fail.
# SETUPHOLD windows are left alone.  The numbers are drawn here, once, so the
# annotated and the baked netlist carry the same perturbed values.
#   GLS_SCATTER_REGION=sigma_r  (F3, within-die variation) ALSO multiply every
#                          arc by one factor per die region, 1 + sigma_r*N(0,1)
#                          from a stable hash of (seed, region), where a region
#                          is a GLS_REGION_SLICES x GLS_REGION_SLICES block of
#                          slice sites (default 10).  Cell arcs take their own
#                          site's region, interconnect its sink's.  This is the
#                          CORRELATED part; GLS_SCATTER(_MODE=wire) stays the
#                          per-wire random part, so "region + wire" is
#                          GLS_SCATTER_REGION=r GLS_SCATTER=w GLS_SCATTER_MODE=wire.
#                          Sizing: research/data/fid/f3_model.md.  Unset or 0 =
#                          the file this was before, byte for byte.
#   GLS_SCATTER_LOGN=1     draw every scatter factor (per arc, per pip, per
#                          region) as exp(sigma*N) instead of 1 + sigma*N: the
#                          same N, the same median (1), the same first-order
#                          spread, but a delay can never reach or cross 0, and a
#                          -2.5 sigma region at sigma 0.32 is 0.45x, not 0.20x.
#                          The linear form is not clamped in any physical sense:
#                          max(0, ...) only hides N < -1/sigma, and well before
#                          that it makes the fast tail far fatter than the slow
#                          one (1 - 2.5*0.32 = 0.20 vs 1 + 2.5*0.32 = 1.80).
#                          Unset = the linear form, byte for byte.
DELAY_SCALE = float(os.environ.get("GLS_DELAY_SCALE", "1"))
SCATTER = float(os.environ.get("GLS_SCATTER", "0"))
_rng = __import__("random").Random(int(os.environ.get("GLS_SCATTER_SEED", "1")))


SCATTER_ONLY = [p for p in os.environ.get("GLS_SCATTER_ONLY", "").split(",") if p]
SCALE_INST = [(p.rsplit(":", 1)[0], float(p.rsplit(":", 1)[1]))
              for p in os.environ.get("GLS_SCALE_INST", "").split(",") if p]
n_scaled_inst = 0


SCATTER_REGION = float(os.environ.get("GLS_SCATTER_REGION", "0"))
LOGN = os.environ.get("GLS_SCATTER_LOGN", "0") not in ("", "0")


def sfactor(sigma, n):
    """the scatter factor for a standard normal draw n"""
    import math
    return math.exp(sigma * n) if LOGN else 1 + sigma * n
REGION_SLICES = int(os.environ.get("GLS_REGION_SLICES", "10"))
_region = None
n_region = n_region_miss = 0


class RegionModel:
    RE_SITE = re.compile(r"^[A-Z0-9_]*?_X(\d+)Y(\d+)/")

    def __init__(self, json_path, sigma, seed, size):
        self.cells = json.load(open(json_path))["modules"]["top"]["cells"]
        self.sigma, self.seed, self.size = sigma, seed, size
        self.cache = {}

    def key(self, inst):
        c = self.cells.get(inst)
        if c is None:
            return None
        m = self.RE_SITE.match(c.get("attributes", {}).get("NEXTPNR_BEL", ""))
        if not m:
            return None
        return (int(m.group(1)) // self.size, int(m.group(2)) // self.size)

    def factor_of_key(self, k):
        if k not in self.cache:
            import hashlib, math
            h = hashlib.md5(("region:%s:%d:%d" % (self.seed, k[0], k[1])).encode()).digest()
            u1 = (int.from_bytes(h[:8], "big") + 1) / 2.0 ** 64
            u2 = int.from_bytes(h[8:], "big") / 2.0 ** 64
            self.cache[k] = sfactor(self.sigma, math.sqrt(-2 * math.log(u1)) * math.cos(2 * math.pi * u2))
        return self.cache[k]

    def factor(self, inst):
        k = self.key(inst)
        return None if k is None else self.factor_of_key(k)


def region_factor(inst):
    """1 unless GLS_SCATTER_REGION is set; else the factor of inst's region."""
    global _region, n_region, n_region_miss
    if not SCATTER_REGION:
        return 1
    if _region is None:
        _region = RegionModel(JSON, SCATTER_REGION,
                              os.environ.get("GLS_SCATTER_SEED", "1"), REGION_SLICES)
    f = _region.factor(inst)
    if f is None:
        n_region_miss += 1
        return 1
    n_region += 1
    return f


def perturb(ps, inst=""):
    global n_scaled_inst
    f = DELAY_SCALE * sfactor(SCATTER, _rng.gauss(0, 1)) if SCATTER else DELAY_SCALE
    if SCATTER_REGION:
        f *= region_factor(inst)
    if SCATTER and SCATTER_ONLY and not any(
            inst == p[:-1] if p.endswith("=") else inst.startswith(p) for p in SCATTER_ONLY):
        f = DELAY_SCALE
    for prefix, g in SCALE_INST:
        if inst.startswith(prefix):
            f *= g
            n_scaled_inst += 1
            break
    if f == 1:
        return ps
    return max(0, int(round(ps * f)))


SCATTER_MODE = os.environ.get("GLS_SCATTER_MODE", "arc")
n_wire = n_wire_fallback = 0


class WireModel:
    def __init__(self, json_path, sigma, seed):
        top = json.load(open(json_path))["modules"]["top"]
        self.cells = top["cells"]
        self.routes = {}
        for nn in top["netnames"].values():
            r = nn.get("attributes", {}).get("ROUTING")
            if r and nn["bits"]:
                self.routes.setdefault(nn["bits"][0], r)
        self.parents = {}
        self.sigma, self.seed = sigma, seed

    def pip_factor(self, pip):
        import hashlib, math
        h = hashlib.md5(("%s:%s" % (self.seed, pip)).encode()).digest()
        u1 = (int.from_bytes(h[:8], "big") + 1) / 2.0 ** 64
        u2 = int.from_bytes(h[8:], "big") / 2.0 ** 64
        return sfactor(self.sigma, math.sqrt(-2 * math.log(u1)) * math.cos(2 * math.pi * u2))

    def parent(self, bit):
        if bit not in self.parents:
            f = self.routes[bit].split(";")
            self.parents[bit] = {f[i]: f[i + 1] for i in range(0, len(f) - 2, 3)}
        return self.parents[bit]

    def factor(self, dst):
        cell, _, pin = dst.rpartition("/")
        c = self.cells.get(cell)
        if c is None or pin not in c["connections"]:
            return None
        bit = c["connections"][pin][0]
        if bit not in self.routes:
            return None
        par = self.parent(bit)
        bel = c["attributes"].get("NEXTPNR_BEL", "")
        if "/" not in bel:
            return None
        site, b = bel.split("/")[:2]
        pre = "SITEWIRE/%s/" % site
        if b.endswith("LUT"):
            sinks = [w for w in par if w.startswith(pre) and re.match(r"^%s[1-6]$" % b[0], w[len(pre):])]
        else:
            sinks = [w for w in par if w.startswith(pre + pin)] or \
                    [w for w in par if w.startswith(pre) and par[w] and
                     not any(par.get(x, "").split("->")[0] == w for x in par)]
        if len(sinks) != 1:
            return None
        pips, w, seen = [], sinks[0], set()
        while w in par and par[w] and w not in seen:
            seen.add(w)
            pips.append(par[w])
            w = par[w].split("->")[0]
        if not pips:
            return None
        return sum(self.pip_factor(p) for p in pips) / len(pips)


_wire = None


def perturb_ic(ps, src, dst):
    """INTERCONNECT arcs: per-arc draw (perturb), or the wire model."""
    global _wire, n_wire, n_wire_fallback
    if SCATTER_MODE != "wire" or not SCATTER:
        return perturb(ps, dst.rpartition("/")[0])   # includes the region factor
    if _wire is None:
        _wire = WireModel(JSON, SCATTER, os.environ.get("GLS_SCATTER_SEED", "1"))
    f = _wire.factor(dst)
    if f is None:
        n_wire_fallback += 1
        return perturb(ps, dst.rpartition("/")[0])
    n_wire += 1
    inst = dst.rpartition("/")[0]
    if SCATTER_ONLY and not any(
            inst == p[:-1] if p.endswith("=") else inst.startswith(p) for p in SCATTER_ONLY):
        f = 1
    if SCATTER_REGION:
        f *= region_factor(inst)
    return max(0, int(round(ps * DELAY_SCALE * f)))


def read_sdf(path):
    """-> iopaths[inst] = [(from,to,ps)], ic = [(srcpin,dstpin,ps)],
          sh[inst] = [(edge,sig,su,hd)], plus raw claim counts."""
    iopaths = collections.defaultdict(list)
    setuphold = collections.defaultdict(list)
    ic = []
    inst = None
    n_io = n_ic = n_sh = 0
    for line in open(path):
        m = RE_IC.search(line)
        if m:
            ic.append((unesc(m.group(1)), unesc(m.group(2)),
                       perturb_ic(tri(m, 3), unesc(m.group(1)), unesc(m.group(2)))))
            n_ic += 1
            continue
        m = RE_INST.search(line)
        if m:
            inst = unesc(m.group(1))
            continue
        m = RE_IO.search(line)
        if m:
            iopaths[inst].append((m.group(1), m.group(2), perturb(tri(m, 3), inst or "")))
            n_io += 1
            continue
        m = RE_SH.search(line)
        if m:
            setuphold[inst].append((m.group(1), m.group(2), int(m.group(5)), int(m.group(6))))
            n_sh += 1
    return iopaths, ic, setuphold, n_io, n_ic, n_sh


def main():
    top = json.load(open(JSON))["modules"]["top"]
    cells = top["cells"]
    iopaths, ic, setuphold, n_io, n_ic, n_sh = read_sdf(SDF)
    netname = {}
    for name, nn2 in top.get("netnames", {}).items():
        for b in nn2["bits"]:
            netname.setdefault(b, name)
    # A DSP's timing is one parameter per (input group, output group), which
    # is exactly what the routed SDF carries on this chipdb.  A perturbed run
    # (scale, scatter) draws per arc; both netlists then take the group's
    # LARGEST arc, so the annotated and the baked build still agree.
    dsp_group_ps = {}
    for cname, c in cells.items():
        if c["type"] != DSP_T or cname not in iopaths:
            continue
        g = {}
        for a, z, ps in iopaths[cname]:
            ga, gz = dsp_group(a), dsp_group(z)
            if ga is None or gz is None:
                sys.exit("gen.py: DSP48E1 %s: SDF arc %s -> %s has no port in the "
                         "model" % (cname, a, z))
            g[(ga, gz)] = max(g.get((ga, gz), 0), ps)
        dsp_group_ps[cname] = g
        iopaths[cname] = [(a, z, g[(dsp_group(a), dsp_group(z))])
                          for a, z, _ in iopaths[cname]]
    sys.stderr.write("delays: SDF column %s, scale %g, scatter sigma %g (seed %s, mode %s)\n"
                     % (os.environ.get("GLS_SDF_FIELD", "min"), DELAY_SCALE, SCATTER,
                        os.environ.get("GLS_SCATTER_SEED", "1"), SCATTER_MODE))
    if SCATTER_MODE == "wire" and SCATTER:
        sys.stderr.write("delays: %d interconnect arc(s) from the wire model, %d fell back "
                         "to one draw each\n" % (n_wire, n_wire_fallback))
    if SCALE_INST:
        sys.stderr.write("delays: %d arc(s) scaled by GLS_SCALE_INST %s\n"
                         % (n_scaled_inst, os.environ["GLS_SCALE_INST"]))
        if n_scaled_inst == 0:
            sys.exit("GLS_SCALE_INST matched no instance -- the fault was not injected")
    if SCATTER_REGION:
        sys.stderr.write("delays: region scatter sigma %g over %dx%d-slice regions: %d arc(s) "
                         "placed, %d without a site (unscaled)\n"
                         % (SCATTER_REGION, REGION_SLICES, REGION_SLICES, n_region, n_region_miss))
    sys.stderr.write("SDF claims: %d IOPATH, %d INTERCONNECT, %d SETUPHOLD\n"
                     % (n_io, n_ic, n_sh))

    # ---- GLS_MODEL=fid (F3): state nodes for the metastability resolver ----
    # A LUT whose output is routed back into one of its own pins is a state
    # node (C-element, latch, arbiter q).  Its loop delay is that feedback
    # wire plus the pin's arc to the output; prims.v's GLS_FID SLICE_LUTX
    # treats an output reversal inside that time as a runt (fid_core.vh).
    # Loops through more than one cell are NOT detected (stated limitation).
    # Nothing here runs, and nothing below changes, without GLS_MODEL=fid.
    fid = os.environ.get("GLS_MODEL", "") == "fid"
    fid_loop = {}
    fid_fb = {}     # (cell, output) -> mask of the pins it feeds back into
    if fid:
        arcs = {}
        for cn, lst in iopaths.items():
            for a, z, ps in lst:
                arcs[(cn, a, z)] = ps
        for src, dst, ps in ic:
            sc, _, sp = src.rpartition("/")
            dc, _, dp = dst.rpartition("/")
            if sc == dc and cells.get(sc, {}).get("type") == "SLICE_LUTX" and sp in ("O5", "O6"):
                L = ps + arcs.get((sc, dp, sp), 124)
                fid_loop[(sc, sp)] = min(L, fid_loop.get((sc, sp), L))
                if not re.fullmatch(r"A[1-6]", dp) or (sp == "O5" and dp == "A6"):
                    sys.exit("gen.py: fid: %s feeds back into pin %s" % (src, dp))
                fid_fb[(sc, sp)] = fid_fb.get((sc, sp), 0) | (1 << (int(dp[1]) - 1))
        Ls = sorted(fid_loop.values())
        sys.stderr.write("fid: %d LUT state node(s) with a self-loop; loop delay min/median/max "
                         "%s ps\n" % (len(Ls), "/".join(str(x) for x in
                                       (Ls[0], Ls[len(Ls) // 2], Ls[-1])) if Ls else "-"))

    # ---- the bijection -----------------------------------------------------
    order = sorted(cells)
    newname = {n: "c_%06d" % i for i, n in enumerate(order)}

    # ---- one ICBUF per INTERCONNECT ---------------------------------------
    # dst pin -> (icbuf name, source net).  The source is looked up in the JSON
    # rather than trusted from the SDF string, so a mismatch between the two
    # files would be a hard error here rather than a quiet miswire.
    icname = {}
    for k, (src, dst, _ps) in enumerate(ic):
        icname[dst] = "ic_%06d" % k

    bits = set()
    for c in cells.values():
        for bl in c.get("connections", {}).values():
            for b in bl:
                bits.add(b)

    def net_of_pin(pin):
        inst, _, port = pin.rpartition("/")
        bl = cells[inst]["connections"].get(port)
        assert bl and len(bl) == 1, ("bad source pin", pin, bl)
        return "n%d" % bl[0]

    # Two netlists come out of one walk, identical except for where the delays
    # live: netlist.v leaves every timing parameter at its default and is the
    # build $sdf_annotate is run against (that is the acceptance gate), while
    # netlist_baked.v hard-codes the SAME parsed numbers as parameters.  They
    # are generated from one parse of one SDF, so they cannot disagree by
    # construction, and a short run of each is diffed to show they do not.
    L, B = [], []

    def both(s):
        L.append(s)
        B.append(s)

    both("// AUTO-GENERATED by gen.py -- do not hand-edit.")
    both("// Cell names are the c_NNNNNN side of names.map; ic_NNNNNN are the")
    both("// per-sink interconnect buffers that carry the routed wire delay.")
    both("`timescale 1ps/1ps")
    both("`default_nettype none")
    both("module top ();")
    for b in sorted(bits):
        both("  wire n%d;" % b)
    for k in range(len(ic)):
        both("  wire w%d;" % k)

    for k, (src, dst, ps) in enumerate(ic):
        L.append("  ICBUF ic_%06d (.I(%s), .O(w%d));" % (k, net_of_pin(src), k))
        B.append("  ICBUF #(.D(%d)) ic_%06d (.I(%s), .O(w%d));"
                 % (ps, k, net_of_pin(src), k))

    unexpected = []
    for cname in order:
        c = cells[cname]
        t = c["type"]
        conns = c.get("connections", {})
        attrs = c.get("attributes", {})
        params = c.get("parameters", {})
        nn = newname[cname]

        def arg(port):
            """Connection expression for one bel port of this cell."""
            if port in OUTPUT_PORTS.get(t, ()):
                bl = conns.get(port)
                if not bl:
                    return None            # dead output: genuinely undriven
                return "n%d" % bl[0]
            # an input: it is driven through its own interconnect buffer
            pin = "%s/%s" % (cname, port)
            if pin in icname:
                return "w%d" % int(icname[pin][3:])
            if conns.get(port):
                # connected but nextpnr wrote no route for it: cannot happen on
                # this design (checked) -- fall back to the raw net.
                return "n%d" % conns[port][0]
            # A CARRY4 whose CIN is unrouted is a chain head, and its carry-in
            # is a CONFIGURATION BIT, not a wire: nextpnr leaves the pin
            # unrouted and records the value in PRECYINIT_CONST.  Reading it is
            # not optional.  Two of the twelve heads here carry 1, and they are
            # urig.udut.usubi0 and usubi1 -- the kernel's subtractors, which are
            # A + ~B + 1.  Tie those to 0 and every subtraction comes out one
            # too small, the gcd loop's operand never reaches its terminating
            # value, and the kernel livelocks with every handshake still
            # toggling.  Vectors 0 and 1 are the C source's two early returns,
            # never enter the loop, and pass anyway -- so this is invisible to
            # exactly the two vectors that would otherwise have caught it.
            if t == "CARRY4" and port == "CYINIT" and "PRECYINIT_CONST" in params:
                return "1'b%s" % params["PRECYINIT_CONST"]
            if t == DSP_T:
                return "1'b0"      # dsp_config() refuses if the model reads it
            d = TIE.get((t, port))
            if d is None:
                unexpected.append((cname, t, port))
                return "1'b0"
            return "1'b%d" % d

        conn = []
        for p in PORT_ORDER[t]:
            if t == "SLICE_LUTX" and p in ("O5", "O6") and not conns.get(p):
                continue
            v = arg(p)
            if v is None:
                continue
            conn.append(".%s(%s)" % (PORT_RENAME.get((t, p), p), v))
        if t == DSP_T:
            for p, fixed in dsp_reg_conn(c):
                conn.append(".%s(%s)" % (p, fixed if fixed else arg(p)))

        # timing parameters for the baked netlist, straight off this cell's own
        # SDF arcs; every arc the SDF does not mention keeps prims.v's nominal.
        tp = [".T%s%s(%d)" % (PORT_RENAME.get((t, a), a), z, ps)
              for a, z, ps in iopaths.get(cname, [])]
        tps = (", " + ", ".join(tp)) if tp else ""
        if fid and (t == "SLICE_LUTX" or (t == "SLICE_FFX" and attrs.get("X_ORIG_TYPE")
                                            not in ("LDCE", "LDPE"))):
            for op in ("O6", "O5"):
                if (cname, op) in fid_loop:
                    tps += ", .META%s(1), .TLOOP%s(%d), .FB%s(%d)" % (
                        op[1], op[1], fid_loop[(cname, op)], op[1], fid_fb[(cname, op)])
            tps += ", .SEED(%d)" % (int(nn[2:]) + 1)

        if t == "SLICE_LUTX":
            out_port = "O6" if conns.get("O6") else "O5"
            init = expand_lut_init(params.get("INIT", "0"), attrs, out_port)
            L.append("  SLICE_LUTX #(.INIT(64'h%016x)) %s (%s);"
                     % (init & ((1 << 64) - 1), nn, ", ".join(conn)))
            B.append("  SLICE_LUTX #(.INIT(64'h%016x)%s) %s (%s);"
                     % (init & ((1 << 64) - 1), tps, nn, ", ".join(conn)))
        elif t == "SLICE_FFX" and attrs.get("X_ORIG_TYPE") in ("LDCE", "LDPE"):
            # A transparent latch on the FF bel (nextpnr marks it X_FF_AS_LATCH).
            # Simulating it as SLICE_FFX would make it edge-triggered.  Open
            # while CK == !IS_CLK_INVERTED (fasm.cc writes CLKINV =
            # !IS_CLK_INVERTED for a latch, and a latch-mode storage element is
            # open while its post-CLKINV clock is low); SR is asynchronous:
            # clear for LDCE, preset for LDPE.  The slice has no SR inverter,
            # so IS_CLR/PRE_INVERTED is NOT applied -- as on the die.
            ghigh = 0 if int(str(params.get("IS_CLK_INVERTED", "0")) or "0", 2) & 1 else 1
            sr_val = 1 if attrs["X_ORIG_TYPE"] == "LDPE" else 0
            init = int((params.get("INIT", "0") or "0").replace("x", "0"), 2) & 1
            L.append("  SLICE_LATX #(.INIT(1'b%d), .SRVAL(1'b%d), .GHIGH(1'b%d)) %s (%s);"
                     % (init, sr_val, ghigh, nn, ", ".join(conn)))
            B.append("  SLICE_LATX #(.INIT(1'b%d), .SRVAL(1'b%d), .GHIGH(1'b%d)%s) %s (%s);"
                     % (init, sr_val, ghigh, "".join(x for x in [tps] if "TCKQ" in x), nn, ", ".join(conn)))
        elif t == "SLICE_FFX":
            # FDRE and FDSE share this bel.  X_ORIG_PORT_SR says which the SR
            # pin is: "R" = synchronous reset to 0, "S" = synchronous set to 1.
            # 20 of the 247 flops here are FDSE, and modelling them as FDRE
            # would hold rst_sr at 0 and never assert the rig's reset at all.
            sr_val = 1 if attrs.get("X_ORIG_PORT_SR") == "S" else 0
            # An uninitialised reg arrives as INIT "x"; the bel powers up 0.
            init = int((params.get("INIT", "0") or "0").replace("x", "0"), 2)
            # iverilog applies none of the SDF's TIMINGCHECKs, so the baked
            # netlist carries the FF's setup/hold as parameters and the model
            # checks them itself (SLICE_FFX in prims.v).
            shs = setuphold.get(cname, [])
            if shs:
                tps += ", .TSU(%d), .THD(%d)" % (max(s for _, _, s, _ in shs),
                                                  max(h for _, _, _, h in shs))
            L.append("  SLICE_FFX #(.INIT(1'b%d), .SRVAL(1'b%d)) %s (%s);"
                     % (init, sr_val, nn, ", ".join(conn)))
            B.append("  SLICE_FFX #(.INIT(1'b%d), .SRVAL(1'b%d)%s) %s (%s);"
                     % (init, sr_val, tps, nn, ", ".join(conn)))
        elif t == DSP_T:
            zmux, acasc, extra = dsp_config(cname, c, netname)
            cfg = ".ZMUX(%d), .ACASC(%d)%s" % (zmux, acasc, extra)
            gp = "".join(", .T%s_%s(%d)" % (ga, gz, ps)
                         for (ga, gz), ps in sorted(dsp_group_ps.get(cname, {}).items()))
            L.append("  %s #(%s) %s (%s);" % (t, cfg, nn, ", ".join(conn)))
            B.append("  %s #(%s%s) %s (%s);" % (t, cfg, gp, nn, ", ".join(conn)))
        else:
            L.append("  %s %s (%s);" % (t, nn, ", ".join(conn)))
            B.append("  %s %s%s %s (%s);"
                     % (t, ("#(" + ", ".join(tp) + ")") if tp else "",
                        "", nn, ", ".join(conn)))

    both("endmodule")
    both("`default_nettype wire")
    open(OUT_V, "w").write("\n".join(L) + "\n")
    open(OUT_VB, "w").write("\n".join(B) + "\n")

    # ---- rewrite the SDF ---------------------------------------------------
    S = ["(DELAYFILE",
         '  (SDFVERSION "3.0")',
         '  (DESIGN "top")',
         '  (VENDOR "nextpnr")',
         '  (PROGRAM "gen.py rewrite of nextpnr gcd_hw.sdf")',
         "  (DIVIDER /)",
         "  (TIMESCALE 1ps)"]
    n_emit_io = 0
    n_emit_sh = sum(1 for c in order if c in setuphold and cells[c]["type"] == "SLICE_FFX")
    for cname in order:
        t = cells[cname]["type"]
        arcs = iopaths.get(cname, [])
        # No TIMINGCHECK: iverilog reports every one as 'SDF WARNING:
        # TIMINGCHECK not supported', which is the line the annotated run is
        # required not to print; the checks live in the baked netlist.
        if not arcs:
            continue
        if t == "SLICE_FFX" and cells[cname].get("attributes", {}).get("X_ORIG_TYPE") in ("LDCE", "LDPE"):
            t = "SLICE_LATX"
        S.append('  (CELL (CELLTYPE "%s") (INSTANCE %s)' % (t, newname[cname]))
        if arcs:
            S.append("    (DELAY (ABSOLUTE")
            for a, z, ps in arcs:
                a = PORT_RENAME.get((t, a), a)
                z = PORT_RENAME.get((t, z), z)
                S.append("      (IOPATH %s %s (%d:%d:%d) (%d:%d:%d))"
                         % (a, z, ps, ps, ps, ps, ps, ps))
                n_emit_io += 1
            S.append("    ))")
        S.append("  )")
    for k, (_src, _dst, ps) in enumerate(ic):
        S.append('  (CELL (CELLTYPE "ICBUF") (INSTANCE ic_%06d)'
                 "    (DELAY (ABSOLUTE (IOPATH I O (%d:%d:%d) (%d:%d:%d)))))"
                 % (k, ps, ps, ps, ps, ps, ps))
        n_emit_io += 1
    S.append(")")
    open(OUT_SDF, "w").write("\n".join(S) + "\n")

    with open(OUT_MAP, "w") as f:
        f.write("# <generated-name> <original-name>\n")
        for n in order:
            f.write("%s %s\n" % (newname[n], n))
        for k, (src, dst, _ps) in enumerate(ic):
            f.write("ic_%06d INTERCONNECT %s -> %s\n" % (k, src, dst))

    with open(OUT_NET, "w") as f:
        f.write("# <verilog-wire> <routed-json-net-name>\n")
        for name, nn2 in sorted(top.get("netnames", {}).items()):
            b = nn2["bits"]
            if len(b) == 1 and isinstance(b[0], int):
                f.write("n%d %s\n" % (b[0], name))

    print("cells         : %d" % len(cells))
    print("icbufs        : %d" % len(ic))
    print("nets          : %d (+%d icbuf outputs)" % (len(bits), len(ic)))
    print("IOPATH  claimed %d -> emitted %d (incl. %d icbuf)"
          % (n_io + n_ic, n_emit_io, len(ic)))
    print("SETUPHOLD claimed %d -> %d flops check them in netlist_baked.v" % (n_sh, n_emit_sh))
    if unexpected:
        print("UNEXPECTED unconnected ports: %d" % len(unexpected))
        for r in unexpected[:20]:
            print("   ", r)
        sys.exit(1)


if __name__ == "__main__":
    main()
