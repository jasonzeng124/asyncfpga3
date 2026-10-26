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
                     r"\s+\((\d+):\d+:\d+\)\s+\((\d+):\d+:\d+\)")


def unesc(s):
    return s.replace("\\", "")


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
DELAY_SCALE = float(os.environ.get("GLS_DELAY_SCALE", "1"))
SCATTER = float(os.environ.get("GLS_SCATTER", "0"))
_rng = __import__("random").Random(int(os.environ.get("GLS_SCATTER_SEED", "1")))


SCATTER_ONLY = [p for p in os.environ.get("GLS_SCATTER_ONLY", "").split(",") if p]
SCALE_INST = [(p.rsplit(":", 1)[0], float(p.rsplit(":", 1)[1]))
              for p in os.environ.get("GLS_SCALE_INST", "").split(",") if p]
n_scaled_inst = 0


def perturb(ps, inst=""):
    global n_scaled_inst
    f = DELAY_SCALE * (1 + SCATTER * _rng.gauss(0, 1)) if SCATTER else DELAY_SCALE
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
        return 1 + self.sigma * math.sqrt(-2 * math.log(u1)) * math.cos(2 * math.pi * u2)

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
        return perturb(ps, dst.rpartition("/")[0])
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
                       perturb_ic(int(m.group(3)), unesc(m.group(1)), unesc(m.group(2)))))
            n_ic += 1
            continue
        m = RE_INST.search(line)
        if m:
            inst = unesc(m.group(1))
            continue
        m = RE_IO.search(line)
        if m:
            iopaths[inst].append((m.group(1), m.group(2), perturb(int(m.group(3)), inst or "")))
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
    sys.stderr.write("delays: scale %g, scatter sigma %g (seed %s, mode %s)\n"
                     % (DELAY_SCALE, SCATTER, os.environ.get("GLS_SCATTER_SEED", "1"), SCATTER_MODE))
    if SCATTER_MODE == "wire" and SCATTER:
        sys.stderr.write("delays: %d interconnect arc(s) from the wire model, %d fell back "
                         "to one draw each\n" % (n_wire, n_wire_fallback))
    if SCALE_INST:
        sys.stderr.write("delays: %d arc(s) scaled by GLS_SCALE_INST %s\n"
                         % (n_scaled_inst, os.environ["GLS_SCALE_INST"]))
        if n_scaled_inst == 0:
            sys.exit("GLS_SCALE_INST matched no instance -- the fault was not injected")
    sys.stderr.write("SDF claims: %d IOPATH, %d INTERCONNECT, %d SETUPHOLD\n"
                     % (n_io, n_ic, n_sh))

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

        # timing parameters for the baked netlist, straight off this cell's own
        # SDF arcs; every arc the SDF does not mention keeps prims.v's nominal.
        tp = [".T%s%s(%d)" % (PORT_RENAME.get((t, a), a), z, ps)
              for a, z, ps in iopaths.get(cname, [])]
        tps = (", " + ", ".join(tp)) if tp else ""

        if t == "SLICE_LUTX":
            out_port = "O6" if conns.get("O6") else "O5"
            init = expand_lut_init(params.get("INIT", "0"), attrs, out_port)
            L.append("  SLICE_LUTX #(.INIT(64'h%016x)) %s (%s);"
                     % (init & ((1 << 64) - 1), nn, ", ".join(conn)))
            B.append("  SLICE_LUTX #(.INIT(64'h%016x)%s) %s (%s);"
                     % (init & ((1 << 64) - 1), tps, nn, ", ".join(conn)))
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
