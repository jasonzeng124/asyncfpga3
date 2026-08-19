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
            ic.append((unesc(m.group(1)), unesc(m.group(2)), int(m.group(3))))
            n_ic += 1
            continue
        m = RE_INST.search(line)
        if m:
            inst = unesc(m.group(1))
            continue
        m = RE_IO.search(line)
        if m:
            iopaths[inst].append((m.group(1), m.group(2), int(m.group(3))))
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
            init = int(params.get("INIT", "0") or "0", 2)
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
    n_emit_io = n_emit_sh = 0
    for cname in order:
        t = cells[cname]["type"]
        arcs = iopaths.get(cname, [])
        shs = setuphold.get(cname, [])
        if not arcs and not shs:
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
        if shs:
            S.append("    (TIMINGCHECK")
            for edge, sig, su, hd in shs:
                S.append("      (SETUPHOLD (%s %s) (posedge CK) (%d:%d:%d) (%d:%d:%d))"
                         % (edge, sig, su, su, su, hd, hd, hd))
                n_emit_sh += 1
            S.append("    )")
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
    print("SETUPHOLD claimed %d -> emitted %d" % (n_sh, n_emit_sh))
    if unexpected:
        print("UNEXPECTED unconnected ports: %d" % len(unexpected))
        for r in unexpected[:20]:
            print("   ", r)
        sys.exit(1)


if __name__ == "__main__":
    main()
