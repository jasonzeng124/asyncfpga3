#!/usr/bin/env python3
"""Derive and exhaustively prove every LUT INIT constant in the cell library.

Every constant in rtl/ is stated here as a boolean function plus a pin order,
and the INIT is *computed* from that spec rather than transcribed.  Running
this file proves three things:

  1. each computed INIT reproduces its spec on all 2**6 input combinations
     (exhaustive, not sampled -- the space is 64 rows);
  2. the constants the design review fixed independently agree with the
     computed ones (EXPECTED below, quoted from the artifact);
  3. the literal that appears in the RTL is the computed one (--check-rtl).

Pin order convention, from the review: I0 is address bit 0.  For a LUT6_2,
O5 is INIT[31:0] read with I0..I4 and O6 is INIT[63:32] read with I0..I4
*provided I5 is tied high* -- which is the only way two independent
five-input functions share one site.
"""

import sys, re, pathlib

# ---------------------------------------------------------------- primitives

def maj(*a):
    return int(sum(a) * 2 > len(a))


def lut6_init(f):
    """INIT for a LUT6 whose output is f(I0..I5)."""
    v = 0
    for k in range(64):
        i = [(k >> b) & 1 for b in range(6)]
        if f(*i):
            v |= 1 << k
    return v


def lut5_init(f):
    """32-bit half for a five-input function f(I0..I4)."""
    v = 0
    for k in range(32):
        i = [(k >> b) & 1 for b in range(5)]
        if f(*i):
            v |= 1 << k
    return v


def lut6_2_init(o6, o5):
    """INIT for a fractured LUT6_2 with I5 tied high: O6 = o6, O5 = o5."""
    return (lut5_init(o6) << 32) | lut5_init(o5)


def lut_eval(init, ins):
    """Read INIT the way silicon does: address = the pin vector, LSB = I0."""
    k = 0
    for b, v in enumerate(ins):
        k |= (v & 1) << b
    return (init >> k) & 1


# ---------------------------------------------------------------- cell specs
# Each entry: name -> (kind, pins, spec)
#   kind "lut6"    spec is f(I0..I5)                     -> 64-bit INIT
#   kind "lut6_2"  spec is (f_O6(I0..I4), f_O5(I0..I4))  -> 64-bit INIT, I5=1
#   kind "lutN"    spec is f(I0..I(N-1))                 -> 2**N-bit INIT

SPECS = {
    # --- C-elements -------------------------------------------------------
    # The rendezvous primitive: follow when the inputs agree, hold when they
    # differ.  Symmetric C(a,b) is exactly majority(a, b, q).
    "C2":       ("lut6", "a b q - - -",
                 lambda a, b, q, _3, _4, _5: maj(a, b, q)),
    "C3":       ("lut6", "a b c q - -",
                 lambda a, b, c, q, _4, _5: (a & b & c) | (q & (a | b | c))),

    # Control C-elements come up at 0 (q = ~rst . C), the loop's select token
    # comes up holding (q = rst + C).  rst is active high.
    "C2_RST":   ("lut6", "a b q rst - -",
                 lambda a, b, q, r, _4, _5: (not r) and maj(a, b, q)),
    "C2_SET":   ("lut6", "a b q rst - -",
                 lambda a, b, q, r, _4, _5: r or maj(a, b, q)),

    # An inverted input is a bubble on the pin, never a cell: C(a, ~b).
    "C2N_RST":  ("lut6", "a b q rst - -",
                 lambda a, b, q, r, _4, _5: (not r) and maj(a, 1 - b, q)),
    "C2N_SET":  ("lut6", "a b q rst - -",
                 lambda a, b, q, r, _4, _5: r or maj(a, 1 - b, q)),

    "C3_RST":   ("lut6", "a b c q rst -",
                 lambda a, b, c, q, r, _5:
                 (not r) and ((a & b & c) | (q & (a | b | c)))),
    # Fan-in four is the ceiling: feedback and rst take two of the six pins.
    "C4_RST":   ("lut6", "a b c d q rst",
                 lambda a, b, c, d, q, r:
                 (not r) and ((a & b & c & d) | (q & (a | b | c | d)))),

    # --- transparent-high D-latch ----------------------------------------
    "LATCH":      ("lut6", "d en q - - -",
                   lambda d, en, q, _3, _4, _5: d if en else q),
    "LATCH_RST0": ("lut6", "d en q rst - -",
                   lambda d, en, q, r, _4, _5: 0 if r else (d if en else q)),
    "LATCH_RST1": ("lut6", "d en q rst - -",
                   lambda d, en, q, r, _4, _5: 1 if r else (d if en else q)),
    # Transparent while the enable is LOW.  The inversion is free -- it is a
    # bubble on the pin, and an inverter is never a cell on this fabric -- so
    # this is the same one LUT as LATCH with a different constant.  No longer
    # used: it was bd_dr2bd's hold latch before the C-element decode replaced
    # it.  Kept because the derivation is sound and the shape recurs.
    "LATCH_NEN":  ("lut6", "d nen q - - -",
                   lambda d, nen, q, _3, _4, _5: q if nen else d),
    # Two bits share {EN, D_i, Q_i, D_j, Q_j} -- five pins, so half a LUT each.
    "LATCH_PAIR": ("lut6_2", "di en qi dj qj +1",
                   ((lambda di, en, qi, dj, qj: dj if en else qj),   # O6 = bit j
                    (lambda di, en, qi, dj, qj: di if en else qi))), # O5 = bit i

    # --- dual-rail decode -------------------------------------------------
    # bd_dr2bd, HOLD=1.  Two functions of the same rails:
    #     O6 = either = t + f          the request, before its matched delay
    #     O5 = d      = C(t, ~f)       the payload, held across the spacer
    # Three distinct inputs between them {t, f, d}, so one fractured LUT6_2
    # does both and the fix costs nothing over the LUT2 it replaces.  The C
    # holds on t=f=0, which IS the spacer -- that is the whole mechanism.
    # No reset: the power-up unknown is overwritten by the first valid code
    # and is never read behind a request, so the loop does not need one.
    "DR_DECODE":  ("lut6_2", "t f d - - +1",
                   ((lambda t, f, d, _3, _4: t | f),                      # O6
                    (lambda t, f, d, _3, _4:                              # O5
                        (t & (not f)) | (d & (t | (not f))))),
                   ),

    # --- steer / encoder --------------------------------------------------
    # Two AND gates over the same two wires.  req0 = req.~s, req1 = req.s.
    "STEER":   ("lut6_2", "req s - - - +1",
                ((lambda q, s, _2, _3, _4: q & s),          # O6 = req1
                 (lambda q, s, _2, _3, _4: q & (1 - s)))),  # O5 = req0
    # Bundled -> dual rail is the same circuit, pin for pin: t = req.d,
    # f = req.~d.  The branches are the rails.
    "ENCODER": ("lut6_2", "req d - - - +1",
                ((lambda q, d, _2, _3, _4: q & d),          # O6 = t
                 (lambda q, d, _2, _3, _4: q & (1 - d)))),  # O5 = f

    # --- pipeline link ----------------------------------------------------
    # C_i = C(req_in, ~C_i+1).  Two adjacent stages share five pins:
    # {req, C_i, C_i+1, C_i+2, rst}, so control is half a LUT per stage.
    "LINK_PAIR": ("lut6_2", "req ci cj ck rst +1",
                  ((lambda rq, ci, cj, ck, r:                     # O6 = C_i+1
                    (not r) and maj(ci, 1 - ck, cj)),
                   (lambda rq, ci, cj, ck, r:                     # O5 = C_i
                    (not r) and maj(rq, 1 - cj, ci)))),

    # --- decoupled link controller (bd_link_dctl, an experiment) ----------
    # Four SR-style state nodes, each `q' = ~rst . (set + q . ~reset)`, from
    # the equations in bd_link.v's header.  ld comes up 0 and is set by the
    # first lt.
    "DC_B":  ("lut6", "req ack ld b rst -",
              lambda rq, ak, ld, b, r, _5:
              (not r) and ((rq & ld & (1 - ak)) | (b & (1 - (ak & (1 - ld)))))),
    "DC_A":  ("lut6", "req b ld a rst -",
              lambda rq, b, ld, a, r, _5:
              (not r) and ((rq & b & ld) | (a & (rq | ld)))),
    "DC_LD": ("lut6", "lt s a ld rst -",
              lambda lt, s, a, ld, r, _5:
              (not r) and (1 - a) and ((lt & s) | ld)),
    "DC_LT": ("lut6", "b a gate - - -",
              lambda b, a, g, _3, _4, _5: (1 - b) & (1 - a) & (1 - g)),

    # --- mux --------------------------------------------------------------
    # The control decode folds into the join: C(x_req, ctl_req.~s) is a
    # function of four wires, one LUT6 with rst.
    "MUX_J0": ("lut6", "xreq creq s j0 rst -",
               lambda xq, cq, s, j, r, _5:
               (not r) and maj(xq, cq & (1 - s), j)),
    "MUX_J1": ("lut6", "yreq creq s j1 rst -",
               lambda yq, cq, s, j, r, _5:
               (not r) and maj(yq, cq & s, j)),
    # z-data = s ? y : x
    "MUX_DATA_PAIR": ("lut6_2", "s xi yi xj yj +1",
                      ((lambda s, xi, yi, xj, yj: yj if s else xj),
                       (lambda s, xi, yi, xj, yj: yi if s else xi))),

    # --- merge ------------------------------------------------------------
    # z-data = sel ? x : y, sel = x_req + x_ack
    "MERGE_DATA_PAIR": ("lut6_2", "sel xi yi xj yj +1",
                        ((lambda s, xi, yi, xj, yj: xj if s else yj),
                         (lambda s, xi, yi, xj, yj: xi if s else yi))),

    # --- arbitration ------------------------------------------------------
    # One state node read straight and complemented.
    "ARB_GRANTS": ("lut6_2", "r1 r2 q - - +1",
                   ((lambda r1, r2, q, _3, _4: r2 & (1 - q)),   # O6 = g2
                    (lambda r1, r2, q, _3, _4: r1 & q))),       # O5 = g1
    # In the arbiter, R0 = g1 + g2 pairs with the state node rather than with
    # the grants: it is a function of the same three wires, and rst makes four.
    "ARB_STATE_R0": ("lut6_2", "r1 r2 q rst - +1",
                     ((lambda r1, r2, q, r, _4:                   # O6 = q
                       r or maj(r1, 1 - r2, q)),
                      (lambda r1, r2, q, r, _4:                   # O5 = R0
                       (r1 & q) | (r2 & (1 - q))))),
    # The same node with one more pin: q is frozen while the shared resource's
    # acknowledge is high, so the next winner cannot be chosen until the
    # current transaction has fully returned to zero.  Still five distinct
    # inputs across both halves, so still one fractured LUT -- the fix is a
    # different constant, not a different cost.  See the finding written up in
    # the header of rtl/bd_arb.v.
    "ARB_STATE_R0_HOLD": ("lut6_2", "r1 r2 q rst A0 +1",
                          ((lambda r1, r2, q, r, a0:               # O6 = q
                            r or (q if a0 else maj(r1, 1 - r2, q))),
                           (lambda r1, r2, q, r, a0:               # O5 = R0
                            (r1 & q) | (r2 & (1 - q))))),

    # The odd bit of a data mux, when the width is odd and there is no partner
    # to pair with.  Three pins, so it is a whole LUT that happens to use half
    # of one -- which is why odd widths cost the extra half.
    "DATAMUX1": ("lut3", "s a b", lambda s, a, b: b if s else a),

    # --- plain gates ------------------------------------------------------
    "OR2":     ("lut2", "a b", lambda a, b: a | b),
    "AND2":    ("lut2", "a b", lambda a, b: a & b),
    "AND2B1":  ("lut2", "a b", lambda a, b: a & (1 - b)),
    "BUF":     ("lut1", "a", lambda a: a),
    # The whole of bd_src.  A source is a channel closed on itself through an
    # inversion, and this is the inversion.
    "INV":     ("lut1", "a", lambda a: 1 - a),
}

# Constants the design review fixed independently.  Quoted from the artifact;
# a mismatch here means the library and the review have drifted apart.
EXPECTED = {
    "C2":           0xE8E8E8E8E8E8E8E8,
    "C3":           0xFE80FE80FE80FE80,
    "C2_RST":       0x00E800E800E800E8,
    "C2N_SET":      0xFFB2FFB2FFB2FFB2,   # artifact states 16'hFFB2
    "LATCH_RST0":   0x00B800B800B800B8,   # artifact states 16'h00B8
    "ARB_GRANTS":   0x0C0C0C0CA0A0A0A0,
}


def compute():
    out = {}
    for name, entry in SPECS.items():
        kind, pins, spec = entry
        pins = pins.split()
        if kind == "lut6":
            init, width = lut6_init(spec), 64
        elif kind == "lut6_2":
            init, width = lut6_2_init(*spec), 64
        else:
            n = int(kind[3:])
            init, width = lut6_init(
                lambda *i, _f=spec, _n=n: _f(*i[:_n])) & ((1 << (1 << n)) - 1), 1 << n
        out[name] = (init, width, kind, pins)
    return out


def prove(name, init, width, kind, pins, spec):
    """Re-read the computed INIT the way the silicon does, on every row."""
    rows = 0
    if kind == "lut6_2":
        f6, f5 = spec
        for k in range(32):
            i = [(k >> b) & 1 for b in range(5)]
            # O6 with I5 tied high: address bit 5 is 1
            got6 = lut_eval(init, i + [1])
            got5 = lut_eval(init & 0xFFFFFFFF, i)
            assert got6 == int(bool(f6(*i))), (name, "O6", i)
            assert got5 == int(bool(f5(*i))), (name, "O5", i)
            rows += 2
    else:
        n = 6 if kind == "lut6" else int(kind[3:])
        for k in range(1 << n):
            i = [(k >> b) & 1 for b in range(n)]
            args = i + [0] * (6 - n)
            assert lut_eval(init, i) == int(bool(spec(*args[:max(n, 6) if kind == "lut6" else n]))), \
                (name, i)
            rows += 1
    return rows


def fmt(init, width):
    return "%d'h%0*X" % (width, width // 4, init)


def main():
    tbl = compute()
    rows = 0
    for name, (init, width, kind, pins) in tbl.items():
        rows += prove(name, init, width, kind, pins, SPECS[name][2])

    bad = []
    for name, want in EXPECTED.items():
        got = tbl[name][0]
        if got != want:
            bad.append((name, want, got))

    w = max(len(n) for n in tbl)
    print("%-*s  %-8s  %-22s  %s" % (w, "cell", "kind", "INIT", "pins I0..I5"))
    print("-" * (w + 62))
    for name, (init, width, kind, pins) in tbl.items():
        mark = "  <- review" if name in EXPECTED else ""
        print("%-*s  %-8s  %-22s  %s%s"
              % (w, name, kind, fmt(init, width), " ".join(pins), mark))

    print("\n%d rows proved exhaustively across %d cells" % (rows, len(tbl)))
    if bad:
        for name, want, got in bad:
            print("MISMATCH %s: review %016X, computed %016X" % (name, want, got))
        return 1
    print("%d constants agree with the design review" % len(EXPECTED))

    if "--check-rtl" in sys.argv:
        return check_rtl(tbl)
    return 0


# --------------------------------------------------------------------- audit
# The direction that matters is RTL -> spec, not spec -> RTL.  A constant in
# the table that no cell happens to use is documentation of a derivable
# variant and costs nothing.  A constant in a LUT that this file cannot derive
# is a number somebody typed, which is exactly the thing this file exists to
# make impossible.

HEX_LIT  = re.compile(r"\b(\d+)\s*'h\s*([0-9A-Fa-f_]+)")
COMMENT  = re.compile(r"//.*$")

# The scan above only sees hexadecimal, so a LUT constant written any other way
# would walk straight past it -- 2'b01 is as much an INIT as 2'h1 is.  Rather
# than teach the scanner every literal base and then have to tell an INIT from
# a bus tie-off, require that INITs be written in hex, so that the one scan is
# the whole of the coverage.  A bare identifier is allowed: it is a localparam,
# and the hex that defines it is caught on its own line.
INIT_ARG = re.compile(r"\.INIT\s*\(\s*([^)]*?)\s*\)")
INIT_OK  = re.compile(r"^(?:\d+\s*'h\s*[0-9A-Fa-f_]+|[A-Za-z_]\w*)$")


def check_rtl(tbl):
    """Every hexadecimal literal in rtl/ must be a constant derived above.

    Not just the ones inside .INIT(): a resettable latch picks its constant
    through a localparam, and a constant that reaches a LUT indirectly is
    still a constant that has to be right.  Comments are stripped first --
    a cell header may quote an INIT as prose, and prose is not a netlist.
    """
    root = pathlib.Path(__file__).resolve().parent.parent / "rtl"
    derived = {}                       # (width, value) -> [names]
    for name, (init, width, kind, pins) in tbl.items():
        derived.setdefault((width, init), []).append(name)

    used, unknown, nonhex = set(), [], []
    for path in sorted(root.glob("*.v")):
        for lineno, raw in enumerate(path.read_text().splitlines(), 1):
            line = COMMENT.sub("", raw)
            for m in INIT_ARG.finditer(line):
                if not INIT_OK.match(m.group(1)):
                    nonhex.append((path.name, lineno, m.group(1)))
            for m in HEX_LIT.finditer(line):
                width = int(m.group(1))
                value = int(m.group(2).replace("_", ""), 16)
                key = (width, value)
                if key in derived:
                    used.update(derived[key])
                else:
                    unknown.append((path.name, lineno, width, value))

    if nonhex:
        print("\nINITs in rtl/ not written as hex, so the audit below cannot see them:")
        for fn, ln, txt in nonhex:
            print("  %s:%d  .INIT(%s)" % (fn, ln, txt))
        return 1

    if unknown:
        print("\nLUT constants in rtl/ that this file cannot derive:")
        for fn, ln, width, value in unknown:
            print("  %s:%d  %s" % (fn, ln, fmt(value, width)))
        return 1

    idle = sorted(set(tbl) - used)
    print("every LUT constant in rtl/ is derived here and proved above")
    if idle:
        print("derived but not currently instantiated: " + ", ".join(idle))
    return 0


if __name__ == "__main__":
    sys.exit(main())
