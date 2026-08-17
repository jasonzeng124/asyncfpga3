#!/usr/bin/env python3
"""Emit trace.vh: log named data buses on the handshake edge that validates them.

WHY THIS EXISTS AND gen_chan.py DOES NOT REPLACE IT.  gen_chan.py samples every
bus at a wall-clock instant.  In a four-phase pipeline the stages at that
instant hold values from DIFFERENT iterations -- a link output lags its own `_u`
input by a full handshake -- so a snapshot across stages reads as incoherent
arithmetic and invites exactly the wrong conclusion.  Here each group is logged
on the rising edge of the request that says its data is valid, so every line is
one iteration of one construct and the numbers in it belong together.

Usage:  GLS_WORK=<dir> python3 gen_trace.py [group ...]
        (no argument means every group in TRACE below)

The output is one line per event on stdout of the simulation:

    T <time_ps> <group> <name>=<signed-decimal> ...

-- READING A BUS WIDTH.  A bus is emitted at its DECLARED width, and a bus
whose top bits are missing from the routed netlist is reported as such rather
than silently narrowed.  gen_chan.py narrows: it takes max(bit index)+1 as the
width, so a 32-bit value whose bit 31 was optimised away prints as a 31-bit
one, and 0xFFFFFF94 arrives looking like 0x7FFFFF94 -- a sign flip, in a
program whose whole difficulty is signs.  A bit goes missing for an ordinary
reason (`a >>> 1` makes z[31] literally the same wire as a[31], so yosys keeps
one name for it), which is what makes the silent version dangerous: the netlist
is right and the readout is wrong.
"""
import json, os, re, sys, collections

HERE = os.environ.get("GLS_WORK") or os.path.dirname(os.path.abspath(__file__))

D = "urig.udut."

# group -> (request net that validates the group, [(label, bus) ...])
#
# The gcd loop, as bdc/emit.py named it from handshake_transformed.mlir.
# bb9  picks b = min(a, b) and tests a == 0   (the outer `while (a != 0)`)
# bb10 computes diff = a - b and a = |diff|
# bb11 is the ctz loop, `while (a > 0 && !(a & 1)) a >>= 1`
TRACE = {
    "bb9_min": (D + "n121_req", [
        ("a",       D + "n115__0", 32),  # merge12 -> select0 true side
        ("b",       D + "n117__0", 32),  # merge13 -> select0 false side
        ("a_lt_b",  D + "n120",     1),  # cmpi9 slt
        ("min",     D + "n121",    32),  # select0 = a<b ? a : b
        ("a_eq",    D + "n112__1", 32),  # merge10 -> cmpi10 (a == 0?)
        ("is_zero", D + "n122",     1),  # cmpi10: the outer loop's exit test
    ]),
    "bb10_abs": (D + "n138_req", [
        ("a",    D + "n125__1", 32),   # mux12 -> subi0 lhs
        ("b",    D + "n127__1", 32),   # mux13 -> subi0 rhs
        ("diff", D + "n134",    32),   # subi0  = a - b
        ("ge0",  D + "n136_u",   1),   # cmpi11 sgt(diff, -1), before its link
        ("nsub", D + "n137_u",  32),   # subi1  = 0 - diff, before its link
        ("abs",  D + "n138",    32),   # select1 = ge0 ? diff : -diff
    ]),
    # The comparator on its OWN request edge, so the reading cannot be blamed
    # on sampling it from a downstream stage's timing.
    "cmpi11": (D + "n136_u_req", [
        ("in",   D + "n135__2", 32),   # diff, as the comparator sees it
        ("sgt",  D + "n136_u",   1),   # cmpi11 output, combinational
        ("held", D + "n136",     1),   # ...and after its link, what select1 uses
    ]),
    "bb11_ctz": (D + "n163_req", [
        ("a",    D + "n145__2", 32),   # fork36 -> shrsi4
        ("shr",  D + "n163",    32),   # a >>> 1  (bit 31 aliases a[31])
        ("exit", D + "n161",     1),   # ori4: (a odd) | (a < 1)
    ]),
}

top = json.load(open(os.path.join(HERE, "routed.json")))["modules"]["top"]
nets = top["netnames"]

bits = collections.defaultdict(dict)
scalar = {}
for name, nn in sorted(nets.items()):
    b = nn["bits"]
    m = re.match(r"(.*)_data\[(\d+)\]$", name)
    if m and len(b) == 1 and isinstance(b[0], int):
        bits[m.group(1)][int(m.group(2))] = b[0]
    elif len(b) == 1 and isinstance(b[0], int):
        scalar[name] = b[0]

# The declared width of a bus, from the RTL rather than from what survived.
# bdc/emit.py's gcd kernel is 32-bit throughout except the 1-bit conditions,
# so the honest default is "as wide as the widest bit we can see, and say so
# if that is not 32".
def bus(name, want_w):
    """Bits of `name` at its DECLARED width, plus the indices that are absent.

    The width is declared by the caller, never inferred from max(bit index):
    inferring it is what makes a missing TOP bit invisible, and a missing top
    bit is the one that flips the sign.  Absent bits become 1'bx, so a trace
    line that cannot be trusted prints as `x` instead of as a plausible number.
    """
    bl = bits.get(name)
    if bl is None:
        # A 1-bit channel is a scalar netname, `<chan>_data` with no [0].
        # Missing this is how the loop CONDITIONS -- the only signals that say
        # which way a branch went -- drop out of a trace without a word.
        b = scalar.get(name + "_data")
        if b is None:
            return None, None
        bl = {0: b}
    holes = [k for k in range(want_w) if k not in bl]
    return holes, bl


want = sys.argv[1:] or list(TRACE)
L = ["// AUTO-GENERATED by gen_trace.py -- do not check in, one route only."]
missing = []

for g in want:
    if g not in TRACE:
        sys.exit(f"gen_trace.py: no such group {g!r}; have {sorted(TRACE)}")
    trig, members = TRACE[g]
    if trig not in scalar:
        missing.append((g, trig, "trigger"))
        continue
    parts, args, notes = [], [], []
    for label, b, w in members:
        holes, bl = bus(b, w)
        if bl is None:
            missing.append((g, b, "bus"))
            continue
        if holes:
            # Report it rather than narrow it.  A hole is normally an ALIAS --
            # `a >>> 1` makes z[31] literally a[31], so yosys keeps one name --
            # which means the netlist is right and only the readout is short.
            notes.append(f"{label} is {w}b, bits {holes} absent from this "
                         f"route (aliased); they print as x")
        cat = "{" + ", ".join(
            ("dut.n%d" % bl[k]) if k in bl else "1'bx"
            for k in range(w - 1, -1, -1)) + "}"
        parts.append(f"{label}=%0d")
        args.append(f"$signed({cat})")
    if notes:
        L.append("// %s: %s" % (g, "; ".join(notes)))
    L.append("always @(posedge dut.n%d)" % scalar[trig])
    L.append('  $display("T %%0t %s %s", $time, %s);'
             % (g, " ".join(parts), ", ".join(args)))

if missing:
    print("gen_trace.py: not in this route:", file=sys.stderr)
    for g, n, kind in missing:
        print(f"  {g}: {kind} {n}", file=sys.stderr)
    sys.exit(1)

open(os.path.join(HERE, "trace.vh"), "w").write("\n".join(L) + "\n")
print("traced groups:", ", ".join(want), "-> trace.vh")
