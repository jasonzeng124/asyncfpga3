#!/usr/bin/env python3
"""Fold duplicated LUT input nets before nextpnr-xilinx (openXC7).

WHY (bench-debugged on silicon, 2026-07-21, EBAZ4205 knapsack bring-up):
nextpnr-xilinx's fixupPlacement() merges LUT inputs that carry the same
net onto one physical A-pin whenever the LUT shares a fractured slice
site with a 5LUT partner, and rebuilds the X_ORIG_PORT_A* attribute for
the merged pin. That attribute comes out mangled ('I0I1 ' -- one token,
no separator), the FASM writer's boost::split cannot map it back to
logical inputs, silently defaults the pin to I0, and the permuted
physical INIT loses every term involving the other duplicated input.
For AND-shaped functions the emitted INIT becomes ALL-ZERO: the LUT is
a constant on real hardware while every simulation and audit (which all
run on the logical netlist) stays green. Which LUTs die is seed- and
placement-dependent.

Our async netlists hit this systematically:
  * alib_delay stage[0]: .i0(path[0]) and .i1(i) are the same net by
    construction -- the first hop of EVERY matched-delay/handshake-delay
    chain. One dead adel stage freezes that hlatch's controller and the
    whole handshake upstream of it (observed: core completely
    unresponsive, i_ack never rises).
  * alib_bdmux s2u at loop entries: the compiler ties ctl and in1_req
    to the same c<N>_req net.

FIX: for every LUT cell, if two input pins carry the same net, rewrite
INIT so the function reads the net from the lowest-index pin only, and
tie the other pin(s) to constant 0. Logically identical, same cell and
hop count (audits unaffected). Pins tied to a CONSTANT net are immune
to the nextpnr bug: the mis-permuted INIT rows are exactly the rows
where the constant pin reads 1, which are never addressed on hardware.

Usage:
  dedup_lut_inputs_xc7.py <yosys.json> [-o out.json]   fold (in-place
    by default), prints a per-kind summary.
  dedup_lut_inputs_xc7.py --check <routed.json>        post-route gate:
    fail (exit 1) if nextpnr merged LUT pins carrying a live (non
    constant) net -- i.e. the mangled-attr FASM hazard is present.
"""
import json
import re
import sys

LUT_TYPES = {"LUT1": 1, "LUT2": 2, "LUT3": 3, "LUT4": 4,
             "LUT5": 5, "LUT6": 6}


def fold_cell(cell, ninputs):
    conn = cell["connections"]
    pins = ["I%d" % i for i in range(ninputs)]
    bynet = {}
    for idx, p in enumerate(pins):
        bits = conn.get(p, [])
        if len(bits) != 1 or not isinstance(bits[0], int):
            continue                       # unconnected or constant
        bynet.setdefault(bits[0], []).append(idx)
    groups = {net: idxs for net, idxs in bynet.items() if len(idxs) > 1}
    if not groups:
        return 0
    init = cell["parameters"]["INIT"]
    width = 1 << ninputs
    if isinstance(init, str) and set(init) <= {"0", "1"}:
        bits = [c == "1" for c in init[::-1]]      # bits[j] = INIT[j]
        bits += [False] * (width - len(bits))
    else:
        val = int(init) if isinstance(init, int) else int(init, 2)
        bits = [(val >> j) & 1 == 1 for j in range(width)]
    folded = 0
    for net, idxs in groups.items():
        master, extras = idxs[0], idxs[1:]
        for e in extras:
            newbits = []
            for j in range(width):
                jj = (j & ~(1 << e)) | ((1 << e) if (j >> master) & 1 else 0)
                newbits.append(bits[jj])
            bits = newbits
            # function no longer depends on pin e; tie it off
            for j in range(width):
                assert bits[j] == bits[j ^ (1 << e)]
            conn["I%d" % e] = ["0"]
            folded += 1
    cell["parameters"]["INIT"] = "".join(
        "1" if b else "0" for b in bits[::-1])
    return folded


def check_routed(path):
    """Scan a nextpnr routed.json for X_ORIG_PORT_A* attributes holding
    more than one logical input (the fixupPlacement merge marker). A
    merged pin is fatal unless its net is the packer GND/VCC constant
    (mis-permuted INIT rows are then unreachable)."""
    with open(path) as f:
        design = json.load(f)
    bad = []
    for mod in design.get("modules", {}).values():
        const_bits = set()
        for nname, ninfo in mod.get("netnames", {}).items():
            if nname in ("$PACKER_GND_NET", "$PACKER_VCC_NET"):
                const_bits.update(b for b in ninfo.get("bits", [])
                                  if isinstance(b, int))
        for cname, cell in mod.get("cells", {}).items():
            attrs = cell.get("attributes", {})
            for k, v in attrs.items():
                if not k.startswith("X_ORIG_PORT_A"):
                    continue
                if not isinstance(v, str):
                    continue
                toks = [t for t in v.strip().split(" ") if t]
                merged = len(toks) > 1 or (
                    len(toks) == 1 and not re.fullmatch(r"I[0-5]", toks[0])
                    and re.fullmatch(r"(I[0-5])+", toks[0]))
                if not merged:
                    continue
                pin = k[len("X_ORIG_PORT_"):]
                bits = cell.get("connections", {}).get(pin, [])
                netbits = [b for b in bits if isinstance(b, int)]
                if not netbits or all(b in const_bits for b in netbits):
                    continue                       # constant: benign
                bad.append((cname, pin, v))
    if bad:
        print("  dedup-lut-inputs CHECK: FAIL -- %d live merged LUT "
              "pin(s) (FASM INIT will be mis-permuted):" % len(bad))
        for cname, pin, v in bad[:10]:
            print("    %s %s attr=%r" % (cname, pin, v))
        sys.exit(1)
    print("  dedup-lut-inputs CHECK: PASS (no live merged LUT pins)")


def main():
    args = sys.argv[1:]
    if args and args[0] == "--check":
        check_routed(args[1])
        return
    out = None
    if "-o" in args:
        i = args.index("-o")
        out = args[i + 1]
        del args[i:i + 2]
    path = args[0]
    out = out or path
    with open(path) as f:
        design = json.load(f)
    total = 0
    kinds = {}
    for mod in design.get("modules", {}).values():
        for cname, cell in mod.get("cells", {}).items():
            n = LUT_TYPES.get(cell.get("type", ""))
            if n is None:
                continue
            k = fold_cell(cell, n)
            if k:
                total += k
                tag = re.sub(r"\[\d+\]", "[*]",
                             ".".join(cname.split(".")[-3:-1]) or cname)
                kinds[tag] = kinds.get(tag, 0) + k
    with open(out, "w") as f:
        json.dump(design, f)
    print("  dedup-lut-inputs: folded %d duplicated input pin(s)" % total)
    for tag in sorted(kinds):
        print("    %-40s %d" % (tag, kinds[tag]))


if __name__ == "__main__":
    main()
