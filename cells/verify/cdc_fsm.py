#!/usr/bin/env python3
"""Does a clocked state register read an asynchronous signal directly?

    python3 verify/cdc_fsm.py HARNESS_JSON [--clock aclk] [--reset aresetn] [--reg st ...]

HARNESS_JSON is yosys `proc; flatten; opt_clean; techmap; opt_clean;
write_json` of a generated bench harness, the kernel and the cell library
left as black boxes: gate level, so every cone is exact to the bit.

The August 2026 bench hang: the 3-bit state register `st` took its
S_WAIT_ACK -> S_WAIT_RES transition straight off o_req_latched/i_ack_latched,
flops that the self-timed kernel SETS ASYNCHRONOUSLY.  When the set landed in
the setup/hold window each of the three flops resolved on its own and `st`
became a bitwise mix of two states (011 -> 110, caught by the 7'h16 sticky
five times in eight board runs).  The fix is a two-flop synchroniser
(gen_bench.py, sync_i_ackl/sync_o_reql).  Metastability itself cannot be
simulated, but the STRUCTURE that allows it is a netlist property:

    a signal is ASYNC if it is an output of a black box (the kernel, a
    library cell), the output of a latch, or the output of a flop that is
    not clocked by --clock or whose asynchronous set/clear/load is driven,
    through logic, by an ASYNC signal (the --reset input alone is allowed
    there: it is the reset, released synchronously by the PS);

    no flop of a --reg register may have an ASYNC signal in the
    combinational cone of its D, enable or synchronous-reset inputs.

A synchroniser's first flop is allowed to (it is not a --reg); a register
that reads the synchroniser's SECOND flop passes, and one that reads the
first flop fails as a one-flop synchroniser.
Exit 0 clean, 1 on a violation, 2 when the register is not found.
"""
import argparse
import json
import sys

# Gate level (yosys `techmap`): every cell is one bit, so a cone is exact.
def ff_kind(t):
    """'ff', 'latch' or None for a yosys gate-level cell type."""
    if t.startswith(("$_DFF", "$_SDFF", "$_ALDFF", "$_DFFSR")):
        return "ff"
    if t.startswith(("$_DLATCH", "$_SR_")):
        return "latch"
    return None


def ff_ports(t):
    """(sampled-on-the-edge ports, asynchronous ports) of a flop type."""
    if t.startswith("$_SDFF"):
        return {"D", "E", "R"}, set()
    return {"D", "E"}, {"R", "S", "L", "AD"}


def load(path):
    with open(path) as f:
        mods = json.load(f)["modules"]
    tops = [m for m in mods.values() if "1" in str(m.get("attributes", {}).get("top", ""))]
    if len(tops) != 1:
        raise SystemExit("cdc_fsm: cannot tell which module is the top")
    return tops[0], mods


def analyse(path, clock="aclk", reset="aresetn", regs=("st",)):
    top, mods = load(path)
    ports = top["ports"]
    clk_bits = set(ports[clock]["bits"]) if clock in ports else set()
    rst_bits = set(ports[reset]["bits"]) if reset in ports else set()
    names, bases = {}, {}
    for n, v in sorted(top["netnames"].items(), key=lambda kv: (kv[1].get("hide_name", 0), kv[0])):
        for i, b in enumerate(v["bits"]):
            if not isinstance(b, str):
                names.setdefault(b, "%s[%d]" % (n, i) if len(v["bits"]) > 1 else n)
                bases.setdefault(b, set()).add(n)

    driver = {}       # bit -> (cell name, kind) kind in comb/ff/latch/bbox
    cells = top["cells"]
    for cn, c in cells.items():
        t = c["type"]
        kind = ff_kind(t) or ("comb" if t.startswith("$") else "bbox")
        dirs = c.get("port_directions", {})
        for p, bits in c["connections"].items():
            d = dirs.get(p)
            if d is None and kind == "bbox":
                d = mods.get(t, {}).get("ports", {}).get(p, {}).get("direction")
            if d == "output":
                for b in bits:
                    if not isinstance(b, str):
                        driver[b] = (cn, kind)

    def cone(bits):
        """Stop points (bit, cell, kind) behind `bits` through comb logic."""
        seen, out, stack = set(), set(), [b for b in bits if not isinstance(b, str)]
        while stack:
            b = stack.pop()
            if b in seen:
                continue
            seen.add(b)
            if b not in driver:
                out.add((b, None, "input"))
                continue
            cn, kind = driver[b]
            if kind != "comb":
                out.add((b, cn, kind))
                continue
            c = cells[cn]
            for p, pb in c["connections"].items():
                if c["port_directions"].get(p) == "input":
                    stack.extend(x for x in pb if not isinstance(x, str))
        return out

    def ff_inputs(cn, qbit=None):
        """Bits sampled on the clock edge by flop cell `cn` -- for one Q bit
        of a multi-bit register, only that bit's D (plus the shared enable
        and synchronous reset), or the first stage of a two-flop shift
        register would taint the second."""
        conn = cells[cn]["connections"]
        data, _ = ff_ports(cells[cn]["type"])
        return [b for p in data & set(conn) for b in conn[p]]

    memo = {}

    def is_async(stop, depth=0):
        b, cn, kind = stop
        if (b, cn) in memo:
            return memo[(b, cn)]
        memo[(b, cn)] = False     # cycles through flops: assume clocked until shown
        if kind in ("bbox", "latch"):
            why = kind
        elif kind == "input":
            why = None
        else:
            c = cells[cn]
            why = None
            if not set(c["connections"].get("C", [])) <= clk_bits:
                why = "clock"
            for p in ff_ports(c["type"])[1] & set(c["connections"]):
                for s in cone(c["connections"][p]):
                    if s[0] in rst_bits:
                        continue
                    if s[2] == "input" or is_async(s, depth + 1):
                        why = why or ("async %s" % p)
        memo[(b, cn)] = why
        return why

    found, bad = 0, []
    for cn, c in sorted(cells.items()):
        if ff_kind(c["type"]) != "ff":
            continue
        q = c["connections"].get("Q", [])
        if not any(bases.get(b, set()) & set(regs) for b in q):
            continue
        found += 1
        for p in ff_ports(c["type"])[0] & set(c["connections"]):
            for s in sorted(cone(c["connections"][p]), key=str):
                why = is_async(s)
                if not why and s[2] == "ff":
                    # a clocked flop whose own D reads an async signal is a
                    # ONE-flop synchroniser: its output can still be
                    # metastable when `st` samples it.  Two flops, not one.
                    if any(is_async(t) for t in cone(ff_inputs(s[1], s[0]))):
                        why = "one-flop synchroniser"
                if why:
                    bad.append("%s.%s <- %s (%s)" % (
                        "/".join(sorted({"%s[%d]" % (r, top["netnames"][r]["bits"].index(b))
                                         for b in q for r in bases.get(b, ()) if r in regs})), p,
                        names.get(s[0], s[1] or "?"), why))
    return found, bad


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("json")
    ap.add_argument("--clock", default="aclk")
    ap.add_argument("--reset", default="aresetn")
    ap.add_argument("--reg", action="append", default=None)
    a = ap.parse_args()
    regs = tuple(a.reg or ["st"])
    found, bad = analyse(a.json, a.clock, a.reset, regs)
    if not found:
        print("cdc_fsm: no flop of %s found -- nothing was checked" % ", ".join(regs))
        return 2
    for b in sorted(set(bad)):
        print("  ASYNC INTO STATE " + b)
    if bad:
        print("cdc_fsm FAIL: %s samples an asynchronous signal without a synchroniser"
              % ", ".join(regs))
        return 1
    print("cdc_fsm PASS: %d flop cell(s) of %s, every input in their cone is clocked by %s"
          % (found, ", ".join(regs), a.clock))
    return 0


if __name__ == "__main__":
    sys.exit(main())
