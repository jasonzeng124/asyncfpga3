#!/usr/bin/env python3
"""Structural bundling audit for hlsc-generated asynchronous netlists.

Classic STA cannot time a clockless netlist (it walks into the intentional
feedback loops), so this tool checks the one timing property the whole
methodology rests on, directly on the POST-SYNTHESIS mapped netlist:

    at every handshake latch, the request must arrive no earlier than
    the data it bundles.

For each alib_hlatch instance it computes, by backward traversal over the
mapped cell graph:

  D = max logic depth of the DATA cones feeding the latch's storage bits
      (this is the real abc-mapped datapath: FUNC expression logic, merge
       data muxes, carry chains, ...)
  R = logic depth of the REQUEST cone feeding the latch's enable gate
      (matched delay chains, merge/steer gates, join C-elements, ...)

and requires  R >= D + SLACK.

Traversal rules:
  * event sources (depth 0, traversal stops): latch controller C-elements
    ('.hs.'), latched data bits ('.mem.' cells ending '.u0'), merge select
    SR latches ('selsr'), top-level input ports, constants;
  * loop_breaker: free pass-through (they are resolved to wires for P&R);
  * SB_LUT4: +1 hop;  SB_CARRY: +CARRY_W hops (default 0.25 -- iCE40 carry
    is much faster than a LUT+routing hop);
  * feedback edges (back to a cell on the DFS stack) contribute 0, which is
    exactly right for C-elements encountered mid-path (e.g. the entry join).

Usage:  audit_bundling.py <yosys-json> [--target ice40|xc7] [--slack 2.0]
                          [--carry-w 0.25] [-v]
The JSON must be written BEFORE loop_breaker (and, for xc7, alib_xlut4)
resolution (see audit.sh / pnr_xc7.sh).
Exit code 0 = every latch has sufficient slack.

--target xc7: the openXC7 flow (synth_xilinx -arch xc7) maps alib_lut4
onto a private alib_xlut4 blackbox instead of SB_LUT4 (see async_lib.v's
ASYNC_SYNTH_XC7 branch -- yosys's own Xilinx cells_sim.v replaces any
same-named `LUT4` blackbox on read, so genuine 1:1-mapped primitive cells
have to hide behind a name it doesn't know about until after abc9 has
run). The hierarchical naming convention (.hs./.mem./selsr event sources,
.u0 suffix) is otherwise identical to ice40, since it comes from the same
Verilog source, not the synthesis backend. IBUF/OBUF are transparent
pass-throughs at the port boundary (mirroring loop_breaker); CARRY4 packs
4 carry-chain bits into one hard cell -- conservatively treated as a
single --carry-w hop across all its inputs/outputs, same simplification
as SB_CARRY.
"""
import argparse
import json
import re
import sys

LUT_W = 1.0

# Per-target cell tables. OUTP: cell type -> output port name(s) that make
# it a candidate driver (tuple for multi-port-output cells). IN_PORTS:
# cell type -> input port names to recurse into. WEIGHTS: cell type ->
# logic-hop cost of traversing it. SOURCE_TYPES: cell types whose outputs
# are always depth-0 event sources (registered/RAM outputs, scope markers)
# regardless of the .hs./.mem./selsr naming check. LUT_TYPES: cell types
# gated by the .u0 + .hs./.mem./selsr naming check to become real event
# sources (everything else of these types is abc-remapped datapath logic).
TARGETS = {
    "ice40": dict(
        OUTP={"SB_LUT4": ("O",), "SB_CARRY": ("CO",),
              "loop_breaker": ("Y",)},
        IN_PORTS={"SB_LUT4": ("I0", "I1", "I2", "I3"),
                  "SB_CARRY": ("CI", "I0", "I1"),
                  "loop_breaker": ("A",)},
        WEIGHTS={"SB_LUT4": LUT_W, "loop_breaker": 0.0},  # SB_CARRY: --carry-w
        SOURCE_TYPES={"SB_RAM40_4K", "SB_DFF", "SB_DFFE", "SB_DFFSR",
                      "SB_DFFR", "SB_DFFS", "SB_DFFSS", "SB_DFFN",
                      "$scopeinfo"},
        LUT_TYPES={"SB_LUT4"},
        # RAM_PORTS: hard memories are depth-0 sources on the way OUT, but
        # their request boundary needs auditing on the way IN, exactly like a
        # latch -- alib_ram's strobe is the capture event and the address /
        # write-data / write-enable are the bundled data. clk = the strobe
        # (the request), dat = every other real input. Constants (RE/MASK tied
        # high) resolve to depth 0 and are harmless to include.
        RAM_PORTS={"SB_RAM40_4K": dict(
            clk=("RCLK", "WCLK"),
            dat=("RADDR", "WADDR", "WDATA", "WCLKE", "RCLKE", "RE", "WE",
                 "MASK"))},
    ),
    "xc7": dict(
        # LUT1..LUT6: abc9-remapped datapath logic (free to re-optimize,
        # same as SB_LUT4 cells with net-derived names on ice40) -- these
        # are NOT alib_xlut4 (our genuine 1:1-mapped primitive boundary),
        # since abc9's own LUT packing picks whatever width it wants.
        # INV: abc9-emitted single-input inverter (distinct from a LUT1 --
        # shows up when a design has real synchronous logic around the
        # async core, e.g. an AXI register-slave wrapper's FSM).
        # MUXF7/MUXF8: dedicated F7/F8 wide-mux silicon that synth_xilinx
        # emits to build the wide multiplexers of a dynamic array/ROM index
        # (a const-table read, a bundle-array read) from LUT6 halves. Faster
        # than a LUT hop in reality; counted at a full LUT_W here, which is
        # conservative (over-counting the data path can only tighten slack).
        # BUFG is a TRANSPARENT zero-weight buffer here, not a source:
        # alib_ram's strobe goes through an explicit BUFG on xc7 (see the
        # ASYNC_SYNTH_XC7 branch there), and treating it as a source would
        # truncate the strobe cone to depth 0, letting every RAM-boundary
        # row pass vacuously as "wired". Genuine clock DOMAINS still root
        # at depth 0 because their BUFG input comes from PS7 (a source).
        OUTP={"alib_xlut4": ("O",), "CARRY4": ("CO", "O"),
              "DSP48E1": ("P",),
              "loop_breaker": ("Y",), "IBUF": ("O",), "OBUF": ("O",),
              "INV": ("O",), "MUXF7": ("O",), "MUXF8": ("O",),
              "BUFG": ("O",),
              **{f"LUT{n}": ("O",) for n in range(1, 7)}},
        IN_PORTS={"alib_xlut4": ("I0", "I1", "I2", "I3"),
                  "CARRY4": ("CI", "CYINIT", "DI", "S"),
                  # All unregistered combinational inputs capable of
                  # influencing P.  Constants disappear in depth(), while
                  # listing the complete surface avoids silently missing a
                  # future multiply/add DSP configuration.
                  "DSP48E1": ("A", "ACIN", "ALUMODE", "B", "BCIN", "C",
                              "CARRYIN", "CARRYINSEL", "D", "INMODE",
                              "OPMODE", "PCIN"),
                  "loop_breaker": ("A",), "IBUF": ("I",), "OBUF": ("I",),
                  "INV": ("I",), "BUFG": ("I",),
                  "MUXF7": ("I0", "I1", "S"), "MUXF8": ("I0", "I1", "S"),
                  **{f"LUT{n}": tuple(f"I{k}" for k in range(n))
                     for n in range(1, 7)}},
        WEIGHTS={"alib_xlut4": LUT_W, "loop_breaker": 0.0,
                 # 5.201 ns Zynq-7 database max / 478 ps calibrated hop,
                 # rounded up plus one hop. Tightened builds remain gated
                 # by the post-route DSP arc audit.
                 "DSP48E1": 12.0,
                 "IBUF": 0.0, "OBUF": 0.0, "INV": LUT_W, "BUFG": 0.0,
                 "MUXF7": LUT_W, "MUXF8": LUT_W,
                 **{f"LUT{n}": LUT_W for n in range(1, 7)}},
        # CARRY4: --carry-w
        # PS7/BUFG: hard-block/clock-buffer outputs, e.g. from an AXI
        # register-slave harness wrapping the async core (zynq/) -- these
        # never appear inside gcd's own req/data cones (gcd has no clock
        # port), but do show up in the netlist once a PS7-driven wrapper
        # is in the design.
        SOURCE_TYPES={"RAMB18E1", "RAMB36E1", "RAM64X1D_1", "RAM32X1D_1",
                      "RAM128X1S_1", "RAM32M", "RAM64M", "RAM32X1S",
                      "RAM64X1S", "FDRE", "FDSE", "FDCE", "FDPE",
                      "LDCE", "LDPE",
                      # BSCANE2: JTAG TAP hard block (zynq/knapsack_jtag_top's
                      # USER1 bridge). Its outputs are TAP-driven events, the
                      # same class as PS7's -- the TCK-domain harness FFs they
                      # feed are then skipped by the selftimed R==0 rule.
                      "BSCANE2",
                      "PS7", "$scopeinfo"},
        LUT_TYPES={"alib_xlut4"},
        # RAM32M: what synth_xilinx actually emits for a small `mem` array
        # (knapsack's 32x16 dp -> 2x RAM32M; port surface read off the
        # emitted netlist, not guessed). WCLK is alib_ram's self-timed
        # strobe; every address (write AND async-read -- read addresses
        # must also be settled before the strobe because strobe-clocked
        # FDREs capture DO on that same edge), write data, and WE are
        # bundled data.
        # FD*/LD* with selftimed=True: yosys splits alib_ram's registered
        # read out of the distributed-RAM primitive into ordinary FFs
        # clocked by the strobe. Those are capture events with the same
        # bundling obligation (their D cone includes the ~we read-gating
        # logic, which the RAM32M entry cannot see). selftimed skips any
        # instance whose clock pin has combinational depth 0 -- i.e. a
        # genuine BUFG/PS7 clock domain, like the AXI wrapper's FFs, where
        # classic sync-domain STA applies and this hop-count check would
        # be meaningless.
        # Block-RAM types (RAMB18E1 etc.) still have NO entry: no xc7
        # design has mapped alib_ram onto one through this flow yet, and
        # guessing CLKARDCLK/ADDRARDADDR/... mappings would produce a
        # check that silently passes. The audit stays loud for those.
        RAM_PORTS={
            "RAM32M": dict(
                clk=("WCLK",),
                dat=("ADDRA", "ADDRB", "ADDRC", "ADDRD",
                     "DIA", "DIB", "DIC", "DID", "WE")),
            **{t: dict(clk=("C",), dat=("D", "CE", "R", "S"),
                       selftimed=True)
               for t in ("FDRE", "FDSE")},
            **{t: dict(clk=("C",), dat=("D", "CE", "CLR", "PRE"),
                       selftimed=True)
               for t in ("FDCE", "FDPE")},
            **{t: dict(clk=("G",), dat=("D", "GE", "CLR", "PRE"),
                       selftimed=True)
               for t in ("LDCE", "LDPE")},
        },
    ),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("json_file")
    ap.add_argument("--target", choices=sorted(TARGETS), default="ice40",
                    help="synthesis backend the JSON came from (default ice40)")
    ap.add_argument("--slack", type=float, default=2.0,
                    help="required R - D margin in LUT hops (default 2.0)")
    ap.add_argument("--carry-w", type=float, default=0.25,
                    help="SB_CARRY/CARRY4 weight in LUT hops (default 0.25)")
    ap.add_argument("-v", "--verbose", action="store_true")
    a = ap.parse_args()
    cfg = TARGETS[a.target]
    CARRY_TYPE = "SB_CARRY" if a.target == "ice40" else "CARRY4"

    top = json.load(open(a.json_file))
    (name, mod), = ((n, m) for n, m in top["modules"].items()
                    if m.get("attributes", {}).get("top") in (1, "1",
                    "00000000000000000000000000000001")) or \
        [next(iter(top["modules"].items()))]

    cells = mod["cells"]
    ports = mod["ports"]

    # ---- net -> driver map -------------------------------------------
    # Cells NOT in OUTP have their outputs treated as depth-0 event
    # sources. That is deliberate for the REGISTERED kinds (BRAM read
    # data / DFF Q settle on their own strobe; alib_ram delays the
    # response request TR hops past that same strobe), but it would
    # silently hide an unknown COMBINATIONAL cell -- hence the whitelist.
    OUTP = dict(cfg["OUTP"])
    IN_PORTS = dict(cfg["IN_PORTS"])
    WEIGHTS = dict(cfg["WEIGHTS"])
    WEIGHTS[CARRY_TYPE] = a.carry_w
    KNOWN_SOURCE_TYPES = cfg["SOURCE_TYPES"]
    LUT_TYPES = cfg["LUT_TYPES"]
    for cname, c in cells.items():
        if c["type"] not in OUTP and c["type"] not in KNOWN_SOURCE_TYPES:
            print(f"bundling audit: ERROR unknown cell type "
                  f"{c['type']} ({cname}) -- extend the audit before "
                  "trusting it", file=sys.stderr)
            sys.exit(2)
    driver = {}
    for cname, c in cells.items():
        for op in OUTP.get(c["type"], ()):
            if op in c["connections"]:
                for bit in c["connections"][op]:
                    driver[bit] = cname
    port_bits = set()
    for pname, p in ports.items():
        if p["direction"] == "input":
            port_bits.update(b for b in p["bits"] if isinstance(b, int))

    def output_inputs(pname):
        """Return the internal (I) nets of this top-level output's OBUFs.

        Using the pad-side O net happens to be equivalent for ordinary cone
        depth because OBUF is transparent, but keeping the boundary on its
        internal side mirrors the post-route audit and lets the request probe
        recognize the final controller cell reliably.
        """
        out = []
        p = ports.get(pname, {})
        if p.get("direction") != "output":
            return out
        for bit in p.get("bits", []):
            cn = driver.get(bit)
            if cn is None or cells[cn]["type"] != "OBUF":
                continue
            out.extend(b for b in cells[cn]["connections"].get("I", [])
                       if isinstance(b, int))
        # iCE40 synth JSON exposes core output nets directly (no explicit
        # OBUF), whereas synth_xilinx inserts OBUFs. Preserve the direct-port
        # boundary instead of silently dropping the output audit.
        return out or [b for b in p.get("bits", []) if isinstance(b, int)]

    def is_source(cname, ctype):
        if ctype not in LUT_TYPES:
            return False
        if not cname.endswith(".u0"):
            return False        # abc datapath cells got net-derived names
        return (".hs." in cname or ".mem." in cname or "selsr" in cname)

    memo = {}
    onstack = set()

    def depth(bit):
        if not isinstance(bit, int):
            return 0.0                              # constant "0"/"1"/"x"
        if bit in memo:
            return memo[bit]
        if bit in port_bits or bit not in driver:
            memo[bit] = 0.0
            return 0.0
        cname = driver[bit]
        if cname in onstack:                        # feedback edge
            return 0.0
        c = cells[cname]
        ct = c["type"]
        if is_source(cname, ct):
            memo[bit] = 0.0
            return 0.0
        onstack.add(cname)
        d = 0.0
        for ip in IN_PORTS[ct]:
            for b in c["connections"].get(ip, []):
                d = max(d, depth(b))
        onstack.discard(cname)
        memo[bit] = d + WEIGHTS[ct]
        return memo[bit]

    def output_request_depth(bit):
        """Depth of the forward event that drives the module output.

        Normal latch-cone traversal intentionally treats every handshake
        C-element as a new event source.  At the *module output*, however,
        the final controller is the boundary being checked, so stopping at
        its Q would incorrectly report a zero-hop request path.  Follow that
        controller's forward delayed-request input (I1; I0 is acknowledge,
        I2 reset, I3 feedback), including the C-element's own LUT hop.
        """
        seen = set()
        while isinstance(bit, int) and bit in driver:
            cn = driver[bit]
            if cn in seen:
                break
            seen.add(cn)
            c = cells[cn]
            ct = c["type"]
            if ct in ("OBUF", "loop_breaker"):
                ins = c["connections"].get(IN_PORTS[ct][0], [])
                if not ins:
                    break
                bit = ins[0]
                continue
            if is_source(cn, ct) and ".hs." in cn:
                fwd = c["connections"].get("I1", [])
                if fwd:
                    return max(depth(b) for b in fwd) + WEIGHTS[ct]
            break
        return depth(bit)

    # ---- per-latch check ---------------------------------------------
    # engate LUT: '<latch>.engate.u0.u0', I0 = i_req (via breaker)
    # mem bit  : '<latch>.mem.bitcell[k].u0.u0', I1 = d[k] (via breaker)
    latches = {}
    for cname, c in cells.items():
        m = re.match(r"(.*)\.engate\.u0\.u0$", cname)
        if m and c["type"] in LUT_TYPES:
            latches.setdefault(m.group(1), {})["req"] = \
                c["connections"]["I0"]
        m = re.match(r"(.*)\.mem\.bitcell\[(\d+)\]\.u0\.u0$", cname)
        if m and c["type"] in LUT_TYPES:
            latches.setdefault(m.group(1), {}).setdefault("dat", []).extend(
                c["connections"]["I1"])
        # XC7-native payload latches.  Their D pin is the same logical probe
        # point as the feedback-LUT implementation's I1, while Q remains an
        # event/data source for downstream-cone traversal.
        m = re.match(r"(.*)\.mem\.bitcell\[(\d+)\]\.native_(?:zero|one)\.native$",
                     cname)
        if m and c["type"] in ("LDCE", "LDPE"):
            latches.setdefault(m.group(1), {}).setdefault("dat", []).extend(
                c["connections"]["D"])

    # Every source (latch data bit, or the environment per protocol) settles
    # one hop BEFORE its corresponding request event -- by alib_hlatch
    # construction (mem at +2 hops, ctl at TC+1 = +3). Credit that lead.
    LEAD = 1.0

    rows, worst, fails = [], None, 0
    for lname in sorted(latches, key=lambda s: (len(s), s)):
        L = latches[lname]
        if "req" not in L or "dat" not in L:
            continue
        R = max(depth(b) for b in L["req"])
        D = max(depth(b) for b in L["dat"])
        slack = R + LEAD - D
        # D <= LEAD means the data cone is pure wiring from an upstream
        # latch/port: capture is then guaranteed by the boundary lead alone
        # (pad latches, ready-token latch, back-to-back latches).
        wired = D <= LEAD
        ok = wired or slack >= a.slack
        fails += (not ok)
        rows.append((lname, R, D, slack, ok, wired))
        if worst is None or (not wired and slack < worst[3]) \
           or (worst[5] and not wired):
            worst = rows[-1]

    # The final FUNC intentionally forwards data directly to o_data instead
    # of inserting a redundant payload latch.  That makes the module output
    # itself a bundled-data boundary: o_req must not arrive before every
    # o_data bit.  Omitting this check lets an aggressively tightened final
    # stage appear safe merely because it has no downstream internal latch.
    rq, dt = output_inputs("o_req"), output_inputs("o_data")
    if rq and dt:
            R = max(output_request_depth(b) for b in rq)
            D = max(depth(b) for b in dt)
            slack = R + LEAD - D
            wired = D <= LEAD
            ok = wired or slack >= a.slack
            fails += (not ok)
            rows.append(("$output", R, D, slack, ok, wired))
            if worst is None or (not wired and slack < worst[3]) \
                    or (worst[5] and not wired):
                worst = rows[-1]
    if worst is None:
        worst = rows[0]

    if a.verbose or fails:
        print(f"{'latch':<12}{'req':>7}{'data':>7}{'slack':>8}  verdict")
        for lname, R, D, slack, ok, wired in rows:
            v = "ok (wired)" if wired else ("ok" if ok else "FAIL")
            print(f"{lname:<12}{R:>7.2f}{D:>7.2f}{slack:>8.2f}  {v}")
    w = worst
    print(f"bundling audit [{name}]: {len(rows)} latches, "
          f"min logic slack {w[3]:.2f} hops at {w[0]} "
          f"(req {w[1]:.2f}+{LEAD:.0f} vs data {w[2]:.2f}), "
          f"required {a.slack:.1f} -> "
          f"{'PASS' if fails == 0 else f'FAIL ({fails})'}")

    # ---- per-RAM request-boundary check --------------------------------
    # A latch is not the only thing that captures. alib_ram turns the request
    # edge into a self-timed strobe TS hops in, and THAT is a capture event
    # with the same bundling obligation: address / write-data / write-enable
    # must be settled before it. On a tagged shared port this includes the
    # request merge's selected payload and tag captured by the request hlatch;
    # alib_ram's TS then also covers the hard RAM setup window. ASYNC_SIM alone
    # cannot sign off the soft mux logic, so this mapped-netlist boundary check
    # remains required.
    # Same LEAD credit as a latch, and for the same reason: both cones start
    # at the upstream latch, whose data bits settle one hop before its ctl.
    RAM_PORTS = cfg.get("RAM_PORTS", {})
    ram_rows, ram_fails = [], 0
    for cname, c in sorted(cells.items()):
        spec = RAM_PORTS.get(c["type"])
        if spec is None:
            continue
        rq, dt = [], []
        for p in spec["clk"]:
            rq.extend(c["connections"].get(p, []))
        for p in spec["dat"]:
            dt.extend(c["connections"].get(p, []))
        if not rq or not dt:
            continue
        R = max(depth(b) for b in rq)
        # selftimed entries (FF types): only audit instances whose clock is
        # produced by combinational logic (a delay-chain strobe). Depth-0
        # clocks come straight from a BUFG/PS7-class source -- a real
        # synchronous domain where this check does not apply.
        if spec.get("selftimed") and R == 0:
            continue
        D = max(depth(b) for b in dt)
        slack = R + LEAD - D
        wired = D <= LEAD
        ok = wired or slack >= a.slack
        ram_fails += (not ok)
        ram_rows.append((cname, R, D, slack, ok, wired))

    # A memory the audit doesn't know how to probe must be loud, not silent:
    # passing an unchecked RAM boundary is exactly the failure this check
    # exists to prevent.
    unchecked = sorted({c["type"] for c in cells.values()
                        if "RAM" in c["type"].upper()
                        and c["type"] not in RAM_PORTS})
    if unchecked:
        print(f"bundling audit [{name}]: WARNING request boundary NOT "
              f"audited for {', '.join(unchecked)} (no RAM_PORTS entry for "
              f"target {a.target}) -- TSEL/TS margins unverified here",
              file=sys.stderr)

    if ram_rows:
        if a.verbose or ram_fails:
            print(f"{'memory':<24}{'req':>7}{'data':>7}{'slack':>8}  verdict")
            for cn, R, D, slack, ok, wired in ram_rows:
                v = "ok (wired)" if wired else ("ok" if ok else "FAIL")
                print(f"{cn:<24}{R:>7.2f}{D:>7.2f}{slack:>8.2f}  {v}")
        rw = min(ram_rows, key=lambda r: r[3])
        print(f"bundling audit [{name}]: {len(ram_rows)} memories, "
              f"min logic slack {rw[3]:.2f} hops at {rw[0]} "
              f"(req {rw[1]:.2f}+{LEAD:.0f} vs data {rw[2]:.2f}), "
              f"required {a.slack:.1f} -> "
              f"{'PASS' if ram_fails == 0 else f'FAIL ({ram_fails})'}")

    return 1 if (fails or ram_fails) else 0


def _run():
    # the depth() cone-walk recurses to the longest combinational chain; a
    # deeply-unrolled (single-stage) design can be thousands deep, past
    # Python's default limit and default C stack. Run under a big stack.
    import threading
    sys.setrecursionlimit(1_000_000)
    result = {}
    threading.stack_size(512 * 1024 * 1024)
    t = threading.Thread(target=lambda: result.setdefault("rc", main()))
    t.start()
    t.join()
    return result.get("rc", 2)


if __name__ == "__main__":
    sys.exit(_run())
