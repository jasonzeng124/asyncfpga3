#!/usr/bin/env python3
"""Post-route bundling audit for the openXC7 (Zynq-7 / Xilinx 7-series)
flow -- XC7 counterpart of tests/postroute_audit.py (ice40). Runs INSIDE
nextpnr-xilinx via:

    PNR_SYNTH_JSON=X.json nextpnr-xilinx --chipdb X.bin --xdc X.xdc \
        --json X.json --ignore-loops --timing-allow-fail \
        --post-route tests/postroute_audit_xc7.py

Requires:
- the local getCellDelay/getRouteDelayPs Python binding additions in
  nextpnr-xilinx/xilinx/arch_pybindings.cc (hand-written against this
  tree's boost::python API; mirrors what tools/nextpnr-getCellDelay.patch
  does for ice40/pybind11 -- the binding is required to compare routed
  request and bundled-data arrivals at latch and RAM capture boundaries).
- PNR_SYNTH_JSON pointing at the SAME yosys JSON passed to --json (the
  synth_xilinx + lut4_resolve_xc7.v + loopbreaker_resolve.v output,
  BEFORE nextpnr has touched it). This script re-reads it directly with
  the stdlib json module for ground-truth logical connectivity -- see
  "Why the JSON re-read" below.

Why the JSON re-read (found the hard way, don't skip this): nextpnr-
xilinx's placer legalizer packs two independent LUT4s onto one physical
SLICE_LUTX bel whenever their combined distinct inputs fit within 5
shared pins (the O5/O6 "fracturable LUT6" mode -- see xilinx/arch_place.cc
around the lut5/lut6 pairing logic). When that happens, ctx.cells's
`.ports` for EITHER logical LUT4 reports the physical bel's FULL pin set,
which includes the OTHER (unrelated) packed-in cell's inputs too -- there
is no way to tell, from the post-route Python API alone, which A1-A6 pin
is "really mine" vs "my bel-mate's". Blindly walking every connected
A-port (as a first attempt here did) silently pulls in a foreign LUT's
fan-in, which can be an arbitrarily deep/slow unrelated path -- this
produced wrong (and internally inconsistent -- D bigger than R on every
single latch, an aggregate "208563 ps" total latency 1000x bigger than
the equivalent iCE40 number) results that LOOKED like real output but
weren't. The synth JSON's cell connections (I0-I3 -> net index) are
still logically exact at that point (pre-place, pre-fracture) and are
exactly what we need: for every LUT4, which of its <=4 real inputs is
port I0 vs I1 (CLAUDE.md's own probe-port convention refers to these
exact logical names). We then use the JSON's `netnames` section (each
net index's full alias list) to re-identify, in the POST-route Python
API, which specific physical A-port carries that SAME net by NAME -- a
robust match against fracturing and any nextpnr-internal LUT input pin
permutation (pin swapping for routability is legal and expected; it
preserves net identity, so name-matching survives it even though a fixed
"I0 always means A1" assumption does not).

Output: build/<top>/timing_xc7.json (same schema as postroute_audit.py's
timing.json, plus a "fdel" section per postroute_audit.py's own
convention).
"""
import json
import os
import re
import sys
import traceback

SLACK_PS = float(os.environ.get("PNR_SLACK_PS", "1000"))

# openXC7's Arch::getCellDelay currently omits DSP48E1 even though the Zynq-7
# SDF contains this arc. Use the database's worst unregistered A/B -> P value
# for the inferred configuration (AREG=BREG=MREG=PREG=0, MULTIPLY). This is
# the SDF max, not a guessed LUT equivalent; placed route delay is added below.
DSP48E1_COMB_MAX_PS = 5201.0
# Worst CARRY4 input-to-output max in the Zynq-7 CLB SDF. Using the bound for
# every active carry arc is conservative across the packing variants.
CARRY4_COMB_MAX_PS = 642.0


def load_true_connectivity(json_path):
    """From the pre-place synth JSON: for every LUT4 cell ending .u0.u0.u0,
    its REAL (non-constant) logical inputs as {port: net_index}, and a
    net_index -> {all known aliases} map from netnames."""
    d = json.load(open(json_path))
    # the design's top module is the only one NOT a library blackbox --
    # heuristically the one with the most cells (library modules have 0-2).
    mods = d["modules"]
    top = max(mods, key=lambda m: len(mods[m].get("cells", {})))
    mod = mods[top]

    true_in = {}     # combinational cell -> {logical input port: net_index}
    true_type = {}   # corresponding pre-pack cell type
    dsp_in = {}      # DSP cell name -> {bit-blasted input port: net_index}
    native_d = {}    # native latch cell name -> D net_index
    for cn, c in mod["cells"].items():
        if c["type"] in ("LDCE", "LDPE", "FDCE", "FDPE") and ".mem.bitcell[" in cn:
            v = c.get("connections", {}).get("D")
            if v and isinstance(v[0], int):
                native_d[cn] = v[0]
            continue
        if c["type"] == "DSP48E1":
            real = {}
            dirs = c.get("port_directions", {})
            for pn, bits in c.get("connections", {}).items():
                if dirs.get(pn) != "input":
                    continue
                for i, bit in enumerate(bits):
                    if isinstance(bit, int):
                        real[pn if len(bits) == 1 else f"{pn}{i}"] = bit
            dsp_in[cn] = real
            continue
        if c["type"] not in ({f"LUT{i}" for i in range(1, 7)} |
                             {"INV", "MUXF7", "MUXF8", "CARRY4"}):
            continue
        conns = c.get("connections", {})
        real = {}
        dirs = c.get("port_directions", {})
        for pn, bits in conns.items():
            if dirs.get(pn) != "input":
                continue
            for i, bit in enumerate(bits):
                if isinstance(bit, int):     # strings are tied constants
                    real[pn if len(bits) == 1 else f"{pn}{i}"] = bit
        true_in[cn] = real
        true_type[cn] = c["type"]

    # Internal side of each top-level output buffer. The final FUNC has no
    # redundant payload latch, so these are real bundled-data boundaries.
    output_in = {}
    for pname in ("o_req", "o_data"):
        p = mod.get("ports", {}).get(pname, {})
        if p.get("direction") != "output":
            continue
        for i, out_bit in enumerate(p.get("bits", [])):
            key = pname if len(p["bits"]) == 1 else f"{pname}[{i}]"
            for c in mod["cells"].values():
                if c["type"] != "OBUF" or out_bit not in c.get("connections", {}).get("O", []):
                    continue
                ib = c.get("connections", {}).get("I", [])
                if ib and isinstance(ib[0], int):
                    output_in[key] = ib[0]
                break

    net_names = {}    # net index -> set of all names it's known by
    for name, info in mod.get("netnames", {}).items():
        bits = info.get("bits", [])
        for i, bit in enumerate(bits):
            if not isinstance(bit, int):
                continue
            # a >1-bit netname is a bus; post-route bit-blasted names are
            # "<name>[<i>]" (nextpnr JSON import splits every multi-bit
            # port/wire into individual single-bit nets on read), a
            # single-bit netname stays bare.
            alias = name if len(bits) == 1 else f"{name}[{i}]"
            net_names.setdefault(bit, set()).add(alias)

    return true_in, true_type, dsp_in, native_d, output_in, net_names


def main(ctx):
    dev = str(ctx.getChipName()) if hasattr(ctx, "getChipName") else "unknown"
    json_path = os.environ["PNR_SYNTH_JSON"]
    (true_in, true_type, dsp_in, native_d, output_in,
     net_names) = load_true_connectivity(json_path)

    # ---- build post-route maps -------------------------------------
    cell_by_name = {}
    cell_type = {}
    for kv in ctx.cells:
        cn = str(kv.first)
        cell_by_name[cn] = kv.second
        cell_type[cn] = str(kv.second.type)

    driver = {}           # net name -> (cell name, out port)
    cell_out = {}         # cell name -> {out port: net name}
    net_users = {}        # net name -> [(cell name, input port)]
    raw_cell_in = {}      # cell name -> {A-port: net name}  (bel-wide, may
                           # include a fractured bel-mate's foreign inputs)
    for kv in ctx.nets:
        nname = str(kv.first)
        net = kv.second
        drv = net.driver
        if drv.cell is not None:
            driver[nname] = (str(drv.cell.name), str(drv.port))
            cell_out.setdefault(str(drv.cell.name), {})[str(drv.port)] = nname
        for u in net.users:
            cn, pn = str(u.cell.name), str(u.port)
            raw_cell_in.setdefault(cn, {})[pn] = nname
            net_users.setdefault(nname, []).append((cn, pn))

    # ---- resolve TRUE logical inputs per cell, by net-name matching -----
    # cell_in[cn] = {logical_port ("I0".."I3"): (physical_A_port, net_name)}
    resolved_in = {}
    unresolved = 0
    for cn, ports in true_in.items():
        packed_cn = cn
        if packed_cn not in raw_cell_in and true_type.get(cn) == "CARRY4":
            candidates = [x for x in raw_cell_in
                          if x.startswith(cn + "$split$") and
                          x.endswith("$PACKED_CARRY4$")]
            if len(candidates) == 1:
                packed_cn = candidates[0]
        if packed_cn not in raw_cell_in:
            unresolved += len(ports)
            continue
        got = {}
        for lp, net_idx in ports.items():
            aliases = net_names.get(net_idx, set())
            # CARRY4's packed CI pin is named CIN. Other carry pins retain
            # their bit-blasted names. LUT pins may be freely permuted and
            # fractured, so those continue to resolve solely by net identity.
            expected = "CIN" if true_type.get(cn) == "CARRY4" and lp == "CI" else lp
            if true_type.get(cn) == "CARRY4":
                nn = raw_cell_in[packed_cn].get(expected)
                if nn is not None and nn in aliases:
                    got[lp] = (expected, nn)
                    continue
                unresolved += 1
                continue
            for ap, nn in raw_cell_in[packed_cn].items():
                if nn in aliases:
                    got[lp] = (ap, nn)
                    break
            else:
                unresolved += 1
        resolved_in[packed_cn] = got
    print(f"  [xc7 audit] resolved logical inputs for {len(resolved_in)} "
          f"combinational cells ({unresolved} inputs unmatched)")

    # DSP ports are neither fracturable nor swappable. nextpnr bit-blasts
    # A[0] to A0 (and similarly for B/P), so require both the exact physical
    # port and the exact logical net identity. This also prevents a shared
    # A/B operand net from accidentally matching the wrong DSP input.
    resolved_dsp_in = {}
    unresolved_dsp = 0
    for cn, ports in dsp_in.items():
        got = {}
        for lp, net_idx in ports.items():
            nn = raw_cell_in.get(cn, {}).get(lp)
            if nn is not None and nn in net_names.get(net_idx, set()):
                got[lp] = (lp, nn)
            else:
                unresolved_dsp += 1
        resolved_dsp_in[cn] = got
    print(f"  [xc7 audit] resolved inputs for {len(resolved_dsp_in)} "
          f"DSP48E1 cells ({unresolved_dsp} inputs unmatched)")

    # Native LDCE/LDPE latch D pins are not fractured or permuted, but match
    # by net identity anyway so this uses the same robust pre/post-route
    # correspondence as LUT inputs.
    resolved_native_d = {}
    for cn, net_idx in native_d.items():
        aliases = net_names.get(net_idx, set())
        for ap, nn in raw_cell_in.get(cn, {}).items():
            if ap == "D" and nn in aliases:
                resolved_native_d[cn] = (ap, nn)
                break
    print(f"  [xc7 audit] resolved D inputs for {len(resolved_native_d)}/"
          f"{len(native_d)} native payload latches")

    resolved_output = {}
    all_routed_nets = set(driver) | set(net_users)
    for key, net_idx in output_in.items():
        matches = sorted(net_names.get(net_idx, set()) & all_routed_nets)
        if matches:
            resolved_output[key] = matches[0]
    print(f"  [xc7 audit] resolved {len(resolved_output)}/"
          f"{len(output_in)} output-boundary nets")

    def route_ps(ap_cn, ap, nn):
        ps = ctx.getRouteDelayPs(nn, ap_cn, ap)
        return ps if ps >= 0.0 else 0.0

    def arc_ps(cn, from_ap, to_port):
        cell = cell_by_name[cn]
        found, ps = ctx.getCellDelay(cell, from_ap, to_port)
        return float(ps) if found else None

    def out_port(cn):
        for op in ("O5", "O6"):
            if op in cell_out.get(cn, {}):
                return op
        return None

    def is_source(cname, ctype):
        if ctype != "SLICE_LUTX" or not cname.endswith(".u0"):
            return False
        return ".hs." in cname or ".mem." in cname or "selsr" in cname

    memo, onstack = {}, set()
    fdel_touch = set()
    dsp_arc_errors = set()
    comb_arc_errors = set()

    def arrival(nname):      # ps at the OUTPUT of nname's driver
        if nname in memo:
            fdel_touch.update(memo[nname][1])
            return memo[nname][0]
        if nname not in driver:
            memo[nname] = (0.0, frozenset())
            return 0.0
        cn, drv_port = driver[nname]
        ct = cell_type.get(cn, "")
        is_lut = ct == "SLICE_LUTX"
        is_dsp = ct == "DSP48E1_DSP48E1"
        # BUFGCTRL is deliberately TRANSPARENT (same policy as the
        # pre-route audit's zero-weight BUFG): alib_ram's explicit strobe
        # buffer must not truncate the strobe-arrival cone, or the RAM
        # boundary check below is vacuous (this exact truncation hid the
        # pre-BUFG-fix bug -- see CLAUDE.md's RAM-strobe gotcha).
        is_comb = is_lut or ct in {"CARRY4", "F7MUX", "F8MUX", "F9MUX",
                                   "SELMUX2_1", "BUFGCTRL"}
        if ((not is_comb and not is_dsp) or is_source(cn, ct) or
                cn in onstack):
            memo[nname] = (0.0, frozenset())
            return 0.0
        onstack.add(cn)
        local = set()
        # search, not match: inside a wrapper top (zynq/*_ps_top.v) every
        # core instance is prefixed (knapsack_i.fdel15....)
        m = re.search(r"(?:^|\.)fdel(\d+)\.", cn)
        if m:
            local.add(m.group(1))
        best = 0.0
        if is_lut and "CLK" in raw_cell_in.get(cn, {}):
            # Distributed-RAM-mode SLICE_LUTX (RAM32M fragment): its
            # combinational READ is A*->O only. The write-port pins
            # (CLK/WE/WA*/DI*) must NOT be walked as if they fed the
            # read output -- the raw-pin fallback below would otherwise
            # drag the whole write-address/merge-tree cone into every
            # read-data arrival. The write port itself is audited as a
            # capture boundary in the RAM-strobe section of main().
            inputs = {ap: (ap, inn)
                      for ap, inn in raw_cell_in.get(cn, {}).items()
                      if ap.startswith("A")}
        elif is_dsp:
            inputs = resolved_dsp_in.get(cn, {})
        elif ct == "CARRY4":
            # Carry packing rewrites/splits the logical cell name, but its
            # physical pins are not fracturable; the post-pack port map is
            # therefore exact and safer than trying to reconstruct the split.
            inputs = {ap: (ap, inn)
                      for ap, inn in raw_cell_in.get(cn, {}).items()}
        else:
            inputs = resolved_in.get(cn, {})
            if not inputs:
                # Rare pack-created XOR/LUT helpers have no pre-pack logical
                # counterpart. Walking every physical input is conservative;
                # unlike using it for all fractured LUTs, this fallback is
                # confined to cells for which no exact mapping exists.
                inputs = {ap: (ap, inn)
                          for ap, inn in raw_cell_in.get(cn, {}).items()}
        found_arc = False
        for lp, (ap, inn) in inputs.items():
            arc = (DSP48E1_COMB_MAX_PS if is_dsp and
                   (ap.startswith("A") or ap.startswith("B")) and
                   drv_port.startswith("P") else
                   CARRY4_COMB_MAX_PS if ct == "CARRY4" else
                   arc_ps(cn, ap, drv_port))
            if ct == "BUFGCTRL":
                if ap != "I0":
                    continue           # CE/S selects: constants here
                if arc is None:
                    arc = 0.0          # no arc in db: conservative for R
            if arc is None and is_lut and "CLK" in raw_cell_in.get(cn, {}):
                # RAM-mode read arc may be absent from the db; use the
                # worst CLB comb bound (conservative on the data side).
                arc = CARRY4_COMB_MAX_PS
            if arc is None:
                continue
            found_arc = True
            a = arrival(inn) + route_ps(cn, ap, inn) + arc
            best = max(best, a)
        if is_dsp and not found_arc:
            dsp_arc_errors.add(f"{cn}:{drv_port}")
        if is_comb and not found_arc:
            comb_arc_errors.add(f"{cn}:{drv_port}")
        onstack.discard(cn)
        memo[nname] = (best, frozenset(local))
        fdel_touch.update(local)
        return best

    def probe(cn, logical_port):
        """arrival at the input named `logical_port` (e.g. I0) of cell cn,
        using the RESOLVED (fracturing-safe) net -- this is the number
        CLAUDE.md's probe-port convention actually refers to."""
        r = resolved_in.get(cn, {}).get(logical_port)
        if r is None:
            return None
        ap, nn = r
        return arrival(nn) + route_ps(cn, ap, nn)

    def probe_native_d(cn):
        r = resolved_native_d.get(cn)
        if r is None:
            return None
        ap, nn = r
        return arrival(nn) + route_ps(cn, ap, nn)

    def data_is_wired(nn):
        if nn not in driver:
            return True
        dcn, _ = driver[nn]
        dct = cell_type.get(dcn, "")
        return dct == "SLICE_FFX" or is_source(dcn, dct)

    def boundary_arrival(nn):
        """Arrival at the internal input of the packed output buffer."""
        base = arrival(nn)
        sinks = []
        for cn, ap in net_users.get(nn, []):
            if cell_type.get(cn, "").endswith("OUTBUF"):
                sinks.append(base + route_ps(cn, ap, nn))
        return max(sinks) if sinks else base

    def boundary_request_arrival(nn):
        """Arrival of the final controller's forward request event.

        `arrival()` correctly stops at handshake C-elements for internal
        latch checks.  The last such C-element is itself part of the module
        output request path, though, so use its logical I1 (delayed forward
        request) arc instead of treating Q as time zero.  I0 is acknowledge,
        I2 reset and I3 feedback in alib_hlatch's controller LUT.
        """
        base = None
        if nn in driver:
            cn, drv_port = driver[nn]
            ct = cell_type.get(cn, "")
            if is_source(cn, ct):
                r = resolved_in.get(cn, {}).get("I1")
                if r is not None:
                    ap, inn = r
                    arc = arc_ps(cn, ap, drv_port)
                    if arc is None:
                        comb_arc_errors.add(f"{cn}:{drv_port}")
                    else:
                        base = (arrival(inn) + route_ps(cn, ap, inn) + arc)
        if base is None:
            base = arrival(nn)
        sinks = []
        for cn, ap in net_users.get(nn, []):
            if cell_type.get(cn, "").endswith("OUTBUF"):
                sinks.append(base + route_ps(cn, ap, nn))
        return max(sinks) if sinks else base

    # ---- per-latch probes: I0 = request, I1 = data bit (CLAUDE.md) ------
    latches = {}
    for cn in resolved_in:
        m = re.match(r"(.*)\.engate\.u0\.u0\.u0$", cn)
        if m:
            latches.setdefault(m.group(1), {})["req"] = cn
        m = re.match(r"(.*)\.mem\.bitcell\[\d+\]\.u0\.u0\.u0$", cn)
        if m:
            latches.setdefault(m.group(1), {}).setdefault("dat", []).append(cn)
    for cn in resolved_native_d:
        m = re.match(r"(.*)\.mem\.bitcell\[\d+\]\.native_(?:zero|one)\.native$",
                     cn)
        if m:
            latches.setdefault(m.group(1), {}).setdefault("native_dat", []).append(cn)

    report = {"device": dev, "pass": True, "slack_ps": SLACK_PS,
              "latches": {}, "fdel_on_path": {}}
    output_unmatched = len(output_in) - len(resolved_output)
    if unresolved_dsp or output_unmatched:
        report["pass"] = False
        report["connectivity_error"] = {
            "dsp_inputs_unmatched": unresolved_dsp,
            "output_nets_unmatched": output_unmatched,
        }
    if unresolved:
        report["logical_inputs_unmatched_after_packing"] = unresolved
    for lname, L in sorted(latches.items()):
        if "req" not in L or ("dat" not in L and "native_dat" not in L):
            continue
        fdel_touch.clear()
        R = probe(L["req"], "I0")
        if R is None:
            continue
        report["fdel_on_path"][lname] = sorted(fdel_touch)
        D, wired = 0.0, True
        for cn in L.get("dat", []):
            d = probe(cn, "I1")
            if d is None:
                continue
            r = resolved_in.get(cn, {}).get("I1")
            if r is not None:
                _, inn = r
                if not data_is_wired(inn):
                    wired = False
            D = max(D, d)
        for cn in L.get("native_dat", []):
            d = probe_native_d(cn)
            if d is None:
                continue
            _, inn = resolved_native_d[cn]
            if not data_is_wired(inn):
                wired = False
            D = max(D, d)
        ok = wired or (R >= D + SLACK_PS)
        report["latches"][lname] = {"R_ps": R, "D_ps": D, "wired": wired, "ok": ok}
        report["pass"] &= ok
        print(f"  postroute-xc7 {lname:<12} R={R:8.0f}ps D={D:8.0f}ps "
              f"{'ok(wired)' if wired else ('ok' if ok else 'FAIL')}")

    # Final FUNC output boundary. It deliberately has no data latch, so the
    # request chain must cover the combinational o_data cone all the way to
    # the internal side of the output buffers.
    req_nn = resolved_output.get("o_req")
    dat_nn = [nn for key, nn in resolved_output.items()
              if key == "o_data" or key.startswith("o_data[")]
    if req_nn is not None and dat_nn:
        fdel_touch.clear()
        R = boundary_request_arrival(req_nn)
        report["fdel_on_path"]["$output"] = sorted(fdel_touch)
        D = max(boundary_arrival(nn) for nn in dat_nn)
        wired = all(data_is_wired(nn) for nn in dat_nn)
        ok = wired or (R >= D + SLACK_PS)
        report["latches"]["$output"] = {
            "R_ps": R, "D_ps": D, "wired": wired, "ok": ok,
        }
        report["pass"] &= ok
        print(f"  postroute-xc7 {'$output':<12} R={R:8.0f}ps "
              f"D={D:8.0f}ps "
              f"{'ok(wired)' if wired else ('ok' if ok else 'FAIL')}")

    # ---- RAM strobe capture boundaries (post-route) ----------------------
    # COVERAGE-GAP FIX (2026-07-21, found on silicon): this script only
    # audited hlatches; the `mem` RAM boundary (RAM32M write port + the
    # strobe-clocked read-capture FFs) was checked ONLY by the pre-route
    # hop-model audit -- exactly the check class BRINGUP.md documents as
    # insufficient against nextpnr-xilinx's multi-ns routing detours on
    # wide buses. A knapsack_bench placement (SEED=4) passed every gate
    # and returned deterministically wrong dp[]-corrupted results on the
    # EBAZ4205. Rule here mirrors audit_bundling's RAM_PORTS semantics
    # with real routed ps: the strobe (BUFG output) must arrive
    # SLACK_PS after every bundled write-port pin (WE/WA*/DI*), every
    # read address pin (A* -- captured by the same strobe edge at the
    # FDREs), and every strobe-clocked FF's D/CE/SR cone.
    strobe_bufgs = {}
    for cn, ct in cell_type.items():
        if ct != "BUFGCTRL":
            continue
        inn = raw_cell_in.get(cn, {}).get("I0")
        if inn is None or inn not in driver:
            continue
        dcn = driver[inn][0]
        if cell_type.get(dcn, "") == "SLICE_LUTX":   # comb-driven = strobe
            out_net = cell_out.get(cn, {}).get("O")
            if out_net is not None:
                strobe_bufgs[cn] = out_net

    for bufg_cn, out_net in sorted(strobe_bufgs.items()):
        fdel_touch.clear()
        R_base = arrival(out_net)      # BUFGCTRL is transparent in arrival()
        group = re.sub(r"\.sgb$", "", bufg_cn)
        worst = None                   # (slack, sink label, R, D)
        for scn, sap in net_users.get(out_net, []):
            sct = cell_type.get(scn, "")
            R = R_base + route_ps(scn, sap, out_net)
            pins = raw_cell_in.get(scn, {})
            if sct == "SLICE_LUTX" and sap == "CLK":
                dat = {ap: nn for ap, nn in pins.items() if ap != "CLK"}
            elif sct == "SLICE_FFX" and sap == "CK":
                dat = {ap: nn for ap, nn in pins.items() if ap != "CK"}
            else:
                continue
            D = 0.0
            for ap, nn in dat.items():
                D = max(D, arrival(nn) + route_ps(scn, ap, nn))
            slack = R - D
            if worst is None or slack < worst[0]:
                worst = (slack, scn, R, D)
        if worst is None:
            continue
        slack, scn, R, D = worst
        ok = R >= D + SLACK_PS
        # Empirical calibration (EBAZ4205, 2026-07-21): a knapsack_bench
        # placement at +1008 ps RAM slack FAILED on silicon (deterministic
        # dp[] corruption) while +1151 ps works -- the 1000 ps latch slack
        # is evidently borderline for this edge-triggered capture class.
        # Flag anything under 1.5x so a marginal build gets hardware-
        # verified instead of trusted.
        marginal = ok and slack < 1.5 * SLACK_PS
        report["latches"][f"$ram:{group}"] = {
            "R_ps": R, "D_ps": D, "wired": False, "ok": ok,
            "worst_sink": scn, "marginal": marginal,
        }
        report["fdel_on_path"][f"$ram:{group}"] = sorted(fdel_touch)
        report["pass"] &= ok
        print(f"  postroute-xc7 $ram:{group} R={R:8.0f}ps D={D:8.0f}ps "
              f"{'MARGINAL-ok' if marginal else ('ok' if ok else 'FAIL')} "
              f"(worst sink {scn})")
        if marginal:
            print(f"  [xc7 audit] WARNING $ram:{group} slack {slack:.0f} ps "
                  f"is in the band where a silicon failure has been "
                  f"observed (+1008 ps failed, +1151 ps passed) -- "
                  f"hardware-verify this build before trusting results")

    if dsp_arc_errors:
        report["pass"] = False
        report["dsp_arc_errors"] = sorted(dsp_arc_errors)
        print("  [xc7 audit] ERROR no timing arc for DSP outputs: " +
              ", ".join(sorted(dsp_arc_errors)))
    if comb_arc_errors:
        report["pass"] = False
        report["comb_arc_errors"] = sorted(comb_arc_errors)
        print("  [xc7 audit] ERROR no timing arc/connectivity for "
              "combinational outputs: " +
              ", ".join(sorted(comb_arc_errors)))

    total_R = sum(L["R_ps"] for L in report["latches"].values())
    report["total_R_ps"] = total_R
    print(f"  rough per-call latency (sum R_ps, not a strict crit path): "
          f"{total_R:.0f} ps")

    # ---- fdel matched-delay chains (for tests/tighten.py) ----------------
    # Same shared-prefix-cancels trick as postroute_audit.py: chain_ps =
    # arrival(chain output net) - arrival(chain input net), using the SAME
    # fracturing-safe resolved_in connectivity as everything above.
    fdel_stages = {}
    for cn in resolved_in:
        m = re.search(r"(?:^|\.)fdel(\d+)\.stage\[(\d+)\]\.u0\.u0\.u0$", cn)
        if m:
            fdel_stages.setdefault(m.group(1), {})[int(m.group(2))] = cn

    report["fdel"] = {}
    for K, stages in sorted(fdel_stages.items(), key=lambda kv: int(kv[0])):
        T = max(stages) + 1
        first_cn, last_cn = stages.get(0), stages.get(T - 1)
        if first_cn is None or last_cn is None:
            continue
        # stage 0's I0 and I1 are both the chain's external input `i`
        r = resolved_in.get(first_cn, {}).get("I0") or resolved_in.get(first_cn, {}).get("I1")
        outp = out_port(last_cn)
        out_net = cell_out.get(last_cn, {}).get(outp) if outp else None
        if r is None or out_net is None:
            continue
        _, in_net = r
        chain_ps = max(0.0, arrival(out_net) - arrival(in_net))
        report["fdel"][K] = {"T": T, "chain_ps": chain_ps,
                              "per_hop_ps": chain_ps / T if T else 0.0}

    out = os.environ.get("PNR_TIMING_OUT", "timing_xc7.json")
    json.dump(report, open(out, "w"), indent=1)
    print(f"  postroute-xc7 audit: {'PASS' if report['pass'] else 'FAIL'} "
          f"-> {out}")
    if not report["pass"]:
        sys.exit(1)


try:
    main(ctx)                                    # noqa: F821 (nextpnr global)
except SystemExit:
    raise
except Exception:
    traceback.print_exc()
    json.dump({"pass": False, "error": traceback.format_exc()},
              open(os.environ.get("PNR_TIMING_OUT", "timing_xc7.json"), "w"))
    sys.exit(1)
