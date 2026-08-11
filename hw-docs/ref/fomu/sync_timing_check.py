#!/usr/bin/env python3
"""Post-route SYNC-domain timing check -- runs INSIDE nextpnr via
--post-route, like tests/postroute_audit.py (and reuses its discovered
conventions: _LC name stripping, .first/.second map iteration, the
getCellDelay binding patch).

Why this exists: the fomu builds need --timing-allow-fail because the
harness's clocked glue forms giant register-to-register cones straight
through the clockless gcd core, which nextpnr (correctly but
irrelevantly) fails at any frequency. But that flag also silences REAL
timing failures in the genuinely synchronous logic -- above all the
vendored USB-CDC core, which must close at 48 MHz or enumeration
breaks. nextpnr's own report can't distinguish the two (the false
paths dominate every summary), so this script re-does the max-arrival
walk itself, cutting every path at cells inside the async core
(default: instance names starting with "dut."). What's left is exactly
the honest synchronous timing graph: USB core + harness counters/FSMs.

Model: arrival at a net = clk-to-out of its driving DFF (or 0 at a cut
/ non-LC source), plus route + cell arcs through combinational LCs.
Endpoint check: arrival + route + SETUP_PS <= PERIOD_PS at every input
of every clocked LC. SETUP_PS=1000 is deliberately generous (real LC
setup+LUT is a few hundred ps); we're checking for multi-ns blowups,
not shaving margins.

Env knobs: SYNC_PERIOD_PS (default 20833 = 48 MHz), SYNC_SETUP_PS,
SYNC_EXCLUDE (regex over stripped cell names, default ^dut\\.),
SYNC_TIMING_OUT (json report path).
"""
import json
import os
import re
import sys
import traceback

PERIOD_PS = float(os.environ.get("SYNC_PERIOD_PS", "20833"))
SETUP_PS = float(os.environ.get("SYNC_SETUP_PS", "1000"))
CLKQ_FALLBACK_PS = 700.0
EXCLUDE = re.compile(os.environ.get("SYNC_EXCLUDE", r"^dut\."))

LC_IN_PORTS = ("I0", "I1", "I2", "I3", "CIN")
ENDPOINT_PORTS = ("I0", "I1", "I2", "I3", "CIN", "CEN", "SR")


def strip_lc(cname, ctype):
    if ctype == "ICESTORM_LC" and cname.endswith("_LC"):
        return cname[:-len("_LC")]
    return cname


def main(ctx):
    cell_by_name, cell_type = {}, {}
    for kv in ctx.cells:
        cn = str(kv.first)
        cell_by_name[cn] = kv.second
        cell_type[cn] = str(kv.second.type)

    driver, cell_in, users = {}, {}, {}
    for kv in ctx.nets:
        nname = str(kv.first)
        net = kv.second
        drv = net.driver
        if drv.cell is not None:
            driver[nname] = (str(drv.cell.name), str(drv.port))
        for u in net.users:
            cn, pn = str(u.cell.name), str(u.port)
            cell_in.setdefault(cn, {})[pn] = nname
            users[(cn, pn)] = (net, u)

    clocked = {cn for cn in cell_by_name if "CLK" in cell_in.get(cn, {})}
    rams = {cn for cn in cell_by_name if cell_type[cn] == "ICESTORM_RAM"}

    def route_ps(cn, pn):
        net, u = users[(cn, pn)]
        return ctx.getDelayNS(ctx.getNetinfoRouteDelay(net, u)) * 1000.0

    def arc_ps(cn, from_port, to_port):
        found, dq = ctx.getCellDelay(cell_by_name[cn], from_port, to_port)
        if not found:
            return None
        return ctx.getDelayNS(dq.maxDelay()) * 1000.0

    memo, onstack = {}, set()

    def arrival(nname):
        """Worst-case ps at the output pin driving net `nname`."""
        if nname in memo:
            return memo[nname]
        if nname not in driver:
            memo[nname] = 0.0
            return 0.0
        cn, dp = driver[nname]
        ct = cell_type.get(cn, "")
        base = strip_lc(cn, ct)
        if EXCLUDE.search(base):
            memo[nname] = 0.0          # false-path cut: async core
            return 0.0
        if ct == "ICESTORM_RAM":
            a = arc_ps(cn, "RCLK", dp) or CLKQ_FALLBACK_PS * 2
            memo[nname] = a
            return a
        if ct != "ICESTORM_LC":
            memo[nname] = 0.0          # IO pads, SB_GB, RGB driver, ...
            return 0.0
        if cn in clocked and dp == "O":
            a = arc_ps(cn, "CLK", "O") or CLKQ_FALLBACK_PS
            memo[nname] = a
            return a
        if cn in onstack:              # comb loop (shouldn't survive the cut)
            memo[nname] = 0.0
            return 0.0
        onstack.add(cn)
        best = 0.0
        for pn in LC_IN_PORTS:
            inn = cell_in.get(cn, {}).get(pn)
            if inn is None:
                continue
            arc = arc_ps(cn, pn, dp)
            if arc is None:
                continue
            best = max(best, arrival(inn) + route_ps(cn, pn) + arc)
        onstack.discard(cn)
        memo[nname] = best
        return best

    endpoints = []
    for cn in sorted(clocked | rams):
        ct = cell_type[cn]
        base = strip_lc(cn, ct)
        if EXCLUDE.search(base):
            continue
        ports = ENDPOINT_PORTS if ct == "ICESTORM_LC" else tuple(
            p for p in cell_in.get(cn, {})
            if p not in ("RCLK", "WCLK", "RCLKE", "WCLKE"))
        for pn in ports:
            inn = cell_in.get(cn, {}).get(pn)
            if inn is None:
                continue
            a = arrival(inn) + route_ps(cn, pn)
            slack = PERIOD_PS - SETUP_PS - a
            endpoints.append((slack, a, base, pn))

    endpoints.sort()
    worst = endpoints[:12]
    fmax_mhz = (1e6 / (endpoints[0][1] + SETUP_PS)) if endpoints else 0.0
    # Acceptance: strict PERIOD_PS closure by default. SYNC_MIN_FMAX_MHZ
    # relaxes it to an empirical floor -- used for the fomu USB builds,
    # where the vendored USB-CDC core cannot close 48 MHz on the UP5K's
    # slow speed grade under nextpnr's worst-case model, yet is proven
    # on silicon (typ. corner is ~1.5x faster than model): the minimal
    # UART-only build enumerated and streamed fine at a modeled
    # 33.8 MHz, while instrumented builds at <=31.4 MHz failed. The
    # floor encodes "no slower than the slowest configuration ever
    # demonstrated to work on this exact board".
    min_fmax = os.environ.get("SYNC_MIN_FMAX_MHZ", "")
    if min_fmax:
        ok = not endpoints or fmax_mhz >= float(min_fmax)
        crit = f"floor {float(min_fmax):.1f} MHz"
    else:
        ok = not endpoints or endpoints[0][0] >= 0.0
        crit = f"period {PERIOD_PS:.0f}ps"

    print(f"  synccheck {len(endpoints)} endpoints, {crit},"
          f" est fmax {fmax_mhz:.1f} MHz -- {'PASS' if ok else 'FAIL'}")
    for slack, a, base, pn in worst:
        print(f"  synccheck {'ok  ' if slack >= 0 else 'FAIL'} "
              f"slack={slack:8.0f}ps arr={a:8.0f}ps  {base}.{pn}")

    out = os.environ.get("SYNC_TIMING_OUT", "")
    if out:
        json.dump({"pass": ok, "period_ps": PERIOD_PS,
                   "setup_ps": SETUP_PS, "est_fmax_mhz": fmax_mhz,
                   "worst": [{"slack_ps": s, "arrival_ps": a,
                              "cell": c, "port": p}
                             for s, a, c, p in worst]},
                  open(out, "w"), indent=1)
    if not ok:
        sys.exit(1)


try:
    main(ctx)                                   # noqa: F821 (nextpnr global)
except SystemExit:
    raise
except Exception:
    traceback.print_exc()
    sys.exit(1)
