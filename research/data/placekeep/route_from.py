# route_from.py -- nextpnr-xilinx --pre-route script: keep the previous route's ROUTES (build_bench.sh BD_ROUTE_FROM).
#
# Runs after placement, before routing, in the same interpreter as cells/hw/place_from.py (the --pre-place script),
# whose `match` (current cell name -> the previous route's name of the same cell) it reuses.  A net is bound to the
# previous route's wires and pips (its ROUTING attribute in the previous routed JSON, BD_ROUTE_FROM) at STRENGTH_LOCKED,
# so the router leaves it, when:
#   * its driver is a kept cell (same bel as before) on the same port, and the previous net on that port had a ROUTING;
#   * every sink is a kept cell, and the previous net had exactly these sinks (cell, port) -- a LUT's input pins are
#     the previous route's (place_from.py restored them);
#   * it is not a constant (the packer's GND / VCC nets, routed by the constant router) nor a global clock;
#   * every wire and pip of the old route is free.
# Every other net (a raised line's, its neighbours', the harness's if it was re-placed) is routed by the router.
# Why: with the placement kept the router still re-routes every net, and the margins of constraints none of whose
# lines changed still moved (xorshift s1 it 5 -> it 6, everything placed as before: median |d| 122 ps, p95 +930).
# Prints "route_from: locked N of M nets (...)".
import json, os, re

src = os.environ["BD_ROUTE_FROM"]
with open(src) as f:
    d = json.load(f)
top = [m for m in d["modules"].values() if any("NEXTPNR_BEL" in c.get("attributes", {}) for c in m.get("cells", {}).values())][0]
pcells = top["cells"]
bel_prev = {n: c["attributes"].get("NEXTPNR_BEL") for n, c in pcells.items()}
routing = {}                          # bit -> ROUTING string of the net routed on it
for nn, v in top.get("netnames", {}).items():
    r = v.get("attributes", {}).get("ROUTING")
    if r and v.get("bits"):
        routing[v["bits"][0]] = r
drv_bit, sinks_of = {}, {}           # (cell, port) -> bit of its output; bit -> {(cell, port)} of its inputs
for n, c in pcells.items():
    for p, v in c.get("connections", {}).items():
        if not v or not isinstance(v[0], int):
            continue
        if c.get("port_directions", {}).get(p) == "output":
            drv_bit[(n, p)] = v[0]
        else:
            sinks_of.setdefault(v[0], set()).add((n, p))
try:
    match                              # from place_from.py
except NameError:
    match = {}
fr_in, fr_out = os.environ.get("BD_ROUTE_FR_IN"), os.environ.get("BD_ROUTE_FR_OUT")
if fr_in and fr_out:
    # --fixed-routes mode: nextpnr's own pinned-route loader (it names a pip by tile and index, so the site pips that
    # getPipByName cannot parse are kept too).  The previous route's dump (--write-fixed-routes) is filtered to the
    # nets this script would lock, renamed to this netlist's net names (by their driver), and written where
    # --fixed-routes reads it, before route() runs.  Global clocks are kept whatever their sinks (the loader leaves the
    # clock tree to the file: "left to fixed-routes (golden distribution)") and the last mile to the router.
    bit_of = {}
    for nn, v in top.get("netnames", {}).items():
        if v.get("bits") and isinstance(v["bits"][0], int):
            bit_of.setdefault(nn, v["bits"][0])
    drv_of_bit = {b: k for k, b in drv_bit.items()}
    rev = {v: k for k, v in match.items()}
    cells_now = {nm: c for nm, c in ctx.cells}
    pips = {}
    with open(fr_in) as f:
        for ln in f:
            if ln.startswith("#") or not ln.strip():
                continue
            nn, pp = ln.rsplit(" ", 1)
            pips.setdefault(nn, []).append(pp.strip())
    out, why = [], {}
    for nn, pl in pips.items():
        b = bit_of.get(nn)
        dk = drv_of_bit.get(b) if b is not None else None
        if dk is None:
            why["no driver"] = why.get("no driver", 0) + 1
            continue
        k, port = dk
        c = rev.get(k)
        cell = cells_now.get(c) if c else None
        if cell is None or cell.bel is None or str(cell.bel) != bel_prev.get(k):
            why["driver not kept"] = why.get("driver not kept", 0) + 1
            continue
        pi = next((q for pn, q in cell.ports if pn == port), None)
        if pi is None or pi.net is None:
            why["no net now"] = why.get("no net now", 0) + 1
            continue
        net = pi.net
        clock = any("GCLK" in x or "BUFG" in x or "HCLK" in x or "CLK_HROW" in x for x in pl)
        if not clock:
            users = set()
            ok = True
            for u in net.users:
                kk = match.get(u.cell.name) if u.cell is not None else None
                if kk is None or u.cell.bel is None or str(u.cell.bel) != bel_prev.get(kk):
                    ok = False
                    break
                users.add((kk, u.port))
            if not ok or users != sinks_of.get(b, set()):
                why["sinks differ"] = why.get("sinks differ", 0) + 1
                continue
        out.extend("%s %s\n" % (net.name, x) for x in pl)
        why["kept" if not clock else "kept (clock)"] = why.get("kept" if not clock else "kept (clock)", 0) + 1
    with open(fr_out, "w") as f:
        f.write("# nextpnr-xilinx fixed-routes: <net> <tile>/<src_idx>.<dst_idx>\n")
        f.writelines(out)
    print("route_from: --fixed-routes file %s: %d pips of %d previous nets (%s)"
          % (fr_out, len(out), len(pips), ", ".join("%s %d" % kv for kv in sorted(why.items()))))
else:
 locked = considered = 0
 why = {}
 for nname, net in ctx.nets:
     considered += 1
     dr = net.driver
     if dr.cell is None:
         why["no driver"] = why.get("no driver", 0) + 1
         continue
     if nname.startswith("$PACKER_") or "GND" in nname and nname.startswith("$") or nname.endswith("_bufg") or \
             nname in ("fclkclk[0]",):
         why["constant / clock"] = why.get("constant / clock", 0) + 1
         continue
     dk = match.get(dr.cell.name)
     if dk is None or dr.cell.bel is None or str(dr.cell.bel) != bel_prev.get(dk):
         why["driver not kept"] = why.get("driver not kept", 0) + 1
         continue
     bt = drv_bit.get((dk, dr.port))
     if bt is None or bt not in routing:
         why["no previous route"] = why.get("no previous route", 0) + 1
         continue
     users = set()
     ok = True
     for u in net.users:
         k = match.get(u.cell.name) if u.cell is not None else None
         if k is None or u.cell.bel is None or str(u.cell.bel) != bel_prev.get(k):
             ok = False
             break
         users.add((k, u.port))
     if not ok or users != sinks_of.get(bt, set()):
         why["sinks differ"] = why.get("sinks differ", 0) + 1
         continue
     r = routing[bt].split(";")
     trip = [(r[i], r[i + 1]) for i in range(0, len(r) - 2, 3)]
     # site-level wires and pips (SITEWIRE/.., SITEPIP/.., and the site <-> tile pips) do not parse back through
     # getPipByName in this build (assertion pip != PipId(), unordered_map::at): only the interconnect is bound, and
     # the router completes the site hops on the net's own locked wires
     trip = [(w, pp) for w, pp in trip if "SITE" not in w and "SITE" not in pp]
     if any("GCLK" in w or "HCLK" in w or "BUFG" in w for w, _ in trip):
         why["constant / clock"] = why.get("constant / clock", 0) + 1
         continue
     bound_w, bound_p, fail = [], [], False
     for w, p in trip:
         try:
             if p == "":
                 if not ctx.checkWireAvail(w):
                     fail = True
                     break
                 ctx.bindWire(w, net, STRENGTH_LOCKED)
                 bound_w.append(w)
             else:
                 if not ctx.checkPipAvail(p):
                     fail = True
                     break
                 ctx.bindPip(p, net, STRENGTH_LOCKED)
                 bound_p.append(p)
         except Exception as e:        # a name this build does not know: leave the net to the router
             fail = True
             why["bind error"] = why.get("bind error", 0) + 1
             if why["bind error"] <= 3:
                 print("route_from: bind error on %s at %r / %r: %s" % (nname, w, p, e))
             break
     if fail:
         for p in bound_p:
             ctx.unbindPip(p)
         for w in bound_w:
             ctx.unbindWire(w)
         why["wire / pip taken"] = why.get("wire / pip taken", 0) + 1
         continue
     locked += 1
 print("route_from: locked %d of %d nets (%s) from %s"
       % (locked, considered, ", ".join("%s %d" % kv for kv in sorted(why.items())), src))
