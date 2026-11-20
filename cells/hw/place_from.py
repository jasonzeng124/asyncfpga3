# place_from.py -- nextpnr-xilinx --pre-place script: keep the previous route's placement (build_bench.sh BD_PLACE_FROM).
#
# Runs inside nextpnr (ctx is its context), after packing and before placement.  Every cell whose name is in the
# previous route's routed JSON (BD_PLACE_FROM, its NEXTPNR_BEL attributes) is bound to the same BEL, so the placer
# leaves it there; cells that are new (a delay line that grew) are placed around them.  Cells with an XDC location
# are left to the placer's own constraint pass.
# Strength (BD_PLACE_STRENGTH, default fixed): STRENGTH_FIXED.  Measured on test_bool_array s1 it 6 from it 5:
# 'user' keeps every cell but the router then does not permute the LUT input pins of the bound cells, and the LUT5 /
# LUT6 pairs the packer starts on the same physical pin (A1) stay in conflict (55 overused site wires, no route);
# 'strong' lets the post-place repair move 681 cells; 'fixed' keeps all 6130 (only the 3 new cells are relocated),
# the router permutes 8313 LUT pins and converges, bench clock 111.5 MHz.
#
# Why (research/data/converge/notes.txt): the automatic sizing loop re-routes after every size change, and a re-route
# moves each constraint's margin by ~0.5 ns (sd) even where none of its lines changed -- on test_bool_array seed 1,
# it 5 -> it 6 added 3 delay elements and 6051 of the 6136 cells the two routes share changed BEL.  The loop then chases
# fresh misses (95 % of the rows short on a finish route were not short on the route before).  With the placement kept,
# a size change moves only the cells it adds.
#
# BD_PLACE_FREE (optional regex): cells whose names match are left for the placer even when the previous route had
# them (e.g. a line whose length changed, to let it be laid out again as a whole).
# Prints "place_from: bound N of M cells (new K, free R, taken T, type-mismatch Y)".
import json, os, re

src = os.environ["BD_PLACE_FROM"]
free_rx = os.environ.get("BD_PLACE_FREE", "")
free_re = re.compile(free_rx) if free_rx else None
# BD_PLACE_ONLY (regex, default empty = every cell): only matching cells are kept (e.g. ^bridge_i\.udut\. for the
# kernel alone: the rest is placed afresh around it).  xorshift s1 it 5 -> it 6, margin change of the sized constraints
# whose lines did not change: kernel only median |d| 196 ps, everything 122, fresh 282.
only_rx = os.environ.get("BD_PLACE_ONLY", "")
only_re = re.compile(only_rx) if only_rx else None
STRENGTH = {"user": STRENGTH_USER, "locked": STRENGTH_LOCKED, "fixed": STRENGTH_FIXED, "strong": STRENGTH_STRONG}[
    os.environ.get("BD_PLACE_STRENGTH", "fixed")]
if src.endswith(".json"):            # a routed JSON: its NEXTPNR_BEL attributes
    with open(src) as f:
        d = json.load(f)
    top = [m for m in d["modules"].values()
           if any("NEXTPNR_BEL" in c.get("attributes", {}) for c in m.get("cells", {}).values())]
    prev = {n: c["attributes"]["NEXTPNR_BEL"] for n, c in top[0]["cells"].items() if "NEXTPNR_BEL" in c.get("attributes", {})}
    names = {}                       # bit -> the name nextpnr routed it under (the alias with ROUTING), if '$'-free
    for nn, v in top[0].get("netnames", {}).items():
        if "$" not in nn and "ROUTING" in v.get("attributes", {}):
            for bt in v.get("bits", []):
                names[bt] = nn
    sig = {}
    for n, c in top[0]["cells"].items():
        out = ["%s=%s" % (p, names[v[0]]) for p, v in c.get("connections", {}).items()
               if c.get("port_directions", {}).get(p) == "output" and v and v[0] in names]
        sig[n] = ",".join(sorted(out))
    ptype = {n: c.get("type") for n, c in top[0]["cells"].items()}
    ppins = {n: {k[len("X_ORIG_PORT_"):]: v for k, v in c.get("attributes", {}).items()
                 if re.fullmatch(r"X_ORIG_PORT_A[1-6]", k)}
             for n, c in top[0]["cells"].items() if c.get("type") == "SLICE_LUTX"}
    # connectivity, for the neighbour key below: cell -> [(port, bit)], bit -> [cell]
    pconn = {n: [(p, v[0]) for p, v in c.get("connections", {}).items() if v and isinstance(v[0], int)]
             for n, c in top[0]["cells"].items()}
    pbit = {}                         # bit -> [(cell, port)]
    for n, lst in pconn.items():
        for p, bt in lst:
            pbit.setdefault(bt, []).append((n, p))
else:                                # research/tools/auto/auto_size.sh's place_I.txt: "cell<TAB>bel[<TAB>sig]" per line
    prev, sig, pconn, pbit, ptype, ppins = {}, {}, None, None, {}, {}
    with open(src) as f:
        for ln in f:
            if ln.strip() and not ln.startswith("#"):
                fl = ln.rstrip("\n").split("\t")
                prev[fl[0]] = fl[1]
                if len(fl) > 2:
                    sig[fl[0]] = fl[2]
# yosys numbers abc's cells from a counter shared by the whole run ($abc$<run>$auto$blifparse.cc:<l>:parse_blif$<k>),
# and a kernel whose size changed shifts <run> and every <k> of the harness's LUTs by the same amount (xorshift s1 it 5
# -> 6: 21205 -> 21209; only 3687 of 7533 names matched).  The cell is the same: key it by k - run.  A key two cells
# of one route share is dropped (no guess).
RE_ABC = re.compile(r"\$abc\$(\d+)\$auto\$blifparse\.cc:(\d+):parse_blif\$(\d+)")


def norm(name):
    return RE_ABC.sub(lambda m: "$abc$*$auto$blifparse.cc:%s:parse_blif$+%d" % (m.group(2), int(m.group(3)) - int(m.group(1))),
                      name)


def out_sig_ctx(cell):
    """the cell's output nets with user names (no '$'), as 'port=net' sorted"""
    out = []
    for pn, pi in cell.ports:
        if pi.type == PORT_OUT and pi.net is not None and "$" not in pi.net.name:
            out.append("%s=%s" % (pn, pi.net.name))
    return ",".join(sorted(out))


pclass = lambda p: "A" if re.fullmatch(r"A[1-6]", p) else p   # a LUT's A1..A6: one class (the router permutes them)
FANOUT_MAX = 16       # a clock, reset or enable net touches thousands of cells: it identifies nothing
# The constant ties the router adds ($PACKER_GND_NET$LUT$.., $PACKER_VCC_NET$LUT$..) are on the routed netlist's nets
# and not yet on this one's: they are left out of every neighbour set.


def cur_nbrs(cell, nm, match):
    """own port class -> {(previous name, its port class)} of the matched cells on that (low-fanout) net.  The
    neighbour's port tells a CARRY4's S input from its DI (its S LUT from its G LUT, alike otherwise)."""
    out = {}
    for pn, pi in cell.ports:
        if pi.net is None:
            continue
        on = [(pi.net.driver.cell.name, pi.net.driver.port)] if pi.net.driver.cell is not None else []
        on += [(u.cell.name, u.port) for u in pi.net.users if u.cell is not None]
        if len(on) > FANOUT_MAX:
            continue
        out.setdefault(pclass(pn), set()).update((match[x], pclass(q)) for x, q in on
                                                 if x != nm and x in match and not x.startswith("$PACKER_"))
    return out


def prev_nbrs(k, rev):
    out = {}
    for p, bt in pconn.get(k, []):
        on = pbit.get(bt, [])
        if len(on) > FANOUT_MAX:
            continue
        out.setdefault(pclass(p), set()).update((x, pclass(q)) for x, q in on
                                                if x != k and x in rev and not x.startswith("$PACKER_"))
    return out


cells_by = {nm: cell for nm, cell in ctx.cells}
match = {}                            # current name -> the previous route's name of the same cell
# 1. TRUSTED names: a name with no yosys / packer counter in it ('$' then digits: bridge_i.udut.umux0.udat.pair[0].u$LUT5,
#    bridge_i.udut.ulink_n7.ctl.u.u), exactly; and abc's cells by their index relative to the run (one previous cell per
#    key).  Every other numbered name ($auto$ff.cc:337:slice$N, $auto$alumacc...$N, x$LUT$N) is NOT a name across
#    routes: yosys reuses the number for another cell when its counter moves (xorshift s1: it 6's slice$9999 and it 5's
#    slice$9999 share no neighbour; it 5's awready flop is slice$10000, it 6's slice$10004), and binding by it put flops
#    of other control sets into one slice ("post-placement validity check failed for Bel ..A5FF (no cell)").
RE_NUM = re.compile(r"\$\d")
for nm in cells_by:
    if nm in prev and not RE_NUM.search(nm):
        match[nm] = nm
qprev = {}
for k in prev:
    if RE_ABC.search(k):
        qprev.setdefault(norm(k), []).append(k)
taken_prev = set(match.values())
for nm in cells_by:
    if nm not in match and RE_ABC.search(nm):
        ks = qprev.get(norm(nm), [])
        if len(ks) == 1 and ks[0] not in taken_prev and not RE_NUM.search(norm(nm).replace("$+", "+")):
            match[nm] = ks[0]
            taken_prev.add(ks[0])
dup = {q for q, ks in qprev.items() if len(ks) > 1}
rejected = 0
# 2. the user names of the output nets (bridge_i.hist[0][10]), one cell on each side
ranked = 0
used_prev = set(match.values())
by_sig_prev, by_sig_cur = {}, {}
for k in prev:
    if k not in used_prev and sig.get(k):
        by_sig_prev.setdefault(sig[k], []).append(k)
for nm, cell in cells_by.items():
    if nm not in match:
        sg = out_sig_ctx(cell)
        if sg:
            by_sig_cur.setdefault(sg, []).append(nm)
for sg, lc in by_sig_cur.items():
    lp = by_sig_prev.get(sg, [])
    if len(lc) == 1 and len(lp) == 1:
        match[lc[0]] = lp[0]
        ranked += 1
# 3. structure: an unmatched cell pairs with the one unmatched previous cell of its type whose nets (per own port
#    class, low-fanout only) hold every matched neighbour this cell has here -- the routed netlist may hold more (a
#    LUT5 / LUT6 pair's shared site pins show both LUTs' inputs).  Rounds, so a cell paired anchors the next.
nbr = 0
if pconn is not None:
    for _round in range(4):
        rev = {v: k for k, v in match.items()}
        inv = {}
        for k in prev:
            if k in rev:
                continue
            for c, v in prev_nbrs(k, rev).items():
                for x in v:
                    inv.setdefault((c, x), set()).add(k)
        got = 0
        claimed = {}
        for nm, cell in cells_by.items():
            if nm in match:
                continue
            S = cur_nbrs(cell, nm, match)
            keys = [(c, x) for c, v in S.items() for x in v]
            if not keys:
                continue
            cand = None
            for key in sorted(keys, key=lambda q: len(inv.get(q, ()))):
                cand = set(inv.get(key, ())) if cand is None else cand & inv.get(key, set())
                if len(cand) <= 1:
                    break
            cand = {k for k in (cand or ()) if ptype.get(k) == cell.type}
            if len(cand) == 1:
                k = cand.pop()
                claimed.setdefault(k, []).append(nm)
        for k, nms in claimed.items():
            if len(nms) == 1:
                match[nms[0]] = k
                got += 1
        nbr += got
        if not got:
            break
hit = {nm: prev[k] for nm, k in match.items()}
n = new = freed = taken = mism = bound = 0
for name, cell in ctx.cells:
    n += 1
    bel = hit.get(name)
    if bel is None:
        new += 1
        continue
    if (free_re is not None and free_re.search(name)) or name.startswith("$PACKER_") or \
            (only_re is not None and not only_re.search(name)):
        # BD_PLACE_FREE, and the packer's constant ties ($PACKER_VCC_NET$LUT$..): pinned into a LUT5 slot whose LUT6
        # uses pin A1 for a signal, their constant input could not be routed (xorshift s1 it 6: 17 sinks left
        # unrouted; the const-sinks check refuses that bitstream); where they go does not touch the kernel
        freed += 1
        continue
    if cell.bel is not None:          # already placed (a packer constraint): leave it
        continue
    if any(kv.first == "BEL" for kv in cell.attrs):   # an XDC / user location: the placer binds it itself
        continue
    if ctx.getBelType(bel) != cell.type:
        mism += 1
        continue
    if not ctx.checkBelAvail(bel):
        taken += 1
        continue
    ctx.bindBel(bel, cell, STRENGTH)
    bound += 1

# The LUT input pins.  The router permutes a LUT's physical input pins per route (X_ORIG_PORT_A<n> = the logical inputs on
# pin A<n>), and the packer starts every LUT1 on A1; a kept LUT6 / LUT5 pair (or a constant tie in a kept carry slice)
# then starts on one shared pin, and the constant router does not swap a tie's pin (xorshift s1 it 6: VCC tie
# $PACKER_VCC_NET$LUT$1360 back on A1 beside its LUT6's signal: "constant sink could not be routed"; the previous route
# had it on A2).  So every kept LUT, and every packer LUT whose cluster parent is kept, gets the previous route's pins:
# the same nets, moved to the pins they had, X_ORIG_PORT rewritten to match (the FASM's INIT follows X_ORIG_PORT;
# fasm_equiv checks the bitstream against the netlist).
def attr_map(cell):
    return {kv.first: str(kv.second) for kv in cell.attrs}


def restore_pins(nm, cell, pmap):
    a = attr_map(cell)
    cur = {k[len("X_ORIG_PORT_"):]: v for k, v in a.items() if re.fullmatch(r"X_ORIG_PORT_A[1-6]", k)}
    lg = lambda v: re.findall(r"I\d+", v)
    if sorted(x for v in cur.values() for x in lg(v)) != sorted(x for v in pmap.values() for x in lg(v)):
        return False                  # not the same logical inputs: leave it
    if cur == pmap:
        return False
    net_of = {}                       # logical input -> net name
    pnet = {pn: (pi.net.name if pi.net is not None else None) for pn, pi in cell.ports}
    for pin, v in cur.items():
        for x in lg(v):
            net_of[x] = pnet.get(pin)
    for pin, v in pmap.items():       # every logical input on a target pin must carry one net
        if len({net_of.get(x) for x in lg(v)}) != 1:
            return False
    for pin in cur:
        if pnet.get(pin) is not None:
            ctx.disconnectPort(nm, pin)
        cell.unsetAttr("X_ORIG_PORT_" + pin)
    for pin, v in pmap.items():
        net = net_of[lg(v)[0]]
        if pin not in pnet:
            cell.addInput(pin)
        if net is not None:
            ctx.connectPort(net, nm, pin)
        cell.setAttr("X_ORIG_PORT_" + pin, v)
    return True


repinned = 0
if ppins:
    kept = {nm for nm, cell in ctx.cells if cell.bel is not None}
    for nm, cell in ctx.cells:
        if cell.type != "SLICE_LUTX":
            continue
        k = match.get(nm) or (nm if nm in prev and nm.startswith("$PACKER_") else None)
        if k is None or k not in ppins:
            continue
        if nm not in kept:
            par = attr_map(cell).get("CONSTR_PARENT")
            if not (nm.startswith("$PACKER_") and par in kept):
                continue
        if restore_pins(nm, cell, ppins[k]):
            repinned += 1
print("place_from: LUT pins restored to the previous route's on %d cells" % repinned)
print("place_from: bound %d of %d cells (new %d, free %d, taken %d, type-mismatch %d, ambiguous keys %d, paired by output nets %d, by neighbours %d) from %s"
      % (bound, n, new, freed, taken, mism, len(dup), ranked, nbr, src))
