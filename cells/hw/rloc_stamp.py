#!/usr/bin/env python3
"""rloc_stamp.py -- put RLOC_GROUP relative-placement attributes on a
post-synthesis netlist.

WHY THIS IS A SEPARATE PASS AND NOT RTL.  cells/rtl/ is frozen, so the
attribute cannot be written next to the cells it constrains.  It is stamped
here instead, on the JSON yosys just wrote, keyed on the instance paths the
library commits to (`<link>.ctl.u.u`, `<link>.lat.*`, `<mux>.uj0/uj1`; a
bd_pipe is a chain of bd_links at `<pipe>.many.stage[i].u.*` or
`<pipe>.one.u.*`) -- the same anchors verify/tighten.py's select_consumers()
uses, and for the same reason: those names are the library's, not the
compiler's.  Every stage gets the identical treatment: a controller next to
one of the latch bits it enables.  A controller cell with more than one
output (none in the library today) can join only ONE latch bank -- see
stage_banks().

WHAT NEXTPNR DOES WITH IT.  Nothing that knows what a bd_link is.  The packer
pass (xilinx/pack.cc, pack_rloc_groups) reads one generic attribute: cells
carrying the same RLOC_GROUP string are tied into one cluster -- same tile,
consecutive logic slots -- and the cluster as a whole floats.  That is
Vivado's RLOC, not a LOC: no cell is ever pinned to a BEL and the placer still
chooses where the group lands.  A SLICE on xc7 holds four LUTs (a fractured
LUT6_2 pair is one slot); a group naming more is laid out as a column, one
tile per four slots, rows alternating above and below the root's so the root
sits mid-column, at most nine tiles (patches/README.md).

WHAT IT IS FOR.  cells/build/hw/gcd_ps/gcd_ps.sdf, measured: a link's C node
reaches its OWN latch's enable with a median 1920 ps of interconnect (p90 3405)
while it reaches the first element of its own matched delay chain in 639 ps.
The chain is a string of single-load nets, so the placer strings it; the
latch's output has heavy fanout and drags the latch away, because nothing in
the design declares that net critical.  That costs latency on every transfer,
and at a bd_mux / bd_steer -- the only two consumers that act on the request
EDGE instead of latching transparently -- it is a correctness term, because the
select must be stable before the request arrives (verify/skew.py, rule E).

VARIANTS.
  v1   {C node, one latch LUT}                 -- 2 slots, every link.
  v2   v1, plus at a link whose latch drives a select, the consuming
       bd_mux's two join LUTs                  -- 4 slots.
  v3   v2, but the WHOLE latch bank            -- a column of slices.
  v4   v3, plus every bd_delay chain as its own column.

Under v1/v2 only ONE latch LUT per link is grouped: a bd_latch packs two data
bits per LUT6_2, so a W=32 link is 16 of them and a four-LUT cluster cannot
hold the bank.  The bit that is grouped is chosen deliberately -- the one that
drives a select consumer where there is one, otherwise the first -- and the
report says how many links are W=1 (where one LUT IS the whole bank) so the
reach of the constraint is never overstated.

v3 names every LUT of the bank.  It needs the rloc-group patch's column
layout (a group past four slots is stacked one slice per tile above and below
the root's), and exists because the enable net is what the whole cycle waits
on: on a W=32 link routed under v2 the C node reached its own latches 640 to
1260 ps after switching (median 936), under v3 150 to 630 (median 540) for
the same design.  The latch closing late shows up twice -- once as data
leaving the stage late relative to its request (rule A, sized into the
consumer's delay line) and once as the acknowledge that may not fall until
the latch is shut (rule H, sized into DACK).

v4 also groups each bd_delay's LUTs (`<dly>.chain.g[i].u`).  Ungrouped, a
link of the chain costs 150 ps of interconnect when the placer put its
neighbour in the same SLICE and 540-630 when it did not, so the same N is
worth anything between 275 and 750 ps per link from one route to the next
and the resize pass, which sizes N against one route and confirms it on
another, keeps rejecting shrinks that a steadier chain would take.  A
placeholder chain longer than the column can hold is left unclustered by
nextpnr, with a warning; only the tightened lengths are ever the ones that
matter.

PLACE_WEIGHT.  `--place-weight K` (K > 1) additionally stamps a PLACE_WEIGHT
attribute on every HANDSHAKE net -- any net touching a library control cell
(a C node, a delay-chain link, a join/merge/mux/steer LUT; anything named,
that is not a `.lat` or `.udat` storage cell) other than reset.  The patched
nextpnr (patches/nextpnr-xilinx-place-weight.patch) multiplies that net's
wirelength by K in both its analytic and annealing placers.  Why: nextpnr's
placer is timing-driven only for nets on a clocked path, and a bd_link ring
has none, so the four or five nets the whole cycle waits on -- request to the
next C node, acknowledge back, C node to its own delay chain -- are placed by
the same wirelength objective as any one bit of a 32-wide data bus, and
land 4-11 tiles from their sink (950-1500 ps each, xorshift_round v4 route)
while the 32 data bits between the same two stages average 2.  RLOC groups
hold a stage together; PLACE_WEIGHT is what pulls the STAGES together.

usage: rloc_stamp.py IN.json OUT.json --variant v1|v2|v3|v4|none
                     [--place-weight K] [--report]

WIRED INTO hw/build_hw.sh and flow.sh, both the same three lines, between
`write_json` and the nextpnr invocation:

    if [ -n "${BD_RLOC:-}" ]; then
        python3 "$(dirname "$0")/rloc_stamp.py" "$OUT/$TOP.json" \
            "$OUT/$TOP.rloc.json" --variant "$BD_RLOC" --report &&
            mv "$OUT/$TOP.rloc.json" "$OUT/$TOP.json"
    fi

and it needs a nextpnr carrying patches/nextpnr-xilinx-rloc-group.patch; an
unpatched binary ignores the attribute silently, which is exactly the failure
mode cells/verify/toolchain.sh exists to catch.  cells/verify/rloc_sweep.sh
drives the whole thing, across placer seeds, from a JSON build_hw.sh already
wrote.

A zero-match stamp -- the regex found no controller at all, or found some and
paired none of them with a latch -- is not treated as success: it prints a
WARNING naming what it looked for, and main() returns a nonzero exit so a
caller like flow.sh's `|| { RLOC STAMP FAILED; exit 1; }` stops the build
instead of silently shipping an unclustered netlist.
"""

import json
import math
import re
import sys
from collections import defaultdict

ATTR = "RLOC_GROUP"
SLOT_ATTR = "RLOC_SLOT"
COL_ATTR = "RLOC_COL"
WEIGHT_ATTR = "PLACE_WEIGHT"
WHOLE_BANK = ("v3", "v4", "v5", "v6", "v7", "v8", "v9", "v10")
VARIANTS = ("v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8", "v9", "v10", "none")
# One logic tile is eight LUT slots (two SLICEs of four); a slot-ordered
# group's row is slot // 8.  v8 aligns each C node to a row boundary so the
# node and the control that follows it share a tile.
ROW_SLOTS = 8
ROW = object()
# ... and how many control cells of the request chain into the node, and of
# the control out of it, share that row with it.
ROW_IN = 3
ROW_OUT = ROW_SLOTS - 1 - ROW_IN
# How many tiles tall one RLOC_GROUP column may be.  Nine was nextpnr's
# limit until patches/nextpnr-xilinx-rloc-group.patch made it the device's
# (100 on xc7z010); --column-rows raises it, and everything sized from it
# below follows through set_column_rows().  The v8/v9 segment limit and the
# side columns are this many rows of eight slots.
COLUMN_ROWS = 9
# v7: the data-path LUTs go in the two logic columns beside the spine, each
# at the row of the spine slots it connects.  A LUT whose nearest free side
# slot is further than SIDE_REACH slots from where its nets want it is left
# to the placer instead: two rows away is already as far as free placement
# puts it.
SIDE_SLOTS = 72
SIDE_REACH = 16
# v5: a spine segment is at most this many logic slots -- four tiles of eight.
# Longer columns are harder to legalise than they are worth; consecutive
# segments share a weighted net and the placer keeps them adjacent.
SPINE_SEGMENT = 32
# v6 carries the latch banks on the spine too, so its segments are longer:
# eight tiles holds two W=32 stages with their control.
SPINE_SEGMENT_V6 = 64
# v8 pads to row boundaries, so a W=32 stage is exactly three tiles; a
# nine-tile column holds three of them, and a segment break between two
# stages is a stage-to-stage hop the placer decides, not this file.
SPINE_SEGMENT_V8 = 72


def set_column_rows(rows):
    global COLUMN_ROWS, SIDE_SLOTS, SPINE_SEGMENT_V8
    COLUMN_ROWS = rows
    SIDE_SLOTS = SPINE_SEGMENT_V8 = rows * ROW_SLOTS


# v9: the bank halves stacked on one side of a shared row are at most this
# many rows (two W=32 banks), and a chain with more inner links than this
# is a placeholder the resize has not shrunk yet: it stays on the spine.
ROW_BANK_ROWS = 2
SIDE_CHAIN = 16
LUT_TYPES = frozenset(f"LUT{i}" for i in range(1, 7)) | {"LUT6_2"}
# bd_link's `lat` (bd_latch) and bd_mux/bd_merge's `udat` (bd_datamux) are
# the library's only data-path instances (cells/rtl); every other named LUT
# is handshake control.  abc's own cells are `$`-prefixed.
_DATA_INST = (".lat.", ".udat.")

# The library's own instance names.  bd_link's controller is `ctl.u.u`, and
# a bd_pipe's stages are bd_links, so theirs are too.  Only bd_link_ctl is
# ever instantiated as `ctl` -- cells/rtl/bd_link.v is the sole source of the
# shape -- so the suffix alone identifies a C node.
# The prefix used to also require an `ulink_<name>` component, which is
# bdc/emit.py's naming convention for a COMPILED link or pipe (emit_links());
# it is not a promise a hand-instantiated one keeps, and cells/verify/soak_top.v
# instantiates its bd_pipe as plain `upipe`.  Capturing whatever precedes the
# suffix, instead of insisting on the compiler's naming, is what makes soak's
# pipe visible at all.
# bd_link_dc's enable is `ctl.ult` (rtl/bd_link.v, BD_LINK_DC).  Its other
# three controller LUTs (`ctl.ub`, `ctl.ua`, `ctl.uld`) are on one another's
# feedback and on the stage's cycle at fixed cost, so the spine walks the
# four as ONE node and lays them out as one block, in handshake order.
# bd_mlink_ctl (rtl/bd_mlink.v, two-phase) enables its bank from `ctl.ux`
# (NOPEN <= 1) or `ctl.slow_reopen.uz`; its request latch `ctl.uq`, the XNOR
# `ctl.ux` and the reopen delay's links are the same kind of block.
RE_CNODE = re.compile(r"^(?P<link>.+)\.ctl\.(?:u\.u|ult|ux|slow_reopen\.uz)$")
RE_DCPART = re.compile(r"^(?P<link>.+)\.ctl\.(?P<part>ub|ua|uld)$")
DC_PARTS = ("ub", "ua", "uld")
RE_MPART = re.compile(r"^(?P<link>.+)\.ctl\.(?P<part>uq\.odd\.u|ux"
                      r"|slow_reopen\.uen\.chain\.g\[(?P<i>\d+)\]\.u)$")
# bd_delay's links: `<dly>.chain.g[i].u` (cells/rtl/bd_latch.v), the same
# chain whether symmetric, FASTFALL or FASTRISE.
RE_DLINK = re.compile(r"^(?P<dly>.+\.chain)\.g\[(?P<i>\d+)\]\.u$")


def load(path):
    with open(path) as f:
        return json.load(f)


def instantiation_counts(mods):
    """How many times each module is instantiated in the whole design.

    A group value has to name ONE physical cluster.  Stamping inside a module
    that is instantiated more than once would give every instance the same
    string and fuse cells from different instances into one impossible group,
    so those modules are skipped entirely and reported.
    """
    top = None
    for name, m in mods.items():
        if m.get("attributes", {}).get("top"):
            top = name
    count = defaultdict(int)
    if top is None:
        return count, None
    count[top] = 1
    frontier = [top]
    seen = 0
    while frontier and seen < 10000:
        seen += 1
        cur = frontier.pop()
        for c in mods[cur].get("cells", {}).values():
            t = c["type"]
            if t in mods and "cells" in mods[t]:
                count[t] += count[cur]
                frontier.append(t)
    return count, top


def net_maps(cells):
    """net bit -> driving (cell, port), and net bit -> [(cell, port), ...]."""
    drv, snk = {}, defaultdict(list)
    for name, c in cells.items():
        if c["type"] == "$scopeinfo":
            continue
        dirs = c.get("port_directions", {})
        for p, bits in c.get("connections", {}).items():
            d = dirs.get(p)
            for b in bits:
                if not isinstance(b, int):
                    continue
                if d == "output":
                    drv[b] = (name, p)
                elif d == "input":
                    snk[b].append((name, p))
    return drv, snk


def select_sites(cells, drv):
    """{net bit driving a select pin: [consumer cell names]}.

    bd_mux's two joins are `uj0`/`uj1` and their select is logical I2.
    bd_steer's `u` is a LUT6_2 whose select is I1 and whose sibling `uack`
    tells it apart from bd_bd2dr -- the same structural signature
    verify/tighten.py uses.  Both are recorded; only the ones whose select is
    driven inside this module can be grouped at all.
    """
    out = defaultdict(list)
    have = set(cells)
    for name, c in cells.items():
        conns = c.get("connections", {})
        if name.endswith(".uj0") or name.endswith(".uj1"):
            parent = name.rsplit(".", 1)[0]
            if parent + ".uj0" not in have or parent + ".uj1" not in have:
                continue
            pin = "I2"
        elif name.endswith(".u") and name.rsplit(".", 1)[0] + ".uack" in have:
            pin = "I1"
        else:
            continue
        for b in conns.get(pin, []):
            if isinstance(b, int) and b in drv:
                out[b].append(name)
    return out


def stage_banks(c, link, snk):
    """The latch bank(s) one controller cell enables, one per output bit.

    bd_link_ctl has a single output, so one bank.  Kept per output bit
    rather than per cell because a fractured LUT6_2 driving two stages (the
    library once had one) has two banks that must not be merged: treating
    their union as one bank would let the "which bit to grab" search below
    hand back a latch that this particular output bit does not even drive.

    Returns a list of (port, bank) pairs, port order matching the cell's own
    connections dict, skipping any output with no latch sinks at all.
    """
    dirs = c.get("port_directions", {})
    out = []
    for p, bits in c.get("connections", {}).items():
        if dirs.get(p) != "output":
            continue
        for b in bits:
            if not isinstance(b, int):
                continue
            bank = []
            for sname, _ in snk.get(b, ()):
                if (sname.startswith(link + ".")
                        and ".lat" in sname[len(link):]
                        and sname not in bank):
                    bank.append(sname)
            if bank:
                bank.sort()
                out.append((p, bank))
    return out


# Markers that a bd_link/bd_pipe instance exists in this netlist at all,
# independent of whether RE_CNODE managed to pair one with a latch bank.
# Measured, not guessed: on xorshift_bench_gen these appear 40 and 106 times;
# on ro_top, which sits directly on bd_delay's LUT1s, both are 0.
_STRUCTURAL_MARKERS = (".ctl.", ".many.")


def has_link_structures(mods):
    """True if anything in this netlist is a bd_link/bd_pipe instance.

    This is what separates the two zeros.  A design that HAS links and stamps
    none of them is the bug the exit code exists for -- every storage cell is
    free for the placer to drag away and the next symptom is a rule-E
    violation nobody can explain.  A design that has no links BY CONSTRUCTION
    -- ro_top, ro_many_top, anything built straight on primitives -- has
    nothing to hold together, and failing it is a false positive that makes
    the design unbuildable for no reason.
    """
    for m in mods.values():
        for cn in m.get("cells", {}):
            if any(k in cn for k in _STRUCTURAL_MARKERS):
                return True
    return False


def is_control_cell(name, c):
    if c["type"] not in LUT_TYPES or name.startswith("$"):
        return False
    dotted = "." + name
    return not any(k in dotted for k in _DATA_INST)


def weight_control_nets(mods, weight, report):
    """PLACE_WEIGHT on every net that touches a control cell, except reset.

    The attribute goes on the yosys netname covering the bit -- a single-bit
    one where there is one, so a bus is never weighted for one member -- and
    on a new hidden netname otherwise.  nextpnr's frontend merges netname
    attributes onto the flattened net, so stamping a net in whichever module
    scope sees it is enough; a request that crosses a module boundary is
    stamped on both sides and that is harmless.
    """
    n_nets = n_cells = 0
    for mname, m in sorted(mods.items()):
        cells = m.get("cells")
        if not cells:
            continue
        rst = set()
        for src in (m.get("ports", {}), m.get("netnames", {})):
            for pname, p in src.items():
                if pname == "rst" or pname.endswith(".rst"):
                    rst.update(b for b in p["bits"] if isinstance(b, int))
        bits = set()
        for cname, c in cells.items():
            if not is_control_cell(cname, c):
                continue
            n_cells += 1
            for pbits in c.get("connections", {}).values():
                bits.update(b for b in pbits if isinstance(b, int))
        bits -= rst
        if not bits:
            continue
        netnames = m.setdefault("netnames", {})
        cover = defaultdict(list)
        for nname, nn in netnames.items():
            for b in nn["bits"]:
                if isinstance(b, int):
                    cover[b].append(nname)
        for b in sorted(bits):
            single = [n for n in cover.get(b, ()) if len(netnames[n]["bits"]) == 1]
            if single:
                target = netnames[single[0]]
            else:
                target = {"hide_name": 1, "bits": [b], "attributes": {}}
                netnames[f"$bd_place_weight${b}"] = target
            target.setdefault("attributes", {})[WEIGHT_ATTR] = weight
            n_nets += 1
    if report:
        print(f"place_weight {n_nets} handshake net(s) weighted x{weight} "
              f"(nets touching {n_cells} control LUT(s), reset excluded)")
    return n_nets


def is_user_module(mods, t):
    """A module of the design proper, not a cells_sim primitive model."""
    m = mods.get(t)
    if m is None or "cells" not in m:
        return False
    a = m.get("attributes", {})
    return not (a.get("blackbox") or a.get("whitebox"))


def flatten(mods, top, counts):
    """Walk the hierarchy from `top` through every module instantiated once.

    Yields (mname, cname, cell, global-bit-of-each-connection) for each cell,
    where a global bit identifies one flattened net -- a module port and the
    parent net it is connected to are the same net, and so are two parent
    nets a module wires straight through (`assign a_ack = z_ack` in a fused
    unit joins the acknowledge it receives to the one it passes on).  Shared
    modules (count != 1) are not entered: one JSON cell object cannot carry
    two placements.
    """
    out = []
    rst = set()
    alias = {}

    def root(g):
        while g in alias:
            g = alias[g]
        return g

    def visit(mname, path, bitmap):
        m = mods[mname]
        local = {}

        def gid(b):
            if not isinstance(b, int):
                return None
            if b in bitmap:
                return bitmap[b]
            return local.setdefault(b, (path, b))

        for nname, nn in m.get("netnames", {}).items():
            if nname == "rst" or nname.endswith(".rst"):
                rst.update(g for g in map(gid, nn["bits"]) if g is not None)
        for cname, c in m.get("cells", {}).items():
            t = c["type"]
            conns = {p: [gid(b) for b in bits]
                     for p, bits in c.get("connections", {}).items()}
            if is_user_module(mods, t):
                if counts.get(t, 0) != 1:
                    continue
                child = {}
                for p, gids in conns.items():
                    for b, g in zip(mods[t]["ports"][p]["bits"], gids):
                        if not isinstance(b, int) or g is None:
                            continue
                        if b in child and root(child[b]) != root(g):
                            alias[root(child[b])] = root(g)
                        child[b] = g
                visit(t, path + cname + ".", child)
            else:
                out.append((mname, cname, c, conns))

    visit(top, "", {})
    if alias:
        out = [(mname, cname, c,
                {p: [None if g is None else root(g) for g in gids]
                 for p, gids in conns.items()})
               for mname, cname, c, conns in out]
        rst = {root(g) for g in rst}
    return out, rst


def spine_order(nodes, adj):
    """One linear order per connected component of the control graph.

    Depth-first, always stepping to the unvisited neighbour with the fewest
    unvisited neighbours of its own: a dead end (an ack delay's single link)
    is taken first so it lands beside the cell it hangs off, and the walk
    then follows the ring.  Any order is legal; this one keeps the cells a
    transition passes through in consecutive slots.
    """
    seen = set()
    components = []
    degree = {n: len(adj[n]) for n in nodes}
    for start in sorted(nodes, key=lambda n: (degree[n], n)):
        if start in seen:
            continue
        order, stack = [start], [start]
        seen.add(start)
        while stack:
            cur = stack[-1]
            nxt = [n for n in adj[cur] if n not in seen]
            if not nxt:
                stack.pop()
                continue
            nxt.sort(key=lambda n: (sum(1 for x in adj[n] if x not in seen), n))
            seen.add(nxt[0])
            stack.append(nxt[0])
            order.append(nxt[0])
        components.append(order)
    return components


class Seg:
    """A spine segment being laid out: its slots (a cell key or None for a
    gap), and the chains to place beside it, each at the slot it hangs off."""

    def __init__(self):
        self.slots = []
        self.beside = []

    def copy(self):
        c = Seg()
        c.slots = list(self.slots)
        c.beside = list(self.beside)
        return c


class Side:
    """In an atom: these cells go in a side column, at the row of the slot
    before this marker -- the nearer free run of either column, or, with
    `col`, that column exactly (v10's bank halves)."""

    def __init__(self, links, col=None):
        self.links = links
        self.col = col


def place_beside(mods, g, beside, taken):
    """Give each run of cells in `beside` consecutive slots of one side
    column of group g, as near the row it hangs off as the column is free,
    columns alternating unless the run names its own.  Returns (cells
    placed, cells left to the placer, {cell: slot} of those placed)."""
    n_ok = n_loose = 0
    placed = {}
    for i, (links, at, own) in enumerate(beside):
        want = (at // ROW_SLOTS) * ROW_SLOTS
        best = None
        for col in (own,) if own is not None else ((-1, 1), (1, -1))[i % 2]:
            for s0 in range(0, SIDE_SLOTS - len(links) + 1):
                if any(s in taken[g][col] for s in range(s0, s0 + len(links))):
                    continue
                key = (abs(s0 - want), s0)
                if best is None or key < best[0]:
                    best = (key, col, s0)
                if s0 >= want:
                    break
        if best is None:
            n_loose += len(links)
            continue
        _, col, s0 = best
        for j, (mname, cname) in enumerate(links):
            taken[g][col].add(s0 + j)
            placed[(mname, cname)] = s0 + j
            attrs = mods[mname]["cells"][cname].setdefault("attributes", {})
            attrs[ATTR] = g
            attrs[SLOT_ATTR] = s0 + j
            attrs[COL_ATTR] = col
        n_ok += len(links)
    return n_ok, n_loose, placed


def stamp_datapath(mods, cells, rst, segments, taken, beside=None):
    """v7: every LUT that is neither control nor on the spine -- abc's data
    path, a bd_datamux, the single latch of a W<=2 link -- goes into the
    logic column to the left or right of the spine segment its nets lead
    to, at the row of the spine slots it connects.

    Measured on the v6 route of xorshift_round (fusion on, cap 4): the two
    data wires of a stage, latch -> xor LUT -> next latch, were 855 and 945
    ps of the 2616 ps data path that sizes the matched delay, against 495
    for a wire into the next logic column at the same row.  The placer had
    put the xor LUTs two columns off because the harness pipe held the near
    one; nothing said the data belonged with its latches.

    Where a LUT wants to be is the mean spine position of what it connects
    to, over all spine segments laid end to end (a cell in a side column,
    `beside`, counts at the slot of its row); LUTs that only reach the spine
    through other data LUTs take the mean of their neighbours, a few rounds
    of it.  Slots are handed out nearest-first to that position in whichever
    side column has the nearer free slot.
    """
    if not segments:
        return 0, 0, 0, {-1: 0, 0: 0, 1: 0}
    base, fixed = {}, {}
    gaps = defaultdict(set)
    offset = 0
    for g, seg in segments:
        base[g] = offset
        for i, key in enumerate(seg):
            if key is None:
                gaps[g].add(i)
            else:
                fixed[key] = offset + i
        for key, i in (beside or {}).get(g, {}).items():
            fixed[key] = offset + i
        offset += len(seg)

    drivers, sinks = {}, defaultdict(list)
    loose = {}
    for mname, cname, c, conns in cells:
        key = (mname, cname)
        if c["type"] in LUT_TYPES and key not in fixed and not is_control_cell(cname, c):
            loose[key] = c
        dirs = c.get("port_directions", {})
        for p, gids in conns.items():
            for gid in gids:
                if gid is None or gid in rst:
                    continue
                if dirs.get(p) == "output":
                    drivers[gid] = key
                else:
                    sinks[gid].append(key)
    neigh = defaultdict(set)
    for gid, d in drivers.items():
        for s in sinks.get(gid, ()):
            if s != d:
                neigh[d].add(s)
                neigh[s].add(d)

    target = dict(fixed)
    for _ in range(6):
        nxt = {}
        for key in loose:
            known = [target[n] for n in neigh[key] if n in target]
            if known:
                # fsum: the mean must not depend on the order a set yields
                # its neighbours, or two LUTs tied for a slot swap columns
                # from one run to the next and the route is not reproducible.
                nxt[key] = math.fsum(known) / len(known)
        target.update(nxt)

    # A slot the spine left empty (v8's row padding) is in the same tile as
    # the control it pads, so it is offered first, at the distance of its row.
    free = {g: {c: set(range(SIDE_SLOTS)) - taken[g][c] for c in (-1, 1)} for g, _ in segments}
    for g, _ in segments:
        free[g][0] = set(gaps[g])
    n_dp = n_far = 0
    per_col = {-1: 0, 0: 0, 1: 0}
    order = sorted((k for k in loose if k in target), key=lambda k: (target[k], k))
    for key in order:
        t = target[key]
        g = max((g for g in base if base[g] <= t), key=lambda g: base[g], default=None)
        want = round(t - base[g])
        best = None
        for col in (0, -1, 1):
            for s in sorted(free[g][col]):
                d = abs(s - want) if col else abs(s // ROW_SLOTS - want // ROW_SLOTS) * ROW_SLOTS
                if best is None or (d, per_col[col], abs(col), col, s) < best[0]:
                    best = ((d, per_col[col], abs(col), col, s), s)
        if best is None or best[0][0] > SIDE_REACH:
            n_far += 1
            continue
        (_, _, _, col, _), s = best
        free[g][col].discard(s)
        attrs = mods[key[0]]["cells"][key[1]].setdefault("attributes", {})
        attrs[ATTR] = g
        attrs[SLOT_ATTR] = s
        attrs[COL_ATTR] = col
        per_col[col] += 1
        n_dp += 1
    return n_dp, n_far, len(loose) - len(order), per_col


def stamp_v5(mods, report, banks_on_spine=False, datapath_beside=False,
             control_row=False, shared_rows=False, side_banks=False):
    """v5: latch banks in their own columns, control on a slot-ordered spine.
    v6 (banks_on_spine): the same spine with each C node's bank around it.
    v7 (datapath_beside): v6, plus the data path in the columns beside it.
    v8 (control_row): v7, with each C node at the start of a tile row and
    the control that follows it -- its ack delay, the OR and matched delay
    of the cone it feeds -- in the same row; the bank's halves are the rows
    above and below.
    v9 (shared_rows): v8 with two stages to a row -- only the control on
    the cycle at fixed cost is in the row, the inner links of every matched
    delay go beside it -- so a two-stage ring never leaves its tile.
    v10 (side_banks): v8's row with the bank's halves in the side columns
    at the row of their node instead of the rows above and below it, so a
    stage is two rows of the spine, not three, and the data path sits in
    the row between two banks instead of between two rows of them.

    v8 is about which hops of the cycle are in-tile.  On the v7 route of
    xorshift_round (fusion on, cap 4) a delay link reaching its neighbour in
    the same tile cost 150-295 ps of interconnect, in the next tile 435-540,
    and the cycle went C node -> OR (540) -> chain -> last link -> next C
    node (540) -> its ack delay -> back (540 + 540), then the same again for
    return-to-zero: seven such hops, 4.7 of the 7.27 ns period, against 2.2
    ns in the matched delay that the data path actually needs.  v6/v7 put
    the C node mid-bank with the OR and chain in the row below it, so every
    one of those hops crossed a tile.  Here the C node, its OR, up to the
    first links of the chain and its own ack delay are eight consecutive
    slots of one tile; the latches move at most one row further from the
    node than v7 had them.

    v5 measured the trade-off: the control ring's hops did drop to 150 ps,
    but the C node -> own latch reach went from a median 435 to 1001 ps
    (fusion-off cap 4), rules A/H sized every DACK up, and the settled route
    was slower than v4.  v6 keeps the bank where v4 had it -- split around
    its own C node, within a tile either way -- and threads the spine
    through it, so the stage-to-stage arcs that v4 left to the placer (C
    node -> OR -> chain -> next C node, C node -> ack delay) are in-column.

    v4 put each C node at the middle of its latch column and each delay
    chain in a column of its own, and a cycle of xorshift_round's routed
    ring then spent eight cross-tile hops (585-810 ps each against 150 ps
    inside a tile) going C node -> uor -> chain -> next C node -> back.
    Here every control LUT -- C nodes, ack and request delay chains, joins,
    the OR in front of a fused cone -- joins ONE RLOC_GROUP per connected
    component of the control graph, with RLOC_SLOT giving the order the
    handshake travels in, so a stage's whole ring is eight consecutive slots:
    one tile.  The latch banks are grouped without their C node and float
    beside the spine on their (weighted) enable net.
    """
    counts, top = instantiation_counts(mods)
    if top is None:
        raise SystemExit("no top module in this netlist")
    cells, rst = flatten(mods, top, counts)

    def scope(mname):
        return "" if mname == top else re.sub(r"[^A-Za-z0-9_]", "_", mname) + "__"

    # Latch banks: every `.lat` LUT one controller enables, keyed as v4 keys
    # its group so the flow's reports and hw/ctl_latch_reach.py still find it.
    n_banks = n_latch = n_cands = 0
    bank_of = {}
    for mname, m in sorted(mods.items()):
        mcells = m.get("cells")
        if not mcells or counts.get(mname, 0) != 1:
            continue
        cands = [n for n in mcells if RE_CNODE.match(n)]
        if not cands:
            continue
        n_cands += len(cands)
        _, snk = net_maps(mcells)
        for cname in sorted(cands):
            link = RE_CNODE.match(cname).group("link")
            for port, bank in stage_banks(mcells[cname], link, snk):
                if len(bank) < 2:
                    continue
                g = "bdlink_" + scope(mname) + re.sub(r"[^A-Za-z0-9_]", "_", cname)
                if banks_on_spine:
                    bank_of[(mname, cname)] = [(mname, mn) for mn in sorted(bank)]
                else:
                    for mn in bank:
                        mcells[mn].setdefault("attributes", {})[ATTR] = g
                n_banks += 1
                n_latch += len(bank)
                break

    # The control graph, over flattened nets.
    control = {}
    drivers, sinks = {}, defaultdict(list)
    out_nets, in_nets = defaultdict(list), defaultdict(list)
    for mname, cname, c, conns in cells:
        if not is_control_cell(cname, c):
            continue
        key = (mname, cname)
        control[key] = c
        dirs = c.get("port_directions", {})
        for p, gids in conns.items():
            for g in gids:
                if g is None or g in rst:
                    continue
                if dirs.get(p) == "output":
                    drivers[g] = key
                    out_nets[key].append(g)
                else:
                    sinks[g].append(key)
                    in_nets[key].append(g)
    # A delay chain is one node, its links in index order: the tap that
    # bypasses it (FASTFALL/FASTRISE) connects the OR to every link and would
    # otherwise let the walk enter a chain in the middle.
    chain_of = {}
    chains = defaultdict(list)
    link_index = {}
    for key in control:
        hit = RE_DLINK.match(key[1])
        if hit:
            node = (key[0], hit.group("dly"))
            chain_of[key] = node
            chains[node].append(key)
            link_index[key] = int(hit.group("i"))
    for node, links in chains.items():
        links.sort(key=lambda k: link_index[k])
    # The tap into a link past the first is not a hop of the walk either:
    # bd_delay_gated takes it from the cell BEFORE the OR, and the walk would
    # step from that cell straight into the chain, leaving the OR and the
    # chain's head -- the hop the request actually takes -- for a later row.
    def side_tap(driver, sink):
        i = link_index.get(sink)
        return i is not None and i > 0 and link_index.get(driver) != i - 1
    # A decoupled controller is one node too: its state LUTs fold onto the
    # enable, which is the C-node candidate the bank hangs off.
    ctl_block = {}
    for key in control:
        hit = RE_DCPART.match(key[1])
        if not hit:
            continue
        node = (key[0], hit.group("link") + ".ctl.ult")
        if node in control:
            chain_of[key] = node
            ctl_block.setdefault(node, []).append(key)
    for node, parts in ctl_block.items():
        parts.sort(key=lambda k: DC_PARTS.index(RE_DCPART.match(k[1]).group("part")))
        parts.append(node)
    # A two-phase controller likewise: uq, ux and the reopen delay fold onto
    # the LUT that drives the bank.  With no reopen delay ux IS that LUT.
    mparts = {}
    for key in control:
        hit = RE_MPART.match(key[1])
        if hit:
            mparts.setdefault((key[0], hit.group("link")), []).append((key, hit))
    for (mname, link), parts in mparts.items():
        node = (mname, link + ".ctl.slow_reopen.uz")
        if node not in control:
            node = (mname, link + ".ctl.ux")
            parts = [(k, h) for k, h in parts if h.group("part") != "ux"]
        if node not in control:
            continue

        def rank(kh):
            part = kh[1].group("part")
            return (0, 0) if part.startswith("uq") else (1, 0) if part == "ux" \
                else (2, int(kh[1].group("i")))
        parts.sort(key=rank)
        for k, _ in parts:
            if k in chain_of:
                chains.pop(chain_of[k], None)
            chain_of[k] = node
        ctl_block[node] = [k for k, _ in parts] + [node]

    def expand(n):
        return chains.get(n) or ctl_block.get(n) or [n]

    nodes = {chain_of.get(k, k) for k in control}
    adj = {n: set() for n in nodes}
    for g, d in drivers.items():
        a = chain_of.get(d, d)
        for s in sinks.get(g, ()):
            b = chain_of.get(s, s)
            if a != b and not side_tap(d, s):
                adj[a].add(b)
                adj[b].add(a)
    adj = {n: sorted(v) for n, v in adj.items()}

    # An atom is what a segment boundary may not split: a delay link, a
    # control LUT, or (v6) a C node with the two halves of its bank around it.
    def atoms(comp):
        if shared_rows:
            yield from shared_row_atoms(comp)
            return
        if side_banks:
            yield from side_bank_atoms(comp)
            return
        if control_row:
            yield from row_atoms(comp)
            return
        for n in comp:
            if n in chains:
                for k in chains[n]:
                    yield [k]
            elif n in bank_of:
                bank = bank_of[n]
                yield bank[:len(bank) // 2] + expand(n) + bank[len(bank) // 2:]
            else:
                yield expand(n)

    # v8's atom is one bank half, a row break, the C node's row, a row break,
    # the other half.  The row holds the last ROW_IN control cells walked
    # before the node (the end of the chain that requests it) and the first
    # ROW_OUT after it (its ack delay, the OR and the start of the chain it
    # requests); what falls between two rows goes, as single links, in the
    # rows before the next stage's bank.  Only the ends matter: the C node's
    # own fanout and the last link's hop are on the cycle at fixed cost,
    # while any wire inside the chain is absorbed by the resize that sizes it.
    def row_atoms(comp):
        i = 0
        carry = []
        while i < len(comp) and comp[i] not in bank_of:
            carry.extend(expand(comp[i]))
            i += 1
        while i < len(comp):
            n = comp[i]
            i += 1
            after = []
            while i < len(comp) and comp[i] not in bank_of:
                after.extend(expand(comp[i]))
                i += 1
            node = expand(n)
            # A four-LUT controller leaves the row one slot on the request
            # side (the chain's last link) and three past it.
            row_in = ROW_IN if len(node) == 1 else 1
            row_out = ROW_SLOTS - len(node) - row_in
            cut = max(0, len(carry) - row_in)
            head, tail = carry[:cut], carry[cut:]
            run, carry = after[:row_out], after[row_out:]
            bank = bank_of[n]
            half = len(bank) // 2
            for k in head:
                yield [k]
            yield [ROW] + bank[:half] + [ROW] + tail + node + run + [ROW] + bank[half:]
        for k in carry:
            yield [k]

    # v10: v8's row, with the bank beside it.  The two halves go in the side
    # columns at the node's own row (one tile away either way, as v8's rows
    # above and below were), so the next node's row is two rows on instead
    # of three: the acknowledge and the return-to-zero of a stage-to-stage
    # cycle each cross one tile less.  The row between two nodes' rows holds
    # the links that overflowed the row before it and is otherwise gaps, and
    # the data path -- reading the bank at the row above, writing the one at
    # the row below -- takes those gaps and the side slots of that row.  On
    # the v8 route the data LUTs sat between banks three rows apart, and the
    # two wires of the data path were 855 and 765 ps against 540 for a hop
    # to the next row; that is what sizes the matched delay.
    def side_bank_atoms(comp):
        i = 0
        carry = []
        first = True
        while i < len(comp) and comp[i] not in bank_of:
            carry.extend(expand(comp[i]))
            i += 1
        while i < len(comp):
            n = comp[i]
            i += 1
            after = []
            while i < len(comp) and comp[i] not in bank_of:
                after.extend(expand(comp[i]))
                i += 1
            node = expand(n)
            row_in = ROW_IN if len(node) == 1 else 1
            row_out = ROW_SLOTS - len(node) - row_in
            cut = max(0, len(carry) - row_in)
            head, tail = carry[:cut], carry[cut:]
            run, carry = after[:row_out], after[row_out:]
            bank = bank_of[n]
            half = len(bank) // 2
            if head or not first:
                yield [ROW] + (head or [None] * ROW_SLOTS)
            first = False
            yield [ROW] + tail + node + run + \
                [Side(bank[:half], -1), Side(bank[half:], 1)]
        for k in carry:
            yield [k]

    # v9: the row is shared.  A stage's control that is on the cycle at a
    # fixed cost -- its C node, the OR and joins the node drives, its ack
    # delay, and the LAST link of every chain that requests it -- is three
    # to five LUTs, so two stages' worth is one tile, and every hop of a
    # two-stage ring is in-tile.  The other links of a chain are a matched
    # delay whose wires the resize absorbs; they go beside the row, in a
    # side column, and the bank halves of the row's stages stack above and
    # below it as in v8.
    def requested(links):
        cs = {chain_of.get(s, s) for g in out_nets[links[-1]] for s in sinks.get(g, ())}
        cs = {c for c in cs if c in bank_of}
        return cs.pop() if len(cs) == 1 else None

    def shared_row_atoms(comp):
        cnodes = [n for n in comp if n in bank_of]
        if not cnodes:
            for n in comp:
                for k in expand(n):
                    yield [k]
            return
        tail = {c: [] for c in cnodes}
        run = {c: [] for c in cnodes}
        beside = {c: [] for c in cnodes}
        spill = {c: [] for c in cnodes}
        inner_of = []
        cur = cnodes[0]
        for n in comp:
            if n in bank_of:
                cur = n
            elif n in chains:
                links = chains[n]
                tail[requested(links) or cur].append(links[-1])
                if len(links) > 1:
                    inner_of.append((links[:-1], cur))
            else:
                run[cur].append(n)
        # A chain's inner links hang off the row of the C node that drives
        # it (an ack delay) or of the node whose row holds its driver (the OR
        # in front of a request delay) -- not of wherever the walk came from.
        owner = {k: c for c in cnodes for k in tail[c] + run[c]}
        for inner, cur in inner_of:
            ins = [chain_of.get(drivers[g], drivers[g])
                   for g in in_nets[inner[0]] if g in drivers]
            at = next((k for k in ins if k in bank_of), None) or \
                next((owner[k] for k in ins if k in owner), cur)
            if len(inner) > SIDE_CHAIN:
                spill[at].extend(inner)
            else:
                beside[at].append(inner)
        # Rows are packed in walk order.  Pairing the two stages of a bd_pipe
        # instead (their request delay and acknowledge are the ring's two
        # stage-to-stage hops) was measured on xorshift_round, cap 4, six
        # routes each: latency 7.72 -> 7.43 ns, but the fast-source interval
        # 5.67 -> 5.94 ns, because the link in front of the pipe then sits
        # across the pipe's bank from stage 0, and the matched delay between
        # their banks -- which is on the same ring -- grew by more than the
        # hop it saved.  Whichever pair shares the row, one pair does not.
        rows, row = [], []
        for c in cnodes:
            block = tail[c] + expand(c) + run[c]
            if row and sum(len(bank_of[c2]) // 2 for c2, _ in row) + len(bank_of[c]) // 2 \
                    > ROW_SLOTS * ROW_BANK_ROWS or sum(len(b) for _, b in row) + len(block) > ROW_SLOTS:
                rows.append(row)
                row = []
            row.append((c, block))
        rows.append(row)
        for row in rows:
            atom = [ROW]
            for c, _ in row:
                atom += bank_of[c][:len(bank_of[c]) // 2]
            atom.append(ROW)
            for c, block in row:
                for k in block:
                    atom.append(k)
                    if k == c:
                        atom += [Side(inner) for inner in beside[c]]
            atom.append(ROW)
            for c, _ in row:
                atom += bank_of[c][len(bank_of[c]) // 2:]
            yield atom
            for c, _ in row:
                for k in spill[c]:
                    yield [k]

    def with_atom(seg, atom):
        out = seg.copy()
        for a in atom:
            if a is ROW:
                while len(out.slots) % ROW_SLOTS:
                    out.slots.append(None)
            elif isinstance(a, Side):
                out.beside.append((a.links, len(out.slots) - 1, a.col))
            else:
                out.slots.append(a)
        return out

    limit = SPINE_SEGMENT_V8 if control_row or shared_rows or side_banks else \
        SPINE_SEGMENT_V6 if banks_on_spine else SPINE_SEGMENT
    n_spines = n_slots = 0
    n_side_links = n_spine_links_loose = 0
    taken = defaultdict(lambda: {-1: set(), 1: set()})
    beside_at = {}
    seg_sizes = []
    segments = []
    for comp in spine_order(nodes, adj):
        if sum(len(chains.get(n, [n])) for n in comp) < 2:
            continue
        segs, seg = [], Seg()
        for atom in atoms(comp):
            grown = with_atom(seg, atom)
            if seg.slots and len(grown.slots) > limit:
                segs.append(seg)
                grown = with_atom(Seg(), atom)
            seg = grown
        segs.append(seg)
        for seg in segs:
            while seg.slots and seg.slots[-1] is None:
                seg.slots.pop()
            members = [k for k in seg.slots if k is not None]
            if len(members) < 2:
                continue
            g = "bdspine_" + scope(members[0][0]) + re.sub(r"[^A-Za-z0-9_]", "_", members[0][1])
            for i, key in enumerate(seg.slots):
                if key is None:
                    continue
                mname, cname = key
                attrs = mods[mname]["cells"][cname].setdefault("attributes", {})
                attrs[ATTR] = g
                attrs[SLOT_ATTR] = i
            n_spines += 1
            n_slots += len(members)
            seg_sizes.append(len(seg.slots))
            segments.append((g, seg.slots))
            n_beside, n_loose_links, beside_at[g] = place_beside(mods, g, seg.beside, taken)
            n_side_links += n_beside
            n_spine_links_loose += n_loose_links

    if datapath_beside:
        dp = stamp_datapath(mods, cells, rst, segments, taken, beside_at)

    if report:
        variant = "v10" if side_banks else "v9" if shared_rows else "v8" if control_row \
            else "v7" if datapath_beside else "v6" if banks_on_spine else "v5"
        print(f"rloc_stamp   variant {variant}")
        print(f"             {n_cands} controller candidate(s) matched "
              f"'{RE_CNODE.pattern}', {len(ctl_block)} decoupled")
        where = "around their C node on the spine" if banks_on_spine \
            else "without their C node"
        print(f"             {n_banks} latch bank(s) grouped {where}, "
              f"{n_latch} latch LUT(s)")
        print(f"             {len(control)} control LUT(s) on {n_spines} spine "
              f"segment(s) of {sorted(seg_sizes, reverse=True)} slot(s), "
              f"{n_slots} slot-ordered")
        if shared_rows:
            print(f"             {n_side_links} delay link(s) beside their row, "
                  f"{n_spine_links_loose} left to the placer for want of a side slot")
        if side_banks:
            print(f"             {n_side_links} latch LUT(s) beside their node's row, "
                  f"{n_spine_links_loose} left to the placer for want of a side slot")
        if datapath_beside:
            n_dp, n_far, n_loose, per_col = dp
            print(f"             {n_dp} data-path LUT(s) beside the spine "
                  f"({per_col[-1]} left, {per_col[1]} right, {per_col[0]} in its gaps), "
                  f"{n_far} too far from a free side slot, "
                  f"{n_loose} not connected to any spine")
    if n_cands == 0 and not has_link_structures(mods):
        print("rloc_stamp   note: no bd_link/bd_pipe instances; nothing to stamp",
              file=sys.stderr)
    elif n_spines == 0:
        print("rloc_stamp   WARNING: no spine could be formed -- no control LUT "
              "is connected to another", file=sys.stderr)
    return n_spines + (0 if banks_on_spine else n_banks), n_cands


def stamp(mods, variant, report):
    if variant in ("v5", "v6", "v7", "v8", "v9", "v10"):
        return stamp_v5(mods, report, banks_on_spine=variant != "v5",
                        datapath_beside=variant in ("v7", "v8", "v9", "v10"),
                        control_row=variant == "v8", shared_rows=variant == "v9",
                        side_banks=variant == "v10")
    counts, top = instantiation_counts(mods)
    if top is None:
        raise SystemExit("no top module in this netlist")

    n_groups = n_members = 0
    n_w1 = n_wide = 0
    n_consumer = 0
    n_latch = 0
    n_chains = n_chain_links = 0
    n_cands = 0
    n_split = n_split_stages_dropped = 0
    skipped_shared = []
    bank_sizes = []

    for mname, m in sorted(mods.items()):
        cells = m.get("cells")
        if not cells:
            continue
        cands = [n for n in cells if RE_CNODE.match(n)]
        chains = defaultdict(list)
        if variant == "v4":
            for cname in sorted(cells):
                hit = RE_DLINK.match(cname)
                if hit:
                    chains[hit.group("dly")].append(cname)
        if not cands and not chains:
            continue
        if counts.get(mname, 0) != 1:
            skipped_shared.append((mname, counts.get(mname, 0), len(cands)))
            continue

        # Group strings are matched design-wide after nextpnr flattens, so a
        # name inside a submodule is qualified by the module: two fused
        # compute cells (bdc_fused_*, kept hierarchical so DELAY stays a
        # knob) both own a `udly.chain`.
        scope = "" if mname == top else re.sub(r"[^A-Za-z0-9_]", "_", mname) + "__"
        for dly, links in sorted(chains.items()):
            if len(links) < 2:
                continue
            g = "bddly_" + scope + re.sub(r"[^A-Za-z0-9_]", "_", dly)
            for mn in links:
                cells[mn].setdefault("attributes", {})[ATTR] = g
            n_chains += 1
            n_chain_links += len(links)
        if not cands:
            continue

        n_cands += len(cands)
        drv, snk = net_maps(cells)
        sel = select_sites(cells, drv)

        for cname in sorted(cands):
            link = RE_CNODE.match(cname).group("link")
            c = cells[cname]

            stages = stage_banks(c, link, snk)
            if not stages:
                continue

            # Score each stage this controller drives: which bit of ITS bank
            # to grab (prefer one that feeds a select -- that is the bit rule
            # E measures -- otherwise the first), and whether it found one.
            scored = []
            for port, bank in stages:
                bank_sizes.append(len(bank))
                if len(bank) == 1:
                    n_w1 += 1
                else:
                    n_wide += 1
                chosen, consumers = bank[0], []
                for lname in bank:
                    lc = cells[lname]
                    ldirs = lc.get("port_directions", {})
                    obits = [b for p, bits in lc.get("connections", {}).items()
                             if ldirs.get(p) == "output" for b in bits
                             if isinstance(b, int)]
                    hit = [x for b in obits for x in sel.get(b, ())]
                    if hit:
                        chosen, consumers = lname, hit
                        break
                scored.append((port, chosen, consumers))

            # A multi-output controller sits in ONE physical logic slot
            # and can join only ONE of its stages' clusters -- picking
            # both would ask nextpnr to hold two different latch banks, each
            # already anchored to its OWN stage's fanout, in the same SLICE
            # as a controller that belongs equally to both.  Prefer the stage
            # whose chosen bit feeds a select (that is the site rule E
            # measures) and otherwise the earlier stage, same tie-break as
            # picking a bit within one bank.
            if len(scored) > 1:
                n_split += 1
                n_split_stages_dropped += len(scored) - 1
            port, chosen, consumers = next(
                (s for s in scored if s[2]), scored[0])

            members = [cname, chosen]
            if variant in WHOLE_BANK:
                bank = next(b for p, b in stages if p == port)
                members += [l for l in bank if l != chosen]
            n_latch += len(members) - 1
            if variant != "v1" and consumers:
                # A SLICE is four LUTs.  The two joins of one bd_mux fit
                # alongside the pair; a latch feeding more than one consumer
                # does not, and taking an arbitrary subset would silently
                # constrain one site and not another, so leave those alone.
                if variant in WHOLE_BANK or len(members) + len(consumers) <= 4:
                    members += sorted(consumers)
                    n_consumer += 1

            if len(members) < 2:
                continue
            # Keyed on the controller's own instance path, not just `link`:
            # one bd_pipe instance owns several controller candidates
            # (one per stage), each its own physical cluster.  Keying on `link` alone would hand two unrelated
            # clusters the same RLOC_GROUP string and ask nextpnr to fuse
            # them into one SLICE.
            g = "bdlink_" + scope + re.sub(r"[^A-Za-z0-9_]", "_", cname)
            for mn in members:
                cells[mn].setdefault("attributes", {})[ATTR] = g
            n_groups += 1
            n_members += len(members)

    if report:
        print(f"rloc_stamp   variant {variant}")
        print(f"             {n_cands} controller candidate(s) matched "
              f"'*.ctl.u.u'")
        print(f"             {n_groups} group(s), {n_members} logic slot(s) "
              f"named")
        print(f"             {n_w1} link/stage bank(s) that ARE one LUT "
              f"(W<=2), {n_wide} wider bank(s) where "
              + ("the whole bank is" if variant in WHOLE_BANK else
                 "only the named bit is") + " constrained")
        if bank_sizes:
            tot = sum(bank_sizes)
            print(f"             {tot} latch LUT(s) across those banks, "
                  f"{n_latch} of them grouped "
                  f"({100.0 * n_latch / tot:.1f}%)")
        if variant != "v1":
            print(f"             {n_consumer} group(s) also hold their select "
                  f"consumer's LUTs")
        if variant == "v4":
            print(f"             {n_chains} delay chain(s) grouped, "
                  f"{n_chain_links} link LUT(s)")
        if n_split:
            print(f"             {n_split} multi-output controller(s) each "
                  f"drive two pipeline stages from one LUT; only one "
                  f"stage's latch can share its SLICE, so "
                  f"{n_split_stages_dropped} stage(s) are left out of any "
                  f"group by construction, not by omission")
        for mname, cnt, ncand in skipped_shared:
            print(f"             SKIPPED {mname}: instantiated {cnt}x, "
                  f"{ncand} controller(s) -- one group value cannot name "
                  f"more than one physical cluster")

    # A stamp that names nothing is not a quiet success: it means every
    # storage cell in this netlist is free for the placer to drag away, and
    # the next thing to notice will be a rule-E violation with no idea why.
    # Say so unconditionally -- not gated on --report -- and let main() turn
    # it into a failing exit code.
    if n_cands == 0 and not has_link_structures(mods):
        print("rloc_stamp   note: this netlist contains no bd_link/bd_pipe "
              "instances at all, so there is no latch cluster to hold "
              "together and nothing to stamp.  Not a failure: a design built "
              "straight on primitives has no storage for RLOC_GROUP to "
              "govern.", file=sys.stderr)
    elif n_cands == 0:
        print("rloc_stamp   WARNING: 0 controller(s) matched "
              "'*.ctl.u.u' in any module, "
              "BUT this netlist does contain bd_link/bd_pipe instances -- "
              "no RLOC_GROUP attributes written, every storage cell in this "
              "netlist floats", file=sys.stderr)
    elif n_groups == 0:
        print(f"rloc_stamp   WARNING: {n_cands} controller candidate(s) "
              f"matched but none could be paired with a latch bank -- no "
              f"RLOC_GROUP attributes written", file=sys.stderr)
    return n_groups, n_cands


def main():
    args = sys.argv[1:]
    variant = "v1"
    if "--variant" in args:
        i = args.index("--variant")
        variant = args[i + 1]
        del args[i:i + 2]
    weight = 1
    if "--place-weight" in args:
        i = args.index("--place-weight")
        weight = int(args[i + 1])
        del args[i:i + 2]
    if "--column-rows" in args:
        i = args.index("--column-rows")
        set_column_rows(int(args[i + 1]))
        del args[i:i + 2]
    if "--row-bank-rows" in args:
        global ROW_BANK_ROWS
        i = args.index("--row-bank-rows")
        ROW_BANK_ROWS = int(args[i + 1])
        del args[i:i + 2]
    report = "--report" in args
    args = [a for a in args if not a.startswith("-")]
    if len(args) != 2 or variant not in VARIANTS:
        print(__doc__)
        return 2
    d = load(args[0])
    ok = True
    if weight > 1:
        weight_control_nets(d["modules"], weight, report)
    if variant != "none":
        n_groups, n_cands = stamp(d["modules"], variant, report)
        # Zero groups is fatal ONLY when there was something to group.  A
        # primitive-only top (ro_top, ro_many_top) legitimately stamps
        # nothing; failing it made ro_top unbuildable once BD_RLOC=v2 became
        # the default, which quietly cost us the ability to reproduce the very
        # calibration the guardband rests on.
        ok = n_groups > 0 or not has_link_structures(d["modules"])
    with open(args[1], "w") as f:
        json.dump(d, f)
    # A silent no-op used to exit 0 and only be noticed once rule E failed on
    # a build nobody thought to suspect.  Matching zero groups to a nonzero
    # exit means flow.sh's `|| { RLOC STAMP FAILED; exit 1; }` catches it at
    # the source instead.
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
