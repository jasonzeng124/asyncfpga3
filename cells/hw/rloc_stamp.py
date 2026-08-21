#!/usr/bin/env python3
"""rloc_stamp.py -- put RLOC_GROUP relative-placement attributes on a
post-synthesis netlist.

WHY THIS IS A SEPARATE PASS AND NOT RTL.  cells/rtl/ is frozen, so the
attribute cannot be written next to the cells it constrains.  It is stamped
here instead, on the JSON yosys just wrote, keyed on the instance paths the
library commits to (`<link>.ctl.u.u`, `<link>.lat.*`, `<mux>.uj0/uj1`) -- the
same anchors verify/tighten.py's select_consumers() uses, and for the same
reason: those names are the library's, not the compiler's.

WHAT NEXTPNR DOES WITH IT.  Nothing that knows what a bd_link is.  The packer
pass (xilinx/pack.cc, pack_rloc_groups) reads one generic attribute: cells
carrying the same RLOC_GROUP string are tied into one cluster -- same tile,
consecutive logic slots -- and the cluster as a whole floats.  That is
Vivado's RLOC, not a LOC: no cell is ever pinned to a BEL and the placer still
chooses where the group lands.  A SLICE on xc7 holds four LUTs, so a group may
name at most four logic slots (a fractured LUT6_2 pair is one slot).

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

Only ONE latch LUT per link is grouped: a bd_latch packs two data bits per
LUT6_2, so a W=32 link is 16 of them and a four-LUT cluster cannot hold the
bank.  The bit that is grouped is chosen deliberately -- the one that drives a
select consumer where there is one, otherwise the first -- and the report says
how many links are W=1 (where one LUT IS the whole bank) so the reach of the
constraint is never overstated.

usage: rloc_stamp.py IN.json OUT.json --variant v1|v2|none [--report]

NOT YET WIRED INTO build_hw.sh -- that file has another owner.  The hook is
three lines, between `write_json` and the nextpnr invocation:

    if [ -n "${BD_RLOC:-}" ]; then
        python3 "$(dirname "$0")/rloc_stamp.py" "$OUT/$TOP.json" \
            "$OUT/$TOP.rloc.json" --variant "$BD_RLOC" --report &&
            mv "$OUT/$TOP.rloc.json" "$OUT/$TOP.json"
    fi

and it needs a nextpnr carrying patches/nextpnr-xilinx-rloc-group.patch; an
unpatched binary ignores the attribute silently, which is exactly the failure
mode cells/verify/toolchain.sh exists to catch.  Until then,
cells/verify/rloc_sweep.sh drives the whole thing from the JSON build_hw.sh
already wrote.
"""

import json
import re
import sys
from collections import defaultdict

ATTR = "RLOC_GROUP"

# The library's own instance names.  bd_link's controller is `ctl.u.u`; a
# bd_pipe pairs two stages' controllers into one fractured LUT6_2 at
# `many.cpair[i].u.u` with an odd final stage at `many.codd.u.u`.
RE_CNODE = re.compile(
    r"^(?P<link>.*ulink_[A-Za-z0-9_]+)\."
    r"(?:ctl\.u\.u|many\.(?:cpair\[\d+\]|codd)\.u\.u)$")


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


def stamp(mods, variant, report):
    counts, top = instantiation_counts(mods)
    if top is None:
        raise SystemExit("no top module in this netlist")

    n_groups = n_members = 0
    n_w1 = n_wide = 0
    n_consumer = 0
    skipped_shared = []
    bank_sizes = []

    for mname, m in sorted(mods.items()):
        cells = m.get("cells")
        if not cells:
            continue
        cands = [n for n in cells if RE_CNODE.match(n)]
        if not cands:
            continue
        if counts.get(mname, 0) != 1:
            skipped_shared.append((mname, counts.get(mname, 0), len(cands)))
            continue

        drv, snk = net_maps(cells)
        sel = select_sites(cells, drv)

        for cname in sorted(cands):
            link = RE_CNODE.match(cname).group("link")
            c = cells[cname]
            dirs = c.get("port_directions", {})
            outs = [b for p, bits in c.get("connections", {}).items()
                    if dirs.get(p) == "output" for b in bits
                    if isinstance(b, int)]

            # The latch bank this controller enables: sinks of the C node's
            # own output that live under the same link and inside its `lat`.
            bank = []
            for b in outs:
                for sname, _ in snk.get(b, ()):
                    if sname.startswith(link + ".") and ".lat" in sname[len(link):]:
                        if sname not in bank:
                            bank.append(sname)
            if not bank:
                continue
            bank.sort()
            bank_sizes.append(len(bank))
            if len(bank) == 1:
                n_w1 += 1
            else:
                n_wide += 1

            # Which bit of the bank to grab.  Prefer one that drives a select
            # -- that is the bit rule E measures -- otherwise the first.
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

            members = [cname, chosen]
            if variant == "v2" and consumers:
                # A SLICE is four LUTs.  The two joins of one bd_mux fit
                # alongside the pair; a latch feeding more than one consumer
                # does not, and taking an arbitrary subset would silently
                # constrain one site and not another, so leave those alone.
                if len(members) + len(consumers) <= 4:
                    members += sorted(consumers)
                    n_consumer += 1

            if len(members) < 2:
                continue
            g = "bdlink_" + re.sub(r"[^A-Za-z0-9_]", "_", link)
            for mn in members:
                cells[mn].setdefault("attributes", {})[ATTR] = g
            n_groups += 1
            n_members += len(members)

    if report:
        print(f"rloc_stamp   variant {variant}")
        print(f"             {n_groups} group(s), {n_members} logic slot(s) "
              f"named")
        print(f"             {n_w1} link(s) whose latch bank IS one LUT "
              f"(W<=2), {n_wide} wider link(s) where only the named bit is "
              f"constrained")
        if bank_sizes:
            tot = sum(bank_sizes)
            print(f"             {tot} latch LUT(s) in those banks, "
                  f"{n_groups} of them grouped "
                  f"({100.0 * n_groups / tot:.1f}%)")
        if variant == "v2":
            print(f"             {n_consumer} group(s) also hold their select "
                  f"consumer's LUTs")
        for mname, cnt, ncand in skipped_shared:
            print(f"             SKIPPED {mname}: instantiated {cnt}x, "
                  f"{ncand} controller(s) -- one group value cannot name "
                  f"more than one physical cluster")
    return n_groups


def main():
    args = sys.argv[1:]
    variant = "v1"
    if "--variant" in args:
        i = args.index("--variant")
        variant = args[i + 1]
        del args[i:i + 2]
    report = "--report" in args
    args = [a for a in args if not a.startswith("-")]
    if len(args) != 2 or variant not in ("v1", "v2", "none"):
        print(__doc__)
        return 2
    d = load(args[0])
    if variant != "none":
        stamp(d["modules"], variant, report)
    with open(args[1], "w") as f:
        json.dump(d, f)
    return 0


if __name__ == "__main__":
    sys.exit(main())
