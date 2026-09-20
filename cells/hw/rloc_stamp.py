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

usage: rloc_stamp.py IN.json OUT.json --variant v1|v2|v3|v4|none [--report]

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
import re
import sys
from collections import defaultdict

ATTR = "RLOC_GROUP"
WHOLE_BANK = ("v3", "v4")

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
RE_CNODE = re.compile(r"^(?P<link>.+)\.ctl\.u\.u$")
# bd_delay's links: `<dly>.chain.g[i].u` (cells/rtl/bd_latch.v), the same
# chain whether symmetric, FASTFALL or FASTRISE.
RE_DLINK = re.compile(r"^(?P<dly>.+\.chain)\.g\[\d+\]\.u$")


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


def stamp(mods, variant, report):
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
    report = "--report" in args
    args = [a for a in args if not a.startswith("-")]
    if len(args) != 2 or variant not in ("v1", "v2", "v3", "v4", "none"):
        print(__doc__)
        return 2
    d = load(args[0])
    ok = True
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
