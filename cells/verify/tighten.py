#!/usr/bin/env python3
"""Post-route matched-delay sizing and bundling audit, from the routed SDF.

Every DELAY, DSETUP and DCO in rtl/ is a placeholder.  The number that belongs
there is not derivable from the source, from a synthesis estimate, or from
abc9's timing model -- it is a property of where the router happened to put
things, and on this part routing is about three quarters of a hop and moves
around a nanosecond between builds.  So sizing is a pass over a ROUTED design,
it runs unconditionally after place-and-route, and it TIGHTENS.  A line that
comes out needing to grow is not a sizing result, it is a bundling violation,
and this tool says so in those words.

    ./flow.sh                    # writes build/pnr/soak.sdf
    python3 verify/tighten.py

-- the three rules ----------------------------------------------------------

A.  THE REQUEST IS THE LAST THING A CELL EMITS.  For a cell with a matched
    delay on its outgoing request, that request must arrive later than every
    other output the same cell produces from the same source, by the review's
    guardband max(0.2*t_data, 200 ps).  This is the general form of
    "z_req = delta(...)": the delay exists so the request cannot announce a
    value that has not finished being computed.

B.  THE RAM BOUNDARY IS A REAL SETUP CHECK.  It is the one edge-sampled
    boundary in the library -- everywhere else the consumer is a transparent
    latch that closes a full phase later, which is why the hold window ends at
    ack-fall.  Here the guardband is not a percentage, it is the vendor's own
    number out of prjxray's BRAM_L.sdf: 566 ps on address, 737 on write data,
    532 on write enable.

C.  CLOCK-TO-OUT.  The acknowledge tapped off the RAM clock must be at least
    t_co = 2454 ps behind it, or the read data is announced before it exists.

-- how a setup check is actually done ---------------------------------------

Late signal on the SHORTEST path, early signal on the LONGEST.  A request that
happens to have one fast route is what breaks the bundle, not its average, and
data that has one slow route is what it breaks against.  Both are measured
from a COMMON START POINT where the cell admits one: a matched delay covers
combinational logic inside one cell's own datapath, and a path that does not
share a start point with the request is the upstream sender's obligation, not
this delay's.

Every hand-written cell in rtl/ does admit one -- its request and its datapath
fan out from the same net inside the cell.  A GENERATED compute unit does not:
its request arrives on a_req and its operands on a_data.  Those are two halves
of one bundled channel, launched together by the upstream cell's own rule A, so
they are paired without a shared start -- earliest request against latest data,
which is strictly more pessimistic than a common start would be.  See
check_bundled.  Which pairing produced a number is always printed.

-- what the numbers are made of ---------------------------------------------

Interconnect delays are REAL: nextpnr writes the delay of the route it
actually picked.  Cell arcs are nextpnr's own model, a flat 124 ps per LUT,
not the per-pin prjxray arcs sim/bd_prims_sim.v uses (56-152 ps depending on
pin and edge).  Routing dominates so heavily on this fabric that the
difference rarely moves a chain by a link, but the arcs are the weaker half of
every number below and must not be quoted as silicon.

-- the loop model -----------------------------------------------------------

Every C-element and every latch here is a LUT feedback loop, so the netlist is
not a DAG and a naive longest path does not terminate.  A pin on a cycle is a
STATE NODE, and the analysis starts and stops at state nodes -- exactly the
four-phase model, where every handshake node is storage and a phase is one hop
between two of them.  Traversal never passes through a state node, so every
path considered here is acyclic by construction.
"""

import json
import math, re, sys, pathlib
from collections import defaultdict

ROOT = pathlib.Path(__file__).resolve().parent.parent

# argv: [sdf]  [--emit <path>]
_args  = [a for a in sys.argv[1:] if not a.startswith("--")]
_flags = [a for a in sys.argv[1:] if a.startswith("--")]
EMIT = None
if "--emit" in sys.argv:
    EMIT = pathlib.Path(sys.argv[sys.argv.index("--emit") + 1])
    _args = [a for a in _args if a != str(EMIT)]
# Default is what flow.sh writes; an explicit path lets the gate be pointed at
# a deliberately under-delayed build to confirm it still has teeth.
SDF = pathlib.Path(_args[0]) if _args else ROOT / "build/pnr/soak.sdf"


def macro(path):
    """An instance path as a Verilog macro name: umem.usetup -> BD_SZ_UMEM_USETUP."""
    return "BD_SZ_" + re.sub(r"[^A-Za-z0-9]", "_", path).upper()

# prjxray BRAM_L.sdf, max corner -- the same constants sim/bd_prims_sim.v
# enforces, so the simulation gate and this gate cannot drift apart.
T_SU = {"ADDRARDADDR": 566, "DIADI": 737, "WEA": 532}
T_CO = 2454

RE_INSTANCE = re.compile(r"\(INSTANCE\s+(\S*)\s*\)")
RE_CELLTYPE = re.compile(r'\(CELLTYPE\s+"([^"]*)"\)')
RE_IOPATH   = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):")
RE_INTERCON = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):")
RE_LINK     = re.compile(r"^(?P<base>.+)\.chain\.g\[(?P<i>\d+)\]\.u$")


def unescape(s):
    return s.replace("\\", "")


def pin_split(pin):
    inst, _, port = pin.rpartition("/")
    return inst, port


def is_output(pin):
    return pin_split(pin)[1].startswith("O")


# --------------------------------------------------------------------- parse

def parse_sdf(path):
    edges = defaultdict(list)
    celltype, inst = {}, None
    ct = None
    n_io = n_ic = 0
    for line in path.read_text().splitlines():
        m = RE_CELLTYPE.search(line)
        if m:
            ct = m.group(1)
            continue
        m = RE_INSTANCE.search(line)
        if m:
            inst = unescape(m.group(1))
            celltype[inst] = ct
            continue
        m = RE_IOPATH.search(line)
        if m and inst is not None:
            a, z, d = unescape(m.group(1)), unescape(m.group(2)), int(m.group(3))
            edges[f"{inst}/{a}"].append((f"{inst}/{z}", d))
            n_io += 1
            continue
        m = RE_INTERCON.search(line)
        if m:
            src, dst, d = unescape(m.group(1)), unescape(m.group(2)), int(m.group(3))
            edges[src].append((dst, d))
            n_ic += 1
    return edges, celltype, n_io, n_ic


# ------------------------------------------------------------ the loop model
#
# STORAGE AND CYCLES ARE DIFFERENT THINGS, and this pass used to treat them as
# one.  They coincide in verify/soak_top.v and they come apart in every design
# that actually handshakes, which is why the conflation survived so long.
#
#   Storage is a LUT whose output feeds its own input.  On this fabric that is
#   the only way a LUT holds anything -- every C-element, every latch, the
#   arbiter's state node.  It is structural, local, and decidable by looking at
#   one instance.
#
#   A cycle in the netlist graph is the HANDSHAKE.  A four-phase channel is a
#   ring by construction: the request goes forward and the acknowledge comes
#   back.  Rings are the protocol, not memory.
#
# Defining a start point as "any pin on a cycle" over-approximates storage by
# exactly the set of combinational gates that happen to sit on a handshake
# ring.  soak_top.v deliberately never closes one -- it cross-wires acks into
# data bits so no cell duplicates another -- so there the two definitions agree
# and nothing was ever wrong.  In a real pipeline the ring passes through every
# cell, so the over-approximation swallows the matched delay itself: measured
# on the first generated kernel, 51 delay-chain links, 7 request ORs and 5
# acknowledge gates were all being called state.  A chain whose own links are
# start points has its tail in its own start set, and the request then measures
# as arriving at itself in 0 ps -- which is precisely the failure
# bdc/compute.py's emit_proto_top docstring records hitting from the other
# direction.
#
# Cutting at storage rather than at cycles yields a DAG, and that is an
# invariant of the library rather than a hope: every handshake ring must
# contain a rendezvous, because a ring of purely combinational gates IS a
# combinational loop -- the same property bdc/slack.py checks on the handshake
# graph, stated at the netlist level.  So it is asserted below rather than
# assumed, and a leftover cycle is reported by name.

def storage_nodes(edges):
    """Output pins that feed an input of their OWN instance: the real storage.

    This is the census of latches and C-elements, and unlike a cycle census it
    cannot be inflated by the protocol wrapped around them.
    """
    out = set()
    for src, lst in edges.items():
        if not is_output(src):
            continue
        inst = pin_split(src)[0]
        for dst, _ in lst:
            if pin_split(dst)[0] == inst and not is_output(dst):
                out.add(src)
                break
    return out


def state_nodes(edges):
    """Pins that lie on a cycle (iterative Tarjan)."""
    index, low, on_stack, stack = {}, {}, set(), []
    result, counter = set(), [0]

    nodes = set(edges)
    for lst in edges.values():
        nodes.update(d for d, _ in lst)

    for root in nodes:
        if root in index:
            continue
        index[root] = low[root] = counter[0]; counter[0] += 1
        stack.append(root); on_stack.add(root)
        work = [(root, iter(edges.get(root, ())))]
        while work:
            node, it = work[-1]
            advanced = False
            for dst, _ in it:
                if dst not in index:
                    index[dst] = low[dst] = counter[0]; counter[0] += 1
                    stack.append(dst); on_stack.add(dst)
                    work.append((dst, iter(edges.get(dst, ()))))
                    advanced = True
                    break
                if dst in on_stack:
                    low[node] = min(low[node], index[dst])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[node])
            if low[node] == index[node]:
                comp = []
                while True:
                    w = stack.pop(); on_stack.discard(w); comp.append(w)
                    if w == node:
                        break
                if len(comp) > 1:
                    result.update(comp)
                elif any(d == node for d, _ in edges.get(node, ())):
                    result.add(node)
    return result


# -------------------------------------------------------- longest / shortest

def walk(edges, start, stops, longest, confine=None):
    """Extremal path length from `start` to everything reachable without
    passing through a stop pin.  longest=True for the data side of a setup
    check, False for the signal that has to be late.

    `confine` restricts the traversal to one cell's subtree, and it is not an
    optimisation -- it is the definition.  A matched delay covers combinational
    logic INSIDE ONE CELL.  Let the walk wander out through the rest of the
    design and back in, and t_data becomes an accumulated arrival from half the
    netlist; 0.2*t_data becomes a guardband on somebody else's path; and every
    line in the design reports as a violation.
    """
    def inside(pin):
        if confine is None:
            return True
        i = pin_split(pin)[0]
        return i == confine or i.startswith(confine + ".")

    best = {start: 0}
    frontier, guard = [start], 0
    better = (lambda a, b: a > b) if longest else (lambda a, b: a < b)
    while frontier:
        guard += 1
        if guard > 100000:
            raise RuntimeError("traversal did not settle -- a combinational "
                               "loop with no state node in it")
        nxt = []
        for pin in frontier:
            t = best[pin]
            for dst, d in edges.get(pin, ()):
                if not inside(dst):
                    continue
                if dst not in best or better(t + d, best[dst]):
                    best[dst] = t + d
                    if dst not in stops:
                        nxt.append(dst)
        frontier = nxt
    return best


def reaches(edges, start, stops):
    """Every pin reachable from `start` without passing through a stop."""
    seen, work = {start}, [start]
    while work:
        p = work.pop()
        for d, _ in edges.get(p, ()):
            if d not in seen:
                seen.add(d)
                if d not in stops:
                    work.append(d)
    return seen


def cell_boundary(edges, back, stops, parent):
    """The start points for a cell's OWN datapath: the nets that enter it from
    outside, plus any state node it contains.

    This is the part that has to be right.  A matched delay covers
    combinational logic inside one cell, so the guardband is a fraction of THAT
    path -- not of an arrival time accumulated through half the design before
    the cell was even reached.  Measuring from a distant state node inflates
    t_data, inflates 0.2*t_data with it, and turns every line in the design
    into a violation.
    """
    prefix = parent + "."
    inside = {p for p in set(edges) | {d for l in edges.values() for d, _ in l}
              if pin_split(p)[0] == parent or pin_split(p)[0].startswith(prefix)}
    starts = set()
    for p in inside:
        for s in back.get(p, ()):
            if s not in inside:
                starts.add(s)
        if p in stops:
            starts.add(p)
    return starts


# The packer's tie-off drivers.  A net held at 0 or 1 for the life of the
# design never transitions, so it cannot be the start of a timing path -- yet
# it fans out to nearly every cell, which makes it the one "common source" that
# any two pins in the design are guaranteed to share.  Left in, it turns every
# setup check into a measurement between two arrivals that never happen.
CONST_DRV = ("$PACKER_GND_DRV", "$PACKER_VCC_DRV")


def is_const(pin):
    return pin_split(pin)[0] in CONST_DRV


def starts_reaching(back, pin, stops, limit=20000):
    seen, out, work = {pin}, set(), [pin]
    while work and len(seen) < limit:
        p = work.pop()
        srcs = back.get(p, ())
        if not srcs:
            out.add(p)
            continue
        for s in srcs:
            if is_const(s):
                continue
            if s in stops:
                out.add(s)
            elif s not in seen:
                seen.add(s); work.append(s)
    return {p for p in out if not is_const(p)}


class Timing:
    """Arrival tables, computed on demand and keyed by (start, confinement)."""

    def __init__(self, edges, stops):
        self.edges, self.stops = edges, stops
        self._late, self._early = {}, {}

    def late(self, s, confine=None):        # longest path: the data side
        k = (s, confine)
        if k not in self._late:
            self._late[k] = walk(self.edges, s, self.stops, True, confine)
        return self._late[k]

    def early(self, s, confine=None):       # shortest path: the request side
        k = (s, confine)
        if k not in self._early:
            self._early[k] = walk(self.edges, s, self.stops, False, confine)
        return self._early[k]


def check(timing, srcs, late_pins, early_pin, guard_of, confine=None):
    """Worst-case setup margin at `early_pin` against `late_pins`, over every
    start point that reaches both.  Returns (margin, guard, t_early, t_late,
    which_pin, which_start) or None if no common source pairs them."""
    worst = None
    for s in srcs:
        e_tab, l_tab = timing.early(s, confine), timing.late(s, confine)
        if early_pin not in e_tab:
            continue
        t_e = e_tab[early_pin]
        for p in late_pins:
            if p not in l_tab:
                continue
            t_l = l_tab[p]
            g = guard_of(p, t_l)
            margin = t_e - t_l - g
            if worst is None or margin < worst[0]:
                worst = (margin, g, t_e, t_l, p, s)
    return worst


def check_bundled(timing, srcs, late_pins, early_pin, guard_of, confine=None):
    """The same setup margin, for a cell whose request and data enter on
    DIFFERENT nets.  Returns (margin, guard, t_early, t_late, which_pin,
    early_start, late_start) or None.

    check() above pairs the two sides by requiring one start point that reaches
    both.  That is exact, and it is what every hand-written cell in rtl/ admits,
    because in all of them the request and the datapath fan out from the same
    net inside the cell.  A generated compute unit does not: its request arrives
    on a_req and its operands on a_data, so no single start pairs them and
    check() correctly reports that it cannot measure anything.  Under four-phase
    bundled data those wires are not independent -- they are two halves of one
    channel, and the upstream cell's OWN rule A is the guarantee that they are
    launched by one event.  That is precisely the property a common start point
    was standing in for, and the reason this pairing is legitimate rather than a
    relaxation.

    Pairing them without a shared start means assuming every boundary net can
    transition at t=0 together, and then taking the worst combination: the
    EARLIEST the request can leave (min over starts) against the LATEST the
    datapath can settle (max over starts).  Three things follow, and they are
    the whole argument for why this is safe to add:

      It can only ever be more pessimistic than check().  For any single start s
      the margin here is <= the margin check() computes from s, since the min
      and the max are taken over a set containing s.  So no cell that passes
      today can start failing because of a looser rule -- only because a real
      path was being skipped.

      Treating an incoming request as launching at t=0 UNDERSTATES it.  Rule A
      on the upstream cell says its request trails its data; ignoring that head
      start shortens the request side, which shrinks the margin.  Conservative.

      A state node inside the cell is in `srcs` too, and it cannot fire until
      the incoming request has already arrived.  Calling it t=0 on the data side
      overstates how late the data is.  Conservative again.

    So this can report a violation that is not real -- a pessimistic pairing --
    and it cannot hide one.  For a gate that is the correct direction to be
    wrong in, but it does mean a failure here is a reason to look, not proof.
    """
    t_e, e_src = None, None
    for s in srcs:
        tab = timing.early(s, confine)
        if early_pin in tab and (t_e is None or tab[early_pin] < t_e):
            t_e, e_src = tab[early_pin], s
    if t_e is None:
        return None

    worst = None
    for s in srcs:
        tab = timing.late(s, confine)
        for p in late_pins:
            if p not in tab:
                continue
            t_l = tab[p]
            g = guard_of(p, t_l)
            margin = t_e - t_l - g
            if worst is None or margin < worst[0]:
                worst = (margin, g, t_e, t_l, p, e_src, s)
    return worst


# ------------------------------------------------------------------ chains

def find_chains(edges):
    links = defaultdict(dict)
    pins = set(edges)
    for lst in edges.values():
        pins.update(d for d, _ in lst)
    for pin in pins:
        inst, _ = pin_split(pin)
        m = RE_LINK.match(inst)
        if m:
            links[m.group("base")][int(m.group("i"))] = inst
    return {b: [d[i] for i in sorted(d)] for b, d in links.items()}


def chain_endpoints(edges, back, links):
    head = next((p for p in back if pin_split(p)[0] == links[0]
                 and not is_output(p)), None)
    tail = next((p for p in edges if pin_split(p)[0] == links[-1]
                 and is_output(p)), None)
    return head, tail


def request_sites(edges, back, chains):
    """Every cell whose outgoing request this rule applies to, INCLUDING the
    ones whose delay line has length zero.

    Finding these by looking for delay chains was the obvious thing and it was
    wrong: bd_delay #(.N(0)) is a bare wire, so a cell with no delay at all --
    the one case that most needs auditing -- left nothing in the netlist to
    find and was silently skipped.  The anchor is instead the request OR that
    every such cell has, `<cell>.uor`.  The request output is the chain tail
    if there is a chain, and the OR's own output if there is not.

    -> [(parent, head, tail, links)]
    """
    sites = []
    insts = {pin_split(p)[0] for p in edges}
    insts |= {pin_split(d)[0] for l in edges.values() for d, _ in l}
    for inst in sorted(insts):
        if not inst.endswith(".uor"):
            continue
        parent = inst[: -len(".uor")]
        or_out = next((p for p in edges
                       if pin_split(p)[0] == inst and is_output(p)), None)
        if or_out is None:
            continue
        base = next((b for b in chains if b.rpartition(".")[0] == parent), None)
        if base:
            head, tail = chain_endpoints(edges, back, chains[base])
            if head and tail:
                sites.append((parent, head, tail, chains[base]))
                continue
        # No chain: the request leaves the cell straight off the OR.
        head = next((p for p in back if pin_split(p)[0] == inst
                     and not is_output(p)), None)
        sites.append((parent, head or or_out, or_out, []))
    return sites


def median_hop(edges):
    """A stand-in for one link's cost when the design has no chain to measure.
    The median ROUTED hop, which is what a link actually costs here."""
    d = sorted(x for lst in edges.values() for _, x in lst if x > 0)
    return d[len(d) // 2] if d else 1


def false_arcs(edges):
    """Arcs the SDF carries that the logic cannot use.

    The SDF gives every physical LUT input an arc to the output, because the
    silicon propagates every pin.  The FUNCTION need not.  A LUT6_2 with two
    functions sharing one site is the normal case in this library: both halves
    are wired to all five pins, and each half typically ignores some of them.

    Those arcs are not conservative, they are wrong, and they are wrong in a
    direction that matters here.  bd_dr2bd's decode shares its site with the
    request OR: the OR is a function of the rails alone, but the site's pins
    include the decode's own feedback, so the SDF shows a path from the PAYLOAD
    into the REQUEST.  That is the bundling constraint running backwards.  Take
    it at face value and the RAM setup check measures a path that cannot exist,
    from a source half the design away.

    Whether a pin is real is not a judgement call -- it is the INIT constant.
    A function is independent of pin k exactly when flipping k changes nothing
    at any address, which is a finite check over the whole table, the same
    exhaustive argument verify/inits.py makes about the constants themselves.
    Only pins proved dead are cut, so this can never hide a path that exists.

    ONE TRAP, and it is the whole reason this function is longer than it looks.
    The packer permutes LUT inputs freely -- any function can go on any pin --
    and in the routed netlist the two halves of the cell disagree about which
    order they are in.  `connections` are PHYSICAL (A1..A6, what the SDF names)
    while `INIT` stays in the cell's ORIGINAL order (I0..I5).  Read the INIT
    against the physical pins and the answer is not merely approximate, it is
    scrambled: bd_latch_rst comes out "independent of A5" when A5 is the pin
    carrying its own feedback, and cutting that arc would delete the loop, take
    the latch out of the state-node set, and let every walk run straight
    through storage.  A gate that quietly stops seeing paths is worse than no
    gate.  nextpnr records the permutation as X_ORIG_PORT_A<k>, and that
    attribute is the only thing that makes the two orders comparable.
    """
    jpath = SDF.with_name(SDF.stem + "_routed.json")
    if not jpath.exists():
        return set(), jpath
    top = list(json.loads(jpath.read_text())["modules"].values())[0]

    dead = set()
    for name, cell in top.get("cells", {}).items():
        init = cell.get("parameters", {}).get("INIT")
        conns = cell.get("connections", {})
        attrs = cell.get("attributes", {})
        outs = [p for p in conns if p.startswith("O")]
        if not init or not outs:
            continue
        n = len(init).bit_length() - 1
        if 1 << n != len(init):
            continue

        # logical index -> physical pin, from the packer's own record
        phys = {}
        for k in range(1, 7):
            orig = attrs.get(f"X_ORIG_PORT_A{k}")
            if orig and orig.startswith("I") and orig[1:].isdigit():
                phys[int(orig[1:])] = f"A{k}"

        bit = lambda a: init[len(init) - 1 - a]
        for k in range(n):
            if any(bit(a) != bit(a ^ (1 << k)) for a in range(len(init))):
                continue                      # the function uses this pin
            pin = phys.get(k)
            if pin is None:                   # no permutation record: say
                continue                      # nothing rather than guess
            for o in outs:
                dead.add((f"{name}/{pin}", f"{name}/{o}"))
    return dead, jpath


def main():
    if not SDF.exists():
        print(f"no routed SDF at {SDF} -- run ./flow.sh first", file=sys.stderr)
        return 2

    edges, celltype, n_io, n_ic = parse_sdf(SDF)

    dead, jpath = false_arcs(edges)
    if dead:
        before = len(storage_nodes(edges))
        cut = 0
        for src in list(edges):
            keep = [(d, w) for d, w in edges[src] if (src, d) not in dead]
            cut += len(edges[src]) - len(keep)
            edges[src] = keep
        after = len(storage_nodes(edges))
        # storage_nodes IS the census of latches and C-elements -- a LUT that
        # feeds its own input, and nothing else.  Cutting an arc must never
        # change it: if it does, a real dependence has been pruned and the
        # analysis has just been handed permission to walk through a latch.
        if after != before:
            print(f"false arcs   ABORT: pruning removed {before - after} "
                  f"feedback loop(s).  A pin the INIT calls dead is carrying a "
                  f"real dependence, so the pin permutation is being read "
                  f"wrong.  Refusing to analyse a netlist with storage in it "
                  f"that this pass can no longer see.", file=sys.stderr)
            return 2
        print(f"false arcs   {cut} pin-to-output arcs cut -- pins the INIT "
              f"proves the function ignores ({before} loops, unchanged)")
    elif not jpath.exists():
        print(f"false arcs   no routed netlist at {jpath} -- NOT pruned, and a "
              f"shared LUT6_2 site will report paths that cannot happen")
    back = defaultdict(set)
    for src, lst in edges.items():
        for dst, _ in lst:
            back[dst].add(src)

    stops = storage_nodes(edges)

    # The invariant that makes cutting at storage legitimate: with every
    # storage node removed, nothing is left on a cycle.  If something is, it is
    # a ring of combinational gates with no rendezvous in it -- a real
    # combinational loop, and one no matched delay can be sized against.  Say
    # which pins, and stop.
    acyclic = {s: lst for s, lst in edges.items() if s not in stops}
    left = {p for p in state_nodes(acyclic) if is_output(p)}
    if left:
        print(f"storage      ABORT: {len(left)} pin(s) lie on a cycle that "
              f"contains no latch or C-element.  That is a combinational loop "
              f"with no storage in it, not a handshake, and no delay length "
              f"makes it safe:")
        for p in sorted(left)[:10]:
            print(f"               {p}")
        return 2
    timing = Timing(edges, stops)
    chains = find_chains(edges)

    # Which nextpnr measured this.  Every margin below is a routed arrival time
    # from one placer's answer, so a margin quoted without its build is not a
    # fact about the design -- it is a fact about a build that may since have
    # been replaced.  flow.sh writes the stamp beside the SDF.
    stamp = SDF.parent / "toolchain.txt"
    if stamp.exists():
        nx = next((l.strip() for l in stamp.read_text().splitlines()
                   if "nextpnr" in l), "")
        print(f"toolchain    {nx or 'stamp present but no nextpnr line'}")
    else:
        print(f"toolchain    UNSTAMPED -- no {stamp.name} beside the SDF, so "
              f"the margins below cannot be attributed to a nextpnr build")

    print(f"routed SDF   {n_io} cell arcs, {n_ic} routed nets")
    print(f"state nodes  {len(stops)} LUT feedback loops -- start and stop points")
    print(f"delay lines  {len(chains)}")

    problems = 0
    sized = {}          # instance path -> recommended link count

    # ---------------------------------------------------- A: the request rule
    print()
    print("A. the request is the last thing its cell emits")
    print("-" * 78)
    hop = median_hop(edges)
    sites = request_sites(edges, back, chains)

    def req_guard(p, t):
        """The review's guardband: a fifth of the data path, floored at 200 ps."""
        return max(int(0.2 * t), 200)

    audited = set()
    for parent, head, tail, links in sites:
        audited.add(parent)
        n = len(links)
        label = parent

        # Every other output the parent cell produces -- minus the ones that
        # are not peers at all: anything upstream of the chain (the OR that
        # feeds it is not a datapath the chain must cover) and anything
        # downstream of it (a second line hanging off this one is not a race
        # against it either).
        downstream = reaches(edges, tail, stops)
        upstream   = {p for p in edges
                      if is_output(p) and head in reaches(edges, p, stops)}
        # The line's own links are not peers of their own output.
        own = set(links)
        peers = sorted({p for p in edges
                        if is_output(p)
                        and pin_split(p)[0].startswith(parent + ".")
                        and pin_split(p)[0] not in own
                        and p not in downstream
                        and p not in upstream})
        if not peers:
            print(f"  {label:<22} {n:>2} links   nothing inside {parent} for "
                  f"this request to wait for")
            continue

        srcs = cell_boundary(edges, back, stops, parent)
        res = check(timing, srcs, peers, tail, req_guard, confine=parent)
        # A cell whose request and data arrive on different nets -- every
        # generated compute unit -- has no common start point, and used to be
        # skipped here with a message.  Skipping is the one outcome this pass
        # must not have: a delay that was never audited reads exactly like a
        # delay that passed.  Fall back to pairing the channel's two halves.
        pairing = "common source"
        if res is None:
            res = check_bundled(timing, srcs, peers, tail, req_guard,
                                confine=parent)
            pairing = "bundled channel"
        if res is None:
            print(f"  {label:<22} {n:>2} links   nothing outside {parent} "
                  f"reaches its request -- not audited")
            continue

        margin, guard, t_e, t_l, pin, s = res[:6]
        late_src = res[6] if len(res) > 6 else s
        # what the chain itself contributes, on the path being measured
        chain_ps = None
        e_tab = timing.early(s, parent)
        if head in e_tab and tail in e_tab:
            chain_ps = e_tab[tail] - e_tab[head]
        # One link's cost.  Measured from the chain when there is one; the
        # median routed hop when there is not, because a zero-length line has
        # nothing to measure and still has to be sized.
        per = (chain_ps / n) if (chain_ps and n) else hop
        want = max(0, n - int(margin // per)) if margin >= 0 \
               else n + math.ceil(-margin / per)

        if want > n:
            verdict = f"PAD to {want} -- VIOLATION"
            problems += 1
        elif want == 0:
            verdict = "0 links -- the request already trails without help"
        elif want < n:
            verdict = f"tighten to {want}"
        else:
            verdict = "already exact"
        sized[parent] = want
        shown = f"{chain_ps} ps" if chain_ps is not None else "-"
        print(f"  {label:<22} {n:>2} links {shown:>9}   "
              f"req {t_e:>5}  peak {t_l:>5}  guard {guard:>4}  "
              f"margin {margin:>6}   {verdict}")
        print(f"  {'':<22} latest peer: {pin_split(pin)[0]}")
        # Never let the pairing be invisible.  The two rules answer the same
        # question with different amounts of evidence, and which one produced a
        # number changes how much it is worth.
        if pairing == "common source":
            print(f"  {'':<22} paired by common source: {s}")
        else:
            print(f"  {'':<22} paired as one bundled channel (no common "
                  f"source):")
            print(f"  {'':<22}   request from {s}")
            print(f"  {'':<22}   data    from {late_src}")

    for base in sorted(chains):
        parent = base.rpartition(".")[0]
        if parent in audited:
            continue
        print(f"  {base:<22} {len(chains[base]):>2} links   not an outgoing "
              f"request -- see rule B or C")

    # ------------------------------------------------ B and C: the RAM boundary
    rams = [i for i, t in celltype.items() if t and "RAMB" in t]
    print()
    print("B. the RAM boundary, against the vendor's own setup windows")
    print("-" * 78)
    if not rams:
        print("  no RAM in this design")
    for ram in rams:
        clk = f"{ram}/CLKARDCLK"
        payload = sorted({p for p in back
                          if pin_split(p)[0] == ram
                          and any(pin_split(p)[1].startswith(k) for k in T_SU)})
        if clk not in back:
            print(f"  {ram}: clock pin not driven?")
            continue
        srcs = starts_reaching(back, clk, stops)

        def guard_of(p, t):
            port = pin_split(p)[1]
            for k, v in T_SU.items():
                if port.startswith(k):
                    return v
            return 200

        res = check(timing, srcs, payload, clk, guard_of)
        if res is None:
            print(f"  {ram}: no common source between the clock and the payload")
            print("        -- in this soak design the payload comes from outside")
            print("           the cell, so the setup window is the caller's to")
            print("           meet; tb_mem enforces it in simulation instead.")
        else:
            margin, guard, t_e, t_l, pin, s = res
            state = "ok" if margin >= 0 else "VIOLATION"
            if margin < 0:
                problems += 1
            print(f"  {ram}: clk {t_e} ps, latest payload {pin_split(pin)[1]} "
                  f"{t_l} ps, t_su {guard} -> margin {margin} ps  {state}")
            # Both arrivals are measured from this pin.  Print it: a setup
            # check is meaningless without saying what it is relative to, and
            # when the number moves it is usually the source that moved.
            print(f"  {'':<{len(ram)}}  both measured from {s}")
            # size the setup line that drives this clock
            setup = next((b for b in chains
                          if b.endswith("usetup")
                          and ram.startswith(b.rpartition(".")[0] + ".")), None)
            if setup:
                nn = len(chains[setup])
                h, t = chain_endpoints(edges, back, chains[setup])
                per = None
                for st in srcs:
                    e = timing.early(st)
                    if h in e and t in e and nn:
                        per = (e[t] - e[h]) / nn
                        break
                per = per or hop
                want = max(0, nn - int(margin // per)) if margin >= 0 \
                       else nn + math.ceil(-margin / per)
                sized[setup] = want
                print(f"  {'':<{len(ram)}}  sized for this route: {want} links "
                      f"(one link is {per:.0f} ps here)")

    print()
    print("C. clock-to-out: the acknowledge must trail the read data")
    print("-" * 78)
    co = [b for b in chains if b.endswith("uco")]
    if not co:
        print("  no clock-to-out line in this design")
    for base in co:
        links = chains[base]
        head, tail = chain_endpoints(edges, back, links)
        ram = rams[0] if rams else None
        if not ram or head is None:
            print(f"  {base}: cannot pair with a RAM")
            continue
        srcs = starts_reaching(back, head, stops)
        best = None
        for s in srcs:
            e = timing.early(s)
            if tail in e and f"{ram}/CLKARDCLK" in e:
                d = e[tail] - e[f"{ram}/CLKARDCLK"]
                if best is None or d < best:
                    best = d
        if best is None:
            print(f"  {base}: no path from the RAM clock to the acknowledge")
            continue
        margin = best - T_CO
        per = best / len(links)
        want = len(links) + math.ceil(-margin / per) if margin < 0 \
               else max(1, len(links) - int(margin // per))
        state = "ok" if margin >= 0 else "VIOLATION"
        if margin < 0:
            problems += 1
        sized[base] = want
        print(f"  {base}: {len(links)} links, ack trails the clock edge by "
              f"{best} ps, t_co {T_CO} -> margin {margin} ps  {state}")
        print(f"  {'':<{len(base)}}  sized for this route: {want} links")

    if EMIT is not None:
        lines = ["// GENERATED by verify/tighten.py -- do not edit, and do not",
                 "// check in as if it were a design constant.  These lengths",
                 "// belong to ONE route.  Anything that moves invalidates them,",
                 f"// including applying them.  Source: {SDF}",
                 ""]
        for k in sorted(sized):
            lines.append(f"`define {macro(k)} {sized[k]}")
        EMIT.parent.mkdir(parents=True, exist_ok=True)
        EMIT.write_text("\n".join(lines) + "\n")
        print()
        print(f"wrote {len(sized)} size(s) to {EMIT}")

    print()
    if problems:
        print(f"{problems} boundary/boundaries do not meet their constraint as "
              f"routed.")
        print("That is not a sizing result.  Re-place, or shorten the datapath;")
        print("padding a delay line is the last resort, never the first.")
        return 1
    print("Every boundary meets its constraint on this route.  The lengths "
          "above are what")
    print("the placeholders should become FOR THIS ROUTE and for no other -- "
          "they are")
    print("measurements, not design constants, and they expire the next time "
          "anything moves.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
