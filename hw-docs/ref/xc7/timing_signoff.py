#!/usr/bin/env python3
"""Bundled-data timing signoff over the routed iCE40 netlist.

Verifies, for every data-consuming element of a compiled hlsc design, that
the routed request path is slower than every routed datapath it covers:

    min routed request arrival  >=  max routed data arrival  +  guardband

both measured from the same fork event (the point where the emitted
structure splits a producer's request from the data it announces).

Guardband policy (--policy, QUESTIONS.md Q9):
  ratio (default, the signoff gate): per comparison the required slack is
      need = max(0.2 x data_arrival, 200 ps)
    i.e. req >= max(1.2 x data, data + 200 ps) -- the conjunction, per the
    user's Q9 answer.  Rationale: the SDF is a single corner; the ratio
    covers proportional PVT/model mismatch between the two racing paths,
    the 200 ps floor covers additive skew on short paths.
  zero: plain slack >= --min-slack-ps (default 0) -- the pre-Q9 gate,
    kept for debugging/bisection.
Same-chain difference checks (F14 pulse width, statevar Tg gap) get the
flat floor only (Policy.need_gap): both racing events are taps on one
delay chain, so proportional PVT scaling cannot flip their difference's
sign -- only local additive mismatch between the divergent hops is a
risk, and the floor covers it.  Applying the ratio to the full arrival
there would gate on the shared prefix, which cancels exactly.
Merge-boundary rows are stitched, not gated (F6/F7), but under the ratio
policy the carried deficit is computed from the policy-INFLATED sender
data arrival, max(0, max(1.2 x da, da + 200) - rq): a deficit is a
*difference* of two paths, so inflating only the downstream comparison
would cover 20% of the (small) deficit instead of 20% of the (large)
sender data path.  The seeded deficit is then inflated again by the
downstream rows' own guardband -- double-covered, strictly pessimistic,
hence sound.

Timing-data source (pluggable, see load_sdf): the SDF file written by stock
`nextpnr-ice40 --sdf`.  It contains, for the routed design, every cell's
IOPATH (pin-to-pin) delays and every routed connection's INTERCONNECT
delay, keyed by the yosys netlist names -- which retain the full
hierarchical instance paths of the compiler's emitted structure.  When the
user's patched nextpnr (QUESTIONS.md Q7) lands, a second loader producing
the same PinGraph is all that is needed.

Model (matches the compiler's charge model, DECISIONS.md D12/F7):

* knob owner `hlatch E` (fork = the driver pin of E.r_i):
    request:  fork -> E.handshake mullerc -> E.req_after_data chain (T LUTs)
              -> fanout, flowing through datapath cells (en-gates, merge
              request ORs, demux ctl gates) and request-forwarding library
              C-elements (demux r0/r1, combine, split) with MIN-join,
              stopping at any other knob's cells / merge sel / IO.
    data:     fork -> E's en-gate -> E's data-latch bits (en pin -> out)
              -> downstream comb (MAX-join through datapath cells),
              stopping at library cells, merge data-mux inputs, IO.
* knob owner `merge_delay E` (one check per merge input request; fork =
  that request's driver pin):
    request:  fork -> merge request OR -> E's delay chain -> as above.
    data:     fork -> merge sel C-element -> the merge's data-mux
              cells -> downstream comb, as above.

Comparisons: per cell that received both request- and data-labelled
arrivals in the same check, restricted to the places where request and
data physically race: transparent-latch bits (req at en pin vs data at
data pin) and combinational cells with mixed inputs (demux ctl gates:
rctl vs dctl).  Library C-elements are exempt: a Muller C output fires on
its *last* input, so input skew there is not a bundling hazard provided
each input is glitch-free -- which the driving-gate comparison verifies.

Merge boundaries (the F7 sender obligation) are stitched exactly rather
than gated: each sender check reports how much later than the merge fork
event its data settles at the merge's mux data inputs (a positive deficit
is a "carry", not a FAIL -- F6: merged data legitimately re-times off the
sel C-element, one LUT after the merged request rises), and the deficit is
seeded into that merge_delay check's data traversal, so the downstream
latch/gate comparisons account for late sender data exactly.

Loop cut strategy: no global timing graph is ever built.  Each check is a
bounded forward traversal that stops at the next knob's cells (every
hlatch's mullerc/latch, every delay chain, every merge's sel/mux).  Every
deliberate combinational loop in these designs (latch/C-element feedback,
token rings, while rings) passes through such a cell, so each traversal
region is a small DAG.  Soundness is inductive over handshake transitions:
each check assumes only "inputs stable when the fork fires" -- established
by the predecessor checks (or the environment contract for top-level
inputs) -- and verifies the same invariant one hop downstream.  Self-
feedback pins of library cells are never traversed (traversals only move
forward from a fork), so latch/C-element state loops cannot recur.

Conservatism: request arrivals take min(rise,fall) delays and MIN-join at
C-elements a request flows through (a C-element actually fires on its
*last* input, so this can only under-estimate the request); data arrivals
take max(rise,fall) and MAX-join.  A PASS is therefore trustworthy within
the tool's delay model; a FAIL may be up to one C-element hop pessimistic
(noted in the report).

stdlib only.  Exit status: 0 all PASS, 1 any FAIL, 2 usage/tracing error.
"""

import argparse
import json
import re
import sys
from collections import defaultdict

INF = float("inf")


class SignoffError(Exception):
    """Tracing/consistency failure -- the analysis cannot be trusted."""


def _is_io_type(t):
    """Top-level boundary cells: 'io' role (rst source discovery, fork
    pad skips, unlatched-input-data filtering).  ice40 names them
    SB_IO/SB_GB*; nextpnr-xilinx uses PAD plus *_INBUF*/*_OUTBUF
    variants (IOB33_INBUF_EN, IOB33_OUTBUF, ...)."""
    return (t in ("SB_IO", "SB_GB", "SB_GB_IO", "PAD")
            or "INBUF" in t or "OUTBUF" in t)


class Policy:
    """Guardband policy (Q9): required slack as a function of the data
    arrival it must beat.  'ratio' is the signoff gate; 'zero' (plain
    slack >= min_slack, default 0) is kept for debugging."""

    RATIO = 0.2
    FLOOR_PS = 200.0

    def __init__(self, name, min_slack=0.0):
        if name not in ("ratio", "zero"):
            raise SignoffError(f"unknown policy {name!r}")
        self.name = name
        self.min_slack = min_slack

    def need(self, data):
        if self.name == "ratio":
            return max(self.RATIO * data, self.FLOOR_PS)
        return self.min_slack

    def need_gap(self):
        """Guardband for same-chain difference checks (the F14 pulse
        width and the statevar snap->commit Tg gap): both racing events
        are taps on ONE delay chain, so under uniform (proportional) PVT
        scaling their difference scales but can never change sign -- the
        ratio term would demand headroom proportional to the shared
        prefix, which contributes zero risk.  What remains is local
        additive mismatch between the few divergent hops; the flat floor
        covers that."""
        if self.name == "ratio":
            return self.FLOOR_PS
        return self.min_slack

    def describe(self):
        if self.name == "ratio":
            return ("slack >= max(%.0f%% x data, %.0f ps) per comparison "
                    "(Q9 guardband)" % (100 * self.RATIO, self.FLOOR_PS))
        return f"slack >= {self.min_slack:.0f} ps (debug policy 'zero')"


# --------------------------------------------------------------------------
# SDF parsing -> PinGraph
# --------------------------------------------------------------------------

class PinGraph:
    """Pin-level delay graph of the routed netlist.

    cells:      name -> celltype
    iopaths:    cell -> {(from_pin, to_pin): (dmin, dmax)}  [ps]
    edges_out:  (cell, pin) -> [(cell2, pin2, dmin, dmax)]   routed nets
    driver_of:  (cell, pin) -> (cell2, pin2, dmin, dmax)
    """

    def __init__(self):
        self.cells = {}
        self.iopaths = defaultdict(dict)
        self.edges_out = defaultdict(list)
        self.driver_of = {}

    def add_interconnect(self, src, dst, dmin, dmax):
        self.edges_out[src].append((dst[0], dst[1], dmin, dmax))
        if dst in self.driver_of:
            raise SignoffError(f"pin {dst} has two drivers")
        self.driver_of[dst] = (src[0], src[1], dmin, dmax)

    def cell_outputs_from(self, cell, from_pin):
        """[(to_pin, dmin, dmax)] IOPATHs of `cell` starting at from_pin."""
        return [(t, d[0], d[1]) for (f, t), d in self.iopaths[cell].items()
                if f == from_pin]


def _sdf_tokens(text):
    # Strip SDF escapes; names contain no whitespace after unescaping.
    text = text.replace("\\", "")
    return re.findall(r"\(|\)|[^\s()]+", text)


def load_graph_json(path):
    """Load a pin-level delay graph dumped by boards/xc7/timing_dump.py
    (run inside nextpnr-xilinx via --post-route; the xc7 substitute for
    ice40's SDF, QUESTIONS.md Q7b).  Delays are single-corner ps, so
    dmin == dmax per arc/edge -- the Q9 ratio guardband is the cover
    for the missing corner split."""
    d = json.load(open(path))
    if d.get("units") != "ps" or "iopaths" not in d:
        raise SignoffError(f"{path}: not a timing_dump.py graph")
    g = PinGraph()
    g.cells.update(d["cells"])
    for cell, fp, tp, ps in d["iopaths"]:
        g.iopaths[cell][(fp, tp)] = (ps, ps)
    for c1, p1, c2, p2, ps in d["edges"]:
        g.add_interconnect((c1, p1), (c2, p2), ps, ps)
    return g


def load_sdf(path):
    """Parse a nextpnr SDF file into a PinGraph."""
    tokens = _sdf_tokens(open(path).read())
    g = PinGraph()
    i = 0
    n = len(tokens)

    def parse_expr(j):
        # returns (list-or-atom, next_index)
        if tokens[j] != "(":
            return tokens[j], j + 1
        j += 1
        items = []
        while tokens[j] != ")":
            e, j = parse_expr(j)
            items.append(e)
        return items, j + 1

    tree, _ = parse_expr(0)
    if tree[0] != "DELAYFILE":
        raise SignoffError(f"{path}: not an SDF DELAYFILE")

    def triple_minmax(vals):
        # vals: "(a:b:c)" groups -> parsed as nested lists of atoms
        nums = []
        def walk(v):
            if isinstance(v, list):
                for x in v:
                    walk(x)
            else:
                nums.extend(float(x) for x in v.split(":") if x != "")
        walk(vals)
        return min(nums), max(nums)

    def split_portpath(p):
        # instance path and pin, divider '/'
        inst, _, pin = p.rpartition("/")
        return inst, pin

    for item in tree[1:]:
        if not isinstance(item, list) or item[0] != "CELL":
            continue
        celltype = instance = None
        delay_sections = []
        for sub in item[1:]:
            if not isinstance(sub, list):
                continue
            if sub[0] == "CELLTYPE":
                celltype = sub[1].strip('"')
            elif sub[0] == "INSTANCE":
                instance = sub[1] if len(sub) > 1 else ""
            elif sub[0] == "DELAY":
                delay_sections.append(sub)
        if instance is None:
            instance = ""
        if instance == "" and celltype in ("top", None):
            # top-level cell: INTERCONNECT entries
            for dly in delay_sections:
                for absl in dly[1:]:
                    if not isinstance(absl, list) or absl[0] != "ABSOLUTE":
                        continue
                    for e in absl[1:]:
                        if not isinstance(e, list) or e[0] != "INTERCONNECT":
                            continue
                        src = split_portpath(e[1])
                        dst = split_portpath(e[2])
                        dmin, dmax = triple_minmax(e[3:])
                        g.add_interconnect(src, dst, dmin, dmax)
            continue
        g.cells[instance] = celltype
        for dly in delay_sections:
            for absl in dly[1:]:
                if not isinstance(absl, list) or absl[0] != "ABSOLUTE":
                    continue
                for e in absl[1:]:
                    if not isinstance(e, list) or e[0] != "IOPATH":
                        continue
                    dmin, dmax = triple_minmax(e[3:])
                    g.iopaths[instance][(e[1], e[2])] = (dmin, dmax)
    # cells referenced only by interconnects (defensive)
    for (c, _p), outs in list(g.edges_out.items()):
        g.cells.setdefault(c, "?")
        for c2, _p2, _a, _b in outs:
            g.cells.setdefault(c2, "?")
    return g


# --------------------------------------------------------------------------
# Netlist role classification (sidecar names -> routed cells)
# --------------------------------------------------------------------------

class Roles:
    """Classification of every routed cell against the timing sidecar."""

    def __init__(self, g, sidecar):
        self.g = g
        self.sidecar = sidecar
        self.role = {}          # cell -> ('hl_mull',E) ('hl_latch',E,i)
                                #         ('chain',E,k) ('merge_sel',inst)
                                #         ('mem_latch',E,tag,bit)
                                #         ('forward',) ('io',) ('dp',)
        self.hl_mull = {}       # E -> cell
        self.hl_latch = {}      # E -> [cells by bit]
        self.chain = {}         # E -> [cells by position]
        # memory elements (M6: ram1rw / statevar), all cells located by
        # hierarchical name exactly like hlatches are:
        self.mem_info = {}      # E -> sidecar "mem" record
        self.mem_segs = {}      # E -> [(segname, [chain cells])] in order
        self.mem_latches = {}   # E -> {tag: [cells by bit]}
        self.mem_gates = {}     # E -> {gate name: cell}  (warm/p1/p2)
        self.mem_en = {}        # E -> [en-gate cells]  (ram1rw)
        self.prefix = self._find_prefix()
        self._classify()

    def _find_prefix(self):
        hls = [e["name"] for e in self.sidecar["elements"]
               if e["kind"] == "hlatch"]
        probe = hls[0]
        suffix = f"{probe}.handshake.main.genblk1.main"
        cands = [c for c in self.g.cells
                 if self._strip(c).endswith(suffix)]
        if len(cands) != 1:
            raise SignoffError(
                f"cannot locate element {probe} in netlist "
                f"(candidates: {cands})")
        full = self._strip(cands[0])
        return full[: len(full) - len(suffix)]

    @staticmethod
    def _strip(cell):
        """Netlist-decoration stripping: nextpnr packing appends _LC /
        $CARRY-suffixes; the yosys library path is what remains."""
        for suf in ("_LC", "_DFFLC"):
            if cell.endswith(suf):
                return cell[: -len(suf)]
        return cell

    def _classify(self):
        g, p = self.g, self.prefix
        by_stripped = {}
        for c in g.cells:
            by_stripped.setdefault(self._strip(c), c)

        def find(name):
            return by_stripped.get(p + name)

        for e in self.sidecar["elements"]:
            E, kind, T = e["name"], e["kind"], e["T"]
            if kind == "hlatch":
                m = find(f"{E}.handshake.main.genblk1.main")
                if m is None:
                    raise SignoffError(f"{E}: handshake mullerc not found")
                self.role[m] = ("hl_mull", E)
                self.hl_mull[E] = m
                bits = []
                while True:
                    c = find(f"{E}.latch.genblk1[{len(bits)}]"
                             ".main.genblk1.main")
                    if c is None:
                        break
                    self.role[c] = ("hl_latch", E, len(bits))
                    bits.append(c)
                if not bits:
                    raise SignoffError(f"{E}: no data-latch bits found")
                self.hl_latch[E] = bits
                chain = []
                for k in range(T):
                    c = find(f"{E}.req_after_data.genblk1[{k}]"
                             ".main.main.genblk1.main")
                    if c is None:
                        raise SignoffError(
                            f"{E}: delay LUT {k}/{T} missing "
                            "(sidecar/netlist mismatch)")
                    self.role[c] = ("chain", E, k)
                    chain.append(c)
                self.chain[E] = chain
            elif kind == "merge_delay":
                chain = []
                for k in range(T):
                    c = find(f"{E}.genblk1[{k}].main.main.genblk1.main")
                    if c is None:
                        raise SignoffError(
                            f"{E}: delay LUT {k}/{T} missing "
                            "(sidecar/netlist mismatch)")
                    self.role[c] = ("chain", E, k)
                    chain.append(c)
                if not chain:
                    raise SignoffError(f"{E}: merge_delay with T=0")
                self.chain[E] = chain
            elif kind in ("ram1rw", "statevar"):
                self._classify_mem(e, find)
            else:
                raise SignoffError(f"unknown sidecar element kind: {kind}")

        # memory-element internals not explicitly classified above (the
        # per-element sweep marks decode/mux/en/pulse-gate LUTs as dp and
        # errors on anything unrecognized under the element's path)

        # remaining library LUTs: merge sel / demux r0,r1 /
        # combine / split C-elements
        unclassified = []
        for c in g.cells:
            if c in self.role:
                continue
            s = self._strip(c)
            if s.endswith(".genblk1.main"):
                if re.search(r"\.sel\.main\.genblk1\.main$", s):
                    inst = s[: s.rindex(".sel.main.genblk1.main")]
                    self.role[c] = ("merge_sel", inst)
                elif re.search(r"\.ror\.genblk1\.main$", s):
                    # merge's request-OR, a lut instance since the xc7
                    # tracing fix (merge.sv `ror`): dp, exactly as the
                    # behavioral OR it replaced was classified -- the
                    # merge analysis finds it as the chain input's
                    # driver and requires kind == "dp".
                    self.role[c] = ("dp",)
                elif re.search(r"\.main\.genblk1\.main$", s):
                    self.role[c] = ("forward",)
                else:
                    unclassified.append(c)
            elif _is_io_type(g.cells[c]):
                self.role[c] = ("io",)
            else:
                self.role[c] = ("dp",)
        if unclassified:
            raise SignoffError(
                f"unclassified library-looking cells: {unclassified[:5]}")
        for c, t in g.cells.items():
            if _is_io_type(t):
                self.role[c] = ("io",)

    def _classify_mem(self, e, find):
        """ram1rw / statevar (M6): locate every internal cell by
        hierarchical name -- the delay chains (classified 'chain' so
        other traversals stop at the element boundary, exactly like any
        knob's chain), the storage dlatches ('mem_latch', a stop for
        both traversals; seeded explicitly by the element's own check),
        the pulse gates and decode/mux/enable LUTs ('dp', so data flows
        through them), erroring on anything unrecognized under the
        element's path (a tracing hole would silently misclassify)."""
        E, kind, mem = e["name"], e["kind"], e["mem"]
        self.mem_info[E] = dict(mem, kind=kind, Tr=e["T"])
        if kind == "ram1rw":
            segs = [("dly_decode", mem["Td"]), ("dly_pulse", mem["Tp"]),
                    ("dly_req", e["T"])]
        else:
            segs = [("dly_s", mem["Ts"]), ("dly_p1", mem["Tp"]),
                    ("dly_g", mem["Tg"]), ("dly_p2", mem["Tp"]),
                    ("dly_r", e["T"])]
        chain = []
        seg_cells = []
        for seg, T in segs:
            cells = []
            for k in range(T):
                c = find(f"{E}.{seg}.genblk1[{k}].main.main.genblk1.main")
                if c is None:
                    raise SignoffError(
                        f"{E}: {seg} delay LUT {k}/{T} missing "
                        "(sidecar/netlist mismatch)")
                self.role[c] = ("chain", E, len(chain))
                chain.append(c)
                cells.append(c)
            seg_cells.append((seg, cells))
        self.chain[E] = chain
        self.mem_segs[E] = seg_cells

        latches = {}

        def latch_bits(tag, path, W):
            bits = []
            for b in range(W):
                c = find(f"{E}.{path}.genblk1[{b}].main.genblk1.main")
                if c is None:
                    raise SignoffError(
                        f"{E}: {path} latch bit {b}/{W} missing")
                self.role[c] = ("mem_latch", E, tag, b)
                bits.append(c)
            latches[tag] = bits

        gates = {}

        def gate(name):
            c = find(f"{E}.{name}.genblk1.main")
            if c is None:
                raise SignoffError(f"{E}: {name} missing")
            self.role[c] = ("dp",)
            gates[name] = c
            return c

        def dp(path):
            c = find(f"{E}.{path}.genblk1.main")
            if c is not None:
                self.role[c] = ("dp",)
            return c

        en_cells = []
        if kind == "ram1rw":
            W, A, depth = mem["W"], mem["A"], mem["depth_words"]
            gate("warm_gate")
            for w in range(depth):
                latch_bits(f"w{w}", f"g_word[{w}].store", W)
                ec = dp(f"g_word[{w}].en_gate")
                if ec is None:
                    raise SignoffError(f"{E}: g_word[{w}].en_gate missing")
                en_cells.append(ec)
                if A <= 4:
                    if dp(f"g_word[{w}].g_dec1.dec_lo") is None:
                        raise SignoffError(f"{E}: word {w} decode missing")
                else:
                    for n in ("dec_lo", "dec_hi", "dec_and"):
                        if dp(f"g_word[{w}].g_dec2.{n}") is None:
                            raise SignoffError(
                                f"{E}: word {w} decode {n} missing")
            for lvl in range(A):
                for i in range(depth >> (lvl + 1)):
                    for b in range(W):
                        if dp(f"g_lvl[{lvl}].g_node[{i}].g_bit[{b}].m") \
                                is None:
                            raise SignoffError(
                                f"{E}: mux LUT lvl{lvl}/{i}/{b} missing")
        else:
            W = mem["W"]
            gate("p1_gate")
            gate("p2_gate")
            latch_bits("master", "master", W)
            latch_bits("snap", "snap", W)
        self.mem_latches[E] = latches
        self.mem_gates[E] = gates
        self.mem_en[E] = en_cells
        # completeness: every LIBRARY lut under the element's path (the
        # ".genblk1.main" leaves) must have been classified above -- an
        # unaccounted one would be a tracing hole.  Cells with other
        # names under the path are yosys datapath LUTs whose output net
        # was aliased into the element's hierarchy at flatten time (the
        # port merge's data mux, nextpnr route-throughs): honest 'dp'.
        p = self.prefix + E + "."
        stray = []
        for c in self.g.cells:
            if not self._strip(c).startswith(p) or c in self.role:
                continue
            if self._strip(c).endswith(".genblk1.main"):
                stray.append(c)
            else:
                self.role[c] = ("dp",)
        if stray:
            raise SignoffError(
                f"{E}: unclassified internal library cells (tracing "
                f"hole): {stray[:5]}")

    def kind(self, cell):
        return self.role.get(cell, ("dp",))[0]


# --------------------------------------------------------------------------
# Structure discovery on top of roles
# --------------------------------------------------------------------------

class Structure:
    """Per-element pin structure: forks, en-gates, merge OR/sel/mux."""

    def __init__(self, g, roles):
        self.g = g
        self.roles = roles
        self.rst_src = self._find_rst_src()
        self.hl = {}       # E -> dict(fork, mull_pin, en_cells, latch data
                           #           pins, chain_out)
        self.merges = {}   # mdly E -> dict(or_cell, sel_cell, mux_cells,
                           #               forks, chain_out)
        self.mems = {}     # mem E -> dict(fork, r_pin, chain_out)
        for e in roles.sidecar["elements"]:
            if e["kind"] == "hlatch":
                self._analyze_hlatch(e["name"])
        for e in roles.sidecar["elements"]:
            if e["kind"] == "merge_delay":
                self._analyze_merge(e["name"])
        for e in roles.sidecar["elements"]:
            if e["kind"] in ("ram1rw", "statevar"):
                self._analyze_mem(e["name"])

    # -- helpers ----------------------------------------------------------
    def _find_rst_src(self):
        """rst is the one source driving a pin of every hlatch mullerc."""
        counts = defaultdict(int)
        mulls = list(self.roles.hl_mull.values())
        for m in mulls:
            for (c, p), drv in self.g.driver_of.items():
                if c == m:
                    counts[(drv[0], drv[1])] += 1
        for src, n in counts.items():
            if n == len(mulls) and self.roles.kind(src[0]) == "io":
                return src
        # fall back: highest-fanout io source
        best, bestn = None, -1
        for src, n in counts.items():
            if self.roles.kind(src[0]) == "io" and n > bestn:
                best, bestn = src, n
        if best is None:
            raise SignoffError("cannot identify the rst distribution net")
        return best

    def _in_pins(self, cell):
        return [(c, p) for (c, p) in self.g.driver_of if c == cell]

    def _is_rst(self, pin):
        d = self.g.driver_of.get(pin)
        return d is not None and (d[0], d[1]) == self.rst_src

    def _is_self(self, pin):
        d = self.g.driver_of.get(pin)
        return d is not None and d[0] == pin[0]

    # -- hlatch -----------------------------------------------------------
    def _analyze_hlatch(self, E):
        g, roles = self.g, self.roles
        m = roles.hl_mull[E]
        cand = [pin for pin in self._in_pins(m)
                if not self._is_rst(pin) and not self._is_self(pin)]
        if len(cand) != 2:
            raise SignoffError(f"{E}: mullerc has {len(cand)} candidate "
                               f"r_i/a_o pins, expected 2: {cand}")
        # r_i is driven by a delay chain LUT or a request-forwarding
        # C-element; the ack is driven by another hlatch's mullerc or a
        # datapath ack-OR (or, for L_out, the split C-element -- resolved
        # because its r_i side is then chain-driven).
        def drv_kind(pin):
            d = g.driver_of[pin]
            return roles.kind(d[0])
        chain_side = [p for p in cand if drv_kind(p) == "chain"]
        fwd_side = [p for p in cand if drv_kind(p) == "forward"]
        io_side = [p for p in cand if drv_kind(p) == "io"]
        if len(chain_side) == 1:
            r_pin = chain_side[0]
        elif len(fwd_side) == 1:
            r_pin = fwd_side[0]
        elif len(io_side) == 1:
            # M7 (Q16, admission-lock removal): L_in's r_i is now driven
            # directly by the module's own r_i port (no `combine` in
            # between) -- the one hlatch in the design whose REQUEST
            # side can be io-driven. L_out's a_o is also now io-driven
            # directly by the module's a_o port, but L_out's r_i is
            # still chain-driven by the upstream stage, so it already
            # resolves via the chain_side branch above without ever
            # reaching here; this branch only ever fires for L_in.
            r_pin = io_side[0]
        elif len(fwd_side) == 2:
            # both candidates driven by library C-elements (e.g. a demux
            # steer output feeding r_i while the ack comes from a split).
            # The request-side C-element (demux r0/r1, combine) always has
            # a delay-chain-driven input (the producer's request); ack-side
            # C-elements (split) join only acks, which are never
            # chain-driven.
            def has_chain_input(pin):
                drv_cell = g.driver_of[pin][0]
                return any(roles.kind(g.driver_of[q][0]) == "chain"
                           for q in self._in_pins(drv_cell))
            req_like = [p for p in fwd_side if has_chain_input(p)]
            if len(req_like) != 1:
                raise SignoffError(
                    f"{E}: forward/forward r_i ambiguity not resolvable "
                    f"({cand})")
            r_pin = req_like[0]
        else:
            raise SignoffError(
                f"{E}: cannot identify r_i pin among {cand} "
                f"(driver kinds {[drv_kind(p) for p in cand]})")
        drv = g.driver_of[r_pin]
        fork = (drv[0], drv[1])
        # en-gate cells = sinks of the fork net that drive one of this
        # element's own latch-bit cells. M7 (QUESTIONS.md Q16): a
        # ctl-recycle fork (`split`, mux2 entry's Lcf, tb_muxwhile) puts
        # this net on the SAME physical wire as a sibling branch's own
        # control plumbing (e.g. a demux2 steer's mullerc) -- split's
        # request side is a bare wire (only the ack side joins), so
        # there is no gate to stop it. abc9/yosys is then free to
        # restructure that SIBLING logic (it now shares an input net
        # with this fork), which can rename or reshape it past any
        # role-based classification (observed: a generic $abc$...
        # cell where a demux2's mullerc used to be). Rather than chase
        # every possible resulting name/shape, filter by WHAT THE SINK
        # ACTUALLY DRIVES: a genuine en-gate for this element drives
        # one of its own latch bits; anything else on the net is
        # harmless split-fork spillover, whatever it ended up called.
        latch_set = set(roles.hl_latch[E])
        en_cells = set()
        for (c2, p2, _dn, _dx) in g.edges_out[fork]:
            if c2 == m or c2 == fork[0]:  # mullerc / driver self-feedback
                continue
            if roles.kind(c2) == "io":
                continue  # top-level port pad on the same net (e.g. r_o)
            if any(c3 in latch_set
                   for (c3, _p3, _a, _b) in g.edges_out[(c2, "O")]):
                en_cells.add(c2)
        if not en_cells:
            raise SignoffError(f"{E}: no en-gate found on the r_i net")
        # latch data pins: driven, not rst, not self, not en(-gate driven)
        data_pins = []
        for c in roles.hl_latch[E]:
            for pin in self._in_pins(c):
                if self._is_rst(pin) or self._is_self(pin):
                    continue
                d = g.driver_of[pin]
                if d[0] in en_cells:
                    continue
                data_pins.append(pin)
        chain = roles.chain.get(E, [])
        chain_out = (chain[-1], "O") if chain else (m, "O")
        self.hl[E] = dict(mull=m, r_pin=r_pin, fork=fork,
                          en_cells=en_cells, data_pins=data_pins,
                          chain_out=chain_out)

    # -- merge_delay ------------------------------------------------------
    def _analyze_merge(self, E):
        g, roles = self.g, self.roles
        chain = roles.chain[E]
        first = chain[0]
        sig = [pin for pin in self._in_pins(first)
               if not self._is_rst(pin) and not self._is_self(pin)]
        if len(sig) != 1:
            raise SignoffError(f"{E}: chain input pins {sig}")
        or_drv = g.driver_of[sig[0]]
        or_cell = or_drv[0]
        if roles.kind(or_cell) != "dp":
            raise SignoffError(
                f"{E}: chain input driven by {or_cell} "
                f"({roles.kind(or_cell)}), expected the request-OR")
        forks = []
        for pin in self._in_pins(or_cell):
            if self._is_rst(pin):
                continue
            d = g.driver_of[pin]
            forks.append((d[0], d[1]))
        if len(forks) != 2:
            raise SignoffError(f"{E}: request OR has {len(forks)} inputs")
        # sel C-element: merge_sel cell fed directly from the fork nets
        sels = set()
        for f in forks:
            for (c2, _p2, _a, _b) in g.edges_out[f]:
                if roles.kind(c2) == "merge_sel":
                    sels.add(c2)
        if len(sels) != 1:
            raise SignoffError(f"{E}: found {len(sels)} sel C-elements "
                               f"({sels}) from forks {forks}")
        sel_cell = sels.pop()
        mux_cells = set(c2 for (c2, _p2, _a, _b)
                        in g.edges_out[(sel_cell, "O")]
                        if c2 != sel_cell)  # skip its own state feedback
        for c in mux_cells:
            if roles.kind(c) != "dp":
                raise SignoffError(
                    f"{E}: sel output drives non-datapath cell {c}")
        self.merges[E] = dict(or_cell=or_cell, sel_cell=sel_cell,
                              mux_cells=mux_cells, forks=forks,
                              chain_out=(chain[-1], "O"))

    # -- ram1rw / statevar -------------------------------------------------
    def _analyze_mem(self, E):
        """The element is a pure delay-line stage: its fork is the driver
        of r_i (= the first chain LUT's signal input)."""
        g = self.g
        chain = self.roles.chain[E]
        first = chain[0]
        sig = [pin for pin in self._in_pins(first)
               if not self._is_rst(pin) and not self._is_self(pin)]
        if len(sig) != 1:
            raise SignoffError(f"{E}: chain input pins {sig}")
        d = g.driver_of[sig[0]]
        self.mems[E] = dict(fork=(d[0], d[1]), r_pin=sig[0],
                            chain_out=(chain[-1], "O"))

    def all_mux_cells(self):
        s = set()
        for m in self.merges.values():
            s |= m["mux_cells"]
        return s


# --------------------------------------------------------------------------
# Per-check traversals
# --------------------------------------------------------------------------

MAX_POPS = 200000


class Check:
    """One (knob element, fork) analysis."""

    def __init__(self, name, st, fork, own_merge=None):
        self.name = name          # e.g. "st1_L" or "if1_mdly[in1]"
        self.st = st
        self.fork = fork
        self.own_merge = own_merge  # merge_delay element name, if any
        self.req = {}             # (cell,pin) -> min ps from fork
        self.req_out = {}         # (cell,outpin) -> min ps from fork
        self.data = {}            # (cell,pin) -> max ps from fork

    # request side: min-propagation ---------------------------------------
    def prop_req_from(self, node, t0, own_chain_cells):
        g, roles = self.st.g, self.st.roles
        heap = [(t0, node)]
        self.req_out[node] = min(self.req_out.get(node, INF), t0)
        best_out = {node: t0}
        pops = 0
        while heap:
            heap.sort()
            t, out = heap.pop(0)
            pops += 1
            if pops > MAX_POPS:
                raise SignoffError(f"{self.name}: request traversal "
                                   "did not terminate (cycle?)")
            if t > best_out.get(out, INF):
                continue
            for (c2, p2, dmin, _dmax) in g.edges_out[out]:
                t2 = t + dmin
                pin = (c2, p2)
                if t2 >= self.req.get(pin, INF):
                    continue
                self.req[pin] = t2
                k = roles.kind(c2)
                if c2 in own_chain_cells:
                    continue  # own chain handled explicitly
                if k in ("dp", "forward"):
                    for (op, dn, _dx) in g.cell_outputs_from(c2, p2):
                        t3 = t2 + dn
                        if t3 < best_out.get((c2, op), INF):
                            best_out[(c2, op)] = t3
                            self.req_out[(c2, op)] = t3
                            heap.append((t3, (c2, op)))
                # everything else (hl_mull, hl_latch, chain of another
                # knob, merge_sel, io): stop -- next knob's territory.

    # data side: max-propagation -------------------------------------------
    def prop_data_from(self, node, t0, own_mux_cells=frozenset()):
        g, roles = self.st.g, self.st.roles
        mux_cells = self.st.all_mux_cells()
        heap = [(t0, node)]
        best_out = {node: t0}
        pops = 0
        while heap:
            heap.sort(reverse=True)
            t, out = heap.pop(0)
            pops += 1
            if pops > MAX_POPS:
                raise SignoffError(f"{self.name}: data traversal "
                                   "did not terminate (comb cycle?)")
            if t < best_out.get(out, -INF):
                continue
            for (c2, p2, _dmin, dmax) in g.edges_out[out]:
                t2 = t + dmax
                pin = (c2, p2)
                if t2 <= self.data.get(pin, -INF):
                    continue
                self.data[pin] = t2
                k = roles.kind(c2)
                stop = (k != "dp") or \
                       (c2 in mux_cells and c2 not in own_mux_cells)
                if stop:
                    continue
                for (op, _dn, dx) in g.cell_outputs_from(c2, p2):
                    t3 = t2 + dx
                    if t3 > best_out.get((c2, op), -INF):
                        best_out[(c2, op)] = t3
                        heap.append((t3, (c2, op)))


def edge_delay(g, src, dst):
    for (c2, p2, dmin, dmax) in g.edges_out[src]:
        if (c2, p2) == dst:
            return dmin, dmax
    raise SignoffError(f"no edge {src} -> {dst}")


def seed_held_bypass(chk, st, own=None):
    """Held-bypass seeding (M6).  Memory-site continuations (and
    degenerate merges whose muxes yosys deleted because both inputs are
    the same nets) hand a request to a consumer latch whose data pins
    are *bypass nets held by an earlier latch*: that holder captured at
    least one full handshake -- for memory sites, the whole port
    traversal (merge + element chain + demux + three latches) -- before
    this check's fork event, and cannot recapture until the transaction
    completes (single-token invariant).  The producing knob's own launch
    never touches those pins, so without this pass they have a request
    and no data: a coverage hole, not a race.

    For every consumer latch that received a request in this check,
    each data pin the data propagation did not reach is walked backward
    through combinational cells to its holder outputs (hlatch bits,
    memory storage bits, merge mux gates), and each holder is
    re-launched at t=0 -- the fork event.  Real settle completed the
    full forward comb *before* the fork, so modelling launch AT the
    fork over-states every downstream arrival by at least one handshake
    traversal: strictly pessimistic, hence sound (same convention as
    the memory-element check's external-input seeds)."""
    g, roles = st.g, st.roles
    mux = st.all_mux_cells()
    consumers = set()
    for (c, _p) in chk.req:
        r = roles.role.get(c, ("dp",))
        if r[0] in ("hl_latch", "hl_mull") and r[1] != own:
            consumers.add(r[1])
    seeds = set()
    for C in sorted(consumers):
        info = st.hl.get(C)
        if info is None:
            continue
        for pin in info["data_pins"]:
            if pin in chk.data:
                continue
            stack, seen = [pin], set()
            while stack:
                q = stack.pop()
                d = g.driver_of.get(q)
                if d is None:
                    continue
                node = (d[0], d[1])
                if node in seen:
                    continue
                seen.add(node)
                k = roles.kind(d[0])
                if k in ("hl_latch", "mem_latch") or d[0] in mux:
                    seeds.add(node)      # a holder: launch point
                elif k in ("dp", "forward"):
                    for q2 in st._in_pins(d[0]):
                        if not st._is_rst(q2) and not st._is_self(q2):
                            stack.append(q2)
                # else (chain / mullerc / merge_sel / io): handshake or
                # primary input -- not held bundled data; skip.
    for node in sorted(seeds):
        chk.prop_data_from(node, 0.0)


def run_hlatch_check(st, E):
    g, roles = st.g, st.roles
    info = st.hl[E]
    chk = Check(E, st, info["fork"])
    chain_cells = set(roles.chain.get(E, [])) | {info["mull"]}

    # request: fork -> mullerc r_i -> IOPATH -> chain -> generic
    dmin, dmax = edge_delay(g, info["fork"], info["r_pin"])
    chk.req[info["r_pin"]] = dmin
    outs = g.cell_outputs_from(info["mull"], info["r_pin"][1])
    if len(outs) != 1:
        raise SignoffError(f"{E}: mullerc IOPATH from r_i: {outs}")
    t = dmin + outs[0][1]
    cur = (info["mull"], "O")
    chk.req_out[cur] = t
    for c in roles.chain.get(E, []):
        pins = [pin for pin in st._in_pins(c)
                if g.driver_of[pin][0] == cur[0]]
        if len(pins) != 1:
            raise SignoffError(f"{E}: chain link into {c} ambiguous")
        dn, _dx = edge_delay(g, cur, pins[0])
        t += dn
        chk.req[pins[0]] = t
        io = g.cell_outputs_from(c, pins[0][1])
        if len(io) != 1:
            raise SignoffError(f"{E}: delay LUT {c} IOPATH: {io}")
        t += io[0][1]
        cur = (c, "O")
        chk.req_out[cur] = t
    chk.prop_req_from(cur, t, chain_cells)

    # data: fork -> en-gate(s) -> latch bits (en pin -> O) -> generic
    for ec in info["en_cells"]:
        pins = [pin for pin in st._in_pins(ec)
                if (g.driver_of[pin][0], g.driver_of[pin][1]) == info["fork"]]
        for pin in pins:
            _dn, dx = edge_delay(g, info["fork"], pin)
            chk.data[pin] = max(chk.data.get(pin, -INF), dx)
            for (op, _a, dxx) in g.cell_outputs_from(ec, pin[1]):
                ten = chk.data[pin] + dxx
                # en net -> each latch bit
                for (c2, p2, _dn2, dx2) in g.edges_out[(ec, op)]:
                    t2 = ten + dx2
                    pin2 = (c2, p2)
                    if roles.kind(c2) == "hl_latch" and \
                            roles.role[c2][1] == E:
                        if t2 <= chk.data.get(pin2, -INF):
                            continue
                        chk.data[pin2] = t2
                        for (op2, _a2, dx3) in g.cell_outputs_from(c2, p2):
                            chk.prop_data_from((c2, op2), t2 + dx3)
                    else:
                        # en-gate fanout outside the latch (none expected,
                        # but record for the comparison pass)
                        chk.data[pin2] = max(chk.data.get(pin2, -INF), t2)
    seed_held_bypass(chk, st, own=E)
    return chk


def run_merge_checks(st, E, deficits):
    """deficits: {(merge_E, fork_node): ps} -- how much later than the
    fork event the sender's data settles at this merge's mux data pins
    (computed by the sender checks, stitched in here)."""
    g, roles = st.g, st.roles
    m = st.merges[E]
    checks = []
    for idx, fork in enumerate(m["forks"]):
        chk = Check(f"{E}[in{idx}]", st, fork, own_merge=E)
        chain_cells = set(roles.chain[E]) | {m["or_cell"]}
        # request: fork -> OR -> chain -> generic
        orpins = [pin for pin in st._in_pins(m["or_cell"])
                  if (g.driver_of[pin][0], g.driver_of[pin][1]) == fork]
        if len(orpins) != 1:
            raise SignoffError(f"{E}: fork {fork} -> OR pins {orpins}")
        dn, _dx = edge_delay(g, fork, orpins[0])
        chk.req[orpins[0]] = dn
        io = g.cell_outputs_from(m["or_cell"], orpins[0][1])
        if len(io) != 1:
            raise SignoffError(f"{E}: OR IOPATH: {io}")
        t = dn + io[0][1]
        cur = (m["or_cell"], "O")
        chk.req_out[cur] = t
        for c in roles.chain[E]:
            pins = [pin for pin in st._in_pins(c)
                    if g.driver_of[pin][0] == cur[0]]
            if len(pins) != 1:
                raise SignoffError(f"{E}: chain link into {c} ambiguous")
            dn2, _ = edge_delay(g, cur, pins[0])
            t += dn2
            chk.req[pins[0]] = t
            io2 = g.cell_outputs_from(c, pins[0][1])
            if len(io2) != 1:
                raise SignoffError(f"{E}: delay LUT {c} IOPATH: {io2}")
            t += io2[0][1]
            cur = (c, "O")
            chk.req_out[cur] = t
        chk.prop_req_from(cur, t, chain_cells)

        # data: fork -> sel -> mux cells (own) -> generic
        selpins = [pin for pin in st._in_pins(m["sel_cell"])
                   if (g.driver_of[pin][0], g.driver_of[pin][1]) == fork]
        if len(selpins) != 1:
            raise SignoffError(f"{E}: fork {fork} -> sel pins {selpins}")
        _dn3, dx3 = edge_delay(g, fork, selpins[0])
        chk.data[selpins[0]] = dx3
        for (op, _a, dxx) in g.cell_outputs_from(m["sel_cell"],
                                                 selpins[0][1]):
            chk.prop_data_from((m["sel_cell"], op), dx3 + dxx,
                               own_mux_cells=m["mux_cells"])

        # stitched sender deficit (F7): this fork's sender delivered its
        # data to the mux data pins `deficit` ps after the fork event;
        # re-seed those pins so downstream maxima are exact.
        deficit = deficits.get((E, fork), 0.0)
        if deficit > 0:
            for c in m["mux_cells"]:
                for pin in st._in_pins(c):
                    d = g.driver_of[pin]
                    if d[0] == m["sel_cell"] or d[0] in m["mux_cells"]:
                        continue  # sel / mux-internal cascade
                    if chk.data.get(pin, -INF) < deficit:
                        chk.data[pin] = deficit
                        for (op, _a, dxx) in g.cell_outputs_from(c, pin[1]):
                            chk.prop_data_from(
                                (c, op), deficit + dxx,
                                own_mux_cells=m["mux_cells"])
        seed_held_bypass(chk, st)
        checks.append(chk)
    return checks


def _walk_mem_chain(g, st, E, fork, chain, chk):
    """Explicit walk down a memory element's full delay chain from its
    fork (the driver of r_i): records the min arrivals as the check's
    request timeline (like the hlatch/merge walks) and returns
    [(cell, out_tmin, out_tmax)] per chain LUT for the pulse math."""
    arr = []
    cur = fork
    tmin = tmax = 0.0
    for c in chain:
        pins = [pin for pin in st._in_pins(c)
                if g.driver_of[pin][0] == cur[0]]
        if len(pins) != 1:
            raise SignoffError(f"{E}: chain link into {c} ambiguous")
        dn, dx = edge_delay(g, cur, pins[0])
        tmin += dn
        tmax += dx
        chk.req[pins[0]] = min(chk.req.get(pins[0], INF), tmin)
        io = g.cell_outputs_from(c, pins[0][1])
        if len(io) != 1:
            raise SignoffError(f"{E}: delay LUT {c} IOPATH: {io}")
        tmin += io[0][1]
        tmax += io[0][2]
        cur = (c, io[0][0])
        chk.req_out[cur] = tmin
        arr.append((c, tmin, tmax))
    return arr, cur, tmin


def _gate_hop(g, st, E, gate_cell, drv_cell):
    """The (min, max, out_node) traversal of `gate_cell` via the pin
    driven by `drv_cell` (edge + IOPATH)."""
    pins = [pin for pin in st._in_pins(gate_cell)
            if g.driver_of[pin][0] == drv_cell]
    if len(pins) != 1:
        raise SignoffError(f"{E}: gate {gate_cell} pin from {drv_cell}: "
                           f"{pins}")
    dn, dx = edge_delay(g, (drv_cell, "O"), pins[0])
    io = g.cell_outputs_from(gate_cell, pins[0][1])
    if len(io) != 1:
        raise SignoffError(f"{E}: gate {gate_cell} IOPATH: {io}")
    return dn + io[0][1], dx + io[0][2], (gate_cell, io[0][0])


def _latch_capture_need(g, st, cell, en_pin):
    """Routed capture requirement of one storage dlatch bit: data
    feed-through (d pin -> O, max) plus the feedback-loop settle
    (O -> feedback pin interconnect + feedback pin -> O, max) -- the
    F14 write-pulse minimum the routed pulse width must exceed."""
    need_data = 0.0
    fb = 0.0
    for pin in st._in_pins(cell):
        if pin == en_pin or st._is_rst(pin):
            continue
        d = g.driver_of[pin]
        io = g.cell_outputs_from(cell, pin[1])
        dx = max((x for (_o, _n, x) in io), default=0.0)
        if d[0] == cell:
            fb = max(fb, d[3] + dx)
        else:
            need_data = max(need_data, dx)
    return need_data + fb


def _pulse_rows(g, st, roles, E, gate_cell, rise_from, fall_from,
                tags, label, policy):
    """F14 pulse-width minimum: the routed enable pulse (rise via
    `rise_from`, latest; fall via `fall_from`, earliest -- both from the
    element's fork, sharing the guard chain, so the shared-path skew is
    absorbed pessimistically) must exceed each destination latch bit's
    routed capture need.  Returns the single worst row."""
    rise_min, rise_max, out = _gate_hop(g, st, E, gate_cell,
                                        rise_from[0])
    fall_min, fall_max, _o2 = _gate_hop(g, st, E, gate_cell,
                                        fall_from[0])
    rise_t = rise_from[2] + rise_max     # latest pulse open
    fall_t = fall_from[1] + fall_min     # earliest pulse close
    worst = None

    def visit(node, r_t, f_t, depth):
        nonlocal worst
        for (c2, p2, dn, dx) in g.edges_out[node]:
            role = roles.role.get(c2, ("dp",))
            if role[0] == "mem_latch" and role[1] == E and role[2] in tags:
                width = (f_t + dn) - (r_t + dx)
                need = _latch_capture_need(g, st, c2, (c2, p2))
                if worst is None or width - need < worst[0] - worst[1]:
                    worst = (width, need, role[2])
            elif role[0] == "dp" and depth < 3:  # en gates
                for (op2, dn2, dx2) in g.cell_outputs_from(c2, p2):
                    visit((c2, op2), r_t + dx + dx2, f_t + dn + dn2,
                          depth + 1)

    visit(out, rise_t, fall_t, 0)
    if worst is None:
        raise SignoffError(f"{E}: {label}: pulse reaches no storage "
                           "latch (tracing hole)")
    width, need, tag = worst
    slack = width - need
    gb = policy.need_gap()
    return dict(consumer=f"{E}.{label}", req=width, data=need,
                slack=slack, need=gb, cells=1,
                verdict="PASS" if slack >= gb else "FAIL")


def run_mem_check(st, E, residual, policy):
    """One check per memory element (ram1rw / statevar), the producing
    knob for its continuation channels (its Tr covers commit + readback
    mux + downstream wiring to the hold latches):

    request:  fork (driver of r_i) -> the element's FULL delay chain
              (decode guard + pulse(s) + Tr) -> r_o -> demux steer ->
              hold-latch mullercs, exactly like an hlatch knob.
    data:     (a) every external input of the element and of its steer
              demux tree, launched at the fork (they were settled before
              r_i rose -- the upstream checks' guarantee -- so this is
              the same conservative convention the merge checks use);
              `residual` shifts the launch late when the port merge
              carried a sender deficit its request delay did not absorb;
              (b) the write path: fork -> decode-guard chain (max) ->
              pulse gate -> enables -> storage latch bits, whose outputs
              re-launch through the readback mux to d_o and beyond.
    plus the F14 pulse-width-minimum rows (routed pulse vs routed
    capture need) and, for statevar, the Tg snapshot-close-to-commit
    gap row."""
    g, roles = st.g, st.roles
    info = st.mems[E]
    mem = roles.mem_info[E]
    kind = mem["kind"]
    chk = Check(E, st, info["fork"])
    chain = roles.chain[E]
    arr, cur, t = _walk_mem_chain(g, st, E, info["fork"], chain, chk)
    chk.prop_req_from(cur, t, set(chain))

    seg_out = {}
    idx = 0
    for segname, cells in roles.mem_segs[E]:
        idx += len(cells)
        seg_out[segname] = arr[idx - 1]

    # ---- data seeds: external inputs of the element + its demux tree
    prefix = roles.prefix
    own = [c for c in g.cells
           if Roles._strip(c).startswith(prefix + E + ".")]
    dmx = [c for c in g.cells
           if Roles._strip(c).startswith(prefix + E + "_dmx")]
    grp = set(own) | set(dmx)
    seeds = set()
    for c in sorted(own) + sorted(dmx):
        for pin in st._in_pins(c):
            if st._is_rst(pin) or st._is_self(pin) \
                    or pin == info["r_pin"]:
                continue
            d = g.driver_of[pin]
            if d[0] in grp:
                continue
            # data sources are holders (latch bits) or merge mux gates;
            # ack sources (mullercs, forwarding C-elements) are handshake
            # signals, not bundled data -- seeding them would fabricate
            # data arrivals on ack nets
            if roles.kind(d[0]) not in ("dp", "hl_latch"):
                continue
            seeds.add((d[0], d[1]))
    for node in sorted(seeds):
        chk.prop_data_from(node, residual)

    # ---- write path: guard chain (max) -> pulse gate(s) -> enables
    gates = roles.mem_gates[E]
    if kind == "ram1rw":
        rise = seg_out["dly_decode"]
        _n, dx, out = _gate_hop(g, st, E, gates["warm_gate"], rise[0])
        chk.prop_data_from(out, rise[2] + dx)
        latch_order = sorted(roles.mem_latches[E])
    else:
        r1 = seg_out["dly_s"]
        _n1, dx1, out1 = _gate_hop(g, st, E, gates["p1_gate"], r1[0])
        chk.prop_data_from(out1, r1[2] + dx1)
        r2 = seg_out["dly_g"]
        _n2, dx2, out2 = _gate_hop(g, st, E, gates["p2_gate"], r2[0])
        chk.prop_data_from(out2, r2[2] + dx2)
        latch_order = ["master", "snap"]  # master feeds snap's data pin

    # ---- storage latches: re-launch from each bit's worst input arrival
    for tag in latch_order:
        for cell in roles.mem_latches[E][tag]:
            best = -INF
            for pin in st._in_pins(cell):
                if st._is_rst(pin) or st._is_self(pin):
                    continue
                ta = chk.data.get(pin, -INF)
                if ta == -INF:
                    continue
                for (op, _dn, dx) in g.cell_outputs_from(cell, pin[1]):
                    best = max(best, ta + dx)
            if best > -INF:
                chk.prop_data_from((cell, "O"), best)

    # ---- F14 pulse-width minimum rows (+ statevar Tg gap)
    extra = []
    if kind == "ram1rw":
        extra.append(_pulse_rows(
            g, st, roles, E, gates["warm_gate"], seg_out["dly_decode"],
            seg_out["dly_pulse"], set(roles.mem_latches[E]),
            "write_pulse(F14)", policy))
    else:
        extra.append(_pulse_rows(
            g, st, roles, E, gates["p1_gate"], seg_out["dly_s"],
            seg_out["dly_p1"], {"snap"}, "snap_pulse(F14)", policy))
        extra.append(_pulse_rows(
            g, st, roles, E, gates["p2_gate"], seg_out["dly_g"],
            seg_out["dly_p2"], {"master"}, "commit_pulse(F14)",
            policy))
        extra.append(_gap_row(g, st, roles, E, gates, seg_out,
                              policy))
    return chk, extra


def _gap_row(g, st, roles, E, gates, seg_out, policy):
    """statevar Tg check: the snapshot latch must be CLOSED (enable
    fallen + feedback settled) before the commit pulse can move `val`
    (its data input).  val moves no earlier than the p2 rise reaching
    the master latch enable plus its feed-through (min path); the snap
    closes no later than the p1 fall reaching its enable plus its
    feedback settle (max path)."""
    p1_fall_min, p1_fall_max, p1_out = _gate_hop(
        g, st, E, gates["p1_gate"], seg_out["dly_p1"][0])
    p2_rise_min, p2_rise_max, p2_out = _gate_hop(
        g, st, E, gates["p2_gate"], seg_out["dly_g"][0])
    t_p1_fall = seg_out["dly_p1"][2] + p1_fall_max
    t_p2_rise = seg_out["dly_g"][1] + p2_rise_min

    def en_pin_arrivals(out, tag, t0, use_max):
        res = []
        for (c2, p2, dn, dx) in g.edges_out[out]:
            role = roles.role.get(c2, ("dp",))
            if role[0] == "mem_latch" and role[1] == E \
                    and role[2] == tag:
                res.append((c2, (c2, p2), t0 + (dx if use_max else dn)))
        if not res:
            raise SignoffError(f"{E}: pulse gate reaches no {tag} latch")
        return res

    # snap closed (max): en fall + en->O + feedback loop, per bit
    closed = -INF
    for cell, pin, ta in en_pin_arrivals(p1_out, "snap", t_p1_fall, True):
        io = g.cell_outputs_from(cell, pin[1])
        en_io = max((x for (_o, _n, x) in io), default=0.0)
        fb = 0.0
        for q in st._in_pins(cell):
            d = g.driver_of[q]
            if d[0] == cell:
                qio = g.cell_outputs_from(cell, q[1])
                fb = max(fb, d[3] + max((x for (_o, _n, x) in qio),
                                        default=0.0))
        closed = max(closed, ta + en_io + fb)
    # val moves (min): p2 rise at master en + en->O feed-through +
    # routing to the snap data pin
    move = INF
    for cell, pin, ta in en_pin_arrivals(p2_out, "master", t_p2_rise,
                                         False):
        io = g.cell_outputs_from(cell, pin[1])
        en_io = min((n for (_o, n, _x) in io), default=0.0)
        hop = min((dn for (_c2, _p2, dn, _dx)
                   in g.edges_out[(cell, "O")]), default=0.0)
        move = min(move, ta + en_io + hop)
    slack = move - closed
    gb = policy.need_gap()
    return dict(consumer=f"{E}.snap_commit_gap(Tg)", req=move,
                data=closed, slack=slack, need=gb, cells=1,
                verdict="PASS" if slack >= gb else "FAIL")


# --------------------------------------------------------------------------
# Comparison + report
# --------------------------------------------------------------------------

def consumer_label(roles, st, cell):
    k = roles.role.get(cell, ("dp",))
    if k[0] == "hl_latch":
        return f"{k[1]}.latch"
    if k[0] == "hl_mull":
        return f"{k[1]}.mullerc"
    if k[0] == "merge_sel":
        return f"{k[1]}.sel"
    if k[0] == "mem_latch":
        return f"{k[1]}.{k[2]}"
    if k[0] == "forward":
        s = Roles._strip(cell)
        s = s[len(roles.prefix):] if s.startswith(roles.prefix) else s
        return s.replace(".main.genblk1.main", "")
    if k[0] == "chain":
        return f"{k[1]}.chain[{k[2]}]"
    # datapath cell (ctl gate etc.)
    s = cell[len(roles.prefix):] if cell.startswith(roles.prefix) else cell
    return f"dp:{s[:60]}"


def compare_check(chk, st, policy):
    """Yield comparison rows: (consumer, req_ps, data_ps, slack, npins)."""
    roles = st.roles
    by_cell_req = defaultdict(dict)
    by_cell_data = defaultdict(dict)
    for (c, p), t in chk.req.items():
        by_cell_req[c][p] = t
    for (c, p), t in chk.data.items():
        by_cell_data[c][p] = t

    rows = []
    grouped = defaultdict(list)  # label -> [(slack, req, data, cell)]
    for c in set(by_cell_req) & set(by_cell_data):
        # Compare only where request and data genuinely race:
        #   hl_latch -- transparent latch: data pin vs en pin;
        #   dp       -- combinational cells with mixed inputs (demux ctl
        #               gates: rctl vs dctl).
        # Library C-elements (hlatch handshake, demux r0/r1, combine,
        # split, merge sel) are exempt: a Muller C output fires on its
        # *last* input, so input skew is not a bundling hazard there --
        # provided each input is glitch-free, which is exactly what the
        # dp-cell comparison at the driving gate verifies.
        if roles.kind(c) not in ("hl_latch", "dp"):
            continue
        rq = min(by_cell_req[c].values())
        da = max(by_cell_data[c].values())
        grouped[consumer_label(roles, st, c)].append((rq - da, rq, da, c))
    for label, entries in grouped.items():
        # gate the entry with the least slack RELATIVE to its own
        # guardband (under the ratio policy the worst absolute slack is
        # not necessarily the worst gated entry)
        slack, rq, da, cell = min(
            entries, key=lambda e: (e[0] - policy.need(e[2]),) + e)
        gb = policy.need(da)
        rows.append(dict(consumer=label, req=rq, data=da, slack=slack,
                         need=gb, cells=len(entries),
                         verdict="PASS" if slack >= gb else "FAIL"))

    # merge-boundary rows (F7 sender obligation) + stitching deficits.
    # Measured against the merge's fork event (the winning request leaving
    # the sender = t0 of the merge_delay check).  A negative slack here is
    # a "carry", not a FAIL: the deficit is seeded into the merge_delay
    # check (see run_merge_checks), whose downstream latch/gate rows are
    # the sound gate.  The merge's own check is excluded (its data
    # arrivals at its own mux are the sel-path cascade, not sender data).
    deficits = {}
    for E, m in st.merges.items():
        if E == chk.own_merge:
            continue
        data_pins = [t for (c, p), t in chk.data.items()
                     if c in m["mux_cells"]
                     and st.g.driver_of.get((c, p), ("",))[0]
                     not in (m["sel_cell"],)
                     and st.g.driver_of.get((c, p), ("",))[0]
                     not in m["mux_cells"]]
        fork_ts = [chk.req_out[f] for f in m["forks"] if f in chk.req_out]
        if not data_pins or not fork_ts:
            continue
        rq, da = min(fork_ts), max(data_pins)
        slack = rq - da
        gb = policy.need(da)
        fork = min(((chk.req_out[f], f) for f in m["forks"]
                    if f in chk.req_out))[1]
        # the carried deficit is computed from the policy-INFLATED sender
        # data arrival (see the header): a deficit is a difference of two
        # long paths, so the guardband must cover the sender's data PATH,
        # not just the small nominal difference.
        deficit = max(0.0, (da + gb) - rq)
        if deficit > 0:
            deficits[(E, fork)] = deficit
        rows.append(dict(consumer=f"merge@{E}", req=rq, data=da,
                         slack=slack, need=gb, cells=len(data_pins),
                         verdict="PASS" if deficit == 0 else "carry"))
    return rows, deficits


def coverage_audit(st, all_rows_by_check):
    """Every real data consumer must have been compared at least once."""
    roles, g = st.roles, st.g
    compared = set()
    for _chk, rows in all_rows_by_check:
        for r in rows:
            compared.add(r["consumer"])
    missing = []
    for E, info in st.hl.items():
        real = [pin for pin in info["data_pins"]
                if roles.kind(g.driver_of[pin][0]) != "io"]
        if real and f"{E}.latch" not in compared:
            missing.append(f"{E}.latch ({len(real)} routed data pins)")
    for E, m in st.merges.items():
        if not m["mux_cells"]:
            # degenerate merge: both data inputs are the same held nets
            # (e.g. a store's unchanged continuation bundle), so yosys
            # deleted every mux -- no cell switches data at the merge
            # and there is nothing to race; the downstream consumer rows
            # (held-bypass seeded) carry the F7 obligation instead.
            continue
        if f"merge@{E}" not in compared:
            missing.append(f"merge@{E}")
    for E in st.mems:
        kind = roles.mem_info[E]["kind"]
        want = ["write_pulse(F14)"] if kind == "ram1rw" else \
            ["snap_pulse(F14)", "commit_pulse(F14)",
             "snap_commit_gap(Tg)"]
        for w in want:
            if f"{E}.{w}" not in compared:
                missing.append(f"{E}.{w}")
    return missing


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--sdf",
                    help="SDF from nextpnr-ice40 --sdf (routed delays)")
    ap.add_argument("--graph-json",
                    help="routed delay graph from boards/xc7/"
                         "timing_dump.py (xc7: stock nextpnr-xilinx "
                         "has no --sdf, Q7b)")
    ap.add_argument("--sidecar", required=True,
                    help="hlsc timing sidecar (<design>.timing.json)")
    ap.add_argument("--policy", choices=("ratio", "zero"), default="ratio",
                    help="guardband policy (Q9): 'ratio' (default) gates "
                         "each comparison at slack >= max(0.2 x data, "
                         "200 ps); 'zero' is the plain slack >= "
                         "--min-slack-ps debug gate")
    ap.add_argument("--min-slack-ps", type=float, default=0.0,
                    help="required slack in ps under --policy zero "
                         "(ignored under 'ratio')")
    ap.add_argument("--report", help="write the report to this file too")
    args = ap.parse_args()
    policy = Policy(args.policy, args.min_slack_ps)

    if bool(args.sdf) == bool(args.graph_json):
        ap.error("exactly one of --sdf / --graph-json is required")
    sidecar = json.load(open(args.sidecar))
    if "elements" not in sidecar:
        raise SignoffError("sidecar has no 'elements' (pre-M3 format?)")
    g = load_sdf(args.sdf) if args.sdf else load_graph_json(args.graph_json)
    roles = Roles(g, sidecar)
    st = Structure(g, roles)

    # Order: hlatch checks first, then merge_delay checks in dependency
    # order (a merge fed by another merge's chain needs that sender's
    # deficit first).  Merge->merge cycles are impossible in the emitted
    # shapes (every ring contains hlatches); detected and rejected anyway.
    hlatches = [e["name"] for e in sidecar["elements"]
                if e["kind"] == "hlatch"]
    mdlys = [e["name"] for e in sidecar["elements"]
             if e["kind"] == "merge_delay"]
    chain_owner = {c: E for E, cells in roles.chain.items() for c in cells}
    deps = {E: set() for E in mdlys}
    for E in mdlys:
        for f in st.merges[E]["forks"]:
            owner = chain_owner.get(f[0])
            if owner in deps:
                deps[E].add(owner)
    order = []
    while len(order) < len(mdlys):
        ready = [E for E in mdlys if E not in order
                 and deps[E] <= set(order)]
        if not ready:
            raise SignoffError("merge->merge dependency cycle "
                               f"among {set(mdlys) - set(order)}")
        order.extend(ready)

    all_rows = []
    deficits = {}
    for E in hlatches:
        chk = run_hlatch_check(st, E)
        rows, defs = compare_check(chk, st, policy)
        deficits.update(defs)
        all_rows.append((chk, rows))
    merge_chain_end = {}   # mdly E -> min request arrival at chain end
    for E in order:
        for chk in run_merge_checks(st, E, deficits):
            rows, defs = compare_check(chk, st, policy)
            deficits.update(defs)
            all_rows.append((chk, rows))
            end = chk.req_out.get(st.merges[E]["chain_out"], INF)
            merge_chain_end[E] = min(merge_chain_end.get(E, INF), end)
    # memory elements last: a port merge's sender deficit larger than
    # its request-delay chain shifts the element's data launch late
    mems = [e["name"] for e in sidecar["elements"]
            if e["kind"] in ("ram1rw", "statevar")]
    for E in mems:
        mem = roles.mem_info[E]
        residual = 0.0
        mdly = mem.get("request_delay")
        if mdly is not None:
            worst = max((v for (dE, _f), v in deficits.items()
                         if dE == mdly), default=0.0)
            residual = max(0.0, worst - merge_chain_end.get(mdly, 0.0))
        chk, extra = run_mem_check(st, E, residual, policy)
        rows, defs = compare_check(chk, st, policy)
        deficits.update(defs)
        all_rows.append((chk, rows + extra))

    missing = coverage_audit(st, all_rows)

    lines = []
    lines.append("bundled-data timing signoff (routed, nextpnr SDF)")
    lines.append("=" * 78)
    lines.append(f"sidecar : {args.sidecar}")
    lines.append(f"delays  : {args.sdf or args.graph_json}")
    lines.append(f"policy  : {policy.describe()}")
    lines.append("          (arrivals in ps from each producer's fork "
                 "event; need = required guardband)")
    lines.append("")
    lines.append(f"{'producer':16} {'consumer':34} {'req_ps':>8} "
                 f"{'data_ps':>8} {'need':>6} {'slack':>7}  verdict")
    lines.append("-" * 78)
    nfail = 0
    ncarry = 0
    worst = None
    for chk, rows in all_rows:
        for r in sorted(rows, key=lambda r: r["slack"] - r["need"]):
            if r["verdict"] == "FAIL":
                nfail += 1
            if r["verdict"] == "carry":
                ncarry += 1
            elif worst is None or \
                    r["slack"] - r["need"] < worst[0] - worst[3]:
                worst = (r["slack"], chk.name, r["consumer"], r["need"])
            lines.append(f"{chk.name:16} {r['consumer']:34} "
                         f"{r['req']:8.0f} {r['data']:8.0f} "
                         f"{r['need']:6.0f} {r['slack']:7.0f}  "
                         f"{r['verdict']}")
    lines.append("-" * 78)
    ncmp = sum(len(rows) for _c, rows in all_rows)
    lines.append(f"{ncmp} comparisons, {nfail} FAIL")
    if worst:
        lines.append(f"worst gated slack: {worst[0]:.0f} ps vs need "
                     f"{worst[3]:.0f} ps ({worst[1]} -> {worst[2]})")
    if ncarry:
        lines.append(f"{ncarry} merge-boundary carry(s): sender data "
                     "settled after the merge fork event; the deficit was "
                     "stitched into that merge's own check (F6/F7), whose "
                     "downstream rows above are the sound gate.")
    if missing:
        nfail += len(missing)
        lines.append("COVERAGE FAIL: consumers never compared "
                     "(tracing hole -- do not trust this signoff):")
        for msg in missing:
            lines.append(f"  ! {msg}")
    lines.append("result: " + ("FAIL" if nfail else "PASS"))
    text = "\n".join(lines) + "\n"
    sys.stdout.write(text)
    if args.report:
        open(args.report, "w").write(text)
    return 1 if nfail else 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except SignoffError as exc:
        print(f"timing_signoff: TRACING ERROR: {exc}", file=sys.stderr)
        sys.exit(2)
