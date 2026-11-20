#!/usr/bin/env python3
"""corner_audit.py ROUTE_DIR [options] -- every post-route constraint of one route at ONE delay corner (the full
stack's worst case by default), and a per-line sizes.vh proposal: each matched delay as short as ITS OWN constraints
allow at the given guards.  PROGRAM item 3 ("shrink the matched delays to what the sim proves"), per cell instead of a
global factor.

    python3 research/tools/corner_audit.py $S/k4/xorshift/seed1                 # worst case, residual guards
    python3 research/tools/corner_audit.py $S/k4/collatz_s50/seed2 --fast-min   # FAST_MIN everywhere

ROUTE_DIR is a bdc/fusion_bench.py route (seedN/), with pnr/{soak_xray.sdf, soak_routed.json, sizes.vh}
(pnr/soak_xray.sdf from cells/gls/fid/xray_delay.py, as the k4 full-stack scripts make it).  Writes into --out
(default <scratchpad>/cs/<kernel>__<seed>__<corner>/):

  soak.sdf          the corner SDF (research/tools/corner_sdf.py), with soak_routed.json linked beside it
  report.txt        every constraint the audits measure, with its margin at this corner and guard, worst first
  lines.tsv         per delay line: size, chain delay at the corner, the constraints it sits on, proposed size
  sizes.vh          the proposal (route's sizes.vh with changed lines only)
  verify.txt        the audits re-run on the corner SDF with every changed line's chain set to its PREDICTED delay

THE AUDITS ARE NOT RE-IMPLEMENTED.  Each run imports cells/verify/skew.py (which imports tighten.py) and
cells/verify/arb_fork.py in a fresh subprocess, patches, for that process only, tighten.req_guard (rule A/F/H/I/K/L
guard: max(a_frac * t_data, a_min) instead of max(0.2 * t_data, 200)) and skew/arb_fork GUARD_LO/GUARD_HI, and calls
their main()s -- the same `verify/<audit>.py <sdf>` invocation bdc/fusion_bench.py makes, on the corner SDF.  Rule D
is reported, never sized on: it is a screen (tighten.py and research/tools/audit_route.sh say so).  Rules B/C keep the
vendor's own BRAM numbers.

TWO DEPARTURES FROM tighten.py's RULE A, both on by default and both printed in report.txt:
  * a constant driver ($PACKER_GND_DRV/VCC) never starts a data path (--keep-const-launch restores it): on
    xorshift_s50 seed 1 the GND tie-off into ucmpi0's carry chain was the "latest data" by 3.4 ns;
  * A' -- where tighten can only pair a cell as a BUNDLED CHANNEL (request from the cell's join at t=0, data from
    the upstream link's latch at t=0, which drops the upstream link's DELAY lead), the same rule is re-measured from
    each upstream link's C node with skew.py's storage-crossing walk(), and A' is what gets sized
    (--rule-a-tighten sizes tighten's own row instead).  tighten's row is still reported, as rule "a".

WHICH LINE A CONSTRAINT DEPENDS ON is MEASURED, not inferred from names: for each delay line (a sizes.vh macro, all its
chains), one more run with that line's internal arcs (its LUT arcs and link-to-link hops) set to 0.  Every constraint
whose margin drops is one the line sits on the early side of (a request, a hold path, a close); dM = how much it
dropped.  A line on no constraint keeps its size.  Shortening by d ps then costs at most min(k*d, dM) on that
constraint, k = max(observed slope dM/D, 1; 0.97 for rule E) -- a shortest path can lose at most what the line gives
up, and never more than removing the whole line did.  Drops on one constraint from several lines are ADDED (an upper
bound).  The shrink is greedy, longest line first; a constraint already negative is first fixed by padding its own
knob (the rule's attributed line, else the line it depends on most).

PER-LINK COST (cells/hw/tighten_loop.sh: a shortened chain gets CHEAPER per link -- 418 -> 304 ps on uaddi0 -- so
"n links at today's cost" under-delivers, in the short direction).  A line of n links shortened to m is assumed to
deliver
        D(m) = min( D(n) - (n - m) * c_rm ,  lut_lo + (m - 1) * c_lo )
  c_rm   the line's own DEAREST link-to-link step at this corner (removing the slowest links first);
  c_lo   the CHEAPEST link-to-link step (LUT arc + routed hop) measured on ANY chain of this route at this corner,
         lut_lo the cheapest chain LUT arc: the rebuilt line is assumed as compact as the most compact link this
         route ever placed.
and a padded line D(n) + (m - n) * c_lo.  Lines keep >= --floor links (default 1: a line is never removed; 0 stays 0).
The harness's own lines (upipe, uspin) are measured but kept unless --all-lines.
SELECT PATHS ARE NEVER SHORTENED (default; --shrink-selects to allow): every mux's own delay (BD_SZ_UUT_UMUX*) and
every link on a channel bdc reads as a SELECT (bdc/emit.py select_channels(), from the route's input.mlir; DELAY and
SDELAY) keep at least their current size.  None of the rules here sees the race these lines guard -- a select that
arrives before its data token, after which the mux fires on the data request alone -- and two shortened select paths
failed the full stack on routes the proposal was not measured on (ipow umux3, collatz64 ulink_n14__1; JOURNAL
2026-11-09 / 11-11).  They may still be padded.

VERIFY: the corner SDF re-audited with each changed line's chain arcs scaled to D(m)/D(n) -- path switching included,
exactly as the audits see it.  A constraint that comes out below --slack bumps the line that cost it most, and the
loop repeats.  This is still ONE route: a proposal must be routed and put through the full stack before it is a size.
"""
import argparse, collections, contextlib, io, json, math, os, pathlib, re, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parent.parent
VERIFY = REPO / "cells" / "verify"
SCRATCH = pathlib.Path("/tmp/claude-0/-home-user-asyncfpga3/5430fd50-f33d-52a5-8a52-f19d5b6000df/scratchpad/cs")
RE_LINK = re.compile(r"^(?P<base>.+)\.chain\.g\[(?P<i>\d+)\]\.u$")
# CA_SIZERULE=1 (opt-in, 2026-11-17; research/data/sizerule/README.md): "sizerule1", one sizing rule for every kernel.
# Unset, every output of this tool is byte-identical to before.  Set, three things change and nothing else:
#   1. ONE band for the delay chains and the rest of the fabric (LUT + wire): --band defaults to 0.21 and no
#      --inst-rx override is applied, so a chain and the data path it matches sit at the same band position (the audit's
#      corner row: never mix corners).  The default corner put chains at 0.21 and the data's LUTs and wires at 0.288.
#      CARRY4 / F7F8 / FF stay at SLOW_MAX (--cell default): they were never measured (SIM-VS-BOARD row 2) and the draws
#      take them up to 1.0.  The residual guards (--guard-lo/hi, --a-frac/--a-min) are unchanged: they already are the
#      measured within-die scatter, not the band.
#   2. A shortened line is priced at its own MEAN link step as routed: D(m) = D(n) - (n - m) * c_own.  The default
#      prices removal at the line's dearest step and caps the rebuilt line at lut_lo + (m - 1) * c_lo, c_lo the single
#      cheapest hop anywhere on the route; on the farm's line accounts (fipowrh_la, fcsel3m_la, fc64eq_la) that gave
#      proposals ~1.6-2x what the line needs as routed.  How a re-placed chain's cost moves is a route-to-route spread,
#      which the per-cell max over routes (max_sizes.py) and the draws on fresh routes already cover; pricing it again
#      per route counted it twice.  CA_SIZERULE_MLO=1 adds the cap lut_lo + (m - 1) * c_mlo back, c_mlo the lowest MEAN
#      step of any chain of >= 3 links on the route (still milder than the default's single cheapest hop).  Padding
#      keeps the default price (c_lo: more links, never fewer).
#   3. Select paths are sized like any other line (implies --shrink-selects): PROGRAM 2026-11-15 withdrew the select
#      rule; rules E and M, which this tool sizes on, model the select races.
#   CA_SIZERULE_FLOOR=sizes.vh: no line is proposed below its value there (the largest size that failed a draw + 1).
SIZERULE = os.environ.get("CA_SIZERULE", "") == "1"
SIZERULE_FLOOR = os.environ.get("CA_SIZERULE_FLOOR", "")
SIZERULE_MLO = os.environ.get("CA_SIZERULE_MLO", "") == "1"
# CA_JOINAWARE=1 (opt-in, 2026-11-17; research/data/sizerule/joinaware.md): an operator's data is checked where it is
# CAPTURED, not at its own request.  Unset, every output of this tool is byte-identical to before.  Set:
#   * for every cell with an A' row (a generated operator whose data comes only from its upstream links), the data's
#     forward cone is followed to every capture: a bd_latch data pin (event: that latch's enable; compared at the latch
#     output, data via D->Q against the enable via EN->Q -- the latch-OPEN contract every other rule measures from: A'
#     launches the next cell's data at the link's C node, rule E crosses a latch on its enable, rule I composes a stage
#     from the sender's enable), or a steer / mux select pin (event: the request pin on the same LUT, as rule E pairs
#     them).  Launch: each upstream link's C node, as A'; the capture side walked with C-elements waiting for their
#     LAST input (skew.py's AND seeding, always on here) and each link C node seeded from its request pin only (its latch
#     cannot open before its request; an acknowledge on c_next is a lap).  This is row "A'j" (sized, rule A); the cell's
#     A' row becomes rule "a" (reported, not sized).  A cell whose cone reaches anything else (a storage input that is
#     not a latch's data or a select, an input of a non-combinational cell with no timing arc -- an FF's D, the PS7, an
#     IO --, a capture with no event or one its own request does not lead to) keeps A' and gets an unsized "j" row
#     saying why.
#   * the join credit (formal FOR-RESEARCH B3: "the later request must cover every input's data"): when the operator's
#     request reaches exactly one storage node, a join J (so its acknowledge is J's), J's other inputs (siblings) are
#     credited with a lower bound on their arrival relative to the launch S: min over S's forward ancestors A (the
#     C nodes driving S's req_in) of s(A -> sibling) - l(A -> S) [S fired by its request], and over S's acknowledge
#     sources K (the C nodes driving S's c_next) of s(K -> sibling) - l(K -> S) [S released by its acknowledge, which
#     is J's, which the sibling's acknowledge also waits for]; the min of the two is a lower bound in every interleaving
#     (research/data/sizerule/joinaware.md).  J's firing is then max(own input, credited sibling) on the capture walk.
#   * guard: A''s, max(a_frac * data, a_min), unless the credit binds; then max(a_frac * (data + capture + 2 l(A -> S)),
#     a_min) -- both legs, as rule E's 0.97 / 1.03, since the capture leg then runs through another cell's request.
#   * a line that no measured constraint depends on, and whose cell has an A'j row, may go to --floor (it is measured
#     free, not unmeasured); every other line on no constraint is kept, as before.
JOINAWARE = os.environ.get("CA_JOINAWARE", "") == "1"
# CA_BENCHCAP=1 (opt-in, 2026-11-19, with CA_JOINAWARE=1; data: research/data/benchcap/): the kernel's LAST operator --
# the one whose data is out0's -- is checked against the bench's clocked capture, not against its own request.  Unset,
# every output of this tool is byte-identical to before.  Why: on every kernel that operator kept A' (row "j": "its data
# reaches 64 input(s) that are not a latch's data or a select"), because its data's only sinks are flip-flops of the
# PS-clocked bench (cells/hw/gen_bench.py: result_hold, sampled in S_WAIT_RES only once BOTH 2-flop synchronisers
# of out0_req, o_req_l_s and o_req_s, read 1; o_data_capture, the free-running mirror the host reads by hand, ms after
# an idle handshake).  On isprime / gcd (a bdc_muxnN mux: its select decode sel[k] = ctl_req & (s == k) is a LUT of its
# own, outside its join C-elements uj0..ujN-1) A' then took that decode as data and measured it two crossings deep:
# the select link's return to zero after the BENCH's acknowledge (o_ack_pl = bench_o_ack & o_req_pl, a LUT the timing
# graph crosses as if the clocked bench_o_ack were already 1) -- a lap, not this token, that grows with the mux's own
# delay, so no line could pad it (-5125 ps on isprime umux13, -3422 on gcd umux21).  Set, two things change, in A'j only:
#   * a cone sink that is the D or CE pin of a flip-flop clocked by a global clock (its CK net driven by a BUFG*) is a
#     CLOCKED capture.  Its event: the operator's request entering that clock domain -- the earliest arrival, on A'j's
#     own early walk from the launch, at any input pin of a flip-flop on the same clock that the operator's request
#     tail reaches without crossing storage (out0_req's synchronisers' first stages, and anything else it reaches:
#     the earliest one is the conservative choice) -- plus CA_BENCHCAP_PS (default 19000): the bench samples out0's data
#     at least two full clock periods after a synchroniser's first stage can first have seen the request (one period
#     per flop; a first stage that samples the rising request inside its window still hands it on one edge later), at
#     the fastest clock the board scripts set (FCLK0 100 MHz, CLK_CTRL 0x00100A00; build_bench.sh closes the bench at
#     83 MHz), less 1000 ps for the first stage's setup / hold window, the capture flop's setup and the clock tree's
#     skew: 2 * 10000 - 1000.  The data's arrival at the flop's pin (A'j's late walk) must beat that event, with A''s
#     guard on the data leg; the event's walk must pass through the operator's tail, as for every A'j capture.  A
#     request that reaches no flop on that clock leaves the sink odd (the operator keeps A', as before).
#   * a cone sink that is an input of one of the operator's OWN join C-elements (a storage node inside the operator
#     that reaches its request chain's head without crossing storage: bdc_muxnN's uj<k>, fed by its select decode) is
#     neither a capture nor odd: it is the request's own cause (sel[k] rises, then uj<k> fires, then the chain), not a
#     place where data must beat a request.  The race on that decode -- s settling before ctl_req -- is a select race,
#     between two pins of the decode LUT, which A' never measured either.  CA_BENCHCAP_OWNJOIN=0 keeps such a sink odd.
#   The row's text says how many sinks of each kind it saw.  Nothing else moves: other rules, other cells' rows, and an
#   operator whose cone reaches any other non-capture keep their old rows.
BENCHCAP = os.environ.get("CA_BENCHCAP", "") == "1"
BENCHCAP_PS = int(os.environ.get("CA_BENCHCAP_PS", "19000"))
BENCHCAP_OWNJOIN = os.environ.get("CA_BENCHCAP_OWNJOIN", "1") != "0"
RE_LINK_C = re.compile(r"\.ctl\.u\.u/O6$")     # a bd_link (Muller) controller's C node
# CA_FAST=1 (opt-in, 2026-11-18; research/tools/ca_fast.py): the same audits, the base run made in this process and
# every later run (each line's sensitivity, each verify) in a fork of it, with the functions they call memoized exactly
# (topology by content; walks, rows A' / A'j and the other weight-reading functions by content and by the pins whose
# arcs they read, so a run that changes a line's arcs recomputes only what read them).  The outputs are the same files,
# byte for byte (research/tools/auto/ca_fast_e2e.sh).  Unset, nothing changes.  Ignored with --cut / --drop-inst /
# --osc (those runs change the graph itself).
FAST = os.environ.get("CA_FAST", "") == "1"
_ORIG = {}                     # the functions worker() wraps, as first imported (CA_FAST: as ca_fast wrapped them)
BASE_ARB = []                  # CA_FAST: the base run's (arb_rc, arb_log); rule J reads no scaled arc
NOMINAL = {"E": None}          # rule E: the request leg is guarded at GUARD_LO; set from args
SIZED_RULES = set("AEFHIKLBC")  # D is a screen; J has no delay line


# ============================================================== worker (one audit run, fresh process)

def worker(sdf, spec):
    """Run tighten.main, skew.main (verbose), arb_fork.main on `sdf`, with guards patched and chain arcs scaled per
    spec['scale'] {chain base: factor}.  -> JSON-able dict of constraints (+ chain geometry when spec['chains'])."""
    sys.path.insert(0, str(VERIFY))
    sys.argv = [sys.argv[0], str(sdf)] + [x for o in spec.get("osc", []) for x in ("--osc", o)]
    import skew                       # imports tighten with argv = [prog, sdf] (+ --osc for rigs with oscillators)
    import tighten as T
    import arb_fork
    if FAST:
        import ca_fast
        ca_fast.install(T, skew, sys.modules[__name__])
        if ca_fast.M.gen:             # a forked run: the pins whose outgoing arcs this run's scale changes
            ca_fast.M.changed = ca_fast.changed_pins(spec.get("scale") or {}, RE_LINK, T.pin_split)
            ca_fast.M.decrease_only = all(f <= 1 for f in (spec.get("scale") or {}).values())
            ca_fast.M._stale = None
            ca_fast.stale_keys()      # before this run replaces any base entry
    for name in ("parse_sdf", "line_links", "cell_boundary", "audit_fastfall"):
        _ORIG.setdefault(name, getattr(T, name))
    a_frac, a_min = spec["a_frac"], spec["a_min"]
    T.req_guard = lambda p, t: max(int(a_frac * t), a_min) + T.SLACK
    skew.GUARD_LO, skew.GUARD_HI = spec["glo"], spec["ghi"]
    arb_fork.GUARD_LO, arb_fork.GUARD_HI = spec["glo"], spec["ghi"]
    skew.VERBOSE = True
    scale = spec.get("scale") or {}
    orig_parse = _ORIG["parse_sdf"]

    def parse(path):
        edges, celltype, n_io, n_ic = orig_parse(path)
        if scale:
            for src in list(edges):
                si = T.pin_split(src)[0]
                ms = RE_LINK.match(si)
                if not ms or ms.group("base") not in scale:
                    continue
                f = scale[ms.group("base")]
                new = []
                for dst, w in edges[src]:
                    md = RE_LINK.match(T.pin_split(dst)[0])
                    if md and md.group("base") == ms.group("base"):   # LUT arc or link-to-link hop
                        w = int(round(w * f))
                    new.append((dst, w))
                edges[src] = new
        # --cut REGEX: case analysis -- drop every arc whose "src -> dst" matches (e.g. the arcs that cannot toggle in
        # the case being checked); the audits then time only what is left
        for rx in spec.get("cut", []):
            crx = re.compile(rx)
            for src in list(edges):
                edges[src] = [(dd, ww) for dd, ww in edges[src] if not crx.search(f"{src} -> {dd}")]
        # --drop-inst REGEX: remove whole instances (their CELL entries and every arc touching them), e.g. the delay
        # line that is not in play in a case, so the audits' per-cell line pairing cannot pick it
        for rx in spec.get("drop", []):
            crx = re.compile(rx)
            gone = {i for i in celltype if crx.search(i)}
            for i in gone: celltype.pop(i, None)
            for src in list(edges):
                if crx.search(T.pin_split(src)[0]):
                    edges.pop(src); continue
                edges[src] = [(dd, ww) for dd, ww in edges[src] if not crx.search(T.pin_split(dd)[0])]
        # --osc: a declared free-running oscillator's arcs are cut here too, so routed_graph() (rule A') sees the same
        # graph tighten.main does after its own --osc handling
        for pre in spec.get("osc", []):
            for src in list(edges):
                i = T.pin_split(src)[0]
                if i == pre or i.startswith(pre + "."):
                    edges[src] = []
        return edges, celltype, n_io, n_ic
    T.parse_sdf = parse
    # A zeroed line prices its own links at 0 ps: tighten's RECOMMENDATION (not its margin) divides by that.
    orig_ll = _ORIG["line_links"]

    def ll(n, *a, **k):
        try:
            return orig_ll(n, *a, **k)
        except ZeroDivisionError:
            return n, 1, "line zeroed by corner_audit"
    T.line_links = ll
    # Rule A's cell_boundary() lets the packer's constant drivers start a data path (tighten.py's own CONST_DRV
    # comment: a net that never transitions cannot start one; starts_reaching() and skew.py already drop them).
    # On xorshift_s50 seed 1 the GND tie-off into ucmpi0's carry chain was the "latest data" by 3.4 ns.
    ocb = _ORIG["cell_boundary"]
    T.cell_boundary = ocb
    if spec.get("drop_const", True):
        T.cell_boundary = lambda *a, **k: {s for s in ocb(*a, **k) if not T.is_const(s)}
    f_rows = []
    orig_ff = _ORIG["audit_fastfall"]

    def ff(*a, **k):
        r = orig_ff(*a, **k)
        f_rows.extend(r)
        return r
    T.audit_fastfall = ff

    out = {}
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        try:
            out["tighten_rc"] = T.main()
        except SystemExit as e:
            out["tighten_rc"] = e.code
    out["tighten_log"] = buf.getvalue()
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        try:
            out["skew_rc"] = skew.main()
        except SystemExit as e:
            out["skew_rc"] = e.code
    out["skew_log"] = buf.getvalue()
    buf = io.StringIO()
    if FAST and ca_fast.M.gen and BASE_ARB:           # rule J reads the corner SDF itself, never a scaled arc
        out["arb_rc"] = BASE_ARB[0]
        buf.write(BASE_ARB[1])
    else:
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
            try:
                out["arb_rc"] = arb_fork.main([str(sdf)])
            except SystemExit as e:
                out["arb_rc"] = e.code
            except Exception as e:                          # no arbiter JSON etc.: a gap, reported
                print("arb_fork raised %s: %s" % (type(e).__name__, e))
                out["arb_rc"] = 2
    out["arb_log"] = buf.getvalue()
    out["constraints"] = parse_logs(out, f_rows, T)
    if spec.get("rule_a_link", True):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            ap = rule_a_from_link(T, skew, sdf)
        for parent, d in ap.items():
            if d.pop("partial", False):                    # added for the peers tighten's A never reached; A stays
                out["constraints"]["A'm %s" % parent] = d
                continue
            out["constraints"]["A' %s" % parent] = d
            k = "A %s" % parent
            if k in out["constraints"]:
                out["constraints"][k]["rule"] = "a"        # reported; A' is what is sized on
        if JOINAWARE:                                      # A'j: the operator's data at its captures (see top)
            aprime = {k.split(" ", 1)[1]: c["margin"] for k, c in out["constraints"].items() if k.startswith("A' ")}
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                jr = rule_a_joined(T, skew, sdf, aprime)
            for parent, d in jr.items():
                sized = d.pop("sized")
                out["constraints"]["A'j %s" % parent] = d
                if sized:
                    out["constraints"]["A' %s" % parent]["rule"] = "a"   # reported; A'j is what is sized on
    if spec.get("chains"):
        out["chains"] = chain_geometry(T, sdf)
    for k in ("tighten_log", "skew_log", "arb_log"):
        if not spec.get("keep_logs"):
            out.pop(k)
    return out


def rule_a_from_link(T, skew, sdf):
    """Rule A at a cell tighten.py can only pair as a BUNDLED CHANNEL (request and data on different nets, every
    boundary net launched at t=0: its own docstring calls that strictly more pessimistic than a common start, "a
    reason to look, not proof").  The common start exists one storage crossing upstream: the C node of each upstream
    bd_link the cell is fed by.  From it the request runs through that link's DELAY and the cell's join to the chain
    tail; the data runs through the link's latch and the cell's logic to every peer.  Both walks are skew.py's own
    walk() (one table per storage crossing; earliest on the fast-fall-pruned arcs, latest on all arcs), so the link's
    DELAY lead and the join, which bundled pairing throws away, are counted -- the measurement rule E already makes
    at select gates.  Only for cells whose every non-constant boundary source is an upstream link (else: tighten's A).
    -> {parent: constraint}"""
    edges, back, stops = T.routed_graph(pathlib.Path(sdf))
    if getattr(skew, "AND_JOIN", False):        # BD_SKEW_AND_JOIN=1: the same C-element seeding as skew.main()
        skew.AND_NODES.clear(); skew.AND_NODES.update(o for o in stops if skew.RE_CTREE_C.search(o))
    X = {}

    def build():                                # the timing graph; CA_FAST: only once a site is recomputed
        X["timing"] = T.Timing(edges, stops)
        X["binc"], X["srcs_of"], X["feed"] = _incoming(edges, stops)
        X["side"] = T.fastfall_side_arcs(edges)
        X["early_edges"] = _side_pruned(edges, X["side"])
    if not FAST:
        build()
    chains = T.find_chains(edges)
    walks = {}

    def walk(c, lng, term=None):                # skew.walk's tables from c (CA_FAST: the memo, which notes the read)
        if term is not None:                    # BD_PEERS_CELL: a data walk that never leaves the request line (below)
            if FAST:
                return skew.walk(edges if lng else X["early_edges"], stops, X["binc"], X["feed"], c, lng, term)[0]
            if (c, lng, term) not in walks:
                walks[(c, lng, term)] = skew.walk(edges if lng else X["early_edges"], stops, X["binc"], X["feed"], c,
                                                  lng, term)[0]
            return walks[(c, lng, term)]
        if FAST:
            return skew.walk(edges if lng else X["early_edges"], stops, X["binc"], X["feed"], c, lng)[0]
        if (c, lng) not in walks:
            walks[(c, lng)] = skew.walk(edges if lng else X["early_edges"], stops, X["binc"], X["feed"], c, lng)[0]
        return walks[(c, lng)]

    def at(levels, pin):
        for k, tab in enumerate(levels):
            if pin in tab:
                return tab[pin], k
        return None

    def site(parent, head, tail, links):        # one request site's A' row, or None
        if not X:
            build()
        timing = X["timing"]
        downstream = T.downstream_of(edges, stops, parent, tail)     # inside the cell (BD_PEERS_CELL; tighten.py)
        upstream = {p for p in edges if T.is_output(p) and head in T.reaches(edges, p, stops)}
        own = set(links)
        # the cell's own request join (parent.ujoin.*) is the request path, not data: its inner C nodes reach the chain
        # head only through the join's top C node (a stop), so the 'upstream' test above misses them, and every request
        # or reset feeding the join then looked like a foreign data launch (2026-11-16: refused A' at collatz's uselect0
        # for the reset flop and the folded constant's request, which reach nothing but the join).  CA_JOIN_PEERS=1: old.
        join_pfx = parent + ".ujoin."
        peers = sorted({p for p in edges if T.is_output(p) and T.pin_split(p)[0].startswith(parent + ".")
                        and T.pin_split(p)[0] not in own and p not in downstream and p not in upstream
                        and (os.environ.get("CA_JOIN_PEERS") == "1" or not T.pin_split(p)[0].startswith(join_pfx))})
        if not peers:
            return None
        bnd = T.cell_boundary(edges, back, stops, parent)
        ups = T.upstream_bd_links(bnd)
        # a 1-bit link's latch is one whole LUT, '<link>.lat.odd.u' (no $LUT5/6 half), which tighten's
        # RE_UPSTREAM_BD_LINK does not match: a select link was then never an upstream link, and its latch output
        # counted as a foreign source (2026-11-16, at every bd_mux).  CA_ODD_LINKS=0: old behaviour.
        if os.environ.get("CA_ODD_LINKS") != "0":
            odd = {mm.group(1) for q in bnd for mm in [re.match(r"^(.*?)\.lat\.odd\.u$", T.pin_split(q)[0])] if mm}
            ups = tuple(sorted(set(ups) | odd))
        region = (parent,) + ups
        srcs = T.cell_boundary(edges, back, stops, region)
        partial = False
        if not ups or T.check(timing, srcs, peers, tail, T.req_guard, confine=region if ups else parent) is not None:
            # T.check pairs the request with ANY peer it shares a source with and says nothing about the peers no common
            # source reaches.  At a bd_mux those are the 32 data outputs the select drives (select latch -> data LUTs):
            # the request comes from the join, the select from the select link's latch, a storage crossing apart, so
            # tighten's A covers the x / y data and never the select's path -- the race the mux's own delay is kept for
            # (JOURNAL 2026-11-16, "rule M").  Those peers get the A' measurement below, from the upstream links' C nodes,
            # as an ADDED constraint (key "A'm"): tighten's A row stays as it is.  CA_MUX_PEERS=0: old behaviour.
            unc = []
            if ups and os.environ.get("CA_MUX_PEERS") != "0":
                conf = region
                unc = [p for p in peers if not any(p in timing.late(s, conf) and tail in timing.early(s, conf)
                                                   for s in srcs)]
            if not unc:
                if os.environ.get("CA_DEBUG_FOREIGN"):
                    with open(os.environ["CA_DEBUG_FOREIGN"], "a") as dbg:
                        print("A' not tried at %s: %s" % (parent, "no upstream link" if not ups else "common source"), file=dbg)
                return None                            # common-source pairing: tighten's A is already exact
            peers, partial = unc, True
        inside = lambda p: any(T.pin_split(p)[0] == r or T.pin_split(p)[0].startswith(r + ".") for r in region)
        # a source outside the region that reaches a peer WITHOUT crossing one of the links' latches would launch
        # data this measurement does not see: then keep tighten's A
        # (an outside combinational source -- logic fused between the link and the cell -- is fine when everything
        # that drives it is itself one of the region's storage nodes, which the walk crosses)
        def foreign(s):
            if inside(s) or T.is_const(s) or not any(p in timing.late(s, region) for p in peers):
                return False
            return s in stops or any(not inside(x) for x in T.starts_reaching(back, s, stops))
        if any(foreign(s) for s in srcs):
            if os.environ.get("CA_DEBUG_FOREIGN"):          # which source blocks A' at this cell (diagnosis only)
                with open(os.environ["CA_DEBUG_FOREIGN"], "a") as dbg:
                    for s in sorted(s for s in srcs if foreign(s)):
                        print("A' refused at %s: foreign %s (stop %s; outside starts %s)" % (parent, s, s in stops,
                              sorted(x for x in T.starts_reaching(back, s, stops) if not inside(x))[:6]), file=dbg)
            return None
        # BD_PEERS_CELL: a peer the request reaches only through its consumer's acknowledge (the divider's enables,
        # tighten.downstream_of) is reached by this unconfined data walk that way too -- C node, join, the request line,
        # the consumer, z_ack, the peer: a lap through the request, later than the request by construction.  At such a
        # site the data walk may arrive at the request line but never leave it (skew.walk's `term`); every other site
        # walks exactly as before.
        lap = None
        if T.PEERS_CELL:
            full = T.reaches(edges, tail, stops)
            if any(p in full for p in peers):
                lap = (RE_LINK.match(links[0]).group("base") + ".") if links else (T.pin_split(tail)[0] + "/")
        worst = None
        for link in ups:
            for c in (link + ".ctl.u.u/O6", link + ".ctl.ub/O6"):
                if c not in stops:
                    continue
                wf, wt = walk(c, False), walk(c, True, lap)
                r = at(wf, tail)
                # the data may cross one storage node more than the request (the link's latch, when the request
                # leaves the C node directly); a peer first reached deeper than that is a lap, not this token
                ds = [(at(wt[:r[1] + 2], p), p) for p in peers] if r else []
                ds = [(v, p) for v, p in ds if v is not None]
                if r is None or not ds:
                    continue
                (t_d, k_d), peer = max(ds)
                g = T.req_guard(None, t_d)
                m = r[0] - t_d - g
                if os.environ.get("CA_DEBUG_FOREIGN"):          # every launch's margin (diagnosis only)
                    with open(os.environ["CA_DEBUG_FOREIGN"], "a") as dbg:
                        print("A'%s %s launch %s: req %d data %d (%s) guard %d margin %d" % ("m" if partial else "",
                              parent, c, r[0], t_d, T.pin_split(peer)[0], g, m), file=dbg)
                if worst is None or m < worst[0]:
                    worst = (m, g, r[0], r[1], t_d, k_d, peer, c)
        if worst is None:
            return None
        m, g, t_r, k_r, t_d, k_d, peer, c = worst
        return {"rule": "A", "margin": int(m), "knob": parent, "partial": partial,
                "text": "%s%s %d links  from %s: req %d (%dx)  data %d (%dx, %s)  guard %d  margin %d"
                        % (parent, " [peers no common source reaches: %d]" % len(peers) if partial else "",
                           len(links), c, t_r, k_r, t_d, k_d, T.pin_split(peer)[0], g, m)}
    out = {}
    for parent, head, tail, links in T.request_sites(edges, back, chains):
        r = _per_site("A'", (edges, stops, back, skew), site, parent, head, tail, links)
        if r is not None:
            out[parent] = r
    return out


def _incoming(edges, stops):
    """(binc, srcs_of, feed): every pin's incoming arcs and sources, and the storage nodes' own feedback arcs -- as
    skew.main builds them.  CA_FAST: built once in the base run; a forked run copies binc with its changed pins'
    arcs re-read, and shares srcs_of and feed (no weight in them)."""
    if FAST:
        import ca_fast
        return ca_fast.incoming(edges, stops)
    binc, srcs_of = collections.defaultdict(list), collections.defaultdict(set)
    for s, lst in edges.items():
        for d, w in lst:
            binc[d].append((s, w))
            srcs_of[d].add(s)
    feed = {(o, ip) for o in stops for ip, _ in binc.get(o, ()) if o in srcs_of[ip]}
    return binc, srcs_of, feed


def _side_pruned(edges, side):
    """edges without the arcs in `side` (the fast-fall taps): the request walks' graph.  CA_FAST: a forked run copies
    the base run's and rebuilds its changed pins only."""
    if FAST:
        import ca_fast
        return ca_fast.side_pruned(edges, side)
    return {s: [(d, w) for d, w in lst if (s, d) not in side] for s, lst in edges.items()}


def _per_site(rule, graph, fn, parent, head, tail, links, *extra):
    """fn(parent, head, tail, links) -> a row (a fresh dict: the caller pops keys) or None.  CA_FAST: memoized per
    site, keyed by the graph's topology, the C-elements the walks wait on, the environment switches the rules read and
    `extra` (inputs from other rows), and reused while nothing it read changed."""
    if not FAST or os.environ.get("CA_DEBUG_FOREIGN"):
        r = fn(parent, head, tail, links)
    else:
        import ca_fast
        edges, stops, back, skew = graph
        key = ("site", rule, ca_fast.fp_graph(edges), ca_fast.fp_set(stops), ca_fast.fp_back(back),
               ca_fast.fp_small(skew.AND_NODES), skew.K,
               tuple(os.environ.get(v) for v in ("CA_JOIN_PEERS", "CA_ODD_LINKS", "CA_MUX_PEERS", "CA_DEBUG_FOREIGN",
                                                 "CA_BENCHCAP", "CA_BENCHCAP_PS", "CA_BENCHCAP_OWNJOIN",
                                                 "BD_PEERS_CELL")),
               parent, head, tail, tuple(links)) + extra
        r = ca_fast.call(key, fn, parent, head, tail, links)
    return dict(r) if r is not None else None


def walk_floor(skew, walked_edges, stops, binc, feed, launch, longest, and_nodes, floor=None, req_only=None):
    """skew.walk() (one arrival table per storage crossing; on the earliest walk a positive C-element in `and_nodes`
    is seeded with its LATEST input reached at the level, every other storage node with its earliest), plus one thing
    for CA_JOINAWARE: `floor` {AND node: t}, a lower bound on that node's firing relative to the launch from an input
    the launch does not reach at that level (rule_a_joined's sibling credit).  The seed is max(reached, floor); the
    predecessor stays the reached input.  `req_only` {link C node: its request pin}: on the earliest walk that node is
    seeded from its request pin alone -- C(req_in, ~c_next) cannot RISE (its latch cannot open) before its request
    arrives, so this is a lower bound on the opening, and it keeps an acknowledge arriving on c_next (a lap: the stage
    behind it emptying, another token) from standing in for the request.  -> (levels, preds), as skew.walk."""
    floor = floor or {}
    req_only = req_only or {}
    better = (lambda a, b: a > b) if longest else (lambda a, b: a < b)
    cap = len(walked_edges) + 1
    out, pred_out = [], []
    seeds, seed_pred = {launch: 0}, {launch: None}
    for lvl in range(skew.K + 1):
        tab, pred = dict(seeds), dict(seed_pred)
        seeded = set(seeds)
        frontier = list(seeds)
        passes = 0
        while frontier:
            passes += 1
            if passes > cap:
                raise skew.CombinationalCycle(sorted(frontier)[0])
            nxt = []
            for pn in frontier:
                tv = tab[pn]
                for d, w in walked_edges.get(pn, ()):
                    if (pn, d) in feed or d in seeded:
                        continue
                    if d not in tab or better(tv + w, tab[d]):
                        tab[d] = tv + w
                        pred[d] = (lvl, pn)
                        if d not in stops:
                            nxt.append(d)
            frontier = nxt
        out.append(tab)
        pred_out.append(pred)
        seeds, seed_pred = {}, {}
        for o in stops:
            if o == launch:
                continue
            if not longest and o in and_nodes:
                best_v = None
                for ip, arc in binc.get(o, ()):
                    if (o, ip) in feed or ip not in tab:
                        continue
                    v = tab[ip] + arc
                    if best_v is None or v > best_v[0]:
                        best_v = (v, ip)
                if best_v is not None:
                    seeds[o] = max(best_v[0], floor.get(o, best_v[0]))
                    seed_pred[o] = (lvl, best_v[1])
                continue
            for ip, arc in binc.get(o, ()):
                if (o, ip) in feed or ip not in tab or (not longest and o in req_only and ip != req_only[o]):
                    continue
                v = tab[ip] + arc
                if o not in seeds or better(v, seeds[o]):
                    seeds[o] = v
                    seed_pred[o] = (lvl, ip)
        if not seeds:
            break
    return out, pred_out


def rule_a_joined(T, skew, sdf, aprime):
    """CA_JOINAWARE=1: rule A' moved from the operator's own request to its data's CAPTURES (the comment at the top of
    this file; the argument in research/data/sizerule/joinaware.md).  `aprime`: the cells with an A' row.
    -> {parent: constraint dict + "sized" (False: the cell keeps its A' row, this one is reported as rule "j")}"""
    sdf = pathlib.Path(sdf)
    edges, back, stops = T.routed_graph(sdf)
    celltype = T.parse_sdf(sdf)[1]                    # instance -> SDF CELLTYPE
    and_nodes = {o for o in stops if skew.RE_CTREE_C.search(o)}     # always AND here: the rule's premise
    binc, srcs_of, feed = _incoming(edges, stops)
    side = T.fastfall_side_arcs(edges)
    early_edges = _side_pruned(edges, side)
    chains = T.find_chains(edges)
    jpath = sdf.with_name(sdf.stem + "_routed.json")
    jcells = _routed_cells(jpath)
    en_of = collections.defaultdict(set)              # bd_latch instance -> its enable pins
    for c in stops:
        if not T.RE_BD_LATCH.search(T.pin_split(c)[0]):
            for dst, _ in T.latch_enables(edges, c):
                en_of[T.pin_split(dst)[0]].add(dst)
    sel_req = {}                                      # steer / mux select pin -> (request pins on its LUT, label)
    for kind, par, reqs, sels in T.select_consumers(jpath) or []:
        for q in sels:
            rq = [r for r in reqs if T.pin_split(r)[0] == T.pin_split(q)[0]]
            if rq:
                sel_req[q] = (rq, "%s %s" % (kind, par))
    clk_of = {}                                       # CA_BENCHCAP: flip-flop -> its clock bit, when a BUFG* drives it
    if BENCHCAP:
        gbits = {b for c in jcells.values() if c.get("type", "").startswith("BUFG")
                 for p, dr in c.get("port_directions", {}).items() if dr == "output" for b in c["connections"].get(p, [])}
        for n, c in jcells.items():
            ck = c.get("connections", {}).get("CK", []) if c.get("type") == "SLICE_FFX" else []
            if len(ck) == 1 and ck[0] in gbits:
                clk_of[n] = ck[0]
    cache = {}

    def wk(launch, lng, floor=None, ro=True):
        if FAST:                                      # the memo (walk_floor's), which notes the read for the site
            return walk_floor(skew, edges if lng else early_edges, stops, binc, feed, launch, lng, and_nodes,
                              floor, req_pin if ro else None)
        key = (launch, lng, tuple(sorted((floor or {}).items())), ro)
        if key not in cache:
            cache[key] = walk_floor(skew, edges if lng else early_edges, stops, binc, feed, launch, lng, and_nodes,
                                    floor, req_pin if ro else None)
        return cache[key]

    def at(levels, pin, maxl=None):
        for k, tab in enumerate(levels if maxl is None else levels[:maxl]):
            if pin in tab:
                return tab[pin], k
        return None

    def path(pred, lvl, pin):
        return [n for _, n in (skew.path_to(pred, lvl, pin) or [])]

    def short(n):                                     # instance, without the kernel's path
        i = T.pin_split(n)[0] if "/" in n else n.split()[-1]
        return i.split(".udut.", 1)[1] if ".udut." in i else i

    def stops_on(p):
        return " > ".join(short(n) for n in p if n in stops) or "-"

    def c_inputs(node):                               # a link C node (bd_c2n: I0 req_in, I1 c_next): physical pins
        inst = T.pin_split(node)[0]
        ports = T.orig_ports(jcells[inst]) if inst in jcells else {}
        return tuple("%s/%s" % (inst, ports[i]) if i in ports else None for i in ("I0", "I1"))

    req_pin = {c: c_inputs(c)[0] for c in stops if RE_LINK_C.search(c) and c_inputs(c)[0]}

    def hs_sources(pin):                              # the handshake nodes (storage, not a latch) driving `pin`
        return sorted(s for s in T.starts_reaching(back, pin, stops)
                      if s in stops and not T.RE_BD_LATCH.search(T.pin_split(s)[0]))

    def out_arc(pin, worst):                          # a latch pin's cell arc to its own output
        ws = [w for d, w in edges.get(pin, ()) if T.is_output(d) and T.pin_split(d)[0] == T.pin_split(pin)[0]]
        return (max(ws) if worst else min(ws)) if ws else 0

    def site(parent, head, tail, links):              # one operator's A'j row (or its "j" row)
        own = set(links)
        inside = [p for p in edges if T.is_output(p) and T.pin_split(p)[0].startswith(parent + ".")]
        downstream = T.downstream_of(edges, stops, parent, tail)     # inside the cell (BD_PEERS_CELL; tighten.py)
        upstream = {p for p in inside if head in T.reaches(edges, p, stops)}
        peers = sorted(p for p in inside if T.pin_split(p)[0] not in own and p not in downstream and p not in upstream
                       and not T.pin_split(p)[0].startswith(parent + ".ujoin."))
        if T.PEERS_CELL:
            # a peer the request reaches only through its consumer's acknowledge (rule_a_from_link): the walks below
            # are unconfined and would time its data through the request itself; this cell keeps its A' row
            full = T.reaches(edges, tail, stops)
            envd = sum(1 for p in peers if p in full)
            if envd:
                return {"rule": "j", "margin": aprime[parent], "knob": None, "sized": False,
                        "text": "%s joined: not applied, keeps A': its request reaches %d of its data outputs through its"
                                " consumer's acknowledge (BD_PEERS_CELL)" % (parent, envd)}
        # the data's forward cone, to every storage input it reaches; a select pin ends the cone at its gate
        caps, odd = {}, set()
        bench = {"clocked": 0, "ownjoin": 0}          # CA_BENCHCAP: the sinks it reclassified (reported in the row)
        entry = {}                                    # CA_BENCHCAP: clock bit -> the request's entry pins on that clock

        def entries(clk):                             # flop inputs on clock `clk` the operator's request tail reaches
            if clk not in entry:
                entry[clk] = sorted(q for q in T.reaches(edges, tail, stops) if not T.is_output(q)
                                    and clk_of.get(T.pin_split(q)[0]) == clk)
            return entry[clk]
        seen, work = set(peers), list(peers)
        while work:
            p = work.pop()
            for d, _ in edges.get(p, ()):
                if d in seen:
                    continue
                seen.add(d)
                if d in sel_req:
                    caps[d] = (sel_req[d][0], "select", sel_req[d][1])
                    continue
                if not T.is_output(d) and not edges.get(d):
                    # no arc on: a pin its LUT / carry / mux ignores (pruned or never timed: no path), or an input of
                    # a cell that is not combinational (an FF's D, the PS7, an IO): a sink this rule cannot time
                    inst = T.pin_split(d)[0]
                    if BENCHCAP and inst in clk_of and T.pin_split(d)[1] in ("D", "CE") and entries(clk_of[inst]):
                        caps[d] = (entries(clk_of[inst]), "clocked", inst)     # sampled by the bench's clock
                        bench["clocked"] += 1
                        continue
                    if celltype.get(inst) not in ("SLICE_LUTX", "CARRY4", "SELMUX2_1"):
                        odd.add(d)
                    continue
                if not T.is_output(d) and any(o in stops for o, _ in edges.get(d, ())):
                    inst = T.pin_split(d)[0]
                    if T.RE_BD_LATCH.search(inst) and en_of.get(inst) and d not in en_of[inst]:
                        caps[d] = (sorted(en_of[inst]), "latch", inst)
                    elif BENCHCAP and BENCHCAP_OWNJOIN and inst.startswith(parent + ".") and any(
                            o in stops and head in T.reaches(edges, o, stops) for o, _ in edges.get(d, ())):
                        bench["ownjoin"] += 1                     # the operator's own join: its request, not data
                    else:
                        odd.add(d)
                    continue
                if d not in stops:
                    work.append(d)
        bnd = T.cell_boundary(edges, back, stops, parent)
        ups = set(T.upstream_bd_links(bnd))
        if os.environ.get("CA_ODD_LINKS") != "0":
            ups |= {mm.group(1) for q in bnd for mm in [re.match(r"^(.*?)\.lat\.odd\.u$", T.pin_split(q)[0])] if mm}
        srcs = [c for link in sorted(ups) for c in (link + ".ctl.u.u/O6", link + ".ctl.ub/O6") if c in stops]
        reach_tail = T.reaches(edges, tail, stops)
        rs = sorted(q for q in reach_tail if q in stops)
        J = rs[0] if len(rs) == 1 and rs[0] in and_nodes else None
        worst, notes = None, []
        for S in srcs:
            lo, _ = wk(S, True)
            dat = {p: r for p in caps for r in [at(lo, p, 3)] if r}
            if not dat:
                continue
            # the join credit: J's inputs this launch does not reach, at their earliest arrival relative to S
            floor, ctext, l_cred = {}, "", 0
            if J is not None:
                rq, ck = c_inputs(S)
                anc = hs_sources(rq) if rq else []
                ack = hs_sources(ck) if ck else []
                for ip, arc in binc.get(J, ()):
                    if (J, ip) in feed or ip in reach_tail or not anc or not ack:
                        continue
                    cands, ok = [], True
                    for L0 in anc + ack:
                        e2, e2p = wk(L0, False, None, L0 in anc)    # an ack launch enters the sibling by its c_next
                        ri, rS = at(e2, ip), at(wk(L0, True)[0], S)
                        # a credit path is the sibling's own handshake, not a lap: from L0 it crosses at most one link
                        # C node (the sibling's source, entered by its request or its acknowledge) and otherwise only
                        # C-tree joins, never a latch, never S; and S is reached from L0 directly (no crossing)
                        pp = path(e2p, ri[1], ip) if ri else []
                        ps = [n for n in pp if n in stops and n != L0]
                        # ... and that link C node is entered by its request (I0) from a forward ancestor, by its
                        # acknowledge (I1) from an acknowledge source: the pairing of transitions the bound assumes
                        lc = [i for i, n in enumerate(pp) if RE_LINK_C.search(n) and n != L0]
                        if ri is None or rS is None or rS[1] != 0 or S in ps or \
                                any(n not in and_nodes and not RE_LINK_C.search(n) for n in ps) or \
                                len(lc) > 1 or (lc and (lc[0] == 0 or pp[lc[0] - 1] != c_inputs(pp[lc[0]])[
                                    0 if L0 in anc else 1])):
                            ok = False
                            break
                        cands.append((ri[0] - rS[0], L0, ri[1], " > ".join(short(n) for n in ps), rS[0]))
                    if ok and cands:
                        c = min(cands)
                        if c[0] + arc > floor.get(J, -math.inf):
                            floor[J] = c[0] + arc
                            l_cred = c[4]
                            sib = sorted(short(q) for q in srcs_of.get(ip, ()))
                            ctext = "join %s: sibling from %s credited %+d ps (worst of %d launches: %s > %s)" % (
                                short(J), ",".join(sib[:2]), c[0], len(cands), short(c[1]), c[3])
            ea, eap = wk(S, False)
            ef, efp = wk(S, False, floor) if floor else (ea, eap)
            for p, (t_d, k_d) in sorted(dat.items()):
                evs, kind, label = caps[p]
                a_d = out_arc(p, True) if kind == "latch" else 0     # data compared at the latch output (D -> Q)
                res = {}
                for tag, tabs, preds in (("cred", ef, efp), ("own", ea, eap)):
                    best = None
                    for e in evs:                                    # the enable (EN -> Q) / the gate's request
                        r = at(tabs, e)
                        if r is not None:
                            a_e = out_arc(e, False) if kind == "latch" else 0
                            if kind == "clocked":            # CA_BENCHCAP: the bench samples >= this after entry
                                a_e = BENCHCAP_PS
                            if best is None or r[0] + a_e < best[0]:
                                best = (r[0] + a_e, r[1], e)
                    pe = path(preds, best[1], best[2]) if best else []
                    if best is None or tail not in pe:      # no capture event, or not one this cell's request leads to
                        res = None
                        break
                    res[tag] = (best, pe)
                if res is None:
                    odd.add(p)
                    continue
                # guard: without a binding credit this is A' moved to the capture, with A''s guard (the data leg); when
                # the credit binds the capture leg runs through another cell's request, so both legs are guarded (as
                # rule E's 0.97 / 1.03), and the credit's l(L0 -> S) leg twice (s fast, l slow)
                (t_e, k_e, e), pe = res["cred"]
                t_o = res["own"][0][0]
                g_o = T.req_guard(None, t_d + a_d)
                g = T.req_guard(None, t_d + a_d + t_e + 2 * l_cred) if t_e > t_o else g_o
                m = t_e - (t_d + a_d) - g
                m_own = t_o - (t_d + a_d) - g_o
                if worst is None or m < worst[0]:
                    worst = [m, g, S, p, t_d + a_d, k_d, e, t_e, k_e, kind, label,
                             stops_on(path(wk(S, True)[1], k_d, p)), stops_on(pe), ctext, m_own]
        def btext():                                  # CA_BENCHCAP: what it reclassified here (unset: nothing)
            if not (bench["clocked"] or bench["ownjoin"]):
                return ""
            return "  [bench: %d clocked capture(s), event = request's entry into the clock domain + %d ps; " \
                   "%d own-join input(s), not data]" % (bench["clocked"], BENCHCAP_PS, bench["ownjoin"])
        if odd or worst is None:
            why = ("its data reaches %d input(s) that are not a latch's data or a select (%s)"
                   % (len(odd), ", ".join(sorted(short(q) + "/" + q.rsplit("/", 1)[1] for q in odd)[:3]))
                   if odd else "no capture of its data from its upstream links (%d capture pin(s) in its cone, "
                   "none reached from %s within 2 crossings)" % (len(caps), ", ".join(short(x) for x in srcs) or "-"))
            return {"rule": "j", "margin": aprime[parent], "knob": None, "sized": False,
                    "text": "%s joined: not applied, keeps A': %s%s" % (parent, why, btext())}
        m, g, S, p, t_d, k_d, e, t_e, k_e, kind, label, dpath, cpath, ctext, m_own = worst
        return {"rule": "A", "margin": int(m), "sized": True,
                "knob": parent if (not ctext or m_own == m) else None,
                "text": "%s %d links joined: %d capture(s); worst %s %s  launch %s: data %d (%dx: %s) at %s  "
                        "capture %d (%dx: %s) at %s%s  guard %d  margin %d  (own-request bound %d)%s"
                        % (parent, len(links), len(caps), kind, short(label), short(S), t_d, k_d, dpath,
                           short(p) + "/" + p.rsplit("/", 1)[1], t_e, k_e, cpath,
                           short(e) + "/" + e.rsplit("/", 1)[1], ("  [" + ctext + "]") if ctext else "",
                           g, m, m_own, btext())}
    out = {}
    for parent, head, tail, links in T.request_sites(edges, back, chains):
        if parent not in aprime:
            continue
        r = _per_site("A'j", (edges, stops, back, skew), site, parent, head, tail, links, aprime[parent])
        if r is not None:
            out[parent] = r
    return out


_JCELLS = {}


def _routed_cells(jpath):
    """The routed JSON's cells (read-only here).  CA_FAST: read once per process."""
    if FAST and str(jpath) in _JCELLS:
        return _JCELLS[str(jpath)]
    cells = list(json.load(open(jpath))["modules"].values())[0]["cells"]
    if FAST:
        _JCELLS[str(jpath)] = cells
    return cells


def parse_logs(out, f_rows, T):
    """-> {key: {rule, margin, text, knob}} ; margin is the GUARDED margin each audit gates on."""
    cons = {}

    def put(key, d):
        k, i = key, 2
        while k in cons:
            k, i = "%s #%d" % (key, i), i + 1
        cons[k] = d
    sec = None
    lines = out["tighten_log"].splitlines()
    for i, ln in enumerate(lines):
        m = re.match(r"^([A-Z])\. ", ln)
        if m:
            sec = m.group(1)
            continue
        if sec is None or sec == "F" or not ln.startswith("  "):
            continue
        mm = re.search(r"margin\s+(-?\d+)", ln)
        if not mm:
            continue
        label = ln.split()[0].rstrip(":")
        d = {"rule": sec, "margin": int(mm.group(1)), "text": ln.strip(), "knob": None}
        if sec == "A":
            d["knob"] = label
        elif sec == "H":
            d["knob"] = T.ack_knob(None, label)
        elif sec == "I" and i + 1 < len(lines):
            mf = re.search(r"from (\S+), latest bit", lines[i + 1])
            if mf:
                k = T.stage_delay_knob(mf.group(1) + "/O6", label + "/O6")
                d["knob"] = k[0] if k else None
                d["text"] += "  [from %s]" % mf.group(1)
        put("%s %s" % (sec, label), d)
    for base, n, t_flush, t_reuse, guard, margin in f_rows:
        if margin is None:
            continue
        put("F %s" % base, {"rule": "F", "margin": int(margin), "knob": None,
                            "text": "%s %d links flushed %d reusable %d guard %d margin %d"
                                    % (base, n, t_flush, t_reuse, guard, margin)})
    # rule E, verbose blocks
    blk = None
    for ln in out["skew_log"].splitlines() + [""]:
        m = re.match(r"^  (VIOLATED|SLACK   |ok      ) (\S+) (\S+)$", ln)
        if m or (blk and not ln.strip()):
            if blk and "rp" in blk and "g" in blk:
                put("E %s" % blk["rp"], {"rule": "E", "margin": blk["g"], "raw": blk["raw"], "knob": blk.get("knob"),
                                         "text": "%s %s req %s %d ps (%d x) sel %s %d ps (%d x) launch %s tc %d "
                                                 "raw %+d guarded %+d" % (
                                                     blk["kind"], blk["parent"], blk["rp"], blk["tr"], blk["kr"],
                                                     blk["sp"], blk["ts"], blk["ks"], blk["launch"], blk["tc"],
                                                     blk["raw"], blk["g"])})
            blk = {"kind": m.group(2), "parent": m.group(3)} if m else None
            continue
        if blk is None:
            continue
        s = ln.strip()
        if s.startswith("launch "):
            blk["launch"] = s.split()[1]
        elif s.startswith("divergence point"):
            blk["tc"] = int(s.split()[2])
        elif s.startswith("req "):
            blk["rp"] = s.split()[1]
        elif s.startswith("sel "):
            blk["sp"] = s.split()[1]
        elif s.startswith("earliest"):
            blk["tr"], blk["kr"] = int(s.split()[1]), int(s.split()[3])
        elif s.startswith("latest"):
            blk["ts"], blk["ks"] = int(s.split()[1]), int(s.split()[3])
        elif s.startswith("margin "):
            mm = re.match(r"margin ([+-]\d+) ps raw, ([+-]\d+) ps guarded", s)
            blk["raw"], blk["g"] = int(mm.group(1)), int(mm.group(2))
        elif s.startswith("fix:"):
            blk["knob"] = re.search(r" on (\S+) \(", s).group(1)
    for ln in out["arb_log"].splitlines():
        m = re.match(r"^  (?:ok      |VIOLATED) (\S+) client (\d+):.*guarded ([+-]\d+)", ln)
        if m:
            put("J %s c%s" % (m.group(1), m.group(2)),
                {"rule": "J", "margin": int(m.group(3)), "knob": None, "text": ln.strip()})
    return cons


def chain_geometry(T, sdf):
    """Per chain base: links, rise-path delay D through the chain's own arcs, link-to-link steps, LUT arcs."""
    edges, _, _, _ = T.parse_sdf(pathlib.Path(sdf))
    chains = T.find_chains(edges)
    back = collections.defaultdict(list)
    for s, lst in edges.items():
        for d, w in lst:
            back[d].append((s, w))
    lut = collections.defaultdict(dict)      # inst -> {in pin: arc}
    for s, lst in edges.items():
        si = T.pin_split(s)[0]
        if RE_LINK.match(si) and not T.is_output(s):
            for d, w in lst:
                if T.pin_split(d)[0] == si and T.is_output(d):
                    lut[si][s] = min(lut[si].get(s, 10 ** 9), w)
    # a line trimmed after routing (research/tools/auto/trim_lines.py) starts at its entry stage, the one whose INIT
    # passes its side input: the stages before it are placed but out of the line
    entry = {}
    jpath = pathlib.Path(sdf).with_name(pathlib.Path(sdf).stem + "_routed.json")
    if jpath.exists():
        for n, c in _routed_cells(jpath).items():
            m = RE_LINK.match(n)
            if m and c.get("parameters", {}).get("INIT") == "1100" and \
                    c.get("attributes", {}).get("X_ORIG_TYPE") == "LUT2":
                entry[m.group("base")] = max(entry.get(m.group("base"), 0), int(m.group("i")))
    geo = {}
    for base, links in chains.items():
        links = links[entry.get(base, 0):]
        arr, prev, steps, ok = None, None, [], True
        for i, inst in enumerate(links):
            best, bstep = None, None
            for p, la in lut.get(inst, {}).items():
                for s, w in back.get(p, ()):
                    si = T.pin_split(s)[0]
                    if i == 0:
                        if RE_LINK.match(si) and RE_LINK.match(si).group("base") == base or T.is_const(s):
                            continue
                        v = la
                    else:
                        if si != prev:
                            continue
                        v = arr + w + la
                        bstep = w + la if bstep is None else min(bstep, w + la)
                    best = v if best is None else min(best, v)
            if best is None:
                ok = False
                break
            arr, prev = best, inst
            if i:
                steps.append(bstep)
        geo[base] = {"n": len(links), "D": arr if ok else None, "steps": steps if ok else [],
                     "luts": sorted(v for inst in links for v in lut.get(inst, {}).values())}
    return geo


# ============================================================== driver

POOL = []       # CA_FAST: [ca_fast.Pool], once the base run has been made in this process


def run_worker(sdf, spec, log=None):
    if POOL:
        out = POOL[0].run(lambda s: worker(sdf, s), [spec])[0]
    elif FAST and spec.get("chains") and not (spec.get("cut") or spec.get("drop") or spec.get("osc")):
        # CA_FAST: the base run, in this process: every later run is a fork of it (ca_fast.Pool)
        import ca_fast
        out = json.loads(json.dumps(worker(sdf, spec)))
        BASE_ARB[:] = [out["arb_rc"], out["arb_log"]]
        POOL.append(ca_fast.Pool())
    else:
        r = subprocess.run([sys.executable, __file__, "--_worker", str(sdf), json.dumps(spec)],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        if r.returncode != 0:
            sys.exit("corner_audit: worker failed:\n" + r.stderr[-3000:])
        out = json.loads(r.stdout)
    if log:
        for k, name in (("tighten_log", "tighten.log"), ("skew_log", "skew.log"), ("arb_log", "arb_fork.log")):
            if k in out:
                (log / name).write_text(out[k])
    return out


def knob_of_base(base, last_stage):
    # a memory's lines sit inside its port module (<inst>_uport.umemK.usetup / .uco, <inst>_uport.uhold) but emit.py names
    # their parameters after the mem_controller (DELAY_<INST>_UMEMK_USETUP ...): without this the rule never sized them
    # ("WARNING chain(s) ... map to ..._UPORT_UMEM0_UCO, which sizes.vh does not set"), and gather's bd_mem lines stayed
    # at the automatic start's 3 / 4 elements and returned x (suitew, 2026-11-18)
    m = re.match(r"^(.*)_uport\.(.*)$", base)
    if m:
        base = m.group(1) + "." + m.group(2)
    m = re.match(r"^(.*)\.udly_s$", base)          # BDC_SPEC_INC's short line: sizes key <INST>_SHORT
    if m:
        return m.group(1) + "_short"
    m = re.match(r"^(.*)\.udly$", base)
    if m:
        return m.group(1)
    m = re.match(r"^(.*?)(?:\.(?:one|many\.stage\[\d+\])\.u)?\.uack$", base)
    if m:
        return m.group(1) + ".uack"
    m = re.match(r"^(.*)\.many\.stage\[(\d+)\]\.u\.rdly$", base)
    if m:
        return m.group(1) if int(m.group(2)) == last_stage.get(m.group(1), -1) else m.group(1) + ".sdelay"
    m = re.match(r"^(.*?)(?:\.one\.u)?\.rdly$", base)
    if m:
        return m.group(1)
    return base


MPFX = "BD_SZ_UUT_"     # macro prefix of the kernel's lines; --prefix sets it


def macro(path):
    return "BD_SZ_" + re.sub(r"[^A-Za-z0-9]", "_", path).upper()


def read_sizes(path):
    sizes, order = {}, []
    for ln in open(path):
        m = re.match(r"`define\s+(\S+)\s+(\d+)", ln)
        if m:
            sizes[m.group(1)] = int(m.group(2))
            order.append(m.group(1))
    return sizes, order


def select_path_macros(route_dir, macros):
    """sizes.vh macros guarding a select path: every BD_SZ_UUT_UMUX<n>, and the DELAY/SDELAY of every link on a channel
    bdc reads as a select (emit.select_channels on the route's input.mlir, which bdc/fusion_bench.py copies next to the
    seedN/ dirs).  No input.mlir -> the mux delays only, with a warning."""
    out = {m for m in macros if re.fullmatch(MPFX + r"UMUX\d+", m)}
    mlir = pathlib.Path(route_dir).resolve().parent / "input.mlir"
    if not mlir.exists():
        print("corner_audit: no %s; protecting the mux delays only" % mlir, file=sys.stderr)
        return out
    sys.path.insert(0, str(REPO / "bdc"))
    import emit
    from hs import parse
    f = [f for f in parse.parse_module(mlir.read_text(), filename=str(mlir)) if not f.is_declaration][0]
    e = emit.Emitter(f)
    for v in e.selects:
        if v in e.linked:
            base = MPFX + "ULINK_" + emit.vname(v).upper()
            out |= {m for m in macros if m in (base, base + "_SDELAY")}
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("route_dir", type=pathlib.Path)
    ap.add_argument("--out", type=pathlib.Path)
    ap.add_argument("--guard-lo", type=float, default=0.97)
    ap.add_argument("--guard-hi", type=float, default=1.03)
    ap.add_argument("--a-frac", type=float, default=0.03)
    ap.add_argument("--a-min", type=int, default=50)
    ap.add_argument("--band", type=float, default=None, help="LUT / wire band (default 0.288; 0.21 with CA_SIZERULE=1)")
    ap.add_argument("--cell", default="CARRY4=1,SELMUX2_1=1,SLICE_FFX=1")
    ap.add_argument("--inst-rx", action="append", default=None)
    ap.add_argument("--fast-min", action="store_true", help="band 0, no cell or instance overrides")
    ap.add_argument("--uniform", type=float, default=None,
                    help="every arc at this band, no cell or instance overrides (0.288 = the calibrated nominal)")
    ap.add_argument("--floor", type=int, default=1)
    ap.add_argument("--slack", type=int, default=0, help="every sized constraint must keep >= this many ps")
    ap.add_argument("--all-lines", action="store_true", help="also resize the harness's lines (upipe, uspin)")
    ap.add_argument("--shrink-selects", action="store_true",
                    help="allow shortening mux delays and select-channel links (unsafe: see the docstring)")
    ap.add_argument("--no-size", action="store_true", help="report only")
    ap.add_argument("--cut", action="append", default=[],
                    help="case analysis: drop every SDF arc whose 'src -> dst' matches this regex (repeatable)")
    ap.add_argument("--drop-inst", action="append", default=[],
                    help="case analysis: remove every instance whose name matches this regex, with its arcs (repeatable)")
    ap.add_argument("--osc", action="append", default=[],
                    help="passed to tighten.py: an instance prefix that is a ring oscillator (gcd_hw's rig: dhk, invhk)")
    ap.add_argument("--prefix", default="uut.",
                    help="the kernel's instance path in the top (soak: uut.; the kernel bench top: bridge_i.udut.)")
    ap.add_argument("--max-iter", type=int, default=30)
    ap.add_argument("--rule-a-tighten", action="store_true",
                    help="size on tighten.py's rule A even where it pairs as a bundled channel (no A' re-measure)")
    ap.add_argument("--keep-const-launch", action="store_true",
                    help="rule A exactly as tighten.py: constant drivers may launch the data path")
    a = ap.parse_args()
    global MPFX
    MPFX = macro(a.prefix)
    if a.band is None:
        a.band = 0.21 if SIZERULE else 0.288
    if a.inst_rx is None:
        a.inst_rx = [] if SIZERULE else [r"\.chain\.g\[\d+\]\.u$:0.21"]
    if SIZERULE:
        a.shrink_selects = True
    if a.fast_min:
        a.band, a.cell, a.inst_rx = 0.0, "", []
    if a.uniform is not None:
        a.band, a.cell, a.inst_rx = a.uniform, "", []
    rd = a.route_dir.resolve()
    pnr = rd / "pnr" if (rd / "pnr").is_dir() else rd
    for f in ("soak_xray.sdf", "soak_routed.json", "sizes.vh"):
        if not (pnr / f).exists():
            sys.exit("corner_audit: no %s in %s" % (f, pnr))
    corner = "fastmin" if a.fast_min else "b%g_c%s_i%s" % (a.band, "1" if a.cell else "0",
                                                            "+".join(s.rpartition(":")[2] for s in a.inst_rx) or "0")
    out = a.out or SCRATCH / ("%s__%s__%s" % (rd.parent.name, rd.name, corner))
    out.mkdir(parents=True, exist_ok=True)
    sys.path.insert(0, str(HERE))
    import corner_sdf
    cargs = [str(pnr / "soak_xray.sdf"), str(pnr / "soak_routed.json"), str(out / "soak.sdf"), "--band", str(a.band)]
    if a.cell:
        cargs += ["--cell", a.cell]
    for s in a.inst_rx:
        cargs += ["--inst-rx", s]
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        corner_sdf.main(cargs)
    csdf_log = buf.getvalue()
    link = out / "soak_routed.json"
    if link.is_symlink() or link.exists():
        link.unlink()
    link.symlink_to(pnr / "soak_routed.json")
    if (pnr / "toolchain.txt").exists():
        (out / "toolchain.txt").write_text((pnr / "toolchain.txt").read_text())
    sdf = out / "soak.sdf"
    spec = {"a_frac": a.a_frac, "a_min": a.a_min, "glo": a.guard_lo, "ghi": a.guard_hi,
            "drop_const": not a.keep_const_launch, "rule_a_link": not a.rule_a_tighten, "osc": a.osc, "cut": a.cut, "drop": a.drop_inst}
    nominal = lambda rule: a.guard_lo if rule == "E" else 1.0

    base = run_worker(sdf, {**spec, "chains": True, "keep_logs": True}, log=out)
    cons, geo = base["constraints"], base["chains"]

    # ---- delay lines: sizes.vh macros -> chains
    sizes, order = read_sizes(pnr / "sizes.vh")
    cells = list(json.load(open(pnr / "soak_routed.json"))["modules"].values())[0]["cells"]
    last_stage = {}
    for n in cells:
        m = re.match(r"^(.*?)\.many\.stage\[(\d+)\]\.u\.", n)
        if m:
            last_stage[m.group(1)] = max(last_stage.get(m.group(1), -1), int(m.group(2)))
    lines = collections.defaultdict(list)       # macro -> [chain base]
    knob_path = {}
    for b in geo:
        k = knob_of_base(b, last_stage)
        lines[macro(k)].append(b)
        knob_path[macro(k)] = k
    warn = []
    for mac, bases in sorted(lines.items()):
        if mac not in sizes:
            warn.append("chain(s) %s map to %s, which sizes.vh does not set (kept, measured)" % (bases, mac))
            continue
        ns = {geo[b]["n"] for b in bases}
        if ns != {sizes[mac]}:
            warn.append("%s = %d in sizes.vh but its chain(s) have %s links" % (mac, sizes[mac], sorted(ns)))
    for mac, v in sizes.items():
        if v > 0 and mac not in lines:
            warn.append("%s = %d in sizes.vh but no chain of it is in the netlist" % (mac, v))

    # ---- per-link costs at this corner
    all_steps = [s for g in geo.values() for s in g["steps"]]
    all_luts = [v for g in geo.values() for v in g["luts"]]
    c_lo = min(all_steps) if all_steps else None
    lut_lo = min(all_luts) if all_luts else 0
    means = {b: sum(g["steps"]) / len(g["steps"]) for b, g in geo.items() if g["steps"]}
    c_mlo = min((v for b, v in means.items() if len(geo[b]["steps"]) >= 2), default=c_lo)   # CA_SIZERULE only

    def d_of(mac):
        return max((geo[b]["D"] or 0) for b in lines[mac])

    def d_new(b, m):
        g = geo[b]
        n, D = g["n"], g["D"] or 0
        if m == n:
            return D
        if m > n:
            return D + (m - n) * c_lo
        if m == 0:
            return 0
        if SIZERULE:
            c_own = means.get(b, D / n if n else D)
            if SIZERULE_MLO:
                return max(0, min(D - (n - m) * c_own, lut_lo + (m - 1) * c_mlo))
            return max(0, D - (n - m) * c_own)
        c_rm = max(g["steps"]) if g["steps"] else D
        return max(0, min(D - (n - m) * c_rm, lut_lo + (m - 1) * c_lo))

    def delta(mac, m):          # ps the line gives up (shrink, > 0) or adds (pad, < 0), worst chain of the macro
        ds = [(geo[b]["D"] or 0) - d_new(b, m) for b in lines[mac]]
        return max(ds) if m <= sizes[mac] else min(ds)

    # ---- sensitivity: one run per line with its chains zeroed
    sized_lines = [mac for mac in lines if mac in sizes and sizes[mac] > 0
                   and (a.all_lines or mac.startswith(MPFX))]
    measured_lines = [mac for mac in lines if mac in sizes and sizes[mac] > 0]
    protected = set() if a.shrink_selects else select_path_macros(a.route_dir, list(sizes))
    sens = {}                   # mac -> {key: dM}
    sens_macs = [] if a.no_size else sorted(measured_lines)   # --no-size: report only, no per-line sensitivity runs
    # CA_JOBS=N runs the per-line sensitivity workers N at a time (each is a deterministic subprocess, so the results are
    # the same as one at a time; unset = 1, the old sequential order).  The cluster node sets it for the sizing loop.
    ca_jobs = max(1, int(os.environ.get("CA_JOBS", "1") or 1))
    if POOL:                    # CA_FAST: forks of the base run, ca_jobs at a time
        sens_runs = dict(zip(sens_macs, POOL[0].run(
            lambda sp: worker(sdf, sp), [{**spec, "scale": {b: 0.0 for b in lines[mac]}} for mac in sens_macs],
            jobs=ca_jobs)))
    elif ca_jobs > 1 and len(sens_macs) > 1:
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=ca_jobs) as ex:
            sens_runs = dict(zip(sens_macs, ex.map(
                lambda mac: run_worker(sdf, {**spec, "scale": {b: 0.0 for b in lines[mac]}}), sens_macs)))
    else:
        sens_runs = None
    for mac in sens_macs:
        r = sens_runs[mac] if sens_runs is not None else run_worker(sdf, {**spec, "scale": {b: 0.0 for b in lines[mac]}})
        s = {}
        for k, c in cons.items():
            c2 = r["constraints"].get(k)
            if c2 is None:
                s[k] = math.inf          # vanished when the line was removed: depends on it, uncapped
            elif c["margin"] - c2["margin"] > 2:
                s[k] = c["margin"] - c2["margin"]
        sens[mac] = s

    def slope(mac, k):
        D = d_of(mac)
        obs = sens[mac][k] / D if D and sens[mac][k] != math.inf else 0
        return max(nominal(cons[k]["rule"]), obs)

    def drop(mac, k, m):        # worst-case margin lost on k when mac goes to m links (negative = gain, pad)
        dd = delta(mac, m)
        if dd <= 0:             # padding: credit nothing to other constraints
            return 0
        return min(slope(mac, k) * dd, sens[mac][k])

    def kernel_con(k):        # a constraint inside the harness (upipe, uspin) is reported, not sized, unless --all-lines
        return a.all_lines or k.split()[1].startswith(a.prefix)
    sized = [k for k, c in cons.items() if c["rule"] in SIZED_RULES and kernel_con(k)]
    prop = dict(sizes)
    why = {}
    if not a.no_size:
        def total_drop(k, p):
            return sum(drop(mac, k, p[mac]) for mac in sized_lines if k in sens.get(mac, {}) and p[mac] != sizes[mac])

        def pad_target(k):
            c = cons[k]
            cand = [mac for mac in sized_lines if k in sens[mac]]
            want = c.get("knob")
            if want:
                hit = [mac for mac in cand if knob_path[mac] == want or knob_path[mac].endswith("." + want)]
                if hit:
                    return hit[0]
            return max(cand, key=lambda mac: (slope(mac, k), sens[mac][k]), default=None)

        def credit(k, mac, n_from, m):   # conservative gain on k from padding mac n_from -> m
            if sens[mac].get(k, 0) == math.inf:
                gk = nominal(cons[k]["rule"])
            else:
                gk = min(nominal(cons[k]["rule"]), sens[mac][k] / d_of(mac)) if d_of(mac) else 0
            return gk * (m - n_from) * c_lo
        padded = {}
        raised_from = {}

        def fix_negative(p, cur):
            """Pad until every constraint in `cur` {key: margin} is >= slack.  A pad is credited to EVERY constraint
            the line was measured on (at the smaller of the rule's slope and the observed one); verify checks it."""
            gain = collections.Counter()
            changed = False
            for k in sorted(cur, key=lambda k: cur[k]):
                need = a.slack - (cur[k] + gain[k])
                if need <= 0:
                    continue
                mac = pad_target(k)
                if mac is None:
                    why.setdefault("_unfixable", []).append(k)
                    continue
                n0 = p[mac]
                m = n0
                while credit(k, mac, n0, m) < need and m < n0 + 200:
                    m += 1
                if m > n0:
                    p[mac] = m
                    padded[mac] = True
                    raised_from.setdefault(mac, n0)
                    for k2 in sens[mac]:
                        gain[k2] += credit(k2, mac, n0, m)
                    why[mac] = (why[mac] + "; " if why.get(mac, "").startswith(("PAD", "verify")) else "") + \
                        "PAD %d->%d for %s (%+d ps)" % (n0, m, k, -need)
                    changed = True
            return changed, gain

        def verify(p):
            scale = {}
            for mac in sized_lines:
                if p[mac] != sizes[mac]:
                    for b in lines[mac]:
                        D = geo[b]["D"] or 0
                        scale[b] = (d_new(b, p[mac]) / D) if D else 1.0
            ver = run_worker(sdf, {**spec, "scale": scale, "keep_logs": True})
            bad = {k: v["margin"] for k, v in ver["constraints"].items()
                   if v["rule"] in SIZED_RULES and kernel_con(k) and v["margin"] < a.slack}
            return bad, ver

        # 1. constraints already short at this corner: pad
        _, gained = fix_negative(prop, {k: cons[k]["margin"] for k in sized if cons[k]["margin"] < a.slack})
        # 2. greedy shrink, longest line first
        budget = {k: cons[k]["margin"] - a.slack + gained[k] for k in sized}
        for mac in sorted(sized_lines, key=lambda m: -d_of(m)):
            if padded.get(mac):
                continue
            on = [k for k in sens[mac] if k in budget]
            if mac in protected:
                why[mac] = "select path: never shortened (see docstring)"
                continue
            if not on:
                kj = "A'j " + knob_path[mac]
                if JOINAWARE and kj in cons and cons[kj]["rule"] == "A" and prop[mac] > a.floor:
                    # measured free, not unmeasured: its own capture row (A'j) does not move when the line is removed,
                    # i.e. a sibling's request is the capture's last input (the join credit), and nothing else
                    # measured depends on it either
                    prop[mac] = a.floor
                    why[mac] = "A'j: on no measured constraint (another input is the capture's last): floor %d" % a.floor
                    continue
                why[mac] = "on no measured constraint: kept"
                continue
            n = prop[mac]
            best = n
            for m in range(n - 1, a.floor - 1, -1):
                if all(drop(mac, k, m) <= budget[k] for k in on):
                    best = m
                else:
                    break
            for k in on:
                budget[k] -= drop(mac, k, best)
            prop[mac] = best
            bind = min(on, key=lambda k: budget[k])
            why[mac] = ("floor %d" % a.floor if best == a.floor else "bound by %s (%d ps left)" % (bind, budget[bind]))
        if SIZERULE and SIZERULE_FLOOR:      # never below the largest size that failed a draw (+1), per line
            for mac, v in read_sizes(pathlib.Path(SIZERULE_FLOOR))[0].items():
                if mac in prop and prop[mac] < min(v, sizes[mac]) and not padded.get(mac):
                    budget_note = "draw floor %d (was %d)" % (min(v, sizes[mac]), prop[mac])
                    prop[mac] = min(v, sizes[mac])
                    why[mac] = (why.get(mac, "") + "; " if why.get(mac) else "") + budget_note
        # 3. verify on the corner SDF with predicted chain delays, bump what fails
        nver = 0
        for it in range(a.max_iter):
            bad, ver = verify(prop)
            nver += 1
            if not bad:
                break
            changed = False
            pad_need = {}
            for k, mg in bad.items():
                kk = k if k in cons else None
                shr = [mac for mac in sized_lines if prop[mac] < sizes[mac] and kk and kk in sens[mac]]
                if shr:
                    mac = max(shr, key=lambda m: drop(m, kk, prop[m]))
                    raised_from.setdefault(mac, prop[mac])
                    prop[mac] += 1
                    why[mac] = (why.get(mac, "") + "; ") + "verify: +1 for %s" % k
                    changed = True
                elif kk:
                    pad_need[kk] = mg
                else:
                    why.setdefault("_new", []).append(k)
            if pad_need:
                changed |= fix_negative(prop, pad_need)[0]
            if not changed:
                break
        # 4. trim what padding / verify raised: the smallest value that still verifies (bisection, monotone assumed)
        if not bad:
            for mac in sorted(raised_from, key=lambda m: -(prop[m] - raised_from[m])):
                lo, hi = raised_from[mac], prop[mac]       # lo failed (or was short), hi verifies
                while hi - lo > 1:
                    mid = (lo + hi) // 2
                    trial = dict(prop)
                    trial[mac] = mid
                    b2, v2 = verify(trial)
                    nver += 1
                    if b2:
                        lo = mid
                    else:
                        hi, ver = mid, v2
                if hi != prop[mac]:
                    why[mac] += "; trimmed %d->%d by verify" % (prop[mac], hi)
                    prop[mac] = hi
            bad, ver = verify(prop)
            nver += 1
        hist = list(range(nver))
        (out / "verify.txt").write_text(
            "verify: corner SDF, every changed line's chain arcs scaled to its predicted delay\n"
            "iterations %d, sized constraints below slack %d after the last\n\n" % (len(hist), len(bad))
            + "\n".join("%-8s %-70s %+6d" % (v["rule"], k[:70], v["margin"])
                        for k, v in sorted(ver["constraints"].items(), key=lambda kv: kv[1]["margin"]))
            + "\n\n" + ver["tighten_log"] + "\n" + ver["skew_log"])
        vcons = ver["constraints"]
    else:
        vcons, bad = {}, {}

    # negative_sized.tsv (a new file; every other output is unchanged): each sized kernel constraint below --slack on this
    # route AS BUILT, and whether the proposal could pad a line for it.  research/tools/auto/auto_size.sh's convergence
    # test: a route is clean under the rule when this file has no rows.
    unf = set(why.get("_unfixable", [])) if not a.no_size else set()
    with open(out / "negative_sized.tsv", "w") as f:
        f.write("rule\tmargin\tkey\tfix\n")
        for k, c in sorted(cons.items(), key=lambda kv: kv[1]["margin"]):
            if c["rule"] in SIZED_RULES and kernel_con(k) and c["margin"] < a.slack:
                f.write("%s\t%d\t%s\t%s\n" % (c["rule"], c["margin"], k, "unfixable" if k in unf else "line"))

    # ---- outputs
    rep = []
    rep.append("corner_audit %s" % rd)
    rep.append("  corner: %s" % csdf_log.strip().replace("\n", "\n          "))
    tc = (pnr / "toolchain.txt").read_text().splitlines()[0] if (pnr / "toolchain.txt").exists() else "UNSTAMPED"
    rep.append("  nextpnr: %s" % tc)
    rep.append("  guards: rule E/J %.3f*req vs %.3f*sel; rule A/F/H/I/K/L guard max(%.3f*t_data, %d ps); slack %d"
               % (a.guard_lo, a.guard_hi, a.a_frac, a.a_min, a.slack))
    rep.append("  rule A data launches from constant drivers: %s" % ("kept (tighten.py as is)" if a.keep_const_launch
                                                                   else "DROPPED (a constant never transitions)"))
    if os.environ.get("BD_PEERS_CELL") == "0":         # the default (on) prints nothing: its reports are unchanged
        rep.append("  rule A peers: BD_PEERS_CELL=0, the OLD test: a request's downstream followed outside its cell "
                   "(hid test_divui's divider behind its consumer's acknowledge)")
    rep.append("  audits exit: tighten %s, skew %s, arb_fork %s" % (base["tighten_rc"], base["skew_rc"], base["arb_rc"]))
    rep.append("  per-link cost at this corner: c_lo %s ps (cheapest link-to-link step on the route), lut_lo %d ps; "
               "chain mean steps %s-%s ps" % (c_lo, lut_lo, int(min(means.values())) if means else "-",
                                               int(max(means.values())) if means else "-"))
    if SIZERULE:
        rep.append("  sizing rule: CA_SIZERULE=1 (sizerule1): chains and LUT/wire at one band %g, CARRY4/F7F8/FF at --cell; "
                   "shortened lines priced at own mean step%s; selects sized by E/M; floor file %s"
                   % (a.band, (", capped by lowest chain mean c_mlo %s ps" % (int(c_mlo) if c_mlo else "-")) if SIZERULE_MLO
                      else "", SIZERULE_FLOOR or "none"))
    if os.environ.get("BD_SKEW_STEER_SELF") == "1":   # rule E's --steer-self (cells/verify/skew.py (5)); unset: no line
        rep.append("  rule E: BD_SKEW_STEER_SELF=1: a latch launch at a select gate whose request C-element carries the "
                   "select's own channel request is bounded by that request (research/data/sizerule/steerE.md)")
    if os.environ.get("BD_SKEW_MUXN") == "1":         # rule E's --muxn (cells/verify/skew.py); unset: no line
        rep.append("  rule E: BD_SKEW_MUXN=1: every bdc_muxnN's select decode sel[k] = ctl_req & (s == k) is a select "
                   "gate too (its ctl_req pin against each index pin; tighten.py muxn_decode_sites(); "
                   "research/data/muxsel/)")
    if JOINAWARE:
        nj = sum(1 for k, c in cons.items() if k.startswith("A'j ") and c["rule"] == "A")
        rep.append("  join-aware: CA_JOINAWARE=1: %d operator(s) sized at their data's captures (A'j: latch data vs its "
                   "enable, select vs its gate's request; C-elements wait for their last input; join credit), their "
                   "A' rows reported as 'a'; %d kept on A' (rows 'j' say why)"
                   % (nj, sum(1 for k, c in cons.items() if k.startswith("A'j ") and c["rule"] == "j")))
    if BENCHCAP:                                       # unset: no line
        rep.append("  bench capture: CA_BENCHCAP=1: in A'j, a D / CE pin of a flip-flop on a BUFG clock is captured by "
                   "that clock >= %d ps after the operator's request first reaches a flop on it (gen_bench.py's 2-flop "
                   "synchronisers at <= 100 MHz, less 1 ns); an input of the operator's own join is not data%s"
                   % (BENCHCAP_PS, "" if BENCHCAP_OWNJOIN else " -- OFF (CA_BENCHCAP_OWNJOIN=0)"))
    for w in warn:
        rep.append("  WARNING " + w)
    neg = sorted((c["margin"], k) for k, c in cons.items() if c["margin"] < 0)
    rep.append("")
    rep.append("NEGATIVE at this corner (%d; rule D is a screen, listed but not gated):" % len(neg))
    for mg, k in neg:
        rep.append("  %-5s %+6d  %s" % (cons[k]["rule"], mg, cons[k]["text"]))
    rep.append("")
    rep.append("every constraint, worst first (margin = guarded margin each audit gates on), and the lines it depends on")
    for k, c in sorted(cons.items(), key=lambda kv: kv[1]["margin"]):
        deps = ", ".join("%s(-%s)" % (mac.replace("BD_SZ_", ""), "all" if sens[mac][k] == math.inf else sens[mac][k])
                         for mac in sorted(sens) if k in sens[mac])
        rep.append("  %-2s %+6d  %s%s" % (c["rule"], c["margin"], c["text"],
                                         ("\n             depends on: " + deps) if deps else ""))
    gaps = [l.strip() for l in base["tighten_log"].splitlines() if "not audited" in l]
    gaps += [l.strip() for l in base["skew_log"].splitlines() if "not checked" in l or "no knob" in l]
    if gaps:
        rep.append("")
        rep.append("gaps the audits report (not measured, not a pass):")
        rep += ["  " + g for g in gaps]
    (out / "report.txt").write_text("\n".join(rep) + "\n")

    tsv = ["macro\tsize\tproposed\tD_ps\tD_new_ps\tc_rm_ps\tconstraints\twhy"]
    for mac in sorted(lines, key=lambda m: -d_of(m) if m in sizes else 0):
        if mac not in sizes:
            continue
        bs = lines[mac]
        c_rm = max((max(geo[b]["steps"]) for b in bs if geo[b]["steps"]), default=0)
        tsv.append("%s\t%d\t%d\t%d\t%d\t%d\t%d\t%s" % (
            mac, sizes[mac], prop[mac], d_of(mac), max(d_new(b, prop[mac]) for b in bs) if sizes[mac] else 0,
            c_rm, len(sens.get(mac, {})),
            why.get(mac, "harness line: measured, kept" if mac not in sized_lines and sizes[mac] else "")))
    (out / "lines.tsv").write_text("\n".join(tsv) + "\n")
    hdr = ("// corner_audit.py %s: per-line proposal at corner %s, guards lo %.3f hi %.3f, rule-A guard max(%.3f*t, %d), "
           "slack %d, floor %d; c_lo %s ps. ONE route: re-route and run the full stack before using it.\n"
           % (rd, corner, a.guard_lo, a.guard_hi, a.a_frac, a.a_min, a.slack, a.floor, c_lo))
    if SIZERULE:
        hdr += "// CA_SIZERULE=1 (sizerule1, research/data/sizerule/README.md): c_mlo %s ps, floor file %s\n" % (
            int(c_mlo) if c_mlo else "-", SIZERULE_FLOOR or "none")
    with open(out / "sizes.vh", "w") as f:
        f.write(hdr)
        for mac in order:
            f.write("`define %s %d%s\n" % (mac, prop[mac], "" if prop[mac] == sizes[mac]
                                            else "   // was %d" % sizes[mac]))

    # ---- stdout summary
    print("\n".join(rep[:rep.index("")]))
    print("negative at this corner: %d" % len(neg))
    for mg, k in neg:
        print("  %-2s %+6d  %s" % (cons[k]["rule"], mg, cons[k]["text"][:150]))
        deps = [mac for mac in sens if k in sens[mac]]
        if deps:
            print("            depends on: %s" % ", ".join(sorted(d.replace("BD_SZ_", "") for d in deps)))
    if not a.no_size:
        ch = [(mac, sizes[mac], prop[mac]) for mac in order if prop[mac] != sizes[mac]]
        tot0 = sum(sizes[m] for m in sized_lines)
        tot1 = sum(prop[m] for m in sized_lines)
        print("proposal: %d line(s) changed, kernel links %d -> %d; verify: %d sized constraint(s) below slack"
              % (len(ch), tot0, tot1, len(bad)))
        for mac, n0, n1 in ch:
            print("  %-40s %3d -> %3d   %s" % (mac, n0, n1, why.get(mac, "")))
        if bad:
            for k, mg in sorted(bad.items(), key=lambda kv: kv[1]):
                print("  STILL SHORT %+6d %s" % (mg, k))
    print("wrote %s/{report.txt, lines.tsv, sizes.vh, verify.txt, soak.sdf}" % out)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--_worker":
        sdf, spec = sys.argv[2], json.loads(sys.argv[3])
        res = worker(sdf, spec)
        sys.stdout = sys.__stdout__
        print(json.dumps(res))
    else:
        main()
