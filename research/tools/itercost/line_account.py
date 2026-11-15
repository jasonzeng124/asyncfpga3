#!/usr/bin/env python3
"""line_account.py CA_OUT --graph GRAPHDIR [options] -- PROGRAM.md "Second lead: account for every delay on collatz's
loop".  For every matched delay line (bd_delay chain) on a kernel's loop, at ONE corner of ONE route:

  * size (elements) and routed rise delay through the chain at the corner, and its per-element cost;
  * the constraint that sets its length: rule, launch, capture, guarded margin;
  * that constraint's data path, split into logic (LUT / CARRY4 / F7-F8 cell arcs), latch (a link's en->Q arc),
    enable wire (controller -> latch enable pin), other wire (INTERCONNECT), controller / C-element arcs;
    and the spread of the enable net over the latch bits of the link the path crosses;
  * the request path: what the request crosses besides the line (wire, join, OR), the guard applied;
  * n_need = the elements this line needs for margin 0 on that constraint as routed, at this line's own per-element
    cost; n_logic = the elements a line would need if the data path were ONLY its combinational cell arcs (plus the
    rule's guard on that), with NO credit for the request's own path -- what the logic alone asks of a matched delay.
  * flags: a line whose macro sizes.vh does not set (the RTL default is what is built), a select-path line held by
    the withdrawn select rule, an upstream link that carries a CONSTANT (data pins driven by tie-offs only), the
    widest wire on the data path when wire dominates.

    python3 research/tools/itercost/line_account.py /home/user/runs/ca/ceb_24/worst \\
        --graph research/data/eventgraph/graphs/ceb_24 --out OUTDIR
    (CA_OUT is a research/tools/corner_audit.py --out directory: soak.sdf, soak_routed.json, report.txt; the route's
     sizes.vh is read from CA_OUT/../seed1/pnr/sizes.vh unless --sizes is given.)

Writes OUTDIR/lines.tsv, OUTDIR/lines.md (one row per line) and OUTDIR/paths.txt (every traced path, arc by arc).

THE AUDITS ARE NOT RE-IMPLEMENTED.  corner_audit.worker() is called in this process, on the corner SDF corner_audit
wrote, with corner_audit's default spec (residual guards 0.97 / 1.03, rule-A guard max(0.03 t, 50), constant drivers
dropped, A' re-measured); its constraints are the rows used here, and tighten.py / skew.py are then the modules it
loaded and patched.  For the binding constraint of each line the same functions are called again (tighten.check /
check_bundled / Timing walks for A, H, I; skew.walk for A' and E) to get the arrival tables, and the path is read off
them: skew.path_to() for skew's walks (its own predecessor pointers), and for tighten's single-level walks a backtrack
over the table (a predecessor u of v with t[u] + w(u, v) == t[v], never through a storage node other than the start).
Every traced total is compared with the audit's own number; a mismatch is printed in the `check` column, not hidden.

Which lines are "on the loop" comes from the timed event graph (research/tools/eventgraph, whatif.G): the critical
cycle plus every next cycle (whatif.next_cycles) within --within ps of it.  The graph's chain weights are the itercost
run's calibrated bands, not this corner's: they say WHICH lines and how much of the cycle, the corner SDF says why.

What this does not determine: rule H's disturbance path (earliest_disturbance() keeps no path) and rule F's flush are
reported as totals only.  Whether a traced path can actually toggle (false path) is flagged only for the structural
cases above; the per-cell list of logic arcs is in paths.txt for a human to read.
"""
import argparse, collections, contextlib, io, json, math, os, pathlib, re, sys

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parent.parent.parent
TOOLS = REPO / "research" / "tools"
sys.path.insert(0, str(TOOLS))
sys.path.insert(0, str(TOOLS / "eventgraph"))

RE_LINK = re.compile(r"^(?P<base>.+)\.chain\.g\[(?P<i>\d+)\]\.u$")
RE_CELLCHAIN = re.compile(r"^(.+?\.(?:udly|udly_s|rdly|uack|us))\.chain\.g\[\d+\]\.u$")


def inst(pin):
    return pin.rpartition("/")[0]


# ============================================================== audit modules

def load_audit(sdf, and_join):
    """corner_audit.worker() in this process: -> (constraints, chain geometry, T, S)."""
    if and_join:
        os.environ["BD_SKEW_AND_JOIN"] = "1"
    import corner_audit as CA
    spec = {"a_frac": 0.03, "a_min": 50, "glo": 0.97, "ghi": 1.03, "drop_const": True, "rule_a_link": True,
            "osc": [], "cut": [], "drop": [], "chains": True, "keep_logs": True}
    res = CA.worker(str(sdf), spec)
    sys.stdout = sys.__stdout__
    return res, CA, sys.modules["tighten"], sys.modules["skew"]


class Graph:
    """The timing graph exactly as the audits build it (tighten.routed_graph), plus what skew.main adds."""

    def __init__(self, T, S, sdf):
        self.T, self.S = T, S
        self.edges, self.back, self.stops = T.routed_graph(pathlib.Path(sdf))
        _, self.celltype, _, _ = T.parse_sdf(pathlib.Path(sdf))
        if getattr(S, "AND_JOIN", False):
            S.AND_NODES.clear()
            S.AND_NODES.update(o for o in self.stops if S.RE_CTREE_C.search(o))
        self.timing = T.Timing(self.edges, self.stops)
        self.chains = T.find_chains(self.edges)
        self.binc, srcs_of = collections.defaultdict(list), collections.defaultdict(set)
        for s, lst in self.edges.items():
            for d, w in lst:
                self.binc[d].append((s, w))
                srcs_of[d].add(s)
        self.feed = {(o, ip) for o in self.stops for ip, _ in self.binc.get(o, ()) if o in srcs_of[ip]}
        side = T.fastfall_side_arcs(self.edges)
        self.early_edges = {s: [(d, w) for d, w in lst if (s, d) not in side] for s, lst in self.edges.items()}
        self.rev = {}
        for name, E in (("all", self.edges), ("early", self.timing.early_edges), ("fall", self.timing.fall_edges)):
            r = collections.defaultdict(list)
            for s, lst in E.items():
                for d, w in lst:
                    r[d].append((s, w))
            self.rev[name] = r
        self.walks = {}

    def stop_of(self, instance):
        return next((s for s in self.stops if inst(s) == instance), None)

    def swalk(self, launch, longest):
        k = (launch, longest)
        if k not in self.walks:
            self.walks[k] = self.S.walk(self.edges if longest else self.early_edges, self.stops, self.binc,
                                        self.feed, launch, longest)
        return self.walks[k]

    # ---- paths -------------------------------------------------------------------------------------------------
    def backtrack(self, table, rev, start, end):
        """The path a single-level walk table's arrival at `end` came from: [(pin, arrival)], start first."""
        if end not in table:
            return None
        # the launch is expanded once, at 0; a longest walk may later write a larger arrival back onto it (a path
        # that returns to the launch, never expanded again), which is not the value its successors were relaxed from
        t = lambda p: 0 if p == start else table[p]
        path, v, n = [(end, t(end))], end, 0
        while v != start:
            n += 1
            if n > 100000:
                return None
            c = [u for u, w in self.rev[rev].get(v, ()) if u in table and t(u) + w == t(v)
                 and (u == start or u not in self.stops)]
            if not c:
                return None
            v = c[0]
            path.append((v, t(v)))
        return path[::-1]

    def spath(self, tables, level, node):
        """skew.walk tables (out, pred) -> [(pin, arrival)] via skew.path_to."""
        out, pred = tables
        p = self.S.path_to(pred, level, node)
        return None if p is None else [(nd, out[l][nd]) for l, nd in p]

    # ---- classification ----------------------------------------------------------------------------------------
    def kind(self, u, v):
        T = self.T
        iu, iv = inst(u), inst(v)
        if iu != iv:
            if T.RE_BD_LATCH.search(iv) and u in self.stops and not T.RE_BD_LATCH.search(iu):
                return "enable"
            return "wire"
        ct = self.celltype.get(iu, "")
        if RE_LINK.match(iu):
            return "chain"
        if T.RE_BD_LATCH.search(iu):
            return "latch"
        if v in self.stops:
            return "ctl"
        if "CARRY" in ct:
            return "carry"
        if "MUX" in ct or "F7" in ct or "F8" in ct:
            return "f7"
        return "lut"

    def split(self, path):
        """-> Counter by kind, list of (u, v, w, kind)."""
        c, arcs = collections.Counter(), []
        for (u, tu), (v, tv) in zip(path, path[1:]):
            k = self.kind(u, v)
            c[k] += tv - tu
            arcs.append((u, v, tv - tu, k))
        return c, arcs

    def const_link(self, link):
        """True if every latch data pin of `link` is driven by a constant (or only by its own feedback)."""
        T = self.T
        lat = {inst(p) for p in self.edges if inst(p).startswith(link + ".lat.") and T.RE_BD_LATCH.search(inst(p))}
        if not lat:
            return False
        for p, drv in self.back.items():
            if inst(p) in lat and not T.is_output(p):
                for s in drv:
                    # allowed: tie-offs, the link's own controller (enable) and its own latch outputs (feedback)
                    if T.is_const(s) or inst(s).startswith(link + ".ctl.") or inst(s).startswith(link + ".lat."):
                        continue
                    return False
        return True

    def enable_spread(self, link_or_ctl):
        """Enable-net spread over a link's latch bits: (min, max) controller -> enable pin arc, n bits."""
        ctl = link_or_ctl if link_or_ctl in self.stops else (
            self.stop_of(link_or_ctl + ".ctl.u.u") or self.stop_of(link_or_ctl + ".ctl.ub"))
        if ctl is None:
            return None
        en = self.T.latch_enables(self.edges, ctl)
        if not en:
            return None
        ds = [d for _, d in en]
        return min(ds), max(ds), len(ds)


def link_of_pin(T, pin):
    m = T.RE_UPSTREAM_BD_LINK.match(inst(pin))
    return m.group(1) if m else None


# ============================================================== tracers (one per rule)

def site_of(g, parent):
    T = g.T
    for p, head, tail, links in T.request_sites(g.edges, g.back, g.chains):
        if p == parent:
            downstream = T.reaches(g.edges, tail, g.stops)
            upstream = {q for q in g.edges if T.is_output(q) and head in T.reaches(g.edges, q, g.stops)}
            own = set(links)
            peers = sorted({q for q in g.edges if T.is_output(q) and inst(q).startswith(parent + ".")
                            and inst(q) not in own and q not in downstream and q not in upstream})
            return head, tail, links, peers
    return None


def trace_A(g, parent):
    """tighten.py rule A, as its main() does it for one site; paths by backtracking its tables."""
    T = g.T
    s0 = site_of(g, parent)
    if not s0:
        return None
    head, tail, links, peers = s0
    ups = T.upstream_bd_links(T.cell_boundary(g.edges, g.back, g.stops, parent))
    region = (parent,) + ups
    srcs = T.cell_boundary(g.edges, g.back, g.stops, region)
    confine = region if ups else parent
    res = T.check(g.timing, srcs, peers, tail, T.req_guard, confine=confine)
    pairing = "common source"
    if res is None:
        res = T.check_bundled(g.timing, srcs, peers, tail, T.req_guard, confine=confine)
        pairing = "bundled channel"
    if res is None:
        return None
    margin, guard, t_e, t_l, pin, s = res[:6]
    late_src = res[6] if len(res) > 6 else s
    lag, lags = 0, {}
    if pairing == "bundled channel":
        with contextlib.redirect_stdout(io.StringIO()):
            lag = T.upstream_data_lag(g.timing, g.back, confine, ups, srcs)
            lags = {u: T.upstream_data_lag(g.timing, g.back, confine, (u,), srcs) for u in ups}
    data = g.backtrack(g.timing.late(late_src, confine), "all", late_src, pin)
    req = g.backtrack(g.timing.early(s, confine), "early", s, tail)
    # check() takes the worst over the (source, peer) pairs it CAN form: a peer that no common source pairs with the
    # request is on no rule-A constraint at all (e.g. a bd_mux's datamux, fed by the x/y/select latches only)
    unpaired = []
    if pairing == "common source":
        e_ok = [x for x in srcs if tail in g.timing.early(x, confine)]
        unpaired = [p for p in peers if not any(p in g.timing.late(x, confine) for x in e_ok)]
    return {"rule": "A", "pairing": pairing, "unpaired": unpaired, "launch_req": s, "launch_data": late_src, "capture": pin,
            "req_pin": tail, "t_req": t_e, "t_data": t_l + lag, "guard": guard, "margin": margin - lag,
            "lag": lag, "lags": lags, "data": data, "req": req, "ups": ups}


def trace_Ap(g, parent):
    """corner_audit.rule_a_from_link for one parent, keeping skew.walk's predecessor pointers."""
    T, S = g.T, g.S
    s0 = site_of(g, parent)
    if not s0:
        return None
    head, tail, links, peers = s0
    ups = T.upstream_bd_links(T.cell_boundary(g.edges, g.back, g.stops, parent))

    def at(levels, p):
        for k, tab in enumerate(levels):
            if p in tab:
                return tab[p], k
        return None
    worst = None
    for link in ups:
        for c in (link + ".ctl.u.u/O6", link + ".ctl.ub/O6"):
            if c not in g.stops:
                continue
            we, wl = g.swalk(c, False), g.swalk(c, True)
            r = at(we[0], tail)
            if r is None:
                continue
            ds = [(at(wl[0][:r[1] + 2], p), p) for p in peers]
            ds = [(v, p) for v, p in ds if v is not None]
            if not ds:
                continue
            (t_d, k_d), peer = max(ds)
            gd = T.req_guard(None, t_d)
            m = r[0] - t_d - gd
            if worst is None or m < worst[0]:
                worst = (m, gd, r[0], r[1], t_d, k_d, peer, c)
    if worst is None:
        return None
    m, gd, t_r, k_r, t_d, k_d, peer, c = worst
    return {"rule": "A'", "pairing": "from upstream link C node", "launch_req": c, "launch_data": c,
            "capture": peer, "req_pin": tail, "t_req": t_r, "t_data": t_d, "guard": gd, "margin": m, "lag": 0,
            "data": g.spath(g.swalk(c, True), k_d, peer), "req": g.spath(g.swalk(c, False), k_r, tail), "ups": ups}


def a_prime_blockers(g, parent):
    """Why corner_audit.rule_a_from_link did NOT re-measure this parent from its upstream links' C nodes: check()
    pairs it by common source (then tighten's A is taken as exact), and/or boundary sources that reach a peer without
    crossing an upstream link's latch (its `foreign` test, same code).  -> (common_source_pairs, [foreign sources])"""
    T = g.T
    s0 = site_of(g, parent)
    if not s0:
        return None, []
    head, tail, links, peers = s0
    ups = T.upstream_bd_links(T.cell_boundary(g.edges, g.back, g.stops, parent))
    region = (parent,) + ups
    srcs = T.cell_boundary(g.edges, g.back, g.stops, region)
    common = T.check(g.timing, srcs, peers, tail, T.req_guard, confine=region if ups else parent) is not None
    inside = lambda p: any(inst(p) == r or inst(p).startswith(r + ".") for r in region)
    out = []
    for x in sorted(srcs):
        if inside(x) or T.is_const(x) or not any(p in g.timing.late(x, region) for p in peers):
            continue
        if x in g.stops or any(not inside(y) for y in T.starts_reaching(g.back, x, g.stops)):
            out.append(x)
    return common, out


def trace_E(g, con):
    """skew.py rule E row: re-walk from its launch (skew.walk, same arcs) and replay both paths."""
    m = re.search(r"req (\S+) (\d+) ps \((\d+) x\) sel (\S+) (\d+) ps \((\d+) x\) launch (\S+) tc (-?\d+)", con["text"])
    if not m:
        return None
    rp, tr, kr, sp, ts, ks, launch, tc = m.groups()
    tr, kr, ts, ks, tc = int(tr), int(kr), int(ts), int(ks), int(tc)
    req = g.spath(g.swalk(launch, False), kr, rp)
    data = g.spath(g.swalk(launch, True), ks, sp)
    return {"rule": "E", "pairing": "common launch", "launch_req": launch, "launch_data": launch, "capture": sp,
            "req_pin": rp, "t_req": tr, "t_data": ts, "tc": tc, "guard": None, "margin": con["margin"], "lag": 0,
            "data": data, "req": req, "ups": ()}


def trace_I(g, label, up_inst):
    """tighten.py rule I for one (stage, upstream stage) pair: close path (rise, ack, fall) and data path."""
    T, tm = g.T, g.timing
    ctl, up = g.stop_of(label), g.stop_of(up_inst)
    if ctl is None or up is None:
        return None
    enables = T.latch_enables(g.edges, ctl)
    en_pins = {p for p, _ in enables}
    insts = {inst(p) for p in en_pins}
    d_pins = T.latch_data_pins(g.back, insts, en_pins)
    t_close_rel = min(d + min((a for _, a in g.edges.get(p, ())), default=0) for p, d in enables)
    feeders = set()
    for dp in d_pins:
        feeders |= {s for s in T.starts_reaching(g.back, dp, g.stops) if s in g.stops and T.RE_BD_LATCH.search(inst(s))}
    t_rise = tm.early(up)[ctl]
    dc = T.dc_link_of(ctl)
    if dc is not None:
        t_ack = t_fall = 0
        t_close = t_rise + t_close_rel
    else:
        t_ack, t_fall = tm.early(ctl).get(up), tm.early_fall(up).get(ctl)
        t_close = t_rise + t_ack + t_fall + t_close_rel
    own_lat = {inst(p) for p, _ in T.latch_enables(g.edges, up)}
    l_up = tm.late(up)
    best = None
    for f in feeders:
        if inst(f) not in own_lat or f not in l_up:
            continue
        l_f = tm.late(f)
        for dp in d_pins:
            if dp in l_f:
                arc = max((a for _, a in g.edges.get(dp, ())), default=0)
                lw = T.loop_wire(g.edges, inst(dp))
                v = l_up[f] + l_f[dp] + arc + lw
                if best is None or v > best[0]:
                    best = (v, f, dp, arc, lw)
    if best is None:
        return None
    t_data, f, dp, arc, lw = best
    gd = T.req_guard(None, t_data)
    p1 = g.backtrack(l_up, "all", up, f) or []
    p2 = g.backtrack(tm.late(f), "all", f, dp) or []
    data = p1 + [(p, t + p1[-1][1]) for p, t in p2[1:]] if p1 and p2 else None
    rise = g.backtrack(tm.early(up), "early", up, ctl)
    ack = g.backtrack(tm.early(ctl), "early", ctl, up)
    fall = g.backtrack(tm.early_fall(up), "fall", up, ctl)
    return {"rule": "I", "pairing": "stage pair", "launch_req": up, "launch_data": up, "capture": dp, "req_pin": ctl,
            "t_req": t_close, "t_data": t_data, "guard": gd, "margin": t_close - t_data - gd, "lag": 0,
            "data": data, "req": rise, "req_ack": ack, "req_fall": fall, "close_rel": t_close_rel,
            "latch_arc": arc, "loop_wire": lw, "ups": (link_of_pin(T, up) or "",)}


# ============================================================== loop membership (event graph)

def loop_lines(gdir, within):
    """-> ({chain base (no prefix): [rise ps, fall ps, cycle tags]}, description of the cycles)."""
    from whatif import G, next_cycles
    g = G(str(gdir))
    lam, cyc = g.period()
    cycles = [(lam, [g.arcs[i] for i in cyc], "critical")]
    for lam2, c2, xs in next_cycles(g, cyc, top=8):
        if lam - lam2 <= within:
            cycles.append((lam2, c2, "next (w/o %s)" % ",".join(xs[:3])))
    out, desc, seen = {}, [], set()
    for k, (l, arcs, tag) in enumerate(cycles):
        key = frozenset((a["u"], a["v"]) for a in arcs)
        if key in seen:
            continue
        seen.add(key)
        tagk = "c%d" % k
        by, flips = g.describe(arcs)
        desc.append("%s %s: %.0f ps, %d arcs, stages %s%s" % (
            tagk, tag, l, len(arcs), ", ".join("%s %d/%d" % (i, r, f) for i, (r, f) in by.items()),
            ("; polarity changes " + ", ".join(flips)) if flips else ""))
        for a in arcs:
            v = g.nodes[a["v"]]
            m = RE_CELLCHAIN.match(v.get("cell", ""))
            if not m:
                continue
            b = m.group(1).split("udut.", 1)[-1]
            e = out.setdefault(b, {"R": 0, "F": 0, "tags": {}})
            e["tags"].setdefault(tagk, [0, 0])
            e["tags"][tagk][0 if v["edge"] == "R" else 1] += a["w"]
    for b, e in out.items():   # time on the worst cycle that holds it
        k = min(e["tags"])
        e["R"], e["F"] = e["tags"][k]
    return out, desc


# ============================================================== main

def parse_deps(report):
    """report.txt -> {constraint text: [(macro, dM)]}"""
    deps, last = {}, None
    for ln in open(report):
        m = re.match(r"^  (\S+)\s+([+-]\d+)  (.*)$", ln.rstrip("\n"))
        if m and not ln.startswith("  depends"):
            last = m.group(3)
            continue
        m = re.match(r"^\s+depends on: (.*)$", ln)
        if m and last:
            deps[last] = [(x.group(1), x.group(2)) for x in re.finditer(r"(\S+?)\(-(\w+)\)", m.group(1))]
    return deps


def fmt_path(g, path, title):
    if not path:
        return ["  %s: (not traced)" % title]
    c, arcs = g.split(path)
    out = ["  %s: %d ps  [%s]" % (title, path[-1][1] - path[0][1],
                                  ", ".join("%s %d" % (k, v) for k, v in sorted(c.items())))]
    out.append("    %6d  %s" % (path[0][1], path[0][0]))
    for u, v, w, k in arcs:
        out.append("    %6d  %-7s +%-5d %s" % (path[[p for p, _ in path].index(v)][1], k, w, v))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("ca_out", type=pathlib.Path)
    ap.add_argument("--graph", type=pathlib.Path, required=True, help="event graph dir (nodes.tsv, arcs.tsv, check.txt)")
    ap.add_argument("--sizes", type=pathlib.Path)
    ap.add_argument("--prefix", default="bridge_i.udut.")
    ap.add_argument("--within", type=int, default=2000, help="also next cycles within this many ps of the critical")
    ap.add_argument("--all", action="store_true", help="every line of the kernel, not only the loop's")
    ap.add_argument("--and-join", type=int, default=1, help="BD_SKEW_AND_JOIN as the item-25 static check (1)")
    ap.add_argument("--out", type=pathlib.Path)
    ap.add_argument("--corner", default=None, help="label for the tables (default: CA_OUT's name)")
    a = ap.parse_args()
    ca = a.ca_out.resolve()
    sdf = ca / "soak.sdf"
    sizes_path = a.sizes or ca.parent / "seed1" / "pnr" / "sizes.vh"
    out = a.out or ca / "line_account"
    out.mkdir(parents=True, exist_ok=True)
    corner = a.corner or ca.name

    res, CA, T, S = load_audit(sdf, a.and_join)
    cons, geo = res["constraints"], res["chains"]
    g = Graph(T, S, sdf)
    deps = parse_deps(ca / "report.txt") if (ca / "report.txt").exists() else {}
    sizes, _ = CA.read_sizes(sizes_path)
    CA.MPFX = CA.macro(a.prefix)
    try:
        with contextlib.redirect_stderr(io.StringIO()):
            protected = CA.select_path_macros(ca.parent / "seed1", list(sizes))
    except Exception:
        protected = set()
    t_elem = T.measure_delay_element(sdf.read_text()) or T.T_DELAY_RISE_FALLBACK
    cells = list(json.load(open(ca / "soak_routed.json"))["modules"].values())[0]["cells"]
    last_stage = {}
    for n in cells:
        m = re.match(r"^(.*?)\.many\.stage\[(\d+)\]\.u\.", n)
        if m:
            last_stage[m.group(1)] = max(last_stage.get(m.group(1), -1), int(m.group(2)))
    loop, cyc_desc = loop_lines(a.graph, a.within)

    def mac_of_knob(k):
        return CA.macro(k) if k else None
    # constraints by the line (macro) whose knob they are
    own = collections.defaultdict(list)
    for k, c in cons.items():
        if c.get("knob"):
            own[mac_of_knob(c["knob"])].append(k)

    prop = {}
    if (ca / "lines.tsv").exists():
        for ln in list(open(ca / "lines.tsv"))[1:]:
            f = ln.rstrip("\n").split("\t")
            prop[f[0]] = (f[2], f[7] if len(f) > 7 else "")
    e_traces = {}
    rows, ptxt = [], ["line_account %s (corner %s), graph %s" % (ca, corner, a.graph), "cycles:"] + \
        ["  " + d for d in cyc_desc] + [""]
    bases = sorted(b for b in geo if b.startswith(a.prefix) and (a.all or b[len(a.prefix):] in loop))
    for b in bases:
        short = b[len(a.prefix):]
        knob = CA.knob_of_base(b, last_stage)
        mac = CA.macro(knob)
        n, D = geo[b]["n"], geo[b]["D"] or 0
        # per-element cost: the line's own mean link-to-link step (LUT arc + hop); a 1-element line has no step,
        # so the route's median element (tighten.measure_delay_element) prices it
        st = geo[b]["steps"]
        c_el = sum(st) / len(st) if st else t_elem
        lp = loop.get(short, {"R": 0, "F": 0, "tags": {}})
        # a constraint SETS a line's length when the line is on its late-request side (A, A', E, I) or on the early
        # side of a hold (H, K, L); rule F (the line's own flush) and the screen D only bound it from above
        mine = [k for k in own.get(mac, []) if cons[k]["rule"] in "AEHIKL"]
        # the A row tighten made is "a" once A' exists for the parent; keep it as the fallback
        if not [k for k in mine if cons[k]["rule"] in "AE"]:
            mine += [k for k in own.get(mac, []) if cons[k]["rule"] == "a"]
        flags = []
        dep = [(k, dm) for k, c in cons.items() if c["rule"] in "AEHIKL"
               for mm, dm in deps.get(c["text"], []) if "BD_SZ_" + mm == mac]
        fl = [k for k, c in cons.items() if c["rule"] == "F" and k.split()[1] == b]
        if fl:
            flags.append("F (own flush) margin %d" % cons[fl[0]]["margin"])
        if mac not in sizes:
            flags.append("not in sizes.vh: RTL default %d" % n)
        if mac in protected:
            flags.append("%s (withdrawn select rule; corner_audit never shortens it)" % (
                "mux delay" if re.search(r"_UMUX\d+$", mac) else "select link"))
        if mine:
            bk = min(mine, key=lambda k: cons[k]["margin"])
            how = "own"
        elif dep:
            bk = min((k for k, _ in dep), key=lambda k: cons[k]["margin"])
            how = "depends"
        else:
            bk, how = None, "none"
            # no sensitivity table (report.txt) or no row: the E rows whose traced REQUEST path runs through it
            for k, cc in cons.items():
                if cc["rule"] != "E":
                    continue
                if k not in e_traces:
                    with contextlib.redirect_stdout(io.StringIO()):
                        e_traces[k] = trace_E(g, cc)
                t2 = e_traces[k]
                if t2 and t2["req"] and any(RE_LINK.match(inst(p)) and RE_LINK.match(inst(p)).group("base") == b
                                            for p, _ in t2["req"]):
                    if bk is None or cc["margin"] < cons[bk]["margin"]:
                        bk, how = k, "on its request"
        tr = None
        c = cons.get(bk) if bk else None
        if c:
            try:
                with contextlib.redirect_stdout(io.StringIO()):
                    if c["rule"] == "A" and bk.startswith("A' "):
                        tr = trace_Ap(g, c["knob"])
                    elif c["rule"] in ("A", "a"):
                        tr = trace_A(g, bk.split()[1])
                    elif c["rule"] == "E":
                        tr = e_traces.get(bk) or trace_E(g, c)
                    elif c["rule"] == "I":
                        mf = re.search(r"\[from (\S+)\]", c["text"])
                        tr = trace_I(g, bk.split()[1], mf.group(1)) if mf else None
            except Exception as e:      # a tracer gap is reported, never a silent pass
                flags.append("trace failed: %s: %s" % (type(e).__name__, e))
        row = {"ca_prop": "", "line": short, "macro": mac.replace("BD_SZ_", ""), "n": n, "size_vh": sizes.get(mac, "-"),
               "D_ps": D, "ps_el": round(c_el), "cyc_R": lp["R"], "cyc_F": lp["F"],
               "cycles": ",".join(sorted(lp["tags"])), "set_by": how,
               "rule": (("A'" if bk and bk.startswith("A' ") else c["rule"]) if c else "-"),
               "margin": c["margin"] if c else "", "constraint": (c["text"][:160] if c else
                                                                ("no measured constraint" if not flags else ""))}
        row.update({k: "" for k in ("launch", "capture", "t_req", "t_data", "guard", "logic", "latch", "enable",
                                    "wire", "ctl", "chain_on_data", "en_spread", "req_other", "req_wire",
                                    "n_need", "n_logic", "top_wire", "check")})
        if c and c["rule"] in ("H", "F"):
            row["check"] = "totals only (%s)" % c["rule"]
            if c["rule"] == "H":
                sp = g.enable_spread(g.stop_of(bk.split()[1]) or bk.split()[1])
                if sp:
                    row["en_spread"] = "%d-%d (%d bits)" % sp
                mm = re.search(r"enable\s+(\d+)\s+data\s+(\d+)", c["text"])
                if mm:
                    row["t_data"], row["t_req"] = int(mm.group(1)), int(mm.group(2))
                if c_el:
                    row["n_need"] = max(0, n - int(c["margin"] // c_el))
        if tr:
            dc, darcs = g.split(tr["data"]) if tr["data"] else (collections.Counter(), [])
            rc, rarcs = g.split(tr["req"]) if tr["req"] else (collections.Counter(), [])
            if tr["rule"] == "I":
                for extra in ("req_ack", "req_fall"):
                    if tr.get(extra):
                        rarcs += g.split(tr[extra])[1]
            # the line's own part of the request: every arc INTO one of its elements (the wire into its head, its
            # LUT arcs, its internal hops); the rest of the request path is what the request crosses besides it
            inline = lambda v: bool(RE_LINK.match(inst(v))) and RE_LINK.match(inst(v)).group("base") == b
            line_on_req = sum(w for u, v, w, k in rarcs if inline(v))
            req_wire = sum(w for u, v, w, k in rarcs if k in ("wire", "enable") and not inline(v))
            other_lines = sum(w for u, v, w, k in rarcs if RE_LINK.match(inst(v)) and not inline(v))
            t_req, t_data = tr["t_req"], tr["t_data"]
            row.update(launch=inst(tr["launch_data"]).replace(a.prefix, ""),
                       capture=tr["capture"].replace(a.prefix, ""), t_req=t_req, t_data=t_data,
                       guard=tr["guard"] if tr["guard"] is not None else "E 0.97/1.03",
                       logic=dc["lut"] + dc["carry"] + dc["f7"], latch=dc["latch"], enable=dc["enable"],
                       wire=dc["wire"], ctl=dc["ctl"], chain_on_data=dc["chain"],
                       req_other=t_req - line_on_req, req_wire=req_wire)
            if other_lines:
                flags.append("request also crosses %d ps of other lines" % other_lines)
            # enable spread of the link whose latch the data path crosses
            lk = next((link_of_pin(T, u) for u, v, w, k in darcs if k == "latch"), None)
            if lk:
                sp = g.enable_spread(lk)
                if sp:
                    row["en_spread"] = "%d-%d (%d bits)" % sp
            if tr["lag"]:
                row["latch"] = "%d (+lag %d)" % (dc["latch"], tr["lag"])
                worst_l = max(tr["lags"], key=tr["lags"].get) if tr.get("lags") else "?"
                own_l = link_of_pin(T, tr["launch_data"]) or re.sub(r"\.lat\..*$", "", inst(tr["launch_data"]))
                flags.append("bundled pairing: request from the join at t=0, data from %s at t=0 plus the WORST "
                             "upstream link's controller->latch lag %d (%s); the data's own link's lag is %s" % (
                                 inst(tr["launch_data"]).replace(a.prefix, ""), tr["lag"],
                                 worst_l.replace(a.prefix, ""), tr.get("lags", {}).get(own_l, "?")))
            wires = sorted(((w, u, v) for u, v, w, k in darcs if k in ("wire", "enable")), reverse=True)
            if wires:
                w, u, v = wires[0]
                row["top_wire"] = "%s -> %s %d" % (u.replace(a.prefix, ""), v.replace(a.prefix, ""), w)
            # traced totals against the audit's own
            got_d = (tr["data"][-1][1] - tr["data"][0][1]) if tr["data"] else None
            if tr["rule"] == "I" and tr["data"]:
                got_d += tr["latch_arc"] + tr["loop_wire"]
            want_d = t_data - tr["lag"]
            got_r = (tr["req"][-1][1] - tr["req"][0][1]) if tr["req"] else None
            want_r = t_req if tr["rule"] != "I" else None
            chk = []
            if got_d is None or got_d != want_d:
                chk.append("data %s vs %s" % (got_d, want_d))
            if want_r is not None and (got_r is None or got_r != want_r):
                chk.append("req %s vs %s" % (got_r, want_r))
            row["check"] = "ok" if not chk else "MISMATCH " + "; ".join(chk)
            # elements for margin 0, and for the logic alone
            logic = row["logic"]
            if c_el:
                if tr["rule"] in ("A", "A'"):
                    need = t_data + tr["guard"] - (t_req - line_on_req)
                    row["n_need"] = max(0, math.ceil(need / c_el))
                    row["n_logic"] = max(0, math.ceil((logic + T.req_guard(None, logic)) / c_el)) if logic else 0
                elif tr["rule"] == "E":
                    tc = tr["tc"]
                    req_need = tc + 1.03 * (t_data - tc) / 0.97
                    row["n_need"] = max(0, math.ceil((req_need - (t_req - line_on_req)) / c_el))
                    row["guard"] = "0.97/1.03"
                    row["n_logic"] = max(0, math.ceil(1.03 / 0.97 * logic / c_el)) if logic else 0
                elif tr["rule"] == "I":
                    fast = any(RE_LINK.match(inst(d)) and RE_LINK.match(inst(d)).group("base") in b
                               for _, d in T.fastfall_side_arcs(g.edges))
                    per = (1 if fast else 2) * c_el
                    row["n_need"] = max(0, math.ceil(n - tr["margin"] / per))
            # const-carrying upstream links (a request that waits on an operand that never changes)
            if tr.get("unpaired"):
                grp = sorted({re.sub(r"\.(?:pair\[\d+\]|odd).*$", "", inst(p)).replace(a.prefix, "")
                              for p in tr["unpaired"]})
                flags.append("rule A pairs by common source %s; %d peer output(s) no common source pairs with the "
                             "request, on NO rule-A constraint: %s" % (inst(tr["launch_req"]).replace(a.prefix, ""),
                                                                      len(tr["unpaired"]), " ".join(grp[:4])))
            if tr["rule"] == "A" and c_el:      # tighten's own A is what binds: would A' measure it, and why not
                common, foreign = a_prime_blockers(g, bk.split()[1])
                with contextlib.redirect_stdout(io.StringIO()):
                    alt = trace_Ap(g, bk.split()[1])
                if alt and not common:   # (where check() pairs, corner_audit never re-measures; A' there is laps)
                    lo = sum(w for u, v, w, k in g.split(alt["req"])[1] if RE_LINK.match(inst(v)) and
                             RE_LINK.match(inst(v)).group("base") == b) if alt["req"] else 0
                    need = math.ceil((alt["t_data"] + alt["guard"] - (alt["t_req"] - lo)) / c_el)
                    flags.append("A' (from the upstream links' C nodes) would give margin %d, n_need %d; not applied "
                                 "because %s" % (alt["margin"], max(0, need), "; ".join(
                                     (["check() pairs it by common source"] if common else []) +
                                     (["foreign source(s) reach a peer: " + " ".join(
                                         x.replace(a.prefix, "") for x in foreign)] if foreign else []))
                                     or "?"))
            cl = [u.replace(a.prefix, "") for u in tr.get("ups", ()) if u and g.const_link(u)]
            if cl:
                flags.append("joins constant-data link(s) " + " ".join(cl))
            ptxt.append("== %s  (%s, %d elements, %d ps at %s; set by %s %s, margin %s)" % (
                short, mac, n, D, corner, how, row["rule"], row["margin"]))
            ptxt.append("  constraint: " + (c["text"] if c else "-"))
            ptxt += fmt_path(g, tr["data"], "data (launch %s -> capture %s)" % (tr["launch_data"], tr["capture"]))
            ptxt += fmt_path(g, tr["req"], "request (from %s to %s)" % (tr["launch_req"], tr["req_pin"]))
            for extra in ("req_ack", "req_fall"):
                if tr.get(extra):
                    ptxt += fmt_path(g, tr[extra], extra)
            if tr["rule"] == "I":
                ptxt.append("  + latch arc %d, loop wire %d, close rel %d" % (tr["latch_arc"], tr["loop_wire"],
                                                                               tr["close_rel"]))
            ptxt.append("")
        elif c:
            ptxt += ["== %s  (%s, %d elements, %d ps; set by %s %s, margin %s)" % (
                short, mac, n, D, how, row["rule"], row["margin"]), "  constraint: " + c["text"], ""]
        if mac in prop:
            row["ca_prop"] = prop[mac][0]
            if prop[mac][1]:
                flags.append("corner_audit: " + prop[mac][1])
        row["flags"] = "; ".join(flags)
        rows.append(row)

    cols = ["line", "macro", "n", "size_vh", "D_ps", "ps_el", "cyc_R", "cyc_F", "cycles", "set_by", "rule", "margin",
            "launch", "capture", "t_req", "t_data", "guard", "logic", "latch", "enable", "wire", "ctl",
            "chain_on_data", "en_spread", "req_other", "req_wire", "n_need", "n_logic", "ca_prop", "top_wire", "check",
            "flags", "constraint"]
    rows.sort(key=lambda r: -(r["cyc_R"] + r["cyc_F"]))
    with open(out / "lines.tsv", "w") as f:
        f.write("\t".join(cols) + "\n")
        for r in rows:
            f.write("\t".join(str(r[c]) for c in cols) + "\n")
    md = ["## %s, corner %s" % (a.graph.name, corner), ""] + ["- " + d for d in cyc_desc] + ["",
          "| line | n | ps (ps/el) | on cycle R/F | set by | margin | launch -> capture | data: logic / latch / "
          "enable / wire / ctl | en spread | req: total / not line / wire | guard | n_need | n_logic | corner_audit "
          "proposal | widest data wire | flags |", "|" + "---|" * 16]
    for r in rows:
        md.append("| %s | %s | %s (%s) | %s/%s | %s %s | %s | %s -> %s | %s / %s / %s / %s / %s | %s | %s / %s / %s"
                  " | %s | %s | %s | %s | %s | %s |" % (
                      r["line"], r["n"], r["D_ps"], r["ps_el"], r["cyc_R"], r["cyc_F"], r["rule"], r["set_by"],
                      r["margin"], r["launch"], r["capture"], r["logic"], r["latch"], r["enable"], r["wire"],
                      r["ctl"], r["en_spread"], r["t_req"], r["req_other"], r["req_wire"], r["guard"], r["n_need"],
                      r["n_logic"], r["ca_prop"], r["top_wire"], "; ".join(x for x in (r["flags"], "" if r["check"] in ("ok", "")
                                                                          else r["check"]) if x)))
    (out / "lines.md").write_text("\n".join(md) + "\n")
    (out / "paths.txt").write_text("\n".join(ptxt) + "\n")
    print("\n".join(md))
    print("wrote %s/{lines.tsv, lines.md, paths.txt}" % out)


if __name__ == "__main__":
    main()
