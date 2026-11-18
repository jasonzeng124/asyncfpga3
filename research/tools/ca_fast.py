"""ca_fast.py -- CA_FAST=1 (opt-in): corner_audit.py's audit runs, the same audits, shared between runs.

corner_audit.py measures which line a constraint depends on by re-running every audit (tighten.main, skew.main,
rule A', A'j, arb_fork) once per sized line with that line's internal arcs set to 0, each run a fresh process that
re-parses the route and re-derives everything: O(lines x design), ~1.5 h per rule step on gcd on the farm.  But such a
run changes nothing except the WEIGHTS of the arcs whose source is a pin of that line (its CHANGED pins): the graph's
topology, the storage nodes, the cells, the routed JSON, and every computation that reads none of those arcs come out
the same.  This module makes that reuse exact.  Nothing in the audits' arithmetic is re-implemented; their own
functions run, with a memo around some of the functions they call:

  * TOPOLOGY functions (reaches, site_peers, cell_boundary, starts_reaching, latch_data_pins, chain_endpoints,
    request_sites, find_chains, storage_nodes, state_nodes, the side-arc sets, back_reach, false_arcs,
    select_consumers, measure_delay_element; pin_split / is_output as dict lookups): they read no arc weight; keyed by
    an order-sensitive fingerprint of their arguments' content (pins, arcs without weights, iteration order kept),
    reused in every run.
  * WEIGHT functions (tighten.walk -- every Timing table --, latch_enables, and the composites earliest_disturbance,
    upstream_data_lag and corner_audit's per-site rows A' / A'j): keyed the same way; each entry records its READ SET,
    every pin whose outgoing arcs it read (a walk table: every pin in it; a composite: the union of what it called).
    A base-run entry is reused in a later run while its read set holds none of that run's changed pins.
  * LEVEL walks (skew.walk, walk_floor: one arrival table per storage-crossing count): level k is made from levels
    < k and the arcs of its own pins, so a base-run walk is handed to a later run up to the level before the first
    one holding a changed pin, behind a guard (_Walk) that makes the walk again on that run's arcs before any deeper
    level is read; every level read notes levels 0..k to the composites being computed.
  * earliest_disturbance (rule H's Dijkstra over the state nodes, arcs = the walk tables): its labels are shortest
    distances and its `hit` a minimum, both unique; in a run whose every scaled line is at a factor <= 1 (a sensitivity
    run: arcs only get shorter) it is updated from the base run's labels, relaxing from the nodes whose table changed
    -- the textbook update for decreased arc weights; any other run makes it in full.  CA_FAST_SELFCHECK=1 runs
    tighten's own function beside it and stops on any difference.
  * the graphs the audits derive (routed_graph, Timing's side-pruned graphs, rule A''s incoming arcs): built in the
    base run; a later run copies them and rebuilds the changed pins' entries only.
  * the base run is made in-process; every later run (one per sized line, each verify) is a fork of that process
    (Pool), so the parse, the routed JSON and the memo are inherited, not re-read.  arb_fork (rule J) reads the
    corner SDF file itself and no scaled arc, so a forked run reuses the base run's rule J log.
  * a memoized function that prints (upstream_data_lag's warnings) replays its output on a hit, so every log is the
    same text.

Exactness rests on: the audits are deterministic within one process and its forks (one hash seed); a memoized
function's result depends only on its arguments' content and the arcs in its read set; no caller mutates a returned
object (starts_reaching's result is, by rule D: it is handed out as a copy).  research/tools/auto/ca_fast_check.py
compares runs with the old path one by one, research/tools/auto/ca_fast_e2e.sh the whole rule's outputs.  Off (unset),
nothing here is imported."""
import collections, contextlib, heapq, io, json, math, os, re, sys, tempfile, time

# ---------------------------------------------------------------- fingerprints (topology only, order-sensitive)


class G(collections.defaultdict):
    """parse_sdf's edges (defaultdict(list) of (dst, w)), with a topology fingerprint kept across assignments: an
    assignment that changes a pin's destinations (or adds a pin) drops it; one that only changes weights keeps it."""

    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self._tfp = None
        self._rc = None              # (stops, {start: reaches(self, start, stops)}): valid while _tfp is

    def __setattr__(self, name, val):
        object.__setattr__(self, name, val)
        if name == "_tfp" and val is None:
            object.__setattr__(self, "_rc", None)

    def __setitem__(self, key, val):
        if self._tfp is not None:
            old = dict.get(self, key)
            if old is None or len(old) != len(val) or any(x[0] != y[0] for x, y in zip(old, val)):
                self._tfp = None
        dict.__setitem__(self, key, val)

    def __delitem__(self, key):
        self._tfp = None
        dict.__delitem__(self, key)

    def pop(self, *a):
        self._tfp = None
        return dict.pop(self, *a)

    def popitem(self):
        self._tfp = None
        return dict.popitem(self)

    def clear(self):
        self._tfp = None
        dict.clear(self)

    def update(self, *a, **k):
        self._tfp = None
        dict.update(self, *a, **k)

    def setdefault(self, key, default=None):
        if key not in self:
            self._tfp = None
        return dict.setdefault(self, key, default)


def _graph_fp(d):
    """{pin: [(pin, w), ...]} -> fingerprint of the topology, weights left out, order kept."""
    t = tuple((k, tuple(x[0] for x in v)) for k, v in d.items())
    return ("g", len(t), sum(len(x[1]) for x in t), hash(t))


def _back_fp(d):
    """{pin: set(pins)} (or lists of pins) -> fingerprint, iteration order kept."""
    t = tuple((k, tuple(v)) for k, v in d.items())
    return ("b", len(t), hash(t))


def _seq_fp(s):
    t = tuple(s)
    return ("s", len(t), hash(t))


_IDFP = {}     # id(obj) -> (obj, len(obj), kind, fp): strong reference, so an id is never reused while cached


def _cached(o, kind, fn):
    e = _IDFP.get(id(o))
    if e is not None and e[0] is o and e[1] == len(o) and e[2] == kind:
        return e[3]
    f = fn(o)
    _IDFP[id(o)] = (o, len(o), kind, f)
    return f


def fp_graph(d):
    if isinstance(d, G):
        if d._tfp is None:
            d._tfp = _graph_fp(d)
        return d._tfp
    return _cached(d, "g", _graph_fp)


def fp_back(d):
    return _cached(d, "b", _back_fp)


def fp_set(s):
    if isinstance(s, frozenset) and len(s) < 64:
        return ("s", len(s), hash(tuple(s)))
    return _cached(s, "s", _seq_fp)


def fp_small(s):
    """A small set built per call (insts, en_pins, srcs, targets): no id cache."""
    return _seq_fp(s)


# ---------------------------------------------------------------- the memo


class Memo:
    def __init__(self):
        self.store = {}          # key -> (gen, readset or None, result, printed text or None)
        self.gen = 0             # 0: the base run (the parent); 1: a forked run
        self.changed = frozenset()
        self.decrease_only = False   # every scaled line at a factor <= 1 (a sensitivity run): weights only fall
        self.acc = []            # read-set accumulators of the composites being computed
        self._stale = None
        self.stats = collections.Counter()


M = Memo()


def stale_keys():
    """The base-run entries a forked run cannot reuse (read set meets the changed pins), once per run."""
    if M._stale is None:
        C = M.changed
        M._stale = frozenset(k for k, e in M.store.items()
                             if e[0] == 0 and e[1] is not None and not e[1].isdisjoint(C))
    return M._stale


def _valid(e):
    return e[1] is None or e[0] != 0 or M.gen == 0 or e[1].isdisjoint(M.changed)


def _note(rs):
    if rs and M.acc:
        for a in M.acc:
            a.update(rs)


def memo_topo(name, fn, keyf, copy=None):
    def wrapped(*a, **k):
        key = keyf(*a, **k)
        if key is None:
            return fn(*a, **k)
        key = (name,) + key
        e = M.store.get(key)
        if e is None:
            M.stats[name + " miss"] += 1
            r = fn(*a, **k)
            M.store[key] = (M.gen, None, r, None)
        else:
            M.stats[name + " hit"] += 1
            r = e[2]
        return copy(r) if copy else r
    wrapped.__wrapped__ = fn
    return wrapped


def memo_weight(name, fn, keyf, readset, prints=False):
    """readset(result, args) -> the pins whose outgoing arcs the call read (None: use what the inner calls noted)."""
    def wrapped(*a, **k):
        key = keyf(*a, **k)
        if key is None:
            return fn(*a, **k)
        key = (name,) + key
        e = M.store.get(key)
        if e is not None and _valid(e):
            M.stats[name + " hit"] += 1
            _note(e[1])
            if e[3]:
                sys.stdout.write(e[3])
            return e[2]
        M.stats[name + (" miss" if e is None else " stale")] += 1
        acc = set()
        M.acc.append(acc)
        try:
            if prints:
                buf = io.StringIO()
                with contextlib.redirect_stdout(buf):
                    r = fn(*a, **k)
                txt = buf.getvalue()
                sys.stdout.write(txt)
            else:
                r, txt = fn(*a, **k), None
        finally:
            M.acc.pop()
        own = readset(r, a, k) if readset else None
        if own:
            acc.update(own)
        rs = frozenset(acc)
        M.store[key] = (M.gen, rs, r, txt or None)
        _note(rs)
        return r
    wrapped.__wrapped__ = fn
    return wrapped


class _Lv(list):
    """One of a level walk's two lists (arrival tables, predecessor maps: one per storage-crossing count), as the
    list the walk returned.  Every read of level k goes through _Walk.touch(k) first: it notes the pins levels
    0..k hold (reading level k depends on all of them) to the composites being computed, and, in a forked run, makes
    the walk again on this run's arcs before handing out a level the base run's walk is not valid for."""
    __slots__ = ("_w",)

    def __getitem__(self, k):
        if isinstance(k, slice):
            r = range(*k.indices(len(self)))
            if len(r):
                self._w.touch(max(r))
            return list.__getitem__(self, k)
        self._w.touch(k if k >= 0 else len(self) + k)
        return list.__getitem__(self, k)

    def __iter__(self):
        for i in range(len(self)):
            self._w.touch(i)
            yield list.__getitem__(self, i)


class _Walk:
    """A level walk's result.  upto None: every level is this run's; upto u: levels 0..u are the base run's and read
    no pin this run changed (so they are what the walk makes on this run's arcs), and `redo` makes the walk again
    before any deeper level is read."""

    def __init__(self, r, upto=None, redo=None):
        self.out, self.pred = r
        self.upto, self.redo = upto, redo
        self.views = (_Lv(), _Lv())
        list.extend(self.views[0], self.out)
        list.extend(self.views[1], self.pred)
        self.views[0]._w = self.views[1]._w = self

    def touch(self, k):
        if k >= len(self.out):
            k = len(self.out) - 1
        if k < 0:
            return
        if self.upto is not None and k > self.upto:
            M.stats["walk redo"] += 1
            self.out, self.pred = self.redo()
            self.upto = self.redo = None
            list.__setitem__(self.views[0], slice(None), self.out)
            list.__setitem__(self.views[1], slice(None), self.pred)
        if M.acc:
            rs = set()
            for tab in self.out[:k + 1]:
                rs.update(tab)
            _note(rs)

    def first_stale(self, C):
        for i, tab in enumerate(self.out):
            for c in C:
                if c in tab:
                    return i
        return None


def memo_levels(name, fn, keyf):
    """skew.walk / walk_floor: keyed like memo_weight; a base-run walk is reused in a forked run up to the level
    before the first one holding a changed pin (a level's tables are made from the levels before it and the arcs of
    its own pins: every pin a level reads an arc of is in its table), behind _Walk's guard."""
    def wrapped(*a, **k):
        key = keyf(*a, **k)
        if key is None:
            return fn(*a, **k)
        key = (name,) + key
        e = M.store.get(key)
        if e is not None:
            W = e[2]
            if M.gen == 0 or e[0] != 0 or W.upto is not None:
                M.stats[name + " hit"] += 1
                return W.views
            fs = W.first_stale(M.changed)
            if fs is None:
                M.stats[name + " hit"] += 1
                return W.views
            if fs > 0:
                M.stats[name + " partial"] += 1
                W2 = _Walk((W.out, W.pred), fs - 1, lambda: fn(*a, **k))
                M.store[key] = (M.gen, None, W2, None)
                return W2.views
        M.stats[name + (" miss" if e is None else " stale")] += 1
        W = _Walk(fn(*a, **k))
        M.store[key] = (M.gen, None, W, None)
        return W.views
    wrapped.__wrapped__ = fn
    return wrapped


def _fp_timing(t):
    return (fp_graph(t.edges), fp_set(t.stops))


_INSTALLED = []


def install(T, skew, ca):
    """Wrap the functions named in the docstring, once per process."""
    if _INSTALLED:
        return
    _INSTALLED.append(True)
    orig_parse = T.parse_sdf
    raw = {}

    def parse_sdf(path):
        p = str(path)
        if p not in raw:
            edges, celltype, n_io, n_ic = orig_parse(path)
            g = G(list)
            for k, v in edges.items():
                dict.__setitem__(g, k, v)
            g._tfp = _graph_fp(g)
            raw[p] = (g, celltype, n_io, n_ic)
        g0, celltype, n_io, n_ic = raw[p]
        g = G(list)
        dict.update(g, g0)           # the arc lists are shared: every caller replaces a list, none edits one
        g._tfp = g0._tfp
        return g, dict(celltype), n_io, n_ic
    T.parse_sdf = parse_sdf
    install.raw = raw

    # pin_split / is_output: the same function of the pin (is_output's pin sets are complete after the first parse,
    # which every run makes before anything else), answered from a dict after its first call per pin
    o_ps, o_io = T.pin_split, T.is_output

    class _PS(dict):
        def __missing__(self, pin):
            v = self[pin] = o_ps(pin)
            return v

    class _IO(dict):
        def __missing__(self, pin):
            v = self[pin] = o_io(pin)
            return v
    T.pin_split = _PS().__getitem__
    T.is_output = _IO().__getitem__
    reach = memo_topo("reaches", T.reaches, lambda e, s, st: (fp_graph(e), fp_set(st), s))

    def reaches(e, s, st):           # the same memo, with a per-graph-object front cache (rule A asks per site)
        if isinstance(e, G):
            rc = e._rc
            if rc is None or rc[0] is not st:
                rc = (st, {})
                object.__setattr__(e, "_rc", rc)
            r = rc[1].get(s)
            if r is None:
                r = rc[1][s] = reach(e, s, st)
            return r
        return reach(e, s, st)
    T.reaches = reaches
    # routed_graph and Timing's side-pruned graphs: built in the base run; a forked run copies them and rebuilds only
    # the pins its scale changed (every other pin's arcs are the base run's, the same parse pruned the same way)
    orig_rg = T.routed_graph

    def routed_graph(sdf):
        k = ("routed_graph", str(sdf))
        d = _DER.get(k)
        if d is None or M.gen == 0:
            r = orig_rg(sdf)
            if M.gen == 0 and d is None:
                fp_graph(r[0]), fp_back(r[1]), fp_set(r[2])
                _DER[k] = r
            return r
        pe, pb, ps = d
        g = T.parse_sdf(sdf)[0]                   # this run's arcs
        dead = T.false_arcs(g, sdf)[0]
        e = G(list)
        dict.update(e, pe)
        for src in M.changed:
            if src in g:
                dict.__setitem__(e, src, [(x, w) for x, w in g[src] if (src, x) not in dead])
        e._tfp = pe._tfp
        return e, pb, ps
    T.routed_graph = routed_graph

    def tinit(self, edges, stops):              # Timing.__init__, its two side-pruned graphs through side_pruned()
        self.edges, self.stops = edges, stops
        ff, fr = T.fastfall_side_arcs(edges), T.fastrise_side_arcs(edges)
        self.early_edges, self.fall_edges = side_pruned(edges, ff), side_pruned(edges, fr)
        self._late, self._early, self._fall, self._any = {}, {}, {}, {}
    T.Timing.__init__ = tinit
    T.site_peers = memo_topo("site_peers", T.site_peers,
                             lambda e, st, parent, head, tail, links: (fp_graph(e), fp_set(st), parent, head, tail,
                                                                       tuple(links)))
    skew.back_reach = memo_topo("back_reach", skew.back_reach,
                                lambda pin, so, fd, bi, st: (fp_back(so), fp_set(fd), fp_graph(bi), fp_set(st), skew.K,
                                                             pin))
    T.cell_boundary = memo_topo("cell_boundary", T.cell_boundary,
                                lambda e, b, st, p: (fp_graph(e), fp_back(b), fp_set(st), p))
    T.starts_reaching = memo_topo("starts_reaching", T.starts_reaching,
                                  lambda b, p, st, limit=20000: (fp_back(b), p, fp_set(st), limit), copy=set)
    T.latch_data_pins = memo_topo("latch_data_pins", T.latch_data_pins,
                                  lambda b, i, e: (fp_back(b), fp_small(i), fp_small(e)))
    T.chain_endpoints = memo_topo("chain_endpoints", T.chain_endpoints,
                                  lambda e, b, links: (fp_graph(e), fp_back(b), tuple(links)))
    T.request_sites = memo_topo("request_sites", T.request_sites,
                                lambda e, b, c: (fp_graph(e), fp_back(b), fp_back(c)))
    T.find_chains = memo_topo("find_chains", T.find_chains, lambda e: (fp_graph(e),))
    T.storage_nodes = memo_topo("storage_nodes", T.storage_nodes, lambda e: (fp_graph(e),))
    T.state_nodes = memo_topo("state_nodes", T.state_nodes, lambda e: (fp_graph(e),))
    T.chain_side_arcs = memo_topo("chain_side_arcs", T.chain_side_arcs, lambda e: (fp_graph(e),))
    T.fastfall_side_arcs = memo_topo("fastfall_side_arcs", T.fastfall_side_arcs, lambda e: (fp_graph(e),))
    T.fastrise_side_arcs = memo_topo("fastrise_side_arcs", T.fastrise_side_arcs, lambda e: (fp_graph(e),))
    T.false_arcs = memo_topo("false_arcs", T.false_arcs, lambda e, sdf=None: (str(sdf if sdf is not None else T.SDF),))
    T.select_consumers = memo_topo("select_consumers", T.select_consumers, lambda j: (str(j),))
    T.measure_delay_element = memo_topo("measure_delay_element", T.measure_delay_element,
                                        lambda text: (len(text), hash(text)))

    def le_rs(r, a, k):            # ctl's arcs, and (bd_link_dc) the ult arcs two hops on
        e, ctl = a[0], a[1]
        s = {ctl}
        for d, _ in e.get(ctl, ()):
            s.add(d)
            for d2, _ in e.get(d, ()):
                s.add(d2)
        return s
    T.latch_enables = memo_weight("latch_enables", T.latch_enables, lambda e, c: (fp_graph(e), c), le_rs)
    # Timing's own per-instance table caches would hide a table's read from a composite: every access goes to the
    # memo (the same walk, the same arguments, the same object returned on every call)
    T.Timing.late = lambda self, s, confine=None: T.walk(self.edges, s, self.stops, True, confine)
    T.Timing.early = lambda self, s, confine=None: T.walk(self.early_edges, s, self.stops, False, confine)
    T.Timing.early_fall = lambda self, s, confine=None: T.walk(self.fall_edges, s, self.stops, False, confine)
    T.Timing.early_any = lambda self, s, confine=None: T.walk(self.edges, s, self.stops, False, confine)
    T.walk = memo_weight("twalk", T.walk,
                         lambda e, s, st, lng, confine=None: (fp_graph(e), fp_set(st), s, lng, confine),
                         lambda r, a, k: r)

    def ed_key(timing, start, targets, skip, falls=True):
        d = getattr(skip, "__defaults__", None)
        if not d or len(d) != 1 or not isinstance(d[0], (set, frozenset)):
            return None
        return (_fp_timing(timing), start, fp_small(targets), skip.__code__, fp_small(d[0]), falls)
    T.earliest_disturbance = memo_weight("earliest_disturbance", _ed(T), ed_key, None)
    _ED_KEY[0] = ed_key
    T.upstream_data_lag = memo_weight(
        "upstream_data_lag", T.upstream_data_lag,
        lambda timing, back, confine, links, srcs: (_fp_timing(timing), fp_back(back), confine, tuple(links),
                                                    fp_small(srcs)), None, prints=True)

    def sw_key(we, stops, binc, feed, launch, longest, term=None, floor=None, fhit=None):
        if floor is not None or fhit is not None:
            return None
        return (fp_graph(we), fp_set(stops), fp_graph(binc), fp_set(feed), fp_small(skew.AND_NODES), skew.K,
                launch, longest, term)
    skew.walk = memo_levels("skew_walk", skew.walk, sw_key)

    def wf_key(sk, we, stops, binc, feed, launch, longest, and_nodes, floor=None, req_only=None):
        return (fp_graph(we), fp_set(stops), fp_graph(binc), fp_set(feed), fp_small(and_nodes), sk.K, launch,
                longest, tuple(sorted((floor or {}).items())), tuple((req_only or {}).items()))
    ca.walk_floor = memo_levels("walk_floor", ca.walk_floor, wf_key)


_DER = {}            # derived structures of the base run's graphs (routed_graph, side-pruned graphs, incoming arcs)


def side_pruned(edges, side):
    """{src: [(dst, w) ... if (src, dst) not in side]} for every src of edges (Timing's early / fall graphs, rule A''s
    early_edges)."""
    k = ("side_pruned", fp_graph(edges), fp_set(side))
    d = _DER.get(k)
    if d is None or M.gen == 0:
        r = {s: [(x, w) for x, w in lst if (s, x) not in side] for s, lst in edges.items()}
        if M.gen == 0 and d is None:
            _DER[k] = (r, fp_graph(r))
        return r
    pr, fpr = d
    r = dict(pr)
    for s in M.changed:
        if s in edges:
            r[s] = [(x, w) for x, w in edges[s] if (s, x) not in side]
    _IDFP[id(r)] = (r, len(r), "g", fpr)
    return r


def incoming(edges, stops):
    """(binc, srcs_of, feed) as corner_audit / skew.main build them; a forked run copies binc with the arcs of its
    changed pins re-read, and shares srcs_of and feed (no weight in them; nothing writes to them after)."""
    k = ("incoming", fp_graph(edges), fp_set(stops))
    d = _DER.get(k)
    if d is None or M.gen == 0:
        binc, srcs_of = collections.defaultdict(list), collections.defaultdict(set)
        for s, lst in edges.items():
            for x, w in lst:
                binc[x].append((s, w))
                srcs_of[x].add(s)
        feed = {(o, ip) for o in stops for ip, _ in binc.get(o, ()) if o in srcs_of[ip]}
        if M.gen == 0 and d is None:
            _DER[k] = (binc, srcs_of, feed, fp_graph(binc))
            fp_back(srcs_of), fp_set(feed)
        return binc, srcs_of, feed
    pb, ps, pf, fpb = d
    binc = collections.defaultdict(list)
    dict.update(binc, pb)
    wmap = {}
    for s in M.changed:
        for x, w in edges.get(s, ()):
            wmap[(s, x)] = w
    for x in {x for _, x in wmap}:
        binc[x] = [(s, wmap.get((s, x), w)) for s, w in pb[x]]
    _IDFP[id(binc)] = (binc, len(binc), "g", fpb)
    return binc, ps, pf


def call(key, fn, *a):
    """fn(*a), memoized under `key` like a composite: its read set is everything the memoized functions it calls
    read, and a base-run result is reused while none of that changed."""
    e = M.store.get(key)
    if e is not None and _valid(e):
        M.stats["site hit"] += 1
        _note(e[1])
        return e[2]
    M.stats["site " + ("miss" if e is None else "stale")] += 1
    acc = set()
    M.acc.append(acc)
    try:
        r = fn(*a)
    finally:
        M.acc.pop()
    rs = frozenset(acc)
    M.store[key] = (M.gen, rs, r, None)
    _note(rs)
    return r


_ED_KEY = [None]
_SA = {}             # id(table) -> (table, [(stop, arrival)] in table order): the stop entries of a walk table
_ED_DATA = {}        # earliest_disturbance key -> (hit, best, {node: its nearest target}, start, falls)


def _stop_arcs(tab, stops):
    e = _SA.get(id(tab))
    if e is not None and e[0] is tab:
        return e[1]
    sa = [(p, d) for p, d in tab.items() if p in stops]
    _SA[id(tab)] = (tab, sa)
    return sa


def _ed(T):
    """tighten.earliest_disturbance, the same computation: a Dijkstra over the state nodes whose arcs are the walk
    tables (the start's early_fall / early, every other node's early_any), every reachable non-skipped stop labelled
    with its shortest arrival, `hit` the least (label + table arrival) at a target.  Both are unique (shortest
    distances, a minimum), whatever the order of pops and pushes.  Two ways to get them:
      * full: the Dijkstra itself, reading each table's targets and stop entries (not every pin of it);
      * incremental, in a forked run whose every scaled line is at a factor <= 1 (weights only fall, so every table
        arrival falls or stays and the base run's labels are upper bounds): the base run's labels, relaxed again from
        the nodes whose table this run recomputes -- the textbook update for decreased arc weights, exact -- and `hit`
        re-taken over every node.
    CA_FAST_SELFCHECK=1 runs tighten's own function beside it and stops on any difference."""
    orig = T.earliest_disturbance
    check = os.environ.get("CA_FAST_SELFCHECK") == "1"

    def table(timing, s, start, falls):
        if s == start:
            return timing.early_fall(s) if falls else timing.early(s)
        return timing.early_any(s)

    def nearest(tab, targets):
        m = None
        for x in targets:
            v = tab.get(x)
            if v is not None and (m is None or v < m):
                m = v
        return m

    def full(timing, start, targets, skip, falls):
        best, heap, near = {start: 0}, [(0, start)], {}
        stops = timing.stops
        while heap:
            t, s = heapq.heappop(heap)
            if t > best.get(s, t):
                continue
            tab = table(timing, s, start, falls)
            m = nearest(tab, targets)
            if m is not None:
                near[s] = m
            for pin, d in _stop_arcs(tab, stops):
                if pin == s:
                    continue
                at = t + d
                if at < best.get(pin, math.inf) and not skip(pin):
                    best[pin] = at
                    heapq.heappush(heap, (at, pin))
        return best, near

    def incremental(timing, start, targets, skip, falls, old):
        _, best0, near0, _, _ = old
        stale = stale_keys()
        kf = (fp_graph(timing.edges), fp_set(timing.stops))
        ks = (fp_graph(timing.fall_edges if falls else timing.early_edges), kf[1])
        changed = [s for s in best0
                   if (("twalk",) + ((ks + (s, False, None)) if s == start else (kf + (s, False, None)))) in stale]
        best, near = dict(best0), dict(near0)
        new = {}
        for s in changed:
            tab = new[s] = table(timing, s, start, falls)
            m = nearest(tab, targets)
            if m is None:
                near.pop(s, None)
            else:
                near[s] = m
        heap = [(best[s], s) for s in changed]
        heapq.heapify(heap)
        stops = timing.stops
        while heap:
            t, s = heapq.heappop(heap)
            if t > best[s]:
                continue
            tab = new[s] if s in new else table(timing, s, start, falls)
            for pin, d in _stop_arcs(tab, stops):
                if pin == s:
                    continue
                at = t + d
                if at < best.get(pin, math.inf) and not skip(pin):
                    best[pin] = at
                    heapq.heappush(heap, (at, pin))
        return best, near

    def ed(timing, start, targets, skip, falls=True):
        key = _ED_KEY[0](timing, start, targets, skip, falls)
        old = _ED_DATA.get(key) if key is not None else None
        if old is not None and M.gen and M.decrease_only:
            best, near = incremental(timing, start, targets, skip, falls, old)
        else:
            best, near = full(timing, start, targets, skip, falls)
        hit = None
        for s, m in near.items():
            at = best[s] + m
            if hit is None or at < hit:
                hit = at
        if key is not None and M.gen == 0:
            _ED_DATA[key] = (hit, best, near, start, falls)
        if check:
            h2, b2 = orig(timing, start, targets, skip, falls)
            if h2 != hit or b2 != best:
                raise AssertionError("ca_fast: earliest_disturbance differs at %s: %s vs %s" % (start, hit, h2))
        return hit, best
    ed.__wrapped__ = orig
    return ed


def changed_pins(scale, RE_LINK, pin_split):
    """The pins whose outgoing arcs a scale changes: exactly the srcs corner_audit.worker's parse rewrites with a
    weight that differs."""
    if not scale:
        return frozenset()
    out = set()
    for p, (g, _, _, _) in install.raw.items():
        for src, lst in g.items():
            ms = RE_LINK.match(pin_split(src)[0])
            if not ms or ms.group("base") not in scale:
                continue
            f = scale[ms.group("base")]
            for dst, w in lst:
                md = RE_LINK.match(pin_split(dst)[0])
                if md and md.group("base") == ms.group("base") and int(round(w * f)) != w:
                    out.add(src)
                    break
    return frozenset(out)


# ---------------------------------------------------------------- forked runs


class Pool:
    """run(fn, specs, jobs): fn(spec) -> JSON-able, each in a fork of this process, at most `jobs` at a time."""

    def __init__(self):
        self.dir = tempfile.mkdtemp(prefix="ca_fast_")
        self.n = 0
        self.cpu = 0.0

    def run(self, fn, specs, jobs=1):
        specs = list(specs)
        res, running, todo = [None] * len(specs), {}, list(range(len(specs)))
        sys.stdout.flush()
        sys.stderr.flush()
        import gc
        gc.freeze()
        while todo or running:
            while todo and len(running) < max(1, jobs):
                i = todo.pop(0)
                self.n += 1
                path = os.path.join(self.dir, "r%d.json" % self.n)
                pid = os.fork()
                if pid == 0:
                    code = 0
                    try:
                        M.gen = 1
                        r = fn(specs[i])
                        with open(path + ".tmp", "w") as f:
                            json.dump(r, f)
                        os.rename(path + ".tmp", path)
                    except BaseException as e:      # noqa: BLE001 -- reported by the parent
                        import traceback
                        with open(path + ".err", "w") as f:
                            f.write(traceback.format_exc())
                        code = 1
                    finally:
                        os._exit(code)
                running[pid] = (i, path)
            pid, status, ru = os.wait3(0)
            if pid not in running:
                continue
            i, path = running.pop(pid)
            self.cpu += ru.ru_utime + ru.ru_stime
            if status != 0 or not os.path.exists(path):
                err = open(path + ".err").read() if os.path.exists(path + ".err") else "status %d" % status
                for p in running:
                    try:
                        os.kill(p, 9)
                    except OSError:
                        pass
                sys.exit("corner_audit: CA_FAST run failed:\n" + err[-3000:])
            with open(path) as f:
                res[i] = json.load(f)
            os.unlink(path)
        return res
