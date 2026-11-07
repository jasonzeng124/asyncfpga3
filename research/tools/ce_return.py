#!/usr/bin/env python3
"""ce_return.py ROUTED_JSON XRAY_SDF [--corner fast_min|slow_max] [--tsv OUT] [--cap PS] [--dut-prefix P] [--all]

Static audit of the "C-element runt" hazard (research/data/item4/isprime_seed30/README.md).

Every C-element (cells/rtl/bd_ce.v) is one LUT6 whose O6 feeds back to one of its own pins.  Its hold loop is
    loop = IOPATH(feedback pin -> O6) + INTERCONNECT(O6 -> feedback pin).
If, after q changes, a path leaves q, runs through other logic and comes back to change one of the C-element's OTHER
data inputs (not the feedback pin, not rst, not a constant) sooner than that loop, the LUT sees the "release" before
its own feedback has latched the new q: a runt, and a lost token.  For each data pin:
    return = shortest(O6 -> ... -> pin) + IOPATH(pin -> O6)        margin = return - loop
(prjxray gives every LUT pin the same arc, so the two IOPATH terms cancel; they are kept so that the numbers read as
"time at which the pin's change reaches O6", the same as the README's 387 vs 421 ps.)

Timing graph: every INTERCONNECT and IOPATH arc of the prjxray SDF (cells/gls/fid/xray_delay.py, triples
FAST_MIN:SLOW_MIN:SLOW_MAX; fast_min = first number, slow_max = third; rise and fall are identical in these files).
  * cut at sequential cells: arcs from CK (flop CK->Q) are dropped, and a flop has no D/CE -> Q arc, so a path
    ends at a flop's D/CE.  BUFGCTRL/BSCAN arcs are dropped too.
  * soak designs (soak_routed.json next to pnr/soak.json): the DUT's ports are the nets bdc/fusion_bench.routed_signals
    resolves, i.e. exactly the nets cells/gls/fid/soak_fid.py forces/observes.  The GLS forces every DUT input net
    (rst, arg X_req/X_data, result Y_ack), so arcs INTO those nets' drivers are dropped (the harness logic behind
    them is overridden).  The testbench is a 0 ps environment: an observed output can change a forced input at once.
    Turnaround edges (0 ps, marked PORT): arg channel X: X_ack out -> X_req, X_data in; result channel Y:
    Y_req, Y_data out -> Y_ack in.  Nets driven by a constant are never a turnaround.  A wire through the DUT
    (isprime's `end`: p_end_req IS the start_req net) chains turnarounds naturally (start_ack -> start_req ==
    p_end_req -> p_end_ack), which is exactly the isprime seed-30 path.
  * --env harness (soak routes): the board view.  No 0 ps turnaround and no forced-net cut (forcing is GLS-only;
    on the board the harness really drives those nets): returns run through the routed soak harness (upipe...),
    which is in the same JSON/SDF, and a path that leaves the DUT prefix is ENV.  The only arcs cut are the ones
    cut in every mode (flop CK->Q, BUFGCTRL, BSCAN).  This is also what gcd_hw-style routes always get.
  * gcd_hw-style designs (no soak.json): no ports; the on-chip environment is real logic.  A path that leaves the DUT
    hierarchy (--dut-prefix, default auto: "uut." or "urig.udut.") and comes back is marked ENV, else INTERNAL.
The shortest path is STRUCTURAL: a path through another C-element is counted as if that C-element always switched,
which it only does when all its inputs agree.  That is conservative (it can only make return shorter).

C-element identification, reported both ways:
  * structural: a LUT whose O6 net drives one of its own pins, whose function (INIT through X_ORIG_PORT_*, rst at its
    inactive value, constant pins at their constant) is a C-element: every data-input assignment gives 0, 1 or hold
    (q), exactly one gives 1, exactly one gives 0, and those two are bitwise complements (this admits bubbles, as in
    bd_c2n, and rejects a LUT latch, whose set/reset assignments differ in d only).
  * by name: the cell's src attribute is rtl/bd_ce.v.
The analysed set is the union; the counts and disagreements are printed.  rst pin = the pin which, held at one
value, makes the function constant (a reset of either polarity, from INIT); cross-checked with bd_ce.v's port order.

Path column: the cells after q, in order; "<tb>" marks a 0 ps testbench turnaround, and the cell after it is the
driver of the forced input net (a harness cell whose output the GLS overrides).
Output per C-element: its worst data input (min margin), bel, loop, return, margin, class, path (cell names).
Summary line:  CE_RETURN n_ce=.. worst_internal=.. worst_env=.. worst_port=.. n_neg_internal=.. n_neg_env=.. n_neg_port=..
Returns beyond loop+CAP (default 5000 ps) are not searched and print as '-'.
"""
import argparse, heapq, json, re, sys
from collections import defaultdict
from pathlib import Path

RE_INST = re.compile(r"\(INSTANCE\s+(\S*?)\)")
RE_IO = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)")
RE_IC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)")
RE_CT = re.compile(r'\(CELLTYPE\s+"(\S+)"\)')
CUT_TYPES = {"BUFGCTRL", "BSCAN", "SLICE_FFX"}
INF = float("inf")


def un(s):
    return s.replace("\\", "")


def parse_sdf(path):
    """-> ic {dst: (src, (fmin, smax))}, io {cell: {(i, o): (fmin, smax)}}, ctype {cell: type}"""
    ic, io, ctype, inst, ct = {}, defaultdict(dict), {}, None, None
    for ln in open(path):
        m = RE_IC.search(ln)
        if m:
            ic[un(m.group(2))] = (un(m.group(1)), (int(m.group(3)), int(m.group(5))))
            continue
        m = RE_CT.search(ln)
        if m:
            ct = m.group(1); continue
        m = RE_INST.search(ln)
        if m:
            inst = un(m.group(1)); ctype[inst] = ct; continue
        m = RE_IO.search(ln)
        if m and inst is not None:
            io[inst][(m.group(1), m.group(2))] = (int(m.group(3)), int(m.group(5)))
    return ic, io, ctype


# ---------------------------------------------------------------- C-element identification
BD_CE_LINES = None


def bd_ce_roles():
    """src line of each LUT6 in cells/rtl/bd_ce.v -> (module, {Ik: role})"""
    global BD_CE_LINES
    if BD_CE_LINES is None:
        BD_CE_LINES = {}
        f = Path(__file__).resolve().parents[2] / "cells/rtl/bd_ce.v"
        mod = None
        lines = f.read_text().splitlines() if f.exists() else []
        for i, ln in enumerate(lines, 1):
            m = re.match(r"\s*module\s+(\w+)", ln)
            if m:
                mod = m.group(1)
            if "LUT6" in ln:
                txt = " ".join(lines[i - 1:i + 2])
                roles = dict((k, v) for k, v in re.findall(r"\.(I\d)\((\w+|1'b\d)\)", txt))
                BD_CE_LINES[i] = (mod, roles)
    return BD_CE_LINES


def lut_fn(init_bits):
    v = int(init_bits, 2) if set(init_bits) <= {"0", "1"} else int(init_bits)
    return lambda idx: (v >> idx) & 1


def classify(cell, const_net):
    """-> dict(fb=phys pin, rst=phys pin or None, data=[phys pins], ce=bool) or None if no self-feedback"""
    con, at = cell["connections"], cell["attributes"]
    if "O6" not in con or not con["O6"]:
        return None
    qn = con["O6"][0]
    fbs = [p for p, b in con.items() if p.startswith("A") and b and b[0] == qn]
    if not fbs:
        return None
    fb = fbs[0]
    init = cell.get("parameters", {}).get("INIT")
    f = lut_fn(init) if init else None
    logical = {}                                     # phys pin -> logical index
    for p, b in con.items():
        if p.startswith("A") and b:
            ix = [int(x) for x in re.findall(r"I(\d)", at.get("X_ORIG_PORT_" + p, ""))]
            if ix:                                   # one physical pin can carry several logical pins ("I2I1")
                logical[p] = ix
    consts = {p: const_net[con[p][0]] for p in logical if con[p][0] in const_net}
    live = [p for p in logical if p not in consts and p not in fbs]
    res = dict(fb=fb, rst=None, data=list(live), ce=False, q=qn)
    if f is None or fb not in logical:
        return res

    def ev(assign):                                   # phys pin -> value, all logical pins
        idx = 0
        for p, lis in logical.items():
            val = consts.get(p, assign.get(p, 0))
            for li in lis:
                idx |= val << li
        return f(idx)

    def all_assign(pins):
        for k in range(1 << len(pins)):
            yield {p: (k >> j) & 1 for j, p in enumerate(pins)}

    # rst: a live pin that, held at some value, makes the function constant over everything else
    others_all = live + [fb]
    for p in live:
        rest = [x for x in others_all if x != p]
        for v in (0, 1):
            outs = {ev({**a, p: v}) for a in all_assign(rest)}
            if len(outs) == 1:
                res["rst"], res["rst_active"] = p, v
                break
        if res["rst"]:
            break
    data = [p for p in live if p != res["rst"]]
    res["data"] = data
    if len(data) < 2:
        return res
    rstv = {} if res["rst"] is None else {res["rst"]: 1 - res["rst_active"]}
    sets, resets, bad = [], [], False
    for a in all_assign(data):
        o0, o1 = ev({**a, **rstv, fb: 0}), ev({**a, **rstv, fb: 1})
        if (o0, o1) == (1, 1):
            sets.append(a)
        elif (o0, o1) == (0, 0):
            resets.append(a)
        elif (o0, o1) != (0, 1):
            bad = True
    if not bad and len(sets) == 1 and len(resets) == 1 and all(sets[0][p] != resets[0][p] for p in data):
        res["ce"] = True
    return res


# ---------------------------------------------------------------- ports (soak designs)
def soak_ports(routed_json):
    """-> (forced bits, [(observed bit, [forced bits it turns around to], label)]) or None"""
    outdir = Path(routed_json).resolve().parent.parent
    sj = outdir / "pnr/soak.json"
    if Path(routed_json).name != "soak_routed.json" or not sj.exists():
        return None
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "bdc"))
    import fusion_bench as FB                                     # noqa: E402
    syn = json.loads(sj.read_text())["modules"]
    top = [k for k in syn if re.match(r"bdc_\w+_top$", k)]
    if len(top) != 1:
        sys.exit("ce_return: cannot find bdc_*_top in %s" % sj)

    class F:
        name = top[0][4:-4]
    sig = FB.routed_signals(outdir, F)
    pdir = syn[top[0]]["cells"]["uut"]["port_directions"]
    forced = set()
    for p, d in pdir.items():
        if d == "input":
            forced.update(sig[p])
    chans = defaultdict(dict)
    for p in pdir:
        m = re.match(r"(.*)_(req|ack|data)$", p)
        if m:
            chans[m.group(1)][m.group(2)] = p
    turn = []
    for ch, ps in chans.items():
        if "req" not in ps or "ack" not in ps:
            continue
        if pdir[ps["req"]] == "input":                           # argument channel: ack out -> req, data in
            outs, ins = [ps["ack"]], [ps["req"]] + ([ps["data"]] if "data" in ps else [])
        else:                                                   # result channel: req, data out -> ack in
            outs, ins = [ps["req"]] + ([ps["data"]] if "data" in ps else []), [ps["ack"]]
        tgt = [b for p in ins for b in sig[p]]
        for p in outs:
            for b in sig[p]:
                turn.append((b, tgt, "%s->%s" % (p, "/".join(ins))))
    return forced, turn


# ---------------------------------------------------------------- analysis
def build(routed_json, sdf, corner, dut_prefix=None, all_ce=False, env="tb", ff_async=None):
    ci = 0 if corner == "fast_min" else 1
    top = json.loads(Path(routed_json).read_text())["modules"]["top"]
    cells = top["cells"]
    ic, io, ctype = parse_sdf(sdf)
    const_net, driver, sinks = {}, {}, defaultdict(list)
    for cn, c in cells.items():
        for p, bl in c["connections"].items():
            if not bl:
                continue
            if c["port_directions"].get(p) == "output":
                driver[bl[0]] = (cn, p)
                if c["type"] == "PSEUDO_GND":
                    const_net[bl[0]] = 0
                if c["type"] == "PSEUDO_VCC":
                    const_net[bl[0]] = 1
            else:
                sinks[bl[0]].append((cn, p))
    for n in list(const_net):
        pass

    def drv_node(bit):                    # the SDF name of the driver pin of a net
        for cn, p in sinks.get(bit, []):
            k = cn + "/" + p
            if k in ic:
                return ic[k][0]
        d = driver.get(bit)
        return d[0] + "/" + d[1] if d else None

    ports = soak_ports(routed_json) if env == "tb" else None
    blocked = set()
    extra = defaultdict(list)                     # node -> [(node, 0, label)]
    if ports:
        forced, turn = ports
        for b in forced:
            if b not in const_net:
                n = drv_node(b)
                if n:
                    blocked.add(n)
        for ob, tg, lab in turn:
            if ob in const_net:
                continue
            a = drv_node(ob)
            for b in tg:
                if b in const_net:
                    continue
                t = drv_node(b)
                if a and t and t != a:
                    extra[a].append((t, lab))
    adj = defaultdict(list)
    for dst, (src, d) in ic.items():
        adj[src].append((dst, d[ci], None))
    for cell, arcs in io.items():
        if ctype.get(cell) in CUT_TYPES:
            continue
        for (i, o), d in arcs.items():
            if i == "CK":
                continue
            if cell + "/" + o in blocked:
                continue
            adj[cell + "/" + i].append((cell + "/" + o, d[ci], None))
    for a, lst in extra.items():
        for t, lab in lst:
            adj[a].append((t, 0, lab))
    if ff_async is not None:
        # prjxray's SDF gives a SLICE_FFX only CK->Q, so an asynchronous clear/preset (the bench's req_clr) would
        # end the search.  --ff-async PS adds SR->Q = PS on every SLICE_FFX (a sync SR too: adding arcs can only
        # shorten a return, so the margin stays a lower bound when PS is at most the real SR->Q).
        for cn, c in cells.items():
            if c["type"] == "SLICE_FFX" and c["connections"].get("SR") and c["connections"].get("Q"):
                adj[cn + "/SR"].append((cn + "/Q", ff_async, None))

    if dut_prefix is None:
        dut_prefix = "uut." if any(n.startswith("uut.") for n in cells) else \
            "urig.udut." if any(n.startswith("urig.udut.") for n in cells) else \
            "bridge_i.udut." if any(n.startswith("bridge_i.udut.") for n in cells) else ""
    roles = bd_ce_roles()
    n_struct = n_init = n_name = 0
    ces, disagree = [], []
    for cn, c in cells.items():
        if c["type"] != "SLICE_LUTX":
            continue
        r = classify(c, const_net)
        src = c["attributes"].get("src", "")
        byname = "bd_ce.v" in src
        n_name += byname
        if r is None:
            if byname:
                disagree.append((cn, "name-only(no feedback)"))
            continue
        n_struct += 1
        n_init += r["ce"]
        if r["ce"] != byname:
            disagree.append((cn, "INIT-CE" if r["ce"] else "name-only"))
        if not (r["ce"] or byname):
            continue
        # cross-check rst/feedback against bd_ce.v's port order
        m = re.search(r"bd_ce\.v:(\d+)", src)
        if m:
            ln = int(m.group(1))
            rl = roles.get(ln) or roles.get(ln - 1)
            if rl:
                orig = {p: c["attributes"].get("X_ORIG_PORT_" + p, "").split()[0] if
                        c["attributes"].get("X_ORIG_PORT_" + p) else "" for p in c["connections"]}
                want_fb = [p for p, o in orig.items() if rl[1].get(o) == "q"]
                want_rst = [p for p, o in orig.items() if rl[1].get(o) == "rst"]
                if want_fb and want_fb[0] != r["fb"]:
                    disagree.append((cn, "fb %s vs bd_ce.v %s" % (r["fb"], want_fb[0])))
                if want_rst and r["rst"] and want_rst[0] != r["rst"]:
                    disagree.append((cn, "rst %s vs bd_ce.v %s" % (r["rst"], want_rst[0])))
        r["name"], r["bel"], r["mod"] = cn, c["attributes"].get("NEXTPNR_BEL", "?"), \
            (roles.get(int(m.group(1)), ("?",))[0] if m else "?")
        ces.append(r)
    info = dict(n_struct=n_struct, n_init=n_init, n_name=n_name, disagree=disagree, dut_prefix=dut_prefix,
                n_ports=len(extra), blocked=len(blocked), soak=bool(ports), env=env)
    an = [r for r in ces if all_ce or r["name"].startswith(dut_prefix)]
    info["n_outside"] = len(ces) - len(an)
    return adj, io, ic, ci, an, info


def analyse(adj, io, ic, ci, r, dut_prefix, cap, times=False):
    cn = r["name"]
    o = cn + "/O6"
    fbp = cn + "/" + r["fb"]
    arc = lambda p: io[cn][(p, "O6")][ci]
    if fbp not in ic or (r["fb"], "O6") not in io.get(cn, {}):
        return None
    loop = arc(r["fb"]) + ic[fbp][1][ci]
    targets = {cn + "/" + p: p for p in r["data"] if (p, "O6") in io.get(cn, {})}
    limit = loop + cap
    dist, pred, port = {o: 0}, {}, {}
    pq, left = [(0, o)], set(targets)
    while pq and left:
        d, u = heapq.heappop(pq)
        if d > dist.get(u, INF) or d > limit:
            if d > limit:
                break
            continue
        if u in left:
            left.discard(u)
            continue                                  # never pass through our own pin -> O6
        for v, w, lab in adj.get(u, ()):
            nd = d + w
            if nd < dist.get(v, INF):
                dist[v], pred[v], port[v] = nd, u, lab
                heapq.heappush(pq, (nd, v))
    rows = []
    for t, p in targets.items():
        if t not in dist or dist[t] > limit:
            rows.append(dict(pin=p, ret=None))
            continue
        path, labs, x = [], [], t
        while x != o:
            path.append(x)
            if port[x]:
                labs.append(port[x])
                path.append("<tb>/")
            x = pred[x]
        path.reverse()
        names, tl = [], []
        for n in path[:-1]:
            c = n.rsplit("/", 1)[0] if n != "<tb>/" else "<tb>"
            if not names or names[-1] != c:
                names.append(c); tl.append(None)
            if n != "<tb>/":
                tl[-1] = dist[n]                      # arrival at this cell's last pin on the path (its output)
        cells_on = [c for c in names if c != "<tb>"]
        cls = "PORT" if labs else ("ENV" if any(not n.startswith(dut_prefix) for n in cells_on) else "INTERNAL")
        ret = dist[t] + arc(p)
        if times:
            names = [c if tt is None else "%s@%d" % (c, tt) for c, tt in zip(names, tl)] + ["%s/%s@%d" % (cn, p, dist[t])]
        rows.append(dict(pin=p, ret=ret, arr=dist[t], cls=cls, path=names, ports=list(reversed(labs)),
                         margin=ret - loop))
    return loop, rows


def run(routed_json, sdf, corner, cap=5000, dut_prefix=None, all_ce=False, out=sys.stdout, tsv=None, quiet=False,
        env="tb", times=False, ff_async=None):
    adj, io, ic, ci, ces, info = build(routed_json, sdf, corner, dut_prefix, all_ce, env, ff_async)
    dp = info["dut_prefix"]
    pr = (lambda *a: None) if quiet else (lambda s: print(s, file=out))
    pr("# ce_return %s %s corner=%s" % (routed_json, sdf, corner))
    pr("# C-elements: self-feedback LUTs %d, INIT is a C-element %d, src bd_ce.v %d, analysed %d (prefix '%s', %d "
       "outside skipped); %d disagreements%s" % (info["n_struct"], info["n_init"], info["n_name"], len(ces), dp,
                                                info["n_outside"], len(info["disagree"]),
                                                (": " + ", ".join("%s(%s)" % d for d in info["disagree"][:8]))
                                                if info["disagree"] else ""))
    pr("# env=%s ports: %s, %d forced-net drivers cut, %d turnaround sources" %
       (env, "soak tb (0 ps turnaround)" if info["soak"] else
        ("none: routed harness/environment kept whole, no arc cut beyond flops/BUFG/BSCAN" if env == "harness" or
         not dp.startswith("uut.") else "none (on-chip environment)"), info["blocked"], info["n_ports"]))
    worst = {"INTERNAL": None, "ENV": None, "PORT": None}
    nneg = {"INTERNAL": 0, "ENV": 0, "PORT": 0}
    res = []
    for r in sorted(ces, key=lambda r: r["name"]):
        a = analyse(adj, io, ic, ci, r, dp, cap, times)
        if a is None:
            pr("%s\t%s\tNO_LOOP_TIMING" % (r["name"], r["bel"]))
            continue
        loop, rows = a
        got = [x for x in rows if x["ret"] is not None]
        for cls in worst:
            cr = [x for x in got if x["cls"] == cls]
            if cr:
                m = min(x["margin"] for x in cr)
                worst[cls] = m if worst[cls] is None else min(worst[cls], m)
                nneg[cls] += m < 0
        w = min(got, key=lambda x: x["margin"]) if got else None
        res.append((r, loop, w, rows))
    res.sort(key=lambda t: t[2]["margin"] if t[2] else INF)
    pr("#instance\tbel\tmod\tfb\trst\tpin\tloop\treturn\tmargin\tclass\tports\tpath")
    lines = []
    for r, loop, w, rows in res:
        if w is None:
            ln = "%s\t%s\t%s\t%s\t%s\t-\t%d\t-\t-\t-\t-\t-" % (r["name"], r["bel"], r["mod"], r["fb"], r["rst"], loop)
        else:
            ln = "%s\t%s\t%s\t%s\t%s\t%s\t%d\t%d\t%d\t%s\t%s\t%s" % (
                r["name"], r["bel"], r["mod"], r["fb"], r["rst"], w["pin"], loop, w["ret"], w["margin"], w["cls"],
                ",".join(w["ports"]) or "-", " > ".join(w["path"]))
        lines.append(ln)
        pr(ln)
    if tsv:
        with open(tsv, "w") as f:
            f.write("instance\tbel\tmod\tfb\trst\tpin\tloop\treturn\tmargin\tclass\tports\tpath\n")
            f.write("\n".join(lines) + "\n")
    fmt = lambda v: "-" if v is None else "%d" % v
    summ = dict(n_ce=len(res), worst_internal=worst["INTERNAL"], worst_env=worst["ENV"], worst_port=worst["PORT"],
                n_neg_internal=nneg["INTERNAL"], n_neg_env=nneg["ENV"], n_neg_port=nneg["PORT"],
                negs=[(r["name"], w["cls"], w["margin"], w["pin"], loop, w["ret"], ",".join(w["ports"]))
                      for r, loop, w, rows in res if w and w["margin"] < 0],
                info=info,
                per={r["name"]: (w["cls"], w["margin"], w["pin"], loop, w["ret"], " > ".join(w["path"]))
                     for r, loop, w, rows in res if w})
    print("CE_RETURN n_ce=%d worst_internal=%s worst_env=%s worst_port=%s n_neg_internal=%d n_neg_env=%d "
          "n_neg_port=%d" % (len(res), fmt(worst["INTERNAL"]), fmt(worst["ENV"]), fmt(worst["PORT"]),
                             nneg["INTERNAL"], nneg["ENV"], nneg["PORT"]), file=out)
    return summ


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("routed_json")
    ap.add_argument("sdf")
    ap.add_argument("--corner", choices=["fast_min", "slow_max"], default="fast_min")
    ap.add_argument("--tsv")
    ap.add_argument("--cap", type=int, default=5000, help="search returns up to loop+CAP ps (default 5000)")
    ap.add_argument("--dut-prefix", default=None)
    ap.add_argument("--all", action="store_true", help="also analyse C-elements outside the DUT prefix")
    ap.add_argument("--env", choices=["tb", "harness"], default="tb",
                    help="soak routes: tb = GLS view (forced DUT ports, 0 ps testbench turnaround, PORT); harness = "
                         "board view (no turnaround edges, no forced-net cuts: returns run through the routed soak "
                         "harness and are classed ENV)")
    ap.add_argument("--times", action="store_true", help="annotate each path cell with its arrival time (ps after q)")
    ap.add_argument("--ff-async", type=int, default=None, metavar="PS",
                    help="add SR->Q = PS ps on every SLICE_FFX (prjxray gives none); 0 = a lower bound on the return "
                         "through an async clear such as gen_bench's req_clr")
    a = ap.parse_args()
    run(a.routed_json, a.sdf, a.corner, a.cap, a.dut_prefix, a.all, tsv=a.tsv, env=a.env, times=a.times,
        ff_async=a.ff_async)


if __name__ == "__main__":
    main()
