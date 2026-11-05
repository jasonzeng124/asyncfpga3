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
NOMINAL = {"E": None}          # rule E: the request leg is guarded at GUARD_LO; set from args
SIZED_RULES = set("AEFHIKLBC")  # D is a screen; J has no delay line


# ============================================================== worker (one audit run, fresh process)

def worker(sdf, spec):
    """Run tighten.main, skew.main (verbose), arb_fork.main on `sdf`, with guards patched and chain arcs scaled per
    spec['scale'] {chain base: factor}.  -> JSON-able dict of constraints (+ chain geometry when spec['chains'])."""
    sys.path.insert(0, str(VERIFY))
    sys.argv = [sys.argv[0], str(sdf)]
    import skew                       # imports tighten with argv = [prog, sdf]
    import tighten as T
    import arb_fork
    a_frac, a_min = spec["a_frac"], spec["a_min"]
    T.req_guard = lambda p, t: max(int(a_frac * t), a_min) + T.SLACK
    skew.GUARD_LO, skew.GUARD_HI = spec["glo"], spec["ghi"]
    arb_fork.GUARD_LO, arb_fork.GUARD_HI = spec["glo"], spec["ghi"]
    skew.VERBOSE = True
    scale = spec.get("scale") or {}
    orig_parse = T.parse_sdf

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
        return edges, celltype, n_io, n_ic
    T.parse_sdf = parse
    # A zeroed line prices its own links at 0 ps: tighten's RECOMMENDATION (not its margin) divides by that.
    orig_ll = T.line_links

    def ll(n, *a, **k):
        try:
            return orig_ll(n, *a, **k)
        except ZeroDivisionError:
            return n, 1, "line zeroed by corner_audit"
    T.line_links = ll
    # Rule A's cell_boundary() lets the packer's constant drivers start a data path (tighten.py's own CONST_DRV
    # comment: a net that never transitions cannot start one; starts_reaching() and skew.py already drop them).
    # On xorshift_s50 seed 1 the GND tie-off into ucmpi0's carry chain was the "latest data" by 3.4 ns.
    if spec.get("drop_const", True):
        ocb = T.cell_boundary
        T.cell_boundary = lambda *a, **k: {s for s in ocb(*a, **k) if not T.is_const(s)}
    f_rows = []
    orig_ff = T.audit_fastfall

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
            out["constraints"]["A' %s" % parent] = d
            k = "A %s" % parent
            if k in out["constraints"]:
                out["constraints"][k]["rule"] = "a"        # reported; A' is what is sized on
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
    timing = T.Timing(edges, stops)
    chains = T.find_chains(edges)
    binc, srcs_of = collections.defaultdict(list), collections.defaultdict(set)
    for s, lst in edges.items():
        for d, w in lst:
            binc[d].append((s, w))
            srcs_of[d].add(s)
    feed = {(o, ip) for o in stops for ip, _ in binc.get(o, ()) if o in srcs_of[ip]}
    side = T.fastfall_side_arcs(edges)
    early_edges = {s: [(d, w) for d, w in lst if (s, d) not in side] for s, lst in edges.items()}
    walks = {}

    def at(levels, pin):
        for k, tab in enumerate(levels):
            if pin in tab:
                return tab[pin], k
        return None
    out = {}
    for parent, head, tail, links in T.request_sites(edges, back, chains):
        downstream = T.reaches(edges, tail, stops)
        upstream = {p for p in edges if T.is_output(p) and head in T.reaches(edges, p, stops)}
        own = set(links)
        peers = sorted({p for p in edges if T.is_output(p) and T.pin_split(p)[0].startswith(parent + ".")
                        and T.pin_split(p)[0] not in own and p not in downstream and p not in upstream})
        if not peers:
            continue
        ups = T.upstream_bd_links(T.cell_boundary(edges, back, stops, parent))
        region = (parent,) + ups
        srcs = T.cell_boundary(edges, back, stops, region)
        if not ups or T.check(timing, srcs, peers, tail, T.req_guard, confine=region if ups else parent) is not None:
            continue                                   # common-source pairing: tighten's A is already exact
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
            continue
        worst = None
        for link in ups:
            for c in (link + ".ctl.u.u/O6", link + ".ctl.ub/O6"):
                if c not in stops:
                    continue
                for lng in (False, True):
                    if (c, lng) not in walks:
                        walks[(c, lng)] = skew.walk(edges if lng else early_edges, stops, binc, feed, c, lng)[0]
                r = at(walks[(c, False)], tail)
                # the data may cross one storage node more than the request (the link's latch, when the request
                # leaves the C node directly); a peer first reached deeper than that is a lap, not this token
                ds = [(at(walks[(c, True)][:r[1] + 2], p), p) for p in peers] if r else []
                ds = [(v, p) for v, p in ds if v is not None]
                if r is None or not ds:
                    continue
                (t_d, k_d), peer = max(ds)
                g = T.req_guard(None, t_d)
                m = r[0] - t_d - g
                if worst is None or m < worst[0]:
                    worst = (m, g, r[0], r[1], t_d, k_d, peer, c)
        if worst is None:
            continue
        m, g, t_r, k_r, t_d, k_d, peer, c = worst
        out[parent] = {"rule": "A", "margin": int(m), "knob": parent,
                       "text": "%s %d links  from %s: req %d (%dx)  data %d (%dx, %s)  guard %d  margin %d"
                               % (parent, len(links), c, t_r, k_r, t_d, k_d, T.pin_split(peer)[0], g, m)}
    return out


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
    geo = {}
    for base, links in chains.items():
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

def run_worker(sdf, spec, log=None):
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


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("route_dir", type=pathlib.Path)
    ap.add_argument("--out", type=pathlib.Path)
    ap.add_argument("--guard-lo", type=float, default=0.97)
    ap.add_argument("--guard-hi", type=float, default=1.03)
    ap.add_argument("--a-frac", type=float, default=0.03)
    ap.add_argument("--a-min", type=int, default=50)
    ap.add_argument("--band", type=float, default=0.288)
    ap.add_argument("--cell", default="CARRY4=1,SELMUX2_1=1,SLICE_FFX=1")
    ap.add_argument("--inst-rx", action="append", default=None)
    ap.add_argument("--fast-min", action="store_true", help="band 0, no cell or instance overrides")
    ap.add_argument("--floor", type=int, default=1)
    ap.add_argument("--slack", type=int, default=0, help="every sized constraint must keep >= this many ps")
    ap.add_argument("--all-lines", action="store_true", help="also resize the harness's lines (upipe, uspin)")
    ap.add_argument("--no-size", action="store_true", help="report only")
    ap.add_argument("--max-iter", type=int, default=30)
    ap.add_argument("--rule-a-tighten", action="store_true",
                    help="size on tighten.py's rule A even where it pairs as a bundled channel (no A' re-measure)")
    ap.add_argument("--keep-const-launch", action="store_true",
                    help="rule A exactly as tighten.py: constant drivers may launch the data path")
    a = ap.parse_args()
    if a.inst_rx is None:
        a.inst_rx = [r"\.chain\.g\[\d+\]\.u$:0.21"]
    if a.fast_min:
        a.band, a.cell, a.inst_rx = 0.0, "", []
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
            "drop_const": not a.keep_const_launch, "rule_a_link": not a.rule_a_tighten}
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
        c_rm = max(g["steps"]) if g["steps"] else D
        return max(0, min(D - (n - m) * c_rm, lut_lo + (m - 1) * c_lo))

    def delta(mac, m):          # ps the line gives up (shrink, > 0) or adds (pad, < 0), worst chain of the macro
        ds = [(geo[b]["D"] or 0) - d_new(b, m) for b in lines[mac]]
        return max(ds) if m <= sizes[mac] else min(ds)

    # ---- sensitivity: one run per line with its chains zeroed
    sized_lines = [mac for mac in lines if mac in sizes and sizes[mac] > 0
                   and (a.all_lines or mac.startswith("BD_SZ_UUT_"))]
    measured_lines = [mac for mac in lines if mac in sizes and sizes[mac] > 0]
    sens = {}                   # mac -> {key: dM}
    for mac in sorted(measured_lines):
        r = run_worker(sdf, {**spec, "scale": {b: 0.0 for b in lines[mac]}})
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
        return a.all_lines or k.split()[1].startswith("uut.")
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
            if not on:
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
    rep.append("  audits exit: tighten %s, skew %s, arb_fork %s" % (base["tighten_rc"], base["skew_rc"], base["arb_rc"]))
    rep.append("  per-link cost at this corner: c_lo %s ps (cheapest link-to-link step on the route), lut_lo %d ps; "
               "chain mean steps %s-%s ps" % (c_lo, lut_lo, int(min(means.values())) if means else "-",
                                               int(max(means.values())) if means else "-"))
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
