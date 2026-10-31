#!/usr/bin/env python3
"""oblgen (probe C-8w): the capstone's Ops-named timing obligations, and which tcheck rows check them.

(1) Emits, from the concrete Lean network `Formal/Net/CapstoneNet.lean` (465 channels, 367
    operators), one record per Ops-named obligation: H_BUNDLE per channel, H_STEER_SEL / H_MUX_SEL
    / H_MUXN_SEL per select, the link stage's H_LATCH_COMB halves (Sep+SetupHold, Hold, open
    width), the arbiter stage's H_ARB / H_AMERGE_RTZ / A3 pulse / H_FF_DRAINED, the mux's
    H_MUX_RTZ / X4 / M3, the join's C7, and the request-line drain (H_QUIESCENT of the TxCover
    premise) per matched delay. Each record carries the Lean reference (channel or operator index),
    the bdc Verilog instance it lives in, and the tcheck rule(s) expected to check it.
(2) Reads tcheck's per-row results for the 4 gcd_hw routes (formal/tools/tcheck/results) and
    matches rows to obligations by instance name; reports unmatched obligations and unmatched rows.

Sources, all read-only:
* the Lean network: parsed from CapstoneNet.lean (chanNames, ops). netgen.py (C-8m) is re-run into
  a scratch file and must reproduce CapstoneNet.lean byte for byte (drift check); its globals give
  the GcdHw rule behind each operator.
* bdc's names: mlir2lean's Graph (bdc's own parser, fusion plan and Emitter; `instname`, `vname`,
  `linked`, `depth`), and the emitted gcd_kernel.v of the tcheck route tree (existence check).

Outputs (formal/tools/oblgen/out/): obligations.tsv, matches.tsv, unmatched_obl.tsv,
unmatched_rows.tsv, summary.txt.  `--check` compares against the committed out/ files.
"""
import os, re, sys, runpy, io, contextlib, collections, tempfile, filecmp, shutil

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
LEAN = os.path.join(ROOT, "formal", "lean")
NETLEAN = os.path.join(LEAN, "Formal", "Net", "CapstoneNet.lean")
NETGEN = os.path.join(LEAN, "Wip", "C8m", "netgen.py")
RES = os.path.join(ROOT, "formal", "tools", "tcheck", "results")
KV = os.path.join(ROOT, "formal", "tools", "tcheck", "build", "tree_d", "build", "gen", "gcd_kernel.v")
SEEDS = ["d", "2", "3", "4"]
DUT = "urig.udut."

for k in ["BDC_OP_FUSION", "BDC_CONST_FOLD", "BDC_FORK_FUSION", "BDC_MAX_FUSE_NODES", "BDC_PROBE",
          "BDC_RING_PAD", "BDC_LINK_FASTFALL", "BDC_SELECT_PAD"]:
    os.environ.pop(k, None)


def run_netgen():
    tmp = tempfile.mkdtemp()
    dst = os.path.join(tmp, "CapstoneNet.lean")
    argv = sys.argv
    sys.argv = [NETGEN, dst]
    err = io.StringIO()
    try:
        with contextlib.redirect_stderr(err):
            G = runpy.run_path(NETGEN, run_name="netgen")
    finally:
        sys.argv = argv
    same = filecmp.cmp(dst, NETLEAN, shallow=False)
    shutil.rmtree(tmp)
    if not same:
        raise SystemExit("oblgen: netgen.py no longer reproduces CapstoneNet.lean (drift)")
    return G


def parse_lean():
    txt = open(NETLEAN).read()
    names = re.findall(r'"([^"]*)"', re.search(r"def chanNames : List String := \[(.*?)\]\n", txt).group(1))
    body = re.search(r"def ops : List \(K NC\) := \[\n(.*?)\n\]\n", txt, re.S).group(1)
    ops = []
    for line in body.split(",\n"):
        line = line.strip()
        m = re.match(r"K\.(\w+) (.*)$", line)
        kind, rest = m.group(1), m.group(2)
        toks = re.findall(r"\[[^\]]*\]|\(\d+, \d+\)|\d+|\S+", rest)
        def L(s): return [int(x) for x in re.findall(r"\d+", s)]
        if kind == "forkG": ins, outs = [int(toks[0])], L(toks[1])
        elif kind == "forkH":
            ins = [int(toks[0])]
            outs = [int(a) for a, _ in re.findall(r"\((\d+), (\d+)\)", rest.split("]")[0])]
        elif kind in ("join", "bjoin"): ins, outs = L(toks[0]), [int(toks[1])]
        elif kind in ("steerC", "steerD"): ins, outs = [int(toks[0])], [int(toks[1]), int(toks[2])]
        elif kind == "mux": ins, outs = [int(t) for t in toks[0:3]], [int(toks[3])]
        elif kind == "muxn": ins, outs = [int(t) for t in toks[0:4]], [int(toks[4])]
        elif kind == "amerge": ins, outs = [int(toks[0]), int(toks[1])], [int(toks[2])]
        elif kind == "link": ins, outs = [int(toks[0])], [int(toks[1])]
        elif kind == "src": ins, outs = [], [int(toks[0])]
        elif kind == "sink": ins, outs = [int(toks[0])], []
        else: raise SystemExit(f"unknown kind {kind}")
        ops.append((kind, ins, outs))
    return names, ops


def main():
    check = "--check" in sys.argv
    G = run_netgen()
    names, lops = parse_lean()
    nops = G["ops"]
    assert len(lops) == len(nops) == 367 and len(names) == 465
    for (k, ins, outs), o in zip(lops, nops):   # Lean term and generator agree operator by operator
        assert k == o[0] and ins == G["op_ins"](o) and outs == G["op_outs"](o), (k, ins, outs, o)
    g = G["g"]; rules = G["rules"]; members = G["members"]; seg = G["seg"]; src_of = G["src_of"]
    prod_rule = G["prod_rule"]
    em = g.em
    import emit as E   # bdc's emitter module, as imported by mlir2lean
    nodes = g.func.nodes
    ssa_node = {}
    for n in nodes:
        for r in n.results: ssa_node[r] = n
    def inst_of_ssa(ssa):   # the bdc instance producing the (alias-resolved) SSA value
        n = ssa_node[ssa]; return E.instname(n, nodes.index(n))
    chname = g.chname
    prod = {}; cons = {}
    for i, (k, ins, outs) in enumerate(lops):
        for c in ins: cons[c] = i
        for c in outs: prod[c] = i
    ghost = G["ghost"]; hch = G["hch"]
    # ---- per-channel physical description
    def rep_of(name):
        m = re.match(r"g(\d+)\.(\d+)$", name); return (int(m.group(1)), int(m.group(2))) if m else None
    linkstages = {}   # (rep, k) -> (instance prefix of stage k)
    unordered = []
    for rep, ms in members.items():
        st = []
        lk = [(c, v) for c in ms for v in sorted(em.linked) if g.A(v) in g.chan and g.chan[g.A(v)] == c]
        if len([1 for c, _ in lk]) > 1: unordered.append(rep)
        for c, v in lk:
            n = em.depth.get(v, 1); base = f"ulink_{E.vname(v)}"
            st += [base] if n == 1 else [f"{base}.many.stage[{i}].u" for i in range(n)]
        assert len(st) == len(seg[rep]) - 1, (rep, st, seg[rep])
        for i, s in enumerate(st): linkstages[(rep, i)] = s
    kv = open(KV).read() if os.path.exists(KV) else ""
    def exists(inst):
        top = inst.split(".")[0]
        return (" " + top + " (") in kv or (" " + top + "(") in kv or re.search(r"\b" + re.escape(top) + r"\b", kv) is not None
    # instance of an operator
    def cm_name(res):
        return inst_of_ssa(chname[res])
    def op_inst(i):
        k, ins, outs = lops[i]; o = nops[i]
        if k == "link":
            rep, kk = rep_of(names[ins[0]]); return linkstages[(rep, kk)]
        if k in ("join",): return inst_of_ssa(chname[o[7]])
        if k == "forkH": return inst_of_ssa(chname[o[5][0]])
        if k == "forkG":
            nm = names[outs[0]]; rep, _ = rep_of(nm)
            r = rules[prod_rule[rep][0]]
            if r[0] == "cm": return cm_name(r[2]) + ("_f" if len([x for x in rules if x[0] == "cm" and x[2] == r[2]]) > 1 else "")
            return inst_of_ssa(chname[rep])
        if k == "bjoin": return inst_of_ssa(chname[rules[int(names[outs[0]][1:])][3]]) + "(join)"
        if k in ("steerC", "steerD"): return inst_of_ssa(chname[rules[int(names[ins[0]][1:])][3]])
        if k in ("mux", "muxn"): return inst_of_ssa(chname[o[8] if k == "mux" else o[7]])
        if k == "amerge":
            nm = names[outs[0]]; res = int(re.sub(r"^(z|acc)", "", nm))
            n3 = len([x for x in rules if x[0] == "cm" and x[2] == res])
            stage = "uarb1" if (nm.startswith("acc") or n3 == 2) else "uarb2"
            return cm_name(res) + "." + stage
        if k == "src": return "env:" + ["a", "b", "start"][o[2]]
        if k == "sink": return "env:sink" if names[ins[0]] in (names[G["last"](3)], names[G["last"](250)]) else inst_of_ssa_sink(i)
        return "?"
    def inst_of_ssa_sink(i):
        c = lops[i][1][0]; rep, _ = rep_of(names[c])
        for l, r in enumerate(rules):
            if r[0] == "sink" and r[1] in members[rep]:
                n = [x for x in nodes if x.op == "sink" and x.attrs.get("handshake.name") == r[2]][0]
                return E.instname(n, nodes.index(n))
        return "?"
    insts = [op_inst(i) for i in range(len(lops))]
    # ---- obligations
    obl = []
    def add(oid, name, lean, inst, expect, note=""):
        obl.append(dict(id=oid, name=name, lean=lean, inst=inst, expect=expect, note=note))
    for c, nm in enumerate(names):
        p = prod[c]; pk = lops[p][0]; ck = lops[cons[c]][0]
        cons_inst = insts[cons[c]]
        isctl = False
        r = rep_of(nm)
        if r is not None: isctl = hch[r[0]] in ghost and G["desc"][c][0] != "hist"
        base = f"H_BUNDLE({nm})"
        lean = f"chan {c} prod op {p} ({pk}) cons op {cons[c]} ({ck})"
        if pk == "join":
            add(f"B{c}", base, lean, insts[p], "A", "physical capture at the cell's matched delay (held_of_checkArr); line drain F/Fd is the TxCover H_QUIESCENT premise")
        elif pk in ("mux", "muxn"):
            add(f"B{c}", base, lean, insts[p], "A", "mux output matched delay")
        elif pk == "amerge":
            if nm.startswith("acc"):
                add(f"B{c}", base, lean, insts[p], "none", "3-input cm stage-1 bus (B's H_BUNDLED_IDX); no matched delay between R0 and acc_req (C-8l)")
            else:
                add(f"B{c}", base, lean, insts[p].rsplit(".", 1)[0], "A", "arbiter composite bus 2*data+won (ghost); A checks index/data vs R0 at bdc_amerge's delay")
        elif pk == "link":
            add(f"B{c}", base, lean, insts[p], "derived:link_held", "Ops: Link.link_held from the input's Held; physical: the stage's H_LATCH_COMB rows")
        elif pk in ("forkH",):
            add(f"B{c}", base, lean, insts[p], "derived:fork_held", "")
        elif pk == "forkG":
            add(f"B{c}", base, lean, insts[p], "derived:fork_held", "control/ghost bus or arbiter index copy")
        elif pk == "steerD":
            add(f"B{c}", base, lean, insts[p], "derived:steer_held", "")
        elif pk == "steerC":
            add(f"B{c}", base, lean, insts[p], "ghost:W=0", "control steer output, ghost value 0")
        elif pk == "bjoin":
            add(f"B{c}", base, lean, insts[p], "derived:join_held;E", "Ops: join of (cond, data); physical: the steer select pin, rule E")
        elif pk == "src":
            add(f"B{c}", base, lean, insts[p], "derived:src_held", "H_SRC")
        else:
            add(f"B{c}", base, lean, insts[p], "?", "")
    for i, (k, ins, outs) in enumerate(lops):
        I = insts[i]; lean = f"op {i} ({k})"
        if k in ("steerD", "steerC"):
            add(f"S{i}", f"H_STEER_SEL({names[ins[0]]})", lean, I, "E", "select (cond bit of the joined bus) settled at the steer LUT before req")
        elif k == "mux":
            add(f"S{i}", f"H_MUX_SEL({names[ins[0]]})", lean, I, "E", "select settled at uj0/uj1 before req")
            add(f"M{i}", f"H_MUX_RTZ({I})", lean, I, "X|Xi|Xic", "B's X1 / A3 pulse")
            add(f"K{i}", f"X4({I})", lean, I, "K", "ctl_req -> {uj0,uj1} fork")
            add(f"N{i}", f"M3({I})", lean, I, "none", "merge isochrony: unchecked")
            ln = [l for l in kv.splitlines() if l.strip().startswith("bd_mux") and l.rstrip().endswith(f" {I} (")]
            plain = len(ln) == 1 and "FASTFALL" not in ln[0]
            if plain:
                add(f"D{i}", f"H_QUIESCENT_REQ({I}.udly)", lean, I + ".udly", "argued:FASTFALL=0", "plain bd_delay (FASTFALL=0): its output falls only after every element fell, so the line is drained when the channel closes (argued, not checked)")
            else:
                add(f"D{i}", f"H_QUIESCENT_REQ({I}.udly)", lean, I + ".udly", "F|Fd", "request line drained before the next launch (TxCover premise of B for its output)")
        elif k == "muxn":
            add(f"S{i}", f"H_MUXN_SEL({names[ins[0]]})", lean, I, "E", "index held at umux21's select")
            add(f"M{i}", f"H_MUX_RTZ({I})", lean, I, "X|Xi|Xic", "")
            add(f"D{i}", f"H_QUIESCENT_REQ({I}.udly)", lean, I + ".udly", "F|Fd", "")
        elif k == "link":
            rep_, _ = rep_of(names[ins[0]])
            w0 = em.width(chname[rep_]) == 0 if chname[rep_] in em.ch else False
            if w0:
                add(f"I{i}", f"Sep+SetupHold({names[ins[0]]}->{names[outs[0]]})", lean, I + ".ctl.u.u", "vacuous:W=0|I", "control channel: the stage latches a constant")
                add(f"H{i}", f"Hold({names[ins[0]]}->{names[outs[0]]})", lean, I + ".ctl.u.u", "vacuous:W=0|H|Hc", "control channel: the stage latches a constant")
                add(f"W{i}", f"OpenWidth({I})", lean, I + ".ctl.u.u", "W(aggregate)", "8e open width; tcheck reports W only as a per-route minimum")
                continue
            add(f"I{i}", f"Sep+SetupHold({names[ins[0]]}->{names[outs[0]]})", lean, I + ".ctl.u.u", "I", "H_LATCH_COMB setup half (8a Sep, SetupHold; B L1,L2,P1,P2)")
            add(f"H{i}", f"Hold({names[ins[0]]}->{names[outs[0]]})", lean, I + ".ctl.u.u", "H|Hc", "H_LATCH_COMB hold half (8a Hold; B L3, D4)")
            add(f"W{i}", f"OpenWidth({I})", lean, I + ".ctl.u.u", "W(aggregate)", "8e open width; tcheck reports W only as a per-route minimum")
        elif k == "amerge":
            cm, st = I.rsplit(".", 1)
            add(f"J{i}", f"H_ARB({I})", lean, f"{I}#2", "J|Jx", "A0 fork, B's A1")
            add(f"Z{i}", f"H_AMERGE_RTZ({I})", lean, f"{I}#2", "Z", "")
            add(f"X{i}", f"A3pulse({I})", lean, f"{I}.ua1.u|{I}.ua2.u", "X|Xc|Xm", "")
            if not names[outs[0]].startswith("acc"):
                add(f"F{i}", f"H_FF_DRAINED({cm}.udly)", lean, cm + ".udly", "Fd|F", "")
        elif k == "join":
            add(f"C{i}", f"C7({I})", lean, I, "none", "C-tree depth latency: unchecked")
            add(f"D{i}", f"H_QUIESCENT_REQ({I}.udly)", lean, I + ".udly", "F|Fd", "")
    obl.append(dict(id="R*", name="H_CEL_SI premise (feedback first, C2)", lean="every C-element of every cell",
                    inst="*", expect="R|Rc(aggregate)", note="per-route minimum only"))
    # ---- tcheck rows
    rows = []
    def rd(fn):
        p = os.path.join(RES, fn)
        if not os.path.exists(p): return []
        L = open(p).read().splitlines(); hdr = L[0].split("\t")
        return [dict(zip(hdr, l.split("\t"))) for l in L[1:]]
    def mn(r, cols):
        v = []
        for c in cols:
            m = re.match(r"\s*(-?\d+)", r.get(c) or "")
            if m: v.append(int(m.group(1)))
        return min(v) if v else None
    for s in SEEDS:
        for r in rd(f"compare5_{s}.tsv"):
            rows.append(dict(seed=s, rule=r["flavour"] if r["rule"] in ("E", "J") else r["rule"], key=r["row"].replace(DUT, ""),
                             fastG=r.get("tc_fastG"), slowG=r.get("tc_slowG"), worst=mn(r, ["tc_fastG", "tc_slowG"]),
                             unguarded=mn(r, ["tc_fast", "tc_slow"]), src=f"compare5_{s}"))
        for r in rd(f"compare_{s}.tsv"):
            rows.append(dict(seed=s, rule=r["rule"], key=r["controller"].replace(DUT, ""), fastG=r["tc_fastG"], slowG=r["tc_slowG"],
                             worst=mn(r, ["tc_fastG", "tc_slowG"]), unguarded=mn(r, ["tc_fast", "tc_slow"]), src=f"compare_{s}"))
        for r in rd(f"cmpcert5_{s}.tsv"):
            pass   # same Hc rows as compare_ (cert late side); verdicts per variant only
    for fn in ("r10k_rows.tsv", "r10l_rows.tsv"):
        for r in rd(fn):
            rows.append(dict(seed=r["seed"], rule=r["rule"], key=r["obligation"], fastG=r["fastG"], slowG=r["slowG"],
                             worst=mn(r, ["fastG", "slowG"]), unguarded=mn(r, ["fast", "slow"]), src=fn))
    # ---- matching
    def head(key):
        k = key.split(" ")[0]
        return k
    by_inst = collections.defaultdict(list)
    for o in obl:
        for alt in o["inst"].split("|"): by_inst[alt].append(o)
    def rule_ok(o, rule):
        ex = o["expect"].replace("(aggregate)", "")
        alts = set(re.split(r"[|;]", ex))
        return rule in alts
    def cands(row):
        k = head(row["key"]); rule = row["rule"]
        out = []
        if rule in ("A",):
            out = [o for o in obl if o["id"].startswith("B") and o["inst"] == k and o["expect"] == "A"]
        elif rule in ("E", "E0"):
            base = re.sub(r"\.(u\$LUT\d|uj\d)$", "", k)
            out = [o for o in obl if o["id"].startswith("S") and o["inst"] == base]
            out += [o for o in obl if o["id"].startswith("B") and o["expect"].endswith(";E") and o["inst"] == base + "(join)"]
        elif rule in ("F", "Fd", "D"):
            out = [o for o in obl if o["inst"] == k and (o["id"].startswith("D") or o["id"].startswith("F"))]
        elif rule in ("Jx", "J0", "Jp", "J", "Z"):
            kk = re.sub(r"#\d+$", "#2", k)
            out = [o for o in obl if o["inst"] == kk and o["id"][0] == ("Z" if rule == "Z" else "J")]
        elif rule in ("X", "Xc", "Xm", "Xi", "Xic"):
            if ".uarb" in k:
                out = [o for o in obl if o["id"].startswith("X") and k in o["inst"].split("|")]
            else:
                base = k.split(".")[0]
                out = [o for o in obl if o["id"].startswith("M") and o["inst"] == base]
        elif rule == "K":
            base = k.split(".")[0]
            out = [o for o in obl if o["id"].startswith("K") and o["inst"] == base]
        elif rule in ("H", "Hc"):
            out = [o for o in obl if o["id"].startswith("H") and o["inst"] == k]
        elif rule == "I":
            out = [o for o in obl if o["id"].startswith("I") and o["inst"] == k]
        return out
    matches = []; unrows = []
    hit = collections.defaultdict(lambda: collections.defaultdict(list))
    for row in rows:
        cs = cands(row)
        if not cs:
            unrows.append(row); continue
        for o in cs:
            matches.append((o["id"], row)); hit[o["id"]][row["seed"]].append(row)
    # ---- outputs
    od = os.path.join(HERE, "out") if not check else tempfile.mkdtemp()
    os.makedirs(od, exist_ok=True)
    def w(fn, lines):
        open(os.path.join(od, fn), "w").write("\n".join(lines) + "\n")
    w("obligations.tsv", ["id\tobligation\tlean\tinstance\texpect\tinstance_in_v\tnote"] +
      [f"{o['id']}\t{o['name']}\t{o['lean']}\t{o['inst']}\t{o['expect']}\t"
       f"{'-' if o['inst'].startswith(('env:', '*')) or not kv else ('yes' if all(exists(x.replace('(join)', '')) for x in o['inst'].split('|')) else 'NO')}\t{o['note']}"
       for o in obl])
    def verdict(rs):
        if not rs: return "-"
        out = []
        for fl in sorted({r["rule"] for r in rs}):
            q = [r for r in rs if r["rule"] == fl]
            ws = [r["worst"] for r in q if r["worst"] is not None]
            us = [r["unguarded"] for r in q if r["unguarded"] is not None]
            wv = min(ws) if ws else None; uv = min(us) if us else None
            v = "NC" if wv is None and uv is None else ("PASS" if wv is not None and wv >= 0 else ("BANDFAIL" if uv is not None and uv >= 0 else "FAIL"))
            out.append(f"{fl}:{v}({wv}/{uv})")
        return " ".join(out)
    w("matches.tsv", ["id\tobligation\texpect\t" + "\t".join(f"seed_{s}" for s in SEEDS)] +
      [f"{o['id']}\t{o['name']}\t{o['expect']}\t" + "\t".join(verdict(hit[o['id']].get(s, [])) for s in SEEDS)
       for o in obl if o["id"] in hit])
    needs = lambda o: not (o["expect"].startswith(("derived", "ghost", "vacuous", "argued")) or "aggregate" in o["expect"])
    unobl = [o for o in obl if o["id"] not in hit]
    w("unmatched_obl.tsv", ["id\tobligation\tinstance\texpect\tclass\tnote"] +
      [f"{o['id']}\t{o['name']}\t{o['inst']}\t{o['expect']}\t{'expected-row-missing' if needs(o) and o['expect'] != 'none' else ('no-rule' if o['expect'] == 'none' else 'not-a-row')}\t{o['note']}" for o in unobl])
    etern = {f"ulink_{E.vname(v)}" for v in em.linked if not (g.A(v) in g.chan)}
    def why(r):
        if r["key"].split(".")[0] in etern: return "eternal-chain link (H_SOURCE_ETERNAL: not a channel of CapstoneNet)"
        return "UNEXPLAINED"
    w("unmatched_rows.tsv", ["seed\trule\tkey\tsrc\twhy"] + [f"{r['seed']}\t{r['rule']}\t{r['key']}\t{r['src']}\t{why(r)}" for r in unrows])
    # summary
    S = []
    S.append(f"oblgen: CapstoneNet.lean reproduced by netgen.py (drift check ok); {len(names)} channels, {len(lops)} operators")
    S.append(f"groups whose link order is ambiguous (links on two members): {unordered}")
    cnt = collections.Counter(o["name"].split("(")[0] + " [" + o["expect"] + "]" for o in obl)
    S.append(f"obligations: {len(obl)}")
    for k_, v in sorted(cnt.items()): S.append(f"  {v:4d}  {k_}")
    S.append(f"tcheck rows read: {len(rows)} ({collections.Counter(r['rule'] for r in rows)})")
    S.append(f"rows matched to >=1 obligation: {len(rows) - len(unrows)}; unmatched rows: {len(unrows)} ({collections.Counter(r['rule'] for r in unrows)})")
    S.append(f"  unmatched rows by reason: {collections.Counter(why(r) for r in unrows)}")
    cls = collections.Counter()
    for o in unobl:
        c_ = 'expected-row-missing' if needs(o) and o['expect'] != 'none' else ('no-rule' if o['expect'] == 'none' else 'not-a-row')
        cls[(c_, o["name"].split("(")[0], o["expect"])] += 1
    S.append(f"obligations with no row: {len(unobl)}")
    for (a, b, c_), v in sorted(cls.items()): S.append(f"  {v:4d}  {a:22s} {b} [{c_}]")
    # per-kind verdicts across seeds
    S.append("per obligation kind, over the 4 seeds (rows matched; worst band margin; worst unguarded):")
    agg = collections.defaultdict(lambda: [0, 0, None, None, 0, 0])
    for o in obl:
        if o["id"] not in hit: continue
        for s in SEEDS:
          for fl in sorted({r["rule"] for r in hit[o["id"]].get(s, [])}):
            key = o["name"].split("(")[0] + " / " + fl
            rs = [r for r in hit[o["id"]].get(s, []) if r["rule"] == fl]
            if not rs: continue
            a = agg[key]; a[0] += 1
            ws = [r["worst"] for r in rs if r["worst"] is not None]; us = [r["unguarded"] for r in rs if r["unguarded"] is not None]
            if ws:
                a[2] = min(ws) if a[2] is None else min(a[2], min(ws))
                if min(ws) < 0: a[4] += 1
            if us:
                a[3] = min(us) if a[3] is None else min(a[3], min(us))
                if min(us) < 0: a[5] += 1
            a[1] += len(rs)
    for k_, a in sorted(agg.items()):
        S.append(f"  {k_:28s} (obligation,seed) pairs {a[0]:4d}  rows {a[1]:5d}  worst band {a[2]}  worst unguarded {a[3]}  "
                 f"pairs failing under band {a[4]}  pairs failing unguarded {a[5]}")
    w("summary.txt", S)
    if check:
        bad = [fn for fn in ("obligations.tsv", "matches.tsv", "unmatched_obl.tsv", "unmatched_rows.tsv", "summary.txt")
               if not filecmp.cmp(os.path.join(od, fn), os.path.join(HERE, "out", fn), shallow=False)]
        shutil.rmtree(od)
        if bad: raise SystemExit(f"oblgen --check: differs: {bad}")
        print("oblgen --check: ok")
    else:
        print("\n".join(S))


if __name__ == "__main__":
    main()
