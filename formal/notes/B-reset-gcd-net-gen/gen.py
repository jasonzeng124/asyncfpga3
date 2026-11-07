#!/usr/bin/env python3
"""gcd_hw control network from the SYNTHESIZED yosys netlist -> Lean term.

    python3 -I gen.py net   SYNTH.json OUT/net.json [--flat OUT/flat.json] [--tc TC]
    python3 -I gen.py match OUT/net.json ResetGcdNet.lean OUT/order.json
    python3 -I gen.py lean  OUT/net.json OUT/order.json OUT/ResetGcdNetRe.lean ResetGcdNet.lean
    (routed comparison: routed.py)

`net`: SYNTH.json is build_hw.sh's `cells/build/hw/gcd_hw/gcd_hw.json` (the
post-`synth_xilinx` netlist nextpnr reads; bdc_gcd and its children are kept
as hierarchy there).  It is flattened with the toolchain's own yosys
(`read_json; hierarchy -top gcd_hw; setattr -mod -unset keep_hierarchy *;
flatten; write_json`), which keeps every instance's `$scopeinfo` cell (its
RTL module type).  Then the control network is cut out exactly as
ResetGcdNet.lean defines it (see README.md):

  * scope: cells under `urig.` (gcd_rig and bdc_gcd); gcd_hw.v's own clocked
    logic, its samplers and the dhk/invhk oscillators are outside;
  * node 0 = the net `urig.rst` (an input node);
  * a CONTROL cell is a LUT whose innermost module scope is one of CTRL_MODS,
    or a LUT instantiated directly in a `bdc_*` kernel module or in gcd_rig
    whose name does not start with `uz_` (the `uor` LUT1s, the rig's
    samplers/filters); plus every synthesized (scope-less) LUT all of whose
    non-constant inputs are control nets (least fixed point: this picks up
    the yosys-inferred `|j` of bdc_muxn3_32 and nothing else, checked below);
  * excluded: bd_latch, bd_datamux, the `uz_*` LUT1s, every other inferred
    LUT (datapath, amerge index, the muxn3 decode) -- these are DATA;
  * one node per LUT output; LUT6_2 gives two nodes, O5 (INIT % 2^32 on
    I0..I4) and O6 (INIT on I0..I5); pins in order [I0, I1, ...];
  * a pin reading a net that is not rst and not a control output is a DATA
    input node (free); a constant pin is k0/k1.

Ordering in net.json is canonical (rst, data by net name, control by cell
name) and owes nothing to ResetGcdNet.  `match` computes a renumbering onto
ResetGcdNet's indices (an UNTRUSTED certificate: Lean checks the result node
by node); unmatched nodes are appended after index 3321.  `lean` writes the
term and the comparison theorems.
"""
import json
import os
import re
import subprocess
import sys
import tempfile

CTRL_MODS = {"bd_arbiter", "bd_c2", "bd_c2n", "bd_c2n_set", "bd_c3", "bd_c4",
             "bd_delay", "bd_delay_gated", "bd_mux", "bd_src", "bd_steer"}
DATA_MODS = {"bd_latch", "bd_datamux"}
LUTS = {"LUT1", "LUT2", "LUT3", "LUT4", "LUT5", "LUT6", "LUT6_2"}
SPLIT = re.compile(r"\.(?![^\[]*\])")


def natkey(s):
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", s)]


def modbase(t):
    m = re.match(r"\$paramod(?:\$\w+)?\\(\w+)", t)
    return m.group(1) if m else t.lstrip("\\")


def flatten(synth, tc):
    yosys = os.path.join(tc, "openxc7/bin/yosys")
    fd, out = tempfile.mkstemp(suffix=".json")
    os.close(fd)
    subprocess.run([yosys, "-q", "-p",
                    f"read_json {synth}; hierarchy -top gcd_hw; "
                    "setattr -mod -unset keep_hierarchy *; flatten; "
                    f"write_json {out}"], check=True)
    d = json.load(open(out))
    os.unlink(out)
    return d


def build(d):
    m = d["modules"]["gcd_hw"]
    cells = m["cells"]
    scopes = {k: v["attributes"] for k, v in cells.items() if v["type"] == "$scopeinfo"}

    def scope_of(name):
        parts = SPLIT.split(name)
        for j in range(len(parts) - 1, 0, -1):
            p = ".".join(parts[:j])
            if p in scopes:
                return p
        return None

    netname = {}
    for n, v in sorted(m["netnames"].items(), key=lambda kv: (kv[1].get("hide_name", 0), len(kv[0]), kv[0])):
        for i, b in enumerate(v["bits"]):
            if isinstance(b, int) and b not in netname:
                netname[b] = n if len(v["bits"]) == 1 else f"{n}[{i}]"
    rst_bits = m["netnames"]["urig.rst"]["bits"]
    assert len(rst_bits) == 1
    rst = rst_bits[0]

    luts = {k: v for k, v in cells.items() if v["type"] in LUTS}
    cls = {}  # cell -> 'ctl' | 'data' | 'inf' (inferred, undecided)
    for k, v in luts.items():
        sc = scope_of(k)
        if sc is None:
            cls[k] = "inf"
            continue
        if not (sc == "urig" or sc.startswith("urig.")):
            cls[k] = "out"
            continue
        mt = modbase(scopes[sc]["module"])
        loc = k[len(sc) + 1:]
        if mt in CTRL_MODS:
            cls[k] = "ctl"
        elif mt in DATA_MODS:
            cls[k] = "data"
        elif (mt.startswith("bdc_") or mt == "gcd_rig") and "." not in loc:
            cls[k] = "data" if loc.startswith("uz_") else "ctl"
        else:
            raise SystemExit(f"unclassified LUT {k} in module {mt}")
    outs = lambda v: [b for p in ("O", "O5", "O6") for b in v["connections"].get(p, [])]
    ins = lambda v: [b for p, bs in sorted(v["connections"].items()) if p.startswith("I") for b in bs]
    ctlnets = {rst} | {b for k, v in luts.items() if cls[k] == "ctl" for b in outs(v)}
    added = []
    changed = True
    while changed:
        changed = False
        for k, v in luts.items():
            if cls[k] == "inf" and all((not isinstance(b, int)) or b in ctlnets for b in ins(v)):
                cls[k] = "ctl"
                added.append(k)
                ctlnets |= set(outs(v))
                changed = True
    # keep an inferred LUT only if it drives a control LUT pin (prunes the
    # amerge index encoders, which only feed latches = data)
    changed = True
    while changed:
        changed = False
        read = {b for k, v in luts.items() if cls[k] == "ctl" for b in ins(v)}
        for k in list(added):
            if not any(b in read for b in outs(luts[k])):
                cls[k] = "inf"
                added.remove(k)
                changed = True
    # driver map for control outputs
    drv = {}
    ctl = sorted((k for k in luts if cls[k] == "ctl"), key=natkey)
    nodes = [dict(kind="rst", name="urig.rst", net=rst)]
    gates = []
    for k in ctl:
        v = luts[k]
        t = v["type"]
        init = int(v["parameters"]["INIT"], 2)
        c = v["connections"]
        if t == "LUT6_2":
            pins6 = [c[f"I{i}"][0] for i in range(6)]
            gates.append(dict(kind="gate", name=k + ".O5", cell=k, out="O5",
                              init=init % (1 << 32), pins=pins6[:5], net=c["O5"][0]))
            gates.append(dict(kind="gate", name=k + ".O6", cell=k, out="O6",
                              init=init, pins=pins6, net=c["O6"][0]))
        else:
            nin = int(t[3])
            gates.append(dict(kind="gate", name=k, cell=k, out="O", init=init,
                              pins=[c[f"I{i}"][0] for i in range(nin)], net=c["O"][0]))
    for g in gates:
        assert g["net"] not in drv, g
        drv[g["net"]] = g
    data = sorted({b for g in gates for b in g["pins"]
                   if isinstance(b, int) and b != rst and b not in drv},
                  key=lambda b: natkey(netname.get(b, f"~{b}")))
    nodes += [dict(kind="data", name=netname.get(b, f"net{b}"), net=b) for b in data]
    nodes += gates
    idx = {n["net"]: i for i, n in enumerate(nodes)}

    def src(b):
        if b in ("0", "1"):
            return ["k", int(b)]
        if b in ("x", "z"):
            raise SystemExit(f"undriven constant pin {b}")
        return ["n", idx[b]]
    for g in gates:
        g["src"] = [src(b) for b in g["pins"]]
    return nodes, added


def cmd_net(argv):
    synth, out = argv[0], argv[1]
    tc = os.environ.get("TC", os.path.expanduser("~/dev2/lib/fpgatoolchain"))
    if "--tc" in argv:
        tc = argv[argv.index("--tc") + 1]
    d = json.load(open(synth))
    mods = d["modules"]
    if any(v.get("type") in mods and mods[v["type"]].get("cells")
           for v in mods["gcd_hw"]["cells"].values()):  # hierarchy left: flatten
        d = flatten(synth, tc)
    if "--flat" in argv:
        json.dump(d, open(argv[argv.index("--flat") + 1], "w"))
    nodes, added = build(d)
    ng = sum(n["kind"] == "gate" for n in nodes)
    nd = sum(n["kind"] == "data" for n in nodes)
    print(f"net: {len(nodes)} nodes = 1 rst + {nd} data + {ng} control LUT outputs; "
          f"inferred control LUTs: {added}")
    import hashlib
    sha = hashlib.sha256(open(synth, "rb").read()).hexdigest()
    json.dump(dict(source=os.path.abspath(synth), sha256=sha, nodes=nodes, inferred=added),
              open(out, "w"), indent=0)


# ---------------------------------------------------------------- match
def parse_lean(path):
    """ResetGcdNet.lean -> list of (kind, init, pins, name) by index."""
    defs = {}
    for line in open(path):
        m = re.match(r"def (I_\w+) : Nat := (0x[0-9A-Fa-f]+|\d+)", line)
        if m:
            defs[m.group(1)] = int(m.group(2), 0)
    rc = os.path.join(os.path.dirname(path), "ResetContract.lean")
    for line in open(rc):
        m = re.match(r"def (I_\w+) : Nat := (0x[0-9A-Fa-f]+|\d+)", line)
        if m:
            defs.setdefault(m.group(1), int(m.group(2), 0))
    out = {}
    for line in open(path):
        m = re.match(r"def n(\d+) : NInfo := (.*?)\s+--\s+(.*)$", line)
        if not m:
            continue
        i, body, nm = int(m.group(1)), m.group(2), m.group(3)
        if body == "RIn":
            out[i] = dict(kind="rst", name=nm)
        elif body == "DIn":
            out[i] = dict(kind="data", name=nm.replace("data: ", ""))
        else:
            g = re.match(r"G (\w+) \[(.*)\] (\d+) (true|false)$", body)
            src = []
            for p in g.group(2).split(","):
                p = p.strip()
                src.append(["n", int(p[2:])] if p.startswith("p ") else ["k", int(p == "k1")])
            out[i] = dict(kind="gate", name=nm, init=defs[g.group(1)], src=src,
                          rank=int(g.group(3)), rv=g.group(4) == "true")
    return [out[i] for i in range(len(out))]


def oldname_variants(name):
    """Candidate ResetGcdNet comment names for a yosys cell name (heuristic only;
    the match is verified structurally below and then by the kernel)."""
    n = name[len("urig.udut."):] if name.startswith("urig.udut.") else name
    suf = ""
    if n.endswith(".O5") or n.endswith(".O6"):
        n, suf = n[:-3], n[-3:]
    ps = [p for p in SPLIT.split(n) if not re.fullmatch(r"genblk\d+|g\d+|gt|chain", p)]
    ps = [re.sub(r"^chunk\[(\d+)\]$", r"chunk\1", p) for p in ps]
    yield ".".join(ps) + suf
    yield ".".join(ps[:-1]) + suf
    yield ".".join(ps[:-2]) + suf


def cmd_match(argv):
    net = json.load(open(argv[0]))["nodes"]
    old = parse_lean(argv[1])
    oldn = {o["name"]: i for i, o in enumerate(old)}
    perm = {0: 0}  # new index -> old index
    for i, n in enumerate(net):
        if n["kind"] != "gate":
            continue
        for v in oldname_variants(n["name"]):
            if v in oldn and old[oldn[v]]["kind"] == "gate":
                perm[i] = oldn[v]
                break
    if net[0]["kind"] == "rst":
        perm[0] = 0
    # special: the inferred muxn3 |j
    for i, n in enumerate(net):
        if i not in perm and n["kind"] == "gate" and n["cell"].startswith("$flatten\\urig.udut.\\umux21."):
            cand = [j for j, o in enumerate(old) if o["name"] == "umux21.|j"]
            if cand:
                perm[i] = cand[0]
    # data nodes: through matched consumers' pins
    votes = {}
    for i, n in enumerate(net):
        if n["kind"] != "gate" or i not in perm:
            continue
        o = old[perm[i]]
        for a, b in zip(n["src"], o["src"]):
            if a[0] == "n" and net[a[1]]["kind"] == "data" and b[0] == "n" and old[b[1]]["kind"] == "data":
                votes.setdefault(a[1], set()).add(b[1])
    # a real data net may stand for several committed data nodes (the RTL has a
    # separate wire per fork copy; synthesis merges them): it takes the least
    # committed index, and phi maps every committed data index to it
    phi = {}
    for i, s in votes.items():
        perm[i] = min(s)
        for j in s:
            assert j not in phi, ("committed data node read as two real nets", j)
            phi[j] = min(s)
    inv = {}
    for a, b in perm.items():
        assert b not in inv, ("old index matched twice", b, inv[b], a)
        inv[b] = a
    nxt = len(old)
    order = [None] * len(net)
    for a, b in perm.items():
        order[a] = b
    extra = []
    for i in range(len(net)):
        if order[i] is None:
            order[i] = nxt
            extra.append((nxt, net[i]["name"]))
            nxt += 1
    missing = [(j, old[j]["name"]) for j in range(len(old)) if j not in inv and j not in phi]
    print(f"match: {len(perm)} of {len(net)} new nodes onto {len(old)} old; "
          f"{len(extra)} new-only, {len(missing)} old-only")
    for e in extra:
        print("  new-only", e)
    for e in missing:
        print("  old-only", e)
    merged = sorted((j, r) for j, r in phi.items() if j != r)
    print(f"  {len(merged)} committed data nodes identified with another one (phi): {merged}")
    json.dump(dict(order=order, extra=extra, missing=missing, phi=sorted(phi.items()),
                   oldM=len(old)), open(argv[2], "w"), indent=0)


# ---------------------------------------------------------------- lean
def ternary_certs(nodes):
    """Rank and reset value per node, computed as ResetGcd checks them: Kleene
    iteration from all-X with rst = 1 and every data net X; a node's rank is
    the iteration (from 0) after which it is definite, its reset value the
    fixed point.  Untrusted: the Lean file re-checks both (H_LOCAL at rank)."""
    X = 2
    N = len(nodes)

    def lut(init, vals):
        xs = [i for i, v in enumerate(vals) if v == X]
        base = sum(v << i for i, v in enumerate(vals) if v != X)
        res = None
        for mask in range(1 << len(xs)):
            a = base
            for j, i in enumerate(xs):
                if mask >> j & 1:
                    a |= 1 << i
            b = (init >> a) & 1
            if res is None:
                res = b
            elif res != b:
                return X
        return res
    val = [1 if n["kind"] == "rst" else X for n in nodes]
    rank = [0 if n["kind"] == "rst" else None for n in nodes]
    for it in range(1, 1000):
        new = [lut(n["init"], [s[1] if s[0] == "k" else val[s[1]] for s in n["src"]])
               if n["kind"] == "gate" else val[i] for i, n in enumerate(nodes)]
        if new == val:
            break
        for i in range(N):
            if new[i] != X and rank[i] is None:
                rank[i] = it - 1
        val = new
    return val, rank


def renumber(net, order):
    M = max(order) + 1
    ren = [None] * M
    for i, n in enumerate(net):
        ren[order[i]] = dict(n, src=[["n", order[s[1]]] if s[0] == "n" else s
                                     for s in n.get("src", [])])
    for j in range(M):
        if ren[j] is None:
            ren[j] = dict(kind="unused", name="(no node: committed data input identified by phi)")
    return ren


def src_lean(s):
    return f"q {s[1]}" if s[0] == "n" else ("k1" if s[1] else "k0")


def cmd_lean(argv):
    netj = json.load(open(argv[0]))
    oj = json.load(open(argv[1]))
    out = argv[2]
    lean_old = argv[3] if len(argv) > 3 and argv[3] != "-" else None  # "-": no comparison part
    ren = renumber(netj["nodes"], oj["order"])
    M = len(ren)
    oldM = oj["oldM"]
    phi = dict((int(a), b) for a, b in oj["phi"])
    calc = [dict(n, kind="data") if n["kind"] == "unused" else n for n in ren]
    val, rank = ternary_certs(calc)
    und = [j for j in range(M) if ren[j]["kind"] == "gate" and rank[j] is None]
    if und:
        raise SystemExit(f"gates never definite under reset: {und[:10]}")
    # compare with the committed term (for the diff lists the theorems state)
    old = parse_lean(lean_old) if lean_old else None
    diff, diffT, permT = [], [], []
    if old:
        for j in range(oldM):
            o, n = old[j], ren[j]
            if o["kind"] != "gate":
                assert n["kind"] in ("data", "unused", "rst"), (j, n)
                continue
            osrc = [["n", phi.get(s[1], s[1])] if s[0] == "n" else s for s in o["src"]]
            if n["kind"] != "gate" or n["init"] != o["init"] or n["src"] != osrc:
                diff.append(j)
                if n["kind"] == "gate" and n["init"] == o["init"] and sorted(map(str, n["src"])) == sorted(map(str, osrc)):
                    perm = [osrc.index(x) for x in n["src"]]
                    assert len(set(perm)) == len(perm)
                    permT.append((j, perm))
                    continue
                ch = [(a, b) for a, b in zip(osrc, n["src"]) if a != b]
                assert n["kind"] == "gate" and n["init"] == o["init"] and len(n["src"]) == len(osrc) \
                    and len(ch) == 1 and ch[0][0][0] == "n" and ch[0][1][0] == "n", (j, o, n)
                diffT.append((j, ch[0][0][1], ch[0][1][1]))
        crank = sum(1 for j in range(oldM) if old[j]["kind"] == "gate"
                    and (old[j]["rank"] != rank[j] or old[j]["rv"] != (val[j] == 1)))
        print(f"lean: {len(diff)} committed nodes differ: one pin redirected {diffT}; pins permuted {permT}; "
              f"certificates (rank, reset value) differing from the committed ones: {crank}")
    newT = [(j, ren[j]) for j in range(oldM, M)]
    unused = [j for j in range(M) if ren[j]["kind"] == "unused"]
    ones = [j for j in range(M) if ren[j]["kind"] in ("gate", "rst") and val[j] == 1]
    L = []
    w = L.append
    w("import Formal.Cells.ResetGcd\n")
    w(GEN_DOC.format(src=netj["sha256"], M=M, oldM=oldM, nnew=M - oldM,
                     nunused=len(unused), nreal=M - len(unused)))
    w("namespace Formal.Cells.ResetGcdRe")
    w("open Formal.Cells Formal.Cells.TernarySound Formal.Cells.ResetContract Formal.Cells.ResetGcd\n")
    w("abbrev q (i : Nat) : Src := .node i")
    w("/-- A control gate (INIT as in the netlist, pins `[I0, I1, ...]`, rank, reset value). -/")
    w("def RG (init : Nat) (pins : List Src) (rk : Nat) (rv : Bool) : NInfo := ⟨.gate init pins, true, rk, rv⟩")
    w("/-- `urig.rst`. -/\ndef RR : NInfo := ⟨.input, true, 0, true⟩")
    w("/-- A data net (free input). -/\ndef RD : NInfo := ⟨.input, false, 0, false⟩\n")
    for j, n in enumerate(ren):
        if n["kind"] == "rst":
            w(f"def r{j} : NInfo := RR  -- {n['name']}")
        elif n["kind"] in ("data", "unused"):
            w(f"def r{j} : NInfo := RD  -- {'data: ' if n['kind'] == 'data' else ''}{n['name']}")
        else:
            ps = ", ".join(src_lean(s) for s in n["src"])
            rv = "true" if val[j] == 1 else "false"
            w(f"def r{j} : NInfo := RG 0x{n['init']:X} [{ps}] {rank[j]} {rv}  -- {n['name']}")
    w("")
    w(braun(M))
    w(f"\n/-- Number of node indices of the regenerated network. -/\ndef rM : Nat := {M}")
    w(f"/-- Index count of the committed term. -/\ndef oldM : Nat := {oldM}")
    w(f"/-- `phi`: committed data index -> the real net standing for it (only the non-identity pairs). -/")
    w("def phiL : List (Nat × Nat) := [" + ", ".join(f"({a}, {b})" for a, b in sorted(phi.items()) if a != b) + "]")
    w("/-- Indices that are no node of the real network (committed data inputs merged by `phi`). -/")
    w("def unusedL : List Nat := [" + ", ".join(map(str, unused)) + "]")
    w("/-- Committed nodes whose regenerated node differs, as (index, committed pin source, real pin source). -/")
    w("def diffT : List (Nat × Nat × Nat) := [" + ", ".join(f"({a}, {b}, {c})" for a, b, c in diffT) + "]")
    w("/-- Committed nodes whose real pins are a permutation of the committed ones, as (index, perm): real pin k = committed pin perm[k]. -/")
    w("def permT : List (Nat × List Nat) := [" + ", ".join(f"({a}, [{', '.join(map(str, b))}])" for a, b in permT) + "]")
    w("/-- The real-only nodes (index, INIT, pin sources). -/")
    w("def newT : List (Nat × Nat × List Src) := [" + ", ".join(
        f"({j}, 0x{n['init']:X}, [{', '.join(src_lean(s) for s in n['src'])}])" for j, n in newT) + "]")
    w("/-- The control nodes whose reset value is 1 (computed; checked below). -/")
    w("def rOnesL : List Nat := [" + ", ".join(map(str, ones)) + "]")
    w(f"def rMaxRank : Nat := {max(r for r in rank if r is not None)}")
    w("\nend Formal.Cells.ResetGcdRe\n")
    tmpl = os.path.join(os.path.dirname(os.path.abspath(__file__)), "thm.lean.tmpl")
    def chunked(top):
        cs, lo = [], 0
        while lo < top:
            cs.append((lo, min(400, top - lo)))
            lo += 400
        return cs
    chunks, chunksA = chunked(M), chunked(oldM)
    t = open(tmpl).read()
    t = t.replace("@CHUNKS_SAME@", "\n".join(
        f"theorem cs{i} : chunkSame {lo} {k} = true := by decide +kernel" for i, (lo, k) in enumerate(chunksA)))
    t = t.replace("@CHUNKS_READ@", "\n".join(
        f"theorem cu{i} : chunkUnread {lo} {k} = true := by decide +kernel" for i, (lo, k) in enumerate(chunks)))
    t = t.replace("@CHUNKS_OK@", "\n".join(
        f"theorem ck{i} : chunkOK {lo} {k} = true := by decide +kernel" for i, (lo, k) in enumerate(chunks)))
    t = t.replace("@ALL_SAME@", cascade("chunk_same_mem", "cs", chunksA))
    t = t.replace("@ALL_READ@", cascade("chunk_unread_mem", "cu", chunks))
    t = t.replace("@ALL_OK@", cascade("chunk_mem", "ck", chunks))
    t = t.replace("@OLDM@", str(oldM)).replace("@M@", str(M))
    if old is None:
        a, b = t.index("-- @PART1_BEGIN@"), t.index("-- @PART1_END@")
        t = t[:a] + "-- (part 1, the comparison with ResetGcdNet, omitted: gen.py lean ... -)\n" + \
            t[b + len("-- @PART1_END@"):]
    else:
        t = t.replace("-- @PART1_BEGIN@\n", "").replace("-- @PART1_END@\n", "")
    L.append(t)
    open(out, "w").write("\n".join(L))
    print(f"lean: wrote {out}: {M} indices ({len(unused)} unused), max rank {max(r for r in rank if r is not None)}, "
          f"{len(ones)} reset-1 nodes")


def cascade(lem, pre, chunks):
    s = []
    for i, (lo, k) in enumerate(chunks[:-1]):
        s.append(f"  by_cases h{i} : n < {lo + k}")
        s.append(f"  · exact {lem} {pre}{i} (by omega) (by omega)")
    s.append(f"  exact {lem} {pre}{len(chunks) - 1} (by omega) (by omega)")
    return "\n".join(s)


def braun(M):
    """Braun tree over 0..M-1 in `BT.get`'s layout (root 0; the left subtree
    holds 2m+1, the right 2m+2), split into defs of bounded size."""
    lines, cnt = [], [0]

    def mk(a, b):
        if b >= M:
            return "BT.leaf"
        s = f"(BT.br {mk(2 * a, a + b)} r{b} {mk(2 * a, 2 * a + b)})"
        if len(s) > 2000:
            cnt[0] += 1
            lines.append(f"def u{cnt[0]} : BT := {s}")
            return f"u{cnt[0]}"
        return s
    lines.append(f"def rTree : BT := {mk(1, 0)}")
    return "\n".join(lines)


GEN_DOC = """/-!
# gcd_hw's control network, regenerated from the SYNTHESIZED netlist (GENERATED)

Generated by `formal/notes/B-reset-gcd-net-gen/gen.py` (`net`, `match`,
`lean`) from the yosys JSON of a real gcd_hw build, `cells/build/hw/gcd_hw/gcd_hw.json`
with sha256 `{src}`
(cells/hw/build_hw.sh gcd_hw, BDC_SELECT_PADS=cells/hw/gcd_hw_pads.json,
BD_RLOC=v4; the C-10e recipe; flattened with the toolchain's yosys). Do not
edit by hand; see `formal/notes/B-reset-gcd-net.md`.

{M} indices, {nreal} real nodes. Indices below {oldM} follow `ResetGcdNet`
(renumbering by `gen.py match`: an untrusted certificate, checked below node
by node); the {nnew} real-only nodes come after. {nunused} indices are no node
of the real network: committed data inputs that the synthesized netlist
merges into one net (`phiL`). Each `rN` has its node (INIT as a hex literal,
straight from the netlist), control flag, and a rank / reset-value
certificate computed by the generator (Kleene from all-X), re-checked below.
-/
"""


if __name__ == "__main__":
    {"net": cmd_net, "match": cmd_match, "lean": cmd_lean}[sys.argv[1]](sys.argv[2:])
