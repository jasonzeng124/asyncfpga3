#!/usr/bin/env python3
"""gcd_hw's control network `gNet` regenerated from bdc's Verilog (shard B, probe Bmap).

    python3 -B formal/tools-B/gcdnet_gen.py net OUTDIR
        runs `bdc/emit.py` (read-only, default sizes: every BDC_* / BD_* override unset) on
        cloud/fixtures/frontend/gcd/comp/handshake_transformed.mlir --no-top --probe n138,
        elaborates cells/hw/gcd_rig.v over it and cells/rtl/*.v with formal/tools-B/vsub.py
        (no yosys), cuts out the control network, writes
          OUTDIR/gcd.v               the emitted kernel,
          OUTDIR/ResetGcdNet.lean    the network in ResetGcdNet.lean's exact format,
          OUTDIR/net.json            nodes with full (yosys-style) names, and net -> node,
        and compares OUTDIR/ResetGcdNet.lean with formal/lean/Formal/Cells/ResetGcdNet.lean
        byte for byte (and, on a difference, line by line).
    python3 -B formal/tools-B/gcdnet_gen.py map OUTDIR LEANOUT
        the C-channel -> gNet-node table (see capmap.py), written as a Lean data file.

What the control network is (the definition ResetGcdNet.lean's header states, made exact):
* node 0: the rig's `rst` input;
* one node per output of every control LUT. A LUT is DATA iff it is inside `bd_latch` or
  `bd_datamux`, or is a `uz_*` LUT1 of a bdc compute module; every other LUT is control.
  LUT6_2: O5 (`INIT % 2^32`, pins I0..I4) and O6 (INIT, pins I0..I5) are two nodes;
* a reduction OR `|x` (a non-wiring expression) all of whose inputs are control nets and
  which a control pin reads is an inferred control gate (INIT = OR, pins in bit order): this
  is the `|j` of `bdc_muxn3_32` (H_INFER_OR3), and nothing else here;
* a control pin whose net (through every pure alias) is driven by a control node reads that
  node; by a constant, reads k0/k1; by anything else (a data LUT, an opaque expression, the
  rig's `idx` input) reads a DATA input node. Data input nodes are keyed by the net the pin
  reaches through PORT CONNECTIONS ONLY (not through assigns), named by its outermost name:
  this is why the fork copies `n5__0/1/2_data` are three data nodes (they are `assign`s of
  one net; synthesis merges them, B-reset-gcd-net.md finding 1).

Order (the committed term's, reproduced; a convention, not semantics):
* rst; then the data inputs in order of first read (gates in order, pins in order); then
  the gates: kernel (`urig.udut`) LUTs in elaboration order (instances in source order,
  depth first); a LUT6_2 gives O6 first when O6 feeds back to one of its own pins (the
  arbiter's state q), else O5 first; an inferred gate comes just before its first reader;
* the rig's LUTs are ordered by function, not source position: the ring (ufork, upsnk,
  urdly, uenv0, uenv1), the probe delays (uabsdly, ucmpdly), the samplers `*_d` (source
  order), then each sampler's filter `*_w` and `*_a`, in the samplers' order.
Names (comments only) follow the committed term's conventions: the kernel prefix `urig.udut.`
is dropped, generate labels of if-blocks (`chain`, `bypass`, `g1`..`g4`, `gt`) are dropped,
`chunk[i]` is written `chunkI` and the chunk's ctree instance `u` dropped, a C-element's LUT
`u` is dropped (named by the C-element instance) except for the rig's own `uenv0/uenv1`.
Rank and reset value are computed as ResetGcd checks them (Kleene from all-X, rst = 1, every
data input X): an untrusted certificate, re-checked by `decide` in ResetGcd.
"""
import glob
import hashlib
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)
import vsub  # noqa: E402

MLIR = "cloud/fixtures/frontend/gcd/comp/handshake_transformed.mlir"
COMMITTED = os.path.join(ROOT, "formal/lean/Formal/Cells/ResetGcdNet.lean")

CELEM = {"bd_c2", "bd_c2_set", "bd_c2n", "bd_c2n_set", "bd_c3", "bd_c4", "bd_c2_norst", "bd_c3_norst"}
DATA_MODS = {"bd_latch", "bd_datamux"}
DROP_LABELS = {"chain", "bypass", "g1", "g2", "g3", "g4", "gt"}
RING = ["ufork", "upsnk", "urdly", "uenv0", "uenv1"]
PROBES = ["uabsdly", "ucmpdly"]


def emit_kernel():
    env = {k: v for k, v in os.environ.items() if not (k.startswith("BDC_") or k.startswith("BD_"))}
    r = subprocess.run([sys.executable, "-B", os.path.join(ROOT, "bdc/emit.py"), MLIR, "--no-top",
                        "--probe", "n138"], cwd=ROOT, env=env, check=True, capture_output=True, text=True)
    return r.stdout


def elaborate(kernel_v):
    texts = [(f, open(f).read()) for f in sorted(glob.glob(os.path.join(ROOT, "cells/rtl/*.v")))]
    texts.append(("<bdc emit>", kernel_v))
    texts.append(("cells/hw/gcd_rig.v", open(os.path.join(ROOT, "cells/hw/gcd_rig.v")).read()))
    mods = vsub.parse(texts)
    E = vsub.Elab(mods)
    E.elab_top("gcd_rig", ["urig"])
    return E


# ------------------------------------------------------------------ names

def full(path):
    return ".".join(path)


def legacy_name(cell, out, E):
    """The committed term's comment name for a LUT (output `out`)."""
    p = list(cell["path"])
    assert p[0] == "urig"
    kern = len(p) > 1 and p[1] == "udut"
    p = p[2:] if kern else p
    # module type of each path prefix: find via scope modules recorded on cells
    q = []
    i = 0
    while i < len(p):
        c = p[i]
        if c in DROP_LABELS:
            i += 1
            continue
        m = re.fullmatch(r"chunk\[(\d+)\]", c)
        if m:
            q.append(f"chunk{m.group(1)}")
            i += 2  # the chunk's ctree instance `u`
            continue
        q.append(c)
        i += 1
    if cell["module"] in CELEM and q[-1] == "u" and (kern or len(q) > 3):
        q = q[:-1]
    nm = ".".join(q)
    if cell["type"] == "LUT6_2":
        nm += "." + out
    return nm


# ------------------------------------------------------------------ the network

def is_data_lut(c):
    return c["module"] in DATA_MODS or c["path"][-1].startswith("uz_")


def build(E):
    ufa, ufp = E.ufa, E.ufp
    rst_bits = E.top_inputs["rst"]
    assert len(rst_bits) == 1
    rst_cls = ufa.find(rst_bits[0])
    # drivers per alias class
    drv = {}

    def add_drv(cls, d):
        if cls in drv and drv[cls] != d:
            raise SystemExit(f"two drivers on one net: {drv[cls]} / {d}")
        drv[cls] = d
    add_drv(rst_cls, ("rst",))
    for nm, bits in E.top_inputs.items():
        if nm != "rst":
            for b in bits:
                add_drv(ufa.find(b), ("input", nm))
    for b, v in E.const.items():
        add_drv(ufa.find(b), ("k", v))
    for b, o in E.opaque.items():
        add_drv(ufa.find(b), ("opaque", b))
    ctl_out = []  # (cell index, out port)
    for ci, c in enumerate(E.cells):
        for o, b in sorted(c["outs"].items()):
            add_drv(ufa.find(b), ("lut", ci, o))
    # control cells and their gate records
    gates = []  # dict(key, cell, out, init, pins (bit items), name, full)
    order_cells = []
    for ci, c in enumerate(E.cells):
        if is_data_lut(c):
            continue
        order_cells.append(ci)

    def lut_outs(ci):
        c = E.cells[ci]
        w = vsub.LUT_W[c["type"]]
        pins = [c["pins"].get(f"I{i}", ("k", 0)) for i in range(w)]
        if c["type"] != "LUT6_2":
            (o, ob), = c["outs"].items()
            return [("O", c["init"], pins, ob)]
        recs = {"O5": ("O5", c["init"] % (1 << 32), pins[:5], c["outs"]["O5"]),
                "O6": ("O6", c["init"], pins, c["outs"]["O6"])}
        own = {ufa.find(b) for b in pins if isinstance(b, int)}
        first = "O6" if ufa.find(c["outs"]["O6"]) in own else "O5"
        return [recs[first], recs["O5" if first == "O6" else "O6"]]

    # rig order
    def rig_key(ci):
        c = E.cells[ci]
        top = c["path"][1]
        if top in RING:
            return (0, RING.index(top))
        if top in PROBES:
            return (1, PROBES.index(top))
        m = re.fullmatch(r"(u\w+?)_(d|w|a)", top)
        assert m, top
        return (2, 0, 0)  # refined below
    kern = [ci for ci in order_cells if E.cells[ci]["path"][1] == "udut"]
    rig = [ci for ci in order_cells if E.cells[ci]["path"][1] != "udut"]
    samplers = []
    for ci in rig:
        top = E.cells[ci]["path"][1]
        if top.endswith("_d") and top[:-2] not in samplers:
            samplers.append(top[:-2])

    def rig_key2(ci):
        c = E.cells[ci]
        top = c["path"][1]
        if top in RING:
            return (0, RING.index(top), ci)
        if top in PROBES:
            return (1, PROBES.index(top), ci)
        base, kind = top[:-2], top[-1]
        if kind == "d":
            return (2, samplers.index(base), ci)
        return (3, samplers.index(base), "wa".index(kind), ci)
    rig.sort(key=rig_key2)

    node_of_cls = {}   # alias class -> gate node key
    gate_list = []     # in order: records
    inferred = {}      # (scope, text) -> record

    for ci in kern + rig:
        for o, init, pins, ob in lut_outs(ci):
            rec = dict(kind="gate", cell=ci, out=o, init=init, pins=pins, outbit=ob,
                       name=legacy_name(E.cells[ci], o, E),
                       full=full(E.cells[ci]["path"]) + ("." + o if E.cells[ci]["type"] == "LUT6_2" else ""))
            gate_list.append(rec)
            node_of_cls[ufa.find(ob)] = rec

    # resolve pins; inferred gates are inserted before their first reader
    data_nodes = {}  # ufp class -> record
    final = []

    def classify(b):
        """-> ('k', v) | ('gate', rec) | ('rst',) | ('data', ufp class) | ('infer', key)"""
        if not isinstance(b, int):
            return b
        cls = ufa.find(b)
        d = drv.get(cls)
        if d is None:
            raise SystemExit(f"undriven control pin net {E.bitname[b]}")
        if d[0] == "rst":
            return ("rst",)
        if d[0] == "k":
            return ("k", d[1])
        if d[0] == "lut":
            if cls in node_of_cls:
                return ("gate", node_of_cls[cls])
            return ("data", ufp.find(b))
        if d[0] == "opaque":
            ob = d[1]
            path, txt, ins, op, bitpos = E.opaque[ob]
            if op == "or" and ins and all(classify(x)[0] in ("gate", "rst") for x in ins):
                return ("infer", (path, txt, tuple(ins)))
            return ("data", ufp.find(b))
        return ("data", ufp.find(b))

    placed = set()

    def place(rec):
        for b in rec["pins"]:
            k = classify(b)
            if k[0] == "infer" and k[1] not in inferred:
                path, txt, ins = k[1]
                n = len(ins)
                init = (1 << (1 << n)) - 2
                ir = dict(kind="gate", cell=None, out="O", init=init, pins=list(ins), outbit=None,
                          name=(".".join(path[2:]) if path[1] == "udut" else ".".join(path)) + "." + txt,
                          full=".".join(path) + "." + txt)
                inferred[k[1]] = ir
                place(ir)
        final.append(rec)

    for rec in gate_list:
        place(rec)

    # numbering: rst, data (first read order), gates
    data_order = []
    for rec in final:
        for b in rec["pins"]:
            k = classify(b)
            if k[0] == "data" and k[1] not in data_nodes:
                data_nodes[k[1]] = None
                data_order.append(k[1])
    # data names: outermost name in the port-only class
    members = {}
    for b in range(len(E.bitname)):
        c = ufp.find(b)
        if c in data_nodes:
            members.setdefault(c, []).append(b)

    def dname(c):
        cands = []
        for b in members[c]:
            path, nm = E.bitname[b]
            if nm.startswith("<"):
                continue
            pl = list(path)
            kern_ = len(pl) > 1 and pl[1] == "udut"
            depth = len(pl)
            shown = ".".join(pl[2:] + [nm]) if kern_ else ".".join(pl + [nm])
            cands.append((depth, shown, ".".join(pl + [nm])))
        cands.sort()
        return cands[0]
    nodes = [dict(kind="rst", name="rst", full="urig.rst")]
    idx_data = {}
    for c in data_order:
        _, shown, fl = dname(c)
        idx_data[c] = len(nodes)
        nodes.append(dict(kind="data", name=shown, full=fl))
    gidx = {}
    for rec in final:
        gidx[id(rec)] = len(nodes)
        nodes.append(rec)

    def src(b):
        k = classify(b)
        if k[0] == "k":
            return ["k", k[1]]
        if k[0] == "rst":
            return ["n", 0]
        if k[0] == "gate":
            return ["n", gidx[id(k[1])]]
        if k[0] == "infer":
            return ["n", gidx[id(inferred[k[1]])]]
        return ["n", idx_data[k[1]]]
    for rec in final:
        rec["src"] = [src(b) for b in rec["pins"]]
    return nodes, drv, classify, gidx, idx_data


def certs(nodes):
    """Rank and reset value, as ResetGcd checks them (Kleene from all-X, rst = 1)."""
    X = 2

    def lut(init, vals):
        xs = [i for i, v in enumerate(vals) if v == X]
        base = sum(v << i for i, v in enumerate(vals) if v != X)
        res = None
        for m in range(1 << len(xs)):
            a = base
            for j, i in enumerate(xs):
                if m >> j & 1:
                    a |= 1 << i
            b = (init >> a) & 1
            if res is None:
                res = b
            elif res != b:
                return X
        return res
    val = [1 if n["kind"] == "rst" else X for n in nodes]
    rank = [0 if n["kind"] != "gate" else None for n in nodes]
    for it in range(1, 10000):
        new = [lut(n["init"], [s[1] if s[0] == "k" else val[s[1]] for s in n["src"]])
               if n["kind"] == "gate" else val[i] for i, n in enumerate(nodes)]
        if new == val:
            break
        for i in range(len(nodes)):
            if new[i] != X and rank[i] is None:
                rank[i] = it - 1
        val = new
    bad = [i for i, n in enumerate(nodes) if n["kind"] == "gate" and rank[i] is None]
    assert not bad, f"gates never definite under reset: {bad[:10]}"
    return val, rank


# ------------------------------------------------------------------ Lean (ResetGcdNet.lean format)

INITN = [("I_c2", 0x00E800E800E800E8), ("I_c2n", 0x00B200B200B200B2), ("I_c2n_set", 0xFFB2FFB2FFB2FFB2),
         ("I_c3", 0x0000FE800000FE80), ("I_c4", 0x00000000FFFE8000), ("I_uj0", 0x0000AE080000AE08),
         ("I_uj1", 0x0000EA800000EA80), ("I_arb", 0xFFF0FFB2ACACACAC), ("I_grant", 0x0C0C0C0CA0A0A0A0),
         ("I_steer", 0x8888888822222222), ("I_buf", 2), ("I_src", 1), ("I_or2", 0xE), ("I_and2", 8),
         ("I_ok", 4), ("I_cmpb", 0x90), ("I_arb5", 0xACACACAC), ("I_grant5", 0xA0A0A0A0),
         ("I_steer5", 0x22222222), ("I_or3", 0xFE)]
INITV = {v: n for n, v in INITN}

HEADER = r"""import Formal.Cells.ResetContract

/-!
# Probe Rst2: gcd_hw's control netlist as a `TernarySound.Circ` (GENERATED)

Generated by the scratchpad script `rst/gen_reset_gcd.py` + `rst/emit_lean.py`
from the bdc-emitted kernel (`python3 bdc/emit.py
cloud/fixtures/frontend/gcd/comp/handshake_transformed.mlir --no-top --probe n138`,
default matched-delay sizes) and `cells/hw/gcd_rig.v` (CMPD 16, PRBD 2, WFILT 2,
no GCD_RIG_CMP_PROBE). Do not edit by hand; see `formal/notes/B-reset-gcd.md`.

* node 0: `rst` (control input); nodes 1..64: data nets read by control
  LUTs (steer/mux selects, the inferred muxn3 decode outputs, the rig's `mism`
  and `abs_data[31]`), each a FREE input;
* nodes 65..3321: one node per LUT output (LUT6_2: O5 and O6 separate),
  with the REAL INIT and pin list `[I0, I1, ...]` of `cells/rtl`; delay lines
  element by element. Each `def nN` carries: node, control flag, rank, reset
  value. Rank and reset value are an UNTRUSTED certificate: `ResetGcd` checks
  them by `decide`.
-/

namespace Formal.Cells.ResetGcd
open Formal.Cells Formal.Cells.TernarySound Formal.Cells.ResetContract

/-- One node of the imported network: its `Circ` node, whether it is a control
node, its rank, its reset value (certificate). -/
structure NInfo where
  node : Node
  ctl : Bool
  rank : Nat
  rv : Bool

def NInfo.dflt : NInfo := ⟨.input, false, 0, false⟩

/-- A Braun tree: index 0 at the root, odd `n` in the left subtree at `n / 2`,
even `n > 0` in the right one at `n / 2 - 1` (logarithmic lookup in the kernel). -/
inductive BT where
  | leaf
  | br (l : BT) (v : NInfo) (r : BT)

def BT.get : BT → Nat → NInfo
  | .leaf, _ => NInfo.dflt
  | .br l v r, n => if n = 0 then v else if n % 2 = 1 then l.get (n / 2) else r.get (n / 2 - 1)

/-- Extra INITs (the others are `ResetContract`'s). -/
def I_arb5 : Nat := 0xACACACAC
def I_grant5 : Nat := 0xA0A0A0A0
def I_steer5 : Nat := 0x22222222
/-- `bdc_muxn3_32`'s `|j` (yosys-inferred OR of the three joins, H_INFER_OR3). -/
def I_or3 : Nat := 0xFE
theorem I_arb5_eq : I_arb5 = I_arb % 2 ^ 32 := by decide
theorem I_grant5_eq : I_grant5 = I_grant % 2 ^ 32 := by decide
theorem I_steer5_eq : I_steer5 = I_steer % 2 ^ 32 := by decide

abbrev p (i : Nat) : Src := .node i
/-- A control gate. -/
def G (init : Nat) (pins : List Src) (rk : Nat) (rv : Bool) : NInfo := ⟨.gate init pins, true, rk, rv⟩
/-- The rst input (control, reset value 1). -/
def RIn : NInfo := ⟨.input, true, 0, true⟩
/-- A data net (free input, not control). -/
def DIn : NInfo := ⟨.input, false, 0, false⟩

"""


def braun_defs(M, depth_cut=6):
    """BT.get's layout (root 0; odd n in the left subtree at n / 2, even n > 0 in the right
    one at n / 2 - 1), subtrees at depth `depth_cut` inlined, the levels above them as
    post-order `def tK`. A subtree is the affine map local j -> a*j + b."""
    lines = []
    cnt = [0]

    def inline(a, b):
        if b >= M:
            return "BT.leaf"
        return f"(BT.br {inline(2 * a, a + b)} n{b} {inline(2 * a, 2 * a + b)})"

    def rec(a, b, d):
        if b >= M:
            return "BT.leaf"
        if d == depth_cut:
            s = inline(a, b)
        else:
            l = rec(2 * a, a + b, d + 1)
            r = rec(2 * a, 2 * a + b, d + 1)
            s = f"(BT.br {l} n{b} {r})"
        cnt[0] += 1
        lines.append(f"def t{cnt[0]} : BT := {s}")
        return f"t{cnt[0]}"
    top = rec(1, 0, 0)
    return lines, top


def lean_text(nodes, val, rank):
    L = [HEADER.rstrip("\n") + "\n"]
    out = []
    for j, n in enumerate(nodes):
        if n["kind"] == "rst":
            out.append(f"def n{j} : NInfo := RIn  -- {n['name']}")
        elif n["kind"] == "data":
            out.append(f"def n{j} : NInfo := DIn  -- data: {n['name']}")
        else:
            ps = ", ".join(f"p {s[1]}" if s[0] == "n" else f"k{s[1]}" for s in n["src"])
            nm = INITV.get(n["init"])
            assert nm is not None, f"INIT {n['init']:#x} has no name"
            rv = "true" if val[j] == 1 else "false"
            out.append(f"def n{j} : NInfo := G {nm} [{ps}] {rank[j]} {rv}  -- {n['name']}")
    defs, top = braun_defs(len(nodes))
    txt = "\n".join([HEADER.rstrip("\n"), ""] + out + [""] + defs +
                    ["", "/-- Number of nodes. -/", f"def gM : Nat := {len(nodes)}", f"def gTree : BT := {top}",
                     "", "end Formal.Cells.ResetGcd", ""])
    return txt


def compare(new, old):
    if new == old:
        return "IDENTICAL (byte for byte)"
    a, b = new.split("\n"), old.split("\n")
    diffs = [(i + 1, x, y) for i, (x, y) in enumerate(zip(a, b)) if x != y]
    msg = [f"DIFFER: {len(diffs)} differing lines of {len(b)} (lengths {len(a)} / {len(b)})"]
    for i, x, y in diffs[:40]:
        msg.append(f"  line {i}:\n    new: {x[:200]}\n    old: {y[:200]}")
    return "\n".join(msg)


def cmd_net(outdir):
    os.makedirs(outdir, exist_ok=True)
    kv = emit_kernel()
    open(os.path.join(outdir, "gcd.v"), "w").write(kv)
    E = elaborate(kv)
    nodes, drv, classify, gidx, idx_data = build(E)
    val, rank = certs(nodes)
    txt = lean_text(nodes, val, rank)
    open(os.path.join(outdir, "ResetGcdNet.lean"), "w").write(txt)
    old = open(COMMITTED).read()
    ng = sum(n["kind"] == "gate" for n in nodes)
    nd = sum(n["kind"] == "data" for n in nodes)
    print(f"kernel sha256 {hashlib.sha256(kv.encode()).hexdigest()}; {len(E.cells)} LUT cells elaborated")
    print(f"net: {len(nodes)} nodes = 1 rst + {nd} data + {ng} control LUT outputs; "
          f"max rank {max(rank)}; reset-1 nodes {[i for i in range(len(nodes)) if val[i] == 1]}")
    print("vs committed ResetGcdNet.lean:", compare(txt, old))
    # net -> node table for the channel map (every named bit of every scope)
    net2node = {}
    for b, (path, nm) in enumerate(E.bitname):
        if nm.startswith("<"):
            continue
        k = classify(b)
        key = ".".join(list(path) + [nm])
        if k[0] == "gate":
            net2node[key] = gidx[id(k[1])]
        elif k[0] == "rst":
            net2node[key] = 0
        elif k[0] == "k":
            net2node[key] = f"k{k[1]}"
        elif k[0] == "data":
            net2node[key] = idx_data.get(k[1], "data")
        elif k[0] == "infer":
            net2node[key] = "infer"
    # readers per wire: control-gate pins (node, pin index) whose bit is in the net's ufw class
    pinbit = {}
    for rec in nodes:
        if rec.get("kind") == "gate":
            for k, b in enumerate(rec["pins"]):
                if isinstance(b, int):
                    pinbit.setdefault(E.ufw.find(b), []).append([gidx[id(rec)], k])
    readers = {}
    for b, (path, nm) in enumerate(E.bitname):
        if nm.startswith("<") or not re.search(r"(req|ack)$|^(r|a)\[\d+\]$", nm):
            continue
        readers[".".join(list(path) + [nm])] = sorted(pinbit.get(E.ufw.find(b), []))
    json.dump(dict(kernel_sha256=hashlib.sha256(kv.encode()).hexdigest(), readers=readers,
                   nodes=[dict(i=i, kind=n["kind"], name=n["name"], full=n["full"]) for i, n in enumerate(nodes)],
                   net2node=net2node), open(os.path.join(outdir, "net.json"), "w"))


if __name__ == "__main__":
    if len(sys.argv) >= 3 and sys.argv[1] == "net":
        cmd_net(sys.argv[2])
    elif len(sys.argv) >= 4 and sys.argv[1] == "map":
        import capmap
        capmap.main(sys.argv[2], sys.argv[3])
    else:
        print(__doc__)
        sys.exit(2)
