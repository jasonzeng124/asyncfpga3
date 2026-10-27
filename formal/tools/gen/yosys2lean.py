#!/usr/bin/env python3
"""yosys2lean.py (11d) -- yosys `write_json` netlists -> Lean `Formal.Gen.Netlist` values.

Usage:
    yosys2lean.py OUT.lean T1.json [T2.json ...]

Each Ti.json comes from formal/tools/gen/gen.sh (synth_xilinx, out of context,
-noiopad): one top module plus the "target" line of targets.txt. The Lean name
of the netlist is the file name (`bd_link_W2.json` -> `bd_link_W2`).

Extends 11a's formal/tools/import/yosys2lean.py (copied, not shared) to every
primitive the library and the fixtures synthesize to:

  LUT1..LUT6, LUT6_2            INIT as a Nat
  MUXF7, MUXF8                  I0 I1 S -> O
  CARRY4                        CI CYINIT DI[3:0] S[3:0] -> O[3:0] CO[3:0]
  FDRE FDSE FDCE FDPE           C CE D R|S|CLR|PRE -> Q, plus a SYNTHETIC
                                master-latch net (pin M, named "<Q>$master"),
                                see Formal/Gen/Netlist.lean (H_FF_MS)
  LDCE LDPE                     CLR|PRE D G GE -> Q
  BUFG                          I -> O (identity)
  RAMB18E1 (and any RAMB*)      OPAQUE: imported with every pin and net, but its
                                outputs evaluate to `none` (not modelled)

Everything else is an import ERROR (exit 1), as are: x/z constants, multiply
driven nets, read-but-undriven nets, a pin set that does not match the
primitive, an INIT that is not 2^k binary digits, any IS_*_INVERTED = 1 on a
flip-flop or latch, and a combinational cycle the cut below does not break.

State (the nets whose values are the netlist's state, see Netlist.lean):
  1. the Q (and synthetic M) nets of every flip-flop / latch primitive;
  2. every LUT/MUX output net read back by the cell that drives it (the
     library's deliberate feedback loops: C-elements, latches);
  3. then, targets of DFS back edges over what remains (deterministic order).
For every library cell 3. is empty (gen.sh records the cut per netlist).

Output is deterministic: no timestamps, no absolute paths, sorted.
"""
import json
import os
import re
import sys

LUT_RE = re.compile(r"^LUT([1-6])$")
IGNORED = {"$scopeinfo"}
REPO_MARK = "cells/rtl/"

# primitive -> (input pins, output pins, lean kind, INIT width or None)
PRIMS = {
    "LUT6_2": (["I0", "I1", "I2", "I3", "I4", "I5"], ["O5", "O6"], ".lut6_2", 64),
    "MUXF7": (["I0", "I1", "S"], ["O"], ".muxf7", None),
    "MUXF8": (["I0", "I1", "S"], ["O"], ".muxf8", None),
    "CARRY4": (["CI", "CYINIT", "DI", "S"], ["O", "CO"], ".carry4", None),
    "FDRE": (["C", "CE", "D", "R"], ["Q"], ".fdre", 1),
    "FDSE": (["C", "CE", "D", "S"], ["Q"], ".fdse", 1),
    "FDCE": (["C", "CE", "CLR", "D"], ["Q"], ".fdce", 1),
    "FDPE": (["C", "CE", "PRE", "D"], ["Q"], ".fdpe", 1),
    "LDCE": (["CLR", "D", "G", "GE"], ["Q"], ".ldce", 1),
    "LDPE": (["PRE", "D", "G", "GE"], ["Q"], ".ldpe", 1),
    "BUFG": (["I"], ["O"], '.buf "BUFG"', None),
}
FFS = {"FDRE", "FDSE", "FDCE", "FDPE"}
SEQ = FFS | {"LDCE", "LDPE"}
OPAQUE_RE = re.compile(r"^RAMB(18|36)E1$")
# pins of these widths are bit-blasted with an index suffix (CARRY4 DI -> DI0..DI3)
MULTI = {("CARRY4", "DI"), ("CARRY4", "S"), ("CARRY4", "O"), ("CARRY4", "CO")}


def die(msg):
    print(f"yosys2lean: ERROR: {msg}", file=sys.stderr)
    sys.exit(1)


def lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def src_of(bit, where):
    if isinstance(bit, int):
        return f".net {bit}"
    if bit == "0":
        return ".const false"
    if bit == "1":
        return ".const true"
    die(f"{where}: constant {bit!r} (x/z) is not modelled")


def norm_src(s):
    out = []
    for part in s.split("|"):
        i = part.find(REPO_MARK)
        out.append(part[i:] if i >= 0 else os.path.basename(part))
    return "|".join(out)


def find_top(d, path):
    tops = [n for n, m in d["modules"].items()
            if int(str(m.get("attributes", {}).get("top", "0")), 2) == 1]
    if len(tops) != 1:
        die(f"{path}: expected one top module, found {tops}")
    return tops[0]


def pinlist(typ, pins, conn, cname, path):
    """Bit-blast the named pins: [(lean pin, bit)]."""
    out = []
    for p in pins:
        bits = conn.get(p)
        if bits is None:
            die(f"{path}: {cname}: pin {p} missing")
        if (typ, p) in MULTI:
            if len(bits) != 4:
                die(f"{path}: {cname}.{p} is {len(bits)} bits, expected 4")
            out += [(f"{p}{i}", b) for i, b in enumerate(bits)]
        else:
            if len(bits) != 1:
                die(f"{path}: {cname}.{p} is {len(bits)} bits wide")
            out.append((p, bits[0]))
    return out


def lean_pin(p):
    return f".{p}" if not p.startswith("other:") else f"(.other {lean_str(p[6:])})"


def feedback_nets(cells, pre):
    """State nets beyond `pre`: targets of DFS back edges in the net graph
    (in-net -> out-net through a combinational cell), where nets in `pre`
    are sources (their incoming edges are cut). Deterministic."""
    succ = {}
    for c in cells:
        if c["seq"] or c["opaque"]:
            continue
        for o in c["outs"]:
            if o in pre:
                continue
            for _, s in c["ins"]:
                if isinstance(s, int):
                    succ.setdefault(s, set()).add(o)
    state = set()
    color = {}
    for root in sorted(succ):
        if root in color:
            continue
        stack = [(root, iter(sorted(succ.get(root, ()))))]
        color[root] = 1
        while stack:
            n, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                color[n] = 2
                stack.pop()
            elif color.get(nxt) == 1:
                state.add(nxt)
            elif nxt not in color:
                color[nxt] = 1
                stack.append((nxt, iter(sorted(succ.get(nxt, ())))))
    return state


def convert(path):
    with open(path) as fh:
        d = json.load(fh)
    top = find_top(d, path)
    m = d["modules"][top]
    name = os.path.splitext(os.path.basename(path))[0]
    target = d.get("target", "?")
    cells = []
    drivers = {}
    maxbit = max([b for nn in m["netnames"].values() for b in nn["bits"] if isinstance(b, int)] + [1])
    synth_next = [maxbit + 1]
    synth_names = {}
    for cname in sorted(m["cells"]):
        c = m["cells"][cname]
        typ = c["type"]
        conn = c["connections"]
        params = c.get("parameters", {})
        attrs = c.get("attributes", {})
        if typ in IGNORED:
            if conn:
                die(f"{path}: {cname}: {typ} with connections")
            continue
        lm = LUT_RE.match(typ)
        opaque = False
        if lm:
            k = int(lm.group(1))
            ipins, opins, kind, iw = [f"I{i}" for i in range(k)], ["O"], f".lut {k}", 2 ** k
        elif typ in PRIMS:
            ipins, opins, kind, iw = PRIMS[typ]
        elif OPAQUE_RE.match(typ):
            opaque = True
            dirs = c.get("port_directions", {})
            if set(dirs) != set(conn):
                die(f"{path}: {cname}: opaque {typ} without port directions")
            ipins = sorted(p for p in conn if dirs[p] == "input")
            opins = sorted(p for p in conn if dirs[p] == "output")
            if set(ipins) | set(opins) != set(conn):
                die(f"{path}: {cname}: opaque {typ} has inout pins")
            iw = None
        else:
            die(f"{path}: cell {cname}: type {typ} is not modelled")
        if not opaque and set(conn) != set(ipins) | set(opins):
            die(f"{path}: cell {cname} ({typ}): pins {sorted(conn)} != {sorted(ipins + opins)}")
        init = 0
        if iw is not None:
            s = params.get("INIT")
            if s is None or len(s) != iw or set(s) - {"0", "1"}:
                die(f"{path}: cell {cname}: INIT {s!r} is not {iw} binary digits")
            init = int(s, 2)
        if typ in SEQ:
            for pn, pv in params.items():
                if pn.startswith("IS_") and pn.endswith("_INVERTED") and set(str(pv)) - {"0"}:
                    die(f"{path}: {cname}: {pn}={pv}: inverted pins are not modelled")
        if opaque:
            ins, outs = [], []
            for p in ipins:
                for i, b in enumerate(conn[p]):
                    ins.append((f"other:{p}[{i}]", b))
            for p in opins:
                for i, b in enumerate(conn[p]):
                    if not isinstance(b, int):
                        die(f"{path}: {cname}.{p}[{i}] output tied to {b}")
                    outs.append((f"other:{p}[{i}]", b))
            kind = f'(.opaque {lean_str(typ)} [{", ".join(lean_str(p[6:]) for p, _ in outs)}])'
        else:
            ins = pinlist(typ, ipins, conn, cname, path)
            outs = pinlist(typ, opins, conn, cname, path)
            for p, b in outs:
                if not isinstance(b, int):
                    die(f"{path}: {cname}.{p} output is not a net: {b}")
        if typ in FFS:          # synthetic master-latch node
            qn = outs[0][1]
            mb = synth_next[0]
            synth_next[0] += 1
            synth_names[mb] = qn
            outs.append(("M", mb))
        for p, b in outs:
            if b in drivers:
                die(f"{path}: net {b} driven by {drivers[b]} and {cname}.{p}")
            drivers[b] = f"{cname}.{p}"
        cells.append(dict(name=cname, typ=typ, kind=kind, init=init, iw=iw,
                          keep=int(str(attrs.get("keep", "0")), 2) == 1,
                          ins=ins, outs_p=outs, outs=[b for _, b in outs],
                          seq=typ in SEQ, opaque=opaque,
                          src=norm_src(attrs.get("src", ""))))
    inputs, outputs = [], []
    for pname, p in m["ports"].items():          # declaration order
        bits = p["bits"]
        for i, b in enumerate(bits):
            label = pname if len(bits) == 1 else f"{pname}[{i}]"
            if p["direction"] == "input":
                if not isinstance(b, int):
                    die(f"{path}: input {label} tied to constant {b}")
                if b in drivers:
                    die(f"{path}: input {label} is driven inside")
                inputs.append((label, b))
            elif p["direction"] == "output":
                outputs.append((label, src_of(b, label)))
            else:
                die(f"{path}: port {label}: direction {p['direction']}")
    inset = {b for _, b in inputs}
    for c in cells:
        for pin, s in c["ins"]:
            if isinstance(s, int) and s not in drivers and s not in inset:
                die(f"{path}: {c['name']}.{pin} reads undriven net {s}")
    for label, s in outputs:
        if s.startswith(".net"):
            b = int(s.split()[1])
            if b not in drivers and b not in inset:
                die(f"{path}: output {label} is undriven")
    names = {}
    for nn in sorted(m["netnames"]):
        nb = m["netnames"][nn]["bits"]
        for i, b in enumerate(nb):
            if isinstance(b, int):
                names.setdefault(b, []).append(nn if len(nb) == 1 else f"{nn}[{i}]")

    def best(b):
        if b in synth_names:
            return best(synth_names[b]) + "$master"
        cand = names.get(b, [f"${b}"])
        pub = [c for c in cand if not c.startswith("$")]
        return sorted(pub or cand, key=lambda s: (len(s), s))[0]

    # state: 1. sequential outputs, 2. self-read comb outputs, 3. DFS back edges
    st_seq = {b for c in cells if c["seq"] for b in c["outs"]}
    st_self = {o for c in cells if not c["seq"] and not c["opaque"]
               for o in c["outs"] if any(s == o for _, s in c["ins"])}
    st_dfs = feedback_nets(cells, st_seq | st_self)
    state = sorted(st_seq | st_self | st_dfs)
    return dict(name=name, top=top, target=target, cells=cells, inputs=inputs,
                outputs=outputs, state=state, st_dfs=sorted(st_dfs), best=best,
                creator=d.get("creator", "?"))


def emit(mods):
    L = []
    w = L.append
    w("import Formal.Gen.Netlist")
    w("")
    w("/-! GENERATED by formal/tools/gen/yosys2lean.py -- DO NOT EDIT.")
    w("Regenerate: formal/tools/gen/gen.sh ; drift check: formal/tools/gen/gen.sh --check")
    w("")
    w("Producer: " + "; ".join(sorted({m["creator"] for m in mods})))
    w("Flow per target (formal/tools/gen/targets.txt), from cells/:")
    w("    read_verilog -lib -specify $TC/openxc7/share/yosys/xilinx/cells_sim.v")
    w("    read_verilog [-D<DEF>] rtl/*.v            (prims_*: formal/tools/gen/test/prims.v)")
    w("    chparam -set <P> <V> <top>                (parameterized targets)")
    w("    synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -noclkbuf -noiopad -top <top>")
    w("    write_json")
    w("-/")
    w("")
    w("namespace Formal.Gen.Cells")
    w("open Formal.Gen")
    w("")
    for md in mods:
        w(f"/-- target `{md['target']}` -/")
        w(f"def {md['name']} : Netlist where")
        w(f"  top := {lean_str(md['top'])}")
        w(f"  target := {lean_str(md['target'])}")
        w("  inputs := [" + ", ".join(f"({lean_str(n)}, {b})" for n, b in md["inputs"]) + "]")
        w("  outputs := [" + ", ".join(f"({lean_str(n)}, {s})" for n, s in md["outputs"]) + "]")
        w("  state := [" + ", ".join(str(s) for s in md["state"]) + "]")
        w("  cut := [" + ", ".join(str(s) for s in md["st_dfs"]) + "]")
        used = sorted({b for c in md["cells"] for _, b in c["ins"] if isinstance(b, int)}
                      | {b for c in md["cells"] for b in c["outs"]}
                      | {b for _, b in md["inputs"]}
                      | {int(s.split()[1]) for _, s in md["outputs"] if s.startswith(".net")})
        w("  nets := [" + ", ".join(f"({b}, {lean_str(md['best'](b))})" for b in used) + "]")
        w("  cells := [")
        for i, c in enumerate(md["cells"]):
            sep = "," if i + 1 < len(md["cells"]) else ""
            conn = [f"({lean_pin(p)}, {src_of(s, c['name'])})" for p, s in c["ins"]]
            conn += [f"({lean_pin(p)}, .net {b})" for p, b in c["outs_p"]]
            if c["iw"] is None:
                init = "0"
            elif c["iw"] == 1:
                init = str(c["init"])
            else:
                init = f"0x{c['init']:0{max(c['iw'] // 4, 1)}X}"
            w(f"    -- {c['typ']}  {c['src'] or 'no src (inserted by synthesis)'}")
            w(f"    {{ name := {lean_str(c['name'])}, kind := {c['kind']}, "
              f"init := {init}, keep := {'true' if c['keep'] else 'false'},")
            w(f"      conn := [{', '.join(conn)}] }}{sep}")
        w("  ]")
        w("")
    w("/-- Every generated netlist, in targets.txt order. -/")
    w("def all : List Netlist := [" + ", ".join(m["name"] for m in mods) + "]")
    w("")
    w("end Formal.Gen.Cells")
    return "\n".join(L) + "\n"


def main():
    if len(sys.argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    out = sys.argv[1]
    mods = [convert(p) for p in sys.argv[2:]]
    text = emit(mods)
    if out == "-":
        sys.stdout.write(text)
    else:
        with open(out, "w") as fh:
            fh.write(text)
    for md in mods:
        kinds = {}
        for c in md["cells"]:
            kinds[c["typ"]] = kinds.get(c["typ"], 0) + 1
        print(f"[yosys2lean] {md['name']:22s} {len(md['inputs'])} in, {len(md['state'])} state"
              f"{' (DFS cut ' + str(len(md['st_dfs'])) + ')' if md['st_dfs'] else ''}: "
              + ", ".join(f"{k}x{v}" for k, v in sorted(kinds.items())), file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
