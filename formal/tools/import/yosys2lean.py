#!/usr/bin/env python3
"""yosys2lean.py -- turn yosys `write_json` netlists of library cells into Lean.

Usage:
    yosys2lean.py OUT.lean SPEC.json [SPEC.json ...]

Each SPEC.json is a yosys JSON file produced by formal/tools/import/import.sh
(the project's synth_xilinx flow). The module to import is the JSON's single
non-blackbox module whose `top` attribute is 1; its Lean name is taken from the
file name (`bd_c2.json` -> `bd_c2`, `bd_latch_W3.json` -> `bd_latch_W3`).

Emitted, per module, one `Formal.Net.Import.Netlist` value with:
  * cells : type, INIT as a Nat, `(* keep *)` flag, and the pin -> net map,
  * nets  : bit id -> name,
  * inputs / outputs : port name (bit-blasted, `d[1]`) -> net,
  * state : the feedback nets cut to break every combinational cycle (the
    targets of DFS back edges). Their values are the netlist's state.

The output is deterministic (sorted, no timestamps, no absolute paths) so a
drift check can compare it byte for byte. The script FAILS (exit 1) on
anything it does not model: an unknown cell type, an x/z constant, a
multiply driven net, a missing LUT pin, an INIT whose width is not 2^k.
"""
import json
import os
import re
import sys

LUT_RE = re.compile(r"^LUT([1-6])$")
IGNORED = {"$scopeinfo"}          # yosys hierarchy bookkeeping, no connections
OUT_PINS = {"LUT6_2": ["O5", "O6"], "IBUF": ["O"], "OBUF": ["O"]}
IN_PINS = {"LUT6_2": ["I0", "I1", "I2", "I3", "I4", "I5"], "IBUF": ["I"], "OBUF": ["I"]}
REPO_MARK = "cells/rtl/"


def die(msg):
    print(f"yosys2lean: ERROR: {msg}", file=sys.stderr)
    sys.exit(1)


def lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def pins_of(typ):
    m = LUT_RE.match(typ)
    if m:
        k = int(m.group(1))
        return [f"I{i}" for i in range(k)], ["O"], k
    if typ in IN_PINS:
        return IN_PINS[typ], OUT_PINS[typ], 6 if typ == "LUT6_2" else None
    return None


def kind_of(typ):
    m = LUT_RE.match(typ)
    if m:
        return f".lut {m.group(1)}"
    return {"LUT6_2": ".lut6_2", "IBUF": ".ibuf", "OBUF": ".obuf"}[typ]


def src_of(bit, where):
    if isinstance(bit, int):
        return f".net {bit}"
    if bit == "0":
        return ".const false"
    if bit == "1":
        return ".const true"
    die(f"{where}: constant {bit!r} (x/z) is not modelled")


def norm_src(s):
    """Strip the machine-dependent prefix of a yosys src attribute."""
    out = []
    for part in s.split("|"):
        i = part.find(REPO_MARK)
        out.append(part[i:] if i >= 0 else os.path.basename(part))
    return "|".join(out)


def find_top(d, path):
    tops = [n for n, m in d["modules"].items()
            if int(m.get("attributes", {}).get("top", "0"), 2) == 1]
    if len(tops) != 1:
        die(f"{path}: expected one top module, found {tops}")
    return tops[0]


def feedback_nets(cells, drivers):
    """Targets of DFS back edges in the net graph (in-net -> out-net through a
    cell). Deterministic: nets visited in increasing id order. Iterative."""
    succ = {}
    for c in cells:
        for o in c["outs"]:
            for _, s in c["ins"]:
                if isinstance(s, int):
                    succ.setdefault(s, set()).add(o)
    state = set()
    color = {}
    for root in sorted(set(succ) | set(drivers)):
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
                state.add(nxt)                       # back edge: cut here
            elif nxt not in color:
                color[nxt] = 1
                stack.append((nxt, iter(sorted(succ.get(nxt, ())))))
    return sorted(state)


def convert(path):
    with open(path) as fh:
        d = json.load(fh)
    top = find_top(d, path)
    m = d["modules"][top]
    name = os.path.splitext(os.path.basename(path))[0]
    cells = []
    drivers = {}
    for cname in sorted(m["cells"]):
        c = m["cells"][cname]
        typ = c["type"]
        if typ in IGNORED:
            if c.get("connections"):
                die(f"{path}: {cname}: {typ} with connections")
            continue
        p = pins_of(typ)
        if p is None:
            die(f"{path}: cell {cname}: type {typ} is not modelled")
        ipins, opins, k = p
        conn = c["connections"]
        if set(conn) != set(ipins) | set(opins):
            die(f"{path}: cell {cname}: pins {sorted(conn)} != {sorted(ipins + opins)}")
        init = 0
        if k is not None:
            s = c["parameters"].get("INIT")
            if s is None or len(s) != 2 ** k or set(s) - {"0", "1"}:
                die(f"{path}: cell {cname}: INIT {s!r} is not {2 ** k} binary digits")
            init = int(s, 2)
        elif c["parameters"]:
            # IBUF/OBUF parameters (IOSTANDARD, ...) do not change the logic
            pass
        ins = []
        for pin in ipins:
            bits = conn[pin]
            if len(bits) != 1:
                die(f"{path}: {cname}.{pin} is {len(bits)} bits wide")
            ins.append((pin, bits[0]))
        outs = []
        for pin in opins:
            bits = conn[pin]
            if len(bits) != 1 or not isinstance(bits[0], int):
                die(f"{path}: {cname}.{pin} output is not one net: {bits}")
            if bits[0] in drivers:
                die(f"{path}: net {bits[0]} driven by {drivers[bits[0]]} and {cname}.{pin}")
            drivers[bits[0]] = f"{cname}.{pin}"
            outs.append((pin, bits[0]))
        attrs = c.get("attributes", {})
        keep = int(attrs.get("keep", "0"), 2) == 1 if "keep" in attrs else False
        cells.append(dict(name=cname, typ=typ, init=init, k=k, keep=keep,
                          ins=ins, outs_p=outs, outs=[b for _, b in outs],
                          src=norm_src(attrs.get("src", ""))))
    inputs, outputs = [], []
    for pname, p in m["ports"].items():          # declaration order
        bits = p["bits"]
        for i, b in enumerate(bits):
            label = pname if len(bits) == 1 else f"{pname}[{i}]"
            if not isinstance(b, int):
                die(f"{path}: port {label} tied to constant {b}")
            if p["direction"] == "input":
                if b in drivers:
                    die(f"{path}: input {label} is driven inside")
                inputs.append((label, b))
            elif p["direction"] == "output":
                outputs.append((label, b))
            else:
                die(f"{path}: port {label}: direction {p['direction']}")
    # every used net must have a driver or be an input
    inset = {b for _, b in inputs}
    for c in cells:
        for pin, s in c["ins"]:
            if isinstance(s, int) and s not in drivers and s not in inset:
                die(f"{path}: {c['name']}.{pin} reads undriven net {s}")
    names = {}
    for nn in sorted(m["netnames"]):
        nb = m["netnames"][nn]["bits"]
        for i, b in enumerate(nb):
            if isinstance(b, int):
                names.setdefault(b, []).append(nn if len(nb) == 1 else f"{nn}[{i}]")

    def best(b):
        cand = names.get(b, [f"${b}"])
        pub = [c for c in cand if not c.startswith("$")]
        return sorted(pub or cand, key=lambda s: (len(s), s))[0]
    state = feedback_nets(cells, drivers)
    return dict(name=name, top=top, cells=cells, inputs=inputs, outputs=outputs,
                state=state, nets=sorted(names), best=best, creator=d.get("creator", "?"))


def emit(mods, script):
    L = []
    w = L.append
    w("import Formal.Net.Import.Netlist")
    w("")
    w("/-! GENERATED by formal/tools/import/yosys2lean.py -- DO NOT EDIT.")
    w("Regenerate: formal/tools/import/import.sh ; drift check: import.sh --check")
    creators = sorted({m["creator"] for m in mods})
    w("")
    w("Producer: " + "; ".join(creators))
    w("Flow (per cell, same options as cells/flow.sh and cells/verify/lutcost.py):")
    for line in script.strip().splitlines():
        w("    " + line)
    w("-/")
    w("")
    w("namespace Formal.Net.Import.Gen")
    w("open Formal.Net.Import")
    w("")
    for md in mods:
        w(f"/-- `{md['top']}` as synthesized (`{md['name']}.json`). -/")
        w(f"def {md['name']} : Netlist where")
        w(f"  top := {lean_str(md['top'])}")
        w("  inputs := [" + ", ".join(f"({lean_str(n)}, {b})" for n, b in md["inputs"]) + "]")
        w("  outputs := [" + ", ".join(f"({lean_str(n)}, {b})" for n, b in md["outputs"]) + "]")
        w("  state := [" + ", ".join(str(s) for s in md["state"]) + "]")
        used = sorted({b for c in md["cells"] for _, b in c["ins"] if isinstance(b, int)}
                      | {b for c in md["cells"] for b in c["outs"]}
                      | {b for _, b in md["inputs"] + md["outputs"]})
        w("  nets := [" + ", ".join(f"({b}, {lean_str(md['best'](b))})" for b in used) + "]")
        w("  cells := [")
        for i, c in enumerate(md["cells"]):
            sep = "," if i + 1 < len(md["cells"]) else ""
            conn = [f"(.{p}, {src_of(s, c['name'])})" for p, s in c["ins"]]
            conn += [f"(.{p}, .net {b})" for p, b in c["outs_p"]]
            init = f"0x{c['init']:0{(2 ** c['k']) // 4 or 1}X}" if c["k"] else "0"
            w(f"    -- {c['src'] or 'no src: inserted by synth_xilinx'}")
            w(f"    {{ name := {lean_str(c['name'])}, kind := {kind_of(c['typ'])}, "
              f"init := {init}, keep := {'true' if c['keep'] else 'false'},")
            w(f"      conn := [{', '.join(conn)}] }}{sep}")
        w("  ]")
        w("")
    w("end Formal.Net.Import.Gen")
    return "\n".join(L) + "\n"


def main():
    if len(sys.argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    out = sys.argv[1]
    mods = [convert(p) for p in sys.argv[2:]]
    script = os.environ.get("YOSYS2LEAN_SCRIPT", "(script not recorded)")
    text = emit(mods, script)
    if out == "-":
        sys.stdout.write(text)
    else:
        with open(out, "w") as fh:
            fh.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
