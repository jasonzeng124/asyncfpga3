#!/usr/bin/env python3
"""dyn_export.py HW_MLIR OUTDIR [--dynamatic DIR] -- Dynamatic's export-rtl for the integer subset the suite uses.

Why: Dynamatic's own figure for a suite kernel is its circuit's clock period times its cycles per iteration. The
cycles are simulated (research/tools/suite/dynamatic_est.py), but the period was only ROUTED for three kernels in
2026-08 (cells/hw/dyn_baseline.sh: export-rtl, then yosys and our nextpnr); every other kernel's period is an estimate
from Dynamatic's timing model scaled by one factor fitted on those three. The owner's Dynamatic build on the cluster
($HOME/dynamatic) has dynamatic-opt (buffer placement, --lower-handshake-to-hw) and the Verilog library and RTL config
(data/), but not the export-rtl binary or its rtl-*-generator binaries. This file does what export-rtl does with
data/rtl-config-verilog.json, for what the suite needs:

  * every hw.module.extern of the lowered circuit (hw.name + hw.parameters) is matched against the config's entries
    for that name by the entries' own parameter constraints (dataflow: data-eq / data-lb / extra-eq; unsigned: eq /
    lb; string: eq); its module is the entry's module-name, or the generic file's module, or, for a generator entry,
    the extern's own name;
  * a generic entry's file is copied unchanged (with every file its dependencies name, transitively); its parameters
    that are not marked "generic": false become Verilog parameters (a dataflow type gives its data width);
  * the generator entries the integer kernels use are reproduced: handshake.cmpi (data/verilog/arith/cmpi.v with
    ENTITY_NAME, the predicate's COMPARATOR and the $signed MODIFIER for the signed predicates, as Dynamatic's
    rtl-cmpi-generator writes them) and handshake.constant (data/verilog/handshake/constant.v with ENTITY_NAME and
    VALUE = WIDTH'b<the binary string hw.parameters carries>). Any other generator entry (floating point, the LSQ,
    counter buffers) stops the export with its name: nothing is guessed;
  * the top module: the kernel's channels as Dynamatic names them (x, x_valid, x_ready; a control channel has no
    data), one wire set per SSA value, each instance connected port by port; a group of hw ports p_0 .. p_k becomes
    the module's packed port p ({p_k, ..., p_0}), as Dynamatic's library declares its arrays.

Nothing under $HOME/dynamatic is edited (CLAUDE.md: vendored, used as data). Checked by simulation against the C and
against dynamatic_est.py's cycle model (research/data/suite/dynamatic/routed/README.md)."""
import json
import os
import re
import shutil
import sys

SIGNED = {"slt": "<", "sle": "<=", "sgt": ">", "sge": ">="}
UNSIGNED = {"eq": "==", "ne": "!=", "ult": "<", "ule": "<=", "ugt": ">", "uge": ">="}


def split_top(s, sep=","):
    """split s at top-level separators (not inside <>, (), [], {} or quotes)"""
    out, depth, cur, q = [], 0, [], False
    for ch in s:
        if ch == '"':
            q = not q
        if not q:
            if ch in "<([{":
                depth += 1
            elif ch in ">)]}":
                depth -= 1
        if ch == sep and depth == 0 and not q:
            out.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if "".join(cur).strip():
        out.append("".join(cur).strip())
    return out


def width(t):
    """data width of an MLIR type: control 0, channel<iN> / iN -> N; None if not a plain integer channel"""
    t = t.strip()
    if t.startswith("!handshake.control"):
        if t != "!handshake.control<>":
            return None          # extra signals: not in the subset
        return 0
    m = re.fullmatch(r"!handshake\.channel<i(\d+)>", t)
    if m:
        return int(m.group(1))
    m = re.fullmatch(r"i(\d+)", t)
    if m:
        return int(m.group(1))
    return None


def parse_params(s):
    """'{A = !handshake.channel<i32>, SIZE = 2 : ui32, P = "sgt"}' -> {A: ('type', ...), ...}"""
    s = s.strip()
    assert s.startswith("{") and s.endswith("}"), s
    out = {}
    for kv in split_top(s[1:-1]):
        k, _, v = kv.partition("=")
        k, v = k.strip(), v.strip()
        if v.startswith('"'):
            out[k] = ("string", v.strip('"'))
        elif v.startswith("!handshake"):
            out[k] = ("dataflow", v)
        else:
            m = re.fullmatch(r"(-?\d+)\s*:\s*\w+", v)
            if not m:
                raise SystemExit("dyn_export: parameter %s = %s not understood" % (k, v))
            out[k] = ("unsigned", int(m.group(1)))
    return out


def parse_ports(s):
    """'in %a : T, out b : T' -> [(dir, name, type)]"""
    ports = []
    for p in split_top(s):
        m = re.fullmatch(r"(in|out)\s+%?([\w.]+)\s*:\s*(.+)", p.strip())
        if not m:
            raise SystemExit("dyn_export: port '%s' not understood" % p)
        ports.append((m.group(1), m.group(2), m.group(3).strip()))
    return ports


def balanced(s, i):
    """index just past the bracket group that opens at s[i]"""
    o = s[i]
    c = {"(": ")", "{": "}", "[": "]", "<": ">"}[o]
    d = 0
    for j in range(i, len(s)):
        if s[j] == o:
            d += 1
        elif s[j] == c:
            d -= 1
            if d == 0:
                return j + 1
    raise SystemExit("dyn_export: unbalanced %s at %d" % (o, i))


def parse_hw(path):
    txt = open(path).read()
    ext = {}
    for m in re.finditer(r"hw\.module\.extern\s+@(\w+)\(", txt):
        e = balanced(txt, m.end() - 1)
        ports = parse_ports(txt[m.end():e - 1])
        a = re.match(r"\s*attributes\s*", txt[e:])
        if not a:
            raise SystemExit("dyn_export: extern %s has no attributes" % m.group(1))
        ab = e + a.end()
        ae = balanced(txt, ab)
        attrs = txt[ab + 1:ae - 1]
        name = re.search(r'hw\.name\s*=\s*"([^"]+)"', attrs).group(1)
        pm = re.search(r"hw\.parameters\s*=\s*\{", attrs)
        params = parse_params(attrs[pm.end() - 1:balanced(attrs, pm.end() - 1)]) if pm else {}
        ext[m.group(1)] = {"ports": ports, "name": name, "params": params}
    # the kernel's module (export-rtl also writes a <kernel>_wrapper that only instantiates it: not needed here)
    tops = [m for m in re.finditer(r"hw\.module\s+@(\w+)\(", txt) if not m.group(1).endswith("_wrapper")]
    if len(tops) != 1:
        raise SystemExit("dyn_export: %d hw.module bodies besides *_wrapper (want 1)" % len(tops))
    m = tops[0]
    e = balanced(txt, m.end() - 1)
    tports = parse_ports(txt[m.end():e - 1])
    body = txt[txt.index("{", e) + 1:balanced(txt, txt.index("{", e)) - 1]
    insts = []
    for line in body.splitlines():
        line = line.strip()
        mi = re.match(r'(?:(.*?)\s*=\s*)?hw\.instance\s+"(\w+)"\s+@(\w+)\((.*)\)\s*->\s*\((.*)\)\s*(\{.*\})?$', line)
        if mi:
            res = [x.strip().lstrip("%") for x in mi.group(1).split(",")] if mi.group(1) else []
            ins = []
            for p in split_top(mi.group(4)):
                mp = re.fullmatch(r"(\w+)\s*:\s*%([\w.]+)\s*:\s*(.+)", p)
                if not mp:
                    raise SystemExit("dyn_export: instance operand '%s' not understood" % p)
                ins.append((mp.group(1), mp.group(2), mp.group(3)))
            outs = []
            for p in split_top(mi.group(5)):
                mp = re.fullmatch(r"(\w+)\s*:\s*(.+)", p)
                outs.append((mp.group(1), mp.group(2)))
            if len(res) != len(outs):
                raise SystemExit("dyn_export: %s: %d results for %d outputs" % (mi.group(2), len(res), len(outs)))
            insts.append({"name": mi.group(2), "ext": mi.group(3), "ins": ins,
                          "outs": [(o[0], o[1], r) for o, r in zip(outs, res)]})
            continue
        mo = re.match(r"hw\.output\s+(.*?)\s*:\s*(.*)$", line)
        if mo:
            outvals = [x.strip().lstrip("%") for x in mo.group(1).split(",")] if mo.group(1).strip() else []
        elif line and not line.startswith("}") and not line.startswith("//"):
            raise SystemExit("dyn_export: line not understood: %s" % line[:120])
    return m.group(1), tports, ext, insts, outvals


def match_entry(cfg, e):
    cands = [c for c in cfg if c.get("name") == e["name"]]
    for c in cands:
        ok = True
        for p in c.get("parameters", []):
            if p["name"] not in e["params"]:
                ok = False
                break
            kind, v = e["params"][p["name"]]
            if p["type"] == "dataflow":
                if kind != "dataflow":
                    ok = False
                    break
                w = width(v)
                if w is None:
                    ok = False
                    break
                if "data-eq" in p and w != p["data-eq"]:
                    ok = False
                if "data-lb" in p and w < p["data-lb"]:
                    ok = False
            elif p["type"] == "unsigned":
                if kind != "unsigned" or ("eq" in p and v != p["eq"]) or ("lb" in p and v < p["lb"]):
                    ok = False
            elif p["type"] == "string":
                if kind != "string" or ("eq" in p and v != p["eq"]):
                    ok = False
            if not ok:
                break
        if ok:
            return c
    raise SystemExit("dyn_export: no RTL config entry for %s %s" % (e["name"], e["params"]))


def module_ports(path, mod):
    src = open(path).read()
    m = re.search(r"\bmodule\s+" + re.escape(mod) + r"\b", src)
    if not m:
        raise SystemExit("dyn_export: no module %s in %s" % (mod, path))
    i = m.end()
    # skip a parameter block #( ... )
    j = src.index("(", i)
    if src[i:j].strip() == "#":
        i = balanced(src, j)
        j = src.index("(", i)
    plist = re.sub(r"//[^\n]*", "", src[j + 1:balanced(src, j) - 1])
    names = re.findall(r"\b(?:input|output)\s+(?:wire\s+|reg\s+)?(?:\[[^\]]*\]\s*)?(\w+)", plist)
    return set(names)


def main():
    a = [x for x in sys.argv[1:] if not x.startswith("--")]
    dyn = os.path.expanduser("~/dynamatic")
    if "--dynamatic" in sys.argv:
        dyn = sys.argv[sys.argv.index("--dynamatic") + 1]
        a = [x for x in a if x != dyn]
    hwp, out = a[0], a[1]
    cfg = json.load(open(os.path.join(dyn, "data", "rtl-config-verilog.json")))
    top, tports, ext, insts, outvals = parse_hw(hwp)
    os.makedirs(out, exist_ok=True)
    byname = {}
    for c in cfg:
        for k in ("module-name", "name"):
            if k in c:
                byname.setdefault(c[k], c)
    files, todo = {}, []

    def gfile(c):
        return c["generic"].replace("$DYNAMATIC", dyn)

    def add_deps(c):
        for d in c.get("dependencies", []):
            dc = byname.get(d)
            if dc is None:      # a support file named by its module (logic, eager_fork_register_block)
                f = os.path.join(dyn, "data", "verilog", "support", d + ".v")
                if not os.path.exists(f):
                    raise SystemExit("dyn_export: dependency %s not in the config nor data/verilog/support" % d)
                files[f] = True
                continue
            if "generic" not in dc:
                raise SystemExit("dyn_export: dependency %s needs a generator" % d)
            f = gfile(dc)
            if f not in files:
                files[f] = True
                add_deps(dc)

    modof, paramsof = {}, {}
    gen_src = {}
    for en, e in ext.items():
        c = match_entry(cfg, e)
        if "generator" in c:
            if e["name"] == "handshake.cmpi":
                pred = e["params"]["PREDICATE"][1]
                cmp_ = SIGNED.get(pred) or UNSIGNED.get(pred)
                if cmp_ is None:
                    raise SystemExit("dyn_export: cmpi predicate %s" % pred)
                src = open(os.path.join(dyn, "data/verilog/arith/cmpi.v")).read()
                src = src.replace("ENTITY_NAME", en).replace("COMPARATOR", cmp_)
                src = src.replace("MODIFIER", "$signed" if pred in SIGNED else "")
                gen_src[en] = src
            elif e["name"] == "handshake.constant":
                w = e["params"]["DATA_WIDTH"][1]
                v = e["params"]["VALUE"][1]
                if not re.fullmatch(r"[01]+", v) or len(v) != w:
                    raise SystemExit("dyn_export: constant %s VALUE %s not a %d-bit binary string" % (en, v, w))
                src = open(os.path.join(dyn, "data/verilog/handshake/constant.v")).read()
                gen_src[en] = src.replace("ENTITY_NAME", en).replace("VALUE", "%d'b%s" % (w, v))
            else:
                raise SystemExit("dyn_export: %s needs Dynamatic's generator (%s): not in the subset" % (en, e["name"]))
            modof[en] = en
            mpath = None
        else:
            f = gfile(c)
            files[f] = True
            mod = c.get("module-name") or re.search(r"\bmodule\s+(\w+)", open(f).read()).group(1)
            modof[en] = mod
            mpath = f
        add_deps(c)
        ps = []
        for p in c.get("parameters", []):
            # a generic file takes every parameter not marked "generic": false; a generator's output only the ones
            # marked "generic": true (cmpi's PREDICATE and constant's VALUE are written into the module instead)
            if p.get("generic", "generator" not in c) is False:
                continue
            kind, v = e["params"][p["name"]]
            if kind == "dataflow":
                ps.append((p["name"], width(v)))
            elif kind == "unsigned":
                ps.append((p["name"], v))
            else:
                ps.append((p["name"], '"%s"' % v))
        paramsof[en] = ps
        e["mpath"] = mpath
    # write the component files
    for f in files:
        shutil.copy(f, os.path.join(out, os.path.basename(f) if not os.path.exists(os.path.join(out, os.path.basename(f)))
                                    else os.path.basename(os.path.dirname(f)) + "_" + os.path.basename(f)))
    for en, src in gen_src.items():
        open(os.path.join(out, en + ".v"), "w").write(src)
    # port sets of every module used
    mports = {}
    for en, e in ext.items():
        p = e["mpath"] or os.path.join(out, en + ".v")
        mports[en] = module_ports(p, modof[en])
    # the top
    W = {}                                     # SSA value -> width
    L = []
    hdr = ["  input clk", "  input rst"]
    for d, n, t in tports:
        if n in ("clk", "rst"):
            continue
        w = width(t)
        if w is None:
            raise SystemExit("dyn_export: top port %s : %s not in the subset" % (n, t))
        io, ri = ("input", "output") if d == "in" else ("output", "input")
        if w:
            hdr.append("  %s [%d:0] %s" % (io, w - 1, n))
        hdr.append("  %s %s_valid" % (io, n))
        hdr.append("  %s %s_ready" % (ri, n))
        if d == "in":
            W[n] = w
    for ins in insts:
        for pn, t, r in ins["outs"]:
            w = width(t)
            if w is None:
                raise SystemExit("dyn_export: %s.%s : %s not in the subset" % (ins["name"], pn, t))
            W[r] = w
    sname = lambda v: re.sub(r"[^\w]", "_", v)
    topnames = {n for d, n, t in tports}
    for v, w in W.items():
        if v in topnames:
            continue
        s = sname(v)
        if w:
            L.append("  wire [%d:0] %s;" % (w - 1, s))
        L.append("  wire %s_valid;" % s)
        L.append("  wire %s_ready;" % s)
    L.append("")

    def conn(ports, en, pairs):
        """pairs: [(hw port, value, width, is_input)] -> Verilog .p(...) list, packing p_0..p_k"""
        groups = {}
        for hp, v, w, isin in pairs:
            m = re.fullmatch(r"(\w+?)_(\d+)", hp)
            if m and (m.group(1) in ports or m.group(1) + "_valid" in ports) and hp not in ports \
                    and hp + "_valid" not in ports:
                groups.setdefault(m.group(1), []).append((int(m.group(2)), v, w, isin))
            else:
                groups.setdefault(hp, []).append((None, v, w, isin))
        cs = []
        for p, items in groups.items():
            items.sort(key=lambda x: -1 if x[0] is None else x[0])
            vals = [sname(x[1]) for x in items][::-1]          # {p_k, ..., p_0}
            cat = lambda suf: vals[0] + suf if len(vals) == 1 else "{" + ", ".join(x + suf for x in vals) + "}"
            w = items[0][2]
            if w:
                if p not in ports:
                    raise SystemExit("dyn_export: %s (%s) has no port %s" % (en, modof[en], p))
                cs.append(".%s(%s)" % (p, cat("")))
            for suf in ("_valid", "_ready"):
                if p + suf not in ports:
                    raise SystemExit("dyn_export: %s (%s) has no port %s" % (en, modof[en], p + suf))
                cs.append(".%s(%s)" % (p + suf, cat(suf)))
        return cs

    for ins in insts:
        en = ins["ext"]
        ports = mports[en]
        pairs = [(hp, v, width(t), True) for hp, v, t in ins["ins"] if hp not in ("clk", "rst")]
        pairs += [(hp, r, width(t), False) for hp, t, r in ins["outs"]]
        cs = [".%s(%s)" % (x, x) for x in ("clk", "rst") if x in ports] + conn(ports, en, pairs)
        pstr = (" #(" + ", ".join(".%s(%s)" % kv for kv in paramsof[en]) + ")") if paramsof[en] else ""
        L.append("  %s%s %s (\n    %s\n  );" % (modof[en], pstr, ins["name"], ",\n    ".join(cs)))
    # top outputs
    outs = [(n, t) for d, n, t in tports if d == "out"]
    if len(outs) != len(outvals):
        raise SystemExit("dyn_export: %d outputs, hw.output has %d values" % (len(outs), len(outvals)))
    for (n, t), v in zip(outs, outvals):
        s = sname(v)
        if width(t):
            L.append("  assign %s = %s;" % (n, s))
        L.append("  assign %s_valid = %s_valid;" % (n, s))
        L.append("  assign %s_ready = %s_ready;" % (s, n))
    # top inputs feed their values directly: rename uses of the input SSA names (they are the port names)
    src = "module %s(\n%s\n);\n\n%s\nendmodule\n" % (top, ",\n".join(hdr), "\n".join(L))
    open(os.path.join(out, top + ".v"), "w").write(src)
    print("dyn_export: %s: %d instances, %d externs (%d generated), %d library files -> %s" % (
        top, len(insts), len(ext), len(gen_src), len(files), out))


if __name__ == "__main__":
    main()
