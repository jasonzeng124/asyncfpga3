#!/usr/bin/env python3
"""Every refusal bdc/emit.py would reach on a frontend output, not just the first one it raises.

    python3 research/tools/suite/dyn_blockers.py OUT.tsv name [name ...]

bdc/emit.py stops at its first EmitError, so its message names one blocker per test.  A feature ranking needs all of
them: a test that needs a load-store queue AND a divider is not unlocked by either alone.  This reads
build/frontend/<name>/comp/handshake_transformed.mlir with bdc's own parser and applies the same tests emit.py
applies, each one written next to the emit.py / mem.py check it mirrors:

  float        a channel or memref of f16/f32/f64, or a float op (out of scope)
  op:<name>    an op with no width rule in emit.py result_channels() (divsi, divui, remsi, remui, ...)
  lsq          an `lsq` op: Dynamatic placed a load-store queue (bd-config.json: todo; no width rule)
  ram          an internal or constant array (generic-syntax "handshake.ram"): bdc/hs/parse.py does not parse it
  mem>1024     a memref deeper than one bd_mem (mem.py check(): RAM_WORDS = 1024)
  mc:store     a mem_controller with a store accessor (emit.py _op_mem_controller: no remainingStores counter)
  mc:load1st   a mem_controller with two accessors, the first a load (emit.py _resolve_mem_accessors: the token
               chain takes the first accessor's z, which only a store leaves free)
  mc:>2        a mem_controller with more than two accessors (emit.py _resolve_mem_accessors / mem.py emit_port:
               bd_arbiter takes two requesters; N needs a tree)

It also writes each controller's accessor shape in program order (L = load, S = store; e.g. `LS` = load then store)
and the op histogram.  A test with no blocker here should emit, and emit.py's first error should be in the set:
both held on all 114 frontend outputs of 2026-11-17 (research/data/suite/dyn/README.md).  The counts this feeds are
UPPER BOUNDS on what a fix unlocks: emit.py's later stages (link sites, ring depths) are past these refusals, and
research/tools/suite/dyn_whatif.py is the check that they do not refuse again.
"""
import collections
import os
import re
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "bdc"))
from hs import parse  # noqa: E402

# emit.py result_channels(): the ops it has a width rule for.
SUPPORTED = {"fork", "lazy_fork", "source", "constant", "cmpi", "addi", "subi", "muli", "andi", "ori", "xori",
             "shli", "shrsi", "shrui", "select", "cond_br", "br", "buffer", "merge", "trunci", "extui", "extsi",
             "mux", "control_merge", "sink", "end", "join", "load", "store", "mem_controller"}
RAM_WORDS = 1024  # bdc/mem.py


def is_float_op(op):
    return op in ("sitofp", "uitofp", "fptosi", "fptoui") or re.fullmatch(r"(add|sub|mul|div|cmp|neg|abs|ext|trunc|"
                                                                          r"max|min|maximum|minimum|sqrt|rem)f", op)


def analyse(mlir):
    text = open(mlir).read()
    out, shapes, hist = set(), [], collections.Counter()
    if re.search(r'"handshake\.ram"', text):
        out.add("ram")
        return out, shapes, hist        # the parser stops here; nothing below can be read
    f = [x for x in parse.parse_module(text, filename=mlir) if not x.is_declaration][0]
    for a in f.args:
        if a.raw.startswith("memref"):
            m = re.fullmatch(r"memref<(\d+)x([iuf])(\d+)>", a.raw)
            if not m:
                out.add("memref:" + a.raw)
            elif m.group(2) == "f":
                out.add("float")
            elif (1 << max(1, (int(m.group(1)) - 1).bit_length())) > RAM_WORDS:
                out.add("mem>1024")
    producer = {r: i for i, n in enumerate(f.nodes) for r in n.results}
    for n in f.nodes:
        hist[n.op] += 1
        if re.search(r"<f(16|32|64)>|xf(16|32|64)>", n.type_sig or "") or is_float_op(n.op):
            out.add("float")
        elif n.op == "lsq":
            out.add("lsq")
        elif n.op not in SUPPORTED:
            out.add("op:" + n.op)
        if n.op == "mem_controller":
            ordered, seen = [], set()
            for v in n.operands[2:-1]:
                p = producer.get(v)
                pop = f.nodes[p].op if p is not None else None
                if pop == "constant":
                    continue
                if pop not in ("load", "store"):
                    shapes.append(f"<{pop}>")       # an MC serving an LSQ: the lsq blocker covers it
                    continue
                if p not in seen:
                    seen.add(p)
                    ordered.append(pop)
            shape = "".join("L" if o == "load" else "S" for o in ordered)
            shapes.append(shape)
            if "S" in shape:
                out.add("mc:store")
            if len(ordered) > 2:
                out.add("mc:>2")
            elif len(ordered) == 2 and ordered[0] == "load":
                out.add("mc:load1st")
    return out, shapes, hist


def main():
    dst, names = sys.argv[1], sys.argv[2:]
    with open(dst, "w") as fo:
        fo.write("name\tblockers\tmc_shapes\tops\n")
        for name in names:
            mlir = os.path.join(ROOT, "build", "frontend", name, "comp", "handshake_transformed.mlir")
            if not os.path.exists(mlir):
                fo.write(f"{name}\t(no frontend output)\t\t\n")
                continue
            b, shapes, hist = analyse(mlir)
            ops = " ".join(f"{k}:{v}" for k, v in sorted(hist.items()))
            fo.write(f"{name}\t{','.join(sorted(b)) or '-'}\t{' '.join(shapes) or '-'}\t{ops}\n")


if __name__ == "__main__":
    main()
