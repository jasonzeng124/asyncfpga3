#!/usr/bin/env python3
"""MEASUREMENT ONLY: does anything in bdc/emit.py refuse a graph AFTER a given refusal is lifted?

    python3 research/tools/suite/dyn_whatif.py BLOCKER[,BLOCKER...] MLIR [MLIR ...]

research/tools/suite/dyn_blockers.py lists every refusal emit.py reaches first; the counts it feeds are upper bounds,
because a stage past those refusals (link sites, ring depths, ...) has never seen these graphs.  This runs a copy of
bdc/emit.py, in memory, with the named refusals switched off by exact text patches (each must apply exactly once, or
this stops: a stale patch cannot silently measure nothing), and reports per file `OK` or the next error.

THE VERILOG A PATCHED EMITTER WRITES IS NOT A CIRCUIT and is never written to disk.  mc:store wires memEnd without
the store-completion counter; mc:load1st chains a token from a load whose z has another consumer (the token nets
are left undriven); mc:>2 builds an unarbitrated N-slot port; op:div* uses Verilog's / and % as a combinational unit
with the 'wide' placeholder delay; mem>1024 lifts the bd_mem depth check.  `OK` means only: no other stage refused.

Blockers: mc:store, mc:load1st, mc:>2, op:div (divsi, divui, remsi, remui), mem>1024.
"""
import os
import sys
import types

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))
BDC = os.path.join(ROOT, "bdc")
sys.path.insert(0, BDC)

PATCHES = {
    "mc:store": [("        if has_store:\n", "        if False and has_store:\n")],
    "mc:load1st": [('            if arb and nodes[ordered[0]].op != "store":\n',
                    '            if False and arb and nodes[ordered[0]].op != "store":\n')],
    "mc:>2": [("            if n > 2:\n", "            if False and n > 2:\n"),
              ("            arb = n == 2\n", "            arb = False\n")],
    "op:div": [('    if op in ("addi", "subi", "muli", "andi", "ori", "xori",\n',
                '    if op in ("addi", "subi", "muli", "andi", "ori", "xori", "divsi", "divui", "remsi", "remui",\n'),
               ("            self.table.lookup(node)\n",
                '            node.op in ("divsi", "divui", "remsi", "remui") or self.table.lookup(node)\n'),
               ('for _op in ("addi", "subi", "muli", "cmpi", "andi", "ori", "xori",\n',
                'for _op in ("addi", "subi", "muli", "cmpi", "andi", "ori", "xori", "divsi", "divui", "remsi", "remui",\n')],
    "mem>1024": [],   # mem.RAM_WORDS, below
}


def patched_emitter(blockers):
    src = open(os.path.join(BDC, "emit.py")).read()
    for b in blockers:
        for old, new in PATCHES[b]:
            n = src.count(old)
            if n != 1:
                sys.exit(f"dyn_whatif: patch for {b} matches {n} times in bdc/emit.py (needs exactly 1): {old.strip()!r}")
            src = src.replace(old, new)
    import compute
    import mem
    if "op:div" in blockers:
        compute.BINARY.update({"divsi": "$signed({a}) / $signed({b})", "divui": "{a} / {b}",
                               "remsi": "$signed({a}) % $signed({b})", "remui": "{a} % {b}"})
    if "mem>1024" in blockers:
        mem.RAM_WORDS = 1 << 24
    mod = types.ModuleType("emit_whatif")
    mod.__file__ = os.path.join(BDC, "emit.py")
    exec(compile(src, mod.__file__, "exec"), mod.__dict__)
    return mod


def main():
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    blockers = [b for b in sys.argv[1].split(",") if b]
    for b in blockers:
        if b not in PATCHES:
            sys.exit(f"unknown blocker {b!r}; known: {sorted(PATCHES)}")
    emit = patched_emitter(blockers)
    for path in sys.argv[2:]:
        try:
            emit.generate(path, top=False)
            res = "OK"
        except Exception as e:  # the point is to see the next refusal, whatever raises it
            res = f"{type(e).__name__}: {str(e).splitlines()[0]}"
        print(f"{path}\t{res}", flush=True)


if __name__ == "__main__":
    main()
