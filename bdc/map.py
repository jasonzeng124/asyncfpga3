#!/usr/bin/env python3
"""op -> cell mapping for the bundled-data backend.

Reads bd-config.json and decides, for each op in a parsed handshake module,
what it lowers to.  Nothing here emits Verilog; that is bdc/emit.py.  The
split exists so that "can we build this kernel at all" is answerable before
any emitter exists -- which is what --report does.

An op with no entry in bd-config.json fails loudly and by name.  It is never
skipped, never guessed at, and never quietly mapped to something adjacent:
a wrong cell here is a silent miscompile, and the whole reason bdc/AUDIT.md
exists is that Dynamatic's op semantics and this library's cell semantics
agree less often than the names suggest.

Usage:
    python3 bdc/map.py --report build/frontend/*/comp/handshake_transformed.mlir
"""

import argparse
import json
import os
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hs import parse  # noqa: E402

CONFIG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bd-config.json")

# Kinds that are ready to emit today.  'compute' waits on the Stage 3 wrapper
# and 'todo' on Stage 6 memory; both are known-missing rather than unknown,
# which is a distinction --report has to make or it cannot say what blocks.
READY = ("cells", "wire", "tree")


class Unmapped(Exception):
    """An op with no entry at all.  Distinct from a mapped-but-unbuilt op:
    this one means the table is incomplete and someone has to audit it."""


class Mapping:
    def __init__(self, op, entry):
        self.op = op
        self.kind = entry["kind"]
        self.cells = entry.get("cells", [])
        self.entry = entry

    @property
    def ready(self):
        return self.kind in READY

    def __repr__(self):
        cells = "+".join(self.cells) if self.cells else "-"
        return f"<{self.op} -> {self.kind}:{cells}>"


class Table:
    def __init__(self, path=CONFIG):
        with open(path) as f:
            cfg = json.load(f)
        self.convention = cfg["control_channel_convention"]
        # Several ops appear more than once under different guards (merge with
        # one operand is a wire, merge with two needs an arbiter), so entries
        # are kept in file order per op and the first matching guard wins.
        self.by_op = defaultdict(list)
        for entry in cfg["ops"]:
            self.by_op[entry["op"]].append(entry)

    def lookup(self, node):
        entries = self.by_op.get(node.op)
        if not entries:
            raise Unmapped(
                f"no entry for handshake op {node.op!r} in bd-config.json. "
                f"Add one -- do not assume a cell."
            )
        for entry in entries:
            guard = entry.get("guard")
            if guard is None:
                return Mapping(node.op, entry)
            if _eval_guard(guard, node):
                return Mapping(node.op, entry)
        raise Unmapped(
            f"handshake op {node.op!r} has {len(node.operands)} operand(s), "
            f"which no guard in bd-config.json covers"
        )


def _eval_guard(guard, node):
    """Guards are deliberately a tiny fixed language, not eval(). The table is
    data that decides what hardware gets built; it must not be able to run
    code, and a typo in it must fail rather than do something."""
    env = {"len(operands)": len(node.operands), "len(results)": len(node.results)}
    for key, value in env.items():
        if guard.startswith(key):
            rest = guard[len(key):].strip()
            for opname, fn in (
                (">=", lambda a, b: a >= b),
                ("<=", lambda a, b: a <= b),
                ("==", lambda a, b: a == b),
                (">", lambda a, b: a > b),
                ("<", lambda a, b: a < b),
            ):
                if rest.startswith(opname):
                    return fn(value, int(rest[len(opname):].strip()))
    raise ValueError(f"unparseable guard {guard!r} in bd-config.json")


def report(paths):
    table = Table()
    overall_blockers = Counter()
    worst = 0

    for path in paths:
        try:
            funcs = parse.parse_module(open(path).read(), filename=path)
        except Exception as e:  # noqa: BLE001 -- a parse failure is a result
            print(f"\n{path}\n  PARSE FAILED: {e}")
            worst = max(worst, 2)
            continue

        kinds = Counter()
        blockers = Counter()
        unmapped = Counter()
        for func in funcs:
            for node in func.nodes:
                try:
                    m = table.lookup(node)
                except Unmapped as e:
                    unmapped[node.op] += 1
                    kinds["UNMAPPED"] += 1
                    del e
                    continue
                kinds[m.kind] += 1
                if not m.ready:
                    blockers[node.op] += 1
                    overall_blockers[node.op] += 1

        name = os.path.basename(os.path.dirname(os.path.dirname(path)))
        total = sum(kinds.values())
        ready = sum(v for k, v in kinds.items() if k in READY)
        print(f"\n{name}  ({total} ops)")
        for kind, n in sorted(kinds.items()):
            print(f"    {n:5d}  {kind}")
        print(f"    {ready}/{total} ops lower with what exists today")
        if unmapped:
            print("    UNMAPPED (table is incomplete):")
            for op, n in unmapped.most_common():
                print(f"        {n:5d}  {op}")
            worst = max(worst, 2)
        if blockers:
            print("    blocked on unbuilt stages:")
            for op, n in blockers.most_common():
                print(f"        {n:5d}  {op}")
            worst = max(worst, 1)
        elif not unmapped:
            print("    ** buildable today **")

    if overall_blockers:
        print("\nWhat to build next, by how many ops it unblocks:")
        for op, n in overall_blockers.most_common():
            print(f"    {n:5d}  {op}")
    return worst


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--report", action="store_true",
                    help="print per-kernel coverage against the table")
    ap.add_argument("files", nargs="+")
    args = ap.parse_args()
    if not args.report:
        ap.error("nothing to do but --report yet; the emitter is bdc/emit.py")
    # Exit 2 means the table is incomplete, 1 means every op is mapped but
    # some need a stage that is not built.  Only 0 means ready to emit.
    sys.exit(report(args.files))


if __name__ == "__main__":
    main()
