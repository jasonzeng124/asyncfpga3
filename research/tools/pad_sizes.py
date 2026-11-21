#!/usr/bin/env python3
"""pad_sizes.py -- a PAD-ONLY sizes file from tighten.py logs of several routes.

    pad_sizes.py OUT.vh tighten_log [tighten_log ...] [--base OLD.vh]

For every cell that rule A flags "PAD to N -- VIOLATION" on any route, the
largest N over the routes (and over --base, if it already names the cell)
becomes `define BD_SZ_<path> N.  Nothing else is written, so every cell rule A
did not flag keeps bdc/emit.py's estimate: a delay is only ever lengthened,
never shortened (CLAUDE.md, Delays).  The macro names are tighten.py's
(re.sub(non-alnum, "_", path).upper()).
"""
import re, sys

RE = re.compile(r"^\s+(\S+)\s+(\d+) links\s+\d+ ps\s+req.*PAD to (\d+) -- VIOLATION")
RE_DEF = re.compile(r"`define\s+(BD_SZ_\w+)\s+(\d+)")


def macro(path):
    return "BD_SZ_" + re.sub(r"[^A-Za-z0-9]", "_", path).upper()


def main():
    args = sys.argv[1:]
    base = None
    if "--base" in args:
        i = args.index("--base"); base = args[i + 1]; del args[i:i + 2]
    out, logs = args[0], args[1:]
    want = {}
    if base:
        for m, n in RE_DEF.findall(open(base).read()):
            want[m] = int(n)
    for f in logs:
        for line in open(f):
            m = RE.match(line)
            if m:
                k = macro(m.group(1))
                want[k] = max(want.get(k, 0), int(m.group(3)))
    with open(out, "w") as f:
        f.write("// pad-only sizes (research/tools/pad_sizes.py) from: %s\n" % " ".join(logs))
        for k in sorted(want):
            f.write("`define %s %d\n" % (k, want[k]))
    print("%d padded cell(s) -> %s" % (len(want), out))
    for k in sorted(want):
        print("  %s %d" % (k, want[k]))


if __name__ == "__main__":
    main()
