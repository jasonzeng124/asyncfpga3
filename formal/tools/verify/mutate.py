#!/usr/bin/env python3
"""Negative-control mutants of a handshake MLIR (probe C-vk).

    python3 mutate.py IN.mlir OUT.mlir --swap NAME      # swap the first two operands of the
                                                        # op whose handshake.name is NAME
    python3 mutate.py IN.mlir OUT.mlir --const NAME=V   # change a constant's value attribute

Text-level edit of one line; fails loudly if NAME does not match exactly one op.
"""
import argparse
import re
import sys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("inp")
    ap.add_argument("out")
    ap.add_argument("--swap")
    ap.add_argument("--const")
    a = ap.parse_args()
    lines = open(a.inp).read().split("\n")
    name = a.swap or a.const.split("=")[0]
    hits = [i for i, l in enumerate(lines) if f'handshake.name = "{name}"' in l]
    if len(hits) != 1:
        raise SystemExit(f"mutate: {name!r} matches {len(hits)} ops")
    i = hits[0]
    old = lines[i]
    if a.swap:
        m = re.match(r"^(\s*%\S+\s*=\s*\w+\s+)(%[\w#]+),\s*(%[\w#]+)(.*)$", old)
        if not m:
            raise SystemExit(f"mutate: cannot parse two operands in: {old.strip()}")
        new = f"{m.group(1)}{m.group(3)}, {m.group(2)}{m.group(4)}"
    else:
        v = a.const.split("=", 1)[1]
        new, n = re.subn(r"value = -?\d+ :", f"value = {v} :", old)
        if n != 1:
            raise SystemExit(f"mutate: no value attribute in: {old.strip()}")
    lines[i] = new
    open(a.out, "w").write("\n".join(lines))
    print(f"mutate: line {i + 1}\n  - {old.strip()}\n  + {new.strip()}", file=sys.stderr)


if __name__ == "__main__":
    main()
