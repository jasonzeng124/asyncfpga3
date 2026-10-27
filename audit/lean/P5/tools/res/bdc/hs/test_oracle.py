#!/usr/bin/env python3
"""Oracle gate for bdc/hs/parse.py: let dynamatic-opt judge the reprint.

The sibling test, test_roundtrip.py, checks that the reprint re-parses to the
same graph.  That is worth having but it is a mirror: it only proves the
printer agrees with the parser.  Both could be wrong about the same thing --
dropping an attribute on read and never printing it -- and the round-trip
would still be green.

This one asks something the parser cannot fake:

    dynamatic-opt <orig>   > norm1     # the oracle's own normal form
    parse norm1, reprint   > rp
    dynamatic-opt rp       > norm2
    require norm1 == norm2 byte for byte

Normalising both sides means we are not fighting Dynamatic's formatting
choices, only real content differences.  If the reader drops an operand, an
attribute or a type, norm2 differs from norm1 and the diff says exactly where.
If the printer emits something that is not valid handshake MLIR, dynamatic-opt
refuses it outright and there is no diff to interpret.

Run:  python3 bdc/hs/test_oracle.py
"""

import glob
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.dirname(HERE))
from hs import parse  # noqa: E402

DYNAMATIC_OPT = os.path.join(ROOT, "dynamatic", "build", "bin", "dynamatic-opt")


def normalise(path_or_text, is_text=False):
    """Run dynamatic-opt and return (ok, stdout, stderr). No shell pipeline:
    a pipe would hand back the wrong process's exit status."""
    if is_text:
        proc = subprocess.run(
            [DYNAMATIC_OPT], input=path_or_text, capture_output=True, text=True
        )
    else:
        proc = subprocess.run(
            [DYNAMATIC_OPT, path_or_text], capture_output=True, text=True
        )
    return proc.returncode == 0, proc.stdout, proc.stderr


def _strip_empty_modules(text):
    """Remove `module {` / `}` pairs with nothing between them. Deliberately
    narrow: it only ever deletes a module that provably contains no text, so
    it cannot hide a dropped function, op or attribute -- those still show up
    as a content difference."""
    lines = text.split("\n")
    out, i = [], 0
    while i < len(lines):
        if (lines[i].strip() == "module {"
                and i + 1 < len(lines) and lines[i + 1].strip() == "}"):
            i += 2
            continue
        out.append(lines[i])
        i += 1
    return "\n".join(out)


def corpus():
    files = sorted(glob.glob(os.path.join(HERE, "corpus", "*.out.mlir")))
    files += sorted(glob.glob(
        os.path.join(ROOT, "build", "frontend", "*", "comp",
                     "handshake_transformed.mlir")))
    return files


def main():
    if not os.path.exists(DYNAMATIC_OPT):
        print(f"dynamatic-opt not built at {DYNAMATIC_OPT}")
        return 2

    files = corpus()
    if not files:
        print("no corpus files found")
        return 2

    passed, failed = 0, []
    for path in files:
        rel = os.path.relpath(path, ROOT)

        ok, norm1, err = normalise(path)
        if not ok:
            # The oracle cannot judge what it will not accept itself. A
            # fixture dynamatic-opt rejects is a broken fixture, not a
            # parser bug -- but it is still reported, never skipped silently.
            failed.append((rel, "oracle rejects the ORIGINAL", err.strip()[:400]))
            continue

        try:
            funcs = parse.parse_module(norm1, filename=rel)
            reprint = parse.module_to_text(funcs)
        except Exception as e:  # noqa: BLE001 -- a parse failure is the result
            failed.append((rel, "parse/reprint raised", str(e)[:400]))
            continue

        ok2, norm2, err2 = normalise(reprint, is_text=True)
        if not ok2:
            failed.append((rel, "oracle rejects the REPRINT", err2.strip()[:400]))
            continue

        if norm1 != norm2 and _strip_empty_modules(norm1) == norm2:
            # ONE named allowance, applied loudly rather than silently: an
            # empty `module { }` block is dropped. parse_module returns a
            # list of Func, so a module containing no function has nothing
            # to hang itself on. It also carries nothing a backend could
            # use -- zero ops, zero channels. Only handshake-hw-inst.out.mlir
            # has one, and it is a hand-written lit test for the `instance`
            # op, which bd-config.json rejects by name anyway.
            passed += 1
            print(f"  ok*   {rel}   (empty `module {{ }}` dropped -- see note in source)")
            continue

        if norm1 != norm2:
            a, b = norm1.splitlines(), norm2.splitlines()
            detail = []
            for i, (x, y) in enumerate(zip(a, b)):
                if x != y:
                    detail.append(f"line {i + 1}:\n  orig: {x.strip()}\n  ours: {y.strip()}")
                    if len(detail) >= 3:
                        break
            if len(a) != len(b):
                detail.append(f"line count {len(a)} vs {len(b)}")
            failed.append((rel, "normalised forms differ", "\n".join(detail)))
            continue

        passed += 1
        print(f"  ok    {rel}")

    print(f"\n{passed}/{len(files)} files survive the oracle round trip")
    if failed:
        print(f"\n{len(failed)} FAILED:")
        for rel, why, detail in failed:
            print(f"\n  {rel}\n    {why}\n{detail}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
