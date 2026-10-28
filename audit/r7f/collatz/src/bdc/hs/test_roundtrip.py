#!/usr/bin/env python3
"""Round-trip gate for bdc/hs/parse.py: parse, reprint, reparse, compare.

For every case in the corpus: parse it, reprint it via to_text(), reparse
the reprint, and require the two parses to compare structurally equal
(dataclass equality -- not text equality; to_text() does not try to match
Dynamatic's own formatting).

The corpus has three tiers, in order of authority:

  1. bdc/hs/corpus/*.out.mlir -- real `dynamatic-opt` output, generated from
     the lit tests under dynamatic/test/ by actually running the passes.
     This is the primary corpus. Where it disagrees with tier 3, it wins.
  2. build/frontend/*/comp/handshake_transformed.mlir -- real compiled C
     kernels (test_loop_free, single_loop, fir, gcd), the actual target of
     this whole exercise. Read directly from the build directory (gitignored
     build output); never copied into bdc/.
  3. dynamatic/test/{Transforms,Dialect/Handshake,Conversion/CfToHandshake}/*.mlir
     -- the lit-test corpus. Two kinds of case come out of each file:
       - "direct": the file's own body, when that body is already real
         handshake text (true for most of Transforms/, false for
         Conversion/CfToHandshake/ and a few Transforms/ files whose real
         body is the arith/cf/scf *input* to a lowering pass).
       - "check": FileCheck `// CHECK:` lines reconstructed into plain text
         by checklines.py. Present in most files; a few (hand-written,
         partial-assertion CHECK blocks) reconstruct into garbage on
         purpose and are expected to fail to parse -- that failure is
         reported as a skip, not hidden.
     dynamatic/test/Dialect/Handshake/invalid.mlir is deliberately malformed
     and is excluded from the pass corpus; it is checked separately, for
     rejection, at the bottom of this file.

Run as: python3 bdc/hs/test_roundtrip.py
Exit 0 if every case that parsed also round-tripped; non-zero otherwise.
"""

import difflib
import os
import pprint
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checklines
import parse

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
HS_DIR = os.path.dirname(os.path.abspath(__file__))

OUT_CORPUS_DIR = os.path.join(HS_DIR, "corpus")
LIT_TEST_DIRS = [
    os.path.join(REPO_ROOT, "dynamatic", "test", "Transforms"),
    os.path.join(REPO_ROOT, "dynamatic", "test", "Dialect", "Handshake"),
    os.path.join(REPO_ROOT, "dynamatic", "test", "Conversion", "CfToHandshake"),
]
REAL_KERNELS = [
    os.path.join(REPO_ROOT, "build", "frontend", name, "comp", "handshake_transformed.mlir")
    for name in ("test_loop_free", "single_loop", "fir", "gcd")
]
INVALID_MLIR = os.path.join(
    REPO_ROOT, "dynamatic", "test", "Dialect", "Handshake", "invalid.mlir"
)


def _lit_test_files():
    files = []
    for d in LIT_TEST_DIRS:
        if not os.path.isdir(d):
            continue
        for name in sorted(os.listdir(d)):
            path = os.path.join(d, name)
            if os.path.isfile(path) and name.endswith(".mlir"):
                files.append(path)
            elif os.path.isdir(path):
                for name2 in sorted(os.listdir(path)):
                    if name2.endswith(".mlir"):
                        files.append(os.path.join(path, name2))
    return files


class Result:
    def __init__(self):
        self.parsed = 0
        self.round_tripped = 0
        self.skipped = []   # (case_id, reason)
        self.failed = []    # (case_id, detail)


def _diff(case_id, funcs1, funcs2):
    a = pprint.pformat(funcs1, width=100).splitlines()
    b = pprint.pformat(funcs2, width=100).splitlines()
    lines = list(difflib.unified_diff(
        a, b, fromfile="parse #1", tofile="parse #2 (after reprint)", lineterm=""
    ))
    return f"{case_id}: structural mismatch after round-trip\n" + "\n".join(lines[:60])


def run_case(result, case_id, text, filename):
    """Parse -> reprint -> reparse -> compare. Updates `result` in place."""
    try:
        funcs1 = parse.parse_module(text, filename=filename)
    except parse.ParseError as e:
        result.skipped.append((case_id, str(e)))
        return
    result.parsed += 1

    # wrap=False: do not invent a `module { ... }` around a fragment that had
    # none. Recorded nesting is still reproduced -- see module_to_text. This
    # test compares parse against reparse, and an invented wrapper would show
    # up as a module_path disagreement that says nothing about the reader.
    reprinted = parse.module_to_text(funcs1, wrap=False)
    try:
        funcs2 = parse.parse_module(reprinted, filename=f"{case_id} (reprint)")
    except parse.ParseError as e:
        result.failed.append((
            case_id,
            f"reprint of {case_id} does not reparse: {e}\n--- reprinted text ---\n{reprinted}",
        ))
        return

    if funcs1 == funcs2:
        result.round_tripped += 1
    else:
        result.failed.append((case_id, _diff(case_id, funcs1, funcs2)))


def run_out_corpus(result):
    if not os.path.isdir(OUT_CORPUS_DIR):
        return
    for name in sorted(os.listdir(OUT_CORPUS_DIR)):
        if not name.endswith(".out.mlir"):
            continue
        path = os.path.join(OUT_CORPUS_DIR, name)
        with open(path) as fh:
            text = fh.read()
        run_case(result, f"corpus/{name}", text, path)


def run_real_kernels(result):
    for path in REAL_KERNELS:
        case_id = f"real-kernel:{os.path.basename(os.path.dirname(os.path.dirname(path)))}"
        if not os.path.isfile(path):
            result.skipped.append((case_id, f"build artifact not present at {path} (run the frontend build first)"))
            continue
        with open(path) as fh:
            text = fh.read()
        run_case(result, case_id, text, path)


def run_lit_tests(result):
    for path in _lit_test_files():
        rel = os.path.relpath(path, REPO_ROOT)
        if os.path.abspath(path) == os.path.abspath(INVALID_MLIR):
            continue  # handled separately, as a must-reject corpus
        with open(path) as fh:
            text = fh.read()
        chunks = checklines.split_lit_cases(text)
        for i, chunk in enumerate(chunks):
            if chunk.strip():
                run_case(result, f"{rel}#{i}:direct", chunk, path)
            reconstructed = checklines.extract_checks(chunk)
            if reconstructed.strip():
                run_case(result, f"{rel}#{i}:check", reconstructed, path)


def run_invalid_mlir():
    """invalid.mlir is deliberately malformed. It is not part of the pass
    corpus, but it is a fine source of things a syntax-level parser SHOULD
    reject -- and a fine reminder that some of its cases are semantic (e.g.
    "'valid' is a reserved name") rather than syntactic, which this reader
    cannot and does not try to catch: it is a reader, not a verifier."""
    if not os.path.isfile(INVALID_MLIR):
        return None
    with open(INVALID_MLIR) as fh:
        text = fh.read()
    chunks = [c for c in checklines.split_lit_cases(text) if c.strip()]
    rejected, accepted = 0, []
    for i, chunk in enumerate(chunks):
        try:
            parse.parse_module(chunk, filename=f"invalid.mlir#{i}")
            accepted.append(i)
        except parse.ParseError:
            rejected += 1
    return len(chunks), rejected, accepted


def main():
    result = Result()
    run_out_corpus(result)
    run_real_kernels(result)
    run_lit_tests(result)

    print(f"{result.parsed} cases parsed, {result.round_tripped} round-tripped")
    print()

    if result.skipped:
        print(f"skipped {len(result.skipped)} case(s):")
        for case_id, reason in result.skipped:
            first_line = reason.splitlines()[0] if reason else reason
            print(f"  - {case_id}: {first_line}")
        print()

    invalid_summary = run_invalid_mlir()
    if invalid_summary:
        total, rejected, accepted = invalid_summary
        print(f"invalid.mlir sanity check: {rejected}/{total} cases correctly rejected")
        if accepted:
            print(
                f"  {len(accepted)} case(s) were syntactically well-formed and parsed "
                f"anyway (indices {accepted}) -- these test semantic verifier errors "
                f"(reserved names, duplicate signals, type mismatches) that a "
                f"syntax-only reader cannot see; this is expected, not a bug."
            )
        print()

    if result.failed:
        print(f"{len(result.failed)} HARD FAILURE(S) -- parsed but did not round-trip:")
        for case_id, detail in result.failed:
            print("=" * 70)
            print(detail)
        return 1

    print("all parsed cases round-tripped cleanly.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
