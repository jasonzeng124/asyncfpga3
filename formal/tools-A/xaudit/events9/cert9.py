"""cert9.py -- emit the CERTIFICATE that xevents9 (Events9Main.lean) checks (UNTRUSTED).

    python3 cert9.py SKEL.json BANDS.json OUT.json [--no-u3] [--no-nary] [--no-gline] [--no-guard] [--no-ws]

Probe HDsub: events8/cert8.py (WE4g) unchanged, plus ONE field per `dsub` hypothesis line:
`wS`, the log line of an unlabelled walk from the label source S to the walk's start D with at
most one token (Events9Cert.WSOK; the premise of the first-reach rule `dsub9`, whose soundness
replaces the hypothesis HDsub).  For a guard certificate this is the guard's own ENTRY walk
`iW` (S -> D, <= 1 token), whose endpoints are checked here and again by the Lean checker.
--no-ws omits wS (control: every dsub line is then rejected, every guarded pin residual).
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "events8"))
from cert8 import Cert7  # noqa: E402


def add_ws(out):
    """Set wS on every dsub hypothesis line from its guard's iW (S -> D walk). Returns the
    number of dsub lines given a wS and a list of problems."""
    log, hyp, n, bad = out["log"], out["hyp"], 0, []
    walk_ends = {}

    def ends(i):
        # (start, end, tokens) of an unlabelled walk line built by cert7's chain(): r1/r3/refl
        if i in walk_ends:
            return walk_ends[i]
        ln = log[i]
        k = ln["k"]
        if k == "refl":
            r = (ln["a"], ln["a"])
        elif k == "r1":
            r = (ln["n"], ends(ln["r"])[1])
        elif k == "r3":
            r = (ln["x"], ends(ln["r"])[1])
        else:
            r = (None, None)
        walk_ends[i] = r
        return r

    for key, g in out["guards"].items():
        for which in ("iB", "iG"):
            h = hyp[g[which]]
            if h["k"] != "dsub":
                continue
            st, en = ends(g["iW"])
            if h["S"] == g["S"] and st == g["S"] and en == h["a"]:
                h["wS"] = g["iW"]
                n += 1
            else:
                bad.append(f"guard {key} {which}: iW {g['iW']} is not a walk S {h['S']} -> D {h['a']}")
    return n, bad


def main():
    os.environ.setdefault("PYTHONHASHSEED", "0")
    a = [x for x in sys.argv[1:] if not x.startswith("--")]
    C = Cert7(a[0], a[1], u3="--no-u3" not in sys.argv, nary="--no-nary" not in sys.argv,
              gline="--no-gline" not in sys.argv, guard="--no-guard" not in sys.argv)
    out = C.run7()
    nws, bad = (0, []) if "--no-ws" in sys.argv else add_ws(out)
    out["errors"] += bad
    json.dump(out, open(a[2], "w"))
    nd = sum(1 for h in out["hyp"] if h["k"] == "dsub")
    print(f"cert9: {len(out['nodes'])} nodes, log {len(out['log'])} lines, back {len(out['back'])}, "
          f"lines {len(out['lines'])}, excl {len(out['excl'])}, guards {len(out['guards'])}, groups {out['groups']}, parts {out['parts']}, "
          f"dsub {nd} (wS given {nws}), errors {len(out['errors'])}")
    for e in out["errors"]:
        print("  UNCERTIFIED", e)


if __name__ == "__main__":
    main()
