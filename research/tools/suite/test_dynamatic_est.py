#!/usr/bin/env python3
"""test_dynamatic_est.py -- checks of research/tools/suite/dynamatic_est.py that can fail.  Run from anywhere:

    python3 research/tools/suite/test_dynamatic_est.py

1. Answers: the six original kernels on their gate vectors (suite_one.sh's) return the C's answers in the model.
2. Cycles, against a derivation that does not use this simulator (research/data/dynamatic_ref/README.md: hw.mlir's
   buffers in cells/hw/dyn_baseline.sh, and the hand count for ipow): exactly 1 cycle per iteration for xorshift,
   collatz, collatz64 and exactly 5 for ipow (muli latency 4 + the ring's one opaque slot).  The static lower bound
   for any buffer placement never exceeds the simulated figure, and is 4 for ipow (the multiplier's latency).
3. Negative controls.  Each injects a defect larger than anything the harness could hide and must be reported:
   a. xori computes OR (one unit's value) on xorshift                            -> WRONG ANSWER
   b. every TEHB forgets the token it holds (passes its input through when full) -> WRONG ANSWER on some kernel
   c. every eager fork forgets which outputs it already served (re-sends)        -> WRONG ANSWER on some kernel
      (2026-11-17: caught on ipow only -- among the six, only ipow's multiplier makes a fork's outputs take a
      token in different cycles; the answer check covers the paths the vectors exercise, no more)
   e. every 2-input mux takes the other input than its index says               -> caught on all six
   d. muli with latency 3 instead of 4 (a cycle-count defect, values unchanged)  -> answers stay RIGHT (the answer
      check cannot see it) and check 2 fails: ipow 4 cycles per iteration
"""
import os
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dynamatic_est as de  # noqa: E402

KS = ["xorshift", "collatz", "collatz64", "ipow", "isprime", "gcd"]
WORK = tempfile.mkdtemp(prefix="dynref_t_")
DIRS = de.fixture_dirs([])


def run(k):
    f = de.find_fixture(k, DIRS)
    return de.analyse(k, de.pick_vectors(k, f, DIRS), DIRS, WORK, max_cycles=20000)  # largest right call: 2139


def cycles_per_iter(r):
    return round(r["fit"]["per_loop"][r["iter_block"]], 6) if "fit" in r else None


fails = []


def check(cond, what):
    print(("ok    " if cond else "FAIL  ") + what, flush=True)
    if not cond:
        fails.append(what)


# 1 and 2
base = {}
for k in KS:
    r = base[k] = run(k)
    check(r["status"] == "ok" and r["n_ok"] == r["n"] > 0, "%s: %d of %d answers equal the C" % (k, r.get("n_ok", 0),
                                                                                                r.get("n", 0)))
for k, want in (("xorshift", 1), ("collatz", 1), ("collatz64", 1), ("ipow", 5)):
    got = cycles_per_iter(base[k])
    check(got == want, "%s: %s cycles per iteration (independent derivation: %d)" % (k, got, want))

# the static lower bound (any buffer placement) must not exceed what the simulation shows, and ipow's is the
# multiplier's latency (research/data/dynamatic_ref/README.md: "even an MILP placement cannot go below 4")
for k in KS:
    r = base[k]
    b = r["ii_bound"].get(r["iter_block"]) if r.get("ii_bound") else None
    check(b is not None and b <= r["cpi"] * 1.05, "%s: lower bound %s <= simulated %.2f cycles per iteration"
          % (k, b, r["cpi"]))
check(base["ipow"]["ii_bound"].get(base["ipow"]["iter_block"]) == 4, "ipow: lower bound 4 (the muli latency)")

# 3a: one unit's value
orig_binop = de.binop


def bad_binop(op, w, pred=None):
    if op == "xori":
        return lambda a, b: a | b
    return orig_binop(op, w, pred)


de.binop = bad_binop
r = run("xorshift")
check(r["status"].startswith("WRONG"), "control a (xori = OR): xorshift %s" % r["status"])
de.binop = orig_binop

# 3b: TEHB loses its stored data
orig_tehb = de.Tehb.comb


def bad_tehb(self):
    V, R, D = self.V, self.R, self.D
    i, o = self.ins[0], self.outs[0]
    ch = de._set(V, o, V[i] or self.full)
    ch |= de._set(D, o, D[i])
    ch |= de._set(R, i, not self.full)
    return ch


de.Tehb.comb = bad_tehb
caught = [k for k in KS if run(k)["status"] != "ok"]
check(bool(caught), "control b (TEHB forgets its token): caught on %s" % (caught or "no kernel"))
de.Tehb.comb = orig_tehb

# 3c: eager fork re-sends
orig_tick = de.Fork.tick
de.Fork.tick = lambda self: None
caught = [k for k in KS if run(k)["status"] != "ok"]
check(bool(caught), "control c (fork re-sends): caught on %s" % (caught or "no kernel"))
de.Fork.tick = orig_tick

# 3e: mux index inverted
orig_mux = de.Mux.comb


def bad_mux(self):
    sel = self.ins[0]
    if len(self.ins) == 3:
        self.D[sel] ^= 1
        try:
            return orig_mux(self)
        finally:
            self.D[sel] ^= 1
    return orig_mux(self)


de.Mux.comb = bad_mux
caught = [k for k in KS if run(k)["status"] != "ok"]
check(len(caught) == len(KS), "control e (mux index inverted): caught on %d of %d kernels" % (len(caught), len(KS)))
de.Mux.comb = orig_mux

# 3d: a cycle defect the answers cannot see
de.PIPE_LAT["muli"] = 3
r = run("ipow")
check(r["status"] == "ok", "control d (muli latency 3): answers still right (%s), as expected" % r["status"])
check(cycles_per_iter(r) == 4, "control d: ipow now %s cycles per iteration, so check 2 would fail"
      % cycles_per_iter(r))
de.PIPE_LAT["muli"] = 4

print("%d check(s) failed" % len(fails) if fails else "all checks passed")
sys.exit(1 if fails else 0)
