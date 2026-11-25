#!/usr/bin/env python3
"""Stage 2d of verify.sh: generated per-vector Lean theorems, for ANY kernel (probe C-vk).

    python3 vecgen.py KERNEL MLIR OUTDIR --c C_FILE --vecs "a,b a,b ..."

For each vector v with compiled-C result r (cref.py), writes into OUTDIR/<K>Vec<i>.lean
(the freshly imported graph + one theorem per vector; one file and one sequential Lean
process per vector) and checks:

  theorem vec<i> :
      (∃ n, Run (step (graph rules)) (ofL I) n (ofL F)) ∧
      (∀ m t, Run (step (graph rules)) (ofL I) m t → Terminal (step (graph rules)) t → t = ofL F)

  I = one token per function argument (v, and the start token),
  F = `[r]` on the data output, `[0]` on the end token, nothing else  -- r from the C, typed
      into the theorem statement before any run.

Proof, generated and identical for every kernel: a witness schedule (found by
tokensearch's search; the Lean kernel re-executes it with GcdHwLib's own semantics, so
the Python semantics is NOT trusted) gives the first conjunct via `execL_run`; `F` is
terminal by `terminal_of_dead`; the initial store has one control-spine token; C-8i's
`determinate` then gives the second conjunct (every complete run, any schedule, any
arbitration, ends in F). No hand-written proof is needed, so this works for a kernel like
xorshift that has none. It says nothing about inputs not listed.

A vector whose witness search finds no correct terminal store gets no theorem (stage 2b
prints its counterexample). Prints `VEC PASS k/n` or `VEC FAIL ...`.
"""
import argparse
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, HERE)
from kernels import KERNELS  # noqa: E402
from cref import c_reference  # noqa: E402
import tokensearch as TS  # noqa: E402

AXIOMS_OK = {"propext", "Classical.choice", "Quot.sound"}


def sp(N, st):
    ent = [f"({c}, [{', '.join(map(str, row))}])" for c, row in enumerate(st) if row]
    return f"sp {N} [{', '.join(ent)}]"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("kernel")
    ap.add_argument("mlir")
    ap.add_argument("outdir")
    ap.add_argument("--c", required=True)
    ap.add_argument("--vecs", required=True)
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--chain", action="store_true",
                    help="certify the witness with C-8i's chainOK (every intermediate store listed); "
                         "default: the kernel evaluates execL directly (smaller file)")
    ap.add_argument("--max-steps", type=int, default=600,
                    help="no theorem for a vector whose witness schedule is longer (Lean cost); not a failure")
    a = ap.parse_args()
    k = KERNELS[a.kernel]
    os.makedirs(a.outdir, exist_ok=True)
    K, ns = k["K"], k["ns"]
    vecs = [tuple(int(x) for x in v.split(",")) for v in a.vecs.split()]
    crefs = c_reference(a.c, k["func"], vecs)
    g = TS.mlir2lean.Graph(a.mlir)
    S = TS.Search(g, max_states=50000)
    graph = TS.mlir2lean.lean_graph(g, argparse.Namespace(ns=ns, label=a.kernel, short=a.kernel))
    graph = re.sub(r"^theorem (ins_ok|outs_ok|spine_ok|bounded_ok|spine_nodup) .*$", "", graph, flags=re.M)
    # (the five well-formedness theorems are re-stated below so that each is checked once)
    head = [graph.replace(f"end {ns}\n", ""),
            "theorem spine_nodup : spine.Nodup := by decide +kernel",
            "theorem ins_ok : checkIns rules = true := by decide +kernel",
            "theorem outs_ok : checkOuts spine rules = true := by decide +kernel",
            "theorem spine_ok : rules.all (Rule.okP spine) = true := by decide +kernel",
            "theorem bounded_ok : bounded N rules = true := by decide +kernel", "",
            "open Formal.Net.Kahn", ""]
    # one file and one (sequential, slot.sh) Lean process per vector: a gcd witness of a few
    # hundred firings takes ~3 GB in the kernel, and several in one file were OOM-killed
    files, skipped, long_ = [], [], []
    for i, (v, r) in enumerate(zip(vecs, crefs)):
        R = S.run(v, r)
        tag = ",".join(map(str, v))
        if R["status"] != "ok":
            skipped.append(f"({tag}): {R['status']}")
            continue
        want = R["want"]
        path = S.path(R["parent"], want)
        if len(path) > a.max_steps:
            long_.append(f"({tag}): witness {len(path)} firings > --max-steps {a.max_steps}")
            continue
        sched = [i_ for (_, i_, _, _) in path]
        trace = [t for (_, _, _, t) in path]
        s0 = S.initial(v)
        out = head + [
                f"/-- vector ({tag}): the compiled C returns {r}. -/",
                f"def I{i} : List (List Nat) := {sp(g.N, s0)}",
                f"def F{i} : List (List Nat) := {sp(g.N, want)}",
                f"def sched{i} : List Nat := {sched}",
                *([f"def trace{i} : List (List (List Nat)) := [" +
                   ",\n  ".join(sp(g.N, t) for t in trace) + "]"] if a.chain else []),
                "-- long witnesses exceed the default 200000 heartbeats in elaboration (gcd, 392 firings)",
                "set_option maxHeartbeats 0 in",
                f"theorem vec{i} :",
                f"    (∃ n, Run (step (graph rules)) (ofL I{i}) n (ofL F{i})) ∧",
                f"    (∀ m t, Run (step (graph rules)) (ofL I{i}) m t → Terminal (step (graph rules)) t →",
                f"      t = ofL F{i}) := by",
                f"  have hrun := execL_run bounded_ok sched{i} (by decide +kernel : I{i}.length = N)",
                (f"    (execL_of_chainOK (ms := trace{i}) (l' := F{i}) (by decide +kernel))" if a.chain else
                 f"    (by decide +kernel : execL natVI rules I{i} sched{i} = some F{i})"),
                f"  have hT := terminal_of_dead rules (ofL F{i})",
                f"    (by decide +kernel : rules.all (Rule.dead (ofL F{i})) = true)",
                f"  have hinv : Inv spine (ofL I{i}) := by",
                f"    show cnt spine (ofL I{i}) ≤ 1; decide +kernel",
                f"  exact ⟨⟨_, hrun⟩, fun m t ht hTt =>",
                f"    (determinate spine rules spine_nodup ins_ok outs_ok spine_ok hinv hrun hT ht hTt).1⟩", "",
                f"end {ns}", f"#print axioms {ns}.vec{i}"]
        f = os.path.join(a.outdir, f"{K}Vec{i}.lean")
        open(f, "w").write("\n".join(out) + "\n")
        files.append((i, tag, r, f, len(path)))
    print(f"vec: wrote {len(files)} file(s) {os.path.join(a.outdir, K + 'Vec<i>.lean')}; no theorem (search did not "
          f"end correctly) for {len(skipped)}: {'; '.join(skipped) or '-'}; not attempted (too long) for "
          f"{len(long_)}: {'; '.join(long_) or '-'}")
    if not files:
        print("VEC FAIL: no vector has a correct terminal store")
        return 1
    failed, axs = [], set()
    for i, tag, cr, f, n in files:
        try:
            r = subprocess.run([os.path.join(ROOT, "formal", "slot.sh"), "lake", "env", "lean", os.path.abspath(f)],
                               capture_output=True, text=True, timeout=a.timeout)
            log, rc = r.stdout + r.stderr, r.returncode
        except subprocess.TimeoutExpired:
            log, rc = "timeout", -1
        open(f + ".log", "w").write(log)
        errs = [l for l in log.split("\n") if ": error" in l]
        m = re.search(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
        ax = {y.strip() for y in m.group(2).split(",")} if m else None
        if rc != 0 or errs or "sorry" in log or ax is None or not ax <= AXIOMS_OK:
            failed.append(tag)
            print(f"  {ns}.vec{i}: input ({tag}) FAILED to check: exit {rc}, {len(errs)} error(s), axioms {ax}")
            for l in (errs or log.strip().split("\n"))[:3]:
                print("     ", l[:300])
            continue
        axs |= ax
        print(f"  {ns}.vec{i}: input ({tag}) -> every complete run ends with out = [{cr % (1 << 32)}] "
              f"(C: {cr}); witness {n} firings")
    if failed:
        print(f"VEC FAIL: {len(failed)} vector theorem(s) did not check")
        return 1
    print(f"VEC PASS {len(files)}/{len(vecs) - len(long_)} (axioms {sorted(axs)})"
          + (" -- some vectors have no theorem (counterexample in stage 2b)" if skipped else ""))
    return 0 if not skipped else 1


if __name__ == "__main__":
    sys.exit(main())
