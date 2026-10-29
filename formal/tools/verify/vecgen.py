#!/usr/bin/env python3
"""Stage 2d of verify.sh: generated per-vector Lean theorems, for ANY kernel (probe C-vk).

    python3 vecgen.py KERNEL MLIR OUTDIR --c C_FILE --vecs "a,b a,b ..."

For each vector v with compiled-C result r (cref.py), writes into OUTDIR/<K>Vec.lean
(the freshly imported graph + one theorem per vector) and checks with one Lean process:

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
    a = ap.parse_args()
    k = KERNELS[a.kernel]
    os.makedirs(a.outdir, exist_ok=True)
    K, ns = k["K"], k["ns"]
    vecs = [tuple(int(x) for x in v.split(",")) for v in a.vecs.split()]
    crefs = c_reference(a.c, k["func"], vecs)
    g = TS.mlir2lean.Graph(a.mlir)
    S = TS.Search(g)
    graph = TS.mlir2lean.lean_graph(g, argparse.Namespace(ns=ns, label=a.kernel, short=a.kernel))
    graph = re.sub(r"^theorem (ins_ok|outs_ok|spine_ok|bounded_ok|spine_nodup) .*$", "", graph, flags=re.M)
    # (the five well-formedness theorems are re-stated below so that each is checked once)
    out = [graph.replace(f"end {ns}\n", ""),
           "theorem spine_nodup : spine.Nodup := by decide +kernel",
           "theorem ins_ok : checkIns rules = true := by decide +kernel",
           "theorem outs_ok : checkOuts spine rules = true := by decide +kernel",
           "theorem spine_ok : rules.all (Rule.okP spine) = true := by decide +kernel",
           "theorem bounded_ok : bounded N rules = true := by decide +kernel", "",
           "open Formal.Net.Kahn", ""]
    names, skipped = [], []
    for i, (v, r) in enumerate(zip(vecs, crefs)):
        R = S.run(v, r)
        tag = ",".join(map(str, v))
        if R["status"] != "ok":
            skipped.append(f"({tag}): {R['status']}")
            continue
        want = R["want"]
        path = S.path(R["parent"], want)
        sched = [i_ for (_, i_, _, _) in path]
        trace = [t for (_, _, _, t) in path]
        s0 = S.initial(v)
        out += [f"/-- vector ({tag}): the compiled C returns {r}. -/",
                f"def I{i} : List (List Nat) := {sp(g.N, s0)}",
                f"def F{i} : List (List Nat) := {sp(g.N, want)}",
                f"def sched{i} : List Nat := {sched}",
                f"def trace{i} : List (List (List Nat)) := [" +
                ",\n  ".join(sp(g.N, t) for t in trace) + "]",
                f"theorem vec{i} :",
                f"    (∃ n, Run (step (graph rules)) (ofL I{i}) n (ofL F{i})) ∧",
                f"    (∀ m t, Run (step (graph rules)) (ofL I{i}) m t → Terminal (step (graph rules)) t →",
                f"      t = ofL F{i}) := by",
                f"  have hrun := execL_run bounded_ok sched{i} (by decide +kernel : I{i}.length = N)",
                f"    (execL_of_chainOK (ms := trace{i}) (l' := F{i}) (by decide +kernel))",
                f"  have hT := terminal_of_dead rules (ofL F{i})",
                f"    (by decide +kernel : rules.all (Rule.dead (ofL F{i})) = true)",
                f"  have hinv : Inv spine (ofL I{i}) := by",
                f"    show cnt spine (ofL I{i}) ≤ 1; decide +kernel",
                f"  exact ⟨⟨_, hrun⟩, fun m t ht hTt =>",
                f"    (determinate spine rules spine_nodup ins_ok outs_ok spine_ok hinv hrun hT ht hTt).1⟩", ""]
        names.append((i, tag, r))
    out.append(f"end {ns}")
    out += [f"#print axioms {ns}.vec{i}" for i, _, _ in names]
    f = os.path.join(a.outdir, f"{K}Vec.lean")
    open(f, "w").write("\n".join(out) + "\n")
    print(f"vec: wrote {f} ({len(names)} vector theorems; skipped {len(skipped)}: {'; '.join(skipped) or '-'})")
    if not names:
        print("VEC FAIL: no vector has a correct terminal store")
        return 1
    try:
        r = subprocess.run([os.path.join(ROOT, "formal", "slot.sh"), "lake", "env", "lean", os.path.abspath(f)],
                           capture_output=True, text=True, timeout=a.timeout)
    except subprocess.TimeoutExpired:
        print("VEC FAIL: timeout")
        return 1
    log = r.stdout + r.stderr
    open(f + ".log", "w").write(log)
    errs = [l for l in log.split("\n") if ": error" in l]
    axl = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
    badax = [n for n, x in axl if not {y.strip() for y in x.split(",")} <= AXIOMS_OK]
    if r.returncode != 0 or errs or "sorry" in log or len(axl) != len(names) or badax:
        print(f"VEC FAIL: exit {r.returncode}, {len(errs)} error(s), {len(axl)}/{len(names)} axiom lines, bad {badax}")
        for l in (errs or log.strip().split("\n"))[:5]:
            print("   ", l[:300])
        return 1
    for i, tag, cr in names:
        print(f"  {ns}.vec{i}: input ({tag}) -> every complete run ends with out = [{cr % (1 << 32)}] (C: {cr})")
    print(f"VEC PASS {len(names)}/{len(vecs)} (axioms {sorted({y.strip() for _, x in axl for y in x.split(',')})})"
          + (" -- some vectors skipped" if skipped else ""))
    return 0 if not skipped else 1


if __name__ == "__main__":
    sys.exit(main())
