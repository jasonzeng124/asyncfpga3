#!/usr/bin/env python3
"""Stage 2a of verify.sh: the token-level Lean proof, re-checked on a FRESH import (probe C-vk).

    python3 leanstage.py KERNEL MLIR OUTDIR [--c C_FILE]

1. Runs C-8i's exporter (formal/tools/dfimport/mlir2lean.py, unchanged) on MLIR with the
   kernel's naming options: the graph (`rules`, with its decide-checked well-formedness
   theorems) and the symbolic schedule certificates (`seg*`).
2. Writes ONE Lean file OUTDIR/<K>Verify.lean = that graph + those certificates + the
   kernel's hand-written proof (formal/lean/Formal/Net/<K>HwProof.lean, its imports of the
   committed graph replaced by the fresh one), then `#print axioms` of the main theorem and
   `#eval`s of the hand transcription of the C on the vectors.
   So the committed proof is checked against the graph the given MLIR produces NOW, not
   against the committed copy: a mutated MLIR breaks it.
3. Checks it with `formal/slot.sh lake env lean` (one Lean process; needs only the
   Formal.Net.GcdHwLib .olean and its imports).

Prints a verdict line `LEAN PASS|FAIL|PARTIAL ...` and, on PASS, the transcription values
as `LEANREF a,b -> r` lines (compared against the compiled C by verify.sh).
A kernel without a hand proof gets PARTIAL: the graph's well-formedness and the schedule
certificates are kernel-checked, nothing about the C function.
"""
import argparse
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
LEAN = os.path.join(ROOT, "formal", "lean")
sys.path.insert(0, HERE)
from kernels import KERNELS  # noqa: E402

AXIOMS_OK = {"propext", "Classical.choice", "Quot.sound"}


def body(text):
    """(imports, rest) of a Lean file."""
    imps, rest = [], []
    for l in text.split("\n"):
        (imps if l.startswith("import ") else rest).append(l)
    return [l.split()[1] for l in imps], "\n".join(rest)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("kernel")
    ap.add_argument("mlir")
    ap.add_argument("outdir")
    ap.add_argument("--timeout", type=int, default=3600)
    a = ap.parse_args()
    k = KERNELS[a.kernel]
    os.makedirs(a.outdir, exist_ok=True)
    K = k["K"]
    g, s = os.path.join(a.outdir, f"{K}.lean"), os.path.join(a.outdir, f"{K}Seg.lean")
    env = {x: y for x, y in os.environ.items() if not x.startswith("BDC_")}
    subprocess.run([sys.executable, os.path.join(ROOT, "formal/tools/dfimport/mlir2lean.py"), a.mlir,
                    "-o", g, "--segments", s] + (k["dfargs"] or []), check=True, env=env)
    gi, gb = body(open(g).read())
    si, sb = body(open(s).read())
    inlined = {f"Formal.Net.{K}", f"Formal.Net.{K}Seg"}
    imports = [x for x in gi + si if x not in inlined]
    parts = [gb, sb]
    thm = k.get("theorem")
    if k.get("proof"):
        for pf in k["proof"]:
            pi, pb = body(open(os.path.join(LEAN, pf)).read())
            imports += [x for x in pi if x not in inlined]
            parts.append(pb)
            inlined.add(pf[:-5].replace("/", "."))
    else:
        # no hand proof: audit the generated certificates
        segs = re.findall(r"^theorem (seg\d+)", sb, re.M)
        thm = None
        parts.append(f"namespace {k['ns']}\n" +
                     "theorem verify_certs : True := by\n  " +
                     "\n  ".join(f"have _ := @{x}" for x in segs + ["ins_ok", "outs_ok", "spine_ok", "bounded_ok"]) +
                     "\n  trivial\nend " + k["ns"])
        thm = f"{k['ns']}.verify_certs"
    tail = [f"#print axioms {thm}"]
    vecs = [v for v in k["vectors"] if k["domain"](v)]
    if k.get("lean_ref"):
        for v in vecs:
            bits = [x % (1 << 32) for x in v]
            tail.append(f'#eval s!"LEANREF {",".join(map(str, v))} -> {{repr ({k["lean_ref"].format(*bits)})}}"')
    seen, imps = set(), []
    for x in imports:
        if x not in seen and x not in inlined:
            seen.add(x)
            imps.append(x)
    text = "\n".join(f"import {x}" for x in imps) + "\n" + "\n".join(parts) + "\n" + "\n".join(tail) + "\n"
    out = os.path.join(a.outdir, f"{K}Verify.lean")
    open(out, "w").write(text)
    print(f"lean: wrote {os.path.relpath(out, ROOT) if out.startswith(ROOT) else out} "
          f"({text.count(chr(10))} lines; imports {', '.join(imps)})")
    try:
        r = subprocess.run([os.path.join(ROOT, "formal", "slot.sh"), "lake", "env", "lean", os.path.abspath(out)],
                           capture_output=True, text=True, timeout=a.timeout)
        log = r.stdout + r.stderr
        rc = r.returncode
    except subprocess.TimeoutExpired:
        print(f"LEAN FAIL: timeout after {a.timeout}s")
        return 1
    open(out + ".log", "w").write(log)
    errs = [l for l in log.split("\n") if ": error" in l]
    sorry = [l for l in log.split("\n") if "sorry" in l]
    m = re.search(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
    axs = set(x.strip() for x in m.group(2).split(",")) if m else set()
    noax = re.search(r"'([^']+)' does not depend on any axioms", log)
    if rc != 0 or errs or sorry:
        print(f"LEAN FAIL: {len(errs)} error(s) (exit {rc}); first ones:")
        for l in (errs or log.strip().split("\n"))[:6]:
            print("   ", l.replace(os.path.abspath(a.outdir) + "/", "")[:300])
        return 1
    if not (m or noax) or not axs <= AXIOMS_OK:
        print(f"LEAN FAIL: axiom audit: {sorted(axs) if m else 'no #print axioms output'}")
        return 1
    for l in log.split("\n"):
        if l.startswith('"LEANREF') or l.startswith("LEANREF"):
            print(l.strip('"'))
    what = "PASS" if k.get("proof") else "PARTIAL"
    print(f"LEAN {what}: {thm} checked; axioms {sorted(axs) or 'none'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
