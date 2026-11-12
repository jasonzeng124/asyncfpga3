#!/usr/bin/env python3
"""Stage 2e of verify.sh: a GENERATED all-inputs token-level proof (probe C-vk2).

    python3 autostage.py KERNEL MLIR OUTDIR [--c C_FILE]

Runs formal/tools/autoproof/autoproof.py on MLIR and the kernel's C function (no hand proof
involved), writes ONE Lean file OUTDIR/Auto<K>V.lean = the fresh graph + its symbolic
segments + the generated proof + `#print axioms` of `auto_computes` + `#eval`s of the
generated C transcription on the vectors, and checks it with `formal/slot.sh lake env lean`.

Prints `AUTO PASS|FAIL|NOTPROVED ...`, and on PASS the transcription values as
`AUTOREF a,b -> r` lines (compared against the compiled C by verify.py).
Exit: 0 PASS, 1 counterexample found by autoproof's co-simulation (Python semantics),
2 not proved (no correspondence found, or Lean rejected the generated proof), 3 skipped.
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

AXIOMS_OK = {"propext", "Classical.choice", "Quot.sound"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("kernel")
    ap.add_argument("mlir")
    ap.add_argument("outdir")
    ap.add_argument("--c")
    ap.add_argument("--vecs", default="")
    ap.add_argument("--timeout", type=int, default=3600)
    a = ap.parse_args()
    k = KERNELS[a.kernel]
    cfile = os.path.abspath(a.c or os.path.join(ROOT, k.get("autoc") or k["c"]))
    os.makedirs(a.outdir, exist_ok=True)
    name = k["K"] + "V"
    gns = f"Formal.Net.Auto{name}G"
    out = os.path.join(a.outdir, f"Auto{name}.lean")
    env = {x: y for x, y in os.environ.items() if not x.startswith("BDC_")}
    cmd = [sys.executable, os.path.join(ROOT, "formal/tools/autoproof/autoproof.py"), a.mlir, cfile, k["func"],
           "--name", name, "--graph-ns", gns, "--combined", out,
           "--dfargs", f"--ns {gns} --graph-module X --label {a.kernel} --short {a.kernel}"]
    if a.vecs:
        cmd += ["--vecs", a.vecs]
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    print(r.stdout.rstrip())
    if r.returncode == 1:
        print("AUTO FAIL: counterexample (above)")
        return 1
    if r.returncode != 0:
        if r.stderr.strip():
            print(r.stderr.strip()[-2000:])
        print("AUTO NOTPROVED: the generator found no correspondence (above)")
        return 2
    thm = f"Formal.Net.Auto{name}.auto_computes"
    tail = [f"#print axioms {thm}"]
    vecs = [tuple(int(x) for x in v.split(",")) for v in a.vecs.split()] if a.vecs else []
    for v in vecs:
        bits = " ".join(str(x % (1 << 32)) for x in v)
        tail.append(f'#eval s!"AUTOREF {",".join(map(str, v))} -> {{repr (Formal.Net.Auto{name}.kC 1000000 {bits})}}"')
    with open(out, "a") as f:
        f.write("\n" + "\n".join(tail) + "\n")
    print(f"auto: wrote {os.path.relpath(out, ROOT) if out.startswith(ROOT) else out}")
    try:
        r = subprocess.run([os.path.join(ROOT, "formal", "slot.sh"), "lake", "env", "lean", os.path.abspath(out)],
                           capture_output=True, text=True, timeout=a.timeout)
        log, rc = r.stdout + r.stderr, r.returncode
    except subprocess.TimeoutExpired:
        print(f"AUTO NOTPROVED: Lean timeout after {a.timeout}s")
        return 2
    open(out + ".log", "w").write(log)
    errs = [l for l in log.split("\n") if ": error" in l]
    m = re.search(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
    axs = set(x.strip() for x in m.group(2).split(",")) if m else set()
    noax = re.search(r"'([^']+)' does not depend on any axioms", log)
    if rc != 0 or errs or "sorry" in log:
        print(f"AUTO NOTPROVED: Lean rejected the generated proof: {len(errs)} error(s); first ones:")
        for l in (errs or log.strip().split("\n"))[:6]:
            print("   ", l.replace(os.path.abspath(a.outdir) + "/", "")[:300])
        return 2
    if not (m or noax) or not axs <= AXIOMS_OK:
        print(f"AUTO NOTPROVED: axiom audit: {sorted(axs) if m else 'no #print axioms output'}")
        return 2
    for l in log.split("\n"):
        if l.startswith('"AUTOREF') or l.startswith("AUTOREF"):
            print(l.strip('"'))
    print(f"AUTO PASS: {thm} checked; axioms {sorted(axs) or 'none'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
